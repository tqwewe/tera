use std::borrow::Cow;
use std::collections::HashMap;
use std::io::Write;

use serde_json::{to_string_pretty, to_value, Number, Value};

use crate::context::{ValueRender, ValueTruthy};
use crate::errors::{Error, Result};
use crate::parser::ast::*;
use crate::renderer::call_stack::CallStack;
use crate::renderer::for_loop::ForLoop;
use crate::renderer::macros::MacroCollection;
use crate::renderer::square_brackets::pull_out_square_bracket;
use crate::renderer::stack_frame::{FrameContext, FrameType, Val};
use crate::template::Template;
use crate::tera::Tera;
use crate::utils::render_to_string;
use crate::Context;

/// Special string indicating request to dump context
static MAGICAL_DUMP_VAR: &str = "__tera_context";

/// This will convert a Tera variable to a json pointer if it is possible by replacing
/// the index with their evaluated stringified value
fn evaluate_sub_variables<'a>(key: &str, call_stack: &CallStack<'a>) -> Result<(String, bool)> {
    let sub_vars_to_calc = pull_out_square_bracket(key);
    let mut new_key = key.to_string();
    let mut user_defined = false;

    for sub_var in &sub_vars_to_calc {
        // Translate from variable name to variable value
        match process_path(sub_var.as_ref(), call_stack) {
            Err(e) => {
                return Err(Error::msg(format!(
                    "Variable {} can not be evaluated because: {}",
                    key, e
                )));
            }
            Ok((post_var, ud)) => {
                let post_var_as_str = match *post_var {
                    Value::String(ref s) => s.to_string(),
                    Value::Number(ref n) => n.to_string(),
                    _ => {
                        return Err(Error::msg(format!(
                            "Only variables evaluating to String or Number can be used as \
                             index (`{}` of `{}`)",
                            sub_var, key,
                        )));
                    }
                };

                // Rebuild the original key String replacing variable name with value
                let nk = new_key.clone();
                let divider = "[".to_string() + sub_var + "]";
                let mut the_parts = nk.splitn(2, divider.as_str());

                new_key = the_parts.next().unwrap().to_string()
                    + "."
                    + post_var_as_str.as_ref()
                    + the_parts.next().unwrap_or("");
                user_defined = ud;
            }
        }
    }

    Ok((
        new_key
            .replace("/", "~1") // https://tools.ietf.org/html/rfc6901#section-3
            .replace("['", ".\"")
            .replace("[\"", ".\"")
            .replace("[", ".")
            .replace("']", "\"")
            .replace("\"]", "\"")
            .replace("]", ""),
        user_defined,
    ))
}

fn process_path<'a>(path: &str, call_stack: &CallStack<'a>) -> Result<(Val<'a>, bool)> {
    if !path.contains('[') {
        match call_stack.lookup(path) {
            Some(v) => Ok(v),
            None => Err(Error::msg(format!(
                "Variable `{}` not found in context while rendering '{}'",
                path,
                call_stack.active_template().name
            ))),
        }
    } else {
        let (full_path, user_defined) = evaluate_sub_variables(path, call_stack)?;

        match call_stack.lookup(full_path.as_ref()) {
            Some((v, ud)) => Ok((v, ud || user_defined)),
            None => Err(Error::msg(format!(
                "Variable `{}` not found in context while rendering '{}': \
                 the evaluated version was `{}`. Maybe the index is out of bounds?",
                path,
                call_stack.active_template().name,
                full_path,
            ))),
        }
    }
}

/// Processes the ast and renders the output
pub struct Processor<'a> {
    /// The template we're trying to render
    template: &'a Template,
    /// Root template of template to render - contains ast to use for rendering
    /// Can be the same as `template` if a template has no inheritance
    template_root: &'a Template,
    /// The Tera object with template details
    tera: &'a Tera,
    /// The call stack for processing
    call_stack: CallStack<'a>,
    /// The macros organised by template and namespaces
    macros: MacroCollection<'a>,
    /// If set, rendering should be escaped
    should_escape: bool,
    /// Used when super() is used in a block, to know where we are in our stack of
    /// definitions and for which block
    /// Vec<(block name, tpl_name, level)>
    blocks: Vec<(&'a str, &'a str, usize)>,
}

impl<'a> Processor<'a> {
    /// Create a new `Processor` that will do the rendering
    pub fn new(
        template: &'a Template,
        tera: &'a Tera,
        context: &'a Context,
        should_escape: bool,
    ) -> Self {
        // Gets the root template if we are rendering something with inheritance or just return
        // the template we're dealing with otherwise
        let template_root = template
            .parents
            .last()
            .map(|parent| tera.get_template(parent).unwrap())
            .unwrap_or(template);

        let call_stack = CallStack::new(&context, template);

        Processor {
            template,
            template_root,
            tera,
            call_stack,
            macros: MacroCollection::from_original_template(&template, &tera),
            should_escape,
            blocks: Vec::new(),
        }
    }

    fn render_body(&mut self, body: &'a [Node], write: &mut impl Write) -> Result<bool> {
        let mut user_defined = false;
        for n in body {
            user_defined = self.render_node(n, write)? || user_defined;

            if self.call_stack.should_break_body() {
                break;
            }
        }

        Ok(user_defined)
    }

    fn render_for_loop(&mut self, for_loop: &'a Forloop, write: &mut impl Write) -> Result<bool> {
        let container_name = match for_loop.container.val {
            ExprVal::Ident(ref ident) => ident,
            ExprVal::FunctionCall(FunctionCall { ref name, .. }) => name,
            ExprVal::Array(_) => "an array literal",
            _ => return Err(Error::msg(format!(
                "Forloop containers have to be an ident or a function call (tried to iterate on '{:?}')",
                for_loop.container.val,
            ))),
        };

        let for_loop_name = &for_loop.value;
        let for_loop_body = &for_loop.body;
        let for_loop_empty_body = &for_loop.empty_body;

        let (container_val, user_defined) = self.safe_eval_expression(&for_loop.container)?;

        let for_loop = match *container_val {
            Value::Array(_) => {
                if for_loop.key.is_some() {
                    return Err(Error::msg(format!(
                        "Tried to iterate using key value on variable `{}`, but it isn't an object/map",
                        container_name,
                    )));
                }
                ForLoop::from_array(&for_loop.value, container_val)
            }
            Value::String(_) => {
                if for_loop.key.is_some() {
                    return Err(Error::msg(format!(
                        "Tried to iterate using key value on variable `{}`, but it isn't an object/map",
                        container_name,
                    )));
                }
                ForLoop::from_string(&for_loop.value, container_val)
            }
            Value::Object(_) => {
                if for_loop.key.is_none() {
                    return Err(Error::msg(format!(
                        "Tried to iterate using key value on variable `{}`, but it is missing a key",
                        container_name,
                    )));
                }
                match container_val {
                    Cow::Borrowed(c) => {
                        ForLoop::from_object(&for_loop.key.as_ref().unwrap(), &for_loop.value, c)
                    }
                    Cow::Owned(c) => ForLoop::from_object_owned(
                        &for_loop.key.as_ref().unwrap(),
                        &for_loop.value,
                        c,
                    ),
                }
            }
            _ => {
                return Err(Error::msg(format!(
                    "Tried to iterate on a container (`{}`) that has a unsupported type",
                    container_name,
                )));
            }
        };

        let len = for_loop.len();
        match (len, for_loop_empty_body) {
            (0, Some(empty_body)) => {
                self.render_body(&empty_body, write)?;
                Ok(user_defined)
            }
            (0, _) => Ok(user_defined),
            (_, _) => {
                self.call_stack.push_for_loop_frame(for_loop_name, for_loop);

                for _ in 0..len {
                    self.render_body(&for_loop_body, write)?;

                    if self.call_stack.should_break_for_loop() {
                        break;
                    }

                    self.call_stack.increment_for_loop()?;
                }

                self.call_stack.pop();

                Ok(user_defined)
            }
        }
    }

    fn render_if_node(&mut self, if_node: &'a If, write: &mut impl Write) -> Result<bool> {
        let mut user_defined = false;
        for &(_, ref expr, ref body) in &if_node.conditions {
            let (b, ud) = self.eval_as_bool(expr)?;
            user_defined = user_defined || ud;
            if b {
                return Ok(self.render_body(body, write)? || user_defined);
            }
        }

        if let Some((_, ref body)) = if_node.otherwise {
            return Ok(self.render_body(body, write)? || user_defined);
        }

        Ok(user_defined)
    }

    /// The way inheritance work is that the top parent will be rendered by the renderer so for blocks
    /// we want to look from the bottom (`level = 0`, the template the user is actually rendering)
    /// to the top (the base template).
    fn render_block(
        &mut self,
        block: &'a Block,
        level: usize,
        write: &mut impl Write,
    ) -> Result<bool> {
        let level_template = match level {
            0 => self.call_stack.active_template(),
            _ => self
                .tera
                .get_template(&self.call_stack.active_template().parents[level - 1])
                .unwrap(),
        };

        let blocks_definitions = &level_template.blocks_definitions;

        // Can we find this one block in these definitions? If so render it
        if let Some(block_def) = blocks_definitions.get(&block.name) {
            let (_, Block { ref body, .. }) = block_def[0];
            self.blocks.push((&block.name[..], &level_template.name[..], level));
            return self.render_body(body, write);
        }

        // Do we have more parents to look through?
        if level < self.call_stack.active_template().parents.len() {
            return self.render_block(block, level + 1, write);
        }

        // Nope, just render the body we got
        self.render_body(&block.body, write)
    }

    fn get_default_value(&mut self, expr: &'a Expr) -> Result<(Val<'a>, bool)> {
        if let Some(default_expr) = expr.filters[0].args.get("value") {
            self.eval_expression(default_expr)
        } else {
            Err(Error::msg("The `default` filter requires a `value` argument."))
        }
    }

    fn eval_in_condition(&mut self, in_cond: &'a In) -> Result<(bool, bool)> {
        let (lhs, lhs_ud) = self.safe_eval_expression(&in_cond.lhs)?;
        let (rhs, rhs_ud) = self.safe_eval_expression(&in_cond.rhs)?;
        let user_defined = lhs_ud || rhs_ud;

        let present = match *rhs {
            Value::Array(ref v) => v.contains(&lhs),
            Value::String(ref s) => match *lhs {
                Value::String(ref s2) => s.contains(s2),
                _ => {
                    return Err(Error::msg(format!(
                        "Tried to check if {:?} is in a string, but it isn't a string",
                        lhs
                    )))
                }
            },
            Value::Object(ref map) => match *lhs {
                Value::String(ref s2) => map.contains_key(s2),
                _ => {
                    return Err(Error::msg(format!(
                        "Tried to check if {:?} is in a object, but it isn't a string",
                        lhs
                    )))
                }
            },
            _ => {
                return Err(Error::msg(
                    "The `in` operator only supports strings, arrays and objects.",
                ))
            }
        };

        Ok((if in_cond.negated { !present } else { present }, user_defined))
    }

    fn eval_expression(&mut self, expr: &'a Expr) -> Result<(Val<'a>, bool)> {
        let mut needs_escape = false;

        let (mut res, mut user_defined) = match expr.val {
            ExprVal::Array(ref arr) => {
                let (values, user_defined) =
                    arr.into_iter().fold(Result::Ok((vec![], false)), |acc, v| {
                        let (mut values, user_defined) = acc?;
                        let (v, ud) = self.eval_expression(v)?;
                        values.push(v.into_owned());
                        Ok((values, ud || user_defined))
                    })?;
                (Cow::Owned(Value::Array(values)), user_defined)
            }
            ExprVal::In(ref in_cond) => {
                let (in_condition, user_defined) = self.eval_in_condition(in_cond)?;
                (Cow::Owned(Value::Bool(in_condition)), user_defined)
            }
            ExprVal::String(ref val) => {
                needs_escape = true;
                (Cow::Owned(Value::String(val.to_string())), false)
            }
            ExprVal::StringConcat(ref str_concat) => {
                let mut res = String::new();
                let mut user_defined = false;
                for s in &str_concat.values {
                    match *s {
                        ExprVal::String(ref v) => res.push_str(&v),
                        ExprVal::Int(ref v) => res.push_str(&format!("{}", v)),
                        ExprVal::Float(ref v) => res.push_str(&format!("{}", v)),
                        ExprVal::Ident(ref i) => {
                            let (v, ud) = self.lookup_ident(i)?;
                            user_defined = user_defined || ud;
                            match *v {
                                Value::String(ref v) => res.push_str(&v),
                                Value::Number(ref v) => res.push_str(&v.to_string()),
                                _ => return Err(Error::msg(format!(
                                    "Tried to concat a value that is not a string or a number from ident {}",
                                    i
                                ))),
                            }
                        }
                        ExprVal::FunctionCall(ref fn_call) => {
                            let (val, ud) = self.eval_tera_fn_call(fn_call, &mut needs_escape)?;
                            user_defined = user_defined || ud;
                            match *val {
                                Value::String(ref v) => res.push_str(&v),
                                Value::Number(ref v) => res.push_str(&v.to_string()),
                                _ => return Err(Error::msg(format!(
                                    "Tried to concat a value that is not a string or a number from function call {}",
                                    fn_call.name
                                ))),
                            }
                        }
                        _ => unreachable!(),
                    };
                }

                (Cow::Owned(Value::String(res)), user_defined)
            }
            ExprVal::Int(val) => (Cow::Owned(Value::Number(val.into())), false),
            ExprVal::Float(val) => {
                (Cow::Owned(Value::Number(Number::from_f64(val).unwrap())), false)
            }
            ExprVal::Bool(val) => (Cow::Owned(Value::Bool(val)), false),
            ExprVal::Ident(ref ident) => {
                needs_escape = ident != MAGICAL_DUMP_VAR;
                // Negated idents are special cased as `not undefined_ident` should not
                // error but instead be falsy values
                match self.lookup_ident(ident) {
                    Ok((val, user_defined)) => {
                        if val.is_null() && expr.has_default_filter() {
                            self.get_default_value(expr)?
                        } else {
                            (val, user_defined)
                        }
                    }
                    Err(e) => {
                        if expr.has_default_filter() {
                            self.get_default_value(expr)?
                        } else {
                            if !expr.negated {
                                return Err(e);
                            }
                            // A negative undefined ident is !false so truthy
                            return Ok((Cow::Owned(Value::Bool(true)), false));
                        }
                    }
                }
            }
            ExprVal::FunctionCall(ref fn_call) => {
                self.eval_tera_fn_call(fn_call, &mut needs_escape)?
            }
            ExprVal::MacroCall(ref macro_call) => {
                let (val, user_defined) = render_to_string(
                    || format!("macro {}", macro_call.name),
                    |w| self.eval_macro_call(macro_call, w),
                )?;
                (Cow::Owned(Value::String(val)), user_defined)
            }
            ExprVal::Test(ref test) => {
                let (b, user_defined) = self.eval_test(test)?;
                (Cow::Owned(Value::Bool(b)), user_defined)
            }
            ExprVal::Logic(_) => {
                let (b, user_defined) = self.eval_as_bool(expr)?;
                (Cow::Owned(Value::Bool(b)), user_defined)
            }
            ExprVal::Math(_) => match self.eval_as_number(&expr.val) {
                Ok((Some(n), user_defined)) => (Cow::Owned(Value::Number(n)), user_defined),
                Ok((None, user_defined)) => {
                    (Cow::Owned(Value::String("NaN".to_owned())), user_defined)
                }
                Err(e) => return Err(Error::msg(e)),
            },
        };

        for filter in &expr.filters {
            if filter.name == "safe" || filter.name == "default" {
                continue;
            }
            (res, user_defined) = self
                .eval_filter(&res, filter, &mut needs_escape)
                .map(|(res, ud)| (res, user_defined || ud))?;
        }

        // Lastly, we need to check if the expression is negated, thus turning it into a bool
        if expr.negated {
            return Ok((Cow::Owned(Value::Bool(!res.is_truthy())), user_defined));
        }

        // Checks if it's a string and we need to escape it (if the last filter is `safe` we don't)
        if self.should_escape && needs_escape && res.is_string() && !expr.is_marked_safe() {
            res = Cow::Owned(
                to_value(self.tera.get_escape_fn()(res.as_str().unwrap())).map_err(Error::json)?,
            );
        }

        Ok((res, user_defined))
    }

    /// Render an expression and never escape its result
    fn safe_eval_expression(&mut self, expr: &'a Expr) -> Result<(Val<'a>, bool)> {
        let should_escape = self.should_escape;
        self.should_escape = false;
        let res = self.eval_expression(expr);
        self.should_escape = should_escape;
        res
    }

    /// Evaluate a set tag and add the value to the right context
    fn eval_set(&mut self, set: &'a Set) -> Result<bool> {
        let (assigned_value, user_defined) = self.safe_eval_expression(&set.value)?;
        self.call_stack.add_assignment(&set.key[..], set.global, assigned_value);
        Ok(user_defined)
    }

    fn eval_test(&mut self, test: &'a Test) -> Result<(bool, bool)> {
        let tester_fn = self.tera.get_tester(&test.name)?;
        let err_wrap = |e| Error::call_test(&test.name, e);

        let (tester_args, user_defined) =
            test.args.iter().fold(Result::Ok((vec![], false)), |acc, arg| {
                let (mut tester_args, user_defined) = acc?;
                let (v, ud) = self.safe_eval_expression(arg).map_err(err_wrap)?;
                tester_args.push(v.clone().into_owned());
                Ok((tester_args, ud || user_defined))
            })?;

        let found = self
            .lookup_ident(&test.ident)
            .map(|(found, ud)| (found.clone().into_owned(), ud || user_defined))
            .ok();

        let result = tester_fn
            .test(found.as_ref().map(|(found, _)| found), &tester_args)
            .map_err(err_wrap)?;
        let user_defined = found.map(|(_, user_defined)| user_defined).unwrap_or(false);
        if test.negated {
            Ok((!result, user_defined))
        } else {
            Ok((result, user_defined))
        }
    }

    fn eval_tera_fn_call(
        &mut self,
        function_call: &'a FunctionCall,
        needs_escape: &mut bool,
    ) -> Result<(Val<'a>, bool)> {
        let tera_fn = self.tera.get_function(&function_call.name)?;
        *needs_escape = !tera_fn.is_safe();

        let err_wrap = |e| Error::call_function(&function_call.name, e);

        let (args, user_defined) = function_call.args.iter().fold(
            Result::Ok((HashMap::new(), false)),
            |acc, (arg_name, expr)| {
                let (mut args, user_defined) = acc?;
                let (v, ud) = self.safe_eval_expression(expr).map_err(err_wrap)?;
                args.insert(arg_name.to_string(), v.clone().into_owned());
                Ok((args, ud || user_defined))
            },
        )?;

        Ok((Cow::Owned(tera_fn.call(&args).map_err(err_wrap)?), user_defined))
    }

    fn eval_macro_call(
        &mut self,
        macro_call: &'a MacroCall,
        write: &mut impl Write,
    ) -> Result<bool> {
        let active_template_name = if let Some(block) = self.blocks.last() {
            block.1
        } else if self.template.name != self.template_root.name {
            &self.template_root.name
        } else {
            &self.call_stack.active_template().name
        };

        let (macro_template_name, macro_definition) = self.macros.lookup_macro(
            active_template_name,
            &macro_call.namespace[..],
            &macro_call.name[..],
        )?;

        let mut frame_context = FrameContext::with_capacity(macro_definition.args.len());

        // First the default arguments
        let mut user_defined = false;
        for (arg_name, default_value) in &macro_definition.args {
            let (value, ud) = match macro_call.args.get(arg_name) {
                Some(val) => self.safe_eval_expression(val)?,
                None => match *default_value {
                    Some(ref val) => self.safe_eval_expression(val)?,
                    None => {
                        return Err(Error::msg(format!(
                            "Macro `{}` is missing the argument `{}`",
                            macro_call.name, arg_name
                        )));
                    }
                },
            };
            frame_context.insert(&arg_name, value);
            user_defined = user_defined || ud;
        }

        self.call_stack.push_macro_frame(
            &macro_call.namespace,
            &macro_call.name,
            frame_context,
            self.tera.get_template(macro_template_name)?,
        );

        user_defined = self.render_body(&macro_definition.body, write)? || user_defined;

        self.call_stack.pop();

        Ok(user_defined)
    }

    fn eval_filter(
        &mut self,
        value: &Val<'a>,
        fn_call: &'a FunctionCall,
        needs_escape: &mut bool,
    ) -> Result<(Val<'a>, bool)> {
        let filter_fn = self.tera.get_filter(&fn_call.name)?;
        *needs_escape = !filter_fn.is_safe();

        let err_wrap = |e| Error::call_filter(&fn_call.name, e);

        let mut args = HashMap::new();
        let mut user_defined = false;
        for (arg_name, expr) in &fn_call.args {
            let (value, ud) = self.safe_eval_expression(expr).map_err(err_wrap)?;
            args.insert(arg_name.to_string(), value.clone().into_owned());
            user_defined = user_defined || ud;
        }

        Ok((Cow::Owned(filter_fn.filter(&value, &args).map_err(err_wrap)?), user_defined))
    }

    fn eval_as_bool(&mut self, bool_expr: &'a Expr) -> Result<(bool, bool)> {
        let (res, user_defined) = match bool_expr.val {
            ExprVal::Logic(LogicExpr { ref lhs, ref rhs, ref operator }) => {
                match *operator {
                    LogicOperator::Or => {
                        let (l, l_ud) = self.eval_as_bool(lhs)?;
                        let (r, r_ud) = self.eval_as_bool(rhs)?;
                        (l || r, l_ud || r_ud)
                    }
                    LogicOperator::And => {
                        let (l, l_ud) = self.eval_as_bool(lhs)?;
                        let (r, r_ud) = self.eval_as_bool(rhs)?;
                        (l && r, l_ud || r_ud)
                    }
                    LogicOperator::Gt
                    | LogicOperator::Gte
                    | LogicOperator::Lt
                    | LogicOperator::Lte => {
                        let (l, l_ud) = self.eval_expr_as_number(lhs)?;
                        let (r, r_ud) = self.eval_expr_as_number(rhs)?;
                        let (ll, rr, user_defined) = match (l, r) {
                            (Some(nl), Some(nr)) => (nl, nr, l_ud || r_ud),
                            _ => return Err(Error::msg("Comparison to NaN")),
                        };

                        match *operator {
                            LogicOperator::Gte => {
                                (ll.as_f64().unwrap() >= rr.as_f64().unwrap(), user_defined)
                            }
                            LogicOperator::Gt => {
                                (ll.as_f64().unwrap() > rr.as_f64().unwrap(), user_defined)
                            }
                            LogicOperator::Lte => {
                                (ll.as_f64().unwrap() <= rr.as_f64().unwrap(), user_defined)
                            }
                            LogicOperator::Lt => {
                                (ll.as_f64().unwrap() < rr.as_f64().unwrap(), user_defined)
                            }
                            _ => unreachable!(),
                        }
                    }
                    LogicOperator::Eq | LogicOperator::NotEq => {
                        let (mut lhs_val, lhs_ud) = self.eval_expression(lhs)?;
                        let (mut rhs_val, rhs_ud) = self.eval_expression(rhs)?;
                        let user_defined = lhs_ud || rhs_ud;

                        // Monomorphize number vals.
                        if lhs_val.is_number() || rhs_val.is_number() {
                            // We're not implementing JS so can't compare things of different types
                            if !lhs_val.is_number() || !rhs_val.is_number() {
                                return Ok((false, user_defined));
                            }

                            lhs_val = Cow::Owned(Value::Number(
                                Number::from_f64(lhs_val.as_f64().unwrap()).unwrap(),
                            ));
                            rhs_val = Cow::Owned(Value::Number(
                                Number::from_f64(rhs_val.as_f64().unwrap()).unwrap(),
                            ));
                        }

                        match *operator {
                            LogicOperator::Eq => (*lhs_val == *rhs_val, user_defined),
                            LogicOperator::NotEq => (*lhs_val != *rhs_val, user_defined),
                            _ => unreachable!(),
                        }
                    }
                }
            }
            ExprVal::Ident(_) => {
                let (res, user_defined) = self
                    .eval_expression(&bool_expr)
                    .unwrap_or((Cow::Owned(Value::Bool(false)), false));
                let mut res = res.is_truthy();
                if bool_expr.negated {
                    res = !res;
                }
                (res, user_defined)
            }
            ExprVal::Math(_) | ExprVal::Int(_) | ExprVal::Float(_) => {
                match self.eval_as_number(&bool_expr.val)? {
                    (Some(n), user_defined) => (n.as_f64().unwrap() != 0.0, user_defined),
                    (None, user_defined) => (false, user_defined),
                }
            }
            ExprVal::In(ref in_cond) => self.eval_in_condition(&in_cond)?,
            ExprVal::Test(ref test) => self.eval_test(test)?,
            ExprVal::Bool(val) => (val, false),
            ExprVal::String(ref string) => (!string.is_empty(), false),
            ExprVal::FunctionCall(ref fn_call) => {
                let (v, user_defined) = self.eval_tera_fn_call(fn_call, &mut false)?;
                match v.as_bool() {
                    Some(val) => (val, user_defined),
                    None => {
                        return Err(Error::msg(format!(
                            "Function `{}` was used in a logic operation but is not returning a bool",
                            fn_call.name,
                        )));
                    }
                }
            }
            ExprVal::StringConcat(_) => {
                let (res, user_defined) = self.eval_expression(bool_expr)?;
                (!res.as_str().unwrap().is_empty(), user_defined)
            }
            ExprVal::MacroCall(ref macro_call) => {
                let mut buf = Vec::new();
                self.eval_macro_call(&macro_call, &mut buf)?;
                (!buf.is_empty(), false) // TODO: are macro calls always static?
            }
            _ => unreachable!("unimplemented logic operation for {:?}", bool_expr),
        };

        if bool_expr.negated {
            return Ok((!res, user_defined));
        }

        Ok((res, user_defined))
    }

    /// In some cases, we will have filters in lhs/rhs of a math expression
    /// `eval_as_number` only works on ExprVal rather than Expr
    fn eval_expr_as_number(&mut self, expr: &'a Expr) -> Result<(Option<Number>, bool)> {
        if !expr.filters.is_empty() {
            let (value, user_defined) = self.eval_expression(expr)?;
            match *value {
                Value::Number(ref s) => Ok((Some(s.clone()), user_defined)),
                _ => {
                    Err(Error::msg("Tried to do math with an expression not resulting in a number"))
                }
            }
        } else {
            self.eval_as_number(&expr.val)
        }
    }

    /// Return the value of an expression as a number
    fn eval_as_number(&mut self, expr: &'a ExprVal) -> Result<(Option<Number>, bool)> {
        let result = match *expr {
            ExprVal::Ident(ref ident) => {
                let (v, user_defined) = self.lookup_ident(ident)?;
                if v.is_i64() {
                    (Some(Number::from(v.as_i64().unwrap())), user_defined)
                } else if v.is_u64() {
                    (Some(Number::from(v.as_u64().unwrap())), user_defined)
                } else if v.is_f64() {
                    (Some(Number::from_f64(v.as_f64().unwrap()).unwrap()), user_defined)
                } else {
                    return Err(Error::msg(format!(
                        "Variable `{}` was used in a math operation but is not a number",
                        ident
                    )));
                }
            }
            ExprVal::Int(val) => (Some(Number::from(val)), false),
            ExprVal::Float(val) => (Some(Number::from_f64(val).unwrap()), false),
            ExprVal::Math(MathExpr { ref lhs, ref rhs, ref operator }) => {
                let (l, r, user_defined) =
                    match (self.eval_expr_as_number(lhs)?, self.eval_expr_as_number(rhs)?) {
                        ((Some(l), l_ud), (Some(r), r_ud)) => (l, r, l_ud || r_ud),
                        ((_, l_ud), (_, r_ud)) => return Ok((None, l_ud || r_ud)),
                    };

                let num = match *operator {
                    MathOperator::Mul => {
                        if l.is_i64() && r.is_i64() {
                            let ll = l.as_i64().unwrap();
                            let rr = r.as_i64().unwrap();
                            let res = match ll.checked_mul(rr) {
                                Some(s) => s,
                                None => {
                                    return Err(Error::msg(format!(
                                        "{} x {} results in an out of bounds i64",
                                        ll, rr
                                    )));
                                }
                            };

                            Some(Number::from(res))
                        } else if l.is_u64() && r.is_u64() {
                            let ll = l.as_u64().unwrap();
                            let rr = r.as_u64().unwrap();
                            let res = match ll.checked_mul(rr) {
                                Some(s) => s,
                                None => {
                                    return Err(Error::msg(format!(
                                        "{} x {} results in an out of bounds u64",
                                        ll, rr
                                    )));
                                }
                            };
                            Some(Number::from(res))
                        } else {
                            let ll = l.as_f64().unwrap();
                            let rr = r.as_f64().unwrap();
                            Number::from_f64(ll * rr)
                        }
                    }
                    MathOperator::Div => {
                        let ll = l.as_f64().unwrap();
                        let rr = r.as_f64().unwrap();
                        let res = ll / rr;
                        if res.is_nan() {
                            None
                        } else {
                            Number::from_f64(res)
                        }
                    }
                    MathOperator::Add => {
                        if l.is_i64() && r.is_i64() {
                            let ll = l.as_i64().unwrap();
                            let rr = r.as_i64().unwrap();
                            let res = match ll.checked_add(rr) {
                                Some(s) => s,
                                None => {
                                    return Err(Error::msg(format!(
                                        "{} + {} results in an out of bounds i64",
                                        ll, rr
                                    )));
                                }
                            };
                            Some(Number::from(res))
                        } else if l.is_u64() && r.is_u64() {
                            let ll = l.as_u64().unwrap();
                            let rr = r.as_u64().unwrap();
                            let res = match ll.checked_add(rr) {
                                Some(s) => s,
                                None => {
                                    return Err(Error::msg(format!(
                                        "{} + {} results in an out of bounds u64",
                                        ll, rr
                                    )));
                                }
                            };
                            Some(Number::from(res))
                        } else {
                            let ll = l.as_f64().unwrap();
                            let rr = r.as_f64().unwrap();
                            Some(Number::from_f64(ll + rr).unwrap())
                        }
                    }
                    MathOperator::Sub => {
                        if l.is_i64() && r.is_i64() {
                            let ll = l.as_i64().unwrap();
                            let rr = r.as_i64().unwrap();
                            let res = match ll.checked_sub(rr) {
                                Some(s) => s,
                                None => {
                                    return Err(Error::msg(format!(
                                        "{} - {} results in an out of bounds i64",
                                        ll, rr
                                    )));
                                }
                            };
                            Some(Number::from(res))
                        } else if l.is_u64() && r.is_u64() {
                            let ll = l.as_u64().unwrap();
                            let rr = r.as_u64().unwrap();
                            let res = match ll.checked_sub(rr) {
                                Some(s) => s,
                                None => {
                                    return Err(Error::msg(format!(
                                        "{} - {} results in an out of bounds u64",
                                        ll, rr
                                    )));
                                }
                            };
                            Some(Number::from(res))
                        } else {
                            let ll = l.as_f64().unwrap();
                            let rr = r.as_f64().unwrap();
                            Some(Number::from_f64(ll - rr).unwrap())
                        }
                    }
                    MathOperator::Modulo => {
                        if l.is_i64() && r.is_i64() {
                            let ll = l.as_i64().unwrap();
                            let rr = r.as_i64().unwrap();
                            if rr == 0 {
                                return Err(Error::msg(format!(
                                    "Tried to do a modulo by zero: {:?}/{:?}",
                                    lhs, rhs
                                )));
                            }
                            Some(Number::from(ll % rr))
                        } else if l.is_u64() && r.is_u64() {
                            let ll = l.as_u64().unwrap();
                            let rr = r.as_u64().unwrap();
                            if rr == 0 {
                                return Err(Error::msg(format!(
                                    "Tried to do a modulo by zero: {:?}/{:?}",
                                    lhs, rhs
                                )));
                            }
                            Some(Number::from(ll % rr))
                        } else {
                            let ll = l.as_f64().unwrap();
                            let rr = r.as_f64().unwrap();
                            Number::from_f64(ll % rr)
                        }
                    }
                };

                (num, user_defined)
            }
            ExprVal::FunctionCall(ref fn_call) => {
                let (v, user_defined) = self.eval_tera_fn_call(fn_call, &mut false)?;
                let num = if v.is_i64() {
                    Some(Number::from(v.as_i64().unwrap()))
                } else if v.is_u64() {
                    Some(Number::from(v.as_u64().unwrap()))
                } else if v.is_f64() {
                    Some(Number::from_f64(v.as_f64().unwrap()).unwrap())
                } else {
                    return Err(Error::msg(format!(
                        "Function `{}` was used in a math operation but is not returning a number",
                        fn_call.name
                    )));
                };
                (num, user_defined)
            }
            ExprVal::String(ref val) => {
                return Err(Error::msg(format!("Tried to do math with a string: `{}`", val)));
            }
            ExprVal::Bool(val) => {
                return Err(Error::msg(format!("Tried to do math with a boolean: `{}`", val)));
            }
            ExprVal::StringConcat(ref val) => {
                return Err(Error::msg(format!(
                    "Tried to do math with a string concatenation: {}",
                    val.to_template_string()
                )));
            }
            ExprVal::Test(ref test) => {
                return Err(Error::msg(format!("Tried to do math with a test: {}", test.name)));
            }
            _ => unreachable!("unimplemented math expression for {:?}", expr),
        };

        Ok(result)
    }

    /// Only called while rendering a block.
    /// This will look up the block we are currently rendering and its level and try to render
    /// the block at level + n, where would be the next template in the hierarchy the block is present
    fn do_super(&mut self, write: &mut impl Write) -> Result<bool> {
        let &(block_name, _, level) = self.blocks.last().unwrap();
        let mut next_level = level + 1;

        while next_level <= self.template.parents.len() {
            let blocks_definitions = &self
                .tera
                .get_template(&self.template.parents[next_level - 1])
                .unwrap()
                .blocks_definitions;

            if let Some(block_def) = blocks_definitions.get(block_name) {
                let (ref tpl_name, Block { ref body, .. }) = block_def[0];
                self.blocks.push((block_name, tpl_name, next_level));

                let user_defined = self.render_body(body, write)?;
                self.blocks.pop();

                // Can't go any higher for that block anymore?
                if next_level >= self.template.parents.len() {
                    // then remove it from the stack, we're done with it
                    self.blocks.pop();
                }
                return Ok(user_defined);
            } else {
                next_level += 1;
            }
        }

        Err(Error::msg("Tried to use super() in the top level block"))
    }

    /// Looks up identifier and returns its value
    fn lookup_ident(&self, key: &str) -> Result<(Val<'a>, bool)> {
        // Magical variable that just dumps the context
        if key == MAGICAL_DUMP_VAR {
            // Unwraps are safe since we are dealing with things that are already Value
            return Ok((
                Cow::Owned(
                    to_value(
                        to_string_pretty(&self.call_stack.current_context_cloned().take()).unwrap(),
                    )
                    .unwrap(),
                ),
                false,
            ));
        }

        process_path(key, &self.call_stack)
    }

    /// Process the given node, appending the string result to the buffer
    /// if it is possible
    pub fn render_node(&mut self, node: &'a Node, write: &mut impl Write) -> Result<bool> {
        let user_defined = match *node {
            // Comments are ignored when rendering
            Node::Comment(_, _) => false,
            Node::Text(ref s) | Node::Raw(_, ref s, _) => {
                write!(write, "{}", s)?;
                false
            }
            Node::VariableBlock(_, ref expr) => {
                let (val, user_defined) = self.eval_expression(expr)?;
                val.render(write)?;
                user_defined
            }
            Node::Set(_, ref set) => self.eval_set(set)?,
            Node::FilterSection(_, FilterSection { ref filter, ref body }, _) => {
                let (body, user_defined) = render_to_string(
                    || format!("filter {}", filter.name),
                    |w| self.render_body(body, w),
                )?;
                // the safe filter doesn't actually exist
                if filter.name == "safe" {
                    write!(write, "{}", body)?;
                    user_defined
                } else {
                    let (val, ud) =
                        self.eval_filter(&Cow::Owned(Value::String(body)), filter, &mut false)?;
                    val.render(write)?;
                    user_defined || ud
                }
            }
            // Macros have been imported at the beginning
            Node::ImportMacro(_, _, _) => false,
            Node::If(ref if_node, _) => self.render_if_node(if_node, write)?,
            Node::Forloop(_, ref forloop, _) => self.render_for_loop(forloop, write)?,
            Node::Break(_) => {
                self.call_stack.break_for_loop()?;
                false
            }
            Node::Continue(_) => {
                self.call_stack.continue_for_loop()?;
                false
            }
            Node::Block(_, ref block, _) => self.render_block(block, 0, write)?,
            Node::Super => self.do_super(write)?,
            Node::Include(_, ref tpl_names, ignore_missing) => {
                let mut found = false;
                let mut user_defined = false;
                for tpl_name in tpl_names {
                    let template = self.tera.get_template(tpl_name);
                    if template.is_err() {
                        continue;
                    }
                    let template = template.unwrap();
                    self.macros.add_macros_from_template(&self.tera, template)?;
                    self.call_stack.push_include_frame(tpl_name, template);
                    user_defined = self.render_body(&template.ast, write)? || user_defined;
                    self.call_stack.pop();
                    found = true;
                    break;
                }
                if !found && !ignore_missing {
                    return Err(Error::template_not_found(
                        vec!["[", &tpl_names.join(", "), "]"].join(""),
                    ));
                }
                user_defined
            }
            Node::Extends(_, ref name) => {
                return Err(Error::msg(format!(
                    "Inheritance in included templates is currently not supported: extended `{}`",
                    name
                )));
            }
            // TODO: make that a compile time error
            Node::MacroDefinition(_, ref def, _) => {
                return Err(Error::invalid_macro_def(&def.name));
            }
        };

        Ok(user_defined)
    }

    /// Helper fn that tries to find the current context: are we in a macro? in a parent template?
    /// in order to give the best possible error when getting an error when rendering a tpl
    fn get_error_location(&self) -> String {
        let mut error_location = format!("Failed to render '{}'", self.template.name);

        // in a macro?
        if self.call_stack.current_frame().kind == FrameType::Macro {
            let frame = self.call_stack.current_frame();
            error_location += &format!(
                ": error while rendering macro `{}::{}`",
                frame.macro_namespace.expect("Macro namespace"),
                frame.name,
            );
        }

        // which template are we in?
        if let Some(&(ref name, ref _template, ref level)) = self.blocks.last() {
            let block_def = self
                .template
                .blocks_definitions
                .get(&(*name).to_string())
                .and_then(|b| b.get(*level));

            if let Some(&(ref tpl_name, _)) = block_def {
                if tpl_name != &self.template.name {
                    error_location += &format!(" (error happened in '{}').", tpl_name);
                }
            } else {
                error_location += " (error happened in a parent template)";
            }
        } else if let Some(parent) = self.template.parents.last() {
            // Error happened in the base template, outside of blocks
            error_location += &format!(" (error happened in '{}').", parent);
        }

        error_location
    }

    /// Entry point for the rendering
    pub fn render(&mut self, write: &mut impl Write) -> Result<bool> {
        let mut user_defined = false;
        for node in &self.template_root.ast {
            user_defined = self
                .render_node(node, write)
                .map_err(|e| Error::chain(self.get_error_location(), e))?
                || user_defined;
        }

        Ok(user_defined)
    }
}
