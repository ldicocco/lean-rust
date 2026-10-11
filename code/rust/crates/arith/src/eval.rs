//! A big-step evaluator: the judgment ρ ⊢ e ⇓ v ("in the environment ρ, the
//! expression e evaluates to the value v") implemented as a function.
//!
//! The evaluator does not look at types. When an operation meets a value of
//! the wrong kind (adding a boolean, branching on a number) it reports a
//! *stuck* state: the run has gone wrong. Type safety says that this never
//! happens to a closed, well-typed expression.

use crate::syntax::{Expr, Ty};
use std::fmt;

// ANCHOR: value
/// The values of Arith: the results that evaluation can produce.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Value {
    Num(u64),
    Bool(bool),
}

impl Value {
    /// The type of a value: every value has exactly one.
    pub fn ty(&self) -> Ty {
        match self {
            Value::Num(_) => Ty::Nat,
            Value::Bool(_) => Ty::Bool,
        }
    }
}
// ANCHOR_END: value

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Num(n) => write!(f, "{n}"),
            Value::Bool(b) => write!(f, "{b}"),
        }
    }
}

/// An environment ρ: the values of the variables in scope, most recent last.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Env {
    bindings: Vec<(String, Value)>,
}

impl Env {
    pub fn new() -> Self {
        Env::default()
    }

    pub fn extend(&self, x: &str, v: Value) -> Env {
        let mut bindings = self.bindings.clone();
        bindings.push((x.to_string(), v));
        Env { bindings }
    }

    pub fn lookup(&self, x: &str) -> Option<Value> {
        self.bindings
            .iter()
            .rev()
            .find(|(name, _)| name == x)
            .map(|(_, v)| *v)
    }
}

// ANCHOR: eval_error
/// The ways a run can fail.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EvalError {
    /// A variable with no value: the run is stuck.
    Unbound(String),
    /// An operation met a value of the wrong kind: the run is stuck.
    Stuck { expr: Expr, value: Value },
    /// A sum does not fit in a `u64`. This is not a stuck state of the
    /// semantics but a limit of the machine, and types do not prevent it.
    Overflow { expr: Expr },
}
// ANCHOR_END: eval_error

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EvalError::Unbound(x) => write!(f, "stuck: `{x}` has no value"),
            EvalError::Stuck { expr, value } => {
                write!(f, "stuck: `{expr}` cannot use the value {value}")
            }
            EvalError::Overflow { expr } => write!(f, "overflow in `{expr}`"),
        }
    }
}

fn as_num(e: &Expr, v: Value) -> Result<u64, EvalError> {
    match v {
        Value::Num(n) => Ok(n),
        other => Err(EvalError::Stuck {
            expr: e.clone(),
            value: other,
        }),
    }
}

// ANCHOR: eval
/// Evaluate `e` in the environment `env`.
pub fn eval(env: &Env, e: &Expr) -> Result<Value, EvalError> {
    match e {
        Expr::Num(n) => Ok(Value::Num(*n)),
        Expr::Bool(b) => Ok(Value::Bool(*b)),
        Expr::Var(x) => env.lookup(x).ok_or_else(|| EvalError::Unbound(x.clone())),
        Expr::Add(a, b) => {
            let n = as_num(e, eval(env, a)?)?;
            let m = as_num(e, eval(env, b)?)?;
            n.checked_add(m)
                .map(Value::Num)
                .ok_or_else(|| EvalError::Overflow { expr: e.clone() })
        }
        Expr::Eq(a, b) => match (eval(env, a)?, eval(env, b)?) {
            (Value::Num(n), Value::Num(m)) => Ok(Value::Bool(n == m)),
            (Value::Bool(p), Value::Bool(q)) => Ok(Value::Bool(p == q)),
            // Comparing a number with a boolean has no meaning in Arith.
            (_, v) => Err(EvalError::Stuck {
                expr: e.clone(),
                value: v,
            }),
        },
        Expr::If(c, a, b) => match eval(env, c)? {
            // Only the branch that is taken is evaluated.
            Value::Bool(true) => eval(env, a),
            Value::Bool(false) => eval(env, b),
            v => Err(EvalError::Stuck {
                expr: e.clone(),
                value: v,
            }),
        },
        Expr::Let(x, a, b) => {
            let v = eval(env, a)?;
            eval(&env.extend(x, v), b)
        }
    }
}
// ANCHOR_END: eval

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse;

    fn run(src: &str) -> Result<Value, EvalError> {
        eval(&Env::new(), &parse(src).unwrap())
    }

    #[test]
    fn evaluates_well_typed_programs() {
        assert_eq!(run("1 + 2 + 3"), Ok(Value::Num(6)));
        assert_eq!(
            run("let x = 3 in if x == 3 then x + 1 else 0"),
            Ok(Value::Num(4))
        );
        assert_eq!(run("true == (1 == 2)"), Ok(Value::Bool(false)));
        assert_eq!(run("let x = true in let x = 5 in x + 1"), Ok(Value::Num(6)));
    }

    #[test]
    fn ill_typed_programs_may_get_stuck() {
        assert!(matches!(run("1 + true"), Err(EvalError::Stuck { .. })));
        assert!(matches!(
            run("if 0 then 1 else 2"),
            Err(EvalError::Stuck { .. })
        ));
        assert!(matches!(run("x"), Err(EvalError::Unbound(_))));
    }

    #[test]
    fn some_ill_typed_programs_run_fine() {
        // The type checker rejects this program, but the branch that would
        // go wrong is never taken. Type systems are conservative.
        assert_eq!(run("if true then 1 else false"), Ok(Value::Num(1)));
    }

    #[test]
    fn overflow_is_not_a_type_error() {
        let big = u64::MAX;
        assert!(matches!(
            run(&format!("{big} + 1")),
            Err(EvalError::Overflow { .. })
        ));
    }
}
