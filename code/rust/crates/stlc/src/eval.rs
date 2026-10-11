//! An environment-based evaluator. A `λ` evaluates to a *closure*: the code of
//! the function together with the values of its free variables, which is how
//! Rust represents closures too.

use crate::syntax::Term;
use std::fmt;
use std::rc::Rc;

// ANCHOR: value
/// The results of evaluation.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Unit,
    Bool(bool),
    Nat(u64),
    Pair(Rc<Value>, Rc<Value>),
    Inl(Rc<Value>),
    Inr(Rc<Value>),
    Closure(Rc<Closure>),
}

/// A function value: a parameter, a body, and the captured variables.
#[derive(Debug, PartialEq)]
pub struct Closure {
    pub param: String,
    pub body: Term,
    /// The values of the body's free variables (other than the parameter),
    /// copied from the environment when the closure was created.
    pub captured: Env,
}
// ANCHOR_END: value

/// An environment: values for variables, searched from the right.
pub type Env = Vec<(String, Value)>;

// ANCHOR: stuck
/// Evaluation got stuck: no rule applies. On terms accepted by the type
/// checker this never happens (that is the *progress* theorem of Chapter 9).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stuck(pub String);
// ANCHOR_END: stuck

impl fmt::Display for Stuck {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "stuck: {}", self.0)
    }
}

impl std::error::Error for Stuck {}

fn lookup(env: &Env, x: &str) -> Result<Value, Stuck> {
    env.iter()
        .rev()
        .find(|(y, _)| y == x)
        .map(|(_, v)| v.clone())
        .ok_or_else(|| Stuck(format!("unbound variable `{x}`")))
}

fn extend(env: &Env, x: &str, v: Value) -> Env {
    let mut env = env.clone();
    env.push((x.to_string(), v));
    env
}

// ANCHOR: make_closure
/// Builds the closure for `λparam. body` in `env`, capturing only the free
/// variables of the λ, as a Rust closure does.
fn make_closure(env: &Env, param: &str, body: &Term) -> Result<Value, Stuck> {
    let lam = Term::Lam(param.to_string(), None, Box::new(body.clone()));
    let mut captured = Vec::new();
    for x in lam.free_vars() {
        captured.push((x.clone(), lookup(env, &x)?));
    }
    Ok(Value::Closure(Rc::new(Closure {
        param: param.to_string(),
        body: body.clone(),
        captured,
    })))
}
// ANCHOR_END: make_closure

// ANCHOR: apply
/// Calls a function value: evaluate the body in the captured environment
/// extended with the argument.
pub fn apply(f: &Value, arg: Value) -> Result<Value, Stuck> {
    match f {
        Value::Closure(c) => eval(&extend(&c.captured, &c.param, arg), &c.body),
        other => Err(Stuck(format!("cannot call {other}: it is not a function"))),
    }
}
// ANCHOR_END: apply

// ANCHOR: eval
/// Evaluates a term in an environment, call-by-value.
pub fn eval(env: &Env, e: &Term) -> Result<Value, Stuck> {
    use Term::*;
    match e {
        Var(x) => lookup(env, x),
        Lam(x, _, body) => make_closure(env, x, body),
        App(f, a) => {
            let f = eval(env, f)?;
            let a = eval(env, a)?; // call-by-value: the argument first
            apply(&f, a)
        }
        Ann(e, _) => eval(env, e),
        Let(x, e1, e2) => {
            let v = eval(env, e1)?;
            eval(&extend(env, x, v), e2)
        }
        Unit => Ok(Value::Unit),
        Bool(b) => Ok(Value::Bool(*b)),
        If(c, a, b) => match eval(env, c)? {
            Value::Bool(true) => eval(env, a),
            Value::Bool(false) => eval(env, b),
            other => Err(Stuck(format!("`if` on {other}, which is not a boolean"))),
        },
        Nat(n) => Ok(Value::Nat(*n)),
        Succ(n) => match eval(env, n)? {
            Value::Nat(k) => Ok(Value::Nat(k + 1)),
            other => Err(Stuck(format!("`succ` of {other}, which is not a number"))),
        },
        Iter(n, z, s) => match eval(env, n)? {
            Value::Nat(k) => {
                let s = eval(env, s)?;
                let mut acc = eval(env, z)?;
                for _ in 0..k {
                    acc = apply(&s, acc)?;
                }
                Ok(acc)
            }
            other => Err(Stuck(format!("`iter` on {other}, which is not a number"))),
        },
        Pair(a, b) => Ok(Value::Pair(Rc::new(eval(env, a)?), Rc::new(eval(env, b)?))),
        Fst(p) | Snd(p) => match eval(env, p)? {
            Value::Pair(a, b) => {
                let v = if matches!(e, Fst(_)) { a } else { b };
                Ok((*v).clone())
            }
            other => Err(Stuck(format!("projection of {other}, which is not a pair"))),
        },
        Inl(a) => Ok(Value::Inl(Rc::new(eval(env, a)?))),
        Inr(b) => Ok(Value::Inr(Rc::new(eval(env, b)?))),
        Case(scrut, x, l, y, r) => match eval(env, scrut)? {
            Value::Inl(v) => eval(&extend(env, x, (*v).clone()), l),
            Value::Inr(v) => eval(&extend(env, y, (*v).clone()), r),
            other => Err(Stuck(format!("`case` on {other}, which is not a sum"))),
        },
    }
}
// ANCHOR_END: eval

/// Evaluates a closed term.
pub fn run(e: &Term) -> Result<Value, Stuck> {
    eval(&Vec::new(), e)
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Unit => write!(f, "()"),
            Value::Bool(b) => write!(f, "{b}"),
            Value::Nat(n) => write!(f, "{n}"),
            Value::Pair(a, b) => write!(f, "({a}, {b})"),
            Value::Inl(v) => write!(f, "inl {v}"),
            Value::Inr(v) => write!(f, "inr {v}"),
            Value::Closure(c) => {
                write!(f, "<closure λ{}. {}", c.param, c.body)?;
                if !c.captured.is_empty() {
                    let caps: Vec<String> = c
                        .captured
                        .iter()
                        .map(|(x, v)| format!("{x} = {v}"))
                        .collect();
                    write!(f, " | {}", caps.join(", "))?;
                }
                write!(f, ">")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse_term;

    fn value_of(src: &str) -> Result<Value, Stuck> {
        run(&parse_term(src).unwrap())
    }

    #[test]
    fn arithmetic_with_iter() {
        let add = "λm: Nat. λn: Nat. iter m n (λk: Nat. succ k)";
        assert_eq!(value_of(&format!("({add}) 3 4")), Ok(Value::Nat(7)));
        let twice = "λf: Nat → Nat. λx: Nat. f (f x)";
        assert_eq!(
            value_of(&format!("({twice}) (({add}) 3) 4")),
            Ok(Value::Nat(10))
        );
    }

    #[test]
    fn closures_capture_only_free_variables() {
        let v = value_of(
            "let k = 5 in let unused = true in λx: Nat. iter k x (λn. succ n)",
        )
        .unwrap();
        let Value::Closure(c) = &v else { panic!() };
        assert_eq!(c.captured, vec![("k".to_string(), Value::Nat(5))]);
        assert_eq!(v.to_string(), "<closure λx. iter k x (λn. succ n) | k = 5>");
    }

    #[test]
    fn lexical_scope() {
        // The closure sees the k of its definition, not the k of the call.
        let src =
            "let k = 1 in let f = λx: Nat. iter k x (λn. succ n) in let k = 100 in f 0";
        assert_eq!(value_of(src), Ok(Value::Nat(1)));
    }

    #[test]
    fn sums_and_pairs() {
        let src = "case (inl 4 : Nat + Bool) of inl n => (n, true) | inr b => (0, b)";
        assert_eq!(value_of(src).unwrap().to_string(), "(4, true)");
    }

    #[test]
    fn ill_typed_terms_get_stuck() {
        assert!(value_of("3 4").is_err());
        assert!(value_of("if 0 then 1 else 2").is_err());
        assert!(value_of("fst true").is_err());
    }
}
