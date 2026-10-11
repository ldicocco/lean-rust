//! Church encodings: booleans, pairs, numerals and arithmetic as λ-terms, and
//! the fixed-point combinators.

use crate::parse::parse;
use crate::term::{Term, app, lam, var};

fn p(src: &str) -> Term {
    parse(src).expect("the encodings in this module are well formed")
}

// ANCHOR: with
/// Parses `src` and replaces its free variables by the given terms. The terms
/// are closed, so the substitution never has to rename anything: this is how
/// we write `and` in terms of `false` without a `let` in the calculus.
fn with(src: &str, defs: &[(&str, Term)]) -> Term {
    defs.iter().fold(p(src), |t, (x, def)| t.subst(x, def))
}
// ANCHOR_END: with

// ANCHOR: booleans
/// `true = λt. λf. t`: of two alternatives, choose the first.
pub fn tru() -> Term {
    p("λt. λf. t")
}

/// `false = λt. λf. f`: of two alternatives, choose the second.
pub fn fls() -> Term {
    p("λt. λf. f")
}

/// `if = λb. λthen. λelse. b then else`: a boolean *is* its own `if`.
pub fn ite() -> Term {
    p("λb. λthen. λelse. b then else")
}

/// `and = λa. λb. a b false`
pub fn and() -> Term {
    with("λa. λb. a b false", &[("false", fls())])
}

/// `or = λa. λb. a true b`
pub fn or() -> Term {
    with("λa. λb. a true b", &[("true", tru())])
}

/// `not = λa. a false true`
pub fn not() -> Term {
    with("λa. a false true", &[("false", fls()), ("true", tru())])
}
// ANCHOR_END: booleans

// ANCHOR: pairs
/// `pair = λa. λb. λs. s a b`: a pair waits for a selector `s`.
pub fn pair() -> Term {
    p("λa. λb. λs. s a b")
}

/// `fst = λp. p true`
pub fn fst() -> Term {
    with("λp. p true", &[("true", tru())])
}

/// `snd = λp. p false`
pub fn snd() -> Term {
    with("λp. p false", &[("false", fls())])
}
// ANCHOR_END: pairs

// ANCHOR: numerals
/// The Church numeral `n = λf. λx. f (f (... (f x)))`, with `n` copies of `f`.
pub fn numeral(n: u64) -> Term {
    let mut body = var("x");
    for _ in 0..n {
        body = app(var("f"), body);
    }
    lam("f", lam("x", body))
}

/// `succ = λn. λf. λx. f (n f x)`: one more application of `f`.
pub fn succ() -> Term {
    p("λn. λf. λx. f (n f x)")
}

/// `plus = λm. λn. λf. λx. m f (n f x)`: `m` applications after `n`.
pub fn plus() -> Term {
    p("λm. λn. λf. λx. m f (n f x)")
}

/// `times = λm. λn. λf. m (n f)`: repeat "apply f n times", m times.
pub fn times() -> Term {
    p("λm. λn. λf. m (n f)")
}

/// `power = λm. λn. n m`: `n m` composes `m` with itself n times, and `m`
/// turns `f` into `f` repeated m times, so the result repeats `f` m^n times.
pub fn power() -> Term {
    p("λm. λn. n m")
}

/// `iszero = λn. n (λz. false) true`: zero applications leave `true`.
pub fn iszero() -> Term {
    with(
        "λn. n (λz. false) true",
        &[("false", fls()), ("true", tru())],
    )
}
// ANCHOR_END: numerals

// ANCHOR: pred
/// The predecessor, by Kleene's trick: count up pairs `(k, k + 1)` starting
/// from `(0, 0)`; after n steps the first component is n - 1.
/// `pred = λn. fst (n (λq. pair (snd q) (succ (snd q))) (pair 0 0))`
pub fn pred() -> Term {
    with(
        "λn. fst (n (λq. pair (snd q) (succ (snd q))) (pair zero zero))",
        &[
            ("pair", pair()),
            ("fst", fst()),
            ("snd", snd()),
            ("succ", succ()),
            ("zero", numeral(0)),
        ],
    )
}

/// `sub = λm. λn. n pred m`: truncated subtraction (`2 - 5 = 0`).
pub fn sub() -> Term {
    with("λm. λn. n pred m", &[("pred", pred())])
}
// ANCHOR_END: pred

// ANCHOR: fixpoints
/// `Ω = (λx. x x) (λx. x x)`: reduces to itself, forever.
pub fn omega() -> Term {
    p("(λx. x x) (λx. x x)")
}

/// Curry's `Y = λf. (λx. f (x x)) (λx. f (x x))`. In two steps `Y g`
/// reduces to `g W`, where `W` is the term `Y g` reached after one step: so
/// `W` and `g W` are equal up to reduction, and `W` is a fixed point of `g`.
pub fn y() -> Term {
    p("λf. (λx. f (x x)) (λx. f (x x))")
}

/// `Z = λf. (λx. f (λv. x x v)) (λx. f (λv. x x v))`: the call-by-value fixed
/// point combinator. The extra `λv` delays the self-application.
pub fn z() -> Term {
    p("λf. (λx. f (λv. x x v)) (λx. f (λv. x x v))")
}
// ANCHOR_END: fixpoints

// ANCHOR: factorial
/// The body of factorial, abstracted over the recursive call `fact`:
/// `λfact. λn. if (iszero n) 1 (times n (fact (pred n)))`.
pub fn fact_step() -> Term {
    with(
        "λfact. λn. if (iszero n) one (times n (fact (pred n)))",
        &factorial_helpers(),
    )
}

/// The same body for call-by-value: the branches are wrapped in `λd. ...` so
/// that only the chosen one runs, and the result is applied to a dummy.
pub fn fact_step_cbv() -> Term {
    with(
        "λfact. λn. if (iszero n) (λd. one) (λd. times n (fact (pred n))) (λd. d)",
        &factorial_helpers(),
    )
}

fn factorial_helpers() -> [(&'static str, Term); 5] {
    [
        ("if", ite()),
        ("iszero", iszero()),
        ("times", times()),
        ("pred", pred()),
        ("one", numeral(1)),
    ]
}
// ANCHOR_END: factorial

// ANCHOR: decode
/// Reads a numeral back from a normal form `λf. λx. f (f (... x))` (with any
/// names for `f` and `x`).
pub fn decode_numeral(t: &Term) -> Option<u64> {
    let Term::Lam(f, inner) = t else { return None };
    let Term::Lam(x, body) = &**inner else {
        return None;
    };
    if f == x {
        return None;
    }
    // Count the applications of f on the way down to x.
    let mut n = 0;
    let mut current: &Term = body;
    loop {
        match current {
            Term::Var(y) if y == x => return Some(n),
            Term::App(g, rest) if matches!(&**g, Term::Var(h) if h == f) => {
                n += 1;
                current = rest;
            }
            _ => return None,
        }
    }
}

/// Reads a boolean back from a normal form.
pub fn decode_bool(t: &Term) -> Option<bool> {
    if t.alpha_eq(&tru()) {
        Some(true)
    } else if t.alpha_eq(&fls()) {
        Some(false)
    } else {
        None
    }
}
// ANCHOR_END: decode

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reduce::{Strategy, reduce};
    use crate::term::apps;

    fn eval_nat(t: Term) -> u64 {
        let r = reduce(&t, Strategy::NormalOrder, 100_000);
        assert!(r.finished, "did not finish: {}", r.term);
        decode_numeral(&r.term).unwrap_or_else(|| panic!("not a numeral: {}", r.term))
    }

    fn eval_bool(t: Term) -> bool {
        let r = reduce(&t, Strategy::NormalOrder, 10_000);
        decode_bool(&r.term).unwrap()
    }

    #[test]
    fn encodings_are_closed() {
        for t in [
            tru(),
            fls(),
            ite(),
            and(),
            or(),
            not(),
            pair(),
            fst(),
            snd(),
            succ(),
            plus(),
            times(),
            power(),
            iszero(),
            pred(),
            sub(),
            y(),
            z(),
            fact_step(),
            fact_step_cbv(),
        ] {
            assert!(t.is_closed(), "{t}");
        }
    }

    #[test]
    fn helpers_are_spelled_out() {
        assert_eq!(fst().to_string(), "λp. p (λt. λf. t)");
        assert_eq!(not().to_string(), "λa. a (λt. λf. f) (λt. λf. t)");
    }

    #[test]
    fn arithmetic() {
        let n = numeral;
        assert_eq!(eval_nat(app(succ(), n(2))), 3);
        assert_eq!(eval_nat(apps(plus(), [n(2), n(3)])), 5);
        assert_eq!(eval_nat(apps(times(), [n(2), n(3)])), 6);
        assert_eq!(eval_nat(apps(power(), [n(2), n(3)])), 8);
        assert_eq!(eval_nat(app(pred(), n(3))), 2);
        assert_eq!(eval_nat(app(pred(), n(0))), 0);
        assert_eq!(eval_nat(apps(sub(), [n(5), n(2)])), 3);
        assert_eq!(eval_nat(apps(sub(), [n(2), n(5)])), 0);
    }

    #[test]
    fn booleans_and_pairs() {
        assert!(!eval_bool(apps(and(), [tru(), fls()])));
        assert!(eval_bool(apps(or(), [fls(), tru()])));
        assert!(eval_bool(app(not(), fls())));
        assert!(eval_bool(app(iszero(), numeral(0))));
        assert!(!eval_bool(app(iszero(), numeral(2))));
        let pr = apps(pair(), [numeral(1), numeral(2)]);
        assert_eq!(eval_nat(app(fst(), pr.clone())), 1);
        assert_eq!(eval_nat(app(snd(), pr)), 2);
        assert_eq!(eval_nat(apps(ite(), [fls(), numeral(1), numeral(2)])), 2);
    }

    #[test]
    fn factorial_with_y_under_normal_order() {
        assert_eq!(eval_nat(apps(y(), [fact_step(), numeral(3)])), 6);
    }

    #[test]
    fn factorial_with_z_under_call_by_value() {
        let t = apps(z(), [fact_step_cbv(), numeral(3)]);
        let r = reduce(&t, Strategy::CallByValue, 100_000);
        assert!(r.finished);
        // Call-by-value stops at a λ; normal order finishes the job.
        assert_eq!(eval_nat(r.term), 6);
        // Y loops under call-by-value.
        let looping = apps(y(), [fact_step_cbv(), numeral(3)]);
        assert!(!reduce(&looping, Strategy::CallByValue, 500).finished);
    }

    #[test]
    fn decoding() {
        assert_eq!(decode_numeral(&numeral(4)), Some(4));
        assert_eq!(decode_numeral(&parse("λg. λy. g (g y)").unwrap()), Some(2));
        assert_eq!(decode_numeral(&parse("λf. λx. x f").unwrap()), None);
        assert_eq!(decode_bool(&parse("λa. λb. b").unwrap()), Some(false));
    }
}
