//! Small-step call-by-value evaluation, in two forms.
//!
//! - [`successors`] transcribes the *relation* `Step` of
//!   `code/lean/Book/Ch09/Semantics.lean`: it tries every rule independently
//!   and returns every step that some rule allows. It is the specification.
//! - [`step`] is the *evaluator*: a function that returns the one step that
//!   call-by-value takes, if any. It is what an interpreter would run.
//!
//! Determinism says that the relation allows at most one step, and that the two
//! agree; the property tests check it.

use crate::subst::instantiate;
use crate::syntax::Term;
use std::fmt;

/// The evaluation rules, named as in the chapter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rule {
    AppL,
    AppR,
    Beta,
    If,
    IfTrue,
    IfFalse,
    AddL,
    AddR,
    AddLit,
    IsZero,
    IsZeroZero,
    IsZeroSucc,
}

impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Rule::AppL => "AppL",
            Rule::AppR => "AppR",
            Rule::Beta => "Beta",
            Rule::If => "If",
            Rule::IfTrue => "IfTrue",
            Rule::IfFalse => "IfFalse",
            Rule::AddL => "AddL",
            Rule::AddR => "AddR",
            Rule::AddLit => "AddLit",
            Rule::IsZero => "IsZero",
            Rule::IsZeroZero => "IsZeroZero",
            Rule::IsZeroSucc => "IsZeroSucc",
        };
        write!(f, "E-{name}")
    }
}

// ANCHOR: step_struct
/// One step `t ⟶ result`, with its derivation: the congruence rules from the
/// outside in, ending with the computation rule that did the work.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Step {
    pub derivation: Vec<Rule>,
    pub result: Term,
}
// ANCHOR_END: step_struct

impl Step {
    /// A computation rule: a derivation with a single rule.
    fn axiom(rule: Rule, result: Term) -> Step {
        Step {
            derivation: vec![rule],
            result,
        }
    }

    /// Puts a congruence rule below this step, rebuilding the enclosing term.
    fn under(self, rule: Rule, rebuild: impl FnOnce(Term) -> Term) -> Step {
        let mut derivation = vec![rule];
        derivation.extend(self.derivation);
        Step {
            derivation,
            result: rebuild(self.result),
        }
    }

    /// The derivation written like the Lean proof term: `E-AppR(E-Beta)`.
    pub fn derivation_string(&self) -> String {
        let mut s = String::new();
        for (k, rule) in self.derivation.iter().enumerate() {
            if k > 0 {
                s.push('(');
            }
            s.push_str(&rule.to_string());
        }
        s.push_str(&")".repeat(self.derivation.len() - 1));
        s
    }
}

// ANCHOR: is_value
/// Values: λ-abstractions, booleans and literals.
pub fn is_value(t: &Term) -> bool {
    matches!(t, Term::Lam(..) | Term::True | Term::False | Term::Lit(_))
}
// ANCHOR_END: is_value

fn boxed(t: &Term) -> Box<Term> {
    Box::new(t.clone())
}

// ANCHOR: successors
/// Every step that the rules allow from `t`: one `if` per rule, each checking
/// exactly that rule's premises.
pub fn successors(t: &Term) -> Vec<Step> {
    let mut out = Vec::new();
    match t {
        Term::App(f, a) => {
            // E-AppL: f ⟶ f'
            for s in successors(f) {
                out.push(s.under(Rule::AppL, |f2| Term::App(Box::new(f2), boxed(a))));
            }
            // E-AppR: f is a value and a ⟶ a'
            if is_value(f) {
                for s in successors(a) {
                    out.push(
                        s.under(Rule::AppR, |a2| Term::App(boxed(f), Box::new(a2))),
                    );
                }
            }
            // E-Beta: f is a λ and a is a value
            if let (Term::Lam(_, body), true) = (&**f, is_value(a)) {
                out.push(Step::axiom(Rule::Beta, instantiate(body, a)));
            }
        }
        Term::If(c, then_branch, else_branch) => {
            // E-If: c ⟶ c'
            for s in successors(c) {
                out.push(s.under(Rule::If, |c2| {
                    Term::If(Box::new(c2), boxed(then_branch), boxed(else_branch))
                }));
            }
            // E-IfTrue and E-IfFalse
            match **c {
                Term::True => {
                    out.push(Step::axiom(Rule::IfTrue, (**then_branch).clone()))
                }
                Term::False => {
                    out.push(Step::axiom(Rule::IfFalse, (**else_branch).clone()))
                }
                _ => {}
            }
        }
        Term::Add(a, b) => {
            // E-AddL: a ⟶ a'
            for s in successors(a) {
                out.push(s.under(Rule::AddL, |a2| Term::Add(Box::new(a2), boxed(b))));
            }
            // E-AddR: a is a value and b ⟶ b'
            if is_value(a) {
                for s in successors(b) {
                    out.push(
                        s.under(Rule::AddR, |b2| Term::Add(boxed(a), Box::new(b2))),
                    );
                }
            }
            // E-AddLit: two literals
            if let (Term::Lit(m), Term::Lit(n)) = (&**a, &**b) {
                out.push(Step::axiom(Rule::AddLit, Term::Lit(m + n)));
            }
        }
        Term::IsZero(n) => {
            // E-IsZero: n ⟶ n'
            for s in successors(n) {
                out.push(s.under(Rule::IsZero, |n2| Term::IsZero(Box::new(n2))));
            }
            // E-IsZeroZero and E-IsZeroSucc
            match **n {
                Term::Lit(0) => out.push(Step::axiom(Rule::IsZeroZero, Term::True)),
                Term::Lit(_) => out.push(Step::axiom(Rule::IsZeroSucc, Term::False)),
                _ => {}
            }
        }
        // No rule has a variable or a value on its left-hand side.
        Term::Var(_) | Term::Lam(..) | Term::True | Term::False | Term::Lit(_) => {}
    }
    out
}
// ANCHOR_END: successors

// ANCHOR: step
/// The evaluator: the step that call-by-value takes from `t`, or `None` if `t`
/// is a value or stuck. Each case first finds the leftmost subterm that is not
/// yet a value, which is what makes it a function.
pub fn step(t: &Term) -> Option<Step> {
    match t {
        Term::App(f, a) if !is_value(f) => {
            step(f).map(|s| s.under(Rule::AppL, |f2| Term::App(Box::new(f2), boxed(a))))
        }
        Term::App(f, a) if !is_value(a) => {
            step(a).map(|s| s.under(Rule::AppR, |a2| Term::App(boxed(f), Box::new(a2))))
        }
        Term::App(f, a) => match &**f {
            Term::Lam(_, body) => Some(Step::axiom(Rule::Beta, instantiate(body, a))),
            _ => None, // a value that is not a function, applied: stuck
        },
        Term::If(c, t1, t2) if !is_value(c) => step(c).map(|s| {
            s.under(Rule::If, |c2| Term::If(Box::new(c2), boxed(t1), boxed(t2)))
        }),
        Term::If(c, t1, t2) => match **c {
            Term::True => Some(Step::axiom(Rule::IfTrue, (**t1).clone())),
            Term::False => Some(Step::axiom(Rule::IfFalse, (**t2).clone())),
            _ => None, // a condition that is not a boolean: stuck
        },
        Term::Add(a, b) if !is_value(a) => {
            step(a).map(|s| s.under(Rule::AddL, |a2| Term::Add(Box::new(a2), boxed(b))))
        }
        Term::Add(a, b) if !is_value(b) => {
            step(b).map(|s| s.under(Rule::AddR, |b2| Term::Add(boxed(a), Box::new(b2))))
        }
        Term::Add(a, b) => match (&**a, &**b) {
            (Term::Lit(m), Term::Lit(n)) => {
                Some(Step::axiom(Rule::AddLit, Term::Lit(m + n)))
            }
            _ => None, // adding something that is not a number: stuck
        },
        Term::IsZero(n) if !is_value(n) => {
            step(n).map(|s| s.under(Rule::IsZero, |n2| Term::IsZero(Box::new(n2))))
        }
        Term::IsZero(n) => match **n {
            Term::Lit(0) => Some(Step::axiom(Rule::IsZeroZero, Term::True)),
            Term::Lit(_) => Some(Step::axiom(Rule::IsZeroSucc, Term::False)),
            _ => None,
        },
        // Variables (free ones: a closed term has none at the top) and values.
        Term::Var(_) | Term::Lam(..) | Term::True | Term::False | Term::Lit(_) => None,
    }
}
// ANCHOR_END: step

/// How a run ended.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    /// The run reached a value.
    Value(Term),
    /// The run reached a term that is not a value and cannot step.
    Stuck(Term),
    /// The fuel ran out first.
    OutOfFuel(Term),
}

/// Runs the evaluator for at most `fuel` steps, recording every step.
pub fn run(t: &Term, fuel: usize) -> (Vec<Step>, Outcome) {
    let mut trace = Vec::new();
    let mut current = t.clone();
    for _ in 0..fuel {
        if is_value(&current) {
            return (trace, Outcome::Value(current));
        }
        match step(&current) {
            Some(s) => {
                current = s.result.clone();
                trace.push(s);
            }
            None => return (trace, Outcome::Stuck(current)),
        }
    }
    let outcome = if is_value(&current) {
        Outcome::Value(current)
    } else {
        Outcome::OutOfFuel(current)
    };
    (trace, outcome)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::{Ty, add, app, is_zero, ite, lam, twice};

    fn add_two() -> Term {
        lam(Ty::Nat, add(Term::Var(0), Term::Lit(2)))
    }

    #[test]
    fn twice_add_two_three_is_seven() {
        let program = app(app(twice(), add_two()), Term::Lit(3));
        let (trace, outcome) = run(&program, 100);
        assert_eq!(outcome, Outcome::Value(Term::Lit(7)));
        let rules: Vec<String> = trace.iter().map(Step::derivation_string).collect();
        assert_eq!(
            rules,
            [
                "E-AppL(E-Beta)",
                "E-Beta",
                "E-AppR(E-Beta)",
                "E-AppR(E-AddLit)",
                "E-Beta",
                "E-AddLit"
            ]
        );
    }

    #[test]
    fn ill_typed_terms_get_stuck() {
        let (trace, outcome) = run(&add(Term::True, Term::Lit(1)), 10);
        assert!(trace.is_empty());
        assert_eq!(outcome, Outcome::Stuck(add(Term::True, Term::Lit(1))));
        let (_, outcome) = run(&app(Term::Lit(3), Term::True), 10);
        assert!(matches!(outcome, Outcome::Stuck(_)));
    }

    #[test]
    fn the_relation_and_the_function_agree() {
        let terms = [
            app(app(twice(), add_two()), Term::Lit(3)),
            ite(
                is_zero(add(Term::Lit(0), Term::Lit(0))),
                Term::Lit(1),
                Term::Lit(2),
            ),
            add(Term::True, Term::Lit(1)),
            is_zero(Term::Lit(5)),
        ];
        for t in &terms {
            let all = successors(t);
            assert!(all.len() <= 1, "{t} has {} successors", all.len());
            assert_eq!(all.first(), step(t).as_ref());
        }
    }

    #[test]
    fn self_application_diverges_without_types() {
        // (λ:bool. #0 #0) (λ:bool. #0 #0) is ill typed, and steps to itself.
        let delta = lam(Ty::Bool, app(Term::Var(0), Term::Var(0)));
        let omega = app(delta.clone(), delta);
        let s = step(&omega).expect("a β-redex");
        assert_eq!(s.result, omega);
        assert!(matches!(run(&omega, 50).1, Outcome::OutOfFuel(_)));
    }
}
