//! β-reduction on named terms, with three strategies and a step limit.

use crate::term::{Term, app, lam};

// ANCHOR: strategy
/// Which redex to contract when there are several.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Strategy {
    /// Leftmost-outermost redex first, also under `λ`. Finds the normal form
    /// whenever there is one.
    NormalOrder,
    /// Leftmost-outermost, but never under `λ` and never inside an argument:
    /// arguments are passed unevaluated.
    CallByName,
    /// Arguments are reduced to values before the call, never under `λ`.
    /// This is what Rust does.
    CallByValue,
}
// ANCHOR_END: strategy

/// In call-by-value, the values are the abstractions (and, for open terms, the
/// variables).
fn is_value(t: &Term) -> bool {
    matches!(t, Term::Lam(..) | Term::Var(_))
}

// ANCHOR: step
/// One step of β-reduction with the given strategy, or `None` if the strategy
/// finds no redex to contract.
pub fn step(t: &Term, strategy: Strategy) -> Option<Term> {
    match t {
        Term::Var(_) => None,
        Term::Lam(x, body) => match strategy {
            Strategy::NormalOrder => step(body, strategy).map(|b| lam(x, b)),
            Strategy::CallByName | Strategy::CallByValue => None,
        },
        Term::App(f, a) => {
            if let Term::Lam(x, body) = &**f {
                // A redex (λx. body) a. Call-by-value contracts it only once
                // the argument is a value.
                if strategy != Strategy::CallByValue || is_value(a) {
                    return Some(body.subst(x, a));
                }
                return step(a, strategy).map(|a2| app((**f).clone(), a2));
            }
            if let Some(f2) = step(f, strategy) {
                return Some(app(f2, (**a).clone()));
            }
            match strategy {
                Strategy::CallByName => None,
                _ => step(a, strategy).map(|a2| app((**f).clone(), a2)),
            }
        }
    }
}
// ANCHOR_END: step

// ANCHOR: reduction
/// The result of running a reducer with a step limit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reduction {
    /// The last term reached.
    pub term: Term,
    /// The number of steps taken.
    pub steps: usize,
    /// `true` if no step was possible at the end; `false` if the fuel ran out.
    pub finished: bool,
}

/// Reduces `t` with `strategy` until no step applies, or until `fuel` steps
/// have been taken.
pub fn reduce(t: &Term, strategy: Strategy, fuel: usize) -> Reduction {
    let mut term = t.clone();
    let mut steps = 0;
    while steps < fuel {
        match step(&term, strategy) {
            Some(next) => {
                term = next;
                steps += 1;
            }
            None => {
                return Reduction {
                    term,
                    steps,
                    finished: true,
                };
            }
        }
    }
    let finished = step(&term, strategy).is_none();
    Reduction {
        term,
        steps,
        finished,
    }
}
// ANCHOR_END: reduction

/// The sequence of terms visited, starting with `t`, for at most `fuel` steps.
pub fn trace(t: &Term, strategy: Strategy, fuel: usize) -> Vec<Term> {
    let mut terms = vec![t.clone()];
    while terms.len() <= fuel {
        match step(terms.last().unwrap(), strategy) {
            Some(next) => terms.push(next),
            None => break,
        }
    }
    terms
}

/// Is `t` in β-normal form (no redex anywhere)?
pub fn is_normal(t: &Term) -> bool {
    step(t, Strategy::NormalOrder).is_none()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse;

    fn p(s: &str) -> Term {
        parse(s).unwrap()
    }

    #[test]
    fn a_single_beta_step() {
        let t = p("(λx. λy. x) a b");
        let r = trace(&t, Strategy::NormalOrder, 10);
        let shown: Vec<String> = r.iter().map(|t| t.to_string()).collect();
        assert_eq!(shown, ["(λx. λy. x) a b", "(λy. a) b", "a"]);
    }

    #[test]
    fn strategies_disagree_on_termination() {
        let t = p("(λx. λy. y) ((λx. x x) (λx. x x))");
        let normal = reduce(&t, Strategy::NormalOrder, 100);
        assert!(normal.finished);
        assert_eq!(normal.term, p("λy. y"));
        let by_name = reduce(&t, Strategy::CallByName, 100);
        assert_eq!(by_name.term, p("λy. y"));
        let by_value = reduce(&t, Strategy::CallByValue, 100);
        assert!(!by_value.finished);
    }

    #[test]
    fn weak_strategies_stop_at_lambdas() {
        let t = p("λx. (λy. y) x");
        assert_eq!(step(&t, Strategy::CallByValue), None);
        assert_eq!(step(&t, Strategy::CallByName), None);
        assert_eq!(step(&t, Strategy::NormalOrder), Some(p("λx. x")));
    }

    #[test]
    fn call_by_value_reduces_the_argument_first() {
        let t = p("(λx. x x) ((λy. y) z)");
        assert_eq!(step(&t, Strategy::CallByValue), Some(p("(λx. x x) z")));
        assert_eq!(
            step(&t, Strategy::CallByName),
            Some(p("(λy. y) z ((λy. y) z)"))
        );
    }

    #[test]
    fn capture_is_avoided_during_reduction() {
        // (λx. λy. x) y z must reduce to y, not z.
        let r = reduce(&p("(λx. λy. x) y z"), Strategy::NormalOrder, 10);
        assert_eq!(r.term, p("y"));
    }

    #[test]
    fn normal_forms() {
        assert!(is_normal(&p("λx. x")));
        assert!(is_normal(&p("x (λy. y z)")));
        assert!(!is_normal(&p("λx. (λy. y) x")));
    }
}
