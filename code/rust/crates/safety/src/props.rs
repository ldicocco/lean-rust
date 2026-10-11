//! Property-based tests of the safety theorems: progress, preservation and
//! determinism, checked along the whole run of many random well-typed terms,
//! with a shrinker that turns a failing term into a small one.

use crate::eval::{Step, is_value, step, successors};
use crate::generate::{gen_term, gen_type};
use crate::rng::Rng;
use crate::syntax::{Term, Ty};
use crate::typing::{Rules, TypeError, type_of_with};
use std::fmt;

// ANCHOR: violation
/// A counterexample to one of the theorems.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Violation {
    /// The generator produced a term that does not have the promised type.
    Generator {
        term: Term,
        ty: Ty,
        found: Result<Ty, TypeError>,
    },
    /// Progress: a well-typed term that is neither a value nor able to step.
    Progress { state: Term, ty: Ty },
    /// Preservation: a step changed the type (or destroyed it).
    Preservation {
        before: Term,
        after: Term,
        ty: Ty,
        found: Result<Ty, TypeError>,
    },
    /// Determinism: two different steps, or the evaluator disagrees with the
    /// rules.
    Determinism { state: Term, steps: Vec<Step> },
    /// The run did not reach a value within the fuel.
    OutOfFuel { state: Term },
}
// ANCHOR_END: violation

impl Violation {
    /// The name of the property that failed.
    pub fn theorem(&self) -> &'static str {
        match self {
            Violation::Generator { .. } => "the generator's claim",
            Violation::Progress { .. } => "progress",
            Violation::Preservation { .. } => "preservation",
            Violation::Determinism { .. } => "determinism",
            Violation::OutOfFuel { .. } => "termination within the fuel",
        }
    }
}

impl fmt::Display for Violation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Violation::Generator { term, ty, found } => {
                write!(
                    f,
                    "generator: {term} should have type {ty}, checker says {found:?}"
                )
            }
            Violation::Progress { state, ty } => {
                write!(f, "progress fails: {state} : {ty} is stuck")
            }
            Violation::Preservation {
                before,
                after,
                ty,
                found,
            } => {
                let found = match found {
                    Ok(t) => t.to_string(),
                    Err(e) => format!("no type ({e})"),
                };
                write!(
                    f,
                    "preservation fails: {before} : {ty}  ⟶  {after} : {found}"
                )
            }
            Violation::Determinism { state, steps } => {
                write!(f, "determinism fails: {state} has {} steps", steps.len())
            }
            Violation::OutOfFuel { state } => write!(f, "out of fuel at {state}"),
        }
    }
}

// ANCHOR: check_run
/// Runs `t`, which should have type `ty`, to a value, checking at every state:
/// the state has type `ty` (preservation; at the start, the generator's claim),
/// it is a value or the rules allow a step (progress), and the rules allow at
/// most one step, the one the evaluator takes (determinism).
/// Returns the number of steps taken.
pub fn check_run(
    rules: Rules,
    t: &Term,
    ty: &Ty,
    fuel: usize,
) -> Result<usize, Violation> {
    let found = type_of_with(rules, &[], t);
    if found.as_ref() != Ok(ty) {
        return Err(Violation::Generator {
            term: t.clone(),
            ty: ty.clone(),
            found,
        });
    }
    let mut current = t.clone();
    for steps_taken in 0..fuel {
        if is_value(&current) {
            return Ok(steps_taken);
        }
        let all = successors(&current);
        if all.is_empty() {
            return Err(Violation::Progress {
                state: current,
                ty: ty.clone(),
            });
        }
        if all.len() > 1 || step(&current).as_ref() != Some(&all[0]) {
            return Err(Violation::Determinism {
                state: current,
                steps: all,
            });
        }
        let next = all[0].result.clone();
        let found = type_of_with(rules, &[], &next);
        if found.as_ref() != Ok(ty) {
            let (before, after, ty) = (current, next, ty.clone());
            return Err(Violation::Preservation {
                before,
                after,
                ty,
                found,
            });
        }
        current = next;
    }
    Err(Violation::OutOfFuel { state: current })
}
// ANCHOR_END: check_run

/// The settings of a fuzzing campaign.
#[derive(Clone, Copy, Debug)]
pub struct Config {
    pub seed: u64,
    pub count: usize,
    pub max_size: usize,
    pub fuel: usize,
    pub rules: Rules,
}

/// What a successful campaign saw.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Summary {
    pub terms: usize,
    pub bools: usize,
    pub nats: usize,
    pub functions: usize,
    pub total_steps: usize,
    pub longest_run: usize,
    pub largest_term: usize,
}

/// A failing campaign: the index of the first failing term, the term, its
/// type and the violation.
#[derive(Clone, Debug)]
pub struct Failure {
    pub index: usize,
    pub term: Term,
    pub ty: Ty,
    pub violation: Violation,
}

// ANCHOR: fuzz
/// Generates `config.count` random terms of random types and checks every
/// run. Stops at the first violation.
pub fn fuzz(config: Config) -> Result<Summary, Failure> {
    let mut rng = Rng::new(config.seed);
    let mut summary = Summary::default();
    for index in 0..config.count {
        let ty = gen_type(&mut rng, 2);
        let size = 1 + rng.below(config.max_size);
        let term = gen_term(&mut rng, config.rules, &[], &ty, size);
        match check_run(config.rules, &term, &ty, config.fuel) {
            Ok(steps) => {
                summary.terms += 1;
                summary.total_steps += steps;
                summary.longest_run = summary.longest_run.max(steps);
                summary.largest_term = summary.largest_term.max(term.size());
                match ty {
                    Ty::Bool => summary.bools += 1,
                    Ty::Nat => summary.nats += 1,
                    Ty::Arrow(..) => summary.functions += 1,
                }
            }
            Err(violation) => {
                return Err(Failure {
                    index,
                    term,
                    ty,
                    violation,
                });
            }
        }
    }
    Ok(summary)
}
// ANCHOR_END: fuzz

/// Terms obtained from `t` by one small simplification: a constant or a
/// subterm in place of the whole, a literal made 0, or one of these inside a
/// subterm.
fn shrink_candidates(t: &Term) -> Vec<Term> {
    let children: Vec<&Term> = match t {
        Term::Lam(_, b) | Term::IsZero(b) => vec![b],
        Term::App(a, b) | Term::Add(a, b) => vec![a, b],
        Term::If(c, a, b) => vec![c, a, b],
        Term::Lit(n) if *n > 0 => return vec![Term::Lit(0)],
        _ => return vec![],
    };
    let mut out = vec![Term::True, Term::False, Term::Lit(0)];
    out.extend(children.iter().map(|c| (*c).clone()));
    for (k, child) in children.iter().enumerate() {
        for smaller in shrink_candidates(child) {
            out.push(replace_child(t, k, smaller));
        }
    }
    out
}

/// `t` with its `k`-th child replaced by `new`.
fn replace_child(t: &Term, k: usize, new: Term) -> Term {
    let new = Box::new(new);
    match (t.clone(), k) {
        (Term::Lam(ty, _), 0) => Term::Lam(ty, new),
        (Term::IsZero(_), 0) => Term::IsZero(new),
        (Term::App(_, b), 0) => Term::App(new, b),
        (Term::App(a, _), 1) => Term::App(a, new),
        (Term::Add(_, b), 0) => Term::Add(new, b),
        (Term::Add(a, _), 1) => Term::Add(a, new),
        (Term::If(_, a, b), 0) => Term::If(new, a, b),
        (Term::If(c, _, b), 1) => Term::If(c, new, b),
        (Term::If(c, a, _), 2) => Term::If(c, a, new),
        _ => unreachable!("{t} has no child {k}"),
    }
}

// ANCHOR: shrink
/// Shrinks a failing term: repeatedly replaces it by a smaller candidate that
/// still has a type (under `rules`) and still violates a theorem.
pub fn shrink(rules: Rules, term: &Term, fuel: usize) -> (Term, Ty, Violation) {
    let ty = type_of_with(rules, &[], term).expect("a failing term has a type");
    let violation = check_run(rules, term, &ty, fuel).expect_err("the term fails");
    let mut best = (term.clone(), ty, violation);
    'improve: loop {
        for candidate in shrink_candidates(&best.0) {
            // Only candidates that are still "well typed" count...
            let Ok(ty) = type_of_with(rules, &[], &candidate) else {
                continue;
            };
            // ...and that still break a theorem.
            if let Err(violation) = check_run(rules, &candidate, &ty, fuel) {
                best = (candidate, ty, violation);
                continue 'improve;
            }
        }
        return best;
    }
}
// ANCHOR_END: shrink

#[cfg(test)]
mod tests {
    use super::*;

    fn config(rules: Rules, count: usize) -> Config {
        Config {
            seed: 9,
            count,
            max_size: 25,
            fuel: 1000,
            rules,
        }
    }

    #[test]
    fn sound_rules_pass_on_many_terms() {
        let summary = fuzz(config(Rules::Sound, 3000)).expect("no violation");
        assert_eq!(summary.terms, 3000);
        assert!(summary.total_steps > 0);
    }

    #[test]
    fn broken_rule_is_caught_and_shrunk() {
        let failure = fuzz(config(Rules::BrokenIf, 3000)).expect_err("a violation");
        let (small, _ty, violation) = shrink(Rules::BrokenIf, &failure.term, 1000);
        assert!(small.size() <= failure.term.size());
        // The smallest counterexamples are `if false then <a> else <b>` with
        // branches of different types: preservation fails after one step.
        assert!(
            matches!(violation, Violation::Preservation { .. }),
            "{violation}"
        );
        assert_eq!(small.size(), 4, "{small}");
    }

    #[test]
    fn check_run_reports_the_generator_claim() {
        let v = check_run(Rules::Sound, &Term::True, &Ty::Nat, 10).unwrap_err();
        assert!(matches!(v, Violation::Generator { .. }));
    }

    #[test]
    fn shrinking_candidates_are_smaller() {
        let t = crate::syntax::add(Term::Lit(3), Term::True);
        for c in shrink_candidates(&t) {
            assert!(c.size() < t.size() || c != t);
        }
    }
}
