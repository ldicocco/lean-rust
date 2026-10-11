//! Proof trees: printing them as a readable trace, and checking them with a
//! checker that is independent of the search.

use crate::formula::Formula;
use crate::rules::{Logic, Rule};
use crate::sequent::{Sequent, remove_one, same_multiset};

// ANCHOR: proof
/// A derivation in the sequent calculus: the rule used at the root, the
/// sequent it concludes, and the derivations of its premises.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    pub rule: Rule,
    pub conclusion: Sequent,
    pub premises: Vec<Proof>,
}
// ANCHOR_END: proof

impl Proof {
    /// The derivation as indented text: one line per rule application, the
    /// rule name in the first column, premises indented below their
    /// conclusion. Read it top-down as the search found it: to prove this
    /// line, prove the lines below it.
    pub fn render(&self) -> String {
        let mut out = String::new();
        self.render_into(0, &mut out);
        out
    }

    fn render_into(&self, depth: usize, out: &mut String) {
        let indent = "  ".repeat(depth);
        out.push_str(&format!("{:<4} {indent}{}\n", self.rule, self.conclusion));
        for premise in &self.premises {
            premise.render_into(depth + 1, out);
        }
    }

    /// The number of rule applications in the derivation.
    pub fn size(&self) -> usize {
        1 + self.premises.iter().map(Proof::size).sum::<usize>()
    }

    /// Does the derivation use the rule `rule` anywhere?
    pub fn uses(&self, rule: Rule) -> bool {
        self.rule == rule || self.premises.iter().any(|p| p.uses(rule))
    }

    // ANCHOR: check
    /// Checks every step of the derivation against the rules of `logic`.
    /// This does not trust the prover: it only compares sequents.
    pub fn check(&self, logic: Logic) -> Result<(), String> {
        for premise in &self.premises {
            premise.check(logic)?;
        }
        let premises: Vec<&Sequent> =
            self.premises.iter().map(|p| &p.conclusion).collect();
        if check_step(logic, self.rule, &self.conclusion, &premises) {
            Ok(())
        } else {
            Err(format!(
                "{} is not a correct use of {}",
                self.conclusion, self.rule
            ))
        }
    }
    // ANCHOR_END: check
}

/// `context` minus one copy of `principal`, plus `added`, as a sorted list.
fn replace(
    context: &[Formula],
    principal: &Formula,
    added: &[&Formula],
) -> Option<Vec<Formula>> {
    let mut rest = remove_one(context, principal)?;
    rest.extend(added.iter().map(|f| (*f).clone()));
    Some(rest)
}

/// Is there a formula in the context, accepted by `matches`, that makes
/// `ok` true? Used for left rules: one of the context formulas is principal.
fn some_principal(
    context: &[Formula],
    mut ok: impl FnMut(&Formula, Vec<Formula>) -> bool,
) -> bool {
    context.iter().any(|f| {
        let rest = remove_one(context, f).expect("f is in the context");
        ok(f, rest)
    })
}

fn is_sub_multiset(small: &[Formula], big: &[Formula]) -> bool {
    let mut rest = big.to_vec();
    for f in small {
        match remove_one(&rest, f) {
            Some(r) => rest = r,
            None => return false,
        }
    }
    true
}

fn check_step(logic: Logic, rule: Rule, c: &Sequent, ps: &[&Sequent]) -> bool {
    let ctx = &c.context;
    let goal = &c.goal;
    let same_goal = |p: &Sequent| p.goal == *goal;
    match (rule, ps) {
        (Rule::Axiom, []) => ctx.len() == 1 && ctx[0] == *goal,
        (Rule::Weaken, [p]) => {
            logic == Logic::Affine && same_goal(p) && is_sub_multiset(&p.context, ctx)
        }
        (Rule::OneR, []) => ctx.is_empty() && *goal == Formula::One,
        (Rule::TopR, []) => *goal == Formula::Top,
        (Rule::ZeroL, []) => ctx.contains(&Formula::Zero),
        (Rule::OneL, [p]) => {
            same_goal(p)
                && replace(ctx, &Formula::One, &[])
                    .is_some_and(|r| same_multiset(&r, &p.context))
        }
        (Rule::TensorR, [p, q]) => match goal {
            Formula::Tensor(a, b) => {
                p.goal == **a && q.goal == **b && {
                    let mut both = p.context.clone();
                    both.extend(q.context.iter().cloned());
                    same_multiset(&both, ctx)
                }
            }
            _ => false,
        },
        (Rule::TensorL, [p]) => {
            same_goal(p)
                && some_principal(ctx, |f, rest| match f {
                    Formula::Tensor(a, b) => {
                        let mut expected = rest;
                        expected.push((**a).clone());
                        expected.push((**b).clone());
                        same_multiset(&expected, &p.context)
                    }
                    _ => false,
                })
        }
        (Rule::WithR, [p, q]) => match goal {
            Formula::With(a, b) => {
                p.goal == **a
                    && q.goal == **b
                    && same_multiset(&p.context, ctx)
                    && same_multiset(&q.context, ctx)
            }
            _ => false,
        },
        (Rule::WithL1 | Rule::WithL2, [p]) => {
            same_goal(p)
                && some_principal(ctx, |f, rest| match f {
                    Formula::With(a, b) => {
                        let chosen = if rule == Rule::WithL1 { a } else { b };
                        let mut expected = rest;
                        expected.push((**chosen).clone());
                        same_multiset(&expected, &p.context)
                    }
                    _ => false,
                })
        }
        (Rule::PlusR1 | Rule::PlusR2, [p]) => match goal {
            Formula::Plus(a, b) => {
                let chosen = if rule == Rule::PlusR1 { a } else { b };
                p.goal == **chosen && same_multiset(&p.context, ctx)
            }
            _ => false,
        },
        (Rule::PlusL, [p, q]) => {
            same_goal(p)
                && same_goal(q)
                && some_principal(ctx, |f, rest| match f {
                    Formula::Plus(a, b) => {
                        let (mut ea, mut eb) = (rest.clone(), rest);
                        ea.push((**a).clone());
                        eb.push((**b).clone());
                        same_multiset(&ea, &p.context) && same_multiset(&eb, &q.context)
                    }
                    _ => false,
                })
        }
        (Rule::LolliR, [p]) => match goal {
            Formula::Lolli(a, b) => {
                p.goal == **b
                    && replace(&p.context, a, &[])
                        .is_some_and(|r| same_multiset(&r, ctx))
            }
            _ => false,
        },
        (Rule::LolliL, [p, q]) => {
            same_goal(q)
                && some_principal(ctx, |f, rest| match f {
                    Formula::Lolli(a, b) => {
                        p.goal == **a
                            && remove_one(&q.context, b).is_some_and(|q_rest| {
                                let mut both = p.context.clone();
                                both.extend(q_rest);
                                same_multiset(&both, &rest)
                            })
                    }
                    _ => false,
                })
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sequent::parse_sequent;

    fn leaf(rule: Rule, s: &str) -> Proof {
        Proof {
            rule,
            conclusion: parse_sequent(s).unwrap(),
            premises: vec![],
        }
    }

    #[test]
    fn checker_accepts_a_hand_built_proof() {
        let proof = Proof {
            rule: Rule::TensorL,
            conclusion: parse_sequent("a * b |- b * a").unwrap(),
            premises: vec![Proof {
                rule: Rule::TensorR,
                conclusion: parse_sequent("a, b |- b * a").unwrap(),
                premises: vec![
                    leaf(Rule::Axiom, "b |- b"),
                    leaf(Rule::Axiom, "a |- a"),
                ],
            }],
        };
        assert_eq!(proof.check(Logic::Linear), Ok(()));
        assert_eq!(proof.size(), 4);
    }

    #[test]
    fn checker_rejects_contraction_and_weakening_in_linear_logic() {
        // a |- a * a "by ⊗R", giving the single a to both premises.
        let bad = Proof {
            rule: Rule::TensorR,
            conclusion: parse_sequent("a |- a * a").unwrap(),
            premises: vec![leaf(Rule::Axiom, "a |- a"), leaf(Rule::Axiom, "a |- a")],
        };
        assert!(bad.check(Logic::Linear).is_err());
        let weak = Proof {
            rule: Rule::Weaken,
            conclusion: parse_sequent("a, b |- a").unwrap(),
            premises: vec![leaf(Rule::Axiom, "a |- a")],
        };
        assert!(weak.check(Logic::Linear).is_err());
        assert_eq!(weak.check(Logic::Affine), Ok(()));
    }
}
