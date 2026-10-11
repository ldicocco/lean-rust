//! Natural-deduction proofs as data.
//!
//! A [`Proof`] is a tree with one node per rule application, written the way
//! the rules of Chapter 4 are read from the bottom: to prove `A ∧ B`, give a
//! proof of `A` and a proof of `B`. Assumptions have names. A rule that
//! *discharges* an assumption (→I, and ∨E in each of its two cases) gives the
//! assumption a name, and inside its subproof [`Proof::Hyp`] can refer to it.
//!
//! The tree records only what the checker cannot work out by itself: the
//! formula of a discharged assumption, the other side of a disjunction, the
//! conclusion of ⊥E. The checker computes every other formula.

use crate::formula::Formula;
use std::collections::BTreeSet;

// ANCHOR: proof
/// A proof tree. Each variant is one rule of natural deduction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Proof {
    /// Hyp: use the assumption with this name.
    Hyp(String),
    /// ⊤I: truth, from no premises.
    TopI,
    /// ⊥E: from a proof of `⊥`, the given formula.
    BotE(Box<Proof>, Formula),
    /// ∧I: from proofs of `A` and of `B`, `A ∧ B`.
    AndI(Box<Proof>, Box<Proof>),
    /// ∧E1: from `A ∧ B`, `A`.
    AndE1(Box<Proof>),
    /// ∧E2: from `A ∧ B`, `B`.
    AndE2(Box<Proof>),
    /// ∨I1: from `A`, `A ∨ B`; the formula is `B`.
    OrI1(Box<Proof>, Formula),
    /// ∨I2: from `B`, `A ∨ B`; the formula is `A`.
    OrI2(Formula, Box<Proof>),
    /// ∨E: from `A ∨ B`, a proof of `C` assuming `A` (named `left.0`) and a
    /// proof of `C` assuming `B` (named `right.0`), conclude `C`.
    OrE {
        scrutinee: Box<Proof>,
        left: (String, Box<Proof>),
        right: (String, Box<Proof>),
    },
    /// →I: assume `A` under the given name, prove `B`, conclude `A → B`.
    /// The assumption is discharged: it cannot be used outside `body`.
    ImpI {
        name: String,
        assumption: Formula,
        body: Box<Proof>,
    },
    /// →E (modus ponens): from `A → B` and `A`, `B`.
    ImpE(Box<Proof>, Box<Proof>),
    /// tonk-I: from `A`, `A tonk B`; the formula is `B`.
    TonkI(Box<Proof>, Formula),
    /// tonk-E: from `A tonk B`, `B`.
    TonkE(Box<Proof>),
}
// ANCHOR_END: proof

// ANCHOR: builders
/// Short constructors, so that proofs read like the rules.
pub fn hyp(name: &str) -> Proof {
    Proof::Hyp(name.to_string())
}

pub fn top_i() -> Proof {
    Proof::TopI
}

pub fn bot_e(p: Proof, goal: Formula) -> Proof {
    Proof::BotE(Box::new(p), goal)
}

pub fn and_i(p: Proof, q: Proof) -> Proof {
    Proof::AndI(Box::new(p), Box::new(q))
}

pub fn and_e1(p: Proof) -> Proof {
    Proof::AndE1(Box::new(p))
}

pub fn and_e2(p: Proof) -> Proof {
    Proof::AndE2(Box::new(p))
}

pub fn or_i1(p: Proof, right: Formula) -> Proof {
    Proof::OrI1(Box::new(p), right)
}

pub fn or_i2(left: Formula, p: Proof) -> Proof {
    Proof::OrI2(left, Box::new(p))
}

pub fn or_e(p: Proof, x: &str, left: Proof, y: &str, right: Proof) -> Proof {
    Proof::OrE {
        scrutinee: Box::new(p),
        left: (x.to_string(), Box::new(left)),
        right: (y.to_string(), Box::new(right)),
    }
}

pub fn imp_i(name: &str, assumption: Formula, body: Proof) -> Proof {
    Proof::ImpI {
        name: name.to_string(),
        assumption,
        body: Box::new(body),
    }
}

pub fn imp_e(f: Proof, a: Proof) -> Proof {
    Proof::ImpE(Box::new(f), Box::new(a))
}

pub fn tonk_i(p: Proof, right: Formula) -> Proof {
    Proof::TonkI(Box::new(p), right)
}

pub fn tonk_e(p: Proof) -> Proof {
    Proof::TonkE(Box::new(p))
}
// ANCHOR_END: builders

impl Proof {
    /// The immediate subproofs, in order.
    pub fn premises(&self) -> Vec<&Proof> {
        match self {
            Proof::Hyp(_) | Proof::TopI => vec![],
            Proof::BotE(p, _)
            | Proof::AndE1(p)
            | Proof::AndE2(p)
            | Proof::OrI1(p, _)
            | Proof::OrI2(_, p)
            | Proof::TonkI(p, _)
            | Proof::TonkE(p) => vec![p],
            Proof::AndI(p, q) | Proof::ImpE(p, q) => vec![p, q],
            Proof::ImpI { body, .. } => vec![body],
            Proof::OrE {
                scrutinee,
                left,
                right,
            } => vec![scrutinee, &left.1, &right.1],
        }
    }

    /// The number of rule applications in the tree.
    pub fn size(&self) -> usize {
        1 + self.premises().iter().map(|p| p.size()).sum::<usize>()
    }

    /// The names of the assumptions that are used but not discharged inside
    /// the proof: its open assumptions.
    pub fn open_assumptions(&self) -> BTreeSet<String> {
        match self {
            Proof::Hyp(name) => BTreeSet::from([name.clone()]),
            Proof::ImpI { name, body, .. } => {
                let mut open = body.open_assumptions();
                open.remove(name);
                open
            }
            Proof::OrE {
                scrutinee,
                left,
                right,
            } => {
                let mut open = scrutinee.open_assumptions();
                let mut in_left = left.1.open_assumptions();
                in_left.remove(&left.0);
                let mut in_right = right.1.open_assumptions();
                in_right.remove(&right.0);
                open.extend(in_left);
                open.extend(in_right);
                open
            }
            other => other
                .premises()
                .iter()
                .flat_map(|p| p.open_assumptions())
                .collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(s: &str) -> Formula {
        s.parse().unwrap()
    }

    #[test]
    fn discharge_closes_assumptions() {
        let p = imp_i("u", f("A"), and_i(hyp("u"), hyp("v")));
        assert_eq!(p.open_assumptions(), BTreeSet::from(["v".to_string()]));
        assert_eq!(p.size(), 4);
    }

    #[test]
    fn or_elimination_discharges_in_each_branch_only() {
        let p = or_e(hyp("d"), "x", hyp("x"), "y", hyp("x"));
        // In the right branch, `x` is not discharged: it is open.
        let open = p.open_assumptions();
        assert!(open.contains("d") && open.contains("x") && !open.contains("y"));
    }
}
