//! The rules of the sequent calculus, read backwards: given a sequent to
//! prove, every way of applying a rule whose conclusion it is, and the
//! premises that this leaves to prove.

use std::collections::BTreeSet;
use std::fmt;

use crate::formula::Formula;
use crate::sequent::{Sequent, remove_one};

// ANCHOR: logic
/// Which structural rules the logic has. Both have exchange (contexts are
/// multisets) and neither has contraction. Affine logic also has weakening.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Logic {
    Linear,
    Affine,
}
// ANCHOR_END: logic

impl fmt::Display for Logic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Logic::Linear => write!(f, "linear"),
            Logic::Affine => write!(f, "affine"),
        }
    }
}

/// The rules of the calculus. `R` rules act on the goal (right of `⊢`), `L`
/// rules on a formula of the context (left of `⊢`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Rule {
    Axiom,
    Weaken,
    OneR,
    OneL,
    TopR,
    ZeroL,
    TensorR,
    TensorL,
    WithR,
    WithL1,
    WithL2,
    PlusR1,
    PlusR2,
    PlusL,
    LolliR,
    LolliL,
}

impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Rule::Axiom => "Ax",
            Rule::Weaken => "W",
            Rule::OneR => "1R",
            Rule::OneL => "1L",
            Rule::TopR => "⊤R",
            Rule::ZeroL => "0L",
            Rule::TensorR => "⊗R",
            Rule::TensorL => "⊗L",
            Rule::WithR => "&R",
            Rule::WithL1 => "&L1",
            Rule::WithL2 => "&L2",
            Rule::PlusR1 => "⊕R1",
            Rule::PlusR2 => "⊕R2",
            Rule::PlusL => "⊕L",
            Rule::LolliR => "⊸R",
            Rule::LolliL => "⊸L",
        };
        // Pad here: the formatter's own padding is ignored by `write!`.
        match f.width() {
            Some(width) => write!(f, "{name:<width$}"),
            None => write!(f, "{name}"),
        }
    }
}

/// One backward application of a rule: the premises that remain to prove.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Step {
    pub rule: Rule,
    pub premises: Vec<Sequent>,
}

fn step(rule: Rule, premises: Vec<Sequent>) -> Step {
    Step { rule, premises }
}

// ANCHOR: splits
/// Every way to divide a multiset of resources between two premises. A
/// context of n formulas has 2^n splits (fewer when formulas repeat).
pub fn splits(context: &[Formula]) -> Vec<(Vec<Formula>, Vec<Formula>)> {
    let mut seen = BTreeSet::new();
    let mut result = Vec::new();
    for mask in 0..(1_u32 << context.len()) {
        let (mut left, mut right) = (Vec::new(), Vec::new());
        for (i, formula) in context.iter().enumerate() {
            if mask & (1 << i) != 0 {
                left.push(formula.clone());
            } else {
                right.push(formula.clone());
            }
        }
        left.sort();
        right.sort();
        if seen.insert(left.clone()) {
            result.push((left, right));
        }
    }
    result
}
// ANCHOR_END: splits

fn with_added(context: &[Formula], extra: &[&Formula]) -> Vec<Formula> {
    let mut result = context.to_vec();
    result.extend(extra.iter().map(|f| (*f).clone()));
    result.sort();
    result
}

/// The distinct formulas of a context, each with the context minus one copy.
fn picks(context: &[Formula]) -> Vec<(Formula, Vec<Formula>)> {
    let mut seen = BTreeSet::new();
    let mut result = Vec::new();
    for formula in context {
        if seen.insert(formula.clone()) {
            let rest = remove_one(context, formula).expect("formula is in the context");
            result.push((formula.clone(), rest));
        }
    }
    result
}

// ANCHOR: steps
/// Every backward rule application to `seq`, in the order the prover tries
/// them: first the rules that close a branch, then the rules that never
/// lose provability (⊸R, &R, ⊗L, 1L, ⊕L), then the rules that make a
/// choice (a split of the context, or a side of a ⊕ or a &).
pub fn steps(logic: Logic, seq: &Sequent) -> Vec<Step> {
    let Sequent { context, goal } = seq;
    let mut steps = Vec::new();

    // ANCHOR: leaves
    // Leaves. In linear logic the identity axiom needs the context to be
    // exactly the goal; affine logic may first discard everything else.
    if context.len() == 1 && context[0] == *goal {
        steps.push(step(Rule::Axiom, vec![]));
    } else if logic == Logic::Affine && context.contains(goal) {
        let axiom = Sequent::new(vec![goal.clone()], goal.clone());
        steps.push(step(Rule::Weaken, vec![axiom]));
    }
    match goal {
        Formula::One if context.is_empty() => steps.push(step(Rule::OneR, vec![])),
        Formula::One if logic == Logic::Affine => {
            let unit = Sequent::new(vec![], Formula::One);
            steps.push(step(Rule::Weaken, vec![unit]));
        }
        Formula::Top => steps.push(step(Rule::TopR, vec![])),
        _ => {}
    }
    if context.contains(&Formula::Zero) {
        steps.push(step(Rule::ZeroL, vec![]));
    }
    // ANCHOR_END: leaves

    // Right rules that never lose provability.
    match goal {
        Formula::Lolli(a, b) => {
            let premise = Sequent::new(with_added(context, &[a]), (**b).clone());
            steps.push(step(Rule::LolliR, vec![premise]));
        }
        Formula::With(a, b) => {
            let left = Sequent::new(context.clone(), (**a).clone());
            let right = Sequent::new(context.clone(), (**b).clone());
            steps.push(step(Rule::WithR, vec![left, right]));
        }
        _ => {}
    }

    // Left rules that never lose provability.
    for (formula, rest) in picks(context) {
        match &formula {
            Formula::Tensor(a, b) => {
                let premise = Sequent::new(with_added(&rest, &[a, b]), goal.clone());
                steps.push(step(Rule::TensorL, vec![premise]));
            }
            Formula::One => {
                steps.push(step(Rule::OneL, vec![Sequent::new(rest, goal.clone())]));
            }
            Formula::Plus(a, b) => {
                let left = Sequent::new(with_added(&rest, &[a]), goal.clone());
                let right = Sequent::new(with_added(&rest, &[b]), goal.clone());
                steps.push(step(Rule::PlusL, vec![left, right]));
            }
            _ => {}
        }
    }

    // Right rules that make a choice.
    match goal {
        // ANCHOR: tensor_right
        Formula::Tensor(a, b) => {
            for (left, right) in splits(context) {
                let p1 = Sequent::new(left, (**a).clone());
                let p2 = Sequent::new(right, (**b).clone());
                steps.push(step(Rule::TensorR, vec![p1, p2]));
            }
        }
        // ANCHOR_END: tensor_right
        Formula::Plus(a, b) => {
            let p1 = Sequent::new(context.clone(), (**a).clone());
            let p2 = Sequent::new(context.clone(), (**b).clone());
            steps.push(step(Rule::PlusR1, vec![p1]));
            steps.push(step(Rule::PlusR2, vec![p2]));
        }
        _ => {}
    }

    // Left rules that make a choice.
    for (formula, rest) in picks(context) {
        match &formula {
            // ANCHOR: with_left
            Formula::With(a, b) => {
                let p1 = Sequent::new(with_added(&rest, &[a]), goal.clone());
                let p2 = Sequent::new(with_added(&rest, &[b]), goal.clone());
                steps.push(step(Rule::WithL1, vec![p1]));
                steps.push(step(Rule::WithL2, vec![p2]));
            }
            // ANCHOR_END: with_left
            Formula::Lolli(a, b) => {
                for (left, right) in splits(&rest) {
                    let p1 = Sequent::new(left, (**a).clone());
                    let p2 = Sequent::new(with_added(&right, &[b]), goal.clone());
                    steps.push(step(Rule::LolliL, vec![p1, p2]));
                }
            }
            _ => {}
        }
    }
    steps
}
// ANCHOR_END: steps

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sequent::parse_sequent;

    #[test]
    fn splits_of_three_distinct_formulas() {
        let ctx: Vec<Formula> =
            ["a", "b", "c"].iter().map(|n| Formula::atom(n)).collect();
        assert_eq!(splits(&ctx).len(), 8);
        let twice = vec![Formula::atom("a"), Formula::atom("a")];
        // {} | {a, a},  {a} | {a},  {a, a} | {}
        assert_eq!(splits(&twice).len(), 3);
    }

    #[test]
    fn every_premise_is_smaller() {
        let seq = parse_sequent("a * b, c -o d, e & f, g + h |- (a -o b) * (c & d)")
            .unwrap()
            .normalized();
        for logic in [Logic::Linear, Logic::Affine] {
            for s in steps(logic, &seq) {
                for p in &s.premises {
                    assert!(p.size() < seq.size(), "{} does not shrink", s.rule);
                }
            }
        }
    }

    #[test]
    fn axiom_needs_an_exact_context_in_linear_logic() {
        let seq = parse_sequent("a, b |- a").unwrap().normalized();
        assert!(steps(Logic::Linear, &seq).is_empty());
        let affine = steps(Logic::Affine, &seq);
        assert_eq!(affine[0].rule, Rule::Weaken);
    }
}
