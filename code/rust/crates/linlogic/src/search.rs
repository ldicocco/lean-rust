//! Backward proof search with memoization.

use std::collections::BTreeMap;

use crate::proof::Proof;
use crate::rules::{Logic, steps};
use crate::sequent::Sequent;

// ANCHOR: prover
/// A proof search for one logic. It remembers every sequent it has
/// examined, with the proof it found or `None`, so no sequent is searched
/// twice.
pub struct Prover {
    logic: Logic,
    memo: BTreeMap<Sequent, Option<Proof>>,
}

impl Prover {
    pub fn new(logic: Logic) -> Prover {
        Prover {
            logic,
            memo: BTreeMap::new(),
        }
    }

    /// Searches for a derivation of `seq`. The search is complete: if it
    /// returns `None`, the sequent has no cut-free derivation at all.
    pub fn prove(&mut self, seq: &Sequent) -> Option<Proof> {
        let mut proof = self.search(&seq.normalized())?;
        // Show the root with the context in the order the user wrote it.
        proof.conclusion = seq.clone();
        Some(proof)
    }

    fn search(&mut self, seq: &Sequent) -> Option<Proof> {
        if let Some(known) = self.memo.get(seq) {
            return known.clone();
        }
        let mut found = None;
        'steps: for step in steps(self.logic, seq) {
            let mut premises = Vec::new();
            for premise in &step.premises {
                match self.search(&premise.normalized()) {
                    Some(proof) => premises.push(proof),
                    None => continue 'steps,
                }
            }
            found = Some(Proof {
                rule: step.rule,
                conclusion: seq.clone(),
                premises,
            });
            break;
        }
        self.memo.insert(seq.clone(), found.clone());
        found
    }
}
// ANCHOR_END: prover

impl Prover {
    /// How many distinct sequents the search has examined so far.
    pub fn explored(&self) -> usize {
        self.memo.len()
    }

    pub fn logic(&self) -> Logic {
        self.logic
    }

    // ANCHOR: explain
    /// Why a sequent is not provable: every rule that applies to it, with
    /// the verdict on each of its premises. (For a provable sequent, the
    /// first line that has no failing premise is the step the proof uses.)
    pub fn explain(&mut self, seq: &Sequent) -> Vec<String> {
        let normal = seq.normalized();
        let mut lines = Vec::new();
        for step in steps(self.logic, &normal) {
            let verdicts: Vec<String> = step
                .premises
                .iter()
                .map(|p| {
                    let ok = self.search(&p.normalized()).is_some();
                    format!("{p} ({})", if ok { "provable" } else { "fails" })
                })
                .collect();
            let premises = if verdicts.is_empty() {
                "no premises".to_string()
            } else {
                verdicts.join(";  ")
            };
            lines.push(format!("{:<4} {premises}", step.rule));
        }
        lines
    }
    // ANCHOR_END: explain
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rules::Rule;
    use crate::sequent::parse_sequent;

    fn provable(logic: Logic, s: &str) -> bool {
        let seq = parse_sequent(s).unwrap();
        let mut prover = Prover::new(logic);
        match prover.prove(&seq) {
            Some(proof) => {
                assert_eq!(proof.check(logic), Ok(()), "bad proof of {s}");
                true
            }
            None => false,
        }
    }

    #[test]
    fn the_chapter_table() {
        // (sequent, linear, affine)
        let table = [
            ("a |- a", true, true),
            ("a |- a * a", false, false),
            ("a * b |- a", false, true),
            ("a * b |- b * a", true, true),
            ("a & b |- a", true, true),
            ("a |- a & a", true, true),
            ("a & b |- a * b", false, false),
            ("a * b |- a & b", false, true),
            ("a -o b -o c |- a * b -o c", true, true),
            ("a * b -o c |- a -o b -o c", true, true),
            ("a |- b -o a", false, true),
            ("a -o a -o b |- a -o b", false, false),
            ("top |- 1", false, true),
            ("1 |- top", true, true),
            ("a * (b + c) |- (a * b) + (a * c)", true, true),
            ("(a * b) + (a * c) |- a * (b + c)", true, true),
            ("a * (b & c) |- (a * b) & (a * c)", true, true),
            ("(a * b) & (a * c) |- a * (b & c)", false, false),
            ("a, a -o b |- b", true, true),
            ("a -o b, b -o c |- a -o c", true, true),
            ("0 |- a * b", true, true),
            ("a + b |- b + a", true, true),
        ];
        for (s, linear, affine) in table {
            assert_eq!(provable(Logic::Linear, s), linear, "linear: {s}");
            assert_eq!(provable(Logic::Affine, s), affine, "affine: {s}");
        }
    }

    #[test]
    fn coffee_machine() {
        let machine = "coin, coin -o (coffee & tea)";
        assert!(provable(Logic::Linear, &format!("{machine} |- coffee")));
        assert!(provable(Logic::Linear, &format!("{machine} |- tea")));
        assert!(!provable(
            Logic::Linear,
            &format!("{machine} |- coffee * tea")
        ));
        assert!(!provable(
            Logic::Affine,
            &format!("{machine} |- coffee * tea")
        ));
        assert!(provable(
            Logic::Linear,
            &format!("{machine} |- coffee & tea")
        ));
        let two = "coin, coin, coin -o (coffee & tea), coin -o (coffee & tea)";
        assert!(provable(Logic::Linear, &format!("{two} |- coffee * tea")));
        let surprise = "coin, coin -o (coffee + tea)";
        assert!(!provable(Logic::Linear, &format!("{surprise} |- coffee")));
        assert!(provable(
            Logic::Linear,
            &format!("{surprise} |- coffee + tea")
        ));
    }

    #[test]
    fn affine_proofs_mark_their_weakenings() {
        let mut prover = Prover::new(Logic::Affine);
        let proof = prover.prove(&parse_sequent("a * b |- a").unwrap()).unwrap();
        assert!(proof.uses(Rule::Weaken));
        let mut linear = Prover::new(Logic::Linear);
        let proof = linear.prove(&parse_sequent("a & b |- a").unwrap()).unwrap();
        assert!(!proof.uses(Rule::Weaken));
    }

    #[test]
    fn explanation_lists_every_attempt() {
        let mut prover = Prover::new(Logic::Linear);
        let lines = prover.explain(&parse_sequent("a |- a * a").unwrap());
        assert_eq!(lines.len(), 2);
        assert!(lines.iter().all(|l| l.contains("fails")));
    }
}
