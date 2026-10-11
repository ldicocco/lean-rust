//! Proof search in the sequent calculus of linear and affine propositional
//! logic (the multiplicative-additive fragment: ⊗, 1, &, ⊤, ⊕, 0, ⊸).
//!
//! Built in Chapter 21. The pieces:
//!
//! - [`formula`]: formulas, a parser (`a * b -o c` or `a ⊗ b ⊸ c`) and a
//!   printer;
//! - [`sequent`]: sequents `Γ ⊢ C` whose context is a multiset;
//! - [`rules`]: the rules of the calculus, applied backwards, for the linear
//!   and the affine logic;
//! - [`search`]: a complete, memoizing backward proof search;
//! - [`proof`]: proof trees, printed as readable traces and checked by an
//!   independent checker.

pub mod formula;
pub mod proof;
pub mod rules;
pub mod search;
pub mod sequent;

pub use formula::{Formula, ParseError, parse_formula};
pub use proof::Proof;
pub use rules::{Logic, Rule};
pub use search::Prover;
pub use sequent::{Sequent, parse_sequent};

#[cfg(test)]
mod properties {
    //! Property tests on random sequents, with a small seeded generator.

    use super::*;

    /// SplitMix64: a tiny, good-enough pseudo-random generator.
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        }

        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    /// A random formula over the atoms `a` and `b`. With `multiplicative`,
    /// only ⊗, ⊸ and 1 are used.
    fn formula(rng: &mut Rng, depth: u32, multiplicative: bool) -> Formula {
        if depth == 0 || rng.below(3) == 0 {
            return match rng.below(if multiplicative { 5 } else { 7 }) {
                0 | 1 => Formula::atom("a"),
                2 | 3 => Formula::atom("b"),
                4 => Formula::One,
                5 => Formula::Top,
                _ => Formula::Zero,
            };
        }
        let a = formula(rng, depth - 1, multiplicative);
        let b = formula(rng, depth - 1, multiplicative);
        match rng.below(if multiplicative { 2 } else { 4 }) {
            0 => Formula::tensor(a, b),
            1 => Formula::lolli(a, b),
            2 => Formula::with(a, b),
            _ => Formula::plus(a, b),
        }
    }

    fn sequent(rng: &mut Rng, multiplicative: bool) -> Sequent {
        let n = rng.below(3) as usize;
        let context = (0..n).map(|_| formula(rng, 2, multiplicative)).collect();
        Sequent::new(context, formula(rng, 2, multiplicative))
    }

    /// Occurrences of `atom` in positive and negative position, seen from
    /// the right-hand side of a sequent. A context formula counts with the
    /// opposite polarity.
    fn polarity_counts(f: &Formula, atom: &str, positive: bool) -> (i64, i64) {
        match f {
            Formula::Atom(name) if name == atom => {
                if positive {
                    (1, 0)
                } else {
                    (0, 1)
                }
            }
            Formula::Atom(_) | Formula::One | Formula::Top | Formula::Zero => (0, 0),
            Formula::Tensor(a, b) | Formula::With(a, b) | Formula::Plus(a, b) => {
                let (p1, n1) = polarity_counts(a, atom, positive);
                let (p2, n2) = polarity_counts(b, atom, positive);
                (p1 + p2, n1 + n2)
            }
            Formula::Lolli(a, b) => {
                let (p1, n1) = polarity_counts(a, atom, !positive);
                let (p2, n2) = polarity_counts(b, atom, positive);
                (p1 + p2, n1 + n2)
            }
        }
    }

    fn balanced(seq: &Sequent, atom: &str) -> bool {
        let (mut pos, mut neg) = polarity_counts(&seq.goal, atom, true);
        for f in &seq.context {
            let (p, n) = polarity_counts(f, atom, false);
            pos += p;
            neg += n;
        }
        pos == neg
    }

    #[test]
    fn found_proofs_check_and_linear_implies_affine() {
        let mut rng = Rng(2026);
        let mut provable = 0;
        for _ in 0..1500 {
            let seq = sequent(&mut rng, false);
            let linear = Prover::new(Logic::Linear).prove(&seq);
            let affine = Prover::new(Logic::Affine).prove(&seq);
            if let Some(p) = &linear {
                assert_eq!(p.check(Logic::Linear), Ok(()), "{seq}");
                assert!(affine.is_some(), "linear but not affine: {seq}");
                provable += 1;
            }
            if let Some(p) = &affine {
                assert_eq!(p.check(Logic::Affine), Ok(()), "{seq}");
            }
        }
        assert!(
            provable > 50,
            "the generator should produce provable sequents"
        );
    }

    #[test]
    fn multiplicative_proofs_balance_atoms() {
        // In the multiplicative fragment every provable linear sequent uses
        // each atom as often as it produces it: the invariant Lean proves.
        let mut rng = Rng(7);
        for _ in 0..1500 {
            let seq = sequent(&mut rng, true);
            if Prover::new(Logic::Linear).prove(&seq).is_some() {
                assert!(balanced(&seq, "a") && balanced(&seq, "b"), "{seq}");
            }
        }
    }

    #[test]
    fn weakening_is_admissible_in_affine_logic() {
        let mut rng = Rng(99);
        for _ in 0..500 {
            let seq = sequent(&mut rng, false);
            if Prover::new(Logic::Affine).prove(&seq).is_some() {
                let mut bigger = seq.clone();
                bigger.context.push(formula(&mut rng, 2, false));
                assert!(
                    Prover::new(Logic::Affine).prove(&bigger).is_some(),
                    "{bigger}"
                );
            }
        }
    }
}
