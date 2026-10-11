// harness: run
//! "Parse, don't validate": newtypes as poor man's refinement types.
//!
//! Demonstrates: a `Percent` newtype whose private field can only be set
//! through a checking constructor, a `NonEmpty<T>` whose shape makes emptiness
//! unrepresentable, and the difference between validating data (a `bool`
//! that is forgotten) and parsing it (a value whose type records the check).
//! Compare with Lean's subtypes `{ n : ℕ // n ≤ 100 }` in
//! `Book/Ch30/Vectors.lean`.
//!
//! Run with: `cargo run --example ch30_refinements`

// ANCHOR: percent
mod percent {
    /// An integer between 0 and 100. The field is private: outside this
    /// module, the only way to obtain a `Percent` is `Percent::new`.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
    pub struct Percent(u8);

    impl Percent {
        pub fn new(value: u8) -> Option<Percent> {
            if value <= 100 {
                Some(Percent(value))
            } else {
                None
            }
        }

        pub fn get(self) -> u8 {
            self.0
        }

        /// Halving keeps the value in range. Nothing checks that claim: inside
        /// the module, the invariant is our responsibility.
        pub fn half(self) -> Percent {
            Percent(self.0 / 2)
        }
    }
}

use percent::Percent;
// ANCHOR_END: percent

// ANCHOR: non_empty
/// A vector with at least one element. The first element is stored on its own,
/// so an empty `NonEmpty` cannot even be written down.
#[derive(Debug)]
struct NonEmpty<T> {
    first: T,
    rest: Vec<T>,
}

impl<T> NonEmpty<T> {
    fn from_vec(mut items: Vec<T>) -> Option<NonEmpty<T>> {
        if items.is_empty() {
            None
        } else {
            let first = items.remove(0);
            Some(NonEmpty { first, rest: items })
        }
    }

    /// Total: no `Option`, no panic.
    fn first(&self) -> &T {
        &self.first
    }

    fn len(&self) -> usize {
        1 + self.rest.len()
    }

    /// Total as well: a non-empty collection always has a largest element.
    fn max(&self) -> &T
    where
        T: Ord,
    {
        self.rest
            .iter()
            .fold(&self.first, |best, x| if x > best { x } else { best })
    }
}
// ANCHOR_END: non_empty

// ANCHOR: validate_vs_parse
/// Validation: the check returns a `bool`, and the knowledge is lost as soon
/// as the `bool` is. Every later use of the data must check again, or trust.
fn validate_scores(raw: &[u8]) -> bool {
    !raw.is_empty() && raw.iter().all(|&s| s <= 100)
}

/// Parsing: the check returns a value whose *type* records what was checked.
fn parse_scores(raw: &[u8]) -> Option<NonEmpty<Percent>> {
    let mut scores = Vec::new();
    for &s in raw {
        scores.push(Percent::new(s)?);
    }
    NonEmpty::from_vec(scores)
}

/// No checks needed: the argument's type guarantees a non-empty list of
/// percentages.
fn best(scores: &NonEmpty<Percent>) -> Percent {
    *scores.max()
}
// ANCHOR_END: validate_vs_parse

fn main() {
    // ANCHOR: main
    for raw in [&[87u8, 92, 45][..], &[87, 192], &[]] {
        let valid = validate_scores(raw);
        match parse_scores(raw) {
            Some(scores) => println!(
                "{raw:?}: valid = {valid}, {} scores, first {}, best {}, half of best {}",
                scores.len(),
                scores.first().get(),
                best(&scores).get(),
                best(&scores).half().get()
            ),
            None => println!("{raw:?}: valid = {valid}, rejected by the parser"),
        }
    }
    // ANCHOR_END: main
}
