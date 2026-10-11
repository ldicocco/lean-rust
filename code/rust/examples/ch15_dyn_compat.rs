// harness: run
//! Making a trait dyn compatible: the two repairs for the trait rejected in
//! `compile_fail/ch15_dyn_incompatible.rs`. A method that mentions `Self` is
//! kept out of the vtable with `where Self: Sized`; a generic method is
//! replaced by one that takes a trait object, so a single vtable entry serves
//! every visitor.
//!
//! Run with: `cargo run --example ch15_dyn_compat`

// ANCHOR: visitor
trait Visitor {
    fn visit(&mut self, value: u32);
}

/// Collects every value it is shown.
struct Collect(Vec<u32>);

impl Visitor for Collect {
    fn visit(&mut self, value: u32) {
        self.0.push(value);
    }
}

/// Keeps only the largest value it is shown.
struct Largest(u32);

impl Visitor for Largest {
    fn visit(&mut self, value: u32) {
        self.0 = self.0.max(value);
    }
}
// ANCHOR_END: visitor

// ANCHOR: compatible
trait Mergeable {
    fn total(&self) -> u32;

    /// Mentions `Self`: excluded from the vtable, so it can be called on
    /// concrete types only.
    fn merge(&self, other: &Self) -> Self
    where
        Self: Sized;

    /// Takes a trait object instead of a type parameter: one vtable entry
    /// that works for every visitor.
    fn accept(&self, visitor: &mut dyn Visitor);
}
// ANCHOR_END: compatible

// ANCHOR: instances
/// Readings of one instrument.
struct Batch(Vec<u32>);

impl Mergeable for Batch {
    fn total(&self) -> u32 {
        self.0.iter().sum()
    }
    fn merge(&self, other: &Batch) -> Batch {
        Batch([self.0.as_slice(), other.0.as_slice()].concat())
    }
    fn accept(&self, visitor: &mut dyn Visitor) {
        for &v in &self.0 {
            visitor.visit(v);
        }
    }
}

/// A single reading.
struct Single(u32);

impl Mergeable for Single {
    fn total(&self) -> u32 {
        self.0
    }
    fn merge(&self, other: &Single) -> Single {
        Single(self.0 + other.0)
    }
    fn accept(&self, visitor: &mut dyn Visitor) {
        visitor.visit(self.0);
    }
}
// ANCHOR_END: instances

fn main() {
    // ANCHOR: run
    // `merge` works on concrete types, where both arguments have the same type.
    let merged = Batch(vec![3, 1]).merge(&Batch(vec![4]));
    println!("merged batch total: {}", merged.total());

    // Through `dyn Mergeable`, `total` and `accept` are available...
    let items: Vec<Box<dyn Mergeable>> = vec![
        Box::new(merged),
        Box::new(Single(9)),
        Box::new(Batch(vec![2, 6])),
    ];
    let totals: Vec<u32> = items.iter().map(|item| item.total()).collect();
    println!("totals: {totals:?}");

    // ...and `accept` works with any visitor, chosen at run time too.
    let mut all = Collect(Vec::new());
    let mut largest = Largest(0);
    for item in &items {
        item.accept(&mut all);
        item.accept(&mut largest);
    }
    println!("visited: {:?}, largest: {}", all.0, largest.0);
    // ANCHOR_END: run
}
