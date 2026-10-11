// harness: run
//! Type classes and their elaboration: a `Monoid` trait with instances, a
//! generic function that uses it, and the same program after the
//! dictionary-passing translation (every trait bound replaced by an explicit
//! struct of functions). Both versions produce identical results.
//!
//! Run with: `cargo run --example ch14_dictionary_passing`

use std::fmt::Debug;

// ---------------------------------------------------------------------------
// Part 1: the class and its instances, written with a trait.
// ---------------------------------------------------------------------------

// ANCHOR: monoid_trait
/// A monoid: a type with a neutral element and an associative operation.
///
/// Laws (stated here in prose, because Rust has no way to state them in code):
/// - associativity: `a.combine(b).combine(c) == a.combine(b.combine(c))`
/// - identity: `M::empty().combine(a) == a == a.combine(M::empty())`
trait Monoid {
    fn empty() -> Self;
    fn combine(self, other: Self) -> Self;
}
// ANCHOR_END: monoid_trait

// ANCHOR: newtypes
/// `i64` has (at least) two monoid structures, addition and multiplication.
/// A type can implement a trait only once, so each structure gets a newtype.
#[derive(Clone, Copy, Debug, PartialEq)]
struct Sum(i64);

#[derive(Clone, Copy, Debug, PartialEq)]
struct Product(i64);

#[derive(Clone, Copy, Debug, PartialEq)]
struct Max(i64);
// ANCHOR_END: newtypes

// ANCHOR: instances
impl Monoid for Sum {
    fn empty() -> Self {
        Sum(0)
    }
    fn combine(self, other: Self) -> Self {
        Sum(self.0 + other.0)
    }
}

impl Monoid for Product {
    fn empty() -> Self {
        Product(1)
    }
    fn combine(self, other: Self) -> Self {
        Product(self.0 * other.0)
    }
}

impl Monoid for Max {
    fn empty() -> Self {
        Max(i64::MIN)
    }
    fn combine(self, other: Self) -> Self {
        Max(self.0.max(other.0))
    }
}

impl Monoid for String {
    fn empty() -> Self {
        String::new()
    }
    fn combine(mut self, other: Self) -> Self {
        self.push_str(&other);
        self
    }
}

impl<T> Monoid for Vec<T> {
    fn empty() -> Self {
        Vec::new()
    }
    fn combine(mut self, other: Self) -> Self {
        self.extend(other);
        self
    }
}
// ANCHOR_END: instances

// ANCHOR: pair_instance
/// An instance with a context: a pair is a monoid *if* both components are.
impl<A: Monoid, B: Monoid> Monoid for (A, B) {
    fn empty() -> Self {
        (A::empty(), B::empty())
    }
    fn combine(self, other: Self) -> Self {
        (self.0.combine(other.0), self.1.combine(other.1))
    }
}
// ANCHOR_END: pair_instance

// ANCHOR: generic_code
/// Combine all the items, left to right. Works for every monoid `M`.
fn mconcat<M: Monoid>(items: Vec<M>) -> M {
    let mut acc = M::empty();
    for item in items {
        acc = acc.combine(item);
    }
    acc
}

/// Combine each batch, then combine the batch results. A generic function
/// that calls another generic function at the same type.
fn mconcat_batches<M: Monoid>(batches: Vec<Vec<M>>) -> M {
    let partials: Vec<M> = batches.into_iter().map(mconcat).collect();
    mconcat(partials)
}
// ANCHOR_END: generic_code

// ---------------------------------------------------------------------------
// Part 2: the same program after the dictionary-passing translation.
// No trait is involved below: a class is a struct, an instance is a value
// of that struct, and a trait bound is an ordinary parameter.
// ---------------------------------------------------------------------------

// ANCHOR: dict_struct
/// The class `Monoid`, as a record type: one field per method.
struct MonoidDict<M> {
    empty: Box<dyn Fn() -> M>,
    combine: Box<dyn Fn(M, M) -> M>,
}
// ANCHOR_END: dict_struct

// ANCHOR: dict_instances
/// The instance `impl Monoid for Sum`, as a value.
fn sum_dict() -> MonoidDict<Sum> {
    MonoidDict {
        empty: Box::new(|| Sum(0)),
        combine: Box::new(|a, b| Sum(a.0 + b.0)),
    }
}

fn product_dict() -> MonoidDict<Product> {
    MonoidDict {
        empty: Box::new(|| Product(1)),
        combine: Box::new(|a, b| Product(a.0 * b.0)),
    }
}

fn max_dict() -> MonoidDict<Max> {
    MonoidDict {
        empty: Box::new(|| Max(i64::MIN)),
        combine: Box::new(|a, b| Max(a.0.max(b.0))),
    }
}

fn string_dict() -> MonoidDict<String> {
    MonoidDict {
        empty: Box::new(String::new),
        combine: Box::new(|mut a, b| {
            a.push_str(&b);
            a
        }),
    }
}

/// `impl<T> Monoid for Vec<T>` is generic, so its dictionary is built by a
/// generic function: one dictionary per element type.
fn vec_dict<T: 'static>() -> MonoidDict<Vec<T>> {
    MonoidDict {
        empty: Box::new(Vec::new),
        combine: Box::new(|mut a, b| {
            a.extend(b);
            a
        }),
    }
}
// ANCHOR_END: dict_instances

// ANCHOR: dict_pair
/// The instance with a context, `impl<A: Monoid, B: Monoid> Monoid for (A, B)`,
/// becomes a function from dictionaries to a dictionary.
fn pair_dict<A: 'static, B: 'static>(
    da: MonoidDict<A>,
    db: MonoidDict<B>,
) -> MonoidDict<(A, B)> {
    // Move each field of the two dictionaries into the closure that needs it.
    let (empty_a, combine_a) = (da.empty, da.combine);
    let (empty_b, combine_b) = (db.empty, db.combine);
    MonoidDict {
        empty: Box::new(move || (empty_a(), empty_b())),
        combine: Box::new(move |(a1, b1), (a2, b2)| {
            (combine_a(a1, a2), combine_b(b1, b2))
        }),
    }
}
// ANCHOR_END: dict_pair

// ANCHOR: dict_code
/// `mconcat`, translated: the bound `M: Monoid` became the parameter `dict`.
fn mconcat_dict<M>(dict: &MonoidDict<M>, items: Vec<M>) -> M {
    let mut acc = (dict.empty)();
    for item in items {
        acc = (dict.combine)(acc, item);
    }
    acc
}

/// `mconcat_batches`, translated: the dictionary it received is passed on to
/// the functions it calls.
fn mconcat_batches_dict<M>(dict: &MonoidDict<M>, batches: Vec<Vec<M>>) -> M {
    let partials: Vec<M> = batches
        .into_iter()
        .map(|batch| mconcat_dict(dict, batch))
        .collect();
    mconcat_dict(dict, partials)
}
// ANCHOR_END: dict_code

// ---------------------------------------------------------------------------
// Part 3: run both versions on the same inputs.
// ---------------------------------------------------------------------------

/// Print one line per computation and check that both versions agree.
fn report<M: Debug + PartialEq>(label: &str, with_trait: M, with_dict: M) {
    assert_eq!(with_trait, with_dict, "{label}: the two versions disagree");
    let with_trait = format!("{with_trait:?}");
    let with_dict = format!("{with_dict:?}");
    println!("{label:<18} trait: {with_trait:<22} dict: {with_dict}");
}

fn main() {
    // ANCHOR: main_calls
    let readings = [3, 1, 4, 1, 5];

    let sums: Vec<Sum> = readings.iter().map(|&n| Sum(n)).collect();
    report(
        "Sum",
        mconcat(sums.clone()),
        mconcat_dict(&sum_dict(), sums),
    );

    let products: Vec<Product> = readings.iter().map(|&n| Product(n)).collect();
    report(
        "Product",
        mconcat(products.clone()),
        mconcat_dict(&product_dict(), products),
    );

    let words = vec!["dictionary".to_string(), "-".into(), "passing".into()];
    report(
        "String",
        mconcat(words.clone()),
        mconcat_dict(&string_dict(), words),
    );

    let lists = vec![vec![1, 2], vec![], vec![3]];
    report(
        "Vec<i32>",
        mconcat(lists.clone()),
        mconcat_dict(&vec_dict(), lists),
    );

    // The pair instance: total and maximum in one pass.
    let stats: Vec<(Sum, Max)> = readings.iter().map(|&n| (Sum(n), Max(n))).collect();
    report(
        "(Sum, Max)",
        mconcat(stats.clone()),
        mconcat_dict(&pair_dict(sum_dict(), max_dict()), stats),
    );

    // A generic function that calls another generic function.
    let batches = vec![vec![Sum(3), Sum(1)], vec![Sum(4)], vec![Sum(1), Sum(5)]];
    report(
        "batches of Sum",
        mconcat_batches(batches.clone()),
        mconcat_batches_dict(&sum_dict(), batches),
    );
    // ANCHOR_END: main_calls

    // ANCHOR: empty_input
    // On an empty input both versions return the neutral element.
    report(
        "empty (Sum, Prod)",
        mconcat(Vec::<(Sum, Product)>::new()),
        mconcat_dict(&pair_dict(sum_dict(), product_dict()), Vec::new()),
    );
    // ANCHOR_END: empty_input
}
