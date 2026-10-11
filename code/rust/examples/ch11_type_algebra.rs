// harness: run
//! The algebra of types: sums, products, the unit and empty types, counting
//! their values, isomorphisms checked by round trips, and memory layout.
//!
//! Demonstrates: `Either` and `Void`, the empty `match`, isomorphisms as pairs
//! of functions with round-trip assertions (exhaustive on finite types,
//! pointwise for function types), cardinalities computed by a trait, and a
//! `size_of` table showing the niche optimization.
//!
//! Run with: `cargo run --example ch11_type_algebra`

use std::convert::Infallible;
use std::fmt::Debug;
use std::mem::size_of;
use std::num::NonZeroU32;

// ANCHOR: either_void
/// The sum type A + B: a value is an `A` or a `B`, tagged with which one.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Either<A, B> {
    Left(A),
    Right(B),
}

/// The empty type 0: no variants, hence no values.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Void {}

/// The elimination rule for 0: a `match` with no arms. It type-checks at any
/// result type `T` because there is no case to handle.
fn absurd<T>(v: Void) -> T {
    match v {}
}
// ANCHOR_END: either_void

// ANCHOR: finite
/// Types with finitely many values, listed explicitly. `CARD` is computed
/// from the structure of the type, `all()` enumerates the values; the
/// counting laws say the two must agree.
trait Finite: Sized {
    const CARD: usize;
    fn all() -> Vec<Self>;
}

impl Finite for Void {
    const CARD: usize = 0;
    fn all() -> Vec<Self> {
        vec![]
    }
}

impl Finite for () {
    const CARD: usize = 1;
    fn all() -> Vec<Self> {
        vec![()]
    }
}

impl Finite for bool {
    const CARD: usize = 2;
    fn all() -> Vec<Self> {
        vec![false, true]
    }
}

/// |A × B| = |A| · |B|
impl<A: Finite + Clone, B: Finite + Clone> Finite for (A, B) {
    const CARD: usize = A::CARD * B::CARD;
    fn all() -> Vec<Self> {
        let mut out = Vec::new();
        for a in A::all() {
            for b in B::all() {
                out.push((a.clone(), b));
            }
        }
        out
    }
}

/// |A + B| = |A| + |B|
impl<A: Finite, B: Finite> Finite for Either<A, B> {
    const CARD: usize = A::CARD + B::CARD;
    fn all() -> Vec<Self> {
        let lefts = A::all().into_iter().map(Either::Left);
        let rights = B::all().into_iter().map(Either::Right);
        lefts.chain(rights).collect()
    }
}

/// |Option A| = 1 + |A|
impl<A: Finite> Finite for Option<A> {
    const CARD: usize = 1 + A::CARD;
    fn all() -> Vec<Self> {
        std::iter::once(None)
            .chain(A::all().into_iter().map(Some))
            .collect()
    }
}

/// |Result<T, E>| = |T| + |E|
impl<T: Finite, E: Finite> Finite for Result<T, E> {
    const CARD: usize = T::CARD + E::CARD;
    fn all() -> Vec<Self> {
        let oks = T::all().into_iter().map(Ok);
        let errs = E::all().into_iter().map(Err);
        oks.chain(errs).collect()
    }
}
// ANCHOR_END: finite

// ANCHOR: exponential
/// |A → B| = |B| ^ |A|: one independent choice in B for each value of A.
/// (We only count functions here; enumerating them is an exercise.)
const fn pow(base: usize, exp: usize) -> usize {
    let mut result = 1;
    let mut i = 0;
    while i < exp {
        result *= base;
        i += 1;
    }
    result
}

fn card_fn<A: Finite, B: Finite>() -> usize {
    pow(B::CARD, A::CARD)
}
// ANCHOR_END: exponential

// ANCHOR: iso
/// An isomorphism: two functions that undo each other.
struct Iso<A, B> {
    name: &'static str,
    forward: fn(A) -> B,
    backward: fn(B) -> A,
}

impl<A, B> Iso<A, B>
where
    A: Finite + Clone + PartialEq + Debug,
    B: Finite + Clone + PartialEq + Debug,
{
    /// Check both round trips on *every* value of both types. For these
    /// particular finite instances this is a complete proof; for all types at
    /// once we need Lean.
    fn check(&self) {
        for a in A::all() {
            assert_eq!((self.backward)((self.forward)(a.clone())), a);
        }
        for b in B::all() {
            assert_eq!((self.forward)((self.backward)(b.clone())), b);
        }
        assert_eq!(A::CARD, B::CARD);
        println!("{:<26} ok: {} values each side", self.name, A::CARD);
    }
}
// ANCHOR_END: iso

// ANCHOR: iso_functions
/// A × 1 ≅ A
fn drop_unit<A>((a, ()): (A, ())) -> A {
    a
}
fn add_unit<A>(a: A) -> (A, ()) {
    (a, ())
}

/// A + 0 ≅ A: the `Right` case cannot happen, and `absurd` says so.
fn drop_void<A>(e: Either<A, Void>) -> A {
    match e {
        Either::Left(a) => a,
        Either::Right(v) => absurd(v),
    }
}
fn add_void<A>(a: A) -> Either<A, Void> {
    Either::Left(a)
}

/// A × (B + C) ≅ A × B + A × C
fn distribute<A, B, C>((a, bc): (A, Either<B, C>)) -> Either<(A, B), (A, C)> {
    match bc {
        Either::Left(b) => Either::Left((a, b)),
        Either::Right(c) => Either::Right((a, c)),
    }
}
fn factor<A, B, C>(e: Either<(A, B), (A, C)>) -> (A, Either<B, C>) {
    match e {
        Either::Left((a, b)) => (a, Either::Left(b)),
        Either::Right((a, c)) => (a, Either::Right(c)),
    }
}

/// Option A ≅ 1 + A
fn option_to_sum<A>(o: Option<A>) -> Either<(), A> {
    match o {
        None => Either::Left(()),
        Some(a) => Either::Right(a),
    }
}
fn sum_to_option<A>(e: Either<(), A>) -> Option<A> {
    match e {
        Either::Left(()) => None,
        Either::Right(a) => Some(a),
    }
}

/// bool ≅ 1 + 1
fn bool_to_sum(b: bool) -> Either<(), ()> {
    if b {
        Either::Left(())
    } else {
        Either::Right(())
    }
}
fn sum_to_bool(e: Either<(), ()>) -> bool {
    matches!(e, Either::Left(()))
}
// ANCHOR_END: iso_functions

// ANCHOR: curry
/// (A × B → C) ≅ (A → (B → C)). The inner function must own a copy of `a`
/// and of `f`, which is why Rust asks for `Clone` and a box.
fn curry<A, B, C, F>(f: F) -> impl Fn(A) -> Box<dyn Fn(B) -> C>
where
    A: Clone + 'static,
    B: 'static,
    C: 'static,
    F: Fn((A, B)) -> C + Clone + 'static,
{
    move |a: A| {
        let f = f.clone();
        Box::new(move |b: B| f((a.clone(), b)))
    }
}

fn uncurry<A, B, C, G, H>(g: G) -> impl Fn((A, B)) -> C
where
    G: Fn(A) -> H,
    H: Fn(B) -> C,
{
    move |(a, b)| g(a)(b)
}
// ANCHOR_END: curry

// ANCHOR: layout
fn layout_table() {
    fn row<T>(name: &str, values: &str) {
        println!("{name:<26} {values:>9} {:>6}", size_of::<T>());
    }
    println!("{:<26} {:>9} {:>6}", "type", "values", "bytes");
    row::<()>("()", "1");
    row::<Void>("Void", "0");
    row::<bool>("bool", "2");
    row::<Option<bool>>("Option<bool>", "3");
    row::<Option<Option<bool>>>("Option<Option<bool>>", "4");
    row::<u32>("u32", "2^32");
    row::<Option<u32>>("Option<u32>", "1+2^32");
    row::<NonZeroU32>("NonZeroU32", "2^32-1");
    row::<Option<NonZeroU32>>("Option<NonZeroU32>", "2^32");
    row::<char>("char", "1112064");
    row::<Option<char>>("Option<char>", "1112065");
    row::<&u8>("&u8", "");
    row::<Option<&u8>>("Option<&u8>", "");
    row::<Box<u64>>("Box<u64>", "");
    row::<Option<Box<u64>>>("Option<Box<u64>>", "");
    row::<Vec<u8>>("Vec<u8>", "");
    row::<Option<Vec<u8>>>("Option<Vec<u8>>", "");
    row::<Result<u32, Infallible>>("Result<u32, Infallible>", "2^32");
    row::<(u8, u32)>("(u8, u32)", "2^40");
    row::<Option<(u8, u32)>>("Option<(u8, u32)>", "1+2^40");
}
// ANCHOR_END: layout

fn main() {
    // ANCHOR: run_isos
    Iso {
        name: "A × 1 ≅ A",
        forward: drop_unit::<Option<bool>>,
        backward: add_unit,
    }
    .check();
    Iso {
        name: "A + 0 ≅ A",
        forward: drop_void::<(bool, bool)>,
        backward: add_void,
    }
    .check();
    Iso {
        name: "A × (B + C) ≅ A×B + A×C",
        forward: distribute::<bool, Option<bool>, ()>,
        backward: factor,
    }
    .check();
    Iso {
        name: "Option A ≅ 1 + A",
        forward: option_to_sum::<bool>,
        backward: sum_to_option,
    }
    .check();
    Iso {
        name: "bool ≅ 1 + 1",
        forward: bool_to_sum,
        backward: sum_to_bool,
    }
    .check();
    // The standard library's `transpose` methods: 1 + (A + E) ≅ (1 + A) + E.
    Iso {
        name: "1 + (A + E) ≅ (1 + A) + E",
        forward: Option::<Result<bool, ()>>::transpose,
        backward: Result::<Option<bool>, ()>::transpose,
    }
    .check();
    // ANCHOR_END: run_isos

    // ANCHOR: run_curry
    // Function types cannot be compared for equality, so we check the round
    // trip pointwise: on every argument we try, the functions agree.
    let f = |(a, b): (u32, u32)| 10 * a + b;
    let back_again = uncurry(curry(f));
    for a in 0..10 {
        for b in 0..10 {
            assert_eq!(back_again((a, b)), f((a, b)));
            assert_eq!(curry(f)(a)(b), f((a, b)));
        }
    }
    println!("{:<26} ok: agree on 100 arguments", "C^(A×B) ≅ (C^B)^A");
    // ANCHOR_END: run_curry

    // ANCHOR: run_counting
    println!();
    println!(
        "|(bool, Option<bool>)|      = {}",
        <(bool, Option<bool>)>::CARD
    );
    println!("|Either<bool, ()>|          = {}", <Either<bool, ()>>::CARD);
    println!(
        "|bool -> Option<bool>|      = {}",
        card_fn::<bool, Option<bool>>()
    );
    println!(
        "|Option<bool> -> bool|      = {}",
        card_fn::<Option<bool>, bool>()
    );
    println!("|Void -> bool|              = {}", card_fn::<Void, bool>());
    println!("|bool -> Void|              = {}", card_fn::<bool, Void>());
    println!("|Void -> Void|              = {}", card_fn::<Void, Void>());
    // The formula and the enumeration agree.
    assert_eq!(
        <(bool, Option<bool>)>::all().len(),
        <(bool, Option<bool>)>::CARD
    );
    assert_eq!(<Either<bool, Option<()>>>::all().len(), 4);
    // ANCHOR_END: run_counting

    println!();
    layout_table();

    // ANCHOR: niche_asserts
    // The niche optimization, as assertions: when the payload has a bit
    // pattern that no valid value uses, `Option` stores `None` there.
    assert_eq!(size_of::<Option<&u8>>(), size_of::<&u8>());
    assert_eq!(size_of::<Option<Box<u64>>>(), size_of::<Box<u64>>());
    assert_eq!(size_of::<Option<NonZeroU32>>(), size_of::<u32>());
    assert!(size_of::<Option<u32>>() > size_of::<u32>());
    // ANCHOR_END: niche_asserts
}
