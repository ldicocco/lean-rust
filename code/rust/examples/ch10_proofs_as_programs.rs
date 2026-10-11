// harness: run
//! Proofs as programs: the propositional tautologies of Chapter 10 as generic
//! Rust functions, contraction made explicit with `Clone`, a "subtype" as a
//! newtype with a private field, and the three ways in which every Rust type
//! is inhabited (`loop {}`, `panic!`, `todo!`), which make Rust inconsistent as
//! a logic.
//!
//! Run with: `cargo run --example ch10_proofs_as_programs`

use std::panic;

// ANCHOR: connectives
/// Falsity, ⊥: a type with no values at all.
enum Void {}

/// Disjunction, A ∨ B: a value of one of two types, tagged with which.
#[derive(Debug, PartialEq)]
enum Either<A, B> {
    Left(A),
    Right(B),
}
// Conjunction A ∧ B is the pair (A, B); truth ⊤ is the unit type ();
// implication A → B is a function; negation ¬A is a function A → Void.
// ANCHOR_END: connectives

// ANCHOR: conjunction
/// ∧-introduction: from proofs of A and B, a proof of A ∧ B.
fn and_intro<A, B>(a: A, b: B) -> (A, B) {
    (a, b)
}

/// ∧-elimination: from A ∧ B, a proof of A (and, symmetrically, of B).
fn and_elim_left<A, B>(pair: (A, B)) -> A {
    pair.0
}

/// A ∧ B → B ∧ A
fn and_comm<A, B>((a, b): (A, B)) -> (B, A) {
    (b, a)
}
// ANCHOR_END: conjunction

// ANCHOR: disjunction
/// ∨-introduction on the left: from A, a proof of A ∨ B.
fn or_intro_left<A, B>(a: A) -> Either<A, B> {
    Either::Left(a)
}

/// ∨-elimination: if A → C and B → C, then A ∨ B → C. It is a `match`.
fn or_elim<A, B, C>(
    e: Either<A, B>,
    if_left: impl FnOnce(A) -> C,
    if_right: impl FnOnce(B) -> C,
) -> C {
    match e {
        Either::Left(a) => if_left(a),
        Either::Right(b) => if_right(b),
    }
}

/// A ∨ B → B ∨ A
fn or_comm<A, B>(e: Either<A, B>) -> Either<B, A> {
    or_elim(e, Either::Right, Either::Left)
}
// ANCHOR_END: disjunction

// ANCHOR: implication
/// →-elimination (modus ponens): from A → B and A, a proof of B.
fn modus_ponens<A, B>(f: impl FnOnce(A) -> B, a: A) -> B {
    f(a)
}

/// (A → B) → (B → C) → (A → C): composition.
fn compose<A, B, C>(
    f: impl FnOnce(A) -> B,
    g: impl FnOnce(B) -> C,
) -> impl FnOnce(A) -> C {
    move |a| g(f(a))
}

/// (A → B → C) → (A ∧ B → C): uncurrying.
fn uncurry<A, B, C, G>(f: impl FnOnce(A) -> G) -> impl FnOnce((A, B)) -> C
where
    G: FnOnce(B) -> C,
{
    move |(a, b)| f(a)(b)
}

/// A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C): distributivity.
fn distribute<A, B, C>((a, bc): (A, Either<B, C>)) -> Either<(A, B), (A, C)> {
    match bc {
        Either::Left(b) => Either::Left((a, b)),
        Either::Right(c) => Either::Right((a, c)),
    }
}
// ANCHOR_END: implication

// ANCHOR: negation
/// ⊥ → A: ex falso quodlibet. A `match` with no arms covers every case of a
/// type with no values, and so it can have any type.
fn ex_falso<A>(v: Void) -> A {
    match v {}
}

/// A → ¬¬A: given A, any refutation of A can be refuted.
fn double_negation_intro<A, N>(a: A) -> impl FnOnce(N) -> Void
where
    N: FnOnce(A) -> Void,
{
    move |not_a| not_a(a)
}

/// (A → B) → (¬B → ¬A): contraposition.
fn contrapositive<A, B, F, NB>(f: F, not_b: NB) -> impl FnOnce(A) -> Void
where
    F: FnOnce(A) -> B,
    NB: FnOnce(B) -> Void,
{
    move |a| not_b(f(a))
}

/// ¬(A ∧ ¬A): no contradiction.
fn non_contradiction<A, N>((a, not_a): (A, N)) -> Void
where
    N: FnOnce(A) -> Void,
{
    not_a(a)
}

/// ¬A ∧ ¬B → ¬(A ∨ B): each refutation is used at most once.
fn de_morgan_and<A, B, NA, NB>(
    not_a: NA,
    not_b: NB,
) -> impl FnOnce(Either<A, B>) -> Void
where
    NA: FnOnce(A) -> Void,
    NB: FnOnce(B) -> Void,
{
    move |e| match e {
        Either::Left(a) => not_a(a),
        Either::Right(b) => not_b(b),
    }
}
// ANCHOR_END: negation

// ANCHOR: contraction
/// ¬(A ∨ B) → ¬A ∧ ¬B. The hypothesis is needed twice, once in each
/// component: that is contraction, and Rust makes us ask for it with `Clone`.
fn de_morgan_or<A, B, N>(n: N) -> (impl FnOnce(A) -> Void, impl FnOnce(B) -> Void)
where
    N: FnOnce(Either<A, B>) -> Void + Clone,
{
    let n2 = n.clone(); // contraction, spelled out
    (move |a| n(Either::Left(a)), move |b| n2(Either::Right(b)))
}

/// A → A ∧ A, the purest form of contraction: it needs `Clone` too.
fn dup<A: Clone>(a: A) -> (A, A) {
    (a.clone(), a)
}
// ANCHOR_END: contraction

// ANCHOR: generics
/// ∀A. A → A: a generic function is a proof for every type at once.
fn identity<A>(a: A) -> A {
    a
}

/// ∃T. T: Display. The caller learns that *some* displayable type comes back,
/// not which one: the witness (here `u32`) is hidden.
fn some_displayable() -> impl std::fmt::Display {
    42_u32
}
// ANCHOR_END: generics

// ANCHOR: subtype
/// The closest Rust gets to Lean's `{ v : Vec<u32> // sorted v }`: a value
/// together with an invariant. The field is private, so the only way to get a
/// `Sorted` is through `Sorted::new`, which checks. The "proof" lives in this
/// module's code, not in the type.
mod sorted {
    pub struct Sorted(Vec<u32>);

    impl Sorted {
        pub fn new(mut v: Vec<u32>) -> Sorted {
            v.sort();
            Sorted(v)
        }

        pub fn as_slice(&self) -> &[u32] {
            &self.0
        }

        /// Relies on the invariant: the smallest element comes first.
        pub fn min(&self) -> Option<u32> {
            self.0.first().copied()
        }
    }
}
// ANCHOR_END: subtype

// ANCHOR: inconsistent
/// "Proofs" of every proposition. Each one type-checks.
#[allow(dead_code)]
fn by_looping<A>() -> A {
    loop {}
}

fn by_panicking<A>() -> A {
    panic!("this proof has nothing inside")
}

#[allow(dead_code)]
fn by_todo<A>() -> A {
    todo!()
}

#[allow(dead_code, unconditional_recursion)]
fn by_recursion<A>() -> A {
    by_recursion() // the compiler warns (a lint), but accepts
}

/// A "proof" of falsity. It compiles.
#[allow(dead_code)]
fn proof_of_false() -> Void {
    by_looping()
}
// ANCHOR_END: inconsistent

fn main() {
    // ANCHOR: main_dictionary
    let show = |label: &str, value: String| println!("{label:<28} = {value}");
    show(
        "and_comm((1, \"one\"))",
        format!("{:?}", and_comm((1, "one"))),
    );
    show(
        "and_elim_left(('a', 2.5))",
        format!("{:?}", and_elim_left(and_intro('a', 2.5))),
    );
    let e: Either<u8, &str> = or_intro_left(7);
    show("or_comm(Left(7))", format!("{:?}", or_comm(e)));
    let len_is_even = compose(|s: &str| s.len(), |n: usize| n % 2 == 0);
    show(
        "compose(len, even)(\"four\")",
        format!("{}", len_is_even("four")),
    );
    show(
        "modus_ponens(double, 21)",
        format!("{}", modus_ponens(|x: i32| 2 * x, 21)),
    );
    let add = uncurry(|a: i32| move |b: i32| a + b);
    show("uncurry(add)((2, 3))", format!("{}", add((2, 3))));
    let pair = (1, Either::<bool, char>::Right('c'));
    show(
        "distribute((1, Right('c')))",
        format!("{:?}", distribute(pair)),
    );
    show(
        "dup(String::from(\"x\"))",
        format!("{:?}", dup(String::from("x"))),
    );
    show("identity(\"same\")", format!("{:?}", identity("same")));
    show("some_displayable()", format!("{}", some_displayable()));
    // ANCHOR_END: main_dictionary

    // ANCHOR: main_subtype
    let s = sorted::Sorted::new(vec![5, 3, 9, 1]);
    println!("Sorted::new(vec![5, 3, 9, 1]) holds {:?}", s.as_slice());
    println!("its minimum, read off the front: {:?}", s.min());
    // ANCHOR_END: main_subtype

    // ANCHOR: main_inconsistent
    // Running a "proof" by panicking: the program compiled, but the proof was
    // never there. (The panic message is silenced; we only report it.)
    panic::set_hook(Box::new(|_| {}));
    let outcome = panic::catch_unwind(|| {
        let n: u32 = by_panicking();
        n
    });
    match outcome {
        Ok(n) => println!("by_panicking::<u32>() returned {n}"),
        Err(_) => {
            println!("by_panicking::<u32>() panicked: no value was ever produced")
        }
    }
    // ANCHOR_END: main_inconsistent

    // The negation proofs cannot be run in a meaningful way (nobody can call a
    // refutation of an inhabited type), but they type-check, and that is the
    // point: the compiler is the proof checker. We mention them so that they
    // are not dead code.
    let _checked = (
        double_negation_intro::<u8, fn(u8) -> Void>,
        contrapositive::<u8, u8, fn(u8) -> u8, fn(u8) -> Void>,
        non_contradiction::<u8, fn(u8) -> Void>,
        de_morgan_and::<u8, u8, fn(u8) -> Void, fn(u8) -> Void>,
        de_morgan_or::<u8, u8, fn(Either<u8, u8>) -> Void>,
        ex_falso::<u8>,
    );
}
