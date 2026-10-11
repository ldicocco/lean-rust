// harness: run
//! The Yoneda lemma as continuation-passing style. A rank-2 type such as
//! `∀B. (A → B) → Vec<B>` is a trait with a generic method; lifting a `Vec<A>`
//! into it and lowering it back are inverse, as long as the implementation is
//! parametric in `B`.
//!
//! Run with: `cargo run --example ch18_yoneda`

use std::mem::size_of;

// ANCHOR: cps
/// `∀B. (A → B) → B`: a value of type `A` in continuation-passing style.
trait Cps<A> {
    fn run<B>(self, k: impl FnOnce(A) -> B) -> B;
}

/// The obvious implementation: hold the value, hand it to the continuation.
struct Value<A>(A);

impl<A> Cps<A> for Value<A> {
    fn run<B>(self, k: impl FnOnce(A) -> B) -> B {
        k(self.0)
    }
}

/// A less obvious one: compute the value only when a continuation arrives.
struct Deferred<F>(F);

impl<A, F: FnOnce() -> A> Cps<A> for Deferred<F> {
    fn run<B>(self, k: impl FnOnce(A) -> B) -> B {
        k((self.0)())
    }
}

/// Lowering: run with the identity continuation.
fn lower_cps<A>(c: impl Cps<A>) -> A {
    c.run(|a| a)
}
// ANCHOR_END: cps

// ANCHOR: yoneda_vec
/// `∀B. (A → B) → Vec<B>`: "whatever you map over me".
trait YonedaVec<A> {
    fn run<B>(self, k: impl FnMut(A) -> B) -> Vec<B>;
}

/// Lifting a vector: map the continuation over it.
struct Lift<A>(Vec<A>);

impl<A> YonedaVec<A> for Lift<A> {
    fn run<B>(self, k: impl FnMut(A) -> B) -> Vec<B> {
        self.0.into_iter().map(k).collect()
    }
}

/// Lowering: run with the identity continuation.
fn lower<A>(y: impl YonedaVec<A>) -> Vec<A> {
    y.run(|a| a)
}

/// An implementation that never stores a `Vec<u32>`: it generates the
/// numbers n, n-1, ..., 1 on demand and feeds them to the continuation.
struct Countdown(u32);

impl YonedaVec<u32> for Countdown {
    fn run<B>(self, k: impl FnMut(u32) -> B) -> Vec<B> {
        (1..=self.0).rev().map(k).collect()
    }
}
// ANCHOR_END: yoneda_vec

// ANCHOR: picky
/// Not parametric in `B`: it returns nothing when `B` is larger than 4 bytes.
/// The trait's signature cannot prevent this, because `size_of` needs no bound.
struct Picky(Vec<u32>);

impl YonedaVec<u32> for Picky {
    fn run<B>(self, k: impl FnMut(u32) -> B) -> Vec<B> {
        if size_of::<B>() > 4 {
            Vec::new()
        } else {
            self.0.into_iter().map(k).collect()
        }
    }
}
// ANCHOR_END: picky

fn main() {
    // ANCHOR: cps_main
    let show = |n: u32| format!("<{n}>");
    println!("Value(42).run(show) = {}", Value(42).run(show));
    println!("lower_cps(Value(42)) = {}", lower_cps(Value(42)));
    let deferred = Deferred(|| 6 * 7);
    println!("lower_cps(Deferred(|| 6 * 7)) = {}", lower_cps(deferred));
    // ANCHOR_END: cps_main

    // ANCHOR: yoneda_main
    // Round trip 1: lower(lift(v)) == v.
    let v = vec![3, 1, 2];
    assert_eq!(lower(Lift(v.clone())), v);
    println!("lower(Lift([3, 1, 2])) = {:?}", lower(Lift(v)));

    // Round trip 2: lift(lower(y)) behaves like y, for every continuation.
    let direct = Countdown(3).run(show);
    let round_trip = Lift(lower(Countdown(3))).run(show);
    assert_eq!(direct, round_trip);
    println!("Countdown(3).run(show)        = {direct:?}");
    println!("Lift(lower(Countdown(3))).run = {round_trip:?}");

    // A non-parametric implementation breaks round trip 2.
    let direct = Picky(vec![3, 1, 2]).run(show);
    let round_trip = Lift(lower(Picky(vec![3, 1, 2]))).run(show);
    assert_ne!(direct, round_trip);
    println!("Picky([3, 1, 2]).run(show)        = {direct:?}");
    println!("Lift(lower(Picky([3, 1, 2]))).run = {round_trip:?}");
    // ANCHOR_END: yoneda_main
}
