// harness: run
//! Natural transformations in Rust: naturality squares checked on samples for
//! `first`, `Option::into_iter`, `reverse` and `len`, and then the ways a Rust
//! generic function can break parametricity: trait bounds, `size_of`, `Any`
//! and panics.
//!
//! Run with: `cargo run --example ch18_naturality`

use std::any::Any;
use std::fmt::Debug;
use std::mem::size_of;

// ANCHOR: transformations
/// Vec ⇒ Option: the first element, if any.
fn first<T>(v: Vec<T>) -> Option<T> {
    v.into_iter().next()
}

/// Option ⇒ Vec: zero or one element (this is `Option::into_iter`, collected).
fn option_to_vec<T>(o: Option<T>) -> Vec<T> {
    o.into_iter().collect()
}

/// Vec ⇒ Vec: the same elements in the opposite order.
fn reverse<T>(mut v: Vec<T>) -> Vec<T> {
    v.reverse();
    v
}

/// Vec ⇒ Const<usize>: the length. Mapping never changes it.
fn len<T>(v: Vec<T>) -> usize {
    v.len()
}
// ANCHOR_END: transformations

// ANCHOR: square
/// Checks one naturality square on one input `x : F<A>`.
///
/// Without higher-kinded types we cannot write "for every functor F", so the
/// caller passes the two components (`eta_a`, `eta_b`) and the two lifted
/// maps (`map_f` is F(f), `map_g` is G(f)) as ordinary closures.
fn square<FA, FB, GA, GB>(
    x: FA,
    eta_a: impl Fn(FA) -> GA,
    eta_b: impl Fn(FB) -> GB,
    map_f: impl Fn(FA) -> FB,
    map_g: impl Fn(GA) -> GB,
) -> (GB, GB)
where
    FA: Clone,
{
    let right_then_down = eta_b(map_f(x.clone())); // map first, then transform
    let down_then_right = map_g(eta_a(x)); // transform first, then map
    (right_then_down, down_then_right)
}

/// `map` for vectors, written out so that the squares below read clearly.
fn vmap<A, B>(f: impl Fn(A) -> B) -> impl Fn(Vec<A>) -> Vec<B> {
    move |v| v.into_iter().map(&f).collect()
}

fn report<T: PartialEq + Debug>(name: &str, input: &str, (lhs, rhs): (T, T)) {
    let verdict = if lhs == rhs { "commutes" } else { "FAILS" };
    println!("{name:<14} {input:<11} {lhs:?} vs {rhs:?}: {verdict}");
}
// ANCHOR_END: square

// ANCHOR: bounded
/// Needs `Ord`: it compares elements, so it is natural only for maps that
/// preserve the order.
fn largest<T: Ord>(v: Vec<T>) -> Option<T> {
    v.into_iter().max()
}

/// Needs `PartialEq`: it compares neighbors, so it is natural only for maps
/// that never make two different elements equal.
fn dedup<T: PartialEq>(mut v: Vec<T>) -> Vec<T> {
    v.dedup();
    v
}
// ANCHOR_END: bounded

// ANCHOR: leaks
/// Type `fn<T>(&T) -> usize`, no bound at all, yet not constant.
fn weigh<T>(_: &T) -> usize {
    size_of::<T>()
}

/// Type `fn<T: Any>(T) -> T`, but not the identity: it negates booleans.
fn sneaky_id<T: Any>(x: T) -> T {
    let mut boxed: Box<dyn Any> = Box::new(x);
    if let Some(b) = boxed.downcast_mut::<bool>() {
        *b = !*b;
    }
    *boxed.downcast::<T>().expect("the box still holds a T")
}

/// Type `fn<T>(T) -> T`, and never returns: `panic!` has type `!`.
fn stubborn<T>(_: T) -> T {
    panic!("no value of type T to return")
}
// ANCHOR_END: leaks

fn main() {
    // ANCHOR: squares_main
    let tens = |n: i32| n * 10;
    let show = |n: i32| format!("<{n}>");
    report(
        "first",
        "[3, 1, 2]",
        square(vec![3, 1, 2], first, first, vmap(show), |o| o.map(show)),
    );
    report(
        "first",
        "[]",
        square(vec![], first, first, vmap(show), |o| o.map(show)),
    );
    report(
        "option_to_vec",
        "Some(7)",
        square(
            Some(7),
            option_to_vec,
            option_to_vec,
            |o| o.map(tens),
            vmap(tens),
        ),
    );
    report(
        "reverse",
        "[3, 1, 2]",
        square(vec![3, 1, 2], reverse, reverse, vmap(show), vmap(show)),
    );
    report(
        "len",
        "[3, 1, 2]",
        square(vec![3, 1, 2], len, len, vmap(show), |n| n),
    );
    // ANCHOR_END: squares_main

    // ANCHOR: bounded_main
    println!();
    let negate = |n: i32| -n;
    let parity = |n: i32| n % 2;
    let input = vec![3, 1, 2];
    report(
        "largest, *10",
        "[3, 1, 2]",
        square(input.clone(), largest, largest, vmap(tens), |o| o.map(tens)),
    );
    report(
        "largest, neg",
        "[3, 1, 2]",
        square(input.clone(), largest, largest, vmap(negate), |o| {
            o.map(negate)
        }),
    );
    report(
        "dedup, *10",
        "[3, 1, 2]",
        square(input.clone(), dedup, dedup, vmap(tens), vmap(tens)),
    );
    report(
        "dedup, %2",
        "[3, 1, 2]",
        square(input, dedup, dedup, vmap(parity), vmap(parity)),
    );
    // ANCHOR_END: bounded_main

    // ANCHOR: leaks_main
    println!();
    println!(
        "weigh(&1u8) = {}, weigh(&1u64) = {}",
        weigh(&1u8),
        weigh(&1u64)
    );
    println!("weigh(&String::new()) = {}", weigh(&String::new()));
    println!(
        "sneaky_id(5) = {}, sneaky_id(true) = {}",
        sneaky_id(5),
        sneaky_id(true)
    );

    // Silence the default panic message, run `stubborn`, restore the hook.
    let previous_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let outcome = std::panic::catch_unwind(|| stubborn(7));
    std::panic::set_hook(previous_hook);
    println!("stubborn(7) returned normally: {}", outcome.is_ok());
    // ANCHOR_END: leaks_main

    // The example doubles as a test of the claims made in the text.
    let (lhs, rhs) = square(vec![3, 1, 2], reverse, reverse, vmap(show), vmap(show));
    assert_eq!(lhs, rhs);
    let (lhs, rhs) = square(vec![3, 1, 2], largest, largest, vmap(negate), |o| {
        o.map(negate)
    });
    assert_ne!(lhs, rhs);
    assert_ne!(weigh(&1u8), weigh(&1u64));
    assert!(!sneaky_id(true));
    assert!(outcome.is_err());
}
