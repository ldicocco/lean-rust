// harness: run
//! Rust's expressions as instances of typing rules: blocks as nested `let`s,
//! `if` with and without `else`, the never type and its coercion, the empty
//! type `Infallible` and its elimination by an empty `match`, and the
//! difference between structural and nominal types.
//!
//! Run with: `cargo run --example ch03_expressions`

use std::convert::Infallible;

// ANCHOR: block_as_lets
/// A block with `let` statements is a nest of T-Let instances:
/// `{ let a = 2; let b = a + 3; a * b }` is `let a = 2 in let b = a + 3 in a * b`.
fn block_as_lets() -> u32 {
    let a = 2;
    let b = a + 3;
    a * b
}
// ANCHOR_END: block_as_lets

// ANCHOR: if_without_else
/// An `if` without `else` is an `if` whose missing branch is `()`. Rule T-If
/// then forces the `then` branch to have type `()` as well, which is why such
/// an `if` can only be used for its effects.
fn log_if_negative(n: i64, log: &mut Vec<String>) {
    if n < 0 {
        log.push(format!("{n} is negative"));
    }
}
// ANCHOR_END: if_without_else

// ANCHOR: never_positions
/// Expressions of type `!` in four positions. Each of them stands in for a
/// value of whatever type the context expects.
fn first_even(xs: &[u32]) -> u32 {
    let mut i = 0;
    let found: u32 = loop {
        if i == xs.len() {
            return 0; // `return 0` has type `!`, coerced to `u32`
        }
        if xs[i] % 2 == 1 {
            i += 1;
            continue; // `continue` has type `!` too
        }
        break xs[i]; // the loop's type comes from `break`
    };
    let checked: u32 = if found < 1000 {
        found
    } else {
        panic!("too big")
    };
    checked
}
// ANCHOR_END: never_positions

// ANCHOR: infallible
/// `Infallible` is an enum with no variants: a type with no values. A function
/// that receives one can never be called, and its body proves that by
/// matching on the argument with no arms at all.
fn absurd<T>(x: Infallible) -> T {
    match x {}
}

/// A parser that cannot fail, written against an interface that allows
/// failure. With the error type `Infallible`, the pattern `Ok(n)` covers every
/// possible value, so the `let` needs no `else`.
fn parse_len(s: &str) -> Result<usize, Infallible> {
    Ok(s.len())
}

fn use_parse_len() -> usize {
    let Ok(n) = parse_len("hello");
    n
}
// ANCHOR_END: infallible

// ANCHOR: structural_nominal
/// Two structs with the same fields are different types (nominal typing).
struct Meters(f64);
struct Seconds(f64);

/// A type alias is just another name for the same type (structural, or
/// rather, no new type at all).
type Pair = (f64, f64);

fn speed(distance: Meters, time: Seconds) -> f64 {
    distance.0 / time.0
}

fn swap_pair(p: Pair) -> (f64, f64) {
    (p.1, p.0)
}
// ANCHOR_END: structural_nominal

fn main() {
    println!("block_as_lets() = {}", block_as_lets());

    let mut log = Vec::new();
    log_if_negative(-3, &mut log);
    log_if_negative(5, &mut log);
    println!("log = {log:?}");

    println!("first_even(&[3, 5, 8, 9]) = {}", first_even(&[3, 5, 8, 9]));
    println!("first_even(&[1, 3]) = {}", first_even(&[1, 3]));

    println!("use_parse_len() = {}", use_parse_len());
    // `absurd` can be named and passed around, but never called: there is no
    // `Infallible` value to call it with.
    let _never_called: fn(Infallible) -> u32 = absurd::<u32>;

    println!("speed = {}", speed(Meters(100.0), Seconds(8.0)));
    // A `Pair` and a `(f64, f64)` are interchangeable.
    let p: (f64, f64) = (1.0, 2.0);
    println!("swap_pair = {:?}", swap_pair(p));
}
