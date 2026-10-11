// harness: run
//! Expressions and their types: the first judgments of the book, in Rust.
//!
//! Demonstrates: blocks as expressions, the unit type, `if` as an expression
//! whose branches share one type, the never type `!` and its coercion, and a
//! sum computed two ways (the Rust half of the chapter's Gauss example).
//!
//! Run with: `cargo run --example ch01_first_types`

use std::any::type_name_of_val;

// ANCHOR: add
/// The signature is a typing judgment for the body: assuming `x: i32` and
/// `y: i32`, the expression `x + y` has type `i32`.
fn add(x: i32, y: i32) -> i32 {
    x + y
}
// ANCHOR_END: add

// ANCHOR: blocks
fn blocks() {
    // A block is an expression; its value is the value of its last expression.
    let area = {
        let width = 3;
        let height = 4;
        width * height
    };
    // When the block ends with a statement (note the semicolon), there is no
    // final expression: the block evaluates to the unit value `()`.
    let nothing = {
        let width = 3;
        println!("inside the block, width = {width}");
    };
    println!("area    = {area:<4} : {}", type_name_of_val(&area));
    println!("nothing = {nothing:<4?} : {}", type_name_of_val(&nothing));
}
// ANCHOR_END: blocks

// ANCHOR: if_expression
/// `if` is an expression: both branches must have the same type, and that
/// type is the type of the whole `if`.
fn sign(n: i64) -> &'static str {
    if n < 0 {
        "negative"
    } else if n == 0 {
        "zero"
    } else {
        "positive"
    }
}
// ANCHOR_END: if_expression

// ANCHOR: never
/// `parse_digit` returns a `u32` on every path. The `panic!` branch has type
/// `!` (never), which has no values, so it can stand in for a `u32`.
fn parse_digit(c: char) -> u32 {
    match c.to_digit(10) {
        Some(d) => d,
        None => panic!("not a digit: {c:?}"),
    }
}
// ANCHOR_END: never

// ANCHOR: swap
/// For all types `A` and `B`: given an `A` and a `B`, produce a `B` and an `A`.
/// Read as logic: "if A and B, then B and A". Compare with `and_swap` in
/// `Book/Ch01/FirstSteps.lean`.
fn swap<A, B>((a, b): (A, B)) -> (B, A) {
    (b, a)
}
// ANCHOR_END: swap

// ANCHOR: gauss
/// The sum 0 + 1 + ... + n, computed by a loop.
fn sum_to(n: u64) -> u64 {
    (0..=n).sum()
}

/// Gauss's closed form for the same sum.
fn gauss(n: u64) -> u64 {
    n * (n + 1) / 2
}
// ANCHOR_END: gauss

fn main() {
    println!("add(2, 3) = {}", add(2, 3));
    blocks();
    for n in [-7, 0, 42] {
        println!("sign({n}) = {}", sign(n));
    }
    println!("parse_digit('7') = {}", parse_digit('7'));
    println!("swap((1, \"one\")) = {:?}", swap((1, "one")));

    // ANCHOR: gauss_test
    // A test can check the formula for as many values as we have patience for,
    // but only for finitely many. Chapter 1's Lean file proves it for all n.
    for n in 0..=10_000 {
        assert_eq!(sum_to(n), gauss(n), "formula fails at n = {n}");
    }
    println!("sum_to(n) == gauss(n) for every n in 0..=10000");
    // ANCHOR_END: gauss_test
}
