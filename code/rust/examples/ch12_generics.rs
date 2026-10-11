// harness: run
//! Rust generics as System F's ∀, compiled by monomorphization.
//!
//! Demonstrates: type parameters as type abstraction, the turbofish as
//! explicit type application, one compiled copy per instantiation (made
//! visible with `type_name_of_val`), what the copies look like when written by
//! hand, trait bounds as bounded quantification, and the alternative of a
//! single copy working on a uniform representation (`dyn`).
//!
//! Run with: `cargo run --example ch12_generics`

use std::any::{type_name, type_name_of_val};
use std::fmt::Display;
use std::mem::size_of;

// ANCHOR: id
/// Λα. λ(x : α). x — the polymorphic identity. Its type is ∀α. α → α.
fn id<T>(x: T) -> T {
    x
}
// ANCHOR_END: id

// ANCHOR: compose
/// ∀α β γ. (β → γ) → (α → β) → α → γ
fn compose<A, B, C>(g: impl Fn(B) -> C, f: impl Fn(A) -> B) -> impl Fn(A) -> C {
    move |x| g(f(x))
}
// ANCHOR_END: compose

// ANCHOR: largest
/// ∀T. (T: PartialOrd + Copy) ⇒ &[T] → T. The first line reports which
/// compiled copy of the function is running.
fn largest<T: PartialOrd + Copy>(items: &[T]) -> T {
    println!("  running {}", type_name_of_val(&largest::<T>));
    let mut best = items[0];
    for &item in items {
        if item > best {
            best = item;
        }
    }
    best
}
// ANCHOR_END: largest

// ANCHOR: by_hand
/// What monomorphization produces for `largest::<i32>`, written by hand:
/// `T` replaced by `i32` everywhere, and `>` compiled to an integer compare.
fn largest_i32(items: &[i32]) -> i32 {
    let mut best = items[0];
    for &item in items {
        if item > best {
            best = item;
        }
    }
    best
}

/// And for `largest::<char>`: the same text, different machine code.
fn largest_char(items: &[char]) -> char {
    let mut best = items[0];
    for &item in items {
        if item > best {
            best = item;
        }
    }
    best
}
// ANCHOR_END: by_hand

// ANCHOR: layout
/// Each copy knows the size of its `T` as a compile-time constant. A
/// language that erases types (one copy for every `T`) could not offer this.
fn layout<T>() -> String {
    format!("{:<22} {:>2} bytes", type_name::<T>(), size_of::<T>())
}
// ANCHOR_END: layout

// ANCHOR: uniform
/// The other strategy: one compiled function for every element type, working
/// on a uniform representation (a pointer to the data plus a pointer to a
/// table of functions). Chapter 15 studies `dyn` in detail.
fn show_all(items: &[&dyn Display]) -> String {
    let parts: Vec<String> = items.iter().map(|item| item.to_string()).collect();
    parts.join(", ")
}

/// The monomorphized counterpart: one copy per `T`, and all items must have
/// the same type.
fn show_all_generic<T: Display>(items: &[T]) -> String {
    let parts: Vec<String> = items.iter().map(|item| item.to_string()).collect();
    parts.join(", ")
}
// ANCHOR_END: uniform

fn main() {
    // ANCHOR: turbofish
    // Type application, explicit (the turbofish) and inferred.
    let a = id::<u8>(7); // id [u8] 7
    let b = id(String::from("seven")); // id [String] "seven", inferred
    let n = "42".parse::<i64>().expect("a number"); // parse [i64]
    let squares = (1..=4).map(|x| x * x).collect::<Vec<u32>>();
    println!("{a} {b} {n} {squares:?}");

    let shout = compose(|s: String| s + "!", |n: u32| n.to_string());
    println!("compose: {}", shout(42));
    // ANCHOR_END: turbofish

    // ANCHOR: run_largest
    let big_int = largest(&[3, 9, 4]);
    let big_char = largest(&['q', 'z', 'a']);
    let big_float = largest(&[2.5, 1.5]);
    println!("results: {big_int} {big_char} {big_float}");
    assert_eq!(big_int, largest_i32(&[3, 9, 4]));
    assert_eq!(big_char, largest_char(&['q', 'z', 'a']));
    // ANCHOR_END: run_largest

    // ANCHOR: run_layout
    println!("{}", layout::<u8>());
    println!("{}", layout::<(u8, u32)>());
    println!("{}", layout::<String>());
    println!("{}", layout::<&str>());
    // ANCHOR_END: run_layout

    // ANCHOR: run_uniform
    println!("dyn:     {}", show_all(&[&1, &"two", &3.5]));
    println!("generic: {}", show_all_generic(&[1, 2, 3]));
    println!("size_of::<&i32>()          = {}", size_of::<&i32>());
    println!("size_of::<&dyn Display>()  = {}", size_of::<&dyn Display>());
    // ANCHOR_END: run_uniform
}
