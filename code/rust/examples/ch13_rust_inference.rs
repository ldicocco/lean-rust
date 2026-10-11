// harness: run
//! Rust's own type inference, made visible: literal defaulting, information
//! that flows backward from a later use, one signature per closure, generic
//! functions instantiated at each call, and `collect` driven by the type that
//! is asked for, with `_` as a hole in that type.
//!
//! Run with: `cargo run --example ch13_rust_inference`

use std::any::type_name_of_val;
use std::collections::BTreeSet;
use std::num::ParseIntError;

/// Prints a value together with the type that inference chose for it.
fn show<T: std::fmt::Debug>(label: &str, value: &T) {
    let ty = without_paths(type_name_of_val(value));
    let line = format!("{label:<24} : {ty} = {value:?}");
    if line.chars().count() <= 78 {
        println!("{line}");
    } else {
        println!("{label:<24} : {ty}");
        println!("{:<24} = {value:?}", "");
    }
}

/// `alloc::vec::Vec<core::num::error::ParseIntError>` becomes
/// `Vec<ParseIntError>`: drops every `path::` prefix.
fn without_paths(name: &str) -> String {
    let mut out = String::new();
    for c in name.chars() {
        out.push(c);
        if out.ends_with("::") {
            out.truncate(out.len() - 2);
            while out.ends_with(|c: char| c.is_alphanumeric() || c == '_') {
                out.pop();
            }
        }
    }
    out
}

fn literals() {
    // ANCHOR: literals
    let a = 42; // nothing constrains it: {integer} falls back to i32
    let b = 2.5; // {float} falls back to f64
    let c = 42; // an {integer} variable for now...
    let small: u8 = c; // ...that this later use unifies with u8
    let mut total = 0; // likewise, 0 is {integer}...
    total += 3_u64; // ...until it meets a u64
    // ANCHOR_END: literals
    show("let a = 42", &a);
    show("let b = 2.5", &b);
    show("let c = 42 (later u8)", &c);
    show("small", &small);
    show("total (+= 3_u64)", &total);
}

fn later_uses() {
    // ANCHOR: later_uses
    let mut log = Vec::new(); // Vec<?T>: the element type is unknown here
    log.push("started"); // ...and solved here: ?T = &str
    log.push("stopped");

    let add_one = |x| x + 1; // the parameter type is unknown here
    let port = add_one(8079_u16); // ...and fixed by the first call: u16
    // ANCHOR_END: later_uses
    show("log", &log);
    show("add_one(8079_u16)", &port);
}

// ANCHOR: generic_fn
/// A generic item: its type is a scheme, `forall T. T -> T`, instantiated
/// afresh at every call.
fn identity<T>(x: T) -> T {
    x
}
// ANCHOR_END: generic_fn

fn generic_items() {
    // ANCHOR: generic_calls
    let n = identity(5);
    let s = identity("five");
    let v = identity::<Vec<u8>>(vec![]); // turbofish: explicit instantiation
    // ANCHOR_END: generic_calls
    show("identity(5)", &n);
    show("identity(\"five\")", &s);
    show("identity::<Vec<u8>>(..)", &v);
}

fn collecting() {
    let text = "to be or not to be";
    // ANCHOR: collect
    let words = text.split(' ').collect::<Vec<_>>(); // Vec<&str>
    let distinct: BTreeSet<_> = text.split(' ').collect(); // BTreeSet<&str>
    let joined: String = text.split(' ').collect(); // String
    let lengths: Vec<_> = words.iter().map(|w| w.len()).collect(); // Vec<usize>
    let ports: Result<Vec<u16>, _> = "80,443".split(',').map(str::parse).collect();
    let bad: Result<Vec<u16>, ParseIntError> =
        "80,x".split(',').map(str::parse).collect();
    // ANCHOR_END: collect
    show("words", &words);
    show("distinct", &distinct);
    show("joined", &joined);
    show("lengths", &lengths);
    show("ports", &ports);
    show("bad", &bad);
}

fn main() {
    literals();
    later_uses();
    generic_items();
    collecting();
}
