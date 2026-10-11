// harness: run
//! References, regions and permissions: the programs that Chapter 26's
//! compile-fail examples get wrong, written the way the borrow checker accepts
//! them, with comments that say which principle each one respects.
//!
//! Demonstrates: `&T` is `Copy` and `&mut T` is not; many readers or one
//! writer; NLL ending a borrow at its last use; `split_at_mut` splitting a
//! unique permission; lifetimes as region variables (`longer`, a tokenizer
//! whose tokens outlive the borrow of the tokenizer); outlives bounds;
//! `'static`; interior mutability with `Cell` and `RefCell`.
//!
//! Run with: `cargo run --example ch26_aliasing`

use std::cell::{Cell, RefCell};
use std::thread;

// ANCHOR: duplicate
/// Contraction, available only for `Copy` types: the value is used twice.
fn duplicate<T: Copy>(x: T) -> (T, T) {
    (x, x)
}

fn references_are_copy() {
    let report = String::from("sensor report");
    // `String` is not `Copy`, but `&String` is: a shared reference can be
    // duplicated freely, and both copies point to the same string.
    let (r1, r2) = duplicate(&report);
    println!(
        "r1 = {r1:?}, r2 = {r2:?}, same address: {}",
        std::ptr::eq(r1, r2)
    );
    // `duplicate(&mut report)` would not compile: `&mut String` is not `Copy`.
}
// ANCHOR_END: duplicate

// ANCHOR: readers
/// Many readers at once: any number of shared references may coexist, and
/// nobody can mutate the data while they are alive.
fn many_readers() {
    let readings = vec![12, 15, 11];
    let a = &readings;
    let b = &readings;
    let c = a; // copying a reference: a third reader
    let total: i32 = a.iter().sum();
    println!(
        "max {:?}, min {:?}, total {total}",
        b.iter().max(),
        c.iter().min()
    );
}
// ANCHOR_END: readers

// ANCHOR: nll
/// The fix for `ch26_shared_then_mut`: copy the value out, so that the shared
/// borrow ends (at its last use) before the vector is mutated.
fn first_then_push(orders: &mut Vec<u32>) {
    let first = orders[0]; // a `u32` copied out of the vector, not a reference
    orders.push(99);
    println!("first order: {first}, now {} orders", orders.len());
}

/// The fix for `ch26_iterator_invalidation`: read everything first, then
/// mutate. The shared borrow of the loop ends before `extend` begins.
fn repeat_large(orders: &mut Vec<u32>) {
    let large: Vec<u32> = orders.iter().copied().filter(|&a| a > 100).collect();
    orders.extend(large);
    println!("orders after repeating the large ones: {orders:?}");
}
// ANCHOR_END: nll

// ANCHOR: split
/// The fix for `ch26_two_mut`: `split_at_mut` turns one unique permission on
/// the whole slice into two unique permissions on disjoint halves.
fn transfer(accounts: &mut [i64], amount: i64) {
    let (left, right) = accounts.split_at_mut(1);
    let from = &mut left[0];
    let to = &mut right[0];
    *from -= amount;
    *to += amount;
}

/// The fix for `ch26_data_race`: two threads, two disjoint unique permissions.
fn count_in_parallel() -> [u32; 2] {
    let mut counters = [0u32; 2];
    let (first, second) = counters.split_at_mut(1);
    thread::scope(|s| {
        s.spawn(|| first[0] += 10);
        s.spawn(|| second[0] += 20);
    });
    counters
}
// ANCHOR_END: split

// ANCHOR: longer
/// One region variable for both inputs and the output: the result is valid
/// wherever *both* inputs are valid.
fn longer<'a>(a: &'a str, b: &'a str) -> &'a str {
    if a.len() >= b.len() { a } else { b }
}
// ANCHOR_END: longer

// ANCHOR: tokenizer
/// A tokenizer over a borrowed input. The region `'src` is the region of the
/// *input*, not of the tokenizer.
struct Tokenizer<'src> {
    input: &'src str,
    pos: usize,
}

impl<'src> Tokenizer<'src> {
    fn new(input: &'src str) -> Self {
        Tokenizer { input, pos: 0 }
    }

    /// `&mut self` is borrowed only for the call, but the token borrows from
    /// the input, so it lives as long as `'src`, not as long as the call.
    fn next_token(&mut self) -> Option<&'src str> {
        let rest = &self.input[self.pos..];
        let start = rest.find(|c: char| !c.is_whitespace())?;
        let rest = &rest[start..];
        let len = rest.find(char::is_whitespace).unwrap_or(rest.len());
        self.pos += start + len;
        Some(&rest[..len])
    }
}

fn tokens(input: &str) -> Vec<&str> {
    let mut tokenizer = Tokenizer::new(input);
    let mut out = Vec::new();
    while let Some(token) = tokenizer.next_token() {
        out.push(token); // tokens outlive the tokenizer: they borrow `input`
    }
    out
}
// ANCHOR_END: tokenizer

// ANCHOR: outlives
/// An explicit outlives bound: `'long: 'short` lets a `&'long` reference be
/// returned where a `&'short` one is promised.
fn pick<'short, 'long: 'short>(
    fallback: &'long str,
    choice: &'short str,
) -> &'short str {
    if choice.is_empty() { fallback } else { choice }
}

/// `T: 'a` says that every reference inside `T` outlives `'a`, which is what
/// makes a `&'a T` meaningful.
struct Labeled<'a, T: 'a> {
    label: &'static str,
    value: &'a T,
}
// ANCHOR_END: outlives

// ANCHOR: statics
/// `'static`: string literals live in the program's binary; a leaked box
/// lives until the process ends; an owned value moved into a thread satisfies
/// a `'static` bound because it contains no borrowed references at all.
fn statics() -> usize {
    let literal: &'static str = "compiled into the binary";
    let leaked: &'static [u8] = Box::leak(vec![1, 2, 3].into_boxed_slice());
    let readings = vec![4, 5, 6];
    let handle = thread::spawn(move || readings.len()); // the fix for ch26_spawn_borrow
    literal.len() + leaked.len() + handle.join().unwrap()
}
// ANCHOR_END: statics

// ANCHOR: interior
/// `Cell`: mutation through a shared reference, safe because no reference
/// into the cell's contents is ever handed out (values are copied in and out).
struct Sensor {
    name: &'static str,
    reads: Cell<u32>,
}

impl Sensor {
    fn read(&self) -> u32 {
        self.reads.set(self.reads.get() + 1);
        42
    }
}

/// `RefCell`: the aliasing rule checked at run time. The cell counts its
/// shared and unique borrows and refuses a conflicting one.
fn refcell_at_run_time() {
    let log = RefCell::new(vec!["boot"]);
    let reader = log.borrow(); // a shared borrow, counted by the cell
    println!(
        "while reading: try_borrow_mut is {:?}",
        log.try_borrow_mut().map(|_| ())
    );
    drop(reader); // the shared borrow ends
    log.borrow_mut().push("ready"); // now a unique borrow succeeds
    println!("after the reader is gone: {:?}", log.borrow());
}
// ANCHOR_END: interior

fn main() {
    references_are_copy();
    many_readers();

    let mut orders = vec![120, 80, 300];
    first_then_push(&mut orders);
    repeat_large(&mut orders);

    let mut accounts = vec![100, 50];
    transfer(&mut accounts, 30);
    println!("accounts after transfer: {accounts:?}");
    println!("counters from two threads: {:?}", count_in_parallel());

    // ANCHOR: longer_call
    let station = String::from("north station");
    let result;
    {
        let probe = String::from("probe 7");
        result = longer(&station, &probe);
        println!("longer: {result}"); // fine: both inputs are alive here
    }
    // Using `result` here would be E0597: its region is that of `probe` too.
    // ANCHOR_END: longer_call

    println!("tokens: {:?}", tokens("  GET /index.html   HTTP/1.1 "));
    println!("pick: {}", pick("default", ""));
    let threshold = 17;
    let labeled = Labeled {
        label: "threshold",
        value: &threshold,
    };
    println!("{} = {}", labeled.label, labeled.value);
    println!("statics: {}", statics());

    let sensor = Sensor {
        name: "thermometer",
        reads: Cell::new(0),
    };
    let (s1, s2) = duplicate(&sensor);
    let sum = s1.read() + s2.read();
    println!(
        "{}: read twice through two shared references, {} reads, sum {sum}",
        sensor.name,
        sensor.reads.get()
    );
    refcell_at_run_time();
}
