// harness: run
//! Functions in Rust: fn items, fn pointers, closures and their anonymous
//! types, capture modes, the `Fn`/`FnMut`/`FnOnce` traits, `impl Fn` and
//! `dyn Fn`, and what currying costs.
//!
//! Run with: `cargo run --example ch08_closures`

use std::any::type_name_of_val;
use std::mem::size_of_val;
use std::sync::atomic::{AtomicUsize, Ordering};

// ANCHOR: fn_items
fn add_one(x: u32) -> u32 {
    x + 1
}

fn double(x: u32) -> u32 {
    x * 2
}
// ANCHOR_END: fn_items

// ANCHOR: callers
/// Calls `f` twice. `Fn` means: callable through a shared reference.
fn call_twice(f: impl Fn() -> u32) -> u32 {
    f() + f()
}

/// Calls `f` twice. `FnMut` means: callable through a mutable reference.
fn call_twice_mut(mut f: impl FnMut() -> u32) -> u32 {
    f() + f()
}

/// Calls `f` once. `FnOnce` means: callable by value, consuming it.
fn call_once(f: impl FnOnce() -> String) -> String {
    f()
}
// ANCHOR_END: callers

// ANCHOR: fee
/// A fee of `percent` percent on `amount` cents.
fn fee(percent: u64, amount: u64) -> u64 {
    amount * percent / 100
}

/// The same function, curried by hand: the result captures `percent`.
fn fee_curried(percent: u64) -> impl Fn(u64) -> u64 {
    move |amount| fee(percent, amount)
}
// ANCHOR_END: fee

// ANCHOR: curry
/// Currying, for any two-argument function. The inner closure is returned as
/// a `Box<dyn Fn>` (Rust does not allow `impl Fn(A) -> impl Fn(B) -> C`), and
/// it must clone `a` on every call, because it may be called many times.
fn curry<A, B, C>(
    f: impl Fn(A, B) -> C + Clone + 'static,
) -> impl Fn(A) -> Box<dyn Fn(B) -> C>
where
    A: Clone + 'static,
    B: 'static,
    C: 'static,
{
    move |a: A| {
        let f = f.clone();
        Box::new(move |b: B| f(a.clone(), b))
    }
}
// ANCHOR_END: curry

// ANCHOR: twice
/// `twice = λf. λx. f (f x)`, for functions on `u64`.
fn twice(f: impl Fn(u64) -> u64) -> impl Fn(u64) -> u64 {
    move |x| f(f(x))
}
// ANCHOR_END: twice

// ANCHOR: tracked
/// A value that counts how many times it is cloned.
struct Tracked(String);

static CLONES: AtomicUsize = AtomicUsize::new(0);

impl Clone for Tracked {
    fn clone(&self) -> Self {
        CLONES.fetch_add(1, Ordering::Relaxed);
        Tracked(self.0.clone())
    }
}
// ANCHOR_END: tracked

fn main() {
    // ANCHOR: fn_items_use
    let f = add_one;
    println!(
        "add_one: type {}, size {}",
        type_name_of_val(&f),
        size_of_val(&f)
    );
    let table: [fn(u32) -> u32; 2] = [add_one, double];
    let p = table[1];
    println!(
        "table[1]: type {}, size {}",
        type_name_of_val(&p),
        size_of_val(&p)
    );
    println!("table[1](21) = {}", p(21));
    // ANCHOR_END: fn_items_use

    // ANCHOR: closure_sizes
    let percent: u16 = 3;
    let label = String::from("invoice 2041");
    let nothing = |x: u16| x + 1;
    let by_ref = |x: u16| x * percent; // captures &percent: a pointer
    let by_value = move |x: u16| x * percent; // captures a copy of percent
    let owns_label = move || label.len(); // captures the String itself
    println!("closure type: {}", type_name_of_val(&nothing));
    println!(
        "sizes: nothing {}, by_ref {}, by_value {}, owns_label {}",
        size_of_val(&nothing),
        size_of_val(&by_ref),
        size_of_val(&by_value),
        size_of_val(&owns_label)
    );
    assert_eq!(
        (nothing(1), by_ref(1), by_value(1), owns_label()),
        (2, 3, 3, 12)
    );
    // ANCHOR_END: closure_sizes

    // ANCHOR: capture_modes
    // By shared reference: the closure only reads `prices`.
    let prices = vec![120, 80, 45];
    let total = || prices.iter().sum::<u32>();
    println!(
        "total = {}, and prices is still usable: {:?}",
        total(),
        prices
    );

    // By mutable reference: the closure updates `calls`.
    let mut calls = 0;
    let mut count = || {
        calls += 1;
        calls
    };
    count();
    count();
    println!("calls = {calls}");

    // By value: the closure moves `report` out of itself when called.
    let report = String::from("Q3 report");
    let send = move || report;
    println!("sent: {}", call_once(send));
    // ANCHOR_END: capture_modes

    // ANCHOR: traits_use
    let base = 20;
    let reads = || base + 1; // Fn: only reads its capture
    println!("call_twice(reads)     = {}", call_twice(reads));
    println!("call_twice_mut(reads) = {}", call_twice_mut(reads));
    let mut ticks = 0;
    let bumps = || {
        ticks += 10;
        ticks
    }; // FnMut: mutates its capture
    println!("call_twice_mut(bumps) = {}", call_twice_mut(bumps));
    // `move` decides HOW variables are captured, not WHICH trait you get:
    let greeting = String::from("hello");
    let greet = move || greeting.len() as u32; // moved in, but only read
    println!("call_twice(greet)     = {}", call_twice(&greet));
    println!("greet is still callable: {}", greet());
    // ANCHOR_END: traits_use

    // ANCHOR: dyn_fn
    // Different closures have different types; to store them together we
    // erase the types behind a pointer: `Box<dyn Fn>`.
    let discount = 10;
    let add_fee = fee_curried(3);
    let pipeline: Vec<Box<dyn Fn(u64) -> u64>> = vec![
        Box::new(move |c| c - c * discount / 100), // 10% off
        Box::new(move |c| c + add_fee(c)),         // plus a 3% fee
        Box::new(|c| c / 100 * 100),               // whole units only
    ];
    let result = pipeline.iter().fold(25_000, |amount, step| step(amount));
    println!("pipeline(25000) = {result}");
    println!(
        "size of Box<dyn Fn(u64) -> u64> = {}",
        size_of_val(&pipeline[0])
    );
    // ANCHOR_END: dyn_fn

    // ANCHOR: currying_use
    println!("fee(3, 2000)            = {}", fee(3, 2000));
    println!("fee_curried(3)(2000)    = {}", fee_curried(3)(2000));
    println!("curry(fee)(3)(2000)     = {}", curry(fee)(3)(2000));
    println!("size of fee_curried(3)  = {}", size_of_val(&fee_curried(3)));
    println!(
        "size of curry(fee)(3)   = {} (plus a heap allocation)",
        size_of_val(&curry(fee)(3))
    );

    let tag = |t: Tracked, line: &str| format!("[{}] {line}", t.0);
    let tagger = curry(tag)(Tracked("audit".to_string()));
    for line in ["opened", "approved", "closed"] {
        println!("{}", tagger(line));
    }
    println!(
        "clones of the captured Tracked: {}",
        CLONES.load(Ordering::Relaxed)
    );
    // ANCHOR_END: currying_use

    // ANCHOR: twice_use
    let add = |m: u64| move |n: u64| m + n;
    let add3 = add(3);
    println!("size of add(3) = {}", size_of_val(&add3));
    println!("twice(add(3))(4) = {}", twice(add3)(4));
    // ANCHOR_END: twice_use
}
