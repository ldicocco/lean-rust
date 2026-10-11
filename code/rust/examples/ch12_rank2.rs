// harness: run
//! Rank-2 polymorphism in Rust: a trait with a generic method stands for a
//! polymorphic argument, and `for<'a>` quantifies over lifetimes inside a
//! bound.
//!
//! Demonstrates: list operations that work for every element type, passed to
//! a function that uses them at two types; a field visitor (the pattern behind
//! serialization libraries); Church numerals as values of a trait with a
//! generic method; and higher-ranked trait bounds over lifetimes.
//!
//! Run with: `cargo run --example ch12_rank2`

use std::fmt::Debug;

// ANCHOR: list_op
/// A value of a type implementing `ListOp` is a polymorphic function
/// ∀T. Vec<T> → Vec<T>: the *caller of* `apply` chooses `T`, every time.
trait ListOp {
    fn apply<T>(&self, items: Vec<T>) -> Vec<T>;
}

struct Reverse;
struct TakeFirst(usize);
struct RotateLeft(usize);

impl ListOp for Reverse {
    fn apply<T>(&self, mut items: Vec<T>) -> Vec<T> {
        items.reverse();
        items
    }
}

impl ListOp for TakeFirst {
    fn apply<T>(&self, mut items: Vec<T>) -> Vec<T> {
        items.truncate(self.0);
        items
    }
}

impl ListOp for RotateLeft {
    fn apply<T>(&self, mut items: Vec<T>) -> Vec<T> {
        if !items.is_empty() {
            let k = self.0 % items.len();
            items.rotate_left(k);
        }
        items
    }
}

/// The rank-2 function: (∀T. Vec<T> → Vec<T>) → Vec<u32> → Vec<&str> → ...
/// It uses its argument at two different element types.
fn on_both<'s>(
    op: &impl ListOp,
    numbers: Vec<u32>,
    words: Vec<&'s str>,
) -> (Vec<u32>, Vec<&'s str>) {
    (op.apply(numbers), op.apply(words))
}
// ANCHOR_END: list_op

// ANCHOR: visitor
/// A visitor must handle a field of *any* type that can be printed.
trait FieldVisitor {
    fn field<T: Debug>(&mut self, name: &str, value: &T);
}

struct ServerConfig {
    host: String,
    port: u16,
    verbose: bool,
    retries: Vec<u32>,
}

impl ServerConfig {
    /// Calls the visitor at four different types: `String`, `u16`, `bool`
    /// and `Vec<u32>`. Serialization libraries are built on this pattern.
    fn visit(&self, v: &mut impl FieldVisitor) {
        v.field("host", &self.host);
        v.field("port", &self.port);
        v.field("verbose", &self.verbose);
        v.field("retries", &self.retries);
    }
}

/// Renders `name = value` lines.
struct Printer(Vec<String>);

impl FieldVisitor for Printer {
    fn field<T: Debug>(&mut self, name: &str, value: &T) {
        self.0.push(format!("{name} = {value:?}"));
    }
}

/// Measures how much memory the field values occupy inline.
struct Sizer(usize);

impl FieldVisitor for Sizer {
    fn field<T: Debug>(&mut self, _name: &str, value: &T) {
        self.0 += size_of_val(value);
    }
}
// ANCHOR_END: visitor

// ANCHOR: church
/// A Church numeral: for every type A, a way to apply a function n times.
/// This is the System F type ∀A. (A → A) → A → A.
trait Church {
    fn iterate<A>(&self, f: &dyn Fn(A) -> A, x: A) -> A;
}

struct Zero;
struct Succ<N>(N);
struct Add<M, N>(M, N);
struct Mul<M, N>(M, N);

impl Church for Zero {
    fn iterate<A>(&self, _f: &dyn Fn(A) -> A, x: A) -> A {
        x
    }
}

impl<N: Church> Church for Succ<N> {
    fn iterate<A>(&self, f: &dyn Fn(A) -> A, x: A) -> A {
        f(self.0.iterate(f, x))
    }
}

/// m + n: apply f n times, then m more times.
impl<M: Church, N: Church> Church for Add<M, N> {
    fn iterate<A>(&self, f: &dyn Fn(A) -> A, x: A) -> A {
        self.0.iterate(f, self.1.iterate(f, x))
    }
}

/// m * n: apply "apply f n times" m times. The inner numeral is used at the
/// same type A, the outer one with a function built from the inner one.
impl<M: Church, N: Church> Church for Mul<M, N> {
    fn iterate<A>(&self, f: &dyn Fn(A) -> A, x: A) -> A {
        self.0.iterate(&|y| self.1.iterate(f, y), x)
    }
}

fn to_u32(n: &impl Church) -> u32 {
    n.iterate(&|k| k + 1, 0)
}
// ANCHOR_END: church

// ANCHOR: self_apply
/// ∀α. α → α as a trait: implementors behave like a polymorphic identity.
trait PolyId {
    fn call<T>(&self, x: T) -> T;
}

struct Identity;

impl PolyId for Identity {
    fn call<T>(&self, x: T) -> T {
        x
    }
}

/// System F's λ(x : ∀α. α → α). x [∀α. α → α] x, in Rust: the method is
/// instantiated at the type of `x` itself (here `&F`), and applied to `x`.
fn self_apply<F: PolyId>(x: &F) -> &F {
    x.call(x)
}
// ANCHOR_END: self_apply

// ANCHOR: hrtb
/// The callback is applied to a string that is created inside this function,
/// so no lifetime the caller could name would fit it. The bound says: for
/// every lifetime 'a, `pick` maps a `&'a str` to a `&'a str`.
fn normalized_len<F>(text: &str, pick: F) -> usize
where
    F: for<'a> Fn(&'a str) -> &'a str,
{
    let lowered = text.to_lowercase(); // a local String
    pick(&lowered).len()
}

/// The same bound, written with the usual sugar: an elided lifetime in an
/// `Fn` bound means `for<'a>`.
fn normalized_len_sugar(text: &str, pick: impl Fn(&str) -> &str) -> usize {
    let lowered = text.to_lowercase();
    pick(&lowered).len()
}

fn first_word(s: &str) -> &str {
    s.split_whitespace().next().unwrap_or("")
}
// ANCHOR_END: hrtb

fn main() {
    // ANCHOR: run_list_op
    let numbers = vec![1, 2, 3, 4];
    let words = vec!["alpha", "beta", "gamma"];
    println!(
        "reverse:  {:?}",
        on_both(&Reverse, numbers.clone(), words.clone())
    );
    println!(
        "take 2:   {:?}",
        on_both(&TakeFirst(2), numbers.clone(), words.clone())
    );
    println!("rotate 1: {:?}", on_both(&RotateLeft(1), numbers, words));
    // ANCHOR_END: run_list_op

    // ANCHOR: run_visitor
    let config = ServerConfig {
        host: "db.internal".to_string(),
        port: 5432,
        verbose: false,
        retries: vec![100, 200, 400],
    };
    let mut printer = Printer(Vec::new());
    config.visit(&mut printer);
    println!("{}", printer.0.join("; "));
    let mut sizer = Sizer(0);
    config.visit(&mut sizer);
    println!("inline bytes of the fields: {}", sizer.0);
    // ANCHOR_END: run_visitor

    // ANCHOR: run_church
    let two = || Succ(Succ(Zero));
    let three = || Succ(Succ(Succ(Zero)));
    println!("2 + 3 = {}", to_u32(&Add(two(), three())));
    println!("2 * 3 = {}", to_u32(&Mul(two(), three())));
    // The same numeral at other types: strings and powers of two.
    println!(
        "{}",
        three().iterate(&|s: String| s + "ab", String::from(">"))
    );
    println!("2^3 = {}", three().iterate(&|k: u64| 2 * k, 1));
    // ANCHOR_END: run_church

    // ANCHOR: run_self_apply
    let same = self_apply(&Identity);
    println!("self-application: {}", same.call("still the identity"));
    // ANCHOR_END: run_self_apply

    // ANCHOR: run_hrtb
    println!(
        "trim:       {}",
        normalized_len("  Hello World ", str::trim)
    );
    println!("first word: {}", normalized_len("Hello World", first_word));
    println!(
        "with sugar: {}",
        normalized_len_sugar("Hello World", first_word)
    );
    // A function pointer type can be higher-ranked too.
    let picker: for<'a> fn(&'a str) -> &'a str = str::trim_start;
    println!("fn pointer: {}", normalized_len("   abc", picker));
    // ANCHOR_END: run_hrtb
}
