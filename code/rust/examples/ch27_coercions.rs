// harness: run
//! Coercions are not subtyping. A subtyping step (`&'static str` used as
//! `&'a str`) reuses the value as it is; a coercion converts it: it may call
//! code (`Deref::deref`) or change the representation (a slice length, a
//! vtable pointer, a function pointer). And coercions do not lift through type
//! constructors, while subtyping does.
//!
//! Run with: `cargo run --example ch27_coercions`

use std::cell::Cell;
use std::fmt::Debug;
use std::mem::size_of_val;
use std::ops::Deref;

// ANCHOR: counting_deref
/// A smart pointer that counts how often it is dereferenced.
struct Tracked<T> {
    value: T,
    derefs: Cell<u32>,
}

impl<T> Deref for Tracked<T> {
    type Target = T;
    fn deref(&self) -> &T {
        self.derefs.set(self.derefs.get() + 1);
        &self.value
    }
}

fn shout(s: &str) -> String {
    s.to_uppercase()
}

fn deref_coercions() {
    let name = Tracked {
        value: String::from("pump 3"),
        derefs: Cell::new(0),
    };
    // `&Tracked<String>` -> `&String` -> `&str`: two coercions, and the first
    // one is a call to our `deref`.
    let loud = shout(&name);
    println!("{loud}: Deref::deref ran {} time(s)", name.derefs.get());
}
// ANCHOR_END: counting_deref

// ANCHOR: representation
trait Describe {
    fn describe(&self) -> String;
}

struct Valve {
    open: bool,
}

impl Describe for Valve {
    fn describe(&self) -> String {
        format!("valve open: {}", self.open)
    }
}

fn double(x: i32) -> i32 {
    2 * x
}

fn representations() {
    // Unsizing a reference to an array adds the length: a thin pointer
    // becomes a fat one.
    let readings = [1, 2, 3];
    let array_ref: &[i32; 3] = &readings;
    let slice_ref: &[i32] = array_ref;
    println!(
        "&[i32; 3]: {} bytes, &[i32]: {} bytes",
        size_of_val(&array_ref),
        size_of_val(&slice_ref)
    );
    // Unsizing a box to a trait object adds a vtable pointer.
    let boxed: Box<Valve> = Box::new(Valve { open: true });
    let size_before = size_of_val(&boxed);
    let object: Box<dyn Describe> = boxed;
    println!(
        "Box<Valve>: {size_before} bytes, Box<dyn Describe>: {} bytes ({})",
        size_of_val(&object),
        object.describe()
    );
    // A function item has its own zero-sized type; coercing it to a function
    // pointer produces an actual address.
    let item = double;
    let pointer: fn(i32) -> i32 = double;
    println!(
        "fn item: {} bytes, fn pointer: {} bytes, both give {}",
        size_of_val(&item),
        size_of_val(&pointer),
        item(21) + pointer(0)
    );
}
// ANCHOR_END: representation

// ANCHOR: subtyping_is_free
/// Subtyping changes nothing: the same pointer, viewed at a shorter lifetime.
fn shorten<'long: 'short, 'short>(x: &'long str) -> &'short str {
    x
}

fn subtyping_is_free() {
    let long: &'static str = "a static string";
    let short: &str = shorten(long);
    println!(
        "&'static str -> &str: {} bytes -> {} bytes, same address: {}",
        size_of_val(&long),
        size_of_val(&short),
        std::ptr::eq(long, short)
    );
}
// ANCHOR_END: subtyping_is_free

// ANCHOR: no_lifting
/// Subtyping lifts through `Vec` for free (`Vec` is covariant)...
fn shorten_all<'long: 'short, 'short>(v: Vec<&'long str>) -> Vec<&'short str> {
    v
}

/// ...but a coercion does not: `Vec<&String>` is not a `Vec<&str>`
/// (`ch27_no_coercion_in_vec`). Converting means building a new vector.
fn as_strs(owned: &[String]) -> Vec<&str> {
    owned.iter().map(|s| s.as_str()).collect()
}
// ANCHOR_END: no_lifting

// ANCHOR: mut_to_shared
/// `&mut T` coerces to `&T`: a unique permission can always be weakened to a
/// shared one, for as long as the unique one is not used.
fn total(values: &[u32]) -> u32 {
    values.iter().sum()
}

fn weaken(values: &mut Vec<u32>) -> u32 {
    values.push(4);
    total(values) // `&mut Vec<u32>` -> `&Vec<u32>` -> `&[u32]`
}
// ANCHOR_END: mut_to_shared

fn show<T: Debug>(label: &str, value: T) {
    println!("{label}: {value:?}");
}

fn main() {
    deref_coercions();
    representations();
    subtyping_is_free();
    show("shorten_all", shorten_all(vec!["alpha", "beta"]));
    let owned = vec![String::from("gamma"), String::from("delta")];
    show("as_strs", as_strs(&owned));
    let mut values = vec![1, 2, 3];
    show("weaken", weaken(&mut values));
}
