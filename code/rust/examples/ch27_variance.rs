// harness: run
//! Subtyping and variance in Rust: lifetimes are the only source of
//! subtyping, and every type constructor has a variance in each parameter.
//!
//! Each `shrink_*`/`grow_*` function below is a *witness*: it compiles only
//! because the type it converts has the variance stated in its comment, so the
//! compiler checks the claim. The rest of the program calls them, and shows
//! `PhantomData` choosing the variance (and the auto traits) of a typed ID and
//! of a raw-pointer view.
//!
//! Run with: `cargo run --example ch27_variance`

use std::cell::Cell;
use std::marker::PhantomData;
use std::rc::Rc;

// ANCHOR: subsumption
/// One region for both arguments: a `&'static str` is accepted where a
/// `&'a str` is expected, because `&'static str <: &'a str`.
fn longer<'a>(a: &'a str, b: &'a str) -> &'a str {
    if a.len() >= b.len() { a } else { b }
}

fn subsumption() {
    let fallback: &'static str = "default";
    let configured = String::from("from the config file");
    let chosen = longer(fallback, &configured); // 'a := the region of `configured`
    println!("chosen: {chosen}");
}
// ANCHOR_END: subsumption

// ANCHOR: witnesses
// `'long: 'short` reads "'long outlives 'short", so `&'long T <: &'short T`.

/// `&'a T` is covariant in `'a`...
fn shrink_ref<'long: 'short, 'short>(x: &'long str) -> &'short str {
    x
}

/// ...and in `T`: a reference to a longer-lived reference can be shortened.
fn shrink_ref_ref<'long: 'short, 'short, 'r>(x: &'r &'long str) -> &'r &'short str {
    x
}

/// `&'a mut T` is covariant in `'a` (but invariant in `T`: see
/// `ch27_mut_invariance`).
fn shrink_mut<'long: 'short, 'short, 'v>(x: &'long mut &'v str) -> &'short mut &'v str {
    x
}

/// `Box<T>`, `Vec<T>` and `Option<T>` are covariant in `T`.
fn shrink_box<'long: 'short, 'short>(x: Box<&'long str>) -> Box<&'short str> {
    x
}

fn shrink_vec<'long: 'short, 'short>(x: Vec<&'long str>) -> Vec<&'short str> {
    x
}

fn shrink_option<'long: 'short, 'short>(x: Option<&'long str>) -> Option<&'short str> {
    x
}

/// `fn() -> T` is covariant in `T`: a function that returns long-lived
/// references can stand in for one that returns short-lived ones.
fn shrink_result<'long: 'short, 'short>(f: fn() -> &'long str) -> fn() -> &'short str {
    f
}

/// `fn(T)` is *contravariant* in `T`: the conversion goes the other way. A
/// callback that accepts any short-lived `&str` can stand in for one that will
/// only ever be given long-lived ones.
fn grow_argument<'long: 'short, 'short>(
    f: fn(&'short str) -> usize,
) -> fn(&'long str) -> usize {
    f
}

/// Two contravariances make a covariance: `fn(fn(T))` is covariant in `T`.
fn shrink_twice<'long: 'short, 'short>(
    f: fn(fn(&'long str) -> usize) -> usize,
) -> fn(fn(&'short str) -> usize) -> usize {
    f
}
// ANCHOR_END: witnesses

fn static_text() -> &'static str {
    "a static string"
}

fn count(s: &str) -> usize {
    s.len()
}

/// Calls its callback with a `'static` string only.
fn apply_to_static(callback: fn(&'static str) -> usize) -> usize {
    callback("static")
}

fn witnesses() {
    let local = String::from("local");
    let r: &str = shrink_ref("static");
    let rr: &&str = shrink_ref_ref(&r);
    println!("shrink_ref, shrink_ref_ref: {rr}");
    let mut slot: &str = &local;
    let m: &mut &str = shrink_mut(&mut slot);
    *m = "replaced";
    println!("shrink_mut, then a write through it: {slot}");
    let b = shrink_box(Box::new("boxed"));
    let v = shrink_vec(vec!["a", "b"]);
    let o = shrink_option(Some("some"));
    println!("shrink_box, shrink_vec, shrink_option: {b} {v:?} {o:?}");
    let f = shrink_result(static_text);
    println!("shrink_result: {}", f());
    let g = grow_argument(count);
    println!("grow_argument: {}", g("a 'static argument"));
    let h = shrink_twice(apply_to_static);
    println!("shrink_twice: {}", h(count));
}

// ANCHOR: typed_id
/// A typed identifier: an `Id<Order>` cannot be passed where an
/// `Id<Customer>` is expected. The `T` is only a marker, and the choice of
/// marker matters:
/// - `PhantomData<T>` would say "an `Id<T>` owns a `T`", so `Id<Rc<..>>`
///   would not be `Send` and the drop checker would assume a `T` is dropped;
/// - `PhantomData<fn() -> T>` says "an `Id<T>` produces `T`s": covariant in
///   `T`, always `Send` and `Sync`, owns nothing.
struct Id<T> {
    raw: u64,
    _marker: PhantomData<fn() -> T>,
}

// Derived `Clone` and `Copy` would require `T: Clone`; an ID is always copyable.
impl<T> Clone for Id<T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T> Copy for Id<T> {}

impl<T> Id<T> {
    fn new(raw: u64) -> Self {
        Id {
            raw,
            _marker: PhantomData,
        }
    }
}

struct Order;
struct Customer;

fn customer_of(order: Id<Order>) -> Id<Customer> {
    Id::new(order.raw / 100)
}

fn require_send_sync<T: Send + Sync>(_: &T) -> &'static str {
    "Send + Sync"
}
// ANCHOR_END: typed_id

// ANCHOR: raw_view
/// A borrowed view of a slice through a raw pointer. The raw pointer carries
/// no lifetime, so `PhantomData<&'a T>` records the borrow: the view is
/// covariant in `'a` and `T`, exactly like `&'a [T]`.
struct RawView<'a, T> {
    ptr: *const T,
    len: usize,
    _borrow: PhantomData<&'a T>,
}

impl<'a, T> RawView<'a, T> {
    fn new(slice: &'a [T]) -> Self {
        RawView {
            ptr: slice.as_ptr(),
            len: slice.len(),
            _borrow: PhantomData,
        }
    }

    fn get(&self, i: usize) -> Option<&'a T> {
        if i < self.len {
            // SAFETY: `ptr` points to `len` initialized elements borrowed for
            // `'a` (see `new`), and `i < len`.
            Some(unsafe { &*self.ptr.add(i) })
        } else {
            None
        }
    }
}

/// The witness: the view is covariant in `'a`.
fn shrink_view<'long: 'short, 'short, T>(v: RawView<'long, T>) -> RawView<'short, T> {
    v
}

/// With `PhantomData<&'a mut T>` the type would be invariant in `T`, and with
/// `PhantomData<fn(T)>` contravariant; `PhantomData<Cell<T>>` also invariant.
#[allow(dead_code)]
struct Invariant<T>(PhantomData<Cell<T>>);
// ANCHOR_END: raw_view

fn main() {
    subsumption();
    witnesses();

    let order: Id<Order> = Id::new(4217);
    let customer = customer_of(order);
    println!("order {} belongs to customer {}", order.raw, customer.raw);
    let shared_id: Id<Rc<String>> = Id::new(7);
    println!("Id<Rc<String>> is {}", require_send_sync(&shared_id));

    let readings = [3.5, 4.0, 4.5];
    let view = shrink_view(RawView::new(&readings));
    println!("view[1] = {:?}, view[3] = {:?}", view.get(1), view.get(3));
}
