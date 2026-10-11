// harness: run
//! Safe abstractions over `unsafe`: every `unsafe` block below comes with a
//! `SAFETY:` comment that discharges the proof obligations of the operations it
//! uses, the way a proof discharges the premises of a rule.
//!
//! Demonstrates: our own `split_at_mut` (two disjoint `&mut` from one), a
//! `Cell`-like type built on `UnsafeCell`, filling a `Vec` through its spare
//! capacity, safety vs validity invariants (`String` and UTF-8, `NonZeroU32`),
//! an `unsafe fn` whose precondition is passed to the caller, and the Rust
//! twins of the Lean libraries `satSub` and `badSub` of Chapter 32.
//!
//! Run with: `cargo run --example ch32_unsafe_abstractions`
//! Under Miri (nightly only, not part of the book's checks):
//! `cargo +nightly miri run --example ch32_unsafe_abstractions`

use std::cell::UnsafeCell;
use std::mem::{MaybeUninit, size_of};
use std::num::NonZeroU32;

// ANCHOR: split_at_mut
/// Split one unique borrow of a slice into unique borrows of its two halves.
///
/// The signature promises two `&mut` slices that do not overlap. The borrow
/// checker cannot verify that (to it, both halves are borrowed from `slice`),
/// so the body works with a raw pointer, and the `unsafe` block carries the
/// argument that the compiler cannot check.
pub fn my_split_at_mut<'a, T>(
    slice: &'a mut [T],
    mid: usize,
) -> (&'a mut [T], &'a mut [T]) {
    let len = slice.len();
    // This check is what makes the unsafe block sound. Without it, a caller
    // could pass `mid > len` and receive a slice that runs past the end.
    assert!(mid <= len, "mid > len");
    let ptr: *mut T = slice.as_mut_ptr();
    // SAFETY: `from_raw_parts_mut(p, n)` requires that `p` is non-null,
    // aligned, and valid for reads and writes of `n` initialized values of `T`
    // inside one allocation, and that nothing else accesses that memory while
    // the result is alive. `ptr.add(mid)` requires that the result stays in
    // the same allocation (or one past its end).
    // 1. `ptr` comes from `slice`, so it is non-null, aligned and points to
    //    `len` initialized values.
    // 2. `mid <= len` (checked above), so `ptr.add(mid)` is in bounds, and
    //    both ranges `[0, mid)` and `[mid, len)` lie inside `slice`.
    // 3. The two ranges are disjoint, so the two results never alias each
    //    other. This is the fact that the borrow checker cannot see.
    // 4. Both results live for `'a`, the lifetime of the unique borrow
    //    `slice`, so no one else can use the memory while they are alive.
    unsafe {
        (
            std::slice::from_raw_parts_mut(ptr, mid),
            std::slice::from_raw_parts_mut(ptr.add(mid), len - mid),
        )
    }
}
// ANCHOR_END: split_at_mut

// ANCHOR: my_cell
/// A minimal `Cell`: mutation through a shared reference, on one thread.
///
/// The invariant that every method relies on: no reference into `value` ever
/// escapes a method, and no method runs code it does not control (such as a
/// destructor or a `clone`) while it is accessing `value`. So whenever a
/// method touches the contents, no other reference to them is alive.
pub struct MyCell<T> {
    value: UnsafeCell<T>,
}

impl<T> MyCell<T> {
    pub const fn new(value: T) -> Self {
        MyCell {
            value: UnsafeCell::new(value),
        }
    }

    /// Put `value` in the cell and return the old contents.
    pub fn replace(&self, value: T) -> T {
        // SAFETY: we create a `&mut T` to the contents for the duration of
        // `mem::replace`, which only moves bytes and runs no other code.
        // No other reference to the contents is alive: no method lets one
        // escape, and `MyCell` is not `Sync` (because `UnsafeCell` is not),
        // so no other thread can be inside a method of this cell right now.
        unsafe { std::mem::replace(&mut *self.value.get(), value) }
    }

    /// Store `value`. The old contents are dropped *after* the access ends:
    /// a destructor can run arbitrary code, including code that uses this
    /// very cell.
    pub fn set(&self, value: T) {
        let old = self.replace(value);
        drop(old);
    }

    pub fn into_inner(self) -> T {
        self.value.into_inner()
    }
}

impl<T: Copy> MyCell<T> {
    /// Copy the contents out. The bound `T: Copy` is part of the safety
    /// argument: copying is a plain bitwise read, while a `clone` could run
    /// code that calls `set` on this cell in the middle of our read.
    pub fn get(&self) -> T {
        // SAFETY: we read the contents through a raw pointer and copy them;
        // as in `replace`, no other reference to the contents is alive, and
        // no user code runs during the read.
        unsafe { *self.value.get() }
    }
}
// ANCHOR_END: my_cell

// ANCHOR: sensor
/// A lab sensor that counts how often it has been read. `read` takes `&self`,
/// so many parts of a program can share the sensor, and still update the
/// counter.
struct Sensor {
    name: &'static str,
    reads: MyCell<u32>,
}

impl Sensor {
    fn read(&self) -> f64 {
        self.reads.set(self.reads.get() + 1);
        20.0 + f64::from(self.reads.get()) / 10.0
    }
}
// ANCHOR_END: sensor

// ANCHOR: vec_fill
/// Build `[0, 1, 4, 9, ...]` by writing into a vector's spare capacity, then
/// telling the vector how many elements are now initialized.
fn squares(n: usize) -> Vec<u64> {
    let mut v: Vec<u64> = Vec::with_capacity(n);
    let spare: &mut [MaybeUninit<u64>] = v.spare_capacity_mut();
    for (i, slot) in spare.iter_mut().take(n).enumerate() {
        slot.write((i as u64) * (i as u64));
    }
    // SAFETY: `set_len(n)` requires `n <= capacity` and that the elements
    // `0..n` are initialized. The capacity is at least `n` (`with_capacity`),
    // so `spare` has at least `n` slots, and the loop wrote all of the first
    // `n`. This re-establishes `Vec`'s invariant: the first `len` elements
    // are initialized and `len <= capacity`.
    unsafe { v.set_len(n) };
    v
}
// ANCHOR_END: vec_fill

// ANCHOR: invariants
/// Safety invariant: a `String` must hold UTF-8. Breaking it is not
/// immediately undefined behavior, but safe methods may misbehave later.
fn shout(s: &str) -> String {
    let bytes: Vec<u8> = s.bytes().map(|b| b.to_ascii_uppercase()).collect();
    // SAFETY: `from_utf8_unchecked` requires valid UTF-8. `s` was valid
    // UTF-8, and `to_ascii_uppercase` only changes bytes in `b'a'..=b'z'`,
    // which never occur inside a multi-byte character (those bytes are all
    // `>= 0x80`), so the result is valid UTF-8 too.
    unsafe { String::from_utf8_unchecked(bytes) }
}

/// Validity invariant: a `NonZeroU32` is never 0, and the compiler relies on
/// it for the layout of `Option<NonZeroU32>`: 0 encodes `None`.
fn port(n: u32) -> Option<NonZeroU32> {
    if n == 0 {
        None
    } else {
        // SAFETY: `new_unchecked` requires `n != 0`, which the `if` checked.
        Some(unsafe { NonZeroU32::new_unchecked(n) })
    }
}
// ANCHOR_END: invariants

// ANCHOR: unsafe_fn
/// Sum the first `n` readings, without bounds checks.
///
/// # Safety
///
/// The caller must guarantee `n <= readings.len()`.
unsafe fn sum_prefix_unchecked(readings: &[u64], n: usize) -> u64 {
    let mut total = 0;
    for i in 0..n {
        // SAFETY: `i < n <= readings.len()`, by the loop bound and by the
        // precondition of this function, which our caller promised.
        total += unsafe { *readings.get_unchecked(i) };
    }
    total
}

fn sum_first_three(readings: &[u64]) -> Option<u64> {
    if readings.len() < 3 {
        return None;
    }
    // SAFETY: `3 <= readings.len()`, checked just above.
    Some(unsafe { sum_prefix_unchecked(readings, 3) })
}
// ANCHOR_END: unsafe_fn

// ANCHOR: sat_sub
/// The Rust twin of `satSub` in `Book/Ch32/Language.lean`.
fn sat_sub(x: u32, y: u32) -> u32 {
    if y <= x {
        // SAFETY: `unchecked_sub` requires that `x - y` does not overflow,
        // that is, `y <= x`, which the `if` has just established.
        unsafe { x.unchecked_sub(y) }
    } else {
        0
    }
}

/// The twin of `badSub`. It compiles and it passes every test below, but it
/// is UNSOUND: it is a safe function, so every caller may pass any `x` and
/// `y`, and `bad_sub(3, 5)` is undefined behavior. No `SAFETY:` comment can
/// be written for this block, because nothing establishes `y <= x`.
fn bad_sub(x: u32, y: u32) -> u32 {
    unsafe { x.unchecked_sub(y) }
}
// ANCHOR_END: sat_sub

fn main() {
    // ANCHOR: main_split
    let mut samples = [3, 1, 4, 1, 5, 9, 2, 6];
    let (left, right) = my_split_at_mut(&mut samples, 3);
    left[0] = 30; // two unique borrows, used side by side
    right[0] = 10;
    left.swap(1, 2);
    right.reverse();
    println!("left  = {left:?}");
    println!("right = {right:?}");
    println!("all   = {samples:?}");
    // ANCHOR_END: main_split
    assert_eq!(samples, [30, 4, 1, 6, 2, 9, 5, 10]);

    let mut empty: [u8; 0] = [];
    let (a, b) = my_split_at_mut(&mut empty, 0);
    assert!(a.is_empty() && b.is_empty());

    // ANCHOR: main_cell
    let sensor = Sensor {
        name: "thermometer",
        reads: MyCell::new(0),
    };
    let first: &Sensor = &sensor; // two shared references to one sensor
    let second: &Sensor = &sensor;
    let r1 = first.read();
    let r2 = second.read();
    let r3 = first.read();
    println!(
        "{}: {r1}, {r2}, {r3} after {} reads",
        sensor.name,
        sensor.reads.get()
    );
    // ANCHOR_END: main_cell
    assert_eq!(sensor.reads.into_inner(), 3);

    let names = MyCell::new(String::from("first"));
    let old = names.replace(String::from("second"));
    names.set(String::from("third"));
    assert_eq!(
        (old.as_str(), names.into_inner().as_str()),
        ("first", "third")
    );

    // ANCHOR: main_rest
    println!("squares(6) = {:?}", squares(6));
    println!(
        "shout(\"safe abstraction\") = {:?}",
        shout("safe abstraction")
    );
    println!("port(8080) = {:?}, port(0) = {:?}", port(8080), port(0));
    println!(
        "size_of: u32 = {}, Option<u32> = {}, Option<NonZeroU32> = {}",
        size_of::<u32>(),
        size_of::<Option<u32>>(),
        size_of::<Option<NonZeroU32>>()
    );
    println!(
        "sum_first_three([5, 6, 7, 8]) = {:?}",
        sum_first_three(&[5, 6, 7, 8])
    );
    println!("sum_first_three([5, 6]) = {:?}", sum_first_three(&[5, 6]));
    println!(
        "sat_sub(5, 3) = {}, sat_sub(3, 5) = {}",
        sat_sub(5, 3),
        sat_sub(3, 5)
    );
    println!(
        "bad_sub(5, 3) = {} (never call bad_sub(3, 5))",
        bad_sub(5, 3)
    );
    // ANCHOR_END: main_rest

    // ANCHOR: main_together
    let mut cells = [10, 20, 30];
    let (front, back) = my_split_at_mut(&mut cells, 2);
    front.swap(0, 1); // touches cells 0 and 1 only
    back[0] = 0; // touches cell 2 only
    println!("cells = {cells:?}");
    // ANCHOR_END: main_together
    assert_eq!(cells, [20, 10, 0]);

    assert_eq!(squares(0), Vec::<u64>::new());
    assert_eq!(squares(6), vec![0, 1, 4, 9, 16, 25]);
    assert_eq!(shout("grüße"), "GRüßE");
    for x in 0..50 {
        for y in 0..50 {
            assert_eq!(sat_sub(x, y), x.saturating_sub(y));
        }
    }
    // The tests of `bad_sub` pass too: tests only try the inputs we chose.
    for (x, y) in [(5, 3), (7, 7), (100, 1)] {
        assert_eq!(bad_sub(x, y), x - y);
    }
    println!("all assertions passed");
}
