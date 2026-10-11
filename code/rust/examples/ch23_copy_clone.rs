// harness: run
//! `Copy`, `Clone` and `Rc` in practice: implicit and free duplication,
//! explicit and possibly effectful duplication, and counted sharing.
//!
//! Run with: `cargo run --example ch23_copy_clone`

use std::cell::Cell;
use std::rc::Rc;
use std::sync::Arc;
use std::thread;

// ANCHOR: dup
/// Contraction for free: a `Copy` value is duplicated by using it twice.
fn dup_copy<T: Copy>(x: T) -> (T, T) {
    (x, x)
}

/// Contraction on request: a `Clone` value is duplicated by calling `clone`.
fn dup_clone<T: Clone>(x: T) -> (T, T) {
    (x.clone(), x)
}
// ANCHOR_END: dup

// ANCHOR: point
/// All fields are `Copy`, and there is no destructor: the derive is accepted.
#[derive(Clone, Copy, Debug, PartialEq)]
struct Point {
    x: i32,
    y: i32,
}
// ANCHOR_END: point

// ANCHOR: tracked
/// A type whose duplication has a visible effect: every clone is counted.
#[derive(Debug)]
struct Specimen {
    id: u32,
    clones: Rc<Cell<u32>>,
}

impl Clone for Specimen {
    fn clone(&self) -> Specimen {
        self.clones.set(self.clones.get() + 1);
        Specimen {
            id: self.id,
            clones: Rc::clone(&self.clones),
        }
    }
}
// ANCHOR_END: tracked

// ANCHOR: reborrow
fn record(log: &mut Vec<&'static str>, event: &'static str) {
    log.push(event);
}

/// `&mut` is not `Copy`, yet `log` is passed twice: each call receives a
/// fresh reborrow `&mut *log`, not a copy of `log` (Chapter 28).
fn record_twice(log: &mut Vec<&'static str>) {
    record(log, "first");
    record(log, "second");
}
// ANCHOR_END: reborrow

// ANCHOR: session
/// A measurement: `Copy`, so it can be used as often as we like.
#[derive(Clone, Copy)]
struct Sample {
    channel: i32,
    value: i32,
}

/// The instrument: one handle, neither `Copy` nor `Clone`.
struct Device {
    reads: i32,
}

fn measure(dev: Device, ch: i32) -> (Sample, Device) {
    let value = 100 + 10 * ch + dev.reads;
    let sample = Sample { channel: ch, value };
    (
        sample,
        Device {
            reads: dev.reads + 1,
        },
    )
}

/// A labeled measurement. The operator's name is a `String`: `Clone`.
struct Record {
    op: String,
    sample: Sample,
}

fn label(op: String, sample: Sample) -> Record {
    Record { op, sample }
}

/// Measure one channel twice; label both samples with the operator's name.
fn session(dev: Device, ch: i32, op: String) -> ((Record, Record), Device) {
    let (a, dev2) = measure(dev, ch);
    let (b, dev3) = measure(dev2, ch);
    ((label(op.clone(), a), label(op, b)), dev3)
}
// ANCHOR_END: session

fn main() {
    // ANCHOR: copy_vs_move
    let a: i32 = 5;
    let b = a; // a copy: `a` is still usable
    let s = String::from("report");
    let t = s; // a move: `s` is not usable any more
    println!("a = {a}, b = {b}, t = {t}");
    // ANCHOR_END: copy_vs_move

    // ANCHOR: copies
    let p = Point { x: 1, y: 2 };
    let (p1, p2) = dup_copy(p);
    println!("{p1:?} {p2:?}, and p is still {p:?}");
    // A copy is a new value in a new place, bit for bit the same.
    let q = p;
    println!(
        "same bits: {}, same place: {}",
        p == q,
        std::ptr::eq(&p, &q)
    );
    // A shared reference is Copy: the copies point to the same String.
    let r = &t;
    let (r1, r2) = dup_copy(r);
    println!("two references, one String: {}", std::ptr::eq(r1, r2));
    // ANCHOR_END: copies

    // ANCHOR: clones
    let (u, v) = dup_clone(String::from("calibration"));
    println!(
        "cloned strings equal: {}, same buffer: {}",
        u == v,
        u.as_ptr() == v.as_ptr()
    );
    let counter = Rc::new(Cell::new(0));
    let specimen = Specimen {
        id: 7,
        clones: Rc::clone(&counter),
    };
    let (s1, s2) = dup_clone(specimen);
    let (s3, _s4) = dup_clone(s1);
    println!(
        "specimens {} and {}: {} clones so far",
        s2.id,
        s3.id,
        counter.get()
    );
    // ANCHOR_END: clones

    // ANCHOR: rc
    let config = Rc::new(String::from("lab-7"));
    println!("count after new: {}", Rc::strong_count(&config));
    let reader = Rc::clone(&config);
    let writer = config.clone();
    println!("count after 2 clones: {}", Rc::strong_count(&config));
    println!("one allocation: {}", Rc::ptr_eq(&reader, &writer));
    drop(reader);
    drop(writer);
    println!("count after 2 drops: {}", Rc::strong_count(&config));
    // ANCHOR_END: rc

    // ANCHOR: arc
    let readings = Arc::new(vec![10, 20, 30]);
    let handles: Vec<_> = (0..3)
        .map(|i| {
            let mine = Arc::clone(&readings);
            thread::spawn(move || mine[i] * 2)
        })
        .collect();
    let doubled: Vec<i32> = handles.into_iter().map(|h| h.join().unwrap()).collect();
    println!(
        "{doubled:?}, count back to {}",
        Arc::strong_count(&readings)
    );
    // ANCHOR_END: arc

    let mut log = Vec::new();
    record_twice(&mut log);
    println!("log: {log:?}");

    // ANCHOR: session_run
    let ((r1, r2), dev) = session(Device { reads: 0 }, 3, String::from("ada"));
    for r in [&r1, &r2] {
        println!(
            "{}: channel {} = {}",
            r.op, r.sample.channel, r.sample.value
        );
    }
    println!("device used {} times", dev.reads);
    // ANCHOR_END: session_run
    assert_eq!(counter.get(), 2);
}
