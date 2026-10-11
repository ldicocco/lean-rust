// harness: run
//! Reborrowing in real Rust, next to the borrow calculus of Chapter 28.
//!
//! Demonstrates: a `&mut` reference used twice thanks to implicit reborrows,
//! the same function with the reborrows written out, a generic function where
//! the reborrow must be explicit, and the three borrow rules of the calculus
//! written as Rust functions (`lend`, `lend_mut`, `reborrow`) whose signatures
//! carry the escape check.
//!
//! Run with: `cargo run --example ch28_reborrows`

// ANCHOR: implicit
fn set(r: &mut i32, value: i32) {
    *r = value;
}

/// Derivation I in Rust: `r` is used twice. Each call receives a fresh
/// reborrow `&mut *r`, which the compiler inserts.
fn twice(r: &mut i32) {
    set(r, 1);
    set(r, 2);
}
// ANCHOR_END: implicit

// ANCHOR: explicit
/// The same function with the reborrows written out, one block for each
/// `borrow y = &'b mut *r in ...` of the calculus.
fn twice_explicit(r: &mut i32) {
    {
        let y1 = &mut *r;
        *y1 = 1;
    }
    {
        let y2 = &mut *r;
        *y2 = 2;
    }
}
// ANCHOR_END: explicit

// ANCHOR: generic
fn consume<T>(_value: T) {}

/// When the parameter type is generic, the compiler does not insert a
/// reborrow: `consume(r)` would move `r` (see `ch28_no_reborrow.rs`). Writing
/// the reborrow by hand restores the pattern.
fn twice_generic(r: &mut i32) {
    consume(&mut *r);
    consume(&mut *r);
    *r += 1;
}
// ANCHOR_END: generic

// ANCHOR: combinators
/// Rule T-Borrow as a Rust function. The owner goes in and comes back out,
/// next to the result of the body. `for<'a>` makes the lifetime fresh, and
/// `S` is chosen outside its scope, so `S` cannot mention `'a`: that is the
/// escape check.
fn lend<T, S>(owner: Box<T>, body: impl for<'a> FnOnce(&'a T) -> S) -> (Box<T>, S) {
    let result = body(&*owner);
    (owner, result)
}

/// Rule T-BorrowMut.
fn lend_mut<T, S>(
    mut owner: Box<T>,
    body: impl for<'a> FnOnce(&'a mut T) -> S,
) -> (Box<T>, S) {
    let result = body(&mut *owner);
    (owner, result)
}

/// Rule T-Reborrow. The reference comes back with its original lifetime `'k`.
fn reborrow<'k, T, S>(
    r: &'k mut T,
    body: impl for<'a> FnOnce(&'a mut T) -> S,
) -> (&'k mut T, S) {
    let result = body(&mut *r);
    (r, result)
}
// ANCHOR_END: combinators

// ANCHOR: twice_calculus
/// Derivation I, transcribed from the calculus term by term.
fn twice_calculus(r: &mut i32) {
    let (r1, ()) = reborrow(r, |y1| *y1 = 1);
    let (_r2, ()) = reborrow(r1, |y2| *y2 = 2);
}
// ANCHOR_END: twice_calculus

// ANCHOR: read_then_push
/// The aliasing program repaired: the shared borrow ends (and gives `v` back)
/// before the mutable borrow begins.
fn read_then_push(v: Box<Vec<i32>>) -> (Box<Vec<i32>>, i32) {
    let (v, first) = lend(v, |f| f[0]);
    let (v, ()) = lend_mut(v, |m| m.push(4));
    (v, first)
}
// ANCHOR_END: read_then_push

fn main() {
    let mut n = 0;
    twice(&mut n);
    println!("twice:            n = {n}");
    assert_eq!(n, 2);

    let mut n = 0;
    twice_explicit(&mut n);
    println!("twice_explicit:   n = {n}");
    assert_eq!(n, 2);

    let mut n = 0;
    twice_generic(&mut n);
    println!("twice_generic:    n = {n}");
    assert_eq!(n, 1);

    let mut n = 0;
    twice_calculus(&mut n);
    println!("twice_calculus:   n = {n}");
    assert_eq!(n, 2);

    let (v, first) = read_then_push(Box::new(vec![1, 2, 3]));
    println!("read_then_push:   first = {first}, v = {v:?}");
    assert_eq!(*v, vec![1, 2, 3, 4]);
}
