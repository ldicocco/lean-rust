// harness: run
//! Recursive types as fixed points, folds as their elimination rule, empty
//! types, and what a *negative* recursive type allows in Rust.
//!
//! Demonstrates: `List<T> = 1 + T × List<T>` with a `Box`, the fixed-point
//! isomorphism (`roll`/`unroll`), `fold` and functions defined by it,
//! `Result<T, Infallible>` with an irrefutable pattern, an uninhabited
//! recursive type, and recursion without any recursive function through a
//! type that refers to itself to the left of an arrow.
//!
//! Run with: `cargo run --example ch11_recursive_types`

use std::convert::Infallible;
use std::mem::size_of;

// ANCHOR: list
/// List<T> = 1 + T × List<T>. The `Box` stores the tail behind a pointer, so
/// that a `List<T>` has a size known at compile time.
#[derive(Debug, PartialEq)]
enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}
// ANCHOR_END: list

// ANCHOR: roll
/// One layer of the list, with the tail left as it is: 1 + T × List<T>.
type Layer<T> = Option<(T, List<T>)>;

impl<T> List<T> {
    /// Unfold one layer.
    fn unroll(self) -> Layer<T> {
        match self {
            List::Nil => None,
            List::Cons(head, tail) => Some((head, *tail)),
        }
    }

    /// Fold one layer back.
    fn roll(layer: Layer<T>) -> List<T> {
        match layer {
            None => List::Nil,
            Some((head, tail)) => List::Cons(head, Box::new(tail)),
        }
    }
}
// ANCHOR_END: roll

// ANCHOR: fold
impl<T> List<T> {
    /// The elimination rule for lists: a result for `Nil`, and a way to
    /// combine a head with the result already computed for the tail.
    fn fold<R>(self, nil: R, cons: &impl Fn(T, R) -> R) -> R {
        match self {
            List::Nil => nil,
            List::Cons(head, tail) => {
                let rest = tail.fold(nil, cons);
                cons(head, rest)
            }
        }
    }

    fn from_vec(items: Vec<T>) -> List<T> {
        let mut list = List::Nil;
        for item in items.into_iter().rev() {
            list = List::Cons(item, Box::new(list));
        }
        list
    }
}

fn length<T>(list: List<T>) -> usize {
    list.fold(0, &|_, n| n + 1)
}

fn sum(list: List<u64>) -> u64 {
    list.fold(0, &|x, total| x + total)
}

fn map<T, U>(list: List<T>, f: impl Fn(T) -> U) -> List<U> {
    list.fold(List::Nil, &|x, mapped| List::Cons(f(x), Box::new(mapped)))
}
// ANCHOR_END: fold

// ANCHOR: infallible
/// A parser that cannot fail: its error type has no values.
fn parse_trusted(digits: &str) -> Result<u64, Infallible> {
    Ok(digits.bytes().fold(0, |n, d| 10 * n + u64::from(d - b'0')))
}

/// The long way: the `Err` arm is there, and its body is a `match` with no
/// arms, because there is no `Infallible` value to take apart.
fn unwrap_long<T>(r: Result<T, Infallible>) -> T {
    match r {
        Ok(t) => t,
        Err(e) => match e {},
    }
}

/// The short way: the `Err` case would need a value of type `Infallible`, so
/// the pattern `Ok(t)` alone is exhaustive and `let` accepts it.
fn unwrap_short<T>(r: Result<T, Infallible>) -> T {
    let Ok(t) = r;
    t
}
// ANCHOR_END: infallible

// ANCHOR: loop_type
/// μX. X: the only variant needs a value of the type itself. The type is
/// accepted, but no value of it can ever be built.
#[allow(dead_code)]
enum Loop {
    Next(Box<Loop>),
}

/// Like `Infallible`, a `Loop` can be turned into anything; unlike it, the
/// proof is a recursion that would never end (and is never started). The
/// compiler notices that this function cannot return, and warns: we allow it.
#[allow(dead_code, unconditional_recursion)]
fn absurd_loop<T>(l: Loop) -> T {
    match l {
        Loop::Next(inner) => absurd_loop(*inner),
    }
}
// ANCHOR_END: loop_type

// ANCHOR: negative
/// A type that occurs to the *left* of an arrow in its own definition: a
/// `SelfApply` contains a function that takes a `SelfApply`. Lean rejects
/// the analogous `inductive`; Rust accepts it.
struct SelfApply(Box<dyn Fn(&SelfApply, u64) -> u64>);

/// Factorial, without any function that calls itself by name: the closure
/// receives *itself* as an argument and uses it for the recursive call.
fn factorial(n: u64) -> u64 {
    let fact = SelfApply(Box::new(
        |me: &SelfApply, k: u64| {
            if k == 0 { 1 } else { k * (me.0)(me, k - 1) }
        },
    ));
    (fact.0)(&fact, n)
}
// ANCHOR_END: negative

fn main() {
    // ANCHOR: run_list
    let list = List::from_vec(vec![3, 4, 5]);
    println!("list     = {list:?}");
    let layer = list.unroll();
    println!("unrolled = {layer:?}");
    let list = List::roll(layer);
    assert_eq!(list, List::from_vec(vec![3, 4, 5]));

    println!("length   = {}", length(List::from_vec(vec!['a', 'b', 'c'])));
    println!("sum      = {}", sum(list));
    println!(
        "map      = {:?}",
        map(List::from_vec(vec![1, 2]), |x| x * 10)
    );
    println!("size_of::<List<u64>>() = {}", size_of::<List<u64>>());
    // ANCHOR_END: run_list

    // ANCHOR: run_rest
    println!("unwrap_long   = {}", unwrap_long(parse_trusted("2024")));
    println!("unwrap_short  = {}", unwrap_short(parse_trusted("1999")));
    println!("factorial(10) = {}", factorial(10));
    assert_eq!(factorial(20), (1..=20).product::<u64>());
    // ANCHOR_END: run_rest
}
