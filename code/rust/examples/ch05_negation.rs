// harness: run
//! Negation as a function into an empty type: Chapter 5's reading of `¬A` as
//! `A → ⊥`, in Rust.
//!
//! Demonstrates: an empty enum as falsity and `match v {}` as ⊥E; refutations
//! as functions into the empty type; the standard library's `Infallible` and
//! how the compiler uses emptiness (irrefutable `let Ok(..)`, arms you may
//! omit); the never type `!`; and the double negation of excluded middle run
//! as a program, with the empty type replaced by an answer type so that it
//! can actually be run.
//!
//! Run with: `cargo run --example ch05_negation`

use std::cell::RefCell;
use std::convert::Infallible;
use std::mem::size_of;
use std::rc::Rc;
use std::str::FromStr;

// ANCHOR: void
/// Falsity: a type with no values at all.
#[derive(Debug)]
enum Void {}

/// Rule ⊥E: from a value of the empty type, a value of any type. The `match`
/// has no arms because there is no case to handle.
fn absurd<T>(v: Void) -> T {
    match v {}
}
// ANCHOR_END: void

// ANCHOR: not
/// `¬A`: a refutation of `A`, a function that turns any `A` into a `Void`.
type Not<A> = Box<dyn FnOnce(A) -> Void>;

/// `A → ¬¬A`: given an `a`, refute every refutation of `A` by feeding it `a`.
fn dni<A: 'static>(a: A) -> Not<Not<A>> {
    Box::new(move |refutation: Not<A>| refutation(a))
}

/// `(A → B) → (¬B → ¬A)`: contraposition is composition.
fn contrapose<A: 'static, B: 'static>(
    f: impl FnOnce(A) -> B + 'static,
    not_b: Not<B>,
) -> Not<A> {
    Box::new(move |a| not_b(f(a)))
}

/// `¬¬¬A → ¬A`: triple negation collapses.
fn tne<A: 'static>(nnn: Not<Not<Not<A>>>) -> Not<A> {
    Box::new(move |a| nnn(dni(a)))
}

/// `¬⊥`: falsity is refutable, by the identity function.
fn not_false() -> Not<Void> {
    Box::new(|v| v)
}
// ANCHOR_END: not

// ANCHOR: infallible
/// A name can be parsed from any string, so parsing cannot fail: the error
/// type is `Infallible`, the standard library's empty enum.
struct Name(String);

impl FromStr for Name {
    type Err = Infallible;
    fn from_str(s: &str) -> Result<Name, Infallible> {
        Ok(Name(s.trim().to_lowercase()))
    }
}

fn parse_name(s: &str) -> Name {
    // The pattern `Ok(name)` is irrefutable: `Err(e)` would need an `e` of an
    // empty type, so the compiler knows that case cannot occur.
    let Ok(name) = s.parse::<Name>();
    name
}

/// An `Option` of an empty type can only be `None`, and the match needs no
/// `Some` arm.
fn only_none(x: Option<Void>) -> &'static str {
    match x {
        None => "None",
    }
}
// ANCHOR_END: infallible

// ANCHOR: never
/// `!` is Rust's built-in empty type. A function returning `!` never returns,
/// and a `!` can stand in for a value of any type (⊥E, built into the language).
fn give_up(reason: &str) -> ! {
    panic!("giving up: {reason}")
}

fn digit_value(c: char) -> u32 {
    match c.to_digit(10) {
        Some(d) => d,
        None => give_up("not a digit"), // has type `!`, coerced to `u32`
    }
}
// ANCHOR_END: never

// ANCHOR: nn_em
/// A sum type: a value of `A ∨ B` says which side it is on.
enum Either<L, R> {
    Left(L),
    Right(R),
}

/// "Refutations" relative to an answer type `R`: consumers of `A`s. With
/// `R = Void` this is `¬A`; with an ordinary `R` we can run it.
type Neg<A, R> = Rc<dyn Fn(A) -> R>;

/// `¬¬(A ∨ ¬A)`, the double negation of excluded middle. Given a consumer `k`
/// of `A ∨ ¬A`, first answer "¬A" with a refutation. If `k` ever applies that
/// refutation to some `a`, go back and call `k` again, this time with
/// `Left(a)`. The consumer is used twice, which is why it is an `Rc<dyn Fn>`.
fn nn_em<A: 'static, R: 'static>(k: Neg<Either<A, Neg<A, R>>, R>) -> R {
    let k_again = Rc::clone(&k);
    let refutation: Neg<A, R> = Rc::new(move |a| k_again(Either::Left(a)));
    k(Either::Right(refutation))
}
// ANCHOR_END: nn_em

fn main() {
    // ANCHOR: main_empty
    println!("size_of::<Void>() = {}", size_of::<Void>());
    println!("size_of::<Infallible>() = {}", size_of::<Infallible>());
    println!("parse_name(\"  Ada \").0 = {:?}", parse_name("  Ada ").0);
    println!("only_none(None) = {}", only_none(None));
    println!("digit_value('7') = {}", digit_value('7'));
    // ANCHOR_END: main_empty

    // ANCHOR: main_not
    // Refutations can be built, and they type-check, which is the point. None
    // of them can ever be run to completion: that would produce a `Void`.
    let _refutes_refutations_of_7: Not<Not<u8>> = dni(7u8);
    let _not_false: Not<Void> = contrapose(|v: Void| v, not_false());
    let _not_false_again: Not<Void> = tne(dni(not_false()));
    let _ex_falso: fn(Void) -> String = absurd::<String>;
    // ANCHOR_END: main_not

    // ANCHOR: main_nn_em
    // Run ¬¬(A ∨ ¬A) with A = u32 and answers of type String.
    let log = Rc::new(RefCell::new(Vec::new()));
    let seen = Rc::clone(&log);
    let k: Neg<Either<u32, Neg<u32, String>>, String> =
        Rc::new(move |answer| match answer {
            Either::Left(a) => {
                seen.borrow_mut().push(format!("k received Left({a})"));
                format!("A holds, witness {a}")
            }
            Either::Right(refutation) => {
                seen.borrow_mut()
                    .push("k received Right(refutation)".to_string());
                seen.borrow_mut()
                    .push("k applies the refutation to 42".to_string());
                refutation(42)
            }
        });
    let result = nn_em(k);
    for line in log.borrow().iter() {
        println!("{line}");
    }
    println!("result: {result}");
    // ANCHOR_END: main_nn_em
}
