// harness: run
//! Cartesian closed structure in Rust: projections and pairing, the terminal
//! object, the exponential (`eval`, `curry`, `uncurry`) with its laws checked
//! on samples, and the place where Rust stops being cartesian: pairing and the
//! diagonal need `Clone`, so `(A, B)` of owned values is a monoidal product.
//!
//! Run with: `cargo run --example ch19_ccc`

use std::rc::Rc;

// ANCHOR: products
/// The two projections out of a product. `fst` drops the second component:
/// discarding is allowed in Rust (it runs `Drop`, if there is one).
fn fst<A, B>((a, _): (A, B)) -> A {
    a
}

fn snd<A, B>((_, b): (A, B)) -> B {
    b
}

/// Pairing ⟨f, g⟩ : X → A × B. Feeding one `x` to two functions needs two
/// copies of `x`, so the input type must be `Clone`.
fn pair<X: Clone, A, B>(
    f: impl Fn(X) -> A,
    g: impl Fn(X) -> B,
) -> impl Fn(X) -> (A, B) {
    move |x: X| (f(x.clone()), g(x))
}

/// The unique map into the terminal object `()`.
fn to_unit<A>(_: A) {}
// ANCHOR_END: products

// ANCHOR: exponential
/// The exponential object C^B: a function from B to C, as a value.
type Exp<B, C> = Box<dyn Fn(B) -> C>;

/// eval : C^B × B → C
fn eval<B, C>((g, b): (Exp<B, C>, B)) -> C {
    g(b)
}

/// curry : Hom(A × B, C) → Hom(A, C^B). The returned function may be called
/// many times, and every closure it returns needs its own `a` (hence
/// `A: Clone`) and access to `f` (shared through an `Rc`).
fn curry<A, B, C>(f: impl Fn((A, B)) -> C + 'static) -> impl Fn(A) -> Exp<B, C>
where
    A: Clone + 'static,
    B: 'static,
    C: 'static,
{
    let f = Rc::new(f);
    move |a: A| {
        let f = Rc::clone(&f);
        Box::new(move |b: B| f((a.clone(), b)))
    }
}

/// uncurry : Hom(A, C^B) → Hom(A × B, C), that is, eval ∘ (g × id).
fn uncurry<A, B, C>(g: impl Fn(A) -> Exp<B, C>) -> impl Fn((A, B)) -> C {
    move |(a, b)| eval((g(a), b))
}
// ANCHOR_END: exponential

// ANCHOR: monoidal
/// The structure that survives without `Clone`: the symmetric monoidal maps.
fn braid<A, B>((a, b): (A, B)) -> (B, A) {
    (b, a)
}

fn associate<A, B, C>(((a, b), c): ((A, B), C)) -> (A, (B, C)) {
    (a, (b, c))
}

fn unit_right<A>((a, ()): (A, ())) -> A {
    a
}

/// Currying without `Clone`: the result can be called once (A ⊸ (B ⊸ C)).
fn curry_once<A, B, C>(
    f: impl FnOnce((A, B)) -> C + 'static,
) -> impl FnOnce(A) -> Box<dyn FnOnce(B) -> C>
where
    A: 'static,
    B: 'static,
    C: 'static,
{
    // `a` and `f` are moved into the inner closure: no copies are made.
    move |a: A| -> Box<dyn FnOnce(B) -> C> { Box::new(move |b: B| f((a, b))) }
}
// ANCHOR_END: monoidal

// ANCHOR: buffer
/// A payload whose duplication is visible: cloning it says so.
#[derive(Debug, PartialEq)]
struct Payload {
    bytes: Vec<u8>,
}

impl Clone for Payload {
    fn clone(&self) -> Self {
        println!("  (cloning a payload of {} bytes)", self.bytes.len());
        Payload {
            bytes: self.bytes.clone(),
        }
    }
}

/// The diagonal A → A × A exists only for duplicable types.
fn diagonal<A: Clone>(a: A) -> (A, A) {
    (a.clone(), a)
}
// ANCHOR_END: buffer

fn main() {
    // ANCHOR: product_main
    let price_of = |item: u32| item * 100;
    let label_of = |item: u32| format!("item-{item}");
    let both = pair(price_of, label_of);
    let p = both(7);
    // The universal property: projecting the pair gives back f and g.
    assert_eq!(fst(p.clone()), price_of(7));
    assert_eq!(snd(p.clone()), label_of(7));
    println!("pair(price_of, label_of)(7) = {p:?}");
    to_unit(p);
    // ANCHOR_END: product_main

    // ANCHOR: exponential_main
    // f : (unit price, quantity) -> total
    let total = |(price, qty): (u32, u32)| price * qty;
    let samples = [(250, 4), (99, 0), (1200, 3)];

    // β: uncurry(curry(f)) = f
    let round_trip = uncurry(curry(total));
    for s in samples {
        assert_eq!(round_trip(s), total(s));
    }
    // η: curry(uncurry(g)) = g, for a g given in curried form
    let discount =
        |pct: u32| -> Exp<u32, u32> { Box::new(move |c| c * (100 - pct) / 100) };
    let again = curry(uncurry(discount));
    for (pct, cents) in [(10, 2000), (0, 1999), (50, 3)] {
        assert_eq!(again(pct)(cents), discount(pct)(cents));
    }
    let price_250 = curry(total)(250);
    println!("curry(total)(250)(4) = {}", price_250(4));
    println!(
        "eval((curry(total)(99), 3)) = {}",
        eval((curry(total)(99), 3))
    );
    println!("beta and eta hold on all samples");
    // ANCHOR_END: exponential_main

    // ANCHOR: monoidal_main
    println!("braid((1, \"a\")) = {:?}", braid((1, "a")));
    println!("associate(((1, 2), 3)) = {:?}", associate(((1, 2), 3)));
    println!("unit_right((5, ())) = {}", unit_right((5, ())));

    let greet =
        curry_once(|(name, greeting): (String, String)| format!("{greeting}, {name}"));
    let to_alice = greet(String::from("Alice"));
    println!("curry_once: {}", to_alice(String::from("Hello")));
    // ANCHOR_END: monoidal_main

    // ANCHOR: diagonal_main
    let payload = Payload {
        bytes: vec![0; 1024],
    };
    println!("diagonal(payload):");
    let (left, right) = diagonal(payload);
    assert_eq!(left, right);

    // Pairing calls the diagonal on its input.
    let summary = pair(|p: Payload| p.bytes.len(), |p: Payload| p.bytes[0]);
    println!("pair(len, first_byte)(payload):");
    println!("  = {:?}", summary(left));
    // ANCHOR_END: diagonal_main
}
