// harness: run
//! Categories in Rust: composition written generically, and the category laws
//! checked on samples.
//!
//! Demonstrates: function composition and its laws; a `Category` trait for
//! categories given as runtime data (a preorder, a monoid, the free category
//! of a protocol) with a generic law checker; products and coproducts through
//! their universal properties (`pair` needs `Clone`, `either` does not); the
//! terminal and initial objects `()` and `Void`; and how side effects break the
//! uniqueness of functions into `()`.
//!
//! Run with: `cargo run --example ch16_categories`

use std::cell::Cell;
use std::fmt::Debug;

// ANCHOR: compose
/// `compose(g, f)` is "first `f`, then `g`": the mathematician's `g ∘ f`.
fn compose<A, B, C>(g: impl Fn(B) -> C, f: impl Fn(A) -> B) -> impl Fn(A) -> C {
    move |a| g(f(a))
}

/// The identity morphism on every type `A`.
fn identity<A>(a: A) -> A {
    a
}
// ANCHOR_END: compose

fn function_laws() {
    // ANCHOR: function_laws
    let len = |s: &str| s.len();
    let double = |n: usize| 2 * n;
    let is_even = |n: usize| n % 2 == 0;
    let samples = ["", "a", "hello", "category"];
    for s in samples {
        // The unit laws: composing with the identity changes nothing.
        assert_eq!(compose(identity, len)(s), len(s));
        assert_eq!(compose(len, identity)(s), len(s));
        // Associativity: the bracketing does not matter.
        let left = compose(compose(is_even, double), len);
        let right = compose(is_even, compose(double, len));
        assert_eq!(left(s), right(s));
    }
    println!("functions: laws hold on {} samples", samples.len());
    println!(
        "functions: (double ∘ len)(\"hello\") = {}",
        compose(double, len)("hello")
    );
    // ANCHOR_END: function_laws
}

// ANCHOR: category_trait
/// A category whose objects and morphisms are runtime values. Rust cannot make
/// the *type* of a morphism depend on the *values* of its source and target
/// (that needs dependent types, Chapter 30), so `compose` checks at run time
/// that the morphisms meet, and returns `None` if they do not.
trait Category {
    type Obj: Copy + PartialEq + Debug;
    type Mor: Clone + PartialEq + Debug;

    fn source(&self, f: &Self::Mor) -> Self::Obj;
    fn target(&self, f: &Self::Mor) -> Self::Obj;
    fn id(&self, a: Self::Obj) -> Self::Mor;
    /// `compose(g, f)`: first `f`, then `g`.
    fn compose(&self, g: &Self::Mor, f: &Self::Mor) -> Option<Self::Mor>;
}
// ANCHOR_END: category_trait

// ANCHOR: check_laws
/// Checks the unit laws for every sample, and associativity for every
/// composable triple of samples. Returns the number of equations checked.
fn check_laws<C: Category>(cat: &C, samples: &[C::Mor]) -> usize {
    let mut checked = 0;
    for f in samples {
        let (a, b) = (cat.source(f), cat.target(f));
        assert_eq!(cat.compose(&cat.id(b), f).as_ref(), Some(f), "id ∘ f = f");
        assert_eq!(cat.compose(f, &cat.id(a)).as_ref(), Some(f), "f ∘ id = f");
        checked += 2;
        for g in samples.iter().filter(|g| cat.source(g) == b) {
            for h in samples.iter().filter(|h| cat.source(h) == cat.target(g)) {
                let g_f = cat.compose(g, f).expect("g and f meet");
                let h_g = cat.compose(h, g).expect("h and g meet");
                let left = cat.compose(h, &g_f);
                let right = cat.compose(&h_g, f);
                assert_eq!(left, right, "h ∘ (g ∘ f) = (h ∘ g) ∘ f");
                checked += 1;
            }
        }
    }
    checked
}
// ANCHOR_END: check_laws

// ANCHOR: divisibility
/// The preorder of positive integers ordered by divisibility: there is one
/// morphism `a ⟶ b` exactly when `a` divides `b`.
struct Divisibility;

#[derive(Clone, PartialEq, Debug)]
struct Divides {
    from: u32,
    to: u32,
}

/// The only way to build a morphism: check that `a` divides `b`.
fn divides(a: u32, b: u32) -> Option<Divides> {
    (a > 0 && b % a == 0).then_some(Divides { from: a, to: b })
}

impl Category for Divisibility {
    type Obj = u32;
    type Mor = Divides;
    fn source(&self, f: &Divides) -> u32 {
        f.from
    }
    fn target(&self, f: &Divides) -> u32 {
        f.to
    }
    fn id(&self, a: u32) -> Divides {
        Divides { from: a, to: a }
    }
    fn compose(&self, g: &Divides, f: &Divides) -> Option<Divides> {
        // Transitivity: a | b and b | c give a | c.
        (f.to == g.from).then(|| Divides {
            from: f.from,
            to: g.to,
        })
    }
}
// ANCHOR_END: divisibility

// ANCHOR: string_monoid
/// The monoid of strings under concatenation, as a category with one object
/// `()`: every string is a morphism `() ⟶ ()`.
struct Strings;

impl Category for Strings {
    type Obj = ();
    type Mor = String;
    fn source(&self, _: &String) {}
    fn target(&self, _: &String) {}
    fn id(&self, _: ()) -> String {
        String::new()
    }
    fn compose(&self, g: &String, f: &String) -> Option<String> {
        Some(format!("{f}{g}")) // first f's text, then g's
    }
}
// ANCHOR_END: string_monoid

// ANCHOR: protocol_graph
/// The states of a connection, and the operations of its protocol.
#[derive(Clone, Copy, PartialEq, Debug)]
enum State {
    Closed,
    Connected,
    Authenticated,
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum Op {
    Connect,
    Login,
    Logout,
    Close,
}

/// The edges of the protocol graph: where each operation may start and end.
fn step(state: State, op: Op) -> Option<State> {
    use State::*;
    match (state, op) {
        (Closed, Op::Connect) => Some(Connected),
        (Connected, Op::Login) => Some(Authenticated),
        (Authenticated, Op::Logout) => Some(Connected),
        (Connected, Op::Close) => Some(Closed),
        _ => None,
    }
}
// ANCHOR_END: protocol_graph

// ANCHOR: protocol_trace
/// A morphism of the free category: a path in the graph, that is, a sequence
/// of operations that the protocol allows, starting from `from`.
#[derive(Clone, PartialEq, Debug)]
struct Trace {
    from: State,
    to: State,
    ops: Vec<Op>,
}

impl Trace {
    fn new(from: State, ops: &[Op]) -> Option<Trace> {
        let mut to = from;
        for &op in ops {
            to = step(to, op)?;
        }
        Some(Trace {
            from,
            to,
            ops: ops.to_vec(),
        })
    }
}
// ANCHOR_END: protocol_trace

// ANCHOR: protocol_category
/// The free category on the protocol graph.
struct Protocol;

impl Category for Protocol {
    type Obj = State;
    type Mor = Trace;
    fn source(&self, f: &Trace) -> State {
        f.from
    }
    fn target(&self, f: &Trace) -> State {
        f.to
    }
    fn id(&self, a: State) -> Trace {
        Trace {
            from: a,
            to: a,
            ops: Vec::new(),
        }
    }
    fn compose(&self, g: &Trace, f: &Trace) -> Option<Trace> {
        if f.to != g.from {
            return None; // the paths do not meet
        }
        let ops = f.ops.iter().chain(&g.ops).copied().collect();
        Some(Trace {
            from: f.from,
            to: g.to,
            ops,
        })
    }
}
// ANCHOR_END: protocol_category

fn data_categories() {
    // ANCHOR: use_divisibility
    let div = Divisibility;
    let (a, b) = (divides(3, 12).unwrap(), divides(12, 36).unwrap());
    println!(
        "divisibility: (12 ⟶ 36) ∘ (3 ⟶ 12) = {:?}",
        div.compose(&b, &a)
    );
    let samples: Vec<Divides> = (1..=12)
        .flat_map(|a| (1..=12).filter_map(move |b| divides(a, b)))
        .collect();
    println!(
        "divisibility: {} equations checked",
        check_laws(&div, &samples)
    );
    // ANCHOR_END: use_divisibility

    // ANCHOR: use_strings
    let words: Vec<String> = ["", "con", "cat", "egory"].map(String::from).to_vec();
    let concat = Strings.compose(&words[2], &words[1]).unwrap();
    println!("strings: \"cat\" ∘ \"con\" = {concat:?}");
    println!(
        "strings: {} equations checked",
        check_laws(&Strings, &words)
    );
    // ANCHOR_END: use_strings

    // ANCHOR: use_protocol
    use {Op::*, State::*};
    let sign_in = Trace::new(Closed, &[Connect, Login]).unwrap();
    let sign_out = Trace::new(Authenticated, &[Logout, Close]).unwrap();
    let session = Protocol.compose(&sign_out, &sign_in).unwrap();
    println!("protocol: sign_out ∘ sign_in = {:?}", session.ops);
    println!(
        "protocol: sign_in ∘ sign_in = {:?}",
        Protocol.compose(&sign_in, &sign_in)
    );
    let traces: Vec<Trace> = [
        (Closed, vec![Connect]),
        (Connected, vec![Login, Logout]),
        (Connected, vec![Close, Connect]),
        (Authenticated, vec![Logout, Close]),
        (Closed, vec![Connect, Login]),
    ]
    .iter()
    .filter_map(|(from, ops)| Trace::new(*from, ops))
    .collect();
    println!(
        "protocol: {} equations checked",
        check_laws(&Protocol, &traces)
    );
    // ANCHOR_END: use_protocol
}

// ANCHOR: product
/// The pairing of the universal property of products: from `f: X -> A` and
/// `g: X -> B`, the unique `X -> (A, B)` whose projections are `f` and `g`.
/// Rust needs `X: Clone` to feed the same input to both functions.
fn pair<X: Clone, A, B>(
    f: impl Fn(X) -> A,
    g: impl Fn(X) -> B,
) -> impl Fn(X) -> (A, B) {
    move |x| (f(x.clone()), g(x))
}
// ANCHOR_END: product

// ANCHOR: coproduct
/// A sum type with two cases: the coproduct of `A` and `B`.
#[derive(Debug)]
enum Either<A, B> {
    Left(A),
    Right(B),
}

/// The copairing: from `f: A -> X` and `g: B -> X`, the unique
/// `Either<A, B> -> X` that behaves like `f` on `Left` and like `g` on `Right`.
/// No `Clone` is needed: each input is used once.
fn either<A, B, X>(
    f: impl Fn(A) -> X,
    g: impl Fn(B) -> X,
) -> impl Fn(Either<A, B>) -> X {
    move |e| match e {
        Either::Left(a) => f(a),
        Either::Right(b) => g(b),
    }
}
// ANCHOR_END: coproduct

// ANCHOR: terminal_initial
/// The unique function from any type into the terminal object `()`.
fn to_unit<A>(_: A) {}

/// A type with no values, and the unique function out of it: the initial object.
enum Void {}

fn absurd<A>(v: Void) -> A {
    match v {}
}
// ANCHOR_END: terminal_initial

fn universal_properties() {
    // ANCHOR: universal_checks
    let square = |n: u32| n * n;
    let label = |n: u32| format!("#{n}");
    let both = pair(square, label);
    for n in [0, 1, 7, 12] {
        // The two triangles of the product diagram commute.
        assert_eq!(both(n).0, square(n));
        assert_eq!(both(n).1, label(n));
        // Any other `h` with the same projections agrees with `pair`.
        let h = |n: u32| (n.pow(2), format!("#{}", n));
        assert_eq!(h(n), both(n));
    }
    println!("product: pair(square, label)(7) = {:?}", both(7));

    let describe = either(
        |n: u32| format!("number {n}"),
        |s: &str| format!("word {s}"),
    );
    println!("coproduct: {}", describe(Either::Left(42)));
    println!("coproduct: {}", describe(Either::Right("hello")));

    let units: Vec<()> = ["a", "b"].into_iter().map(to_unit).collect();
    println!(
        "terminal: to_unit maps {} strings to {:?}",
        units.len(),
        units
    );
    let nothing: Vec<Void> = Vec::new();
    let numbers: Vec<u32> = nothing.into_iter().map(absurd).collect();
    println!("initial: absurd maps no values to {numbers:?}");
    // ANCHOR_END: universal_checks
}

fn effects() {
    // ANCHOR: effects
    // Two functions `i32 -> ()` that return the same thing on every input...
    let calls = Cell::new(0);
    let quiet = |_: i32| ();
    let noisy = |_: i32| calls.set(calls.get() + 1);
    for n in 0..3 {
        assert_eq!(quiet(n), noisy(n));
    }
    // ...but they are different programs: `()` is terminal only for pure code.
    println!("effects: same outputs, but noisy ran {} times", calls.get());
    // ANCHOR_END: effects
}

fn main() {
    function_laws();
    data_categories();
    universal_properties();
    effects();
}
