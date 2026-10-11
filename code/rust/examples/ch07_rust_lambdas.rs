// harness: run
//! Rust closures as λ-terms: the combinators of Chapter 7 written as closures,
//! call-by-value made visible, Church numerals at a fixed type, and macro
//! hygiene as capture-avoiding substitution.
//!
//! Run with: `cargo run --example ch07_rust_lambdas`

use std::rc::Rc;

// ANCHOR: combinators
/// `λx. x`
fn identity<A>(x: A) -> A {
    x
}

/// `λx. λy. x`: given x, return a closure that ignores its argument.
fn konst<A: Clone, B>(x: A) -> impl Fn(B) -> A {
    move |_y| x.clone()
}

/// `λf. λg. λx. g (f x)`: first f, then g.
fn compose<A, B, C>(f: impl Fn(A) -> B, g: impl Fn(B) -> C) -> impl Fn(A) -> C {
    move |x| g(f(x))
}
// ANCHOR_END: combinators

// ANCHOR: by_value
/// An argument that announces when it is evaluated.
fn arg(name: &'static str) -> &'static str {
    println!("  evaluating the argument {name:?}");
    name
}
// ANCHOR_END: by_value

// ANCHOR: church
/// A function on `u64`, shared so that it can be used many times.
type Fun = Rc<dyn Fn(u64) -> u64>;

/// A Church numeral *at the fixed type `u64`*: given `f`, return `f` composed
/// with itself n times.
type Church = Rc<dyn Fn(Fun) -> Fun>;

/// `0 = λf. λx. x`
fn zero() -> Church {
    Rc::new(|_f: Fun| -> Fun { Rc::new(|x| x) })
}

/// `succ = λn. λf. λx. f (n f x)`
fn succ(n: Church) -> Church {
    Rc::new(move |f: Fun| -> Fun {
        let n_f = n(f.clone());
        Rc::new(move |x| f(n_f(x)))
    })
}

/// `plus = λm. λn. λf. λx. m f (n f x)`
fn plus(m: Church, n: Church) -> Church {
    Rc::new(move |f: Fun| -> Fun {
        let m_f = m(f.clone());
        let n_f = n(f);
        Rc::new(move |x| m_f(n_f(x)))
    })
}

/// `times = λm. λn. λf. m (n f)`
fn times(m: Church, n: Church) -> Church {
    Rc::new(move |f: Fun| m(n(f)))
}

/// Read a numeral back: apply it to "add one" and start from 0.
fn to_u64(n: &Church) -> u64 {
    n(Rc::new(|x| x + 1))(0)
}
// ANCHOR_END: church

// ANCHOR: hygiene
/// Multiplies its argument by a local `x`. The `x` inside the macro and an `x`
/// at the call site are different variables: `macro_rules!` renames the
/// macro's local bindings, exactly like capture-avoiding substitution.
macro_rules! double_it {
    ($e:expr) => {{
        let x = 2;
        x * $e
    }};
}
// ANCHOR_END: hygiene

fn main() {
    // ANCHOR: combinators_use
    println!("identity(7)              = {}", identity(7));
    println!("konst(\"kept\")(42)        = {}", konst("kept")(42));
    let inc = |n: u32| n + 1;
    let double = |n: u32| n * 2;
    println!("compose(inc, double)(5)  = {}", compose(inc, double)(5));
    // ANCHOR_END: combinators_use

    // ANCHOR: by_value_use
    println!("Rust is call-by-value: both arguments are evaluated first");
    let first = |a: &'static str, _b: &'static str| a;
    let result = first(arg("a"), arg("b"));
    println!("  result: {result}");
    println!("A closure delays evaluation, as call-by-name would:");
    let first_lazy = |a: &dyn Fn() -> &'static str, _b: &dyn Fn() -> &'static str| a();
    let result = first_lazy(&|| arg("a"), &|| arg("b"));
    println!("  result: {result}");
    // ANCHOR_END: by_value_use

    // ANCHOR: church_use
    let two = succ(succ(zero()));
    let three = succ(two.clone());
    println!("Church numerals at type u64:");
    println!("  two = {}, three = {}", to_u64(&two), to_u64(&three));
    println!(
        "  plus(two, three)  = {}",
        to_u64(&plus(two.clone(), three.clone()))
    );
    println!("  times(two, three) = {}", to_u64(&times(two, three)));
    // ANCHOR_END: church_use

    // ANCHOR: hygiene_use
    let x = 10;
    let doubled = double_it!(x);
    assert_eq!(doubled, 20);
    println!("double_it!(x) with x = 10 is {doubled}, not 2 * 2 = 4");
    // ANCHOR_END: hygiene_use
}
