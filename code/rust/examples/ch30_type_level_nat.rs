// harness: run
//! Natural numbers at the type level.
//!
//! Demonstrates: Peano numerals as types (`Z`, `S<N>`), reflection from a
//! type-level number to a value (`Nat::VALUE`), addition as a trait with an
//! associated type (computed by the trait solver at compile time),
//! length-indexed vectors `Vect<T, N>` whose `head` exists only for non-empty
//! vectors, whose `zip` demands equal lengths and whose `append` adds the
//! lengths, and the dependent pair `Σ n. Vect<T, n>` as a trait object.
//!
//! Run with: `cargo run --example ch30_type_level_nat`

use std::any::type_name;
use std::marker::PhantomData;

// ANCHOR: peano
/// Zero, as a type.
struct Z;

/// The successor of `N`, as a type. `PhantomData<N>` lets the struct mention
/// `N` without storing a value of it: `S<N>` has size zero.
struct S<N>(PhantomData<N>);

/// Reflection: from a number that lives in the types back to an ordinary
/// `usize` value. The compiler computes `VALUE` by recursion on the type.
trait Nat {
    const VALUE: usize;
}

impl Nat for Z {
    const VALUE: usize = 0;
}

impl<N: Nat> Nat for S<N> {
    const VALUE: usize = N::VALUE + 1;
}

type One = S<Z>;
type Two = S<One>;
type Three = S<Two>;
type Five = S<S<Three>>;
// ANCHOR_END: peano

// ANCHOR: plus
/// Addition as a function on types, by recursion on the first argument:
///   0 + m = m
///   (n + 1) + m = (n + m) + 1
/// `<N as Plus<M>>::Sum` is the type-level number `N + M`.
trait Plus<M> {
    type Sum;
}

impl<M> Plus<M> for Z {
    type Sum = M;
}

impl<N: Plus<M>, M> Plus<M> for S<N> {
    type Sum = S<N::Sum>;
}
// ANCHOR_END: plus

// ANCHOR: vect
/// A vector whose length `N` is part of its type. The elements live in an
/// ordinary `Vec`; `N` exists only at compile time.
struct Vect<T, N> {
    items: Vec<T>,
    len: PhantomData<N>,
}

impl<T> Vect<T, Z> {
    /// The empty vector has length zero.
    fn nil() -> Self {
        Vect {
            items: Vec::new(),
            len: PhantomData,
        }
    }
}

impl<T, N> Vect<T, N> {
    /// Adding an element makes the vector one longer: `N` becomes `S<N>`.
    fn push(mut self, x: T) -> Vect<T, S<N>> {
        self.items.push(x);
        Vect {
            items: self.items,
            len: PhantomData,
        }
    }

    /// Both vectors have the same length `N`, so no element is left over.
    fn zip<U>(self, other: Vect<U, N>) -> Vect<(T, U), N> {
        let items = self.items.into_iter().zip(other.items).collect();
        Vect {
            items,
            len: PhantomData,
        }
    }

    /// The result has length `N + M`, computed by the trait solver.
    fn append<M>(mut self, other: Vect<T, M>) -> Vect<T, <N as Plus<M>>::Sum>
    where
        N: Plus<M>,
    {
        self.items.extend(other.items);
        Vect {
            items: self.items,
            len: PhantomData,
        }
    }

    fn as_slice(&self) -> &[T] {
        &self.items
    }
}

impl<T, N: Nat> Vect<T, N> {
    /// The length is read from the type, not from the `Vec`.
    fn len(&self) -> usize {
        N::VALUE
    }
}

/// `head` and `tail` exist only for vectors of length `S<N>`, that is, for
/// non-empty vectors. On `Vect<T, Z>` the methods are simply not there.
impl<T, N> Vect<T, S<N>> {
    fn head(&self) -> &T {
        &self.items[0]
    }

    fn tail(mut self) -> Vect<T, N> {
        self.items.remove(0);
        Vect {
            items: self.items,
            len: PhantomData,
        }
    }
}
// ANCHOR_END: vect

// ANCHOR: sigma
/// `Σ n. Vect<T, n>`: a vector of *some* length. The trait object hides the
/// type-level length; `len` still reports it, computed from the hidden type.
trait SomeVect<T> {
    fn len(&self) -> usize;
    fn items(&self) -> &[T];
}

impl<T, N: Nat> SomeVect<T> for Vect<T, N> {
    fn len(&self) -> usize {
        N::VALUE
    }

    fn items(&self) -> &[T] {
        &self.items
    }
}
// ANCHOR_END: sigma

/// The name of a type, without the module path, for printing.
fn short_name<X>() -> String {
    type_name::<X>().replace("ch30_type_level_nat::", "")
}

fn main() {
    // ANCHOR: main_arith
    type TwoPlusThree = <Two as Plus<Three>>::Sum;
    println!("Two + Three = {}", short_name::<TwoPlusThree>());
    println!("            = {} (as a value)", TwoPlusThree::VALUE);
    // ANCHOR_END: main_arith

    // ANCHOR: main_vect
    let names: Vect<&str, Three> = Vect::nil().push("ada").push("alan").push("grace");
    println!("names       = {:?}, len {}", names.as_slice(), names.len());
    println!("head        = {}", names.head());
    let years = Vect::nil().push(1815).push(1912).push(1906);
    let pairs = names.zip(years);
    println!("zipped      = {:?}", pairs.as_slice());
    let rest: Vect<(&str, i32), Two> = pairs.tail();
    println!("tail        = {:?}", rest.as_slice());
    // ANCHOR_END: main_vect

    // ANCHOR: main_append
    let xs: Vect<u8, Three> = Vect::nil().push(1).push(2).push(3);
    let ys: Vect<u8, Two> = Vect::nil().push(4).push(5);
    // This annotation is checked: it compiles only because 3 + 2 = 5.
    let zs: Vect<u8, Five> = xs.append(ys);
    println!("appended    = {:?}, len {}", zs.as_slice(), zs.len());
    // ANCHOR_END: main_append

    // ANCHOR: main_sigma
    // Vectors of different lengths have different types, so they cannot share
    // a `Vec`, unless the length is hidden behind a trait object.
    let bag: Vec<Box<dyn SomeVect<u8>>> = vec![
        Box::new(Vect::nil().push(7)),
        Box::new(zs),
        Box::new(Vect::<u8, Z>::nil()),
    ];
    for v in &bag {
        println!("some vector of length {}: {:?}", v.len(), v.items());
    }
    // ANCHOR_END: main_sigma
}
