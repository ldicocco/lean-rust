// harness: run
//! Functors in Rust: `map` everywhere, the functor laws checked on samples,
//! and two encodings of the missing `Functor` trait with generic associated
//! types (GATs), with their limits.
//!
//! Demonstrates: the identity and composition laws for `Option`, `Vec`,
//! `Result<_, E>`, pairs `(E, _)` and functions `fn(E) -> _`; a GAT-based
//! `Functor` trait implemented by applied types (and an impl that compiles but
//! is not what we meant); the "family" pattern, in which a marker type stands
//! for a type constructor and the laws can be checked generically; a lawless
//! map caught by the checker; contravariant functors (predicates, comparators)
//! and bifunctors (`Result`, pairs).
//!
//! Run with: `cargo run --example ch17_functors`

use std::cmp::Ordering;
use std::marker::PhantomData;

// ANCHOR: map_helpers
/// The standard library has no `map` for pairs; this one maps the second
/// component and keeps the first, a label of type `E`.
fn map_snd<E, A, B>((e, a): (E, A), f: impl FnOnce(A) -> B) -> (E, B) {
    (e, f(a))
}

/// Mapping over a function's result is composing after it.
fn map_fn<E, A, B>(r: impl Fn(E) -> A, f: impl Fn(A) -> B) -> impl Fn(E) -> B {
    move |e| f(r(e))
}
// ANCHOR_END: map_helpers

fn laws_on_samples() {
    // ANCHOR: laws_on_samples
    let f = |n: i32| n + 1;
    let g = |n: i32| n * 10;

    // Option: `Option::map`.
    for x in [None, Some(0), Some(7)] {
        assert_eq!(x.map(|a| a), x); // map id = id
        assert_eq!(x.map(|a| g(f(a))), x.map(f).map(g)); // map (g ∘ f) = map g ∘ map f
    }
    // Vec: through an iterator, `map`, then `collect`.
    for v in [vec![], vec![1, 2, 3]] {
        let map = |v: &Vec<i32>, h: &dyn Fn(i32) -> i32| -> Vec<i32> {
            v.iter().map(|&a| h(a)).collect()
        };
        assert_eq!(map(&v, &|a| a), v);
        assert_eq!(map(&v, &|a| g(f(a))), map(&map(&v, &f), &g));
    }
    // Result<_, E>: `Result::map` changes the `Ok` value, leaves `Err` alone.
    for r in [Ok(3), Err("bad input")] {
        assert_eq!(r.map(|a| a), r);
        assert_eq!(r.map(|a| g(f(a))), r.map(f).map(g));
    }
    // (E, _): a value with a label; map the value, keep the label.
    let p = ("sensor-1", 4);
    assert_eq!(map_snd(p, |a| a), p);
    assert_eq!(map_snd(p, |a| g(f(a))), map_snd(map_snd(p, f), g));
    // fn(E) -> _: mapping is post-composition; compare the results pointwise.
    let reading = |sensor: u32| sensor as i32 * 3;
    for e in [0, 5] {
        assert_eq!(map_fn(reading, |a| a)(e), reading(e));
        assert_eq!(
            map_fn(reading, |a| g(f(a)))(e),
            map_fn(map_fn(reading, f), g)(e)
        );
    }
    println!("laws: Option, Vec, Result, (E, _) and fn(E) -> _ pass on samples");
    // ANCHOR_END: laws_on_samples
}

// ANCHOR: tree
/// A binary tree with values at the nodes.
#[derive(Clone, PartialEq, Debug)]
enum Tree<A> {
    Leaf,
    Node(Box<Tree<A>>, A, Box<Tree<A>>),
}

fn node<A>(left: Tree<A>, value: A, right: Tree<A>) -> Tree<A> {
    Tree::Node(Box::new(left), value, Box::new(right))
}

/// `map` for trees: apply `f` to every value, keeping the shape.
fn map_tree<A, B>(t: Tree<A>, f: &mut impl FnMut(A) -> B) -> Tree<B> {
    match t {
        Tree::Leaf => Tree::Leaf,
        Tree::Node(l, a, r) => {
            let l = map_tree(*l, f);
            let b = f(a);
            node(l, b, map_tree(*r, f))
        }
    }
}
// ANCHOR_END: tree

// ANCHOR: gat_functor
/// A `Functor` trait with a generic associated type. `Self` is an *applied*
/// type such as `Option<A>`; `Wrapped<B>` is meant to be "the same type
/// constructor, applied to `B`".
trait Functor: Sized {
    type Elem;
    type Wrapped<B>: Functor<Elem = B>;
    fn fmap<B>(self, f: impl FnMut(Self::Elem) -> B) -> Self::Wrapped<B>;
}

impl<A> Functor for Option<A> {
    type Elem = A;
    type Wrapped<B> = Option<B>;
    fn fmap<B>(self, f: impl FnMut(A) -> B) -> Option<B> {
        self.map(f)
    }
}

impl<A> Functor for Vec<A> {
    type Elem = A;
    type Wrapped<B> = Vec<B>;
    fn fmap<B>(self, f: impl FnMut(A) -> B) -> Vec<B> {
        self.into_iter().map(f).collect()
    }
}

/// `Result<A, E>` fixes `E` and maps `A`: the partial application `Result<_, E>`.
impl<A, E> Functor for Result<A, E> {
    type Elem = A;
    type Wrapped<B> = Result<B, E>;
    fn fmap<B>(self, f: impl FnMut(A) -> B) -> Result<B, E> {
        self.map(f)
    }
}

impl<A> Functor for Tree<A> {
    type Elem = A;
    type Wrapped<B> = Tree<B>;
    fn fmap<B>(self, mut f: impl FnMut(A) -> B) -> Tree<B> {
        map_tree(self, &mut f)
    }
}

/// Generic over the container: one function for every `Functor`.
fn double_all<F: Functor<Elem = i32>>(x: F) -> F::Wrapped<i32> {
    x.fmap(|n| n * 2)
}
// ANCHOR_END: gat_functor

// ANCHOR: odd_impl
/// Nothing forces `Wrapped<B>` to be built from the same constructor as
/// `Self`: this impl compiles, and turns a `Box` into an `Option`.
impl<A> Functor for Box<A> {
    type Elem = A;
    type Wrapped<B> = Option<B>;
    fn fmap<B>(self, mut f: impl FnMut(A) -> B) -> Option<B> {
        Some(f(*self))
    }
}
// ANCHOR_END: odd_impl

fn gat_examples() {
    // ANCHOR: gat_examples
    println!(
        "gat: double_all(Some(21))      = {:?}",
        double_all(Some(21))
    );
    println!(
        "gat: double_all(vec![1, 2, 3]) = {:?}",
        double_all(vec![1, 2, 3])
    );
    let ok: Result<i32, String> = Ok(5);
    println!("gat: double_all(Ok(5))         = {:?}", double_all(ok));
    let tree = node(node(Tree::Leaf, 1, Tree::Leaf), 2, Tree::Leaf);
    println!(
        "gat: double_all(tree) has root = {:?}",
        root(&double_all(tree))
    );
    println!(
        "gat: double_all(Box::new(4))   = {:?}",
        double_all(Box::new(4))
    );
    // ANCHOR_END: gat_examples
}

fn root<A>(t: &Tree<A>) -> Option<&A> {
    match t {
        Tree::Leaf => None,
        Tree::Node(_, a, _) => Some(a),
    }
}

// ANCHOR: family
/// The "family" pattern: a marker type stands for a type constructor, and the
/// generic associated type `Of<T>` applies it to `T`.
trait Family {
    type Of<T>;
}

/// A functor is a family with a `map`.
trait FunctorFamily: Family {
    fn fmap<A, B>(x: Self::Of<A>, f: impl FnMut(A) -> B) -> Self::Of<B>;
}

struct OptionFamily;
struct VecFamily;
/// `Result<_, E>`: the marker carries the fixed error type.
struct ResultFamily<E>(PhantomData<E>);
struct TreeFamily;

impl Family for OptionFamily {
    type Of<T> = Option<T>;
}
impl FunctorFamily for OptionFamily {
    fn fmap<A, B>(x: Option<A>, f: impl FnMut(A) -> B) -> Option<B> {
        x.map(f)
    }
}
// ANCHOR_END: family

impl Family for VecFamily {
    type Of<T> = Vec<T>;
}
impl FunctorFamily for VecFamily {
    fn fmap<A, B>(x: Vec<A>, f: impl FnMut(A) -> B) -> Vec<B> {
        x.into_iter().map(f).collect()
    }
}

impl<E> Family for ResultFamily<E> {
    type Of<T> = Result<T, E>;
}
impl<E> FunctorFamily for ResultFamily<E> {
    fn fmap<A, B>(x: Result<A, E>, f: impl FnMut(A) -> B) -> Result<B, E> {
        x.map(f)
    }
}

impl Family for TreeFamily {
    type Of<T> = Tree<T>;
}
impl FunctorFamily for TreeFamily {
    fn fmap<A, B>(x: Tree<A>, mut f: impl FnMut(A) -> B) -> Tree<B> {
        map_tree(x, &mut f)
    }
}

// ANCHOR: lawless
/// A lawless "functor": it maps, then reverses the vector.
struct ReversingVec;

impl Family for ReversingVec {
    type Of<T> = Vec<T>;
}
impl FunctorFamily for ReversingVec {
    fn fmap<A, B>(x: Vec<A>, f: impl FnMut(A) -> B) -> Vec<B> {
        let mut v: Vec<B> = x.into_iter().map(f).collect();
        v.reverse();
        v
    }
}
// ANCHOR_END: lawless

// ANCHOR: generic_laws
/// The functor laws, checked once for every family `F` on sample values.
/// Here `F` is a type constructor, so both sides of each law have the same
/// type (`F::Of<i32>` and `F::Of<usize>`) and can be compared.
fn law_report<F: FunctorFamily>(samples: &[F::Of<i32>]) -> (bool, bool)
where
    F::Of<i32>: Clone + PartialEq,
    F::Of<usize>: PartialEq,
{
    let f = |n: i32| format!("{n}"); // i32 -> String
    let g = |s: String| s.len(); // String -> usize
    let identity = samples.iter().all(|x| F::fmap(x.clone(), |a| a) == *x);
    let composition = samples
        .iter()
        .all(|x| F::fmap(x.clone(), |a| g(f(a))) == F::fmap(F::fmap(x.clone(), f), g));
    (identity, composition)
}

fn show(name: &str, (identity, composition): (bool, bool)) {
    let verdict = |ok: bool| if ok { "holds" } else { "FAILS" };
    println!(
        "family: {name:<13} identity {}, composition {}",
        verdict(identity),
        verdict(composition)
    );
}
// ANCHOR_END: generic_laws

fn family_examples() {
    // ANCHOR: family_examples
    show(
        "OptionFamily",
        law_report::<OptionFamily>(&[None, Some(-5), Some(42)]),
    );
    show(
        "VecFamily",
        law_report::<VecFamily>(&[vec![], vec![1, 22, 333]]),
    );
    let results = [Ok(10), Err("timeout".to_string())];
    show("ResultFamily", law_report::<ResultFamily<String>>(&results));
    let tree = node(Tree::Leaf, 7, node(Tree::Leaf, 100, Tree::Leaf));
    show("TreeFamily", law_report::<TreeFamily>(&[Tree::Leaf, tree]));
    show(
        "ReversingVec",
        law_report::<ReversingVec>(&[vec![1, 22, 333]]),
    );
    // ANCHOR_END: family_examples
}

// ANCHOR: contravariant
/// A predicate: a test on values of type `T`.
struct Predicate<T>(Box<dyn Fn(&T) -> bool>);

impl<T: 'static> Predicate<T> {
    fn test(&self, value: &T) -> bool {
        (self.0)(value)
    }

    /// Precompose with `f`: a test on `T` becomes a test on `S`.
    /// The arrow `S -> T` is turned around into `Predicate<T> -> Predicate<S>`.
    fn contramap<S>(self, f: impl Fn(&S) -> T + 'static) -> Predicate<S> {
        Predicate(Box::new(move |s| self.test(&f(s))))
    }
}

/// A comparator on keys becomes a comparator on values: the same contramap,
/// and what `sort_by_key` does for you.
fn by_key<T, K: Ord>(key: impl Fn(&T) -> K) -> impl Fn(&T, &T) -> Ordering {
    move |a, b| key(a).cmp(&key(b))
}
// ANCHOR_END: contravariant

fn contravariant_examples() {
    // ANCHOR: contravariant_examples
    let is_large = Predicate(Box::new(|n: &usize| *n > 3));
    let is_long: Predicate<String> = is_large.contramap(|s: &String| s.len());
    println!(
        "contravariant: is_long(\"abc\") = {}, is_long(\"abcd\") = {}",
        is_long.test(&"abc".to_string()),
        is_long.test(&"abcd".to_string())
    );
    let mut words = vec!["category", "map", "functor", "id"];
    words.sort_by(by_key(|w: &&str| w.len()));
    println!("contravariant: sorted by length = {words:?}");
    // ANCHOR_END: contravariant_examples
}

// ANCHOR: bifunctor
/// A pair maps both components at once.
fn bimap_pair<A, B, C, D>(
    (a, b): (A, B),
    f: impl FnOnce(A) -> C,
    g: impl FnOnce(B) -> D,
) -> (C, D) {
    (f(a), g(b))
}
// ANCHOR_END: bifunctor

fn bifunctor_examples() {
    // ANCHOR: bifunctor_examples
    let to_message = |code: u16| format!("error {code}");
    for r in [Ok::<i32, u16>(20), Err(404)] {
        // `map` and `map_err` act on different sides, so their order does not matter.
        let one = r.map(|n| n + 1).map_err(to_message);
        let other = r.map_err(to_message).map(|n| n + 1);
        assert_eq!(one, other);
        println!("bifunctor: {r:?} -> {one:?}");
    }
    let p = bimap_pair(("temperature", 21.5), str::len, |t: f64| t.round() as i64);
    println!("bifunctor: bimap_pair = {p:?}");
    // ANCHOR_END: bifunctor_examples
}

fn main() {
    laws_on_samples();
    gat_examples();
    family_examples();
    contravariant_examples();
    bifunctor_examples();
}
