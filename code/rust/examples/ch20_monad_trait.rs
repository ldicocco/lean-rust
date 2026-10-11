// harness: run
//! A `Monad` trait for Rust, written with a generic associated type, and what
//! it costs. Generic code (Kleisli composition, `pair`, `sequence`) is written
//! once and used with `Option` and `Vec`, but the trait has to pick one closure
//! trait for `bind`, and generic code pays with `Clone` bounds and turbofishes.
//!
//! Run with: `cargo run --example ch20_monad_trait`

// ANCHOR: monad_trait
/// A family of types with `pure` and `bind`. `Self` is a marker type that
/// stands for a type constructor; `Self::Of<T>` applies it to `T`.
trait Monad {
    type Of<T>;

    fn pure<A>(a: A) -> Self::Of<A>;

    /// `FnMut`, not `FnOnce`: the `Vec` instance calls `f` once per element.
    fn bind<A, B, F>(m: Self::Of<A>, f: F) -> Self::Of<B>
    where
        F: FnMut(A) -> Self::Of<B>;
}

/// The marker for `Option`.
struct OptionM;

/// The marker for `Vec`.
struct VecM;

impl Monad for OptionM {
    type Of<T> = Option<T>;

    fn pure<A>(a: A) -> Option<A> {
        Some(a)
    }

    fn bind<A, B, F>(m: Option<A>, f: F) -> Option<B>
    where
        F: FnMut(A) -> Option<B>,
    {
        m.and_then(f)
    }
}

impl Monad for VecM {
    type Of<T> = Vec<T>;

    fn pure<A>(a: A) -> Vec<A> {
        vec![a]
    }

    fn bind<A, B, F>(m: Vec<A>, f: F) -> Vec<B>
    where
        F: FnMut(A) -> Vec<B>,
    {
        m.into_iter().flat_map(f).collect()
    }
}
// ANCHOR_END: monad_trait

// ANCHOR: generic
/// Kleisli composition, once for every monad.
fn kleisli<M: Monad, A, B, C>(
    mut f: impl FnMut(A) -> M::Of<B>,
    g: impl FnMut(B) -> M::Of<C> + Clone,
) -> impl FnMut(A) -> M::Of<C> {
    move |a| M::bind(f(a), g.clone())
}

/// Every combination of a result of `ma` with a result of `mb`.
fn pair<M: Monad, A: Clone, B>(ma: M::Of<A>, mb: M::Of<B>) -> M::Of<(A, B)>
where
    M::Of<B>: Clone,
{
    M::bind(ma, move |a: A| {
        M::bind(mb.clone(), move |b: B| M::pure((a.clone(), b)))
    })
}

/// Turn a list of computations into one computation of a list.
fn sequence<M: Monad, A: Clone>(ms: Vec<M::Of<A>>) -> M::Of<Vec<A>>
where
    M::Of<A>: Clone,
{
    let mut acc = M::pure(Vec::new());
    for m in ms {
        acc = M::bind(acc, move |done: Vec<A>| {
            M::bind(m.clone(), move |x: A| {
                let mut next = done.clone();
                next.push(x);
                M::pure(next)
            })
        });
    }
    acc
}
// ANCHOR_END: generic

fn parse_qty(s: &str) -> Option<u32> {
    s.trim().parse().ok()
}

fn check_qty(n: u32) -> Option<u32> {
    if (1..=100).contains(&n) {
        Some(n)
    } else {
        None
    }
}

fn sizes(product: &str) -> Vec<String> {
    vec![format!("{product}/S"), format!("{product}/M")]
}

fn colors(variant: String) -> Vec<String> {
    vec![format!("{variant}/red"), format!("{variant}/blue")]
}

fn main() {
    // ANCHOR: use_generic
    // The same generic functions, used with two different monads. The marker
    // type must be named: the compiler cannot work out `M` from `Option<u32>`.
    let mut read_qty = kleisli::<OptionM, _, _, _>(parse_qty, check_qty);
    let mut variants = kleisli::<VecM, _, _, _>(sizes, colors);
    println!("read_qty(\"12\")  = {:?}", read_qty("12"));
    println!("read_qty(\"500\") = {:?}", read_qty("500"));
    println!("variants(\"tee\") = {:?}", variants("tee"));

    println!(
        "pair, Option  = {:?}",
        pair::<OptionM, _, _>(Some(3), Some("bolts"))
    );
    println!(
        "pair, Vec     = {:?}",
        pair::<VecM, _, _>(vec![1, 2], vec!['a', 'b'])
    );

    let all = sequence::<OptionM, _>(vec![Some(1), Some(2), Some(3)]);
    let one_missing = sequence::<OptionM, _>(vec![Some(1), None, Some(3)]);
    let grid = sequence::<VecM, _>(vec![vec!["S", "M"], vec!["red", "blue"]]);
    println!("sequence, Option = {all:?} and {one_missing:?}");
    println!("sequence, Vec    = {grid:?}");
    // ANCHOR_END: use_generic

    // The standard library has `sequence` for `Option` only, as `collect`.
    let collected: Option<Vec<u32>> =
        vec![Some(1), Some(2), Some(3)].into_iter().collect();
    assert_eq!(collected, all);
}
