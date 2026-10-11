// harness: compile-fail E0308
//! With the GAT-based `Functor` trait, the composition law cannot even be
//! stated: mapping twice and mapping once produce two different types.

trait Functor: Sized {
    type Elem;
    type Wrapped<B>: Functor<Elem = B>;
    fn fmap<B>(self, f: impl FnMut(Self::Elem) -> B) -> Self::Wrapped<B>;
}

// ANCHOR: composition_law
fn comp_law<F, B, C>(x: F, f: impl Fn(F::Elem) -> B, g: impl Fn(B) -> C) -> bool
where
    F: Functor + Clone,
    F::Wrapped<C>: PartialEq,
{
    let once = x.clone().fmap(|a| g(f(a)));
    let twice = x.fmap(&f).fmap(&g);
    once == twice
}
// ANCHOR_END: composition_law
