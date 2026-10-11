// harness: compile-fail E0308
//! The trait solver computes `2 + 0`, but it cannot prove `n + 0 = n` for an
//! unknown `n`: that would take induction.
use std::marker::PhantomData;

pub struct Z;
pub struct S<N>(PhantomData<N>);

pub trait Plus<M> {
    type Sum;
}
impl<M> Plus<M> for Z {
    type Sum = M;
}
impl<N: Plus<M>, M> Plus<M> for S<N> {
    type Sum = S<N::Sum>;
}

pub struct Vect<T, N>(Vec<T>, PhantomData<N>);

pub fn append<T, N: Plus<M>, M>(a: Vect<T, N>, b: Vect<T, M>) -> Vect<T, N::Sum> {
    let mut items = a.0;
    items.extend(b.0);
    Vect(items, PhantomData)
}

// ANCHOR: append_nil
pub fn append_nil<T, N: Plus<Z>>(v: Vect<T, N>) -> Vect<T, N> {
    let nil: Vect<T, Z> = Vect(Vec::new(), PhantomData);
    append(v, nil)
}
// ANCHOR_END: append_nil
