// harness: compile-fail E0308
//! `zip` takes two vectors of the same type-level length.
use std::marker::PhantomData;

pub struct Z;
pub struct S<N>(PhantomData<N>);
pub struct Vect<T, N>(Vec<T>, PhantomData<N>);

impl<T, N> Vect<T, N> {
    pub fn zip<U>(self, other: Vect<U, N>) -> Vect<(T, U), N> {
        Vect(self.0.into_iter().zip(other.0).collect(), PhantomData)
    }
}

// ANCHOR: zip_lengths
pub fn pair_up(names: Vect<&str, S<S<Z>>>, ages: Vect<u32, S<Z>>) {
    let _pairs = names.zip(ages);
}
// ANCHOR_END: zip_lengths
