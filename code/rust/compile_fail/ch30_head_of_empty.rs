// harness: compile-fail E0599
//! `head` is defined only for vectors whose length is a successor.
use std::marker::PhantomData;

pub struct Z;
pub struct S<N>(PhantomData<N>);
pub struct Vect<T, N>(Vec<T>, PhantomData<N>);

impl<T, N> Vect<T, S<N>> {
    pub fn head(&self) -> &T {
        &self.0[0]
    }
}

// ANCHOR: head_of_empty
pub fn first_of_nothing() -> i32 {
    let empty: Vect<i32, Z> = Vect(Vec::new(), PhantomData);
    *empty.head()
}
// ANCHOR_END: head_of_empty
