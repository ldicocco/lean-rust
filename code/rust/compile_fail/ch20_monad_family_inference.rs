// harness: compile-fail E0283
//! A "monad family" trait: the compiler cannot recover the family from the
//! type it produces, because `Of` is not injective.

// ANCHOR: family
trait Monad {
    type Of<T>;
    fn pure<A>(a: A) -> Self::Of<A>;
}

struct OptionM;

impl Monad for OptionM {
    type Of<T> = Option<T>;
    fn pure<A>(a: A) -> Option<A> {
        Some(a)
    }
}

fn twice<M: Monad>(n: u32) -> M::Of<u32> {
    M::pure(n * 2)
}

pub fn answer() -> Option<u32> {
    twice(21)
}
// ANCHOR_END: family
