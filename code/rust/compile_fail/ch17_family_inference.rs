// harness: compile-fail E0283
//! With the "family" encoding, the compiler cannot infer the family from an
//! applied type: `Of<T>` is not injective, so `Option<i32>` does not
//! determine `F`.

trait Family {
    type Of<T>;
}
trait FunctorFamily: Family {
    fn fmap<A, B>(x: Self::Of<A>, f: impl FnMut(A) -> B) -> Self::Of<B>;
}
struct OptionFamily;
impl Family for OptionFamily {
    type Of<T> = Option<T>;
}
impl FunctorFamily for OptionFamily {
    fn fmap<A, B>(x: Option<A>, f: impl FnMut(A) -> B) -> Option<B> {
        x.map(f)
    }
}

// ANCHOR: double_all
fn double_all<F: FunctorFamily>(x: F::Of<i32>) -> F::Of<i32> {
    F::fmap(x, |n| n * 2)
}

fn caller() -> Option<i32> {
    double_all(Some(21)) // works with `double_all::<OptionFamily>`
}
// ANCHOR_END: double_all
