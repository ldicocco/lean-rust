// harness: compile-fail E0562
//! A curried function would like to return `impl Fn(A) -> impl Fn(B) -> C`,
//! but `impl Trait` is not allowed in the return type of an `Fn` bound.

// ANCHOR: curry
pub fn curry<A: Clone, B, C>(
    f: impl Fn(A, B) -> C + Clone,
) -> impl Fn(A) -> impl Fn(B) -> C {
    move |a: A| {
        let f = f.clone();
        move |b: B| f(a.clone(), b)
    }
}
// ANCHOR_END: curry
