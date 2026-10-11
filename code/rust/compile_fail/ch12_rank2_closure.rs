// harness: compile-fail E0308
//! Rust's type parameters are rank-1: the caller picks `A`, `B` and `F`, so
//! `f` works at the single type `Vec<A>` and cannot be applied to a `Vec<B>`.

// ANCHOR: lengths_after
fn lengths_after<A, B, F>(f: F, a: Vec<A>, b: Vec<B>) -> (usize, usize)
where
    F: Fn(Vec<A>) -> Vec<A>,
{
    (f(a).len(), f(b).len())
}
// ANCHOR_END: lengths_after
