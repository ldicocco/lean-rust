// harness: compile-fail E0277
//! Instance resolution fails: there is no `impl Monoid for bool`, so the
//! constraint `bool: Monoid` has no proof and the call is rejected.

trait Monoid {
    fn empty() -> Self;
    fn combine(self, other: Self) -> Self;
}

fn mconcat<M: Monoid>(items: Vec<M>) -> M {
    items.into_iter().fold(M::empty(), M::combine)
}

// ANCHOR: no_instance
fn all_ready(flags: Vec<bool>) -> bool {
    mconcat(flags)
}
// ANCHOR_END: no_instance
