// harness: compile-fail E0382
//! Contraction is not free: A → A ∧ A needs a value twice, and a value of an
//! arbitrary type `A` can be used only once unless `A: Copy` or `A: Clone`.

// ANCHOR: dup
fn dup<A>(a: A) -> (A, A) {
    (a, a)
}
// ANCHOR_END: dup
