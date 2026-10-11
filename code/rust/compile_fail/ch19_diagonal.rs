// harness: compile-fail E0382
//! The diagonal `A → A × A` of a cartesian category: Rust rejects it for a
//! type that is not `Copy`, because the value would have two owners.

// ANCHOR: diagonal
fn diagonal<A>(a: A) -> (A, A) {
    (a, a)
}
// ANCHOR_END: diagonal
