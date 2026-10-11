// harness: compile-fail E0502
//! Two-phase borrows apply only to borrows the compiler inserts, not to an
//! explicit `&mut`.

// ANCHOR: explicit_mut_borrow
fn record_count_explicit() -> Vec<usize> {
    let mut counts = Vec::new();
    Vec::push(&mut counts, counts.len());
    counts
}
// ANCHOR_END: explicit_mut_borrow
