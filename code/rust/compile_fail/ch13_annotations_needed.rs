// harness: compile-fail E0282
//! An inference variable that nothing constrains: the element type of the
//! vector is never determined, so the program has no single typing.

// ANCHOR: count
fn count_entries() -> usize {
    let entries = Vec::new();
    entries.len()
}
// ANCHOR_END: count
