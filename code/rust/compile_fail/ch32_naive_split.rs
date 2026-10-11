// harness: compile-fail E0499
//! A safe `split_at_mut` cannot be written: the borrow checker sees two
//! mutable borrows of `*slice`, not two borrows of disjoint halves.

// ANCHOR: naive_split
pub fn naive_split_at_mut<T>(slice: &mut [T], mid: usize) -> (&mut [T], &mut [T]) {
    let len = slice.len();
    (&mut slice[..mid], &mut slice[mid..len])
}
// ANCHOR_END: naive_split
