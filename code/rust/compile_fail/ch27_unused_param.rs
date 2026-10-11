// harness: compile-fail E0392
//! A parameter that no field mentions has no variance, and Rust rejects it:
//! `PhantomData` must say how the type uses it.

// ANCHOR: raw_view
pub struct RawView<'a, T> {
    ptr: *const T,
    len: usize,
}
// ANCHOR_END: raw_view
