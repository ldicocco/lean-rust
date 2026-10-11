// harness: compile-fail E0382
//! Without the reborrow that the compiler inserts at a call with a known
//! `&mut` parameter type, a mutable reference is affine: one use, and it is
//! gone.

// ANCHOR: no_reborrow
fn consume<T>(_value: T) {}

pub fn twice_generic(r: &mut i32) {
    consume(r);
    consume(r);
}
// ANCHOR_END: no_reborrow
