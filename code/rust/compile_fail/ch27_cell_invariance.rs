// harness: compile-fail E0521
//! Interior mutability makes `Cell<T>` invariant in `T`: through a shared
//! reference it can be written, so it must not be shortened either.

// ANCHOR: set_label
use std::cell::Cell;

pub fn set_label(slot: &Cell<&'static str>, label: &str) {
    slot.set(label);
}
// ANCHOR_END: set_label
