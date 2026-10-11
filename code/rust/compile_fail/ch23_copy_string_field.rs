// harness: compile-fail E0204
//! Promotion: a struct can be `Copy` only if all its fields are.

// ANCHOR: reading
#[derive(Clone, Copy)]
struct Reading {
    sensor: String,
    value: f64,
}
// ANCHOR_END: reading
