// harness: compile-fail E0308
//! `!` coerces to every type, but an empty enum does not: its elimination
//! must be written out, as a `match` with no arms.

use std::convert::Infallible;

// ANCHOR: absurd
fn absurd(x: Infallible) -> u32 {
    x
}
// ANCHOR_END: absurd
