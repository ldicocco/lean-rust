// harness: compile-fail E0119
//! Coherence: two impls of the same trait may not apply to the same type.
//! The blanket impl already covers `i32`, which implements `Display`.

use std::fmt::Display;

// ANCHOR: overlap
trait Log {
    fn log_line(&self) -> String;
}

impl<T: Display> Log for T {
    fn log_line(&self) -> String {
        format!("[log] {self}")
    }
}

impl Log for i32 {
    fn log_line(&self) -> String {
        format!("[log] the number {self}")
    }
}
// ANCHOR_END: overlap
