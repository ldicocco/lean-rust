// harness: compile-fail E0117
//! The orphan rule: an impl must be in the crate that defines the trait or
//! the crate that defines the type. Here neither `Display` nor `Vec` is ours.

use std::fmt;

// ANCHOR: orphan
impl fmt::Display for Vec<u8> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} bytes", self.len())
    }
}
// ANCHOR_END: orphan
