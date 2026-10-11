// harness: compile-fail E0515
//! The escape check: a function cannot return a reference to one of its own
//! locals, because the local's region ends when the function returns.

// ANCHOR: shout
pub fn shout(text: &str) -> &str {
    let loud = text.to_uppercase();
    &loud
}
// ANCHOR_END: shout
