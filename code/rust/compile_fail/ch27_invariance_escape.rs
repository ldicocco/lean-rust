// harness: compile-fail E0521
//! The same attack inside one function signature: a `&mut Vec<&'static str>`
//! cannot be viewed as a `&mut Vec<&'short str>`, so a short-lived line cannot
//! be pushed into it.

// ANCHOR: remember
pub fn remember(log: &mut Vec<&'static str>, line: &str) {
    log.push(line);
}
// ANCHOR_END: remember
