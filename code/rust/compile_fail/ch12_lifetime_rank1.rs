// harness: compile-fail E0597
//! A lifetime parameter is chosen by the caller, so it outlives the function
//! body: a callback typed with it cannot accept a reference to a local.

// ANCHOR: normalized_len
fn normalized_len<'a, F>(text: &str, pick: F) -> usize
where
    F: Fn(&'a str) -> &'a str,
{
    let lowered = text.to_lowercase();
    pick(&lowered).len()
}
// ANCHOR_END: normalized_len
