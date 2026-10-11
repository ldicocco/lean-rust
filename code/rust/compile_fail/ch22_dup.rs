// harness: compile-fail E0382
//! No contraction: the body of `dup` would need two copies of `s`.

// ANCHOR: dup
fn dup(s: String) -> (String, String) {
    (s, s)
}
// ANCHOR_END: dup
