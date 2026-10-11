// harness: compile-fail E0382
//! A mutable reference is a unique permission: it is not `Copy`.

// ANCHOR: writers
fn writers(w: &mut String) -> (&mut String, &mut String) {
    let a = w;
    let b = w;
    (a, b)
}
// ANCHOR_END: writers
