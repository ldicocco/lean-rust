// harness: compile-fail E0308
//! Rule T-If: both branches of an `if` must have the same type.

// ANCHOR: describe
fn describe(ready: bool) {
    let status = if ready { 1 } else { "not yet" };
    println!("{status}");
}
// ANCHOR_END: describe
