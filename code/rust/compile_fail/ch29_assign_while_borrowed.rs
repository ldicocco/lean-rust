// harness: compile-fail E0506
//! Assigning to a place while a loan of it is live.

// ANCHOR: assign_while_borrowed
fn assign_while_borrowed() -> i32 {
    let mut total = 10;
    let r = &total;
    total = 20;
    *r + total
}
// ANCHOR_END: assign_while_borrowed
