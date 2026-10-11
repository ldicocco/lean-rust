// harness: compile-fail E0505
//! The dangling reference that the escape check rules out: `r` still points
//! into the box when the box is freed.

// ANCHOR: drop_while_borrowed
pub fn dangling() -> i32 {
    let b = Box::new(5);
    let r: &i32 = &b;
    drop(b);
    *r
}
// ANCHOR_END: drop_while_borrowed
