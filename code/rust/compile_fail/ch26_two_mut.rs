// harness: compile-fail E0499
//! A mutable reference is a unique permission: two of them to the same vector
//! cannot be alive at once, even for different indices.

// ANCHOR: transfer
pub fn transfer(accounts: &mut Vec<i64>, amount: i64) {
    let from = &mut accounts[0];
    let to = &mut accounts[1];
    *from -= amount;
    *to += amount;
}
// ANCHOR_END: transfer
