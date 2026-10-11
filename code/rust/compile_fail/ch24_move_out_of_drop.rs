// harness: compile-fail E0509
//! A type with a destructor cannot be taken apart by moving a field out: the
//! destructor needs the whole value.

pub struct Transaction {
    pub pending: Vec<String>,
}

impl Drop for Transaction {
    fn drop(&mut self) {}
}

// ANCHOR: move_out
pub fn steal_rows(tx: Transaction) -> Vec<String> {
    tx.pending
}
// ANCHOR_END: move_out
