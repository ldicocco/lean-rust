// harness: compile-fail E0040
//! `Drop::drop` cannot be called by hand: the compiler would call it again at
//! the end of the scope, releasing the resource twice.

pub struct Lock {
    pub id: u32,
}

impl Drop for Lock {
    fn drop(&mut self) {}
}

// ANCHOR: explicit
pub fn release_early(lock: Lock) {
    lock.drop();
}
// ANCHOR_END: explicit
