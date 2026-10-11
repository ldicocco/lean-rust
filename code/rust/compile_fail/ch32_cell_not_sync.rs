// harness: compile-fail E0277
//! `MyCell` inherits "not `Sync`" from `UnsafeCell`, so two threads can never
//! share one: the single-thread assumption of its `SAFETY:` comments is
//! enforced by the type system.

use std::cell::UnsafeCell;

pub struct MyCell<T> {
    value: UnsafeCell<T>,
}

impl MyCell<u32> {
    pub fn bump(&self) {
        // SAFETY: only one thread can reach a `&MyCell` (it is not `Sync`).
        unsafe { *self.value.get() += 1 };
    }
}

// ANCHOR: share
pub fn bump_in_two_threads(counter: &MyCell<u32>) {
    std::thread::scope(|s| {
        s.spawn(|| counter.bump());
        counter.bump(); // if this compiled, it would be a data race
    });
}
// ANCHOR_END: share
