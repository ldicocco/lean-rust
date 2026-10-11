// harness: compile-fail E0373
//! `thread::spawn` requires a `'static` closure: the thread may outlive every
//! local region of the function that spawns it.

// ANCHOR: spawn
use std::thread;

pub fn spawn_with_borrow() {
    let readings = vec![1, 2, 3];
    let handle = thread::spawn(|| readings.len());
    handle.join().unwrap();
}
// ANCHOR_END: spawn
