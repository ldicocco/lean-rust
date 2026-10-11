// harness: compile-fail E0499
//! Data races are aliasing plus mutation across threads: two threads cannot
//! both receive a mutable reference to the same counter.

// ANCHOR: race
use std::thread;

pub fn race() {
    let mut counter = 0;
    let first = &mut counter;
    let second = &mut counter;
    thread::scope(|s| {
        s.spawn(move || *first += 1);
        s.spawn(move || *second += 1);
    });
}
// ANCHOR_END: race
