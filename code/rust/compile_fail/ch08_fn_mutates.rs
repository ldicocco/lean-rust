// harness: compile-fail E0594
//! A closure that mutates a captured variable is `FnMut`, not `Fn`, so it
//! cannot be passed where an `Fn` is required.

// ANCHOR: count_calls
fn call_twice<F: Fn()>(f: F) {
    f();
    f();
}

pub fn count_calls() {
    let mut count = 0;
    call_twice(|| count += 1);
}
// ANCHOR_END: count_calls
