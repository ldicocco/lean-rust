// harness: compile-fail E0369
//! Parametricity, enforced: without a bound, a generic function cannot even
//! compare two values of type `T`.

// ANCHOR: no_peeking
fn keep_if_same<T>(a: T, b: T) -> Option<T> {
    if a == b { Some(a) } else { None }
}
// ANCHOR_END: no_peeking
