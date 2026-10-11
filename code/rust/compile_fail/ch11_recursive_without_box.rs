// harness: compile-fail E0072
//! A recursive type stored inline would need infinite size.

// ANCHOR: list
enum List<T> {
    Nil,
    Cons(T, List<T>),
}
// ANCHOR_END: list
