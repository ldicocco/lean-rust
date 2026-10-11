// harness: compile-fail E0109
//! Rust has no higher-kinded type parameters: a type parameter stands for a
//! type, never for a type constructor, so it cannot be applied to arguments.

// ANCHOR: column
/// A column of a table, stored in a container of our choice (`Vec`,
/// `VecDeque`, ...): we would like to pass the container's type constructor.
struct Column<F> {
    values: F<String>,
}
// ANCHOR_END: column
