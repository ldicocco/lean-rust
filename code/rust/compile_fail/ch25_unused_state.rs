// harness: compile-fail E0392
//! A type parameter that no field mentions is rejected: the compiler would
//! not know its variance or whether a value "owns" an `S`.

// ANCHOR: unused
pub struct Connection<S> {
    host: String,
}
// ANCHOR_END: unused
