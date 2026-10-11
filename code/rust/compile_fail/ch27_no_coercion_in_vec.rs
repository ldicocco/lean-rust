// harness: compile-fail E0308
//! Coercions are not subtyping: `&String` coerces to `&str`, but the coercion
//! does not lift through `Vec`.

// ANCHOR: names
pub fn names(owned: Vec<&String>) -> Vec<&str> {
    owned
}
// ANCHOR_END: names
