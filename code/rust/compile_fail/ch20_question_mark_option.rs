// harness: compile-fail E0277
//! `?` binds in one monad per function: the one named by the return type.

// ANCHOR: mismatch
pub fn first_qty(lines: &[&str]) -> Result<u32, String> {
    let first = lines.first()?;
    first.parse::<u32>().map_err(|e| e.to_string())
}
// ANCHOR_END: mismatch
