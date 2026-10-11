// harness: compile-fail E0317
//! An `if` without `else` has an implicit `else { () }`, so rule T-If forces
//! the `then` branch to have type `()` too.

// ANCHOR: missing_else
fn bonus(points: u32) -> u32 {
    let extra = if points > 100 { 10 };
    points + extra
}
// ANCHOR_END: missing_else
