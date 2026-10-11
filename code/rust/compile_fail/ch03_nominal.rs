// harness: compile-fail E0308
//! Nominal typing: two structs with the same fields are different types.

// ANCHOR: units
struct Meters(f64);
struct Seconds(f64);

fn speed(distance: Meters, time: Seconds) -> f64 {
    distance.0 / time.0
}

fn oops() -> f64 {
    speed(Seconds(8.0), Meters(100.0))
}
// ANCHOR_END: units
