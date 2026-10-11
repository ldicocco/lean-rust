// harness: compile-fail E0502
//! A shared borrow that is used after a mutation conflicts with it (NLL).

// ANCHOR: still_used
fn still_used() {
    let mut readings = vec![10, 20, 30];
    let first = &readings[0];
    readings.push(40);
    println!("first = {first}");
}
// ANCHOR_END: still_used
