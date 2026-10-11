// harness: compile-fail E0502
//! Aliasing XOR mutation: while a shared reference into the vector is alive,
//! the vector cannot be mutated (a `push` may move its buffer).

// ANCHOR: first_then_push
pub fn first_then_push(orders: &mut Vec<u32>) {
    let first = &orders[0];
    orders.push(99);
    println!("first order: {first}");
}
// ANCHOR_END: first_then_push
