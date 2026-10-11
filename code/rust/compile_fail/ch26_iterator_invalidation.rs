// harness: compile-fail E0502
//! Iterator invalidation: the loop holds a shared borrow of the vector for its
//! whole duration, so the body cannot push into it.

// ANCHOR: repeat_large
pub fn repeat_large(orders: &mut Vec<u32>) {
    for amount in orders.iter() {
        if *amount > 100 {
            orders.push(*amount);
        }
    }
}
// ANCHOR_END: repeat_large
