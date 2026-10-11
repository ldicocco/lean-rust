// harness: compile-fail E0308
//! Every closure expression has its own anonymous type, so the two branches of
//! this `if` have different types (rule T-If again).

// ANCHOR: scaler
pub fn scaler(double: bool, k: u32) -> impl Fn(u32) -> u32 {
    let times_k = move |x| x * k;
    let plus_k = move |x| x + k;
    if double { times_k } else { plus_k }
}
// ANCHOR_END: scaler
