// harness: compile-fail E0382
//! Contraction is refused: an owned value that is not `Copy` cannot be used
//! twice.

pub struct Coupon {
    pub code: String,
}

pub fn redeem(coupon: Coupon) -> u32 {
    coupon.code.len() as u32
}

// ANCHOR: checkout
pub fn checkout(coupon: Coupon) -> u32 {
    let first = redeem(coupon);
    let second = redeem(coupon);
    first + second
}
// ANCHOR_END: checkout
