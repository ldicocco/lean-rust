// harness: compile-fail E0382
//! An additive pair `Coffee & Tea` in Rust: one value with two consuming
//! methods. Choosing one alternative uses up the value.

pub struct Coin;
pub struct Coffee;
pub struct Tea;

pub struct Voucher {
    coin: Coin,
}

// ANCHOR: voucher
impl Voucher {
    pub fn coffee(self) -> Coffee {
        drop(self.coin);
        Coffee
    }
    pub fn tea(self) -> Tea {
        drop(self.coin);
        Tea
    }
}

pub fn both(v: Voucher) -> (Coffee, Tea) {
    (v.coffee(), v.tea())
}
// ANCHOR_END: voucher
