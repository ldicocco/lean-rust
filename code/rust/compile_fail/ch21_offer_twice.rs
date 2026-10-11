// harness: compile-fail E0382
//! `A & B` offers a choice, not both: the two consuming methods of an offer
//! cannot both be called.

pub struct Coin {
    pub serial: u32,
}
pub struct Coffee;
pub struct Tea;

fn spend(_coin: Coin) {}

pub struct Offer {
    coin: Coin,
}

impl Offer {
    pub fn coffee(self) -> Coffee {
        spend(self.coin);
        Coffee
    }

    pub fn tea(self) -> Tea {
        spend(self.coin);
        Tea
    }
}

// ANCHOR: both
pub fn both(offer: Offer) -> (Coffee, Tea) {
    (offer.coffee(), offer.tea())
}
// ANCHOR_END: both
