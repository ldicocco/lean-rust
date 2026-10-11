// harness: run
//! The resource reading of linear logic, in Rust: a tuple is ⊗, an offer
//! with two consuming methods is &, an enum is ⊕, a `FnOnce` closure is ⊸.
//! The domain is Girard's: a coin buys a coffee or a tea.
//!
//! Run with: `cargo run --example ch21_resources`

// ANCHOR: resources
/// A coin: the resource. Neither `Copy` nor `Clone`: it can be spent once.
#[derive(Debug)]
struct Coin {
    serial: u32,
}

#[derive(Debug)]
struct Coffee {
    paid_with: u32,
}

#[derive(Debug)]
struct Tea {
    paid_with: u32,
}

/// `Coin ⊸ Coffee`: spending a coin produces a coffee.
fn brew_coffee(coin: Coin) -> Coffee {
    Coffee {
        paid_with: coin.serial,
    }
}

/// `Coin ⊸ Tea`.
fn brew_tea(coin: Coin) -> Tea {
    Tea {
        paid_with: coin.serial,
    }
}
// ANCHOR_END: resources

// ANCHOR: tensor
/// ⊗R: two coins, split between the two drinks, give a coffee *and* a tea.
fn coffee_and_tea(c1: Coin, c2: Coin) -> (Coffee, Tea) {
    (brew_coffee(c1), brew_tea(c2))
}
// ANCHOR_END: tensor

// ANCHOR: with
/// `Coffee & Tea`: the machine after one coin was inserted. Both choices are
/// paid for by the *same* coin (&R shares its context); the customer picks
/// one by calling one of the consuming methods (&L1 or &L2).
struct Offer {
    coin: Coin,
}

impl Offer {
    fn insert(coin: Coin) -> Offer {
        Offer { coin }
    }

    fn coffee(self) -> Coffee {
        brew_coffee(self.coin)
    }

    fn tea(self) -> Tea {
        brew_tea(self.coin)
    }
}
// ANCHOR_END: with

// ANCHOR: with_generic
/// `A & B` in general: shared resources `S` and two ways to consume them.
struct With<S, F, G> {
    resources: S,
    left: F,
    right: G,
}

impl<S, A, B, F: FnOnce(S) -> A, G: FnOnce(S) -> B> With<S, F, G> {
    fn left(self) -> A {
        (self.left)(self.resources)
    }

    fn right(self) -> B {
        (self.right)(self.resources)
    }
}
// ANCHOR_END: with_generic

// ANCHOR: plus
/// `Coffee ⊕ Tea`: the machine decides, and the customer must handle both.
#[derive(Debug)]
enum Drink {
    Coffee(Coffee),
    Tea(Tea),
}

/// ⊕R: the machine picks a drink (here, by the coin's serial number).
fn surprise(coin: Coin) -> Drink {
    if coin.serial % 2 == 0 {
        Drink::Coffee(brew_coffee(coin))
    } else {
        Drink::Tea(brew_tea(coin))
    }
}

/// A receipt: another resource, consumed by whoever files it.
struct Receipt {
    number: u32,
}

/// Filing a receipt consumes it.
fn file(receipt: Receipt) -> u32 {
    receipt.number
}

/// ⊕L: both arms consume the same `receipt`, because only one arm runs.
fn serve(drink: Drink, receipt: Receipt) -> String {
    match drink {
        Drink::Coffee(c) => {
            format!("coffee (coin {}), filed {}", c.paid_with, file(receipt))
        }
        Drink::Tea(t) => format!("tea (coin {}), filed {}", t.paid_with, file(receipt)),
    }
}
// ANCHOR_END: plus

// ANCHOR: lolli
/// A paper cup: a resource that a coffee machine needs once.
struct Cup;

/// `Coin ⊸ Coffee` as a value: a closure that has captured the cup. It can be
/// called once, because calling it moves the cup out.
fn machine_with_cup(cup: Cup) -> impl FnOnce(Coin) -> Coffee {
    move |coin| {
        let Cup = cup; // the cup is used up by this call
        brew_coffee(coin)
    }
}
// ANCHOR_END: lolli

// ANCHOR: units
/// `0`, the empty type: from a value of it, anything follows (0L).
enum Void {}

fn absurd<T>(v: Void) -> T {
    match v {}
}

/// `1` is `()`. In an affine language, any value can be turned into `()` by
/// discarding it, so `⊤` and `1` collapse into one type.
fn discard<T>(_value: T) {}
// ANCHOR_END: units

fn main() {
    // ANCHOR: main_tensor
    let (coffee, tea) = coffee_and_tea(Coin { serial: 1 }, Coin { serial: 2 });
    println!("⊗: {coffee:?} and {tea:?}");
    // ANCHOR_END: main_tensor

    // ANCHOR: main_with
    let first = Offer::insert(Coin { serial: 3 });
    let choice = first.tea(); // `first` is consumed: no coffee from it now
    println!("&: chose {choice:?}");
    let second = Offer::insert(Coin { serial: 4 });
    println!("&: chose {:?}", second.coffee());
    let make = |serial| With {
        resources: Coin { serial },
        left: brew_coffee,
        right: brew_tea,
    };
    println!("&: chose {:?} and {:?}", make(5).left(), make(6).right());
    // ANCHOR_END: main_with

    // ANCHOR: main_plus
    for serial in [7, 8] {
        let receipt = Receipt {
            number: 100 + serial,
        };
        println!("⊕: served {}", serve(surprise(Coin { serial }), receipt));
    }
    // ANCHOR_END: main_plus

    // ANCHOR: main_lolli
    let machine = machine_with_cup(Cup);
    let coffee = machine(Coin { serial: 9 });
    println!("⊸: {coffee:?}");
    // ANCHOR_END: main_lolli

    discard(Coin { serial: 10 });
    let nothing: Option<Void> = None;
    let never_used: Option<u32> = nothing.map(absurd);
    assert!(never_used.is_none());
    println!("1: a coin discarded, () returned");
}
