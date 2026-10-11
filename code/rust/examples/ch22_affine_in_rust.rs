// harness: run
//! The terms of the affine λ-calculus of Chapter 22, written in Rust: swap,
//! discarding (weakening, which in Rust runs a destructor), the additive pair
//! `&` as one value with two consuming methods, `match` arms that share the
//! context, closures as `FnOnce`, and partial moves.
//!
//! Run with: `cargo run --example ch22_affine_in_rust`

use std::cell::RefCell;

thread_local! {
    /// What happened, in order: the example prints it at the end.
    static LOG: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
}

fn log(event: String) {
    LOG.with(|l| l.borrow_mut().push(event));
}

/// A file handle. It is not `Copy` and not `Clone`: it is a resource.
#[derive(Debug)]
struct File(&'static str);

impl Drop for File {
    fn drop(&mut self) {
        log(format!("close {}", self.0));
    }
}

/// A connection that remembers how many messages it sent.
#[derive(Debug)]
struct Conn {
    sent: u32,
}

fn send(c: Conn, msg: String) -> Conn {
    log(format!("send {msg:?}"));
    Conn { sent: c.sent + 1 }
}

// ANCHOR: swap
/// `λp. let (x, y) = p in (y, x)`: each variable is used exactly once.
fn swap<A, B>(p: (A, B)) -> (B, A) {
    let (x, y) = p;
    (y, x)
}

/// The same function with Rust's projections. Rust tracks moves per place,
/// and `p.0` and `p.1` are different places.
fn swap_fields<A, B>(p: (A, B)) -> (B, A) {
    (p.1, p.0)
}
// ANCHOR_END: swap

// ANCHOR: first
/// `λx. λy. x`: `y` is discarded. In the calculus that is weakening and
/// nothing happens; in Rust the discarded value is dropped.
fn first<A, B>(x: A, _y: B) -> A {
    x
}
// ANCHOR_END: first

// ANCHOR: with
struct Coin;
#[derive(Debug)]
struct Coffee;
#[derive(Debug)]
struct Tea;

fn buy_coffee(_c: Coin) -> Coffee {
    Coffee
}

fn buy_tea(_c: Coin) -> Tea {
    Tea
}

/// `Coffee & Tea`: one coin, two ways to spend it. Both methods take `self`,
/// so whichever you call consumes the voucher, and the other is gone.
struct Voucher {
    coin: Coin,
}

impl Voucher {
    fn coffee(self) -> Coffee {
        buy_coffee(self.coin)
    }
    fn tea(self) -> Tea {
        buy_tea(self.coin)
    }
}

/// The general form: the shared resources `R` and the two alternatives.
struct With<R, A, B> {
    resources: R,
    fst: fn(R) -> A,
    snd: fn(R) -> B,
}

impl<R, A, B> With<R, A, B> {
    fn fst(self) -> A {
        (self.fst)(self.resources)
    }
    fn snd(self) -> B {
        (self.snd)(self.resources)
    }
}
// ANCHOR_END: with

// ANCHOR: settle
enum Either<A, B> {
    Left(A),
    Right(B),
}

/// Both arms use `c`: only one of them runs.
fn settle(m: Either<String, String>, c: Conn) -> Conn {
    match m {
        Either::Left(order) => send(c, format!("ship {order}")),
        Either::Right(refund) => send(c, format!("refund {refund}")),
    }
}
// ANCHOR_END: settle

// ANCHOR: later
/// `λu. send c msg`: the closure owns `c` and `msg`, so it is `FnOnce`.
fn later(c: Conn, msg: String) -> impl FnOnce() -> Conn {
    move || send(c, msg)
}
// ANCHOR_END: later

fn main() {
    let (f, s) = swap((String::from("report"), File("a.txt")));
    println!("swap:        ({f:?}, {s:?})");
    let (f2, s2) = swap_fields((String::from("notes"), File("b.txt")));
    println!("swap_fields: ({f2:?}, {s2:?})");

    log("first: start".to_string());
    let kept = first(String::from("kept"), File("c.txt"));
    log(format!("first: returned {kept:?}"));

    // ANCHOR: offers
    // Each voucher (each offer) is spent once, on the alternative we choose.
    let coffee = Voucher { coin: Coin }.coffee();
    let tea = Voucher { coin: Coin }.tea();
    println!("vouchers: {coffee:?}, {tea:?}");
    let offer = || With {
        resources: Coin,
        fst: buy_coffee,
        snd: buy_tea,
    };
    let (coffee, tea) = (offer().fst(), offer().snd());
    println!("offers:   {coffee:?}, {tea:?}");
    // ANCHOR_END: offers

    let c = settle(Either::Left("order 17".to_string()), Conn { sent: 0 });
    let c = settle(Either::Right("order 18".to_string()), c);
    let call = later(c, "goodbye".to_string());
    let c = call();
    println!("messages sent: {}", c.sent);
    assert_eq!(c.sent, 3);

    drop((f, s, f2, s2));
    LOG.with(|l| {
        for event in l.borrow().iter() {
            println!("log: {event}");
        }
    });
}
