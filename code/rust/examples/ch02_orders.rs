// harness: run
//! An order book: structs, enums, `Result`, `BTreeMap` and iterators.
//!
//! Traders place limit orders to buy or sell at a price; the book keeps the
//! orders that are waiting. This book is "post-only": an order that would
//! trade immediately against the other side is rejected instead of matched,
//! so the book is never *crossed* (every bid is below every ask).
//!
//! The same program is written in Lean in `code/lean/Book/Ch02/Orders.lean`,
//! and `code/lean/Book/Ch02/FirstProofs.lean` proves properties of it.
//!
//! Run with: `cargo run --example ch02_orders`

use std::collections::BTreeMap;
use std::fmt;

// ANCHOR: types
/// Which side of the book an order is on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Side {
    Buy,
    Sell,
}

/// A resting limit order. Prices are in cents, so that they are exact.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Order {
    id: u64,
    trader: String,
    side: Side,
    price: u64,
    qty: u64,
}

/// Why an order or a cancellation was rejected.
#[derive(Debug, Clone, PartialEq, Eq)]
enum OrderError {
    ZeroQuantity,
    ZeroPrice,
    /// The order would trade against `best`, the best price on the other side.
    WouldCross {
        best: u64,
    },
    UnknownOrder(u64),
}

/// The resting orders, by id, and the id the next order will get.
#[derive(Debug)]
struct Book {
    orders: BTreeMap<u64, Order>,
    next_id: u64,
}
// ANCHOR_END: types

// ANCHOR: display
/// A price in cents, printed as dollars and cents.
fn price(cents: u64) -> String {
    format!("{}.{:02}", cents / 100, cents % 100)
}

impl fmt::Display for Order {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let verb = match self.side {
            Side::Buy => "buys",
            Side::Sell => "sells",
        };
        let (id, who, qty, p) = (self.id, &self.trader, self.qty, price(self.price));
        write!(f, "#{id} {who} {verb} {qty} @ {p}")
    }
}

impl fmt::Display for OrderError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OrderError::ZeroQuantity => write!(f, "quantity must be positive"),
            OrderError::ZeroPrice => write!(f, "price must be positive"),
            OrderError::WouldCross { best } => {
                write!(f, "would cross the best price {}", price(*best))
            }
            OrderError::UnknownOrder(id) => write!(f, "no order #{id}"),
        }
    }
}
// ANCHOR_END: display

// ANCHOR: queries
impl Book {
    fn new() -> Book {
        Book {
            orders: BTreeMap::new(),
            next_id: 1,
        }
    }

    /// The orders on one side, in id order.
    fn side(&self, side: Side) -> impl Iterator<Item = &Order> {
        self.orders.values().filter(move |o| o.side == side)
    }

    /// The highest price a buyer is offering.
    fn best_bid(&self) -> Option<u64> {
        self.side(Side::Buy).map(|o| o.price).max()
    }

    /// The lowest price a seller is asking.
    fn best_ask(&self) -> Option<u64> {
        self.side(Side::Sell).map(|o| o.price).min()
    }

    /// The gap between the best ask and the best bid. The subtraction cannot
    /// underflow because the book is never crossed: Lean proves it.
    fn spread(&self) -> Option<u64> {
        let bid = self.best_bid()?;
        let ask = self.best_ask()?;
        Some(ask - bid)
    }

    /// The total quantity on one side.
    fn volume(&self, side: Side) -> u64 {
        self.side(side).map(|o| o.qty).sum()
    }

    /// The total quantity at each price on one side, by increasing price.
    fn depth(&self, side: Side) -> BTreeMap<u64, u64> {
        let mut levels = BTreeMap::new();
        for o in self.side(side) {
            *levels.entry(o.price).or_insert(0) += o.qty;
        }
        levels
    }
}
// ANCHOR_END: queries

// ANCHOR: commands
impl Book {
    /// The best price on the other side, if an order at `price` would trade
    /// against it.
    fn crossing(&self, side: Side, price: u64) -> Option<u64> {
        match side {
            Side::Buy => self.best_ask().filter(|&ask| ask <= price),
            Side::Sell => self.best_bid().filter(|&bid| price <= bid),
        }
    }

    /// Validate an order and add it to the book; return its id.
    fn place(
        &mut self,
        trader: &str,
        side: Side,
        price: u64,
        qty: u64,
    ) -> Result<u64, OrderError> {
        if qty == 0 {
            return Err(OrderError::ZeroQuantity);
        }
        if price == 0 {
            return Err(OrderError::ZeroPrice);
        }
        if let Some(best) = self.crossing(side, price) {
            return Err(OrderError::WouldCross { best });
        }
        let id = self.next_id;
        let trader = trader.to_string();
        let order = Order {
            id,
            trader,
            side,
            price,
            qty,
        };
        self.orders.insert(id, order);
        self.next_id += 1;
        Ok(id)
    }

    /// Remove an order from the book and return it.
    fn cancel(&mut self, id: u64) -> Result<Order, OrderError> {
        self.orders.remove(&id).ok_or(OrderError::UnknownOrder(id))
    }
}
// ANCHOR_END: commands

// ANCHOR: main
fn main() {
    let mut book = Book::new();
    let requests = [
        ("alice", Side::Buy, 10050, 10),
        ("bob", Side::Sell, 10125, 5),
        ("carol", Side::Buy, 10075, 7),
        ("dave", Side::Sell, 10125, 8),
        ("gina", Side::Sell, 10200, 4),
        ("erin", Side::Buy, 10150, 3),
        ("frank", Side::Sell, 9900, 0),
    ];
    for (trader, side, p, qty) in requests {
        match book.place(trader, side, p, qty) {
            Ok(id) => println!("placed   {}", book.orders[&id]),
            Err(e) => println!("rejected {trader}: {e}"),
        }
    }

    let (bid, ask) = (book.best_bid().unwrap(), book.best_ask().unwrap());
    let spread = book.spread().unwrap();
    println!(
        "best bid {}, best ask {}, spread {}",
        price(bid),
        price(ask),
        price(spread)
    );
    let (buys, sells) = (book.volume(Side::Buy), book.volume(Side::Sell));
    println!("volume: {buys} to buy, {sells} to sell");
    for (p, qty) in book.depth(Side::Sell) {
        println!("sell depth at {}: {qty}", price(p));
    }

    match book.cancel(3) {
        Ok(order) => println!("cancelled {order}"),
        Err(e) => println!("rejected cancel: {e}"),
    }
    match book.cancel(3) {
        Ok(order) => println!("cancelled {order}"),
        Err(e) => println!("rejected cancel: {e}"),
    }
    println!("best bid now {}", price(book.best_bid().unwrap()));
    assert_eq!(book.orders.len(), 4);
}
// ANCHOR_END: main
