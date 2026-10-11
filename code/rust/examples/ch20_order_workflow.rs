// harness: run
//! The order workflow of `Book/Ch20/Transformers.lean`, written the Rust way:
//! the state is a `&mut` borrow and failure is a `Result` propagated with `?`.
//! The plain version keeps the reservations made before a failure (like
//! Lean's `ExceptT OrderError (StateM Stock)`); the atomic version works on a
//! copy and commits only on success (like `StateT Stock (Except OrderError)`).
//!
//! Run with: `cargo run --example ch20_order_workflow`

use std::collections::BTreeMap;

// ANCHOR: domain
#[derive(Debug, PartialEq)]
enum OrderError {
    EmptyOrder,
    UnknownItem(String),
    OutOfStock {
        item: String,
        wanted: u32,
        available: u32,
    },
}

/// Item names and quantities on hand. A `BTreeMap` prints in a fixed order.
type Stock = BTreeMap<String, u32>;
// ANCHOR_END: domain

// ANCHOR: reserve
/// Take `qty` units of `item` out of the stock.
fn reserve(stock: &mut Stock, item: &str, qty: u32) -> Result<(), OrderError> {
    let available = stock
        .get_mut(item)
        .ok_or_else(|| OrderError::UnknownItem(item.to_string()))?;
    if qty > *available {
        return Err(OrderError::OutOfStock {
            item: item.to_string(),
            wanted: qty,
            available: *available,
        });
    }
    *available -= qty;
    Ok(())
}

/// Reserve every line of an order; return the number of units.
fn place_order(stock: &mut Stock, lines: &[(&str, u32)]) -> Result<u32, OrderError> {
    if lines.is_empty() {
        return Err(OrderError::EmptyOrder);
    }
    for &(item, qty) in lines {
        reserve(stock, item, qty)?;
    }
    Ok(lines.iter().map(|&(_, qty)| qty).sum())
}
// ANCHOR_END: reserve

// ANCHOR: atomically
/// All or nothing: work on a copy of the stock and commit only on success.
fn place_order_atomically(
    stock: &mut Stock,
    lines: &[(&str, u32)],
) -> Result<u32, OrderError> {
    let mut draft = stock.clone();
    let units = place_order(&mut draft, lines)?;
    *stock = draft;
    Ok(units)
}
// ANCHOR_END: atomically

fn warehouse() -> Stock {
    BTreeMap::from([("bolts".to_string(), 10), ("nuts".to_string(), 4)])
}

fn main() {
    let good = [("bolts", 3), ("nuts", 2)];
    let bad = [("bolts", 3), ("nuts", 9)];

    // ANCHOR: runs
    let mut stock = warehouse();
    let result = place_order(&mut stock, &good);
    println!("plain,  good order: {result:?}, stock {stock:?}");

    let mut stock = warehouse();
    let result = place_order(&mut stock, &bad);
    println!("plain,  bad order : {result:?}, stock {stock:?}");

    let mut stock = warehouse();
    let result = place_order_atomically(&mut stock, &bad);
    println!("atomic, bad order : {result:?}, stock {stock:?}");
    // ANCHOR_END: runs
    assert_eq!(stock, warehouse());

    let mut stock = warehouse();
    assert_eq!(place_order(&mut stock, &[]), Err(OrderError::EmptyOrder));
    assert_eq!(
        place_order(&mut stock, &[("screws", 1)]),
        Err(OrderError::UnknownItem("screws".to_string()))
    );
}
