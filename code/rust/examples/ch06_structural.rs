// harness: run
//! The three structural rules as Rust programs.
//!
//! Exchange (the order of assumptions does not matter for typing, but
//! evaluation and drop order are fixed), weakening (an unused value is
//! allowed, and its destructor runs: weakening with an effect), and
//! contraction (refused for moved values, made explicit by `Clone`, free for
//! `Copy` types).
//!
//! Run with: `cargo run --example ch06_structural`

use std::fmt;

// ANCHOR: resources
/// A connection to a server: a resource. Neither `Copy` nor `Clone`, and it
/// announces when it is closed (dropped).
struct Connection {
    host: String,
}

impl Connection {
    fn open(host: &str) -> Connection {
        println!("  open {host}");
        Connection {
            host: host.to_string(),
        }
    }
}

impl Drop for Connection {
    fn drop(&mut self) {
        println!("  close {}", self.host);
    }
}

/// A discount coupon. It can be cloned (printing a second coupon is a
/// deliberate act), but it is not `Copy`.
#[derive(Clone, Debug, PartialEq)]
struct Coupon {
    code: String,
}
// ANCHOR_END: resources

impl fmt::Display for Coupon {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "coupon {}", self.code)
    }
}

// ANCHOR: exchange
/// Exchange: from `a: A, b: B` we can build `(B, A)` as easily as `(A, B)`.
/// The order in which assumptions are listed is irrelevant to typing.
fn exchange<A, B>(a: A, b: B) -> (B, A) {
    (b, a)
}
// ANCHOR_END: exchange

// ANCHOR: weakening
/// Weakening: the assumption `_unused` is never used. Rust accepts this, and
/// the value is dropped when the function returns.
fn weaken<A, B>(a: A, _unused: B) -> A {
    a
}
// ANCHOR_END: weakening

// ANCHOR: contraction
/// Contraction, paid for: duplicating a value is an explicit call to `clone`.
fn contract_clone<A: Clone>(a: A) -> (A, A) {
    (a.clone(), a)
}

/// Contraction, for free: a `Copy` value is duplicated bit by bit, silently.
fn contract_copy<A: Copy>(a: A) -> (A, A) {
    (a, a)
}
// ANCHOR_END: contraction

/// Prints a label and returns it: lets us watch the order of evaluation.
fn note(label: &'static str) -> &'static str {
    println!("  evaluate {label}");
    label
}

fn main() {
    // ANCHOR: exchange_demo
    println!("exchange:");
    let (b, a) = exchange("order #17", 42_u32);
    println!("  exchange(\"order #17\", 42) = ({b}, {a:?})");
    // Typing does not care about order; evaluation does: left to right.
    let pair = (note("left"), note("right"));
    assert_eq!(pair, ("left", "right"));
    // Drop order is fixed too: reverse order of declaration.
    {
        let _db = Connection::open("db.internal");
        let _cache = Connection::open("cache.internal");
        println!("  end of scope");
    }
    // ANCHOR_END: exchange_demo

    // ANCHOR: weakening_demo
    println!("weakening:");
    let total = weaken(250_u32, Connection::open("audit.internal"));
    println!("  weaken returned {total}");
    let unused = Connection::open("metrics.internal");
    drop(unused); // weakening made explicit: discard the assumption now
    println!("  after drop");
    // ANCHOR_END: weakening_demo

    // ANCHOR: contraction_demo
    println!("contraction:");
    let coupon = Coupon {
        code: "SPRING-10".to_string(),
    };
    let (first, second) = contract_clone(coupon);
    assert_eq!(first, second);
    println!("  contract_clone gave {first} and {second}");
    let (x, y) = contract_copy(7_u64);
    println!("  contract_copy(7) = ({x}, {y})");
    // A shared reference is `Copy`: duplicating it duplicates a permission to
    // read, not the coupon (Part VI).
    let (r1, r2) = contract_copy(&first);
    println!(
        "  two references to the same {r1}: {}",
        std::ptr::eq(r1, r2)
    );
    // ANCHOR_END: contraction_demo

    // ANCHOR: loop_demo
    println!("loops:");
    let conn = Connection::open("orders.internal");
    for order in [101, 102, 103] {
        // Each iteration uses `conn`; borrowing makes that legal.
        println!("  send order {order} via {}", conn.host);
    }
    println!("  done sending");
    // ANCHOR_END: loop_demo
}
