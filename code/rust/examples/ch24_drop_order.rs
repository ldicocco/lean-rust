// harness: run
//! Drop order, line by line: when Rust runs destructors, and in which order.
//!
//! Demonstrates: locals dropped in reverse declaration order, fields and
//! elements dropped in declaration order (after the outer `Drop::drop`),
//! temporaries dropped at the end of their statement, `let _ = ...` versus
//! `let _name = ...`, moves that cancel drops, drop flags for conditional
//! moves, assignment dropping the old value, and `mem::drop`.
//!
//! Run with: `cargo run --example ch24_drop_order`

// ANCHOR: noisy
/// A value that announces its own destruction.
struct Noisy(&'static str);

impl Drop for Noisy {
    fn drop(&mut self) {
        println!("  drop {}", self.0);
    }
}
// ANCHOR_END: noisy

// ANCHOR: locals
fn locals() {
    let _a = Noisy("a");
    let _b = Noisy("b");
    let _c = Noisy("c");
    println!("  end of scope");
} // _c, _b, _a are dropped here, in this order
// ANCHOR_END: locals

// ANCHOR: fields
/// A struct with its own destructor *and* fields that have destructors.
struct Pair {
    first: Noisy,
    second: Noisy,
}

impl Drop for Pair {
    fn drop(&mut self) {
        // Runs first, while the fields are still intact.
        println!("  drop Pair({}, {})", self.first.0, self.second.0);
    }
}

fn fields() {
    let _pair = Pair {
        first: Noisy("first"),
        second: Noisy("second"),
    };
    let _tuple = (Noisy("t.0"), Noisy("t.1"));
    println!("  end of scope");
}
// ANCHOR_END: fields

// ANCHOR: temporaries
fn name_length(n: &Noisy) -> usize {
    n.0.len()
}

fn temporaries() {
    // The temporary lives until the end of the statement that created it.
    let len = name_length(&Noisy("temporary"));
    println!("  after the call, len = {len}");
    // `_` is not a variable: nothing owns the value, so it is dropped at once.
    let _ = Noisy("underscore");
    println!("  after `let _ =`");
    // `_kept` is a variable: the value lives until the end of the scope.
    let _kept = Noisy("kept");
    println!("  end of scope");
}
// ANCHOR_END: temporaries

// ANCHOR: moves
/// Takes ownership: its parameter is dropped when `consume` returns.
fn consume(n: Noisy) {
    println!("  consume({})", n.0);
}

fn moves(send: bool) {
    let x = Noisy("x");
    let _y = Noisy("y");
    if send {
        consume(x); // x is moved: this scope must no longer drop it
    }
    println!("  end of scope (send = {send})");
} // _y is dropped; x is dropped only if it was not moved (a drop flag)
// ANCHOR_END: moves

// ANCHOR: early
fn early() {
    let mut slot = Noisy("old");
    println!("  slot holds {}", slot.0);
    slot = Noisy("new"); // the old value is dropped by the assignment
    println!("  slot holds {}", slot.0);
    let guard = Noisy("guard");
    drop(guard); // std::mem::drop: release now, not at the end of the scope
    println!("  end of scope");
}
// ANCHOR_END: early

fn main() {
    println!("locals:");
    locals();
    println!("fields:");
    fields();
    println!("temporaries:");
    temporaries();
    println!("moves (send = true):");
    moves(true);
    println!("moves (send = false):");
    moves(false);
    println!("early:");
    early();
}
