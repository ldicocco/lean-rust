// harness: run
//! RAII: resources released by destructors. Lock guards, a transaction that
//! rolls back unless committed, a buffered writer that flushes on drop,
//! destructors during unwinding, drop glue (`mem::needs_drop`) and
//! `ManuallyDrop`.
//!
//! Run with: `cargo run --example ch24_raii`

use std::io::{BufWriter, Write};
use std::mem::{self, ManuallyDrop};
use std::sync::Mutex;

struct Noisy(&'static str);

impl Drop for Noisy {
    fn drop(&mut self) {
        println!("  drop {}", self.0);
    }
}

// ANCHOR: lock
fn lock_guard() {
    let balance = Mutex::new(100_u32);
    {
        let mut guard = balance.lock().unwrap(); // acquire
        *guard -= 30;
        println!("  inside: locked by us? {}", balance.try_lock().is_err());
    } // the MutexGuard is dropped here: release
    println!("  after the block: free? {}", balance.try_lock().is_ok());
    println!("  balance = {}", balance.lock().unwrap());
}
// ANCHOR_END: lock

// ANCHOR: transaction
/// A transaction on an in-memory table. Rows are staged in `pending` and
/// reach the table only on `commit`; a transaction that is dropped without
/// being committed rolls back.
#[must_use = "a transaction rolls back unless it is committed"]
struct Transaction<'db> {
    table: &'db mut Vec<String>,
    pending: Vec<String>,
    committed: bool,
}

impl<'db> Transaction<'db> {
    fn begin(table: &'db mut Vec<String>) -> Self {
        Transaction {
            table,
            pending: Vec::new(),
            committed: false,
        }
    }

    fn insert(&mut self, row: &str) {
        self.pending.push(row.to_string());
    }

    /// Consumes the transaction: after `commit` it cannot be used again.
    fn commit(mut self) {
        self.table.append(&mut self.pending);
        self.committed = true;
    } // `self` is dropped here, and `drop` sees `committed == true`
}

impl Drop for Transaction<'_> {
    fn drop(&mut self) {
        if !self.committed {
            println!(
                "  rollback: {} pending row(s) discarded",
                self.pending.len()
            );
        }
    }
}

fn transactions() {
    let mut orders = Vec::new();

    let mut tx = Transaction::begin(&mut orders);
    tx.insert("order 1: 3 x sensor");
    tx.insert("order 2: 1 x cable");
    tx.commit();

    let mut tx = Transaction::begin(&mut orders);
    tx.insert("order 3: 9 x probe");
    // An early return, a `?` or a panic here would skip the commit:
    // the destructor rolls back either way.
    drop(tx);

    println!("  table = {orders:?}");
}
// ANCHOR_END: transaction

// ANCHOR: bufwriter
fn buffered_writer() {
    let mut file_contents: Vec<u8> = Vec::new();
    {
        let mut writer = BufWriter::new(&mut file_contents);
        writer.write_all(b"t,celsius\n0,21.5\n").unwrap();
        println!(
            "  buffered, not yet written: {} bytes",
            writer.buffer().len()
        );
    } // BufWriter's destructor flushes the buffer (and ignores any error)
    println!("  after the drop, written: {} bytes", file_contents.len());
}
// ANCHOR_END: bufwriter

// ANCHOR: unwinding
fn unwinding() {
    // Replace the default panic message (printed on stderr) with nothing.
    std::panic::set_hook(Box::new(|_| {}));
    let result = std::panic::catch_unwind(|| {
        let _probe = Noisy("probe guard");
        panic!("sensor disconnected");
    });
    let _ = std::panic::take_hook(); // restore the default hook
    println!("  caught a panic: {}", result.is_err());
}
// ANCHOR_END: unwinding

// ANCHOR: drop_glue
fn drop_glue() {
    println!("  u64                  {}", mem::needs_drop::<u64>());
    println!("  &String              {}", mem::needs_drop::<&String>());
    println!("  String               {}", mem::needs_drop::<String>());
    println!(
        "  (u64, String)        {}",
        mem::needs_drop::<(u64, String)>()
    );
    println!(
        "  Option<Box<u8>>      {}",
        mem::needs_drop::<Option<Box<u8>>>()
    );
    println!("  Noisy                {}", mem::needs_drop::<Noisy>());
    println!(
        "  ManuallyDrop<String> {}",
        mem::needs_drop::<ManuallyDrop<String>>()
    );
}
// ANCHOR_END: drop_glue

// ANCHOR: manually_drop
fn manually_drop() {
    let wrapped = ManuallyDrop::new(Noisy("wrapped"));
    println!("  holding {}", wrapped.0);
    let unwrapped = ManuallyDrop::into_inner(ManuallyDrop::new(Noisy("unwrapped")));
    println!("  holding {}", unwrapped.0);
    println!("  end of scope");
} // `unwrapped` is dropped; `wrapped` is not (its destructor never runs)
// ANCHOR_END: manually_drop

fn main() {
    println!("lock guard:");
    lock_guard();
    println!("transactions:");
    transactions();
    println!("buffered writer:");
    buffered_writer();
    println!("unwinding:");
    unwinding();
    println!("needs_drop (does the type have drop glue?):");
    drop_glue();
    println!("ManuallyDrop:");
    manually_drop();
}
