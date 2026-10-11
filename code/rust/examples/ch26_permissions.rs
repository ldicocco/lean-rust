// harness: run
//! A permission ledger: the aliasing rule checked on traces of events.
//!
//! Each trace is the sequence of borrows, uses and frees of one of Chapter 26's
//! programs. The ledger keeps, for every place, who holds which permission: the
//! owner, any number of shared (read-only) loans, or one unique (read-write)
//! loan. A loan is live from its creation to its last use in the trace, the
//! way non-lexical lifetimes work (Chapter 29 does this properly, over
//! control-flow graphs). The ledger counts *permissions on places*, not *uses
//! of variables*: a shared loan may be used any number of times.
//!
//! Run with: `cargo run --example ch26_permissions`

use std::collections::BTreeMap;

// ANCHOR: events
/// Reading or writing.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Access {
    Read,
    Write,
}

/// The events of a trace.
#[derive(Clone, Copy, Debug)]
enum Event {
    /// A new place, owned by the current function.
    Own(&'static str),
    /// `loan = &place` (shared) or `loan = &mut place` (unique).
    Borrow {
        loan: &'static str,
        place: &'static str,
        unique: bool,
    },
    /// A read or a write through a loan.
    Through(&'static str, Access),
    /// A read or a write of the place by its owner.
    Direct(&'static str, Access),
    /// The owner frees the place: end of scope, `drop`, a move.
    Free(&'static str),
}
// ANCHOR_END: events

/// A loan: which place it borrows, and whether it is unique.
struct Loan {
    place: &'static str,
    unique: bool,
}

// ANCHOR: ledger
/// The ledger. `last_use` is computed from the trace before running it, so
/// that a loan is live exactly until its last use.
struct Ledger {
    owned: Vec<&'static str>,
    loans: BTreeMap<&'static str, Loan>,
    last_use: BTreeMap<&'static str, usize>,
}

impl Ledger {
    fn new(trace: &[Event]) -> Self {
        let mut last_use = BTreeMap::new();
        for (i, event) in trace.iter().enumerate() {
            if let Event::Through(loan, _) = event {
                last_use.insert(*loan, i);
            }
        }
        Ledger {
            owned: Vec::new(),
            loans: BTreeMap::new(),
            last_use,
        }
    }

    /// The loans of `place` that are still live at step `now`.
    fn live_loans(&self, place: &str, now: usize) -> Vec<(&'static str, bool)> {
        self.loans
            .iter()
            .filter(|(name, loan)| {
                loan.place == place
                    && self.last_use.get(*name).is_some_and(|&u| u > now)
            })
            .map(|(name, loan)| (*name, loan.unique))
            .collect()
    }

    // ANCHOR: step
    /// The aliasing rule, one event at a time.
    fn step(&mut self, now: usize, event: Event) -> Result<(), String> {
        match event {
            Event::Own(place) => self.owned.push(place),
            Event::Borrow {
                loan,
                place,
                unique,
            } => {
                // Shared loans coexist; a unique loan coexists with nothing.
                for (other, other_unique) in self.live_loans(place, now) {
                    if unique || other_unique {
                        let how = if unique { "uniquely" } else { "shared" };
                        return Err(format!(
                            "cannot borrow `{place}` {how} while `{other}` is live"
                        ));
                    }
                }
                self.loans.insert(loan, Loan { place, unique });
            }
            Event::Through(loan, access) => {
                let l = &self.loans[loan];
                if !self.owned.contains(&l.place) {
                    return Err(format!("`{loan}` points to freed `{}`", l.place));
                }
                // A shared loan is a read permission only.
                if access == Access::Write && !l.unique {
                    return Err(format!("cannot write through shared loan `{loan}`"));
                }
            }
            Event::Direct(place, access) => {
                // While lent, the owner may read (if all loans are shared)
                // but not write.
                for (other, other_unique) in self.live_loans(place, now) {
                    if access == Access::Write || other_unique {
                        let verb = if access == Access::Write {
                            "write"
                        } else {
                            "read"
                        };
                        return Err(format!(
                            "cannot {verb} `{place}` while `{other}` is live"
                        ));
                    }
                }
            }
            Event::Free(place) => {
                // Freeing needs every permission back.
                if let Some((other, _)) = self.live_loans(place, now).first() {
                    return Err(format!(
                        "cannot free `{place}` while `{other}` is live"
                    ));
                }
                self.owned.retain(|p| *p != place);
            }
        }
        Ok(())
    }
    // ANCHOR_END: step
}

/// Run a whole trace, stopping at the first violation.
fn check(trace: &[Event]) -> Result<(), (usize, String)> {
    let mut ledger = Ledger::new(trace);
    for (now, event) in trace.iter().enumerate() {
        ledger.step(now, *event).map_err(|msg| (now, msg))?;
    }
    Ok(())
}
// ANCHOR_END: ledger

// ANCHOR: traces
use Access::{Read, Write};
use Event::{Borrow, Direct, Free, Own, Through};

const fn shared(loan: &'static str, place: &'static str) -> Event {
    Borrow {
        loan,
        place,
        unique: false,
    }
}

const fn unique(loan: &'static str, place: &'static str) -> Event {
    Borrow {
        loan,
        place,
        unique: true,
    }
}

/// The traces, each named after the program it comes from.
#[rustfmt::skip]
const TRACES: &[(&str, &[Event])] = &[
    // Lean's `share`: two readers, then the owner frees. Accepted.
    ("share", &[Own("x"), shared("y", "x"), shared("z", "x"),
        Through("y", Read), Through("z", Read), Free("x")]),
    // ch26_dangling (E0597) and ch26_free_while_borrowed (E0505).
    ("dangling", &[Own("reading"), shared("r", "reading"), Free("reading"),
        Through("r", Read)]),
    // ch26_shared_then_mut (E0502).
    ("shared_then_mut", &[Own("orders"), shared("first", "orders"),
        Direct("orders", Write), Through("first", Read)]),
    // The fix: the shared loan is dead after its last use. Accepted.
    ("copy_out_first", &[Own("orders"), shared("first", "orders"),
        Through("first", Read), Direct("orders", Write)]),
    // ch26_two_mut (E0499).
    ("two_mut", &[Own("accounts"), unique("from", "accounts"),
        unique("to", "accounts"), Through("from", Write), Through("to", Write)]),
    // ch26_iterator_invalidation (E0502).
    ("iterator_invalidation", &[Own("orders"), shared("iter", "orders"),
        Through("iter", Read), Direct("orders", Write), Through("iter", Read)]),
    // Writing through a shared reference (rustc: E0594).
    ("write_through_shared", &[Own("n"), shared("r", "n"), Through("r", Write)]),
    // Lend and return: a unique loan, then the owner uses the place again.
    ("lend_and_return", &[Own("log"), unique("w", "log"), Through("w", Write),
        Through("w", Write), Direct("log", Read)]),
];
// ANCHOR_END: traces

fn main() {
    for (name, trace) in TRACES {
        match check(trace) {
            Ok(()) => println!("{name:<22} ok"),
            Err((at, msg)) => println!("{name:<22} event {at}: {msg}"),
        }
    }
    assert!(check(TRACES[0].1).is_ok());
    assert!(check(TRACES[1].1).is_err());
}
