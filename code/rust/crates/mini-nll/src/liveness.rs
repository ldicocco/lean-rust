//! Liveness (backward) and storage (forward) analyses over locals.
//!
//! A local is *live* at a point if the value it holds there may be read
//! later. Non-lexical lifetimes are built on this: a reference stored in a
//! local keeps its loan alive exactly while the local is live. The lexical
//! checker uses the storage analysis instead: a local is "in scope" from its
//! `StorageLive` to its `StorageDead`, whether or not it is used again.

use std::collections::BTreeSet;

use crate::dataflow::{Analysis, Direction};
use crate::mir::*;

pub type LocalSet = BTreeSet<Local>;

fn union(state: &mut LocalSet, other: &LocalSet) -> bool {
    let before = state.len();
    state.extend(other.iter().copied());
    state.len() != before
}

// ANCHOR: liveness
/// Backward "may" analysis: the locals whose current value may be used later.
pub struct Liveness;

impl Liveness {
    /// An assignment to `dest`: a *def* of the local if the whole local is
    /// overwritten, a *use* if we write through a reference stored in it.
    fn def(state: &mut LocalSet, dest: &Place) {
        if dest.projection.is_empty() {
            state.remove(&dest.local);
        } else if dest.has_deref() {
            state.insert(dest.local);
        }
    }
}

impl Analysis for Liveness {
    type Domain = LocalSet;
    const DIRECTION: Direction = Direction::Backward;

    fn bottom(&self, _body: &Body) -> LocalSet {
        LocalSet::new()
    }

    fn boundary(&self, _body: &Body) -> LocalSet {
        LocalSet::new() // nothing is used after `return`
    }

    fn join(&self, state: &mut LocalSet, other: &LocalSet) -> bool {
        union(state, other)
    }

    // Backward: first remove what the statement defines, then add what it
    // uses (the uses happen before the definition).
    fn apply_statement(&self, state: &mut LocalSet, stmt: &Statement, _: Location) {
        match &stmt.kind {
            StatementKind::Assign(dest, rv) => {
                Self::def(state, dest);
                for p in rv.places() {
                    state.insert(p.local);
                }
            }
            StatementKind::StorageLive(l) | StatementKind::StorageDead(l) => {
                state.remove(l);
            }
            StatementKind::FakeRead(l) => {
                state.insert(*l);
            }
        }
    }

    fn apply_terminator(&self, state: &mut LocalSet, term: &Terminator, _: Location) {
        match &term.kind {
            TerminatorKind::Call { args, dest, .. } => {
                Self::def(state, dest);
                for p in args.iter().filter_map(Operand::place) {
                    state.insert(p.local);
                }
            }
            TerminatorKind::SwitchInt { discr, .. } => {
                if let Some(p) = discr.place() {
                    state.insert(p.local);
                }
            }
            // A drop uses the value: its destructor may read it.
            TerminatorKind::Drop { place, .. } => {
                state.insert(place.local);
            }
            TerminatorKind::Return => {
                state.insert(Local(0));
            }
            TerminatorKind::Goto(_) => {}
        }
    }
}
// ANCHOR_END: liveness

/// Forward analysis: the locals whose storage is live (in scope). The return
/// place and the arguments are in scope for the whole body.
pub struct MaybeStorageLive;

impl Analysis for MaybeStorageLive {
    type Domain = LocalSet;
    const DIRECTION: Direction = Direction::Forward;

    fn bottom(&self, _body: &Body) -> LocalSet {
        LocalSet::new()
    }

    fn boundary(&self, body: &Body) -> LocalSet {
        (0..=body.arg_count).map(Local).collect()
    }

    fn join(&self, state: &mut LocalSet, other: &LocalSet) -> bool {
        union(state, other)
    }

    fn apply_statement(&self, state: &mut LocalSet, stmt: &Statement, _: Location) {
        match &stmt.kind {
            StatementKind::StorageLive(l) => {
                state.insert(*l);
            }
            StatementKind::StorageDead(l) => {
                state.remove(l);
            }
            _ => {}
        }
    }

    fn apply_terminator(&self, _: &mut LocalSet, _: &Terminator, _: Location) {}
}
