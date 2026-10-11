//! Location-sensitive loan liveness, after Polonius.
//!
//! NLL computes one set of points per region and asks "is this point in the
//! loan's region?". Polonius turns the question around: an *origin* (a
//! region) is a set of *loans*, and the facts are computed per point:
//!
//! ```text
//! origin_contains_loan_on_entry(O, L, P) :- loan_issued_at(O, L, P).
//! origin_contains_loan_on_entry(O2, L, P) :-
//!     origin_contains_loan_on_entry(O1, L, P), subset(O1, O2, P).
//! origin_contains_loan_on_entry(O, L, Q) :-
//!     origin_contains_loan_on_entry(O, L, P), !loan_killed_at(L, P),
//!     cfg_edge(P, Q), origin_live_on_entry(O, Q).
//! subset(O1, O2, P) :- subset_base(O1, O2, P).
//! subset(O1, O3, P) :- subset(O1, O2, P), subset(O2, O3, P).
//! subset(O1, O2, Q) :-
//!     subset(O1, O2, P), cfg_edge(P, Q),
//!     origin_live_on_entry(O1, Q), origin_live_on_entry(O2, Q).
//! loan_live_at(L, P) :-
//!     origin_contains_loan_on_entry(O, L, P), origin_live_on_entry(O, P).
//! errors(L, P) :- loan_invalidated_at(L, P), loan_live_at(L, P).
//! ```
//!
//! Here the rules are run as a forward dataflow analysis with our framework:
//! the state at a point holds the `origin_contains_loan` and `subset` facts.
//! (Real Polonius uses two points per statement, "start" and "mid"; one is
//! enough for our programs.)

use std::collections::{BTreeMap, BTreeSet};

use crate::borrowck::{Loan, LoanId, loans_killed_at};
use crate::dataflow::{Analysis, Direction, solve};
use crate::liveness::Liveness;
use crate::mir::*;
use crate::regions::OutlivesConstraint;

// ANCHOR: state
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PoloniusState {
    /// `origin_contains_loan_on_entry(o, l)`: origin `o` may hold a reference
    /// created by loan `l`.
    pub contains: BTreeSet<(RegionVid, LoanId)>,
    /// `subset(o1, o2)`: every loan in `o1` is also in `o2`.
    pub subset: BTreeSet<(RegionVid, RegionVid)>,
}
// ANCHOR_END: state

pub struct PoloniusLoans<'a> {
    body: &'a Body,
    loans: &'a [Loan],
    /// `subset_base`: the outlives constraints generated at each point. A
    /// constraint `'a: 'b` means that loans flow from `'a` into `'b`.
    subset_base: BTreeMap<Location, Vec<(RegionVid, RegionVid)>>,
    /// `origin_live_on_entry`.
    live_origins: BTreeMap<Location, BTreeSet<RegionVid>>,
}

/// The origins live on entry to each point: the regions in the types of the
/// live locals, the named regions (live everywhere), and the region of a
/// borrow created at that point.
pub fn live_origins(body: &Body) -> BTreeMap<Location, BTreeSet<RegionVid>> {
    let live_locals = solve(body, Liveness).states_before(body);
    let mut out = BTreeMap::new();
    for (loc, locals) in live_locals {
        let mut origins: BTreeSet<RegionVid> =
            body.universal_regions().into_iter().collect();
        for local in locals {
            origins.extend(body.decl(local).ty.regions());
        }
        if let Some(Statement {
            kind: StatementKind::Assign(_, Rvalue::Ref(k, _, _)),
            ..
        }) = body.blocks[loc.block.0].statements.get(loc.index)
        {
            origins.insert(*k);
        }
        out.insert(loc, origins);
    }
    out
}

// ANCHOR: transfer
impl PoloniusLoans<'_> {
    fn apply(&self, state: &mut PoloniusState, loc: Location) {
        let live = &self.live_origins[&loc];
        // Facts about dead origins are not carried into this point.
        state.contains.retain(|(o, _)| live.contains(o));
        state
            .subset
            .retain(|(a, b)| live.contains(a) && live.contains(b));
        // loan_issued_at and subset_base for this point.
        for (id, loan) in self.loans.iter().enumerate() {
            if loan.location == loc {
                state.contains.insert((loan.region, id));
            }
        }
        state
            .subset
            .extend(self.subset_base.get(&loc).into_iter().flatten().copied());
        // Close under transitivity and under "loans flow along subsets".
        loop {
            let mut new_subset = Vec::new();
            for &(a, b) in &state.subset {
                for &(c, d) in &state.subset {
                    if b == c && !state.subset.contains(&(a, d)) {
                        new_subset.push((a, d));
                    }
                }
            }
            let mut new_contains = Vec::new();
            for &(o, l) in &state.contains {
                for &(a, b) in &state.subset {
                    if a == o && !state.contains.contains(&(b, l)) {
                        new_contains.push((b, l));
                    }
                }
            }
            if new_subset.is_empty() && new_contains.is_empty() {
                break;
            }
            state.subset.extend(new_subset);
            state.contains.extend(new_contains);
        }
        // Killed loans do not flow to the successors.
        let killed = loans_killed_at(self.body, self.loans, loc);
        state.contains.retain(|(_, l)| !killed.contains(l));
    }
}
// ANCHOR_END: transfer

impl Analysis for PoloniusLoans<'_> {
    type Domain = PoloniusState;
    const DIRECTION: Direction = Direction::Forward;

    fn bottom(&self, _body: &Body) -> PoloniusState {
        PoloniusState::default()
    }

    fn boundary(&self, _body: &Body) -> PoloniusState {
        PoloniusState::default()
    }

    fn join(&self, state: &mut PoloniusState, other: &PoloniusState) -> bool {
        let before = (state.contains.len(), state.subset.len());
        state.contains.extend(other.contains.iter().copied());
        state.subset.extend(other.subset.iter().copied());
        before != (state.contains.len(), state.subset.len())
    }

    fn apply_statement(&self, state: &mut PoloniusState, _: &Statement, loc: Location) {
        self.apply(state, loc);
    }

    fn apply_terminator(
        &self,
        state: &mut PoloniusState,
        _: &Terminator,
        loc: Location,
    ) {
        self.apply(state, loc);
    }
}

/// The facts on entry to every point (before the point's own transfer).
pub fn facts(
    body: &Body,
    loans: &[Loan],
    constraints: &[OutlivesConstraint],
) -> (
    BTreeMap<Location, PoloniusState>,
    BTreeMap<Location, BTreeSet<RegionVid>>,
) {
    let mut subset_base: BTreeMap<Location, Vec<(RegionVid, RegionVid)>> =
        BTreeMap::new();
    for c in constraints {
        subset_base
            .entry(c.location)
            .or_default()
            .push((c.sup, c.sub));
    }
    let live = live_origins(body);
    let analysis = PoloniusLoans {
        body,
        loans,
        subset_base,
        live_origins: live.clone(),
    };
    (solve(body, analysis).states_before(body), live)
}

// ANCHOR: loan_live_at
/// `loan_live_at(L, P)`: some origin live at `P` contains `L` on entry to `P`.
pub fn live_loans(
    body: &Body,
    loans: &[Loan],
    constraints: &[OutlivesConstraint],
) -> BTreeMap<Location, BTreeSet<LoanId>> {
    let (states, live) = facts(body, loans, constraints);
    states
        .into_iter()
        .map(|(loc, state)| {
            let loans = state
                .contains
                .iter()
                .filter(|(o, _)| live[&loc].contains(o))
                .map(|&(_, l)| l)
                .collect();
            (loc, loans)
        })
        .collect()
}
// ANCHOR_END: loan_live_at
