//! Loans, the loans in scope at each point, and the conflict check that
//! reports E0499, E0502, E0503, E0505, E0506 and E0597. Also the four
//! checkers that Chapter 29 compares on the same programs.

use std::collections::{BTreeMap, BTreeSet};

use crate::dataflow::{Analysis, Direction, solve};
use crate::diagnostics::Diagnostic;
use crate::mir::*;
use crate::moves::check_moves;
use crate::polonius;
use crate::regions::{self, OutlivesConstraint, RegionMode, RegionValues};

pub type LoanId = usize;

// ANCHOR: loan
/// A loan: the result of one borrow expression `&'k p` / `&'k mut p`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Loan {
    pub kind: BorrowKind,
    /// The borrowed place.
    pub place: Place,
    /// The loan's region `'k`.
    pub region: RegionVid,
    /// Where the borrow happens (for a two-phase borrow: its reservation).
    pub location: Location,
    /// The local that receives the reference.
    pub temp: Local,
    /// For a two-phase borrow: the first use of `temp`, where it activates.
    pub activation: Option<Location>,
    pub span: Option<Span>,
}
// ANCHOR_END: loan

/// Does the statement or terminator at `loc` read `local` (directly, or by
/// dereferencing it)?
pub fn reads_local(body: &Body, loc: Location, local: Local) -> bool {
    let block = &body.blocks[loc.block.0];
    match block.statements.get(loc.index) {
        Some(stmt) => match &stmt.kind {
            StatementKind::Assign(dest, rv) => {
                rv.places().iter().any(|p| p.local == local)
                    || (dest.has_deref() && dest.local == local)
            }
            _ => false,
        },
        None => match &block.terminator.kind {
            TerminatorKind::Call { args, .. } => args
                .iter()
                .filter_map(Operand::place)
                .any(|p| p.local == local),
            TerminatorKind::SwitchInt { discr, .. } => {
                discr.place().is_some_and(|p| p.local == local)
            }
            TerminatorKind::Drop { place, .. } => place.local == local,
            TerminatorKind::Return => local == Local(0),
            TerminatorKind::Goto(_) => false,
        },
    }
}

/// The first point after `from` that reads `local`.
fn first_use(body: &Body, from: Location, local: Local) -> Option<Location> {
    let mut seen = BTreeSet::new();
    let mut work: Vec<Location> = body.successor_locations(from);
    while !work.is_empty() {
        let loc = work.remove(0);
        if !seen.insert(loc) {
            continue;
        }
        if reads_local(body, loc, local) {
            return Some(loc);
        }
        work.extend(body.successor_locations(loc));
    }
    None
}

/// Every borrow expression of the body, in program order. Without two-phase
/// borrows, a two-phase `&mut` is an ordinary one.
pub fn collect_loans(body: &Body, two_phase: bool) -> Vec<Loan> {
    let mut loans = Vec::new();
    for loc in body.locations() {
        if let Some(Statement {
            kind: StatementKind::Assign(dest, Rvalue::Ref(region, kind, place)),
            span,
        }) = body.blocks[loc.block.0].statements.get(loc.index)
        {
            let kind = match kind {
                BorrowKind::TwoPhaseMut if !two_phase => BorrowKind::Mut,
                k => *k,
            };
            let activation = match kind {
                BorrowKind::TwoPhaseMut => first_use(body, loc, dest.local),
                _ => None,
            };
            loans.push(Loan {
                kind,
                place: place.clone(),
                region: *region,
                location: loc,
                temp: dest.local,
                activation,
                span: *span,
            });
        }
    }
    loans
}

/// The loans that stop being reachable at `loc`: overwriting a local (or
/// freeing its storage) kills the loans of places based on it.
pub fn loans_killed_at(body: &Body, loans: &[Loan], loc: Location) -> Vec<LoanId> {
    let block = &body.blocks[loc.block.0];
    let overwritten: Option<Local> = match block.statements.get(loc.index) {
        Some(stmt) => match &stmt.kind {
            StatementKind::Assign(dest, _) if dest.projection.is_empty() => {
                Some(dest.local)
            }
            StatementKind::StorageDead(l) => Some(*l),
            _ => None,
        },
        None => match &block.terminator.kind {
            TerminatorKind::Call { dest, .. } if dest.projection.is_empty() => {
                Some(dest.local)
            }
            _ => None,
        },
    };
    match overwritten {
        Some(local) => (0..loans.len())
            .filter(|&id| loans[id].place.local == local)
            .collect(),
        None => Vec::new(),
    }
}

// ANCHOR: borrows_in_scope
/// Forward analysis: the loans in scope at each point. A loan enters scope
/// where it is created and leaves it at the first point outside its region,
/// or when the borrowed local is overwritten or dies.
pub struct BorrowsInScope<'a> {
    pub body: &'a Body,
    pub loans: &'a [Loan],
    pub values: &'a RegionValues,
}

// ANCHOR: borrows_apply
impl BorrowsInScope<'_> {
    fn apply(&self, state: &mut BTreeSet<LoanId>, loc: Location) {
        // Leaving the region: the loan can no longer be used from here on.
        state.retain(|&id| self.values.contains(self.loans[id].region, loc));
        for id in loans_killed_at(self.body, self.loans, loc) {
            state.remove(&id);
        }
        for (id, loan) in self.loans.iter().enumerate() {
            if loan.location == loc {
                state.insert(id);
            }
        }
    }
}
// ANCHOR_END: borrows_apply

impl Analysis for BorrowsInScope<'_> {
    type Domain = BTreeSet<LoanId>;
    const DIRECTION: Direction = Direction::Forward;

    fn bottom(&self, _body: &Body) -> Self::Domain {
        BTreeSet::new()
    }

    fn boundary(&self, _body: &Body) -> Self::Domain {
        BTreeSet::new()
    }

    fn join(&self, state: &mut Self::Domain, other: &Self::Domain) -> bool {
        let before = state.len();
        state.extend(other.iter().copied());
        state.len() != before
    }

    fn apply_statement(&self, state: &mut Self::Domain, _: &Statement, loc: Location) {
        self.apply(state, loc);
    }

    fn apply_terminator(
        &self,
        state: &mut Self::Domain,
        _: &Terminator,
        loc: Location,
    ) {
        self.apply(state, loc);
    }
}
// ANCHOR_END: borrows_in_scope

/// The loans in scope on entry to every point (after leaving the regions
/// that do not contain the point).
pub fn loans_in_scope(
    body: &Body,
    loans: &[Loan],
    values: &RegionValues,
) -> BTreeMap<Location, BTreeSet<LoanId>> {
    let analysis = BorrowsInScope {
        body,
        loans,
        values,
    };
    let mut states = solve(body, analysis).states_before(body);
    for (loc, state) in states.iter_mut() {
        state.retain(|&id| values.contains(loans[id].region, *loc));
    }
    states
}

// ANCHOR: access
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Depth {
    /// Touches the place itself, not what it points to (assignment, `StorageDead`).
    Shallow,
    /// Touches the place and everything reachable from it.
    Deep,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AccessKind {
    /// `copy p`, `discriminant(p)`.
    ReadCopy,
    /// `&p`.
    ReadBorrow,
    /// `p = ...`.
    Mutate,
    /// `move p`.
    Move,
    /// `&mut p`.
    MutBorrow,
    /// A two-phase `&mut p` at its reservation: acts like a shared borrow.
    Reservation,
    /// A two-phase `&mut p` at its activation: now acts like `&mut p`.
    Activation(LoanId),
    /// `StorageDead(p)` or `drop(p)`.
    StorageDeadOrDrop,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Access {
    pub place: Place,
    pub depth: Depth,
    pub kind: AccessKind,
    pub span: Option<Span>,
}
// ANCHOR_END: access

/// The accesses performed at `loc`, in evaluation order.
pub fn accesses_at(body: &Body, loans: &[Loan], loc: Location) -> Vec<Access> {
    let span = body.span_at(loc);
    let mut out = Vec::new();
    let mut push = |place: &Place, depth, kind| {
        out.push(Access {
            place: place.clone(),
            depth,
            kind,
            span,
        })
    };
    // Two-phase borrows activated here come first.
    for (id, loan) in loans.iter().enumerate() {
        if loan.activation == Some(loc) {
            push(&loan.place, Depth::Deep, AccessKind::Activation(id));
        }
    }
    let operand =
        |op: &Operand, push: &mut dyn FnMut(&Place, Depth, AccessKind)| match op {
            Operand::Copy(p) => push(p, Depth::Deep, AccessKind::ReadCopy),
            Operand::Move(p) => push(p, Depth::Deep, AccessKind::Move),
            Operand::Const(_) => {}
        };
    let block = &body.blocks[loc.block.0];
    match block.statements.get(loc.index) {
        Some(stmt) => match &stmt.kind {
            StatementKind::Assign(dest, rv) => {
                match rv {
                    Rvalue::Ref(_, _, p) => {
                        // Use the kind recorded in the loan (two-phase may be off).
                        let kind = loans
                            .iter()
                            .find(|l| l.location == loc)
                            .map(|l| l.kind)
                            .expect("every borrow has a loan");
                        let access = match kind {
                            BorrowKind::Shared => AccessKind::ReadBorrow,
                            BorrowKind::Mut => AccessKind::MutBorrow,
                            BorrowKind::TwoPhaseMut => AccessKind::Reservation,
                        };
                        push(p, Depth::Deep, access);
                    }
                    Rvalue::Discriminant(p) => {
                        push(p, Depth::Shallow, AccessKind::ReadCopy)
                    }
                    _ => rv
                        .operands()
                        .into_iter()
                        .for_each(|op| operand(op, &mut push)),
                }
                push(dest, Depth::Shallow, AccessKind::Mutate);
            }
            StatementKind::StorageDead(l) => {
                push(
                    &Place::from(*l),
                    Depth::Shallow,
                    AccessKind::StorageDeadOrDrop,
                );
            }
            StatementKind::StorageLive(_) | StatementKind::FakeRead(_) => {}
        },
        None => match &block.terminator.kind {
            TerminatorKind::Call { args, dest, .. } => {
                args.iter().for_each(|op| operand(op, &mut push));
                push(dest, Depth::Shallow, AccessKind::Mutate);
            }
            TerminatorKind::SwitchInt { discr, .. } => operand(discr, &mut push),
            TerminatorKind::Drop { place, .. } => {
                push(place, Depth::Deep, AccessKind::StorageDeadOrDrop);
            }
            TerminatorKind::Goto(_) | TerminatorKind::Return => {}
        },
    }
    out
}

// ANCHOR: places_conflict
/// Can an access to `access` (at `depth`) touch memory of the borrowed place?
pub fn places_conflict(borrowed: &Place, access: &Place, depth: Depth) -> bool {
    if borrowed.local != access.local {
        return false;
    }
    for (b, a) in borrowed.projection.iter().zip(&access.projection) {
        if b != a {
            return false; // different fields or variants: disjoint memory
        }
    }
    if borrowed.projection.len() <= access.projection.len() {
        return true; // the access is inside the borrowed place
    }
    // The access is to a prefix of the borrowed place, e.g. `x` vs `(*x).0`.
    // A shallow access does not go through a dereference.
    let rest = &borrowed.projection[access.projection.len()..];
    depth == Depth::Deep || !rest.contains(&ProjectionElem::Deref)
}
// ANCHOR_END: places_conflict

// ANCHOR: conflict_rules
/// The error code if `access` conflicts with a loan of kind `loan`, given
/// whether the loan (if two-phase) has been activated.
pub fn conflict(
    access: AccessKind,
    loan: BorrowKind,
    loan_active: bool,
) -> Option<&'static str> {
    use AccessKind::*;
    match (access, loan) {
        // Reading is compatible with shared loans, and so is a reservation.
        (ReadCopy | ReadBorrow | Reservation, BorrowKind::Shared) => None,
        // Reading is compatible with a two-phase loan that is only reserved.
        (ReadCopy | ReadBorrow, _) if !loan_active => None,
        (ReadCopy, _) => Some("E0503"),
        (ReadBorrow, _) => Some("E0502"),
        (MutBorrow | Activation(_), BorrowKind::Shared) => Some("E0502"),
        (MutBorrow | Reservation | Activation(_), _) => Some("E0499"),
        (Mutate, _) => Some("E0506"),
        (Move, _) => Some("E0505"),
        (StorageDeadOrDrop, _) => Some("E0597"),
    }
}
// ANCHOR_END: conflict_rules

// ANCHOR: checker
/// The four borrow checkers compared in Chapter 29.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Checker {
    /// Rust 2015: a loan lasts while the reference is in scope; no
    /// two-phase borrows.
    Lexical,
    /// Non-lexical lifetimes, but every `&mut` takes effect immediately.
    NllWithoutTwoPhase,
    /// Today's borrow checker: NLL with two-phase borrows.
    Nll,
    /// NLL's checks with location-sensitive loan liveness, as in Polonius.
    Polonius,
}
// ANCHOR_END: checker

impl Checker {
    pub const ALL: [Checker; 4] = [
        Checker::Lexical,
        Checker::NllWithoutTwoPhase,
        Checker::Nll,
        Checker::Polonius,
    ];

    pub fn name(self) -> &'static str {
        match self {
            Checker::Lexical => "lexical",
            Checker::NllWithoutTwoPhase => "NLL, no 2PB",
            Checker::Nll => "NLL",
            Checker::Polonius => "Polonius",
        }
    }

    pub fn two_phase(self) -> bool {
        matches!(self, Checker::Nll | Checker::Polonius)
    }
}

/// Everything the conflict check needs to know about the loans of a body.
pub struct LoanFacts {
    pub loans: Vec<Loan>,
    pub constraints: Vec<OutlivesConstraint>,
    /// The loans live (in scope) on entry to each point.
    pub live: BTreeMap<Location, BTreeSet<LoanId>>,
    /// The region values (lexical or NLL). The Polonius checker does not
    /// use them to decide anything, only to explain its errors.
    pub values: RegionValues,
}

pub fn loan_facts(body: &Body, checker: Checker) -> LoanFacts {
    let loans = collect_loans(body, checker.two_phase());
    let constraints = regions::outlives_constraints(body);
    let mode = match checker {
        Checker::Lexical => RegionMode::Lexical,
        _ => RegionMode::Nll,
    };
    let (values, _) =
        regions::propagate(regions::initial_values(body, mode), &constraints);
    let live = match checker {
        Checker::Polonius => polonius::live_loans(body, &loans, &constraints),
        _ => loans_in_scope(body, &loans, &values),
    };
    LoanFacts {
        loans,
        constraints,
        live,
        values,
    }
}

/// The points after a two-phase loan's reservation and before its activation.
fn reserved_points(body: &Body, loan: &Loan) -> BTreeSet<Location> {
    let mut seen = BTreeSet::new();
    if loan.kind != BorrowKind::TwoPhaseMut {
        return seen;
    }
    let mut work = body.successor_locations(loan.location);
    while let Some(loc) = work.pop() {
        if Some(loc) == loan.activation || !seen.insert(loc) {
            continue;
        }
        work.extend(body.successor_locations(loc));
    }
    seen
}

// ANCHOR: check_loans
/// Check every access against every loan live at its point.
pub fn check_loans(body: &Body, checker: Checker) -> Vec<Diagnostic> {
    let facts = loan_facts(body, checker);
    let reserved: Vec<BTreeSet<Location>> = facts
        .loans
        .iter()
        .map(|l| reserved_points(body, l))
        .collect();
    let mut diags = Vec::new();
    let mut reported: BTreeSet<(Place, Option<Span>)> = BTreeSet::new();
    let mut reservation_errors: BTreeSet<Place> = BTreeSet::new();
    for loc in body.locations() {
        for access in accesses_at(body, &facts.loans, loc) {
            if let AccessKind::Activation(_) = access.kind {
                // rustc reports a bad reservation once, not again at activation.
                if reservation_errors.contains(&access.place) {
                    continue;
                }
            }
            if reported.contains(&(access.place.clone(), access.span)) {
                continue;
            }
            for &id in &facts.live[&loc] {
                let loan = &facts.loans[id];
                if access.kind == AccessKind::Activation(id)
                    || !places_conflict(&loan.place, &access.place, access.depth)
                {
                    continue;
                }
                let active = !reserved[id].contains(&loc);
                if let Some(code) = conflict(access.kind, loan.kind, active) {
                    diags.push(report_conflict(
                        body, &facts, checker, &access, loc, id, code,
                    ));
                    reported.insert((access.place.clone(), access.span));
                    if access.kind == AccessKind::Reservation {
                        reservation_errors.insert(access.place.clone());
                    }
                    break;
                }
            }
        }
    }
    diags
}
// ANCHOR_END: check_loans

/// Move check plus loan check: all the errors `checker` reports for `body`.
pub fn check(body: &Body, checker: Checker) -> Vec<Diagnostic> {
    let mut diags = check_moves(body);
    diags.extend(check_loans(body, checker));
    diags.sort_by_key(|d| d.location);
    diags
}

fn report_conflict(
    body: &Body,
    facts: &LoanFacts,
    checker: Checker,
    access: &Access,
    loc: Location,
    id: LoanId,
    code: &'static str,
) -> Diagnostic {
    let loan = &facts.loans[id];
    let place = body.describe_place(&access.place);
    let borrowed = body.describe_place(&loan.place);
    let shared = loan.kind == BorrowKind::Shared;
    let (message, loan_label, access_label, prefix) = match code {
        "E0499" => (
            format!("cannot borrow `{place}` as mutable more than once at a time"),
            "first mutable borrow occurs here".to_string(),
            "second mutable borrow occurs here".to_string(),
            "first ",
        ),
        "E0502" if shared => (
            format!(
                "cannot borrow `{place}` as mutable because it is also borrowed as immutable"
            ),
            "immutable borrow occurs here".to_string(),
            "mutable borrow occurs here".to_string(),
            "immutable ",
        ),
        "E0502" => (
            format!(
                "cannot borrow `{place}` as immutable because it is also borrowed as mutable"
            ),
            "mutable borrow occurs here".to_string(),
            "immutable borrow occurs here".to_string(),
            "mutable ",
        ),
        "E0503" => (
            format!("cannot use `{place}` because it was mutably borrowed"),
            format!("`{borrowed}` is borrowed here"),
            format!("use of borrowed `{borrowed}`"),
            "",
        ),
        "E0505" => (
            format!("cannot move out of `{place}` because it is borrowed"),
            format!("borrow of `{borrowed}` occurs here"),
            format!("move out of `{place}` occurs here"),
            "",
        ),
        "E0506" => (
            format!("cannot assign to `{place}` because it is borrowed"),
            format!("`{borrowed}` is borrowed here"),
            format!("`{place}` is assigned to here but it was already borrowed"),
            "",
        ),
        _ => (
            format!("`{place}` does not live long enough"),
            "borrowed value does not live long enough".to_string(),
            format!("`{place}` dropped here while still borrowed"),
            "",
        ),
    };
    let mut d = Diagnostic::new(code, message, loc);
    if code == "E0505" {
        let name = body.describe_place(&Place::from(loan.place.local));
        d.secondary(
            body.decl(loan.place.local).span,
            format!("binding `{name}` declared here"),
        );
    }
    if code == "E0597" {
        d.primary(loan.span, loan_label);
        d.secondary(access.span, access_label);
    } else {
        d.secondary(loan.span, loan_label);
        d.primary(access.span, access_label);
    }
    explain(body, facts, checker, id, loc, prefix, &mut d);
    d
}

/// The locals whose type mentions a region that the loan's region must
/// contain: the references that may carry the loan.
fn carriers(body: &Body, facts: &LoanFacts, id: LoanId) -> BTreeSet<Local> {
    let reach = regions::reachable(&facts.constraints, facts.loans[id].region);
    (0..body.locals.len())
        .map(Local)
        .filter(|l| body.decl(*l).ty.regions().iter().any(|r| reach.contains(r)))
        .collect()
}

// ANCHOR: explain
/// Say why the loan is still live at the error point, as rustc does.
fn explain(
    body: &Body,
    facts: &LoanFacts,
    checker: Checker,
    id: LoanId,
    error: Location,
    prefix: &str,
    d: &mut Diagnostic,
) {
    let loan = &facts.loans[id];
    let reach = regions::reachable(&facts.constraints, loan.region);
    let carriers = carriers(body, facts, id);
    // 1. The loan flows into a named region: the caller needs it.
    if let Some(r) = reach.iter().copied().find(|r| body.is_universal(*r)) {
        let name = body.region_name(r);
        d.secondary(
            body.regions[r.0].span,
            format!("lifetime `{name}` defined here"),
        );
        let returned = body.locations().into_iter().find(|&loc| {
            matches!(
                body.blocks[loc.block.0].statements.get(loc.index),
                Some(Statement {
                    kind: StatementKind::Assign(dest, Rvalue::Use(Operand::Move(p) | Operand::Copy(p))),
                    ..
                }) if dest.local == Local(0) && carriers.contains(&p.local)
            )
        });
        if let Some(loc) = returned {
            let borrowed = body.describe_place(&loan.place);
            d.secondary(
                body.span_at(loc),
                format!("returning this value requires that `{borrowed}` is borrowed for `{name}`"),
            );
        }
        return;
    }
    // 2. Walk forward from the error, inside the loan's region, to the
    // reason the region extends that far.
    let mut seen = BTreeSet::new();
    let mut work = body.successor_locations(error);
    while !work.is_empty() {
        let loc = work.remove(0);
        if !seen.insert(loc) || !facts.values.contains(loan.region, loc) {
            continue;
        }
        let stmt = body.blocks[loc.block.0].statements.get(loc.index);
        if checker == Checker::Lexical {
            // The lexical checker: the loan ends where the reference's scope ends.
            if let Some(Statement {
                kind: StatementKind::StorageDead(l),
                span: Some(span),
            }) = stmt
            {
                if carriers.contains(l) {
                    d.secondary(Some(*span), format!("{prefix}borrow ends here"));
                    return;
                }
            }
        } else if carriers.iter().any(|&c| reads_local(body, loc, c)) {
            let term = &body.blocks[loc.block.0].terminator;
            if stmt.is_none() && matches!(term.kind, TerminatorKind::Call { .. }) {
                d.secondary(
                    term.callee_span,
                    format!("{prefix}borrow later used by call"),
                );
            } else {
                d.secondary(
                    body.span_at(loc),
                    format!("{prefix}borrow later used here"),
                );
            }
            return;
        }
        work.extend(body.successor_locations(loc));
    }
}
// ANCHOR_END: explain

#[cfg(test)]
mod tests {
    use super::*;

    fn place(local: usize, projection: Vec<ProjectionElem>) -> Place {
        Place {
            local: Local(local),
            projection,
        }
    }

    #[test]
    fn conflicting_places() {
        use ProjectionElem::{Deref, Field};
        let x = place(1, vec![]);
        let x0 = place(1, vec![Field(0)]);
        let x1 = place(1, vec![Field(1)]);
        let star_x = place(1, vec![Deref]);
        // A field and the whole struct overlap; two fields do not.
        assert!(places_conflict(&x0, &x, Depth::Deep));
        assert!(places_conflict(&x, &x0, Depth::Deep));
        assert!(!places_conflict(&x0, &x1, Depth::Deep));
        // Overwriting a reference does not touch what it points to...
        assert!(!places_conflict(&star_x, &x, Depth::Shallow));
        // ...but moving it (a deep access) does.
        assert!(places_conflict(&star_x, &x, Depth::Deep));
        assert!(!places_conflict(&x, &place(2, vec![]), Depth::Deep));
    }

    #[test]
    fn conflict_table() {
        use AccessKind::*;
        use BorrowKind::{Mut, Shared, TwoPhaseMut};
        assert_eq!(conflict(ReadBorrow, Shared, true), None);
        assert_eq!(conflict(Reservation, Shared, true), None);
        assert_eq!(conflict(ReadBorrow, TwoPhaseMut, false), None);
        assert_eq!(conflict(ReadBorrow, TwoPhaseMut, true), Some("E0502"));
        assert_eq!(conflict(ReadCopy, Mut, true), Some("E0503"));
        assert_eq!(conflict(MutBorrow, Shared, true), Some("E0502"));
        assert_eq!(conflict(Reservation, TwoPhaseMut, false), Some("E0499"));
        assert_eq!(conflict(Mutate, Shared, true), Some("E0506"));
        assert_eq!(conflict(Move, Shared, true), Some("E0505"));
        assert_eq!(conflict(StorageDeadOrDrop, Shared, true), Some("E0597"));
    }
}
