//! Move analysis: which move paths may be uninitialized (or initialized) at
//! each program point, the E0382 check built on it, and the drop-elaboration
//! decision that uses both.
//!
//! A *move path* is a place without dereferences (`_2`, `(_3 as Some).0`):
//! the memory this function owns. rustc builds a tree of them (`MoveData`);
//! here a set of places is enough.

use std::collections::BTreeSet;

use crate::dataflow::{Analysis, Direction, solve};
use crate::diagnostics::Diagnostic;
use crate::mir::*;

pub type PlaceSet = BTreeSet<Place>;

/// Record that `place` (and everything inside it) is now uninitialized.
fn mark_uninit(state: &mut PlaceSet, place: &Place) {
    if place.has_deref() {
        return; // memory behind a reference is not owned by this function
    }
    state.retain(|q| !place.is_prefix_of(q));
    state.insert(place.clone());
}

/// Record that `place` (and everything inside it) is now initialized.
fn mark_init(state: &mut PlaceSet, place: &Place) {
    if !place.has_deref() {
        state.retain(|q| !place.is_prefix_of(q));
    }
}

fn moved_places(ops: &[&Operand]) -> Vec<Place> {
    ops.iter()
        .filter_map(|op| match op {
            Operand::Move(p) => Some(p.clone()),
            _ => None,
        })
        .collect()
}

// ANCHOR: maybe_uninit
/// Forward "may" analysis: a move path is in the set at a point if on *some*
/// path from the start of the function to that point it was never
/// initialized, or was moved out of, or its storage died.
pub struct MaybeUninit;

impl Analysis for MaybeUninit {
    type Domain = PlaceSet;
    const DIRECTION: Direction = Direction::Forward;

    fn bottom(&self, _body: &Body) -> PlaceSet {
        PlaceSet::new()
    }

    fn boundary(&self, body: &Body) -> PlaceSet {
        // On entry, everything except the arguments is uninitialized.
        (0..body.locals.len())
            .filter(|&i| i == 0 || i > body.arg_count)
            .map(|i| Place::from(Local(i)))
            .collect()
    }

    fn join(&self, state: &mut PlaceSet, other: &PlaceSet) -> bool {
        let before = state.len();
        state.extend(other.iter().cloned());
        state.len() != before
    }

    fn apply_statement(&self, state: &mut PlaceSet, stmt: &Statement, _: Location) {
        match &stmt.kind {
            StatementKind::Assign(dest, rv) => {
                for p in moved_places(&rv.operands()) {
                    mark_uninit(state, &p); // gen: moved out
                }
                mark_init(state, dest); // kill: (re)initialized
            }
            StatementKind::StorageLive(l) | StatementKind::StorageDead(l) => {
                mark_uninit(state, &Place::from(*l));
            }
            StatementKind::FakeRead(_) => {}
        }
    }

    fn apply_terminator(&self, state: &mut PlaceSet, term: &Terminator, _: Location) {
        match &term.kind {
            TerminatorKind::Call { args, dest, .. } => {
                let args: Vec<&Operand> = args.iter().collect();
                for p in moved_places(&args) {
                    mark_uninit(state, &p);
                }
                mark_init(state, dest);
            }
            TerminatorKind::Drop { place, .. } => mark_uninit(state, place),
            _ => {}
        }
    }
}
// ANCHOR_END: maybe_uninit

/// Forward "may" analysis: a move path is in the set if on some path it was
/// initialized and not moved out since. (The dual of `MaybeUninit`.)
pub struct MaybeInit;

impl Analysis for MaybeInit {
    type Domain = PlaceSet;
    const DIRECTION: Direction = Direction::Forward;

    fn bottom(&self, _body: &Body) -> PlaceSet {
        PlaceSet::new()
    }

    fn boundary(&self, body: &Body) -> PlaceSet {
        (1..=body.arg_count)
            .map(|i| Place::from(Local(i)))
            .collect()
    }

    fn join(&self, state: &mut PlaceSet, other: &PlaceSet) -> bool {
        let before = state.len();
        state.extend(other.iter().cloned());
        state.len() != before
    }

    fn apply_statement(&self, state: &mut PlaceSet, stmt: &Statement, _: Location) {
        match &stmt.kind {
            StatementKind::Assign(dest, rv) => {
                for p in moved_places(&rv.operands()) {
                    state.retain(|q| !p.is_prefix_of(q));
                }
                if !dest.has_deref() {
                    state.insert(dest.clone());
                }
            }
            StatementKind::StorageLive(l) | StatementKind::StorageDead(l) => {
                let p = Place::from(*l);
                state.retain(|q| !p.is_prefix_of(q));
            }
            StatementKind::FakeRead(_) => {}
        }
    }

    fn apply_terminator(&self, state: &mut PlaceSet, term: &Terminator, _: Location) {
        match &term.kind {
            TerminatorKind::Call { args, dest, .. } => {
                for a in args {
                    if let Operand::Move(p) = a {
                        state.retain(|q| !p.is_prefix_of(q));
                    }
                }
                if !dest.has_deref() {
                    state.insert(dest.clone());
                }
            }
            TerminatorKind::Drop { place, .. } => {
                state.retain(|q| !place.is_prefix_of(q))
            }
            _ => {}
        }
    }
}

/// Some part of `place` (or a place containing it) is in `state`.
fn overlaps(state: &PlaceSet, place: &Place) -> Option<Place> {
    let mp = place.move_path();
    // `mp` itself or a place containing it ...
    if let Some(q) = state.iter().find(|q| q.is_prefix_of(&mp)) {
        return Some(q.clone());
    }
    // ... or, if the whole of `mp` is used, a part of it.
    if !place.has_deref() {
        return state.iter().find(|q| mp.is_prefix_of(q)).cloned();
    }
    None
}

/// How a place is used: read (copied or moved) or borrowed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum UseKind {
    Use,
    Borrow,
}

/// The places that must be initialized for the statement at `loc` to run.
fn uses_at(body: &Body, loc: Location) -> Vec<(Place, UseKind)> {
    let block = &body.blocks[loc.block.0];
    let mut out = Vec::new();
    let operand = |op: &Operand, out: &mut Vec<(Place, UseKind)>| {
        if let Some(p) = op.place() {
            out.push((p.clone(), UseKind::Use));
        }
    };
    match block.statements.get(loc.index) {
        Some(stmt) => match &stmt.kind {
            StatementKind::Assign(dest, rv) => {
                match rv {
                    Rvalue::Ref(_, _, p) => out.push((p.clone(), UseKind::Borrow)),
                    Rvalue::Discriminant(p) => out.push((p.clone(), UseKind::Use)),
                    _ => rv
                        .operands()
                        .into_iter()
                        .for_each(|op| operand(op, &mut out)),
                }
                if dest.has_deref() {
                    // `*r = v` reads the reference `r`.
                    out.push((Place::from(dest.local), UseKind::Use));
                }
            }
            StatementKind::FakeRead(l) => out.push((Place::from(*l), UseKind::Use)),
            _ => {}
        },
        None => match &block.terminator.kind {
            TerminatorKind::Call { args, .. } => {
                args.iter().for_each(|op| operand(op, &mut out));
            }
            TerminatorKind::SwitchInt { discr, .. } => operand(discr, &mut out),
            _ => {}
        },
    }
    out
}

/// Does the statement at `loc` move out of a path overlapping `mp`?
fn moves_out(body: &Body, loc: Location, mp: &Place) -> bool {
    let block = &body.blocks[loc.block.0];
    let ops: Vec<&Operand> = match block.statements.get(loc.index) {
        Some(Statement {
            kind: StatementKind::Assign(_, rv),
            ..
        }) => rv.operands(),
        Some(_) => vec![],
        None => match &block.terminator.kind {
            TerminatorKind::Call { args, .. } => args.iter().collect(),
            _ => vec![],
        },
    };
    moved_places(&ops)
        .iter()
        .any(|p| p.is_prefix_of(mp) || mp.is_prefix_of(p))
}

/// Does the statement at `loc` (re)initialize `mp` or a place containing it?
fn initializes(body: &Body, loc: Location, mp: &Place) -> bool {
    let block = &body.blocks[loc.block.0];
    match block.statements.get(loc.index) {
        Some(stmt) => match &stmt.kind {
            StatementKind::Assign(dest, _) => {
                !dest.has_deref() && dest.is_prefix_of(mp)
            }
            StatementKind::StorageLive(l) => *l == mp.local,
            _ => false,
        },
        None => match &block.terminator.kind {
            TerminatorKind::Call { dest, .. } => dest.is_prefix_of(mp),
            _ => false,
        },
    }
}

/// Walk backwards from a use to the moves that may have emptied the place.
fn move_sites(body: &Body, use_loc: Location, mp: &Place) -> Vec<Location> {
    let mut sites = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut work = body.predecessor_locations(use_loc);
    while let Some(loc) = work.pop() {
        if !seen.insert(loc) {
            continue;
        }
        if moves_out(body, loc, mp) {
            sites.insert(loc);
        } else if !initializes(body, loc, mp) {
            work.extend(body.predecessor_locations(loc));
        }
    }
    sites.into_iter().collect()
}

// ANCHOR: check_moves
/// Report every use of a place that may be uninitialized: E0382 if some
/// path moved out of it, E0381 if it was never initialized.
pub fn check_moves(body: &Body) -> Vec<Diagnostic> {
    let uninit = solve(body, MaybeUninit).states_before(body);
    let mut diags = Vec::new();
    for loc in body.locations() {
        for (place, kind) in uses_at(body, loc) {
            if let Some(missing) = overlaps(&uninit[&loc], &place) {
                diags.push(report_uninit_use(body, loc, &place, kind, &missing));
            }
        }
    }
    diags
}
// ANCHOR_END: check_moves

fn report_uninit_use(
    body: &Body,
    loc: Location,
    place: &Place,
    kind: UseKind,
    missing: &Place,
) -> Diagnostic {
    let mp = place.move_path();
    let name = body.describe_place(&mp);
    let decl_span = body.decl(mp.local).span;
    let sites = move_sites(body, loc, &mp);
    if sites.is_empty() {
        let mut d = Diagnostic::new(
            "E0381",
            format!("used binding `{name}` isn't initialized"),
            loc,
        );
        d.secondary(decl_span, "binding declared here but left uninitialized");
        d.primary(
            body.span_at(loc),
            format!("`{name}` used here but it isn't initialized"),
        );
        return d;
    }
    let partial = *missing != mp && mp.is_prefix_of(missing);
    let (verb, noun) = match kind {
        UseKind::Use => ("use", "used"),
        UseKind::Borrow => ("borrow", "borrowed"),
    };
    let what = if partial { "partially moved" } else { "moved" };
    let mut d =
        Diagnostic::new("E0382", format!("{verb} of {what} value: `{name}`"), loc);
    let moved = if partial { missing } else { &mp };
    let ty = body.fmt_ty(&body.place_ty(moved));
    let (kind_of_move, moved_name) = if partial {
        ("partial move", body.describe_place(missing))
    } else {
        ("move", name.clone())
    };
    d.secondary(
        decl_span,
        format!(
            "{kind_of_move} occurs because `{moved_name}` has type `{ty}`, \
             which does not implement the `Copy` trait"
        ),
    );
    for site in sites {
        let text = if site == loc {
            "value moved here, in previous iteration of loop"
        } else if partial {
            "value partially moved here"
        } else {
            "value moved here"
        };
        d.secondary(body.span_at(site), text);
    }
    let after = if partial {
        "after partial move"
    } else {
        "after move"
    };
    d.primary(body.span_at(loc), format!("value {noun} here {after}"));
    d
}

// ANCHOR: drop_style
/// What drop elaboration does with a `drop(place)` terminator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DropStyle {
    /// The place is definitely uninitialized here: the drop is deleted.
    Dead,
    /// The place is definitely initialized: drop it unconditionally.
    Static,
    /// Initialized on some paths only: drop it if a run-time flag says so.
    Conditional,
    /// Partly moved out: drop the fields that are still there.
    Open,
}

/// Classify every `drop` terminator, as rustc's drop elaboration does after
/// borrow checking.
pub fn drop_styles(body: &Body) -> Vec<(Location, Place, DropStyle)> {
    let init = solve(body, MaybeInit).states_before(body);
    let uninit = solve(body, MaybeUninit).states_before(body);
    let mut out = Vec::new();
    for bb in body.block_ids() {
        if let TerminatorKind::Drop { place, .. } = &body.blocks[bb.0].terminator.kind {
            let loc = body.terminator_location(bb);
            let maybe_init = overlaps(&init[&loc], place).is_some();
            let style = match overlaps(&uninit[&loc], place) {
                _ if !maybe_init => DropStyle::Dead,
                None => DropStyle::Static,
                Some(q) if q.is_prefix_of(place) => DropStyle::Conditional,
                Some(_) => DropStyle::Open,
            };
            out.push((loc, place.clone(), style));
        }
    }
    out
}
// ANCHOR_END: drop_style

#[cfg(test)]
mod tests {
    use super::*;
    use crate::build::{Builder, mv};

    const SOURCE: &str = "\
fn send_all(msg: String) {
    loop {
        consume(msg);
    }
}

fn split(order: Order) -> String {
    let name = order.customer;
    check(order)
}
";

    /// A move inside a loop: the back edge carries "maybe moved" around.
    #[test]
    fn move_in_loop() {
        let mut b = Builder::new("send_all", "loop.rs", SOURCE);
        b.ret(scalar("()"));
        let msg = b.arg("msg", owned("String"), b.span("fn send_all", "msg"));
        let unit = b.temp(scalar("()"));
        let [bb0, bb1] = [(); 2].map(|_| b.block());
        b.goto(bb0, bb1);
        let call = b.span("consume", "consume(msg)");
        let callee = b.span("consume", "consume");
        b.call(bb1, unit, "consume", vec![mv(msg)], bb1)
            .spans(call, callee);
        let body = b.finish();
        let diags = check_moves(&body);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].message, "use of moved value: `msg`");
        let text = diags[0].render(&body);
        assert!(text.contains("value moved here, in previous iteration of loop"));
    }

    /// Moving a field leaves the struct partially moved.
    #[test]
    fn partial_move() {
        let mut b = Builder::new("split", "split.rs", SOURCE);
        b.ret(owned("String"));
        let order_ty = adt("Order", vec![scalar("u32"), owned("String")]);
        let order = b.arg("order", order_ty, b.span("fn split", "order"));
        let name = b.var("name", owned("String"), b.span("let name", "name"));
        let [bb0, bb1] = [(); 2].map(|_| b.block());
        let field = Place::from(order).field(1);
        let span = b.span("let name", "order.customer");
        b.assign(bb0, name, Rvalue::Use(mv(field)), Some(span));
        let call = b.span("check(order)", "check(order)");
        let callee = b.span("check(order)", "check");
        b.call(bb0, Local(0), "check", vec![mv(order)], bb1)
            .spans(call, callee);
        let body = b.finish();
        let diags = check_moves(&body);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].message, "use of partially moved value: `order`");
    }

    #[test]
    fn maybe_uninit_reaches_the_join() {
        let body = crate::programs::conditional_move();
        let uninit = solve(&body, MaybeUninit).states_before(&body);
        let join = Location {
            block: BlockId(5),
            index: 0,
        };
        assert!(uninit[&join].contains(&Place::from(Local(2))));
        let init = solve(&body, MaybeInit).states_before(&body);
        assert!(init[&join].contains(&Place::from(Local(2))));
    }
}
