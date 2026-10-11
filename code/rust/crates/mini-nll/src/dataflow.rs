//! A generic dataflow framework: an analysis supplies a lattice of facts and a
//! transfer function per statement; the framework finds the fixpoint with a
//! worklist.
//!
//! This is the shape of rustc's own framework (`rustc_mir_dataflow`), much
//! simplified: states are stored per basic block and recomputed per statement
//! on demand.

use std::collections::{BTreeMap, VecDeque};
use std::fmt::Debug;

use crate::mir::{BlockId, Body, Location, Statement, Terminator};

// ANCHOR: analysis
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Direction {
    /// Facts flow along the edges of the CFG (initialization, loans).
    Forward,
    /// Facts flow against the edges (liveness: "used later").
    Backward,
}

/// A dataflow analysis. `Domain` must be a join-semilattice with `bottom` as
/// its least element, and the two `apply_*` functions must be monotone; then
/// the worklist algorithm terminates (if the lattice has finite height) and
/// computes the least solution of the dataflow equations.
pub trait Analysis {
    type Domain: Clone + PartialEq + Debug;
    const DIRECTION: Direction;

    /// The least element: "no facts yet".
    fn bottom(&self, body: &Body) -> Self::Domain;

    /// The facts at the boundary: on entry to `bb0` for a forward analysis,
    /// at every `return` for a backward one.
    fn boundary(&self, body: &Body) -> Self::Domain;

    /// Join `other` into `state`; return `true` if `state` grew.
    fn join(&self, state: &mut Self::Domain, other: &Self::Domain) -> bool;

    /// The effect of a statement (applied "backwards" for a backward analysis).
    fn apply_statement(
        &self,
        state: &mut Self::Domain,
        stmt: &Statement,
        loc: Location,
    );

    /// The effect of a terminator.
    fn apply_terminator(
        &self,
        state: &mut Self::Domain,
        term: &Terminator,
        loc: Location,
    );
}
// ANCHOR_END: analysis

/// The fixpoint: one state per basic block, at the block's entry in the
/// direction of the analysis (forward: before the first statement;
/// backward: after the terminator).
pub struct Results<A: Analysis> {
    pub analysis: A,
    pub block_states: Vec<A::Domain>,
    /// How many times a block was (re)processed before the fixpoint.
    pub block_visits: usize,
}

// ANCHOR: solve
/// Iterate to the fixpoint with a worklist of basic blocks.
pub fn solve<A: Analysis>(body: &Body, analysis: A) -> Results<A> {
    let n = body.blocks.len();
    let preds = body.predecessors();
    let mut states = vec![analysis.bottom(body); n];
    let mut worklist: VecDeque<usize> = (0..n).collect();
    match A::DIRECTION {
        Direction::Forward => states[0] = analysis.boundary(body),
        Direction::Backward => {
            for bb in body.block_ids() {
                if body.successors(bb).is_empty() {
                    states[bb.0] = analysis.boundary(body);
                }
            }
            worklist = (0..n).rev().collect();
        }
    }
    let mut queued = vec![true; n];
    let mut block_visits = 0;

    while let Some(bb) = worklist.pop_front() {
        queued[bb] = false;
        block_visits += 1;
        // Push the state through the block...
        let mut state = states[bb].clone();
        apply_block(body, &analysis, bb, &mut state, |_, _| {});
        // ...and join it into the neighbors that come next in our direction.
        let next: Vec<usize> = match A::DIRECTION {
            Direction::Forward => body.successors(BlockId(bb)),
            Direction::Backward => preds[bb].clone(),
        }
        .into_iter()
        .map(|b| b.0)
        .collect();
        for succ in next {
            if analysis.join(&mut states[succ], &state) && !queued[succ] {
                queued[succ] = true;
                worklist.push_back(succ);
            }
        }
    }
    Results {
        analysis,
        block_states: states,
        block_visits,
    }
}
// ANCHOR_END: solve

/// Apply the transfer functions of block `bb` to `state`, in the direction of
/// the analysis, calling `visit(location, state_before_that_location)` along
/// the way. "Before" means before the statement executes, in program order:
/// for a backward analysis that is the state *after* its transfer function.
fn apply_block<A: Analysis>(
    body: &Body,
    analysis: &A,
    bb: usize,
    state: &mut A::Domain,
    mut visit: impl FnMut(Location, &A::Domain),
) {
    let block = &body.blocks[bb];
    let block_id = BlockId(bb);
    let term_loc = body.terminator_location(block_id);
    match A::DIRECTION {
        Direction::Forward => {
            for (index, stmt) in block.statements.iter().enumerate() {
                let loc = Location {
                    block: block_id,
                    index,
                };
                visit(loc, state);
                analysis.apply_statement(state, stmt, loc);
            }
            visit(term_loc, state);
            analysis.apply_terminator(state, &block.terminator, term_loc);
        }
        Direction::Backward => {
            analysis.apply_terminator(state, &block.terminator, term_loc);
            visit(term_loc, state);
            for (index, stmt) in block.statements.iter().enumerate().rev() {
                let loc = Location {
                    block: block_id,
                    index,
                };
                analysis.apply_statement(state, stmt, loc);
                visit(loc, state);
            }
        }
    }
}

impl<A: Analysis> Results<A> {
    /// The state on entry to every program point, i.e. before the statement
    /// at that point executes. For liveness this is "live-in".
    pub fn states_before(&self, body: &Body) -> BTreeMap<Location, A::Domain> {
        let mut out = BTreeMap::new();
        for bb in 0..body.blocks.len() {
            let mut state = self.block_states[bb].clone();
            apply_block(body, &self.analysis, bb, &mut state, |loc, s| {
                out.insert(loc, s.clone());
            });
        }
        out
    }
}
