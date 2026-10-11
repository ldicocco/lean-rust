//! A miniature MIR with move analysis, liveness and non-lexical borrow checking.
//!
//! Built in Chapter 29. The modules follow the stages of rustc's borrow
//! checker:
//!
//! * [`mir`]: the intermediate representation (places, statements,
//!   terminators, basic blocks), and [`build`], a builder for writing it by
//!   hand;
//! * [`dataflow`]: a generic worklist solver for dataflow analyses;
//! * [`moves`]: maybe-initialized and maybe-uninitialized places, the
//!   E0382 check and drop elaboration;
//! * [`liveness`]: live locals (and locals in scope, for the lexical checker);
//! * [`regions`]: outlives constraints and region inference over CFG points;
//! * [`borrowck`]: loans, loans in scope, conflicts (E0499, E0502, E0505,
//!   E0506, ...) and the four checkers compared in the chapter;
//! * [`polonius`]: location-sensitive loan liveness in the style of Polonius;
//! * [`programs`]: real Rust functions translated to the miniature MIR by hand.

pub mod borrowck;
pub mod build;
pub mod dataflow;
pub mod diagnostics;
pub mod liveness;
pub mod mir;
pub mod moves;
pub mod polonius;
pub mod programs;
pub mod regions;

pub use borrowck::{Checker, check};
