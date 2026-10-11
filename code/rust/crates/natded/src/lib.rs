//! A proof checker for natural deduction in propositional logic.
//!
//! Built in Chapter 4. The crate has four parts:
//!
//! - [`formula`]: the syntax of formulas, with a parser and a printer;
//! - [`proof`] and [`check`]: proof trees and a checker that turns a correct
//!   tree into a [`check::Derivation`] (a tree of sequents) and a wrong one
//!   into a [`check::CheckError`] that says which rule failed, where and why;
//! - [`truth`]: truth tables, to test the soundness theorem on examples and to
//!   find counterexamples;
//! - [`normalize`]: detour removal (local soundness), normalization and the
//!   subformula property.
//!
//! Prior's `tonk` is included as an optional extension of the checker, to
//! show what a connective without harmony does to a logic.

pub mod check;
pub mod formula;
pub mod normalize;
pub mod proof;
pub mod truth;

pub use check::{CheckError, Checker, Derivation, ErrorKind, Rule};
pub use formula::Formula;
pub use proof::Proof;
