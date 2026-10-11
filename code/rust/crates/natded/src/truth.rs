//! Truth tables: the classical, two-valued semantics of formulas.
//!
//! The soundness theorem of Chapter 4 (proved in Lean in `Book/Ch04/Deep.lean`)
//! says that every derivable sequent is valid: every row of the truth table
//! that makes the assumptions true makes the conclusion true. This module lets
//! the Rust side test that claim on concrete proofs, find counterexamples to
//! formulas that are not valid, and search for a truth table for `tonk`.

use crate::formula::Formula;
use std::collections::{BTreeMap, BTreeSet};

/// A row of a truth table: a truth value for each atom.
pub type Valuation = BTreeMap<String, bool>;

/// A candidate truth table for `tonk`: `table[a][b]` is the value of
/// `a tonk b` (index 0 is false, 1 is true).
pub type TonkTable = [[bool; 2]; 2];

// ANCHOR: eval
/// The truth value of `f` in the row `v`. Atoms missing from `v` are false.
/// Returns `None` if `f` mentions `tonk`, which has no truth table.
pub fn eval(f: &Formula, v: &Valuation) -> Option<bool> {
    if f.mentions_tonk() {
        return None;
    }
    Some(eval_with(f, v, &[[false; 2]; 2]))
}

/// The truth value of `f`, reading `tonk` from the given table.
pub fn eval_with(f: &Formula, v: &Valuation, tonk: &TonkTable) -> bool {
    match f {
        Formula::Atom(name) => v.get(name).copied().unwrap_or(false),
        Formula::Top => true,
        Formula::Bot => false,
        Formula::And(a, b) => eval_with(a, v, tonk) && eval_with(b, v, tonk),
        Formula::Or(a, b) => eval_with(a, v, tonk) || eval_with(b, v, tonk),
        Formula::Imp(a, b) => !eval_with(a, v, tonk) || eval_with(b, v, tonk),
        Formula::Tonk(a, b) => {
            tonk[eval_with(a, v, tonk) as usize][eval_with(b, v, tonk) as usize]
        }
    }
}
// ANCHOR_END: eval

/// Every row of the truth table for the given atoms, in the usual order
/// (all false first, the last atom changing fastest).
pub fn valuations(atoms: &BTreeSet<String>) -> Vec<Valuation> {
    let names: Vec<&String> = atoms.iter().collect();
    let n = names.len();
    (0..1u32 << n)
        .map(|bits| {
            names
                .iter()
                .enumerate()
                .map(|(i, name)| ((*name).clone(), bits >> (n - 1 - i) & 1 == 1))
                .collect()
        })
        .collect()
}

// ANCHOR: counterexample
/// A row that makes every assumption true and the conclusion false, if one
/// exists. `None` means the sequent `hyps ⊢ goal` is valid. Formulas that
/// mention `tonk` have no truth table, so the caller must not pass them.
pub fn counterexample(hyps: &[Formula], goal: &Formula) -> Option<Valuation> {
    let mut atoms = goal.atoms();
    for h in hyps {
        atoms.extend(h.atoms());
    }
    let truth =
        |f: &Formula, v: &Valuation| eval(f, v).expect("no tonk in a truth table");
    valuations(&atoms)
        .into_iter()
        .find(|v| hyps.iter().all(|h| truth(h, v)) && !truth(goal, v))
}

/// Is `f` true in every row of its truth table?
pub fn is_tautology(f: &Formula) -> bool {
    counterexample(&[], f).is_none()
}
// ANCHOR_END: counterexample

/// Shows a row as `A = T, B = F`.
pub fn show_valuation(v: &Valuation) -> String {
    let parts: Vec<String> = v
        .iter()
        .map(|(name, value)| format!("{name} = {}", if *value { "T" } else { "F" }))
        .collect();
    parts.join(", ")
}

/// The whole truth table of `f`, one row per line.
pub fn truth_table(f: &Formula) -> String {
    let atoms = f.atoms();
    let mut out = String::new();
    let header: Vec<&str> = atoms.iter().map(|a| a.as_str()).collect();
    out.push_str(&format!("{} │ {f}\n", header.join(" ")));
    for v in valuations(&atoms) {
        let cells: Vec<String> = atoms
            .iter()
            .map(|a| {
                let width = a.chars().count();
                format!("{:<width$}", if v[a] { "T" } else { "F" })
            })
            .collect();
        let value = eval(f, &v).map_or("?", |b| if b { "T" } else { "F" });
        out.push_str(&format!("{} │ {value}\n", cells.join(" ")));
    }
    out
}

// ANCHOR: tonk_search
/// The 16 possible truth tables for a binary connective.
pub fn all_tables() -> Vec<TonkTable> {
    (0..16u8)
        .map(|bits| {
            let bit = |i: u8| bits >> i & 1 == 1;
            [[bit(0), bit(1)], [bit(2), bit(3)]]
        })
        .collect()
}

/// tonk-I (from `A`, infer `A tonk B`) is sound for a table when every row
/// with `A` true has `A tonk B` true.
pub fn tonk_intro_sound(t: &TonkTable) -> bool {
    [false, true].iter().all(|&b| t[1][b as usize])
}

/// tonk-E (from `A tonk B`, infer `B`) is sound for a table when every row
/// with `A tonk B` true has `B` true.
pub fn tonk_elim_sound(t: &TonkTable) -> bool {
    [false, true].iter().all(|&a| !t[a as usize][0])
}
// ANCHOR_END: tonk_search

#[cfg(test)]
mod tests {
    use super::*;

    fn f(s: &str) -> Formula {
        s.parse().unwrap()
    }

    #[test]
    fn classical_tautologies() {
        for s in [
            "A ∨ ¬A",
            "¬¬A → A",
            "((A → B) → A) → A",
            "¬(A ∧ B) → ¬A ∨ ¬B",
            "A ∧ B → B ∧ A",
        ] {
            assert!(is_tautology(&f(s)), "{s}");
        }
    }

    #[test]
    fn counterexamples() {
        let v = counterexample(&[], &f("A ∨ B → A")).unwrap();
        assert_eq!(show_valuation(&v), "A = F, B = T");
        assert!(counterexample(&[f("A"), f("A → B")], &f("B")).is_none());
        assert!(counterexample(&[], &f("⊥")).is_some());
    }

    #[test]
    fn tonk_has_no_truth_table() {
        assert_eq!(eval(&f("A tonk B"), &Valuation::new()), None);
        let tables = all_tables();
        assert_eq!(tables.len(), 16);
        assert_eq!(tables.iter().filter(|t| tonk_intro_sound(t)).count(), 4);
        assert_eq!(tables.iter().filter(|t| tonk_elim_sound(t)).count(), 4);
        assert!(
            !tables
                .iter()
                .any(|t| tonk_intro_sound(t) && tonk_elim_sound(t))
        );
    }

    #[test]
    fn table_layout() {
        let table = truth_table(&f("A → B"));
        assert_eq!(table.lines().count(), 5);
        assert!(table.lines().nth(3).unwrap().ends_with("│ F"));
    }
}
