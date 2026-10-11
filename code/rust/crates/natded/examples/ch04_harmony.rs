// harness: run
//! Harmony in practice: a proof with a detour is normalized (local soundness)
//! and gains the subformula property; then Prior's `tonk` is added to the
//! checker, which promptly accepts a proof of ⊥ that no truth table and no
//! reduction can make sense of.
//!
//! Run with: `cargo run -p natded --example ch04_harmony`

use natded::normalize::{foreign_formulas, normalize};
use natded::proof::*;
use natded::truth::{all_tables, counterexample, tonk_elim_sound, tonk_intro_sound};
use natded::{Checker, Formula};

fn f(s: &str) -> Formula {
    s.parse().expect("a well-formed formula")
}

fn show(formulas: &std::collections::BTreeSet<Formula>) -> String {
    let parts: Vec<String> = formulas.iter().map(|a| a.to_string()).collect();
    format!("{{{}}}", parts.join(", "))
}

fn main() {
    let checker = Checker::intuitionistic();

    // ANCHOR: detour
    // A ∧ B ⊢ B ∧ A, proved by first proving a general lemma A ∧ B → B ∧ A
    // (→I) and then applying it to the assumption `u` (→E): a detour.
    let lemma = imp_i("x", f("A ∧ B"), and_i(and_e2(hyp("x")), and_e1(hyp("x"))));
    let with_detour = imp_e(lemma, hyp("u"));
    let hyps = [("u", f("A ∧ B"))];
    let before = checker.check(&hyps, &with_detour).expect("correct");
    print!("{before}");
    println!("not subformulas: {}", show(&foreign_formulas(&before)));
    // ANCHOR_END: detour
    println!();

    // ANCHOR: normalized
    let result = normalize(&with_detour, 100);
    println!("reductions: {:?}", result.steps);
    let after = checker.check(&hyps, &result.proof).expect("still correct");
    print!("{after}");
    println!("not subformulas: {}", show(&foreign_formulas(&after)));
    assert_eq!(before.sequent(), after.sequent());
    // ANCHOR_END: normalized
    println!();

    // ANCHOR: tonk
    // ⊤ ⊢ ⊤ tonk ⊥ by tonk-I, then ⊥ by tonk-E.
    let absurd = tonk_e(tonk_i(top_i(), Formula::Bot));
    match checker.check(&[], &absurd) {
        Ok(_) => unreachable!("intuitionistic logic has no tonk"),
        Err(e) => println!("{e}"),
    }
    let tonk_checker = Checker::with_tonk();
    let d = tonk_checker
        .check(&[], &absurd)
        .expect("accepted with tonk");
    print!("{d}");

    // Now every formula has a proof: wrap the proof of ⊥ in ⊥E.
    let anything = bot_e(absurd.clone(), f("A ∧ ¬A"));
    let d = tonk_checker
        .check(&[], &anything)
        .expect("accepted with tonk");
    println!("accepted: {}", d.sequent());
    // ANCHOR_END: tonk

    // ANCHOR: tonk_diagnosis
    // Soundness is gone: ⊥ is false in every row of every truth table...
    assert!(counterexample(&[], &Formula::Bot).is_some());
    // ...and no truth table for tonk could rescue it.
    let tables = all_tables();
    let intro = tables.iter().filter(|t| tonk_intro_sound(t)).count();
    let elim = tables.iter().filter(|t| tonk_elim_sound(t)).count();
    let both = tables
        .iter()
        .filter(|t| tonk_intro_sound(t) && tonk_elim_sound(t))
        .count();
    println!(
        "truth tables for tonk: {intro} fit tonk-I, {elim} fit tonk-E, {both} fit both"
    );

    // Local soundness fails: the detour tonk-I/tonk-E cannot be reduced.
    let stuck = normalize(&absurd, 100);
    println!("reductions: {:?}, stuck: {:?}", stuck.steps, stuck.stuck);
    // ANCHOR_END: tonk_diagnosis
}
