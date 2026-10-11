// harness: run
//! The natural-deduction proof checker of Chapter 4 at work: two correct
//! proofs printed as trees of sequents, three incorrect proofs and their error
//! messages, and the soundness theorem tested against truth tables.
//!
//! Run with: `cargo run -p natded --example ch04_proof_checker`

use natded::proof::*;
use natded::truth::{counterexample, show_valuation, truth_table};
use natded::{Checker, Formula};

/// Parses a formula written in the book's notation.
fn f(s: &str) -> Formula {
    s.parse().expect("a well-formed formula")
}

fn main() {
    let checker = Checker::intuitionistic();

    // ANCHOR: and_comm
    // ⊢ A ∧ B → B ∧ A. Assume A ∧ B under the name `u`, take it apart twice
    // (∧E2 and ∧E1), put the parts back together in the other order (∧I),
    // and discharge `u` (→I).
    let and_comm = imp_i("u", f("A ∧ B"), and_i(and_e2(hyp("u")), and_e1(hyp("u"))));
    let d1 = checker
        .prove(&[], &f("A ∧ B → B ∧ A"), &and_comm)
        .expect("a correct proof");
    print!("{d1}");
    // ANCHOR_END: and_comm
    println!();

    // ANCHOR: or_map
    // ⊢ (A → B) → A ∨ C → B ∨ C: a case analysis (∨E) on the disjunction `d`.
    let or_map = imp_i(
        "g",
        f("A → B"),
        imp_i(
            "d",
            f("A ∨ C"),
            or_e(
                hyp("d"),
                "a", // case A: apply g, then choose the left side
                or_i1(imp_e(hyp("g"), hyp("a")), f("C")),
                "c", // case C: choose the right side
                or_i2(f("B"), hyp("c")),
            ),
        ),
    );
    let d2 = checker
        .prove(&[], &f("(A → B) → A ∨ C → B ∨ C"), &or_map)
        .expect("a correct proof");
    print!("{d2}");
    // ANCHOR_END: or_map
    println!();

    // ANCHOR: errors
    // Three mistakes. First: projecting from something that is not a pair.
    let wrong_shape = and_e1(hyp("u"));
    let e1 = checker
        .check(&[("u", f("A → B"))], &wrong_shape)
        .unwrap_err();
    println!("{e1}");

    // Second: using an assumption after the →I that discharged it.
    let out_of_scope = and_i(imp_i("u", f("A"), hyp("u")), hyp("u"));
    let e2 = checker.check(&[], &out_of_scope).unwrap_err();
    println!("{e2}");

    // Third: modus ponens with the wrong argument.
    let wrong_argument = imp_i("b", f("B"), imp_e(hyp("g"), hyp("b")));
    let e3 = checker
        .check(&[("g", f("A → C"))], &wrong_argument)
        .unwrap_err();
    println!("{e3}");
    // ANCHOR_END: errors
    println!();

    // ANCHOR: soundness
    // Soundness, tested: every sequent the checker accepts is true in every
    // row of its truth table.
    for d in [&d1, &d2] {
        let hyps: Vec<Formula> = d.context.iter().map(|(_, a)| a.clone()).collect();
        assert!(counterexample(&hyps, &d.conclusion).is_none());
    }
    print!("{}", truth_table(&f("A ∧ B → B ∧ A")));

    // A formula with a counterexample cannot have a proof: by soundness, the
    // proof would make it true in the falsifying row.
    let not_valid = f("A ∨ B → A");
    let row = counterexample(&[], &not_valid).expect("not a tautology");
    println!("{not_valid} is false when {}", show_valuation(&row));
    // ANCHOR_END: soundness
}
