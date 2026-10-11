// harness: run
//! The simply typed λ-calculus at work: types synthesized by the bidirectional
//! checker, a checking trace, evaluation with closures, and the programs the
//! checker rejects (which would get stuck if we ran them anyway).
//!
//! Run with: `cargo run -p stlc --example ch08_stlc`

use stlc::{Term, check_with_trace, infer, parse_term, parse_type, run};

fn term(src: &str) -> Term {
    parse_term(src).unwrap_or_else(|e| panic!("{e}: {src}"))
}

// ANCHOR: library
/// A small library of definitions, put in scope with `let`.
const LIBRARY: [(&str, &str); 6] = [
    ("twice", "(λf. λx. f (f x) : (Nat → Nat) → Nat → Nat)"),
    ("add", "λm: Nat. λn: Nat. iter m n (λk: Nat. succ k)"),
    ("mul", "λm: Nat. λn: Nat. iter m 0 (add n)"),
    ("iszero", "λn: Nat. iter n true (λb: Bool. false)"),
    (
        "pred",
        "λn: Nat. fst (iter n (0, 0) (λp: Nat × Nat. (snd p, succ (snd p))))",
    ),
    ("swap", "λp: Nat × Bool. (snd p, fst p)"),
];

/// Wraps `body` in `let name = definition in ...` for every library entry.
fn with_library(body: &str) -> Term {
    let src = LIBRARY
        .iter()
        .rev()
        .fold(body.to_string(), |acc, (name, def)| {
            format!("let {name} = {def} in {acc}")
        });
    term(&src)
}
// ANCHOR_END: library

fn main() {
    // ANCHOR: types
    println!("The library, with synthesized types:");
    for (i, (name, def)) in LIBRARY.iter().enumerate() {
        // Each definition may use the earlier ones.
        let earlier: Vec<String> = LIBRARY[..i]
            .iter()
            .map(|(n, d)| format!("let {n} = {d} in "))
            .collect();
        let t = term(&format!("{}{def}", earlier.concat()));
        let ty = infer(&t).expect("library definitions are well typed");
        println!("  {name:<7}: {ty}");
    }
    // ANCHOR_END: types

    // ANCHOR: trace
    println!("\nChecking λf. λx. f (f x) against (Nat → Nat) → Nat → Nat:");
    let (result, lines) = check_with_trace(
        &term("λf. λx. f (f x)"),
        &parse_type("(Nat → Nat) → Nat → Nat").unwrap(),
    );
    assert!(result.is_ok());
    for line in lines {
        println!("  {line}");
    }
    // ANCHOR_END: trace

    // ANCHOR: run
    println!("\nEvaluation:");
    for src in [
        "twice (add 3) 4",
        "mul 6 7",
        "pred 10",
        "iszero 0",
        "swap (7, true)",
        "case (inr true : Nat + Bool) of inl n => n | inr b => 1",
        "add 3",
    ] {
        let program = with_library(src);
        let ty = infer(&program).unwrap();
        let value = run(&program).unwrap();
        println!("  {src}  :  {ty}  ⇓  {value}");
    }
    // ANCHOR_END: run

    // ANCHOR: rejected
    println!("\nRejected by the checker:");
    for src in [
        "3 4",
        "λx. x",
        "if true then 1 else false",
        "(λx. x : Nat)",
        "λx: Nat → Nat. x x",
    ] {
        let err = infer(&term(src)).unwrap_err();
        println!("  {src}\n      {err}");
    }
    // ANCHOR_END: rejected

    // ANCHOR: stuck
    println!("\nRun without checking:");
    for src in ["3 4", "if 0 then 1 else 2"] {
        println!("  {src}  ⇓  {}", run(&term(src)).unwrap_err());
    }
    // ANCHOR_END: stuck
}
