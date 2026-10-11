// harness: run
//! Proof search in linear and affine logic: which sequents survive the loss
//! of the structural rules, the derivations the prover finds, and why the
//! unprovable ones fail.
//!
//! Run with: `cargo run -p linlogic --example ch21_prover`

use linlogic::{Logic, Prover, parse_sequent};

/// Is the sequent provable in `logic`? Every proof found is checked by the
/// independent checker before we believe it.
fn provable(logic: Logic, text: &str) -> bool {
    let seq = parse_sequent(text).expect("valid sequent");
    match Prover::new(logic).prove(&seq) {
        Some(proof) => {
            proof.check(logic).expect("the prover's proofs are correct");
            true
        }
        None => false,
    }
}

fn yes_no(b: bool) -> &'static str {
    if b { "yes" } else { "no" }
}

// ANCHOR: table
const TABLE: [(&str, &str); 12] = [
    ("A |- A * A", "contraction"),
    ("A * B |- A", "weakening"),
    ("A & B |- A", "a choice"),
    ("A |- A & A", "sharing"),
    ("A * B |- B * A", "exchange"),
    ("A * B |- A & B", "& from ⊗ needs weakening"),
    ("A & B |- A * B", "⊗ from & needs contraction"),
    ("A |- B -o A", "the K combinator"),
    ("A -o A -o B |- A -o B", "the W combinator"),
    ("A -o B -o C |- A * B -o C", "currying"),
    ("top |- 1", "1 from ⊤ needs weakening"),
    ("A * (B + C) |- (A * B) + (A * C)", "distributivity"),
];
// ANCHOR_END: table

// ANCHOR: coffee
const COFFEE: [&str; 5] = [
    "coin, coin -o (coffee & tea) |- coffee",
    "coin, coin -o (coffee & tea) |- coffee * tea",
    "coin, coin, coin -o (coffee & tea), coin -o (coffee & tea) |- coffee * tea",
    "coin, coin -o (coffee + tea) |- coffee",
    "coin, coin -o (coffee + tea) |- coffee + tea",
];
// ANCHOR_END: coffee

fn main() {
    // ANCHOR: run_table
    println!("{:<34} {:<7} {:<7} shows", "sequent", "linear", "affine");
    for (text, shows) in TABLE {
        let seq = parse_sequent(text).unwrap().to_string();
        let lin = yes_no(provable(Logic::Linear, text));
        let aff = yes_no(provable(Logic::Affine, text));
        println!("{seq:<34} {lin:<7} {aff:<7} {shows}");
    }
    println!("\nlin  aff  sequent");
    for text in COFFEE {
        let seq = parse_sequent(text).unwrap().to_string();
        let lin = yes_no(provable(Logic::Linear, text));
        let aff = yes_no(provable(Logic::Affine, text));
        println!("{lin:<4} {aff:<4} {seq}");
    }
    // ANCHOR_END: run_table

    // ANCHOR: traces
    for (logic, text) in [
        (Logic::Linear, "A * B |- B * A"),
        (Logic::Affine, "A * B |- A"),
        (Logic::Linear, "coin, coin -o (coffee & tea) |- coffee"),
    ] {
        let seq = parse_sequent(text).unwrap();
        let proof = Prover::new(logic).prove(&seq).unwrap();
        println!("\n{logic} proof of {seq}:");
        print!("{}", proof.render());
    }
    // ANCHOR_END: traces

    // ANCHOR: failures
    for text in ["A |- A * A", "coin, coin -o (coffee & tea) |- coffee * tea"] {
        let seq = parse_sequent(text).unwrap();
        let mut prover = Prover::new(Logic::Linear);
        assert!(prover.prove(&seq).is_none());
        println!("\nno linear proof of {seq}; the rules that apply:");
        for line in prover.explain(&seq) {
            println!("  {line}");
        }
        println!("  ({} sequents examined)", prover.explored());
    }
    // ANCHOR_END: failures
}
