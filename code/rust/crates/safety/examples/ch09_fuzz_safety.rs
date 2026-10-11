// harness: run
//! Type safety, tested: a run of a well-typed program step by step, a few
//! ill-typed programs that go wrong, and a property-based test of progress,
//! preservation and determinism on thousands of random well-typed terms.
//! Then the same harness against a broken typing rule, which it catches.
//!
//! Run with: `cargo run -p safety --example ch09_fuzz_safety`

use safety::eval::{Outcome, run};
use safety::generate::gen_untyped;
use safety::props::{Config, fuzz, shrink};
use safety::rng::Rng;
use safety::syntax::{Term, Ty, add, app, ite, lam, twice};
use safety::typing::{Rules, type_of, type_of_with};

// ANCHOR: trace
/// Prints every step of the run of `t`, with the type of every intermediate
/// term (preservation, visibly) and the derivation of every step.
fn show_run(rules: Rules, t: &Term) {
    let ty = |t: &Term| match type_of_with(rules, &[], t) {
        Ok(ty) => ty.to_string(),
        Err(e) => format!("ill typed: {e}"),
    };
    let (trace, outcome) = run(t, 100);
    println!("   {t}  : {}", ty(t));
    for s in &trace {
        println!("⟶  {}  : {}", s.result, ty(&s.result));
        println!("      by {}", s.derivation_string());
    }
    match outcome {
        Outcome::Value(_) => println!("   (a value)"),
        Outcome::Stuck(_) => println!("   (stuck)"),
        Outcome::OutOfFuel(_) => println!("   (out of fuel)"),
    }
}
// ANCHOR_END: trace

fn main() {
    // ANCHOR: walkthrough
    let add_two = lam(Ty::Nat, add(Term::Var(0), Term::Lit(2)));
    let program = app(app(twice(), add_two), Term::Lit(3));
    println!("== One run, step by step ==");
    show_run(Rules::Sound, &program);
    // ANCHOR_END: walkthrough

    // ANCHOR: going_wrong
    println!("\n== Ill-typed terms ==");
    let self_apply = lam(Ty::Bool, app(Term::Var(0), Term::Var(0)));
    let examples = [
        add(Term::True, Term::Lit(1)),
        app(lam(Ty::Nat, add(Term::Var(0), Term::Lit(1))), Term::True),
        ite(Term::True, Term::Lit(1), Term::False),
        app(self_apply.clone(), self_apply),
    ];
    for t in &examples {
        let (trace, outcome) = run(t, 100);
        let steps = match trace.len() {
            1 => "1 step".to_string(),
            n => format!("{n} steps"),
        };
        let ending = match outcome {
            Outcome::Value(v) => format!("reaches the value {v} in {steps}"),
            Outcome::Stuck(s) => format!("is stuck at {s} after {steps}"),
            Outcome::OutOfFuel(_) => format!("is still running after {steps}"),
        };
        println!("{t}");
        println!("   rejected: {}", type_of(&[], t).unwrap_err());
        println!("   it {ending}");
    }
    // ANCHOR_END: going_wrong

    // ANCHOR: fuzz_sound
    println!("\n== Property test: random well-typed terms ==");
    let config = Config {
        seed: 2024,
        count: 10_000,
        max_size: 30,
        fuel: 1_000,
        rules: Rules::Sound,
    };
    let s = fuzz(config).expect("no counterexample");
    println!("terms        : {} (seed {})", s.terms, config.seed);
    println!(
        "types        : {} bool, {} nat, {} function",
        s.bools, s.nats, s.functions
    );
    println!("largest term : {} constructors", s.largest_term);
    println!(
        "steps        : {} in total, longest run {}",
        s.total_steps, s.longest_run
    );
    println!(
        "progress     : held in all {} states visited",
        s.total_steps + s.terms
    );
    println!("preservation : held for all {} steps", s.total_steps);
    println!("determinism  : one rule at most in every state, as the evaluator chose");
    // ANCHOR_END: fuzz_sound

    // ANCHOR: untyped
    println!("\n== Random closed terms, ignoring types ==");
    let mut rng = Rng::new(7);
    let (mut typed, mut stuck, mut value, mut diverging) = (0, 0, 0, 0);
    for _ in 0..10_000 {
        let size = 1 + rng.below(12);
        let t = gen_untyped(&mut rng, 0, size);
        if type_of(&[], &t).is_ok() {
            typed += 1;
            continue;
        }
        match run(&t, 200).1 {
            Outcome::Stuck(_) => stuck += 1,
            Outcome::Value(_) => value += 1,
            Outcome::OutOfFuel(_) => diverging += 1,
        }
    }
    println!("well typed   : {typed}");
    println!("ill typed    : {}", stuck + value + diverging);
    println!("   stuck              : {stuck}");
    println!("   reached a value    : {value}");
    println!("   ran out of fuel    : {diverging}");
    // ANCHOR_END: untyped

    // ANCHOR: fuzz_broken
    println!("\n== The same test, with the broken rule for `if` ==");
    let broken = Config {
        rules: Rules::BrokenIf,
        ..config
    };
    let failure = fuzz(broken).expect_err("the broken rule is caught");
    let size = failure.term.size();
    let theorem = failure.violation.theorem();
    println!(
        "term #{} ({size} constructors) violates {theorem}",
        failure.index
    );
    let (small, ty, violation) = shrink(Rules::BrokenIf, &failure.term, broken.fuel);
    println!("shrunk to    : {small} : {ty}");
    println!("   {violation}");
    let lean_example = add(ite(Term::False, Term::Lit(1), Term::True), Term::Lit(2));
    println!("and the counterexample from Safety.lean:");
    show_run(Rules::BrokenIf, &lean_example);
    // ANCHOR_END: fuzz_broken
}
