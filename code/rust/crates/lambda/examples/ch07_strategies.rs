// harness: run
//! Reduction strategies side by side: divergence (`Ω`), a discarded divergent
//! argument, confluence on a small term, and the `Y` and `Z` fixed-point
//! combinators under call-by-value.
//!
//! Run with: `cargo run -p lambda --example ch07_strategies`

use lambda::church::{decode_numeral, fact_step_cbv, numeral, omega, y, z};
use lambda::{Reduction, Strategy, Term, app, apps, parse, reduce, step};

const STRATEGIES: [(&str, Strategy); 3] = [
    ("normal order", Strategy::NormalOrder),
    ("call-by-name", Strategy::CallByName),
    ("call-by-value", Strategy::CallByValue),
];

fn describe(r: &Reduction) -> String {
    if r.finished {
        let plural = if r.steps == 1 { "" } else { "s" };
        format!("{}   ({} step{plural})", r.term, r.steps)
    } else {
        format!("out of fuel after {} steps", r.steps)
    }
}

fn p(src: &str) -> Term {
    parse(src).unwrap()
}

fn main() {
    // ANCHOR: omega
    let om = omega();
    println!("Ω = {om}");
    let next = step(&om, Strategy::NormalOrder).unwrap();
    println!("  one step later: {next}   (the same term: {})", next == om);
    println!("  {}", describe(&reduce(&om, Strategy::NormalOrder, 1000)));
    // ANCHOR_END: omega

    // ANCHOR: discard
    let discard = app(p("λx. λy. y"), omega());
    println!("\n{discard}");
    for (name, strategy) in STRATEGIES {
        println!(
            "  {name:<14} {}",
            describe(&reduce(&discard, strategy, 1000))
        );
    }
    // ANCHOR_END: discard

    // ANCHOR: confluence
    let t = p("(λx. x x) ((λy. y) z)");
    println!("\n{t}");
    for (name, strategy) in STRATEGIES {
        println!("  {name:<14} {}", describe(&reduce(&t, strategy, 1000)));
    }
    // ANCHOR_END: confluence

    // ANCHOR: weak
    let under_lambda = p("λx. (λy. y) x");
    println!("\n{under_lambda}");
    for (name, strategy) in STRATEGIES {
        println!(
            "  {name:<14} {}",
            describe(&reduce(&under_lambda, strategy, 1000))
        );
    }
    // ANCHOR_END: weak

    // ANCHOR: fixpoints
    println!("\nfactorial of 3 under call-by-value:");
    let with_y = apps(y(), [fact_step_cbv(), numeral(3)]);
    let r = reduce(&with_y, Strategy::CallByValue, 200);
    assert!(!r.finished);
    println!(
        "  with Y: out of fuel after {} steps; the term grew from {} to {} nodes",
        r.steps,
        with_y.size(),
        r.term.size()
    );
    let with_z = apps(z(), [fact_step_cbv(), numeral(3)]);
    let r = reduce(&with_z, Strategy::CallByValue, 100_000);
    assert!(r.finished);
    // Call-by-value stops at a λ: the result is a value, not yet a numeral.
    let value = r.term;
    let normal = reduce(&value, Strategy::NormalOrder, 100_000);
    let n = decode_numeral(&normal.term).unwrap();
    assert_eq!(n, 6);
    println!(
        "  with Z: a value after {} steps; normalizing it gives the numeral {n}",
        r.steps
    );
    // ANCHOR_END: fixpoints
}
