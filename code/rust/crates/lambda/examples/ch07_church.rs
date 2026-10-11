// harness: run
//! Church encodings computed by β-reduction: numerals, arithmetic, booleans,
//! pairs and a factorial defined with the `Y` combinator.
//!
//! Run with: `cargo run -p lambda --example ch07_church`

use lambda::church::{
    and, decode_bool, decode_numeral, fact_step, fls, fst, iszero, numeral, pair, plus,
    power, pred, sub, succ, times, tru, y,
};
use lambda::{Strategy, Term, app, apps, reduce, to_de_bruijn, trace};

/// How to read a normal form back: the same term can be a numeral and a
/// boolean (`0` and `false` are α-equivalent), so the caller must say which.
#[derive(Clone, Copy)]
enum Read {
    Nat,
    Bool,
}

/// Runs `t` with normal-order reduction and reads back the result.
fn evaluate(t: &Term, read: Read) -> (String, usize) {
    let r = reduce(t, Strategy::NormalOrder, 100_000);
    assert!(r.finished, "no normal form within the step limit");
    let shown = match read {
        Read::Nat => decode_numeral(&r.term).map(|n| n.to_string()),
        Read::Bool => decode_bool(&r.term).map(|b| b.to_string()),
    };
    (shown.unwrap_or_else(|| r.term.to_string()), r.steps)
}

fn main() {
    // ANCHOR: numerals
    println!("Church numerals");
    for n in [0, 1, 3] {
        println!("  {n} = {}", numeral(n));
    }
    // ANCHOR_END: numerals

    // ANCHOR: succ_trace
    println!("\nsucc 1, step by step (normal order):");
    let steps = trace(&app(succ(), numeral(1)), Strategy::NormalOrder, 10);
    for (i, t) in steps.iter().enumerate() {
        let arrow = if i == 0 { " " } else { "→" };
        println!("  {arrow} {t}");
    }
    assert_eq!(decode_numeral(steps.last().unwrap()), Some(2));
    // ANCHOR_END: succ_trace

    // ANCHOR: arithmetic
    let n = numeral;
    let fact = app(y(), fact_step());
    let programs = vec![
        ("plus 2 3", apps(plus(), [n(2), n(3)]), Read::Nat, "5"),
        ("times 2 3", apps(times(), [n(2), n(3)]), Read::Nat, "6"),
        ("power 2 3", apps(power(), [n(2), n(3)]), Read::Nat, "8"),
        ("pred 3", app(pred(), n(3)), Read::Nat, "2"),
        ("sub 5 2", apps(sub(), [n(5), n(2)]), Read::Nat, "3"),
        ("iszero 0", app(iszero(), n(0)), Read::Bool, "true"),
        ("iszero 2", app(iszero(), n(2)), Read::Bool, "false"),
        (
            "and true false",
            apps(and(), [tru(), fls()]),
            Read::Bool,
            "false",
        ),
        (
            "fst (pair 1 2)",
            app(fst(), apps(pair(), [n(1), n(2)])),
            Read::Nat,
            "1",
        ),
        ("Y fact_step 3", app(fact, n(3)), Read::Nat, "6"),
    ];
    println!("\n{:<18}{:>8}{:>8}", "program", "result", "steps");
    for (name, term, read, expected) in &programs {
        let (result, steps) = evaluate(term, *read);
        assert_eq!(result, *expected, "{name}");
        println!("{name:<18}{result:>8}{steps:>8}");
    }
    // ANCHOR_END: arithmetic

    // ANCHOR: agree
    // The same computation with de Bruijn indices: same choices, same steps,
    // and the same normal form.
    let fact3 = app(app(y(), fact_step()), n(3));
    let named = reduce(&fact3, Strategy::NormalOrder, 100_000);
    let (db_normal, db_steps) = to_de_bruijn(&fact3, &[])
        .unwrap()
        .normalize(100_000)
        .unwrap();
    let same = to_de_bruijn(&named.term, &[]).unwrap() == db_normal;
    println!(
        "
Y fact_step 3 with de Bruijn indices: {db_steps} steps, same normal form: {same}"
    );
    assert!(same);
    // ANCHOR_END: agree

    // ANCHOR: false_is_zero
    // The untyped calculus cannot tell a boolean from a number.
    println!("\nfalse = {}", fls());
    println!("0     = {}", numeral(0));
    println!("α-equivalent: {}", fls().alpha_eq(&numeral(0)));
    // ANCHOR_END: false_is_zero
}
