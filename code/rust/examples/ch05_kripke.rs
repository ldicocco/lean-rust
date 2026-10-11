// harness: run
//! An exhaustive search for Kripke countermodels (Chapter 5).
//!
//! Enumerates every Kripke model with up to three worlds and two atoms: every
//! partial order on the worlds, every monotone valuation of `P` and `Q`. For
//! each classical law it reports the smallest model in which the law fails at
//! some world; for a few intuitionistic laws it confirms that no model in the
//! search refutes them. (A search over small models is evidence, not a proof:
//! the proofs are in `Book/Ch05/Kripke.lean` and `Book/Ch05/Constructive.lean`.)
//!
//! Run with: `cargo run --example ch05_kripke`

use std::fmt;

// ANCHOR: formula
/// Propositional formulas over the atoms `P` (0) and `Q` (1).
#[derive(Clone, Debug, PartialEq)]
enum Formula {
    Atom(usize),
    Bot,
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Imp(Box<Formula>, Box<Formula>),
}
// ANCHOR_END: formula

use Formula::{Atom, Bot};

fn p() -> Formula {
    Atom(0)
}
fn q() -> Formula {
    Atom(1)
}
fn and(a: Formula, b: Formula) -> Formula {
    Formula::And(Box::new(a), Box::new(b))
}
fn or(a: Formula, b: Formula) -> Formula {
    Formula::Or(Box::new(a), Box::new(b))
}
fn imp(a: Formula, b: Formula) -> Formula {
    Formula::Imp(Box::new(a), Box::new(b))
}
fn not(a: Formula) -> Formula {
    imp(a, Bot)
}

impl Formula {
    fn precedence(&self) -> u8 {
        match self {
            Atom(_) | Bot => 5,
            Formula::Imp(_, b) if **b == Bot => 4,
            Formula::And(..) => 3,
            Formula::Or(..) => 2,
            Formula::Imp(..) => 1,
        }
    }
}

/// The same printing conventions as the `natded` crate: `¬` binds tightest,
/// then `∧`, `∨`, `→`; binary connectives group to the right.
impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let sub = |f: &mut fmt::Formatter<'_>, c: &Formula, min: u8| {
            if c.precedence() < min {
                write!(f, "({c})")
            } else {
                write!(f, "{c}")
            }
        };
        match self {
            Atom(i) => write!(f, "{}", ["P", "Q"][*i]),
            Bot => write!(f, "⊥"),
            Formula::Imp(a, b) if **b == Bot => {
                write!(f, "¬")?;
                sub(f, a, 4)
            }
            Formula::And(a, b) => {
                sub(f, a, 4)?;
                write!(f, " ∧ ")?;
                sub(f, b, 3)
            }
            Formula::Or(a, b) => {
                sub(f, a, 3)?;
                write!(f, " ∨ ")?;
                sub(f, b, 2)
            }
            Formula::Imp(a, b) => {
                sub(f, a, 2)?;
                write!(f, " → ")?;
                sub(f, b, 1)
            }
        }
    }
}

// ANCHOR: model
/// A finite Kripke model. Worlds are `0..n`; `le[w][v]` says that `v` is a
/// possible future of `w`; `val[atom][w]` says that the atom is known at `w`.
struct Model {
    n: usize,
    le: Vec<Vec<bool>>,
    val: Vec<Vec<bool>>,
}

/// The forcing relation `w ⊩ A`. Only implication (and so negation) looks
/// beyond the present world: it must hold in every future.
fn forces(m: &Model, w: usize, a: &Formula) -> bool {
    match a {
        Atom(i) => m.val[*i][w],
        Bot => false,
        Formula::And(a, b) => forces(m, w, a) && forces(m, w, b),
        Formula::Or(a, b) => forces(m, w, a) || forces(m, w, b),
        Formula::Imp(a, b) => (0..m.n)
            .filter(|&v| m.le[w][v])
            .all(|v| !forces(m, v, a) || forces(m, v, b)),
    }
}
// ANCHOR_END: model

// ANCHOR: enumerate
/// Every partial order on `n` worlds: reflexive, antisymmetric, transitive.
fn partial_orders(n: usize) -> Vec<Vec<Vec<bool>>> {
    let pairs: Vec<(usize, usize)> = (0..n)
        .flat_map(|i| (0..n).map(move |j| (i, j)))
        .filter(|(i, j)| i != j)
        .collect();
    let mut orders = Vec::new();
    for bits in 0..1u32 << pairs.len() {
        let mut le = vec![vec![false; n]; n];
        for (i, row) in le.iter_mut().enumerate() {
            row[i] = true;
        }
        for (k, &(i, j)) in pairs.iter().enumerate() {
            le[i][j] = bits >> k & 1 == 1;
        }
        let antisymmetric = pairs.iter().all(|&(i, j)| !(le[i][j] && le[j][i]));
        let transitive = (0..n).all(|i| {
            (0..n).all(|j| (0..n).all(|k| !(le[i][j] && le[j][k]) || le[i][k]))
        });
        if antisymmetric && transitive {
            orders.push(le);
        }
    }
    orders
}

/// Every monotone valuation of one atom: a set of worlds closed upward
/// (once known, an atom stays known).
fn up_sets(le: &[Vec<bool>]) -> Vec<Vec<bool>> {
    let n = le.len();
    (0..1u32 << n)
        .map(|bits| (0..n).map(|w| bits >> w & 1 == 1).collect::<Vec<bool>>())
        .filter(|set| (0..n).all(|w| (0..n).all(|v| !(set[w] && le[w][v]) || set[v])))
        .collect()
}

/// Every model with 1 to `max_worlds` worlds and two atoms.
fn all_models(max_worlds: usize) -> Vec<Model> {
    let mut models = Vec::new();
    for n in 1..=max_worlds {
        for le in partial_orders(n) {
            let ups = up_sets(&le);
            for vp in &ups {
                for vq in &ups {
                    models.push(Model {
                        n,
                        le: le.clone(),
                        val: vec![vp.clone(), vq.clone()],
                    });
                }
            }
        }
    }
    models
}
// ANCHOR_END: enumerate

/// Describes a countermodel: its order, where each atom holds, where the
/// formula fails.
fn describe(m: &Model, w: usize) -> String {
    let edges: Vec<String> = (0..m.n)
        .flat_map(|i| (0..m.n).map(move |j| (i, j)))
        .filter(|&(i, j)| i != j && m.le[i][j])
        .map(|(i, j)| format!("{i}≤{j}"))
        .collect();
    let order = if edges.is_empty() {
        "no order".to_string()
    } else {
        edges.join(" ")
    };
    let atoms: Vec<String> = ["P", "Q"]
        .iter()
        .enumerate()
        .map(|(i, name)| {
            let worlds: Vec<String> = (0..m.n)
                .filter(|&w| m.val[i][w])
                .map(|w| w.to_string())
                .collect();
            format!("{name}@{{{}}}", worlds.join(","))
        })
        .collect();
    format!("{} worlds, {order}, {}, fails at {w}", m.n, atoms.join(" "))
}

fn main() {
    let models = all_models(3);
    println!("models with at most 3 worlds and 2 atoms: {}", models.len());
    println!();

    // ANCHOR: classical_laws
    let classical = [
        ("excluded middle", or(p(), not(p()))),
        ("double negation", imp(not(not(p())), p())),
        ("Peirce", imp(imp(imp(p(), q()), p()), p())),
        ("De Morgan", imp(not(and(p(), q())), or(not(p()), not(q())))),
        ("weak excl. middle", or(not(p()), not(not(p())))),
        ("linearity", or(imp(p(), q()), imp(q(), p()))),
    ];
    // ANCHOR_END: classical_laws
    // ANCHOR: search
    for (name, law) in &classical {
        // `models` is ordered by size, so the first hit is a smallest one.
        let found = models
            .iter()
            .find_map(|m| (0..m.n).find(|&w| !forces(m, w, law)).map(|w| (m, w)));
        match found {
            Some((m, w)) => println!("{name:<17} {law}\n  {}", describe(m, w)),
            None => println!("{name:<17} {law}\n  no countermodel found"),
        }
    }
    // ANCHOR_END: search
    println!();

    // ANCHOR: intuitionistic_laws
    let intuitionistic = [
        not(not(or(p(), not(p())))),
        imp(p(), not(not(p()))),
        imp(not(not(not(p()))), not(p())),
        imp(not(or(p(), q())), and(not(p()), not(q()))),
        imp(or(not(p()), not(q())), not(and(p(), q()))),
        imp(and(imp(p(), q()), imp(p(), not(q()))), not(p())),
    ];
    for law in &intuitionistic {
        let holds = models.iter().all(|m| (0..m.n).all(|w| forces(m, w, law)));
        assert!(holds, "{law} should hold in every Kripke model");
        println!("holds in all {} models: {law}", models.len());
    }
    // ANCHOR_END: intuitionistic_laws
}
