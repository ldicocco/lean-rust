//! Removing detours: the local-soundness reductions of Chapter 4.
//!
//! A *detour* is an introduction rule whose conclusion is immediately the main
//! premise of an elimination rule for the same connective. Each harmonious
//! connective comes with a reduction that removes such a detour and proves the
//! same conclusion from the same assumptions. Repeating the reductions until
//! no detour is left is *normalization*. For `tonk` there is no reduction:
//! the detour tonk-I/tonk-E is stuck.

use crate::check::Derivation;
use crate::formula::Formula;
use crate::proof::Proof;
use std::collections::BTreeSet;

impl Proof {
    /// The same node with its premises replaced (in the order of `premises`).
    fn with_premises(&self, mut new: Vec<Proof>) -> Proof {
        let mut next = || Box::new(new.remove(0));
        match self {
            Proof::Hyp(_) | Proof::TopI => self.clone(),
            Proof::BotE(_, c) => Proof::BotE(next(), c.clone()),
            Proof::AndI(_, _) => Proof::AndI(next(), next()),
            Proof::AndE1(_) => Proof::AndE1(next()),
            Proof::AndE2(_) => Proof::AndE2(next()),
            Proof::OrI1(_, b) => Proof::OrI1(next(), b.clone()),
            Proof::OrI2(a, _) => Proof::OrI2(a.clone(), next()),
            Proof::OrE { left, right, .. } => Proof::OrE {
                scrutinee: next(),
                left: (left.0.clone(), next()),
                right: (right.0.clone(), next()),
            },
            Proof::ImpI {
                name, assumption, ..
            } => Proof::ImpI {
                name: name.clone(),
                assumption: assumption.clone(),
                body: next(),
            },
            Proof::ImpE(_, _) => Proof::ImpE(next(), next()),
            Proof::TonkI(_, b) => Proof::TonkI(next(), b.clone()),
            Proof::TonkE(_) => Proof::TonkE(next()),
        }
    }
}

// ANCHOR: substitute
/// Replaces every use of the assumption `name` in `body` by the proof
/// `replacement`. Binders that would capture an open assumption of
/// `replacement` are renamed first, exactly as in capture-avoiding
/// substitution for the λ-calculus (Chapter 7).
pub fn substitute(body: &Proof, name: &str, replacement: &Proof) -> Proof {
    let open = replacement.open_assumptions();
    subst(body, name, replacement, &open)
}
// ANCHOR_END: substitute

fn subst(p: &Proof, name: &str, repl: &Proof, open: &BTreeSet<String>) -> Proof {
    match p {
        Proof::Hyp(n) if n == name => repl.clone(),
        Proof::Hyp(_) | Proof::TopI => p.clone(),
        Proof::ImpI {
            name: x,
            assumption,
            body,
        } => {
            let (x, body) = under_binder(x, body, name, repl, open);
            Proof::ImpI {
                name: x,
                assumption: assumption.clone(),
                body: Box::new(body),
            }
        }
        Proof::OrE {
            scrutinee,
            left,
            right,
        } => {
            let (x, l) = under_binder(&left.0, &left.1, name, repl, open);
            let (y, r) = under_binder(&right.0, &right.1, name, repl, open);
            Proof::OrE {
                scrutinee: Box::new(subst(scrutinee, name, repl, open)),
                left: (x, Box::new(l)),
                right: (y, Box::new(r)),
            }
        }
        other => {
            let new = other
                .premises()
                .into_iter()
                .map(|q| subst(q, name, repl, open))
                .collect();
            other.with_premises(new)
        }
    }
}

/// Substitutes inside the scope of a binder `x`.
fn under_binder(
    x: &str,
    body: &Proof,
    name: &str,
    repl: &Proof,
    open: &BTreeSet<String>,
) -> (String, Proof) {
    if x == name {
        // `name` is rebound here: inner uses refer to the inner assumption.
        return (x.to_string(), body.clone());
    }
    if open.contains(x) {
        // Renaming `x` avoids capturing the replacement's own assumption `x`.
        let mut taken = body.open_assumptions();
        taken.extend(open.iter().cloned());
        taken.insert(name.to_string());
        let mut fresh = format!("{x}'");
        while taken.contains(&fresh) {
            fresh.push('\'');
        }
        let renamed = subst(body, x, &Proof::Hyp(fresh.clone()), &BTreeSet::new());
        return (fresh, subst(&renamed, name, repl, open));
    }
    (x.to_string(), subst(body, name, repl, open))
}

// ANCHOR: contract
/// If `p` is itself a detour, removes it and names the reduction.
fn contract(p: &Proof) -> Option<(Proof, &'static str)> {
    match p {
        Proof::AndE1(q) => match &**q {
            // ∧I followed by ∧E1: keep the first component, drop the second.
            Proof::AndI(a, _) => Some(((**a).clone(), "∧I/∧E1")),
            _ => None,
        },
        Proof::AndE2(q) => match &**q {
            Proof::AndI(_, b) => Some(((**b).clone(), "∧I/∧E2")),
            _ => None,
        },
        Proof::ImpE(f, arg) => match &**f {
            // →I followed by →E: plug the argument into the body.
            Proof::ImpI { name, body, .. } => {
                Some((substitute(body, name, arg), "→I/→E"))
            }
            _ => None,
        },
        Proof::OrE {
            scrutinee,
            left,
            right,
        } => match &**scrutinee {
            // ∨I followed by ∨E: we know which case happened; take it.
            Proof::OrI1(a, _) => Some((substitute(&left.1, &left.0, a), "∨I1/∨E")),
            Proof::OrI2(_, b) => Some((substitute(&right.1, &right.0, b), "∨I2/∨E")),
            _ => None,
        },
        // tonk-I followed by tonk-E is a detour, but there is nothing to
        // reduce it to: the premise proves A and we need B.
        _ => None,
    }
}
// ANCHOR_END: contract

/// One reduction step: the first detour found, root first, then the
/// premises from left to right.
pub fn step(p: &Proof) -> Option<(Proof, &'static str)> {
    if let Some(done) = contract(p) {
        return Some(done);
    }
    let premises = p.premises();
    for (i, q) in premises.iter().enumerate() {
        if let Some((reduced, rule)) = step(q) {
            let mut new: Vec<Proof> = premises.iter().map(|q| (*q).clone()).collect();
            new[i] = reduced;
            return Some((p.with_premises(new), rule));
        }
    }
    None
}

/// The detours in a proof, reducible or not, root first.
pub fn detours(p: &Proof) -> Vec<&'static str> {
    let here = match p {
        Proof::AndE1(q) | Proof::AndE2(q) if matches!(**q, Proof::AndI(..)) => {
            Some("∧I/∧E")
        }
        Proof::ImpE(q, _) if matches!(**q, Proof::ImpI { .. }) => Some("→I/→E"),
        Proof::OrE { scrutinee, .. }
            if matches!(**scrutinee, Proof::OrI1(..) | Proof::OrI2(..)) =>
        {
            Some("∨I/∨E")
        }
        Proof::TonkE(q) if matches!(**q, Proof::TonkI(..)) => Some("tonk-I/tonk-E"),
        _ => None,
    };
    let mut out: Vec<&'static str> = here.into_iter().collect();
    for q in p.premises() {
        out.extend(detours(q));
    }
    out
}

// ANCHOR: normalize
/// The result of normalizing a proof.
pub struct Normalized {
    pub proof: Proof,
    /// The reductions performed, in order.
    pub steps: Vec<&'static str>,
    /// Detours that remain because no reduction applies (only tonk's).
    pub stuck: Vec<&'static str>,
}

/// Reduces detours until none is left (or `max_steps` is reached).
pub fn normalize(p: &Proof, max_steps: usize) -> Normalized {
    let mut proof = p.clone();
    let mut steps = Vec::new();
    while steps.len() < max_steps {
        match step(&proof) {
            Some((next, rule)) => {
                proof = next;
                steps.push(rule);
            }
            None => break,
        }
    }
    let stuck = detours(&proof);
    Normalized {
        proof,
        steps,
        stuck,
    }
}
// ANCHOR_END: normalize

// ANCHOR: subformulas
/// The formulas in a derivation that are *not* subformulas of its conclusion
/// or of its open assumptions. In a normal derivation this list is empty:
/// that is the subformula property.
pub fn foreign_formulas(d: &Derivation) -> BTreeSet<Formula> {
    let mut allowed = d.conclusion.subformulas();
    for (_, a) in &d.context {
        allowed.extend(a.subformulas());
    }
    d.nodes()
        .into_iter()
        .map(|node| &node.conclusion)
        .filter(|c| !allowed.contains(*c))
        .cloned()
        .collect()
}
// ANCHOR_END: subformulas

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::Checker;
    use crate::proof::*;

    fn f(s: &str) -> Formula {
        s.parse().unwrap()
    }

    /// `A ∧ B ⊢ B ∧ A` through a lemma `A ∧ B → B ∧ A` applied to `u`.
    fn with_lemma() -> Proof {
        let lemma = imp_i("x", f("A ∧ B"), and_i(and_e2(hyp("x")), and_e1(hyp("x"))));
        imp_e(lemma, hyp("u"))
    }

    #[test]
    fn beta_for_implication() {
        let n = normalize(&with_lemma(), 10);
        assert_eq!(n.steps, vec!["→I/→E"]);
        assert_eq!(n.proof, and_i(and_e2(hyp("u")), and_e1(hyp("u"))));
        assert!(n.stuck.is_empty());
    }

    #[test]
    fn normalization_preserves_the_sequent() {
        let hyps = [("u", f("A ∧ B"))];
        let checker = Checker::intuitionistic();
        let before = checker.check(&hyps, &with_lemma()).unwrap();
        let after = checker
            .check(&hyps, &normalize(&with_lemma(), 10).proof)
            .unwrap();
        assert_eq!(before.sequent(), after.sequent());
        assert!(!foreign_formulas(&before).is_empty());
        assert!(foreign_formulas(&after).is_empty());
    }

    #[test]
    fn beta_for_conjunction_and_disjunction() {
        let p = and_e1(and_i(hyp("a"), hyp("b")));
        assert_eq!(normalize(&p, 10).proof, hyp("a"));
        let q = or_e(
            or_i2(f("A"), hyp("b")),
            "x",
            or_i2(f("B"), hyp("x")),
            "y",
            or_i1(hyp("y"), f("A")),
        );
        let n = normalize(&q, 10);
        assert_eq!(n.steps, vec!["∨I2/∨E"]);
        assert_eq!(n.proof, or_i1(hyp("b"), f("A")));
    }

    #[test]
    fn substitution_avoids_capture() {
        // (λx:B. λa:A. x) applied to the open assumption `a`:
        // the inner binder `a` must be renamed.
        let k = imp_i("x", f("B"), imp_i("a", f("A"), hyp("x")));
        let p = imp_e(k, hyp("a"));
        let n = normalize(&p, 10);
        assert_eq!(n.proof, imp_i("a'", f("A"), hyp("a")));
        let d = Checker::intuitionistic()
            .check(&[("a", f("B"))], &n.proof)
            .unwrap();
        assert_eq!(d.conclusion, f("A → B"));
    }

    #[test]
    fn nested_detours_all_reduce() {
        // (λf. f u) (λx. x) with u : A
        let id = imp_i("x", f("A"), hyp("x"));
        let apply_to_u = imp_i("g", f("A → A"), imp_e(hyp("g"), hyp("u")));
        let p = imp_e(apply_to_u, id);
        let n = normalize(&p, 10);
        assert_eq!(n.proof, hyp("u"));
        assert_eq!(n.steps.len(), 2);
    }

    #[test]
    fn tonk_detour_is_stuck() {
        let p = tonk_e(tonk_i(top_i(), Formula::Bot));
        let n = normalize(&p, 10);
        assert!(n.steps.is_empty());
        assert_eq!(n.stuck, vec!["tonk-I/tonk-E"]);
    }
}
