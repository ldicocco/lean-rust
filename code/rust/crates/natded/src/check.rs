//! The proof checker.
//!
//! [`Checker::check`] walks a [`Proof`] from the leaves to the root, computes
//! the formula each node proves, and checks that every rule is applied to
//! premises of the right shape. The result is a [`Derivation`]: the same tree,
//! with the full sequent `Γ ⊢ A` written at every node. When a rule is
//! misapplied, the result is a [`CheckError`] that says which rule, where in
//! the tree, and what was expected.

use crate::formula::Formula;
use crate::proof::Proof;
use std::fmt;

// ANCHOR: rule
/// The rules of natural deduction, plus Prior's two rules for `tonk`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rule {
    Hyp,
    TopI,
    BotE,
    AndI,
    AndE1,
    AndE2,
    OrI1,
    OrI2,
    OrE,
    ImpI,
    ImpE,
    TonkI,
    TonkE,
}
// ANCHOR_END: rule

impl Rule {
    /// The rule applied at the root of a proof.
    pub fn of(proof: &Proof) -> Rule {
        match proof {
            Proof::Hyp(_) => Rule::Hyp,
            Proof::TopI => Rule::TopI,
            Proof::BotE(..) => Rule::BotE,
            Proof::AndI(..) => Rule::AndI,
            Proof::AndE1(..) => Rule::AndE1,
            Proof::AndE2(..) => Rule::AndE2,
            Proof::OrI1(..) => Rule::OrI1,
            Proof::OrI2(..) => Rule::OrI2,
            Proof::OrE { .. } => Rule::OrE,
            Proof::ImpI { .. } => Rule::ImpI,
            Proof::ImpE(..) => Rule::ImpE,
            Proof::TonkI(..) => Rule::TonkI,
            Proof::TonkE(..) => Rule::TonkE,
        }
    }
}

impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Rule::Hyp => "Hyp",
            Rule::TopI => "⊤I",
            Rule::BotE => "⊥E",
            Rule::AndI => "∧I",
            Rule::AndE1 => "∧E1",
            Rule::AndE2 => "∧E2",
            Rule::OrI1 => "∨I1",
            Rule::OrI2 => "∨I2",
            Rule::OrE => "∨E",
            Rule::ImpI => "→I",
            Rule::ImpE => "→E",
            Rule::TonkI => "tonk-I",
            Rule::TonkE => "tonk-E",
        };
        write!(f, "{name}")
    }
}

/// The assumptions in scope at a node: names and formulas, oldest first.
pub type Context = Vec<(String, Formula)>;

// ANCHOR: derivation
/// A checked proof: every node carries the sequent it establishes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Derivation {
    pub rule: Rule,
    /// The assumption used (Hyp) or discharged (→I, ∨E).
    pub labels: Vec<String>,
    pub context: Context,
    pub conclusion: Formula,
    pub premises: Vec<Derivation>,
}
// ANCHOR_END: derivation

// ANCHOR: error
/// What went wrong, and where.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckError {
    /// The rule that was misapplied.
    pub rule: Rule,
    /// The position of that rule in the tree: premise numbers from the root,
    /// so `[2, 1]` is the first premise of the second premise of the root.
    pub path: Vec<usize>,
    pub kind: ErrorKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    /// Hyp names an assumption that is not available at this point.
    UnknownAssumption {
        name: String,
        available: Vec<String>,
    },
    /// A premise does not have the shape the rule needs.
    WrongShape {
        premise: &'static str,
        expected: &'static str,
        found: Formula,
    },
    /// →E: the argument does not prove the antecedent of the implication.
    ArgumentMismatch {
        implication: Formula,
        found: Formula,
    },
    /// ∨E: the two cases prove different formulas.
    CasesDisagree { left: Formula, right: Formula },
    /// The rule is not part of the logic being checked.
    RuleNotInLogic,
    /// The proof is correct, but it proves something else.
    WrongConclusion { goal: Formula, found: Formula },
}
// ANCHOR_END: error

impl fmt::Display for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let place = if self.path.is_empty() {
            "root".to_string()
        } else {
            let parts: Vec<String> = self.path.iter().map(|n| n.to_string()).collect();
            format!("root.{}", parts.join("."))
        };
        write!(f, "error in {} at {place}:\n  ", self.rule)?;
        match &self.kind {
            ErrorKind::UnknownAssumption { name, available } => {
                write!(f, "no assumption named `{name}` is available here")?;
                if available.is_empty() {
                    write!(f, " (none are)")
                } else {
                    write!(f, " (available: {})", available.join(", "))
                }
            }
            ErrorKind::WrongShape {
                premise,
                expected,
                found,
            } => write!(
                f,
                "the {premise} must prove {expected}, but it proves `{found}`"
            ),
            ErrorKind::ArgumentMismatch { implication, found } => {
                let antecedent = match implication {
                    Formula::Imp(a, _) => a.to_string(),
                    other => other.to_string(),
                };
                write!(
                    f,
                    "the implication is `{implication}`, so the argument must prove \
                     `{antecedent}`, but it proves `{found}`"
                )
            }
            ErrorKind::CasesDisagree { left, right } => write!(
                f,
                "both cases must prove the same formula, but the first proves `{left}` \
                 and the second proves `{right}`"
            ),
            ErrorKind::RuleNotInLogic => {
                write!(
                    f,
                    "this rule is not part of intuitionistic natural deduction"
                )
            }
            ErrorKind::WrongConclusion { goal, found } => {
                write!(f, "the proof proves `{found}`, but the goal is `{goal}`")
            }
        }
    }
}

// ANCHOR: checker
/// A proof checker. `Checker::intuitionistic()` knows the rules of Chapter 4;
/// `Checker::with_tonk()` also accepts Prior's tonk-I and tonk-E.
#[derive(Clone, Copy, Debug)]
pub struct Checker {
    tonk: bool,
}

impl Checker {
    pub fn intuitionistic() -> Checker {
        Checker { tonk: false }
    }

    pub fn with_tonk() -> Checker {
        Checker { tonk: true }
    }

    /// Checks `proof` under the named assumptions `hyps`, and returns the
    /// derivation with the sequent it proves at every node.
    pub fn check(
        &self,
        hyps: &[(&str, Formula)],
        proof: &Proof,
    ) -> Result<Derivation, CheckError> {
        let context: Context = hyps
            .iter()
            .map(|(name, a)| (name.to_string(), a.clone()))
            .collect();
        self.infer(&context, proof, &mut Vec::new())
    }

    /// Checks `proof` and also that it proves `goal`.
    pub fn prove(
        &self,
        hyps: &[(&str, Formula)],
        goal: &Formula,
        proof: &Proof,
    ) -> Result<Derivation, CheckError> {
        let derivation = self.check(hyps, proof)?;
        if &derivation.conclusion != goal {
            return Err(CheckError {
                rule: derivation.rule,
                path: vec![],
                kind: ErrorKind::WrongConclusion {
                    goal: goal.clone(),
                    found: derivation.conclusion,
                },
            });
        }
        Ok(derivation)
    }
    // ANCHOR_END: checker

    // ANCHOR: infer
    /// Computes what `proof` proves in `context`. `path` is the position of
    /// `proof` in the whole tree, for error messages.
    fn infer(
        &self,
        context: &Context,
        proof: &Proof,
        path: &mut Vec<usize>,
    ) -> Result<Derivation, CheckError> {
        let rule = Rule::of(proof);
        let fail = |path: &Vec<usize>, kind| CheckError {
            rule,
            path: path.clone(),
            kind,
        };
        let mut premises = Vec::new();
        let mut labels = Vec::new();
        let conclusion = match proof {
            Proof::Hyp(name) => {
                // The most recent assumption with this name wins.
                match context.iter().rev().find(|(n, _)| n == name) {
                    Some((_, a)) => {
                        labels.push(name.clone());
                        a.clone()
                    }
                    None => {
                        let available =
                            context.iter().map(|(n, _)| n.clone()).collect();
                        let name = name.clone();
                        return Err(fail(
                            path,
                            ErrorKind::UnknownAssumption { name, available },
                        ));
                    }
                }
            }
            Proof::TopI => Formula::Top,
            Proof::BotE(p, goal) => {
                let d = self.premise(context, p, path, 1)?;
                if d.conclusion != Formula::Bot {
                    let found = d.conclusion;
                    let kind = shape("premise", "`⊥`", found);
                    return Err(fail(path, kind));
                }
                premises.push(d);
                goal.clone()
            }
            Proof::AndI(p, q) => {
                let d1 = self.premise(context, p, path, 1)?;
                let d2 = self.premise(context, q, path, 2)?;
                let c = Formula::and(d1.conclusion.clone(), d2.conclusion.clone());
                premises.extend([d1, d2]);
                c
            }
            // ANCHOR: infer_and_e
            Proof::AndE1(p) | Proof::AndE2(p) => {
                let d = self.premise(context, p, path, 1)?;
                let Formula::And(a, b) = &d.conclusion else {
                    let found = d.conclusion;
                    let kind = shape("premise", "a conjunction", found);
                    return Err(fail(path, kind));
                };
                let c = if rule == Rule::AndE1 { a } else { b };
                let c = (**c).clone();
                premises.push(d);
                c
            }
            // ANCHOR_END: infer_and_e
            Proof::OrI1(p, right) => {
                let d = self.premise(context, p, path, 1)?;
                let c = Formula::or(d.conclusion.clone(), right.clone());
                premises.push(d);
                c
            }
            Proof::OrI2(left, p) => {
                let d = self.premise(context, p, path, 1)?;
                let c = Formula::or(left.clone(), d.conclusion.clone());
                premises.push(d);
                c
            }
            Proof::OrE {
                scrutinee,
                left,
                right,
            } => {
                let d0 = self.premise(context, scrutinee, path, 1)?;
                let Formula::Or(a, b) = &d0.conclusion else {
                    let found = d0.conclusion;
                    let kind = shape("first premise", "a disjunction", found);
                    return Err(fail(path, kind));
                };
                // Each case may use its disjunct as an assumption.
                let ctx_left = extended(context, &left.0, a);
                let ctx_right = extended(context, &right.0, b);
                let d1 = self.premise(&ctx_left, &left.1, path, 2)?;
                let d2 = self.premise(&ctx_right, &right.1, path, 3)?;
                if d1.conclusion != d2.conclusion {
                    let kind = ErrorKind::CasesDisagree {
                        left: d1.conclusion,
                        right: d2.conclusion,
                    };
                    return Err(fail(path, kind));
                }
                let c = d1.conclusion.clone();
                labels.extend([left.0.clone(), right.0.clone()]);
                premises.extend([d0, d1, d2]);
                c
            }
            // ANCHOR: infer_imp
            Proof::ImpI {
                name,
                assumption,
                body,
            } => {
                // The body may use the new assumption; the conclusion may not.
                let inner = extended(context, name, assumption);
                let d = self.premise(&inner, body, path, 1)?;
                let c = Formula::imp(assumption.clone(), d.conclusion.clone());
                labels.push(name.clone());
                premises.push(d);
                c
            }
            Proof::ImpE(p, q) => {
                let d1 = self.premise(context, p, path, 1)?;
                let Formula::Imp(a, b) = &d1.conclusion else {
                    let found = d1.conclusion;
                    let kind = shape("first premise", "an implication", found);
                    return Err(fail(path, kind));
                };
                let d2 = self.premise(context, q, path, 2)?;
                if d2.conclusion != **a {
                    let kind = ErrorKind::ArgumentMismatch {
                        implication: d1.conclusion.clone(),
                        found: d2.conclusion,
                    };
                    return Err(fail(path, kind));
                }
                let c = (**b).clone();
                premises.extend([d1, d2]);
                c
            }
            // ANCHOR_END: infer_imp
            Proof::TonkI(p, right) => {
                if !self.tonk {
                    return Err(fail(path, ErrorKind::RuleNotInLogic));
                }
                let d = self.premise(context, p, path, 1)?;
                let c = Formula::tonk(d.conclusion.clone(), right.clone());
                premises.push(d);
                c
            }
            Proof::TonkE(p) => {
                if !self.tonk {
                    return Err(fail(path, ErrorKind::RuleNotInLogic));
                }
                let d = self.premise(context, p, path, 1)?;
                let Formula::Tonk(_, b) = &d.conclusion else {
                    let found = d.conclusion;
                    let kind = shape("premise", "a `tonk` formula", found);
                    return Err(fail(path, kind));
                };
                let c = (**b).clone();
                premises.push(d);
                c
            }
        };
        Ok(Derivation {
            rule,
            labels,
            context: context.clone(),
            conclusion,
            premises,
        })
    }
    // ANCHOR_END: infer

    /// Checks the `index`-th premise (counting from 1) of the node at `path`.
    fn premise(
        &self,
        context: &Context,
        proof: &Proof,
        path: &mut Vec<usize>,
        index: usize,
    ) -> Result<Derivation, CheckError> {
        path.push(index);
        let result = self.infer(context, proof, path);
        path.pop();
        result
    }
}

fn shape(premise: &'static str, expected: &'static str, found: Formula) -> ErrorKind {
    ErrorKind::WrongShape {
        premise,
        expected,
        found,
    }
}

fn extended(context: &Context, name: &str, a: &Formula) -> Context {
    let mut out = context.clone();
    out.push((name.to_string(), a.clone()));
    out
}

impl Derivation {
    /// The sequent `Γ ⊢ A` established at the root.
    pub fn sequent(&self) -> String {
        let hyps: Vec<String> =
            self.context.iter().map(|(_, a)| a.to_string()).collect();
        if hyps.is_empty() {
            format!("⊢ {}", self.conclusion)
        } else {
            format!("{} ⊢ {}", hyps.join(", "), self.conclusion)
        }
    }

    /// Every node of the derivation, root first.
    pub fn nodes(&self) -> Vec<&Derivation> {
        let mut out = vec![self];
        for p in &self.premises {
            out.extend(p.nodes());
        }
        out
    }

    fn lines(&self, prefix: &str, child_prefix: &str, out: &mut Vec<(String, String)>) {
        let mut rule = self.rule.to_string();
        for label in &self.labels {
            rule.push(' ');
            rule.push_str(label);
        }
        out.push((format!("{prefix}{}", self.sequent()), rule));
        let n = self.premises.len();
        for (i, p) in self.premises.iter().enumerate() {
            let last = i + 1 == n;
            let branch = if last { "└─ " } else { "├─ " };
            let cont = if last { "   " } else { "│  " };
            p.lines(
                &format!("{child_prefix}{branch}"),
                &format!("{child_prefix}{cont}"),
                out,
            );
        }
    }
}

// ANCHOR: tree_display
/// Prints the derivation as a tree, root first, one sequent per line, with
/// the rule (and the assumption it uses or discharges) in a column on the right.
impl fmt::Display for Derivation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut lines = Vec::new();
        self.lines("", "", &mut lines);
        let width = lines
            .iter()
            .map(|(l, _)| l.chars().count())
            .max()
            .unwrap_or(0);
        for (left, rule) in lines {
            let pad = width - left.chars().count();
            writeln!(f, "{left}{}   {rule}", " ".repeat(pad))?;
        }
        Ok(())
    }
}
// ANCHOR_END: tree_display

#[cfg(test)]
mod tests {
    use super::*;
    use crate::proof::*;

    fn f(s: &str) -> Formula {
        s.parse().unwrap()
    }

    fn and_comm() -> Proof {
        imp_i("u", f("A ∧ B"), and_i(and_e2(hyp("u")), and_e1(hyp("u"))))
    }

    #[test]
    fn checks_and_comm() {
        let d = Checker::intuitionistic().check(&[], &and_comm()).unwrap();
        assert_eq!(d.conclusion, f("A ∧ B → B ∧ A"));
        assert_eq!(d.sequent(), "⊢ A ∧ B → B ∧ A");
        assert_eq!(d.premises[0].sequent(), "A ∧ B ⊢ B ∧ A");
        assert_eq!(d.nodes().len(), 6);
    }

    #[test]
    fn checks_or_elimination() {
        // (A → B) → A ∨ C → B ∨ C
        let p = imp_i(
            "f",
            f("A → B"),
            imp_i(
                "d",
                f("A ∨ C"),
                or_e(
                    hyp("d"),
                    "a",
                    or_i1(imp_e(hyp("f"), hyp("a")), f("C")),
                    "c",
                    or_i2(f("B"), hyp("c")),
                ),
            ),
        );
        let goal = f("(A → B) → A ∨ C → B ∨ C");
        assert!(Checker::intuitionistic().prove(&[], &goal, &p).is_ok());
    }

    #[test]
    fn rejects_projection_from_implication() {
        let err = Checker::intuitionistic()
            .check(&[("u", f("A → B"))], &and_e1(hyp("u")))
            .unwrap_err();
        assert_eq!(err.rule, Rule::AndE1);
        assert!(matches!(err.kind, ErrorKind::WrongShape { .. }));
        assert_eq!(
            err.to_string(),
            "error in ∧E1 at root:\n  the premise must prove a conjunction, \
             but it proves `A → B`"
        );
    }

    #[test]
    fn rejects_discharged_assumption_outside_its_scope() {
        // (A → A) ∧ A: the second component tries to use `u` after →I closed it.
        let p = and_i(imp_i("u", f("A"), hyp("u")), hyp("u"));
        let err = Checker::intuitionistic().check(&[], &p).unwrap_err();
        assert_eq!(err.path, vec![2]);
        assert!(matches!(err.kind, ErrorKind::UnknownAssumption { .. }));
    }

    #[test]
    fn rejects_wrong_argument() {
        let p = imp_e(hyp("f"), hyp("b"));
        let hyps = [("f", f("A → C")), ("b", f("B"))];
        let err = Checker::intuitionistic().check(&hyps, &p).unwrap_err();
        assert!(matches!(err.kind, ErrorKind::ArgumentMismatch { .. }));
    }

    #[test]
    fn rejects_disagreeing_cases() {
        let p = or_e(hyp("d"), "x", hyp("x"), "y", hyp("y"));
        let err = Checker::intuitionistic()
            .check(&[("d", f("A ∨ B"))], &p)
            .unwrap_err();
        assert!(matches!(err.kind, ErrorKind::CasesDisagree { .. }));
    }

    #[test]
    fn rejects_wrong_goal() {
        let err = Checker::intuitionistic()
            .prove(&[], &f("B ∧ A → A ∧ B"), &and_comm())
            .unwrap_err();
        assert!(matches!(err.kind, ErrorKind::WrongConclusion { .. }));
    }

    #[test]
    fn tonk_only_with_tonk() {
        let p = tonk_e(tonk_i(top_i(), Formula::Bot));
        let err = Checker::intuitionistic().check(&[], &p).unwrap_err();
        assert_eq!(err.kind, ErrorKind::RuleNotInLogic);
        let d = Checker::with_tonk().check(&[], &p).unwrap();
        assert_eq!(d.conclusion, Formula::Bot);
    }

    #[test]
    fn inner_assumption_shadows_outer() {
        // u : A outside, u : B inside: Hyp u inside refers to B.
        let p = imp_i("u", f("B"), hyp("u"));
        let d = Checker::intuitionistic()
            .check(&[("u", f("A"))], &p)
            .unwrap();
        assert_eq!(d.conclusion, f("B → B"));
    }
}
