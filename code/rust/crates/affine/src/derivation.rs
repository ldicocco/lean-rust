//! Derivation trees, reconstructed by the checker from its input and output
//! contexts, and printed as indented text.

use crate::syntax::Ty;

// ANCHOR: derivation
/// A node of a typing derivation: `ctx ⊢ expr : ty`, justified by `rule`
/// from the premises. The context is the part of the checker's input context
/// that this subterm actually used (the soundness theorem of Chapter 22 says
/// that this part is enough to derive the judgment).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Derivation {
    pub rule: &'static str,
    pub ctx: Vec<(String, Ty)>,
    pub expr: String,
    pub ty: Ty,
    pub premises: Vec<Derivation>,
}
// ANCHOR_END: derivation

impl Derivation {
    /// The judgment, as `x: A, y: B ⊢ e : T`.
    pub fn judgment(&self) -> String {
        let ctx: Vec<String> =
            self.ctx.iter().map(|(x, t)| format!("{x}: {t}")).collect();
        let ctx = ctx.join(", ");
        let sep = if ctx.is_empty() { "" } else { " " };
        format!("{ctx}{sep}⊢ {} : {}", self.expr, self.ty)
    }

    /// The judgment with the context written as variable names only:
    /// `x, y ⊢ e : T`.
    pub fn judgment_compact(&self) -> String {
        let ctx: Vec<&str> = self.ctx.iter().map(|(x, _)| x.as_str()).collect();
        let ctx = ctx.join(", ");
        let sep = if ctx.is_empty() { "" } else { " " };
        format!("{ctx}{sep}⊢ {} : {}", self.expr, self.ty)
    }

    /// The whole tree, one judgment per line, premises indented below their
    /// conclusion.
    pub fn render(&self) -> String {
        let mut out = String::new();
        self.render_into(&mut out, 0, false);
        out
    }

    /// The whole tree, with the contexts as variable names only.
    pub fn render_compact(&self) -> String {
        let mut out = String::new();
        self.render_into(&mut out, 0, true);
        out
    }

    fn render_into(&self, out: &mut String, depth: usize, compact: bool) {
        let judgment = if compact {
            self.judgment_compact()
        } else {
            self.judgment()
        };
        out.push_str(&format!(
            "{:indent$}[{}] {}\n",
            "",
            self.rule,
            judgment,
            indent = 2 * depth
        ));
        for p in &self.premises {
            p.render_into(out, depth + 1, compact);
        }
    }

    /// The number of rule instances in the tree.
    pub fn size(&self) -> usize {
        1 + self.premises.iter().map(Derivation::size).sum::<usize>()
    }
}
