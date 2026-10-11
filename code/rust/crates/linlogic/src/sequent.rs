//! Sequents `Γ ⊢ C`, with the context treated as a multiset.

use std::fmt;

use crate::formula::{Formula, ParseError, parse_formula};

// ANCHOR: sequent
/// A sequent `Γ ⊢ C` of intuitionistic linear logic: a multiset of resources
/// `Γ` (the context) and one goal `C`. The order of the context is irrelevant
/// (exchange is built in); its multiplicities are not.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Sequent {
    pub context: Vec<Formula>,
    pub goal: Formula,
}
// ANCHOR_END: sequent

impl Sequent {
    pub fn new(context: Vec<Formula>, goal: Formula) -> Sequent {
        Sequent { context, goal }
    }

    /// The same sequent with its context sorted: two sequents that differ
    /// only by the order of their contexts have the same normal form.
    pub fn normalized(&self) -> Sequent {
        let mut context = self.context.clone();
        context.sort();
        Sequent {
            context,
            goal: self.goal.clone(),
        }
    }

    /// The total size of all formulas: it decreases with every backward step.
    pub fn size(&self) -> usize {
        self.context.iter().map(Formula::size).sum::<usize>() + self.goal.size()
    }
}

impl fmt::Display for Sequent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let context: Vec<String> = self.context.iter().map(|a| a.to_string()).collect();
        if context.is_empty() {
            write!(f, "⊢ {}", self.goal)
        } else {
            write!(f, "{} ⊢ {}", context.join(", "), self.goal)
        }
    }
}

/// Splits `text` at the commas that are not inside parentheses.
fn split_top_level(text: &str) -> Vec<&str> {
    let mut parts = Vec::new();
    let mut depth = 0;
    let mut start = 0;
    for (i, c) in text.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            ',' if depth == 0 => {
                parts.push(&text[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    parts.push(&text[start..]);
    parts
}

/// Parses `A, B |- C` (or with `⊢`). The context may be empty: `|- C`.
pub fn parse_sequent(input: &str) -> Result<Sequent, ParseError> {
    let (left, right) = match input.split_once("|-").or_else(|| input.split_once('⊢'))
    {
        Some(sides) => sides,
        None => {
            return Err(ParseError {
                position: 0,
                message: "expected '|-'".to_string(),
            });
        }
    };
    let mut context = Vec::new();
    if !left.trim().is_empty() {
        for part in split_top_level(left) {
            context.push(parse_formula(part)?);
        }
    }
    Ok(Sequent {
        context,
        goal: parse_formula(right)?,
    })
}

/// Removes one occurrence of `item` from `multiset`, if there is one.
pub fn remove_one(multiset: &[Formula], item: &Formula) -> Option<Vec<Formula>> {
    let index = multiset.iter().position(|x| x == item)?;
    let mut rest = multiset.to_vec();
    rest.remove(index);
    Some(rest)
}

/// Multiset equality: the same elements with the same multiplicities.
pub fn same_multiset(a: &[Formula], b: &[Formula]) -> bool {
    let mut a = a.to_vec();
    let mut b = b.to_vec();
    a.sort();
    b.sort();
    a == b
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_and_print() {
        let s = parse_sequent("coin, coin -o (coffee & tea) |- coffee").unwrap();
        assert_eq!(s.to_string(), "coin, coin ⊸ (coffee & tea) ⊢ coffee");
        let empty = parse_sequent("|- a -o a").unwrap();
        assert!(empty.context.is_empty());
        assert_eq!(empty.to_string(), "⊢ a ⊸ a");
        assert!(parse_sequent("a, b").is_err());
    }

    #[test]
    fn multisets() {
        let a = Formula::atom("a");
        let b = Formula::atom("b");
        assert!(same_multiset(
            &[a.clone(), b.clone()],
            &[b.clone(), a.clone()]
        ));
        assert!(!same_multiset(&[a.clone(), a.clone()], &[a.clone()]));
        assert_eq!(
            remove_one(&[a.clone(), b.clone(), a.clone()], &a),
            Some(vec![b, a])
        );
    }
}
