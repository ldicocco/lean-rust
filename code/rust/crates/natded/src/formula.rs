//! Propositional formulas: the syntax of Chapter 4.
//!
//! A formula is a tree. `¬A` is not a separate case: it is `A → ⊥`, and the
//! printer shows it as `¬A`. The `Tonk` case exists only so that Chapter 4 can
//! add Prior's connective to the checker and watch what happens.

use std::collections::BTreeSet;
use std::fmt;
use std::str::FromStr;

// ANCHOR: formula
/// A formula of propositional logic.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Formula {
    /// An atomic proposition such as `A` or `Raining`.
    Atom(String),
    /// Truth, `⊤`.
    Top,
    /// Falsity, `⊥`.
    Bot,
    /// Conjunction, `A ∧ B`.
    And(Box<Formula>, Box<Formula>),
    /// Disjunction, `A ∨ B`.
    Or(Box<Formula>, Box<Formula>),
    /// Implication, `A → B`. Negation `¬A` is `A → ⊥`.
    Imp(Box<Formula>, Box<Formula>),
    /// Prior's `A tonk B`: not a real connective, see Chapter 4.
    Tonk(Box<Formula>, Box<Formula>),
}
// ANCHOR_END: formula

impl Formula {
    /// The atom with the given name.
    pub fn atom(name: &str) -> Formula {
        Formula::Atom(name.to_string())
    }

    /// `a ∧ b`.
    pub fn and(a: Formula, b: Formula) -> Formula {
        Formula::And(Box::new(a), Box::new(b))
    }

    /// `a ∨ b`.
    pub fn or(a: Formula, b: Formula) -> Formula {
        Formula::Or(Box::new(a), Box::new(b))
    }

    /// `a → b`.
    pub fn imp(a: Formula, b: Formula) -> Formula {
        Formula::Imp(Box::new(a), Box::new(b))
    }

    /// `¬a`, which is `a → ⊥`.
    pub fn not(a: Formula) -> Formula {
        Formula::imp(a, Formula::Bot)
    }

    /// `a tonk b`.
    pub fn tonk(a: Formula, b: Formula) -> Formula {
        Formula::Tonk(Box::new(a), Box::new(b))
    }

    /// The names of the atoms that occur in the formula, in sorted order.
    pub fn atoms(&self) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        self.collect_atoms(&mut out);
        out
    }

    fn collect_atoms(&self, out: &mut BTreeSet<String>) {
        match self {
            Formula::Atom(name) => {
                out.insert(name.clone());
            }
            Formula::Top | Formula::Bot => {}
            Formula::And(a, b)
            | Formula::Or(a, b)
            | Formula::Imp(a, b)
            | Formula::Tonk(a, b) => {
                a.collect_atoms(out);
                b.collect_atoms(out);
            }
        }
    }

    /// Every subformula, including the formula itself.
    pub fn subformulas(&self) -> BTreeSet<Formula> {
        let mut out = BTreeSet::new();
        self.collect_subformulas(&mut out);
        out
    }

    fn collect_subformulas(&self, out: &mut BTreeSet<Formula>) {
        out.insert(self.clone());
        match self {
            Formula::Atom(_) | Formula::Top | Formula::Bot => {}
            Formula::And(a, b)
            | Formula::Or(a, b)
            | Formula::Imp(a, b)
            | Formula::Tonk(a, b) => {
                a.collect_subformulas(out);
                b.collect_subformulas(out);
            }
        }
    }

    /// Does the formula mention `tonk` anywhere?
    pub fn mentions_tonk(&self) -> bool {
        match self {
            Formula::Atom(_) | Formula::Top | Formula::Bot => false,
            Formula::Tonk(_, _) => true,
            Formula::And(a, b) | Formula::Or(a, b) | Formula::Imp(a, b) => {
                a.mentions_tonk() || b.mentions_tonk()
            }
        }
    }

    /// Binding strength for printing: higher binds tighter.
    fn precedence(&self) -> u8 {
        match self {
            Formula::Atom(_) | Formula::Top | Formula::Bot => 5,
            Formula::Imp(_, b) if **b == Formula::Bot => 4, // ¬A
            Formula::And(_, _) => 3,
            Formula::Or(_, _) => 2,
            Formula::Imp(_, _) | Formula::Tonk(_, _) => 1,
        }
    }
}

// ANCHOR: display
/// Prints with the usual conventions: `¬` binds tightest, then `∧`, then `∨`,
/// then `→`; the binary connectives group to the right, so `A → B → C` means
/// `A → (B → C)`. Parentheses appear only where they are needed.
impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Print `child`, in parentheses if it binds more loosely than `min`.
        let sub = |f: &mut fmt::Formatter<'_>, child: &Formula, min: u8| {
            if child.precedence() < min {
                write!(f, "({child})")
            } else {
                write!(f, "{child}")
            }
        };
        match self {
            Formula::Atom(name) => write!(f, "{name}"),
            Formula::Top => write!(f, "⊤"),
            Formula::Bot => write!(f, "⊥"),
            Formula::Imp(a, b) if **b == Formula::Bot => {
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
            Formula::Tonk(a, b) => {
                sub(f, a, 2)?;
                write!(f, " tonk ")?;
                sub(f, b, 2)
            }
        }
    }
}
// ANCHOR_END: display

// ---------------------------------------------------------------------------
// Parsing
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq)]
enum Token {
    Name(String),
    Top,
    Bot,
    And,
    Or,
    Imp,
    Not,
    Tonk,
    LParen,
    RParen,
}

fn tokenize(input: &str) -> Result<Vec<Token>, String> {
    let chars: Vec<char> = input.chars().collect();
    let mut tokens = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        let two: String = chars[i..chars.len().min(i + 2)].iter().collect();
        let (token, width) = match c {
            '(' => (Token::LParen, 1),
            ')' => (Token::RParen, 1),
            '∧' | '&' => (Token::And, 1),
            '∨' | '|' => (Token::Or, 1),
            '→' => (Token::Imp, 1),
            '¬' | '~' | '!' => (Token::Not, 1),
            '⊤' => (Token::Top, 1),
            '⊥' => (Token::Bot, 1),
            '-' if two == "->" => (Token::Imp, 2),
            _ if c.is_alphanumeric() || c == '_' => {
                let start = i;
                let mut end = i;
                while end < chars.len()
                    && (chars[end].is_alphanumeric() || chars[end] == '_')
                {
                    end += 1;
                }
                let word: String = chars[start..end].iter().collect();
                let token = match word.as_str() {
                    "top" | "true" => Token::Top,
                    "bot" | "false" => Token::Bot,
                    "tonk" => Token::Tonk,
                    _ => Token::Name(word),
                };
                (token, end - start)
            }
            _ => return Err(format!("unexpected character {c:?} at position {i}")),
        };
        tokens.push(token);
        i += width;
    }
    Ok(tokens)
}

/// A recursive-descent parser, one function per precedence level.
struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }

    fn eat(&mut self, token: &Token) -> bool {
        if self.peek() == Some(token) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    // imp := or ( '→' imp | 'tonk' or )?
    fn imp(&mut self) -> Result<Formula, String> {
        let left = self.or()?;
        if self.eat(&Token::Imp) {
            Ok(Formula::imp(left, self.imp()?))
        } else if self.eat(&Token::Tonk) {
            Ok(Formula::tonk(left, self.or()?))
        } else {
            Ok(left)
        }
    }

    // or := and ( '∨' or )?
    fn or(&mut self) -> Result<Formula, String> {
        let left = self.and()?;
        if self.eat(&Token::Or) {
            Ok(Formula::or(left, self.or()?))
        } else {
            Ok(left)
        }
    }

    // and := unary ( '∧' and )?
    fn and(&mut self) -> Result<Formula, String> {
        let left = self.unary()?;
        if self.eat(&Token::And) {
            Ok(Formula::and(left, self.and()?))
        } else {
            Ok(left)
        }
    }

    // unary := '¬' unary | name | '⊤' | '⊥' | '(' imp ')'
    fn unary(&mut self) -> Result<Formula, String> {
        let token = self.peek().cloned();
        self.pos += 1;
        match token {
            Some(Token::Not) => Ok(Formula::not(self.unary()?)),
            Some(Token::Name(name)) => Ok(Formula::Atom(name)),
            Some(Token::Top) => Ok(Formula::Top),
            Some(Token::Bot) => Ok(Formula::Bot),
            Some(Token::LParen) => {
                let inner = self.imp()?;
                if self.eat(&Token::RParen) {
                    Ok(inner)
                } else {
                    Err("expected ')'".to_string())
                }
            }
            Some(other) => Err(format!("unexpected {other:?}")),
            None => Err("unexpected end of input".to_string()),
        }
    }
}

/// Parses formulas such as `A ∧ B → B ∧ A` or, in ASCII, `A & B -> B & A`.
/// Negation is `¬`, `~` or `!`; truth and falsity are `⊤`/`top` and `⊥`/`bot`.
impl FromStr for Formula {
    type Err = String;

    fn from_str(s: &str) -> Result<Formula, String> {
        let mut parser = Parser {
            tokens: tokenize(s)?,
            pos: 0,
        };
        let formula = parser.imp()?;
        if parser.pos != parser.tokens.len() {
            return Err(format!("unexpected input after formula in {s:?}"));
        }
        Ok(formula)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(s: &str) -> Formula {
        s.parse().unwrap()
    }

    #[test]
    fn precedence_and_associativity() {
        assert_eq!(
            f("A & B -> C"),
            Formula::imp(Formula::and(f("A"), f("B")), f("C"))
        );
        assert_eq!(f("A -> B -> C"), Formula::imp(f("A"), f("B -> C")));
        assert_eq!(f("A | B & C"), Formula::or(f("A"), f("B & C")));
        assert_eq!(f("~A"), Formula::imp(f("A"), Formula::Bot));
    }

    #[test]
    fn printing_round_trips() {
        for s in [
            "A ∧ B → B ∧ A",
            "(A → B) → A ∨ C → B ∨ C",
            "¬¬A → A",
            "¬(A ∧ B) → ¬A ∨ ¬B",
            "((A → B) → A) → A",
            "(A ∨ B) ∧ C",
            "⊤ tonk ⊥",
            "¬(A → B)",
        ] {
            let parsed = f(s);
            assert_eq!(parsed.to_string(), s);
            assert_eq!(f(&parsed.to_string()), parsed);
        }
    }

    #[test]
    fn ascii_and_unicode_agree() {
        assert_eq!(f("~(A & B) -> ~A | ~B"), f("¬(A ∧ B) → ¬A ∨ ¬B"));
        assert_eq!(f("top -> bot"), f("⊤ → ⊥"));
    }

    #[test]
    fn subformulas_and_atoms() {
        let g = f("A ∧ B → A");
        assert_eq!(g.atoms().len(), 2);
        assert!(g.subformulas().contains(&f("A ∧ B")));
        assert!(!g.subformulas().contains(&f("B ∧ A")));
    }

    #[test]
    fn parse_errors() {
        assert!("A ∧".parse::<Formula>().is_err());
        assert!("(A".parse::<Formula>().is_err());
        assert!("A B".parse::<Formula>().is_err());
        assert!("A ? B".parse::<Formula>().is_err());
    }
}
