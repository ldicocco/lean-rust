//! Formulas of intuitionistic linear logic (the multiplicative-additive
//! fragment), with a parser and a printer.

use std::fmt;

// ANCHOR: formula
/// A formula of intuitionistic multiplicative-additive linear logic.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Formula {
    /// An atomic proposition: a kind of resource, such as `coin` or `A`.
    Atom(String),
    /// `1`, the unit of ⊗: no resources at all.
    One,
    /// `⊤`, the unit of &: accepts any resources and offers nothing.
    Top,
    /// `0`, the unit of ⊕: an impossible situation.
    Zero,
    /// `A ⊗ B` (tensor): both A and B, at the same time.
    Tensor(Box<Formula>, Box<Formula>),
    /// `A & B` (with): A or B, and the consumer chooses which.
    With(Box<Formula>, Box<Formula>),
    /// `A ⊕ B` (plus): A or B, and the producer chooses which.
    Plus(Box<Formula>, Box<Formula>),
    /// `A ⊸ B` (lollipop): consume an A to produce a B.
    Lolli(Box<Formula>, Box<Formula>),
}
// ANCHOR_END: formula

impl Formula {
    pub fn atom(name: &str) -> Formula {
        Formula::Atom(name.to_string())
    }

    pub fn tensor(a: Formula, b: Formula) -> Formula {
        Formula::Tensor(Box::new(a), Box::new(b))
    }

    pub fn with(a: Formula, b: Formula) -> Formula {
        Formula::With(Box::new(a), Box::new(b))
    }

    pub fn plus(a: Formula, b: Formula) -> Formula {
        Formula::Plus(Box::new(a), Box::new(b))
    }

    pub fn lolli(a: Formula, b: Formula) -> Formula {
        Formula::Lolli(Box::new(a), Box::new(b))
    }

    /// The number of nodes in the formula's syntax tree. Every rule of the
    /// sequent calculus, read backwards, makes the total size of a sequent
    /// strictly smaller, which is why proof search terminates.
    pub fn size(&self) -> usize {
        match self {
            Formula::Atom(_) | Formula::One | Formula::Top | Formula::Zero => 1,
            Formula::Tensor(a, b)
            | Formula::With(a, b)
            | Formula::Plus(a, b)
            | Formula::Lolli(a, b) => 1 + a.size() + b.size(),
        }
    }

    fn is_binary(&self) -> bool {
        matches!(
            self,
            Formula::Tensor(..)
                | Formula::With(..)
                | Formula::Plus(..)
                | Formula::Lolli(..)
        )
    }
}

/// Prints with Unicode connectives. A binary subformula is always put in
/// parentheses, except on the right of `⊸`, so `A ⊸ B ⊸ C` means
/// `A ⊸ (B ⊸ C)`.
impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn operand(f: &mut fmt::Formatter<'_>, a: &Formula) -> fmt::Result {
            if a.is_binary() {
                write!(f, "({a})")
            } else {
                write!(f, "{a}")
            }
        }
        match self {
            Formula::Atom(name) => write!(f, "{name}"),
            Formula::One => write!(f, "1"),
            Formula::Top => write!(f, "⊤"),
            Formula::Zero => write!(f, "0"),
            Formula::Lolli(a, b) => {
                operand(f, a)?;
                write!(f, " ⊸ ")?;
                if matches!(**b, Formula::Lolli(..)) {
                    write!(f, "{b}")
                } else {
                    operand(f, b)
                }
            }
            Formula::Tensor(a, b) | Formula::With(a, b) | Formula::Plus(a, b) => {
                let op = match self {
                    Formula::Tensor(..) => "⊗",
                    Formula::With(..) => "&",
                    _ => "⊕",
                };
                operand(f, a)?;
                write!(f, " {op} ")?;
                operand(f, b)
            }
        }
    }
}

/// A parse error, with the position (in characters) where it happened.
#[derive(Debug, PartialEq, Eq)]
pub struct ParseError {
    pub position: usize,
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "parse error at {}: {}", self.position, self.message)
    }
}

#[derive(Clone, Debug, PartialEq)]
enum Token {
    Name(String),
    One,
    Top,
    Zero,
    Tensor,
    With,
    Plus,
    Lolli,
    LParen,
    RParen,
}

fn tokenize(input: &str) -> Result<Vec<(usize, Token)>, ParseError> {
    let chars: Vec<char> = input.chars().collect();
    let mut tokens = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        let start = i;
        i += 1;
        let token = match c {
            ' ' | '\t' => continue,
            '(' => Token::LParen,
            ')' => Token::RParen,
            '*' | '⊗' => Token::Tensor,
            '&' => Token::With,
            '+' | '⊕' => Token::Plus,
            '⊸' => Token::Lolli,
            '-' if chars.get(i) == Some(&'o') => {
                i += 1;
                Token::Lolli
            }
            '1' => Token::One,
            '0' => Token::Zero,
            '⊤' => Token::Top,
            c if c.is_alphabetic() || c == '_' => {
                while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_')
                {
                    i += 1;
                }
                let name: String = chars[start..i].iter().collect();
                if name == "top" {
                    Token::Top
                } else {
                    Token::Name(name)
                }
            }
            other => {
                return Err(ParseError {
                    position: start,
                    message: format!("unexpected character {other:?}"),
                });
            }
        };
        tokens.push((start, token));
    }
    Ok(tokens)
}

/// A recursive-descent parser. Precedence, from loosest to tightest:
/// `-o` (right associative), `+`, `&`, `*` (left associative).
struct Parser {
    tokens: Vec<(usize, Token)>,
    pos: usize,
    end: usize,
}

impl Parser {
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos).map(|(_, t)| t)
    }

    fn here(&self) -> usize {
        self.tokens.get(self.pos).map_or(self.end, |(p, _)| *p)
    }

    fn error<T>(&self, message: &str) -> Result<T, ParseError> {
        Err(ParseError {
            position: self.here(),
            message: message.to_string(),
        })
    }

    fn lolli(&mut self) -> Result<Formula, ParseError> {
        let left = self.plus()?;
        if self.peek() == Some(&Token::Lolli) {
            self.pos += 1;
            let right = self.lolli()?;
            return Ok(Formula::lolli(left, right));
        }
        Ok(left)
    }

    fn binary_level(
        &mut self,
        op: Token,
        next: fn(&mut Parser) -> Result<Formula, ParseError>,
        build: fn(Formula, Formula) -> Formula,
    ) -> Result<Formula, ParseError> {
        let mut left = next(self)?;
        while self.peek() == Some(&op) {
            self.pos += 1;
            let right = next(self)?;
            left = build(left, right);
        }
        Ok(left)
    }

    fn plus(&mut self) -> Result<Formula, ParseError> {
        self.binary_level(Token::Plus, Parser::with, Formula::plus)
    }

    fn with(&mut self) -> Result<Formula, ParseError> {
        self.binary_level(Token::With, Parser::tensor, Formula::with)
    }

    fn tensor(&mut self) -> Result<Formula, ParseError> {
        self.binary_level(Token::Tensor, Parser::atom, Formula::tensor)
    }

    fn atom(&mut self) -> Result<Formula, ParseError> {
        let token = match self.peek() {
            Some(t) => t.clone(),
            None => return self.error("expected a formula"),
        };
        self.pos += 1;
        match token {
            Token::Name(name) => Ok(Formula::Atom(name)),
            Token::One => Ok(Formula::One),
            Token::Top => Ok(Formula::Top),
            Token::Zero => Ok(Formula::Zero),
            Token::LParen => {
                let inner = self.lolli()?;
                if self.peek() != Some(&Token::RParen) {
                    return self.error("expected ')'");
                }
                self.pos += 1;
                Ok(inner)
            }
            _ => {
                self.pos -= 1;
                self.error("expected a formula")
            }
        }
    }
}

/// Parses a formula. ASCII and Unicode notations are both accepted:
/// `A * B` or `A ⊗ B`, `A & B`, `A + B` or `A ⊕ B`, `A -o B` or `A ⊸ B`,
/// and the units `1`, `0`, `top` or `⊤`.
pub fn parse_formula(input: &str) -> Result<Formula, ParseError> {
    let tokens = tokenize(input)?;
    let mut parser = Parser {
        tokens,
        pos: 0,
        end: input.chars().count(),
    };
    let formula = parser.lolli()?;
    if parser.pos != parser.tokens.len() {
        return parser.error("unexpected input after the formula");
    }
    Ok(formula)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn precedence_and_printing() {
        let f = parse_formula("a -o b -o c").unwrap();
        assert_eq!(f.to_string(), "a ⊸ b ⊸ c");
        let g = parse_formula("(a -o b) -o c").unwrap();
        assert_eq!(g.to_string(), "(a ⊸ b) ⊸ c");
        let h = parse_formula("coin -o coffee & tea").unwrap();
        assert_eq!(h.to_string(), "coin ⊸ (coffee & tea)");
        let k = parse_formula("a * b + a * c").unwrap();
        assert_eq!(k.to_string(), "(a ⊗ b) ⊕ (a ⊗ c)");
        assert_eq!(
            parse_formula("top & 1 + 0").unwrap().to_string(),
            "(⊤ & 1) ⊕ 0"
        );
    }

    #[test]
    fn printing_round_trips() {
        for text in ["a ⊸ b ⊸ c", "(a ⊗ b) ⊸ c", "a ⊗ (b & c)", "(a ⊕ 0) & ⊤"]
        {
            let f = parse_formula(text).unwrap();
            assert_eq!(f.to_string(), text);
            assert_eq!(parse_formula(&f.to_string()).unwrap(), f);
        }
    }

    #[test]
    fn errors() {
        assert!(parse_formula("a *").is_err());
        assert!(parse_formula("(a").is_err());
        assert!(parse_formula("a b").is_err());
        assert_eq!(parse_formula("a ? b").unwrap_err().position, 2);
    }

    #[test]
    fn size_counts_nodes() {
        assert_eq!(parse_formula("a ⊗ (b ⊸ 1)").unwrap().size(), 5);
    }
}
