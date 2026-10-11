//! A small parser for λ-terms, so that examples can be written as text.
//!
//! Grammar (`λ` may also be written `\`):
//!
//! ```text
//! term ::= λ x1 x2 ... xn . term      (sugar for λx1. λx2. ... λxn. term)
//!        | atom atom* [λ-term]        (application, left associative)
//! atom ::= name | ( term )
//! ```

use crate::term::{Term, app, lam, var};
use std::fmt;

/// A parse error, with the byte offset where it was detected.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub position: usize,
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "parse error at {}: {}", self.position, self.message)
    }
}

impl std::error::Error for ParseError {}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Lambda,
    Dot,
    Open,
    Close,
    Name(String),
}

fn tokenize(src: &str) -> Result<Vec<(usize, Token)>, ParseError> {
    let mut tokens = Vec::new();
    let mut chars = src.char_indices().peekable();
    while let Some(&(pos, c)) = chars.peek() {
        if c.is_whitespace() {
            chars.next();
        } else if c == 'λ' || c == '\\' {
            tokens.push((pos, Token::Lambda));
            chars.next();
        } else if c == '.' {
            tokens.push((pos, Token::Dot));
            chars.next();
        } else if c == '(' {
            tokens.push((pos, Token::Open));
            chars.next();
        } else if c == ')' {
            tokens.push((pos, Token::Close));
            chars.next();
        } else if c.is_alphanumeric() || c == '_' {
            let mut name = String::new();
            while let Some(&(_, c)) = chars.peek() {
                if c.is_alphanumeric() || c == '_' || c == '\'' {
                    name.push(c);
                    chars.next();
                } else {
                    break;
                }
            }
            tokens.push((pos, Token::Name(name)));
        } else {
            return Err(ParseError {
                position: pos,
                message: format!("unexpected character {c:?}"),
            });
        }
    }
    Ok(tokens)
}

struct Parser {
    tokens: Vec<(usize, Token)>,
    pos: usize,
    end: usize,
}

impl Parser {
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos).map(|(_, t)| t)
    }

    fn offset(&self) -> usize {
        self.tokens.get(self.pos).map_or(self.end, |(p, _)| *p)
    }

    fn error<T>(&self, message: &str) -> Result<T, ParseError> {
        Err(ParseError {
            position: self.offset(),
            message: message.to_string(),
        })
    }

    fn term(&mut self) -> Result<Term, ParseError> {
        if self.peek() == Some(&Token::Lambda) {
            return self.lambda();
        }
        let mut t = self.atom()?;
        loop {
            match self.peek() {
                Some(Token::Name(_)) | Some(Token::Open) => {
                    let u = self.atom()?;
                    t = app(t, u);
                }
                Some(Token::Lambda) => {
                    // A trailing λ extends to the right: `f λx. x` is `f (λx. x)`.
                    let u = self.lambda()?;
                    return Ok(app(t, u));
                }
                _ => return Ok(t),
            }
        }
    }

    fn lambda(&mut self) -> Result<Term, ParseError> {
        self.pos += 1; // the λ
        let mut params = Vec::new();
        while let Some(Token::Name(x)) = self.peek() {
            params.push(x.clone());
            self.pos += 1;
        }
        if params.is_empty() {
            return self.error("expected a variable name after λ");
        }
        if self.peek() != Some(&Token::Dot) {
            return self.error("expected '.' after the λ parameters");
        }
        self.pos += 1;
        let body = self.term()?;
        Ok(params.iter().rev().fold(body, |acc, x| lam(x, acc)))
    }

    fn atom(&mut self) -> Result<Term, ParseError> {
        match self.peek().cloned() {
            Some(Token::Name(x)) => {
                self.pos += 1;
                Ok(var(&x))
            }
            Some(Token::Open) => {
                self.pos += 1;
                let t = self.term()?;
                if self.peek() != Some(&Token::Close) {
                    return self.error("expected ')'");
                }
                self.pos += 1;
                Ok(t)
            }
            _ => self.error("expected a variable, '(' or λ"),
        }
    }
}

/// Parses a λ-term such as `λf. λx. f (f x)` or `\f x. f (f x)`.
pub fn parse(src: &str) -> Result<Term, ParseError> {
    let mut parser = Parser {
        tokens: tokenize(src)?,
        pos: 0,
        end: src.len(),
    };
    let t = parser.term()?;
    if parser.pos != parser.tokens.len() {
        return parser.error("unexpected input after the end of the term");
    }
    Ok(t)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn application_is_left_associative() {
        assert_eq!(
            parse("f x y").unwrap(),
            app(app(var("f"), var("x")), var("y"))
        );
    }

    #[test]
    fn lambda_extends_right() {
        assert_eq!(parse("λx. x y").unwrap(), lam("x", app(var("x"), var("y"))));
        assert_eq!(parse("f λx. x").unwrap(), app(var("f"), lam("x", var("x"))));
    }

    #[test]
    fn several_parameters() {
        assert_eq!(parse("\\x y. x").unwrap(), parse("λx. λy. x").unwrap());
    }

    #[test]
    fn errors() {
        assert!(parse("λ. x").is_err());
        assert!(parse("(x").is_err());
        assert!(parse("x )").is_err());
        assert!(parse("x + y").is_err());
    }
}
