//! Concrete syntax: from text to abstract syntax trees.
//!
//! The parser is a classic recursive-descent parser. Each grammar level is one
//! function, and precedence is encoded in which function calls which:
//!
//! ```text
//! expr    ::= "let" ident "=" expr "in" expr
//!           | "if" expr "then" expr "else" expr
//!           | compare
//! compare ::= sum ( "==" sum )?
//! sum     ::= atom ( "+" atom )*
//! atom    ::= number | "true" | "false" | ident | "(" expr ")"
//! ```
//!
//! The book's BNF in Chapter 3 is the *abstract* grammar: it says what the
//! trees are, and ignores parentheses and precedence. This file is where those
//! concrete details live, and nothing after it needs to know about them.

use crate::syntax::Expr;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Num(u64),
    Ident(String),
    Let,
    In,
    If,
    Then,
    Else,
    True,
    False,
    Plus,
    EqEq,
    Assign,
    LParen,
    RParen,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Num(n) => write!(f, "{n}"),
            Token::Ident(x) => write!(f, "{x}"),
            Token::Let => write!(f, "let"),
            Token::In => write!(f, "in"),
            Token::If => write!(f, "if"),
            Token::Then => write!(f, "then"),
            Token::Else => write!(f, "else"),
            Token::True => write!(f, "true"),
            Token::False => write!(f, "false"),
            Token::Plus => write!(f, "+"),
            Token::EqEq => write!(f, "=="),
            Token::Assign => write!(f, "="),
            Token::LParen => write!(f, "("),
            Token::RParen => write!(f, ")"),
        }
    }
}

/// A syntax error, with a short description of what went wrong.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError(pub String);

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "syntax error: {}", self.0)
    }
}

fn tokenize(src: &str) -> Result<Vec<Token>, ParseError> {
    let chars: Vec<char> = src.chars().collect();
    let mut tokens = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
        } else if c.is_ascii_digit() {
            let start = i;
            while i < chars.len() && chars[i].is_ascii_digit() {
                i += 1;
            }
            let text: String = chars[start..i].iter().collect();
            let n = text
                .parse()
                .map_err(|_| ParseError(format!("number too large: {text}")))?;
            tokens.push(Token::Num(n));
        } else if c.is_ascii_alphabetic() || c == '_' {
            let start = i;
            while i < chars.len()
                && (chars[i].is_ascii_alphanumeric() || chars[i] == '_')
            {
                i += 1;
            }
            let word: String = chars[start..i].iter().collect();
            tokens.push(match word.as_str() {
                "let" => Token::Let,
                "in" => Token::In,
                "if" => Token::If,
                "then" => Token::Then,
                "else" => Token::Else,
                "true" => Token::True,
                "false" => Token::False,
                _ => Token::Ident(word),
            });
        } else if c == '=' && chars.get(i + 1) == Some(&'=') {
            tokens.push(Token::EqEq);
            i += 2;
        } else {
            tokens.push(match c {
                '+' => Token::Plus,
                '=' => Token::Assign,
                '(' => Token::LParen,
                ')' => Token::RParen,
                _ => return Err(ParseError(format!("unexpected character {c:?}"))),
            });
            i += 1;
        }
    }
    Ok(tokens)
}

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }

    fn next(&mut self) -> Option<Token> {
        let t = self.tokens.get(self.pos).cloned();
        self.pos += 1;
        t
    }

    fn expect(&mut self, want: Token) -> Result<(), ParseError> {
        match self.next() {
            Some(t) if t == want => Ok(()),
            Some(t) => Err(ParseError(format!("expected `{want}`, found `{t}`"))),
            None => Err(ParseError(format!("expected `{want}`, found end of input"))),
        }
    }

    fn expr(&mut self) -> Result<Expr, ParseError> {
        match self.peek() {
            Some(Token::Let) => {
                self.next();
                let x = match self.next() {
                    Some(Token::Ident(x)) => x,
                    _ => {
                        return Err(ParseError(
                            "expected a variable after `let`".into(),
                        ));
                    }
                };
                self.expect(Token::Assign)?;
                let e1 = self.expr()?;
                self.expect(Token::In)?;
                let e2 = self.expr()?;
                Ok(Expr::Let(x, Box::new(e1), Box::new(e2)))
            }
            Some(Token::If) => {
                self.next();
                let c = self.expr()?;
                self.expect(Token::Then)?;
                let e1 = self.expr()?;
                self.expect(Token::Else)?;
                let e2 = self.expr()?;
                Ok(Expr::If(Box::new(c), Box::new(e1), Box::new(e2)))
            }
            _ => self.compare(),
        }
    }

    fn compare(&mut self) -> Result<Expr, ParseError> {
        let left = self.sum()?;
        if self.peek() == Some(&Token::EqEq) {
            self.next();
            let right = self.sum()?;
            return Ok(Expr::Eq(Box::new(left), Box::new(right)));
        }
        Ok(left)
    }

    fn sum(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.atom()?;
        while self.peek() == Some(&Token::Plus) {
            self.next();
            let right = self.atom()?;
            // Building the tree as we go makes `+` associate to the left.
            left = Expr::Add(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn atom(&mut self) -> Result<Expr, ParseError> {
        match self.next() {
            Some(Token::Num(n)) => Ok(Expr::Num(n)),
            Some(Token::True) => Ok(Expr::Bool(true)),
            Some(Token::False) => Ok(Expr::Bool(false)),
            Some(Token::Ident(x)) => Ok(Expr::Var(x)),
            Some(Token::LParen) => {
                let e = self.expr()?;
                self.expect(Token::RParen)?;
                Ok(e)
            }
            Some(t) => Err(ParseError(format!("unexpected `{t}`"))),
            None => Err(ParseError("unexpected end of input".into())),
        }
    }
}

/// Parse a complete Arith expression.
pub fn parse(src: &str) -> Result<Expr, ParseError> {
    let mut p = Parser {
        tokens: tokenize(src)?,
        pos: 0,
    };
    let e = p.expr()?;
    match p.next() {
        None => Ok(e),
        Some(t) => Err(ParseError(format!("unexpected `{t}` after the expression"))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::build::*;

    #[test]
    fn parses_the_running_example() {
        let e = parse("let x = 3 in if x == 3 then x + 1 else 0").unwrap();
        let expected = let_in(
            "x",
            num(3),
            ite(eq(var("x"), num(3)), add(var("x"), num(1)), num(0)),
        );
        assert_eq!(e, expected);
    }

    #[test]
    fn plus_associates_to_the_left_and_binds_tighter_than_eq() {
        assert_eq!(
            parse("1 + 2 + 3").unwrap(),
            add(add(num(1), num(2)), num(3))
        );
        assert_eq!(
            parse("1 + 2 == 3").unwrap(),
            eq(add(num(1), num(2)), num(3))
        );
        assert_eq!(
            parse("1 + (2 + 3)").unwrap(),
            add(num(1), add(num(2), num(3)))
        );
    }

    #[test]
    fn reports_syntax_errors() {
        assert!(parse("1 +").is_err());
        assert!(parse("let = 3 in x").is_err());
        assert!(parse("if true then 1").is_err());
        assert!(parse("1 2").is_err());
        assert!(parse("1 == 2 == 3").is_err());
        assert!(parse("x * 2").is_err());
    }
}
