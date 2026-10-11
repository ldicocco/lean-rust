//! A parser for the concrete syntax printed by [`crate::syntax`].
//!
//! ```text
//! term ::= λx[: type]. term | let x = term in term
//!        | if term then term else term
//!        | case term of inl x => term | inr y => term
//!        | app
//! app  ::= head atom*
//! head ::= succ atom | fst atom | snd atom | inl atom | inr atom
//!        | iter atom atom atom | atom
//! atom ::= x | n | true | false | () | (term) | (term, term) | (term : type)
//! type ::= sum [→ type]        sum ::= prod (+ prod)*
//! prod ::= base (× base)*      base ::= Unit | Bool | Nat | (type)
//! ```
//! ASCII spellings are accepted too: `\` for `λ`, `->` for `→`, `*` for `×`.

use crate::syntax::{Term, Ty, fun, prod, sum};
use std::fmt;

/// A parse error with the byte offset where it was detected.
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
enum Tok {
    Ident(String),
    Num(u64),
    Sym(&'static str),
}

const KEYWORDS: [&str; 18] = [
    "let", "in", "if", "then", "else", "case", "of", "inl", "inr", "succ", "iter",
    "fst", "snd", "true", "false", "Unit", "Bool", "Nat",
];

fn tokenize(src: &str) -> Result<Vec<(usize, Tok)>, ParseError> {
    let mut out = Vec::new();
    let chars: Vec<(usize, char)> = src.char_indices().collect();
    let mut i = 0;
    while i < chars.len() {
        let (pos, c) = chars[i];
        let next = chars.get(i + 1).map(|&(_, c)| c);
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        let two = match (c, next) {
            ('-', Some('>')) => Some("→"),
            ('=', Some('>')) => Some("=>"),
            _ => None,
        };
        if let Some(sym) = two {
            out.push((pos, Tok::Sym(sym)));
            i += 2;
            continue;
        }
        let one = match c {
            'λ' | '\\' => Some("λ"),
            '→' => Some("→"),
            '×' | '*' => Some("×"),
            '+' => Some("+"),
            '.' => Some("."),
            ':' => Some(":"),
            ',' => Some(","),
            '(' => Some("("),
            ')' => Some(")"),
            '=' => Some("="),
            '|' => Some("|"),
            _ => None,
        };
        if let Some(sym) = one {
            out.push((pos, Tok::Sym(sym)));
            i += 1;
        } else if c.is_ascii_digit() {
            let mut n: u64 = 0;
            while i < chars.len() && chars[i].1.is_ascii_digit() {
                n = n * 10 + chars[i].1.to_digit(10).unwrap() as u64;
                i += 1;
            }
            out.push((pos, Tok::Num(n)));
        } else if c.is_alphabetic() || c == '_' {
            let mut name = String::new();
            while i < chars.len() {
                let c = chars[i].1;
                if c.is_alphanumeric() || c == '_' || c == '\'' {
                    name.push(c);
                    i += 1;
                } else {
                    break;
                }
            }
            out.push((pos, Tok::Ident(name)));
        } else {
            return Err(ParseError {
                position: pos,
                message: format!("unexpected character {c:?}"),
            });
        }
    }
    Ok(out)
}

struct Parser {
    toks: Vec<(usize, Tok)>,
    pos: usize,
    end: usize,
}

impl Parser {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos).map(|(_, t)| t)
    }

    fn is_sym(&self, s: &str) -> bool {
        matches!(self.peek(), Some(Tok::Sym(t)) if *t == s)
    }

    fn is_kw(&self, k: &str) -> bool {
        matches!(self.peek(), Some(Tok::Ident(t)) if t == k)
    }

    fn fail<T>(&self, message: &str) -> Result<T, ParseError> {
        Err(ParseError {
            position: self.toks.get(self.pos).map_or(self.end, |(p, _)| *p),
            message: message.to_string(),
        })
    }

    fn expect_sym(&mut self, s: &str) -> Result<(), ParseError> {
        if self.is_sym(s) {
            self.pos += 1;
            Ok(())
        } else {
            self.fail(&format!("expected '{s}'"))
        }
    }

    fn expect_kw(&mut self, k: &str) -> Result<(), ParseError> {
        if self.is_kw(k) {
            self.pos += 1;
            Ok(())
        } else {
            self.fail(&format!("expected '{k}'"))
        }
    }

    fn name(&mut self) -> Result<String, ParseError> {
        match self.peek() {
            Some(Tok::Ident(x)) if !KEYWORDS.contains(&x.as_str()) => {
                let x = x.clone();
                self.pos += 1;
                Ok(x)
            }
            _ => self.fail("expected a variable name"),
        }
    }

    // ----- types -----

    fn ty(&mut self) -> Result<Ty, ParseError> {
        let left = self.sum_ty()?;
        if self.is_sym("→") {
            self.pos += 1;
            Ok(fun(left, self.ty()?))
        } else {
            Ok(left)
        }
    }

    fn sum_ty(&mut self) -> Result<Ty, ParseError> {
        let mut t = self.prod_ty()?;
        while self.is_sym("+") {
            self.pos += 1;
            t = sum(t, self.prod_ty()?);
        }
        Ok(t)
    }

    fn prod_ty(&mut self) -> Result<Ty, ParseError> {
        let mut t = self.base_ty()?;
        while self.is_sym("×") {
            self.pos += 1;
            t = prod(t, self.base_ty()?);
        }
        Ok(t)
    }

    fn base_ty(&mut self) -> Result<Ty, ParseError> {
        for (kw, ty) in [("Unit", Ty::Unit), ("Bool", Ty::Bool), ("Nat", Ty::Nat)] {
            if self.is_kw(kw) {
                self.pos += 1;
                return Ok(ty);
            }
        }
        if self.is_sym("(") {
            self.pos += 1;
            let t = self.ty()?;
            self.expect_sym(")")?;
            return Ok(t);
        }
        self.fail("expected a type")
    }

    // ----- terms -----

    fn term(&mut self) -> Result<Term, ParseError> {
        if self.is_sym("λ") {
            self.pos += 1;
            let x = self.name()?;
            let ty = if self.is_sym(":") {
                self.pos += 1;
                Some(self.ty()?)
            } else {
                None
            };
            self.expect_sym(".")?;
            return Ok(Term::Lam(x, ty, Box::new(self.term()?)));
        }
        if self.is_kw("let") {
            self.pos += 1;
            let x = self.name()?;
            self.expect_sym("=")?;
            let e1 = self.term()?;
            self.expect_kw("in")?;
            return Ok(Term::Let(x, Box::new(e1), Box::new(self.term()?)));
        }
        if self.is_kw("if") {
            self.pos += 1;
            let c = self.term()?;
            self.expect_kw("then")?;
            let a = self.term()?;
            self.expect_kw("else")?;
            let b = self.term()?;
            return Ok(Term::If(Box::new(c), Box::new(a), Box::new(b)));
        }
        if self.is_kw("case") {
            self.pos += 1;
            let e = self.term()?;
            self.expect_kw("of")?;
            self.expect_kw("inl")?;
            let x = self.name()?;
            self.expect_sym("=>")?;
            let l = self.term()?;
            self.expect_sym("|")?;
            self.expect_kw("inr")?;
            let y = self.name()?;
            self.expect_sym("=>")?;
            let r = self.term()?;
            return Ok(Term::Case(Box::new(e), x, Box::new(l), y, Box::new(r)));
        }
        self.app()
    }

    fn starts_atom(&self) -> bool {
        match self.peek() {
            Some(Tok::Num(_)) => true,
            Some(Tok::Sym(s)) => *s == "(",
            Some(Tok::Ident(x)) => {
                x == "true" || x == "false" || !KEYWORDS.contains(&x.as_str())
            }
            None => false,
        }
    }

    fn app(&mut self) -> Result<Term, ParseError> {
        let mut t = self.head()?;
        while self.starts_atom() {
            let a = self.atom()?;
            t = Term::App(Box::new(t), Box::new(a));
        }
        Ok(t)
    }

    fn head(&mut self) -> Result<Term, ParseError> {
        type Unary = fn(Box<Term>) -> Term;
        let unary: [(&str, Unary); 5] = [
            ("succ", Term::Succ),
            ("fst", Term::Fst),
            ("snd", Term::Snd),
            ("inl", Term::Inl),
            ("inr", Term::Inr),
        ];
        for (kw, build) in unary {
            if self.is_kw(kw) {
                self.pos += 1;
                return Ok(build(Box::new(self.atom()?)));
            }
        }
        if self.is_kw("iter") {
            self.pos += 1;
            let n = self.atom()?;
            let z = self.atom()?;
            let s = self.atom()?;
            return Ok(Term::Iter(Box::new(n), Box::new(z), Box::new(s)));
        }
        self.atom()
    }

    fn atom(&mut self) -> Result<Term, ParseError> {
        match self.peek().cloned() {
            Some(Tok::Num(n)) => {
                self.pos += 1;
                Ok(Term::Nat(n))
            }
            Some(Tok::Ident(x)) if x == "true" || x == "false" => {
                self.pos += 1;
                Ok(Term::Bool(x == "true"))
            }
            Some(Tok::Ident(_)) => Ok(Term::Var(self.name()?)),
            Some(Tok::Sym("(")) => {
                self.pos += 1;
                if self.is_sym(")") {
                    self.pos += 1;
                    return Ok(Term::Unit);
                }
                let e = self.term()?;
                if self.is_sym(",") {
                    self.pos += 1;
                    let e2 = self.term()?;
                    self.expect_sym(")")?;
                    return Ok(Term::Pair(Box::new(e), Box::new(e2)));
                }
                if self.is_sym(":") {
                    self.pos += 1;
                    let ty = self.ty()?;
                    self.expect_sym(")")?;
                    return Ok(Term::Ann(Box::new(e), ty));
                }
                self.expect_sym(")")?;
                Ok(e)
            }
            _ => self.fail("expected a term"),
        }
    }
}

/// Parses a term such as `λf: Nat → Nat. λx: Nat. f (f x)`.
pub fn parse_term(src: &str) -> Result<Term, ParseError> {
    let mut p = Parser {
        toks: tokenize(src)?,
        pos: 0,
        end: src.len(),
    };
    let t = p.term()?;
    if p.pos != p.toks.len() {
        return p.fail("unexpected input after the end of the term");
    }
    Ok(t)
}

/// Parses a type such as `(Nat → Nat) → Nat × Bool`.
pub fn parse_type(src: &str) -> Result<Ty, ParseError> {
    let mut p = Parser {
        toks: tokenize(src)?,
        pos: 0,
        end: src.len(),
    };
    let t = p.ty()?;
    if p.pos != p.toks.len() {
        return p.fail("unexpected input after the end of the type");
    }
    Ok(t)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trip() {
        for src in [
            "λf: Nat → Nat. λx: Nat. f (f x)",
            "let k = 5 in λx: Nat. iter k x (λn. succ n)",
            "case e of inl a => a | inr b => if b then 1 else 0",
            "(λx. x : Nat → Nat) 3",
            "fst (1, true)",
            "(inl () : Unit + Bool)",
            "f (g x) (succ y)",
        ] {
            let t = parse_term(src).unwrap();
            let printed = t.to_string();
            assert_eq!(
                parse_term(&printed).unwrap(),
                t,
                "{src} printed as {printed}"
            );
        }
    }

    #[test]
    fn ascii_spellings() {
        assert_eq!(
            parse_term("\\x: Nat -> Nat * Bool. x").unwrap(),
            parse_term("λx: Nat → Nat × Bool. x").unwrap()
        );
    }

    #[test]
    fn types() {
        assert_eq!(
            parse_type("Nat → Nat → Nat").unwrap().to_string(),
            "Nat → Nat → Nat"
        );
        assert_eq!(
            parse_type("(Nat → Nat) → Nat").unwrap().to_string(),
            "(Nat → Nat) → Nat"
        );
        assert_eq!(
            parse_type("Nat × Bool + Unit").unwrap().to_string(),
            "Nat × Bool + Unit"
        );
    }

    #[test]
    fn errors() {
        assert!(parse_term("λ. x").is_err());
        assert!(parse_term("let x = 1 x").is_err());
        assert!(parse_term("(1, 2").is_err());
        assert!(parse_term("1 #").is_err());
    }
}
