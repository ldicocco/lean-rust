//! A small recursive-descent parser for programs of the calculus.
//!
//! ```text
//! program ::= fn NAME [<'a, ...>] (x: τ, ...) { term }
//! term    ::= let x = term in term
//!           | let (x, y) = term in term
//!           | borrow y = &'a unary in term          shared borrow
//!           | borrow y = &'a mut unary in term      mutable borrow
//!           | borrow y = &'a mut *unary in term     reborrow
//!           | *unary := term                        assignment
//!           | unary
//! unary   ::= *unary | new unary | drop unary | atom
//! atom    ::= x | n | () | (term) | (term, term)
//! τ       ::= prefix [⊗ prefix]
//! prefix  ::= Box prefix | &'a prefix | &'a mut prefix | Int | Unit | (τ)
//! ```

use std::fmt;

use crate::syntax::{BorrowKind, Lifetime, Term, Ty};

/// A whole program: a function whose parameters form the initial context.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    pub name: String,
    /// The lifetime parameters: the initial `Δ`.
    pub lifetimes: Vec<Lifetime>,
    /// The parameters: the initial `Γ`.
    pub params: Vec<(String, Ty)>,
    pub body: Term,
}

/// A syntax error, with the line and column where it was found.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    pub line: usize,
    pub column: usize,
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "parse error at {}:{}: {}",
            self.line, self.column, self.message
        )
    }
}

impl std::error::Error for ParseError {}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok {
    Ident(String),
    Int(i64),
    Lifetime(String),
    Sym(&'static str),
    End,
}

impl fmt::Display for Tok {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Tok::Ident(s) => write!(f, "`{s}`"),
            Tok::Int(n) => write!(f, "`{n}`"),
            Tok::Lifetime(s) => write!(f, "`'{s}`"),
            Tok::Sym(s) => write!(f, "`{s}`"),
            Tok::End => write!(f, "end of input"),
        }
    }
}

const SYMBOLS: [&str; 13] = [
    ":=", "(", ")", ",", "=", "&", "*", "<", ">", ":", "{", "}", "⊗",
];

fn lex(src: &str) -> Result<Vec<(Tok, usize, usize)>, ParseError> {
    let chars: Vec<char> = src.chars().collect();
    let mut toks = Vec::new();
    let (mut i, mut line, mut col) = (0, 1, 1);
    let err = |line, column, message: String| ParseError {
        line,
        column,
        message,
    };
    while i < chars.len() {
        let c = chars[i];
        let (l, cl) = (line, col);
        if c == '\n' {
            i += 1;
            line += 1;
            col = 1;
            continue;
        }
        if c.is_whitespace() {
            i += 1;
            col += 1;
            continue;
        }
        // Comments run from `//` to the end of the line.
        if c == '/' && chars.get(i + 1) == Some(&'/') {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
            continue;
        }
        let start = i;
        if c.is_ascii_alphabetic() || c == '_' || c == '\'' {
            i += 1;
            while i < chars.len()
                && (chars[i].is_ascii_alphanumeric() || chars[i] == '_')
            {
                i += 1;
            }
            let word: String = chars[start..i].iter().collect();
            col += i - start;
            let tok = match word.strip_prefix('\'') {
                Some("") => return Err(err(l, cl, "a lifetime needs a name".into())),
                Some(name) => Tok::Lifetime(name.to_string()),
                None => Tok::Ident(word),
            };
            toks.push((tok, l, cl));
            continue;
        }
        if c.is_ascii_digit() {
            while i < chars.len() && chars[i].is_ascii_digit() {
                i += 1;
            }
            let digits: String = chars[start..i].iter().collect();
            col += i - start;
            let n = digits
                .parse()
                .map_err(|_| err(l, cl, format!("integer `{digits}` is too large")))?;
            toks.push((Tok::Int(n), l, cl));
            continue;
        }
        let rest: String = chars[i..chars.len().min(i + 2)].iter().collect();
        match SYMBOLS.iter().find(|s| rest.starts_with(**s)) {
            Some(s) => {
                let n = s.chars().count();
                i += n;
                col += n;
                toks.push((Tok::Sym(s), l, cl));
            }
            None => return Err(err(l, cl, format!("unexpected character `{c}`"))),
        }
    }
    toks.push((Tok::End, line, col));
    Ok(toks)
}

struct Parser {
    toks: Vec<(Tok, usize, usize)>,
    pos: usize,
}

const KEYWORDS: [&str; 10] = [
    "let", "in", "new", "drop", "borrow", "mut", "fn", "Int", "Unit", "Box",
];

impl Parser {
    fn peek(&self) -> &Tok {
        &self.toks[self.pos].0
    }

    fn error<T>(&self, message: String) -> Result<T, ParseError> {
        let (_, line, column) = self.toks[self.pos];
        Err(ParseError {
            line,
            column,
            message,
        })
    }

    fn advance(&mut self) -> Tok {
        let t = self.toks[self.pos].0.clone();
        if self.pos + 1 < self.toks.len() {
            self.pos += 1;
        }
        t
    }

    fn is_sym(&self, s: &str) -> bool {
        matches!(self.peek(), Tok::Sym(t) if *t == s)
    }

    fn is_kw(&self, k: &str) -> bool {
        matches!(self.peek(), Tok::Ident(t) if t == k)
    }

    fn expect_sym(&mut self, s: &str) -> Result<(), ParseError> {
        if self.is_sym(s) {
            self.advance();
            Ok(())
        } else {
            self.error(format!("expected `{s}`, found {}", self.peek()))
        }
    }

    fn expect_kw(&mut self, k: &str) -> Result<(), ParseError> {
        if self.is_kw(k) {
            self.advance();
            Ok(())
        } else {
            self.error(format!("expected `{k}`, found {}", self.peek()))
        }
    }

    fn ident(&mut self) -> Result<String, ParseError> {
        match self.peek().clone() {
            Tok::Ident(s) if !KEYWORDS.contains(&s.as_str()) => {
                self.advance();
                Ok(s)
            }
            t => self.error(format!("expected a variable, found {t}")),
        }
    }

    fn lifetime(&mut self) -> Result<Lifetime, ParseError> {
        match self.peek().clone() {
            Tok::Lifetime(s) => {
                self.advance();
                Ok(s)
            }
            t => self.error(format!("expected a lifetime such as `'a`, found {t}")),
        }
    }

    fn program(&mut self) -> Result<Program, ParseError> {
        self.expect_kw("fn")?;
        let name = self.ident()?;
        let mut lifetimes = Vec::new();
        if self.is_sym("<") {
            self.advance();
            loop {
                lifetimes.push(self.lifetime()?);
                if self.is_sym(",") {
                    self.advance();
                } else {
                    break;
                }
            }
            self.expect_sym(">")?;
        }
        self.expect_sym("(")?;
        let mut params = Vec::new();
        while !self.is_sym(")") {
            let x = self.ident()?;
            self.expect_sym(":")?;
            params.push((x, self.ty()?));
            if !self.is_sym(")") {
                self.expect_sym(",")?;
            }
        }
        self.expect_sym(")")?;
        self.expect_sym("{")?;
        let body = self.term()?;
        self.expect_sym("}")?;
        Ok(Program {
            name,
            lifetimes,
            params,
            body,
        })
    }

    fn ty(&mut self) -> Result<Ty, ParseError> {
        let mut t = self.ty_prefix()?;
        while self.is_sym("⊗") {
            self.advance();
            t = Ty::pair(t, self.ty_prefix()?);
        }
        Ok(t)
    }

    fn ty_prefix(&mut self) -> Result<Ty, ParseError> {
        if self.is_kw("Box") {
            self.advance();
            return Ok(Ty::boxed(self.ty_prefix()?));
        }
        if self.is_sym("&") {
            self.advance();
            let k = self.lifetime()?;
            if self.is_kw("mut") {
                self.advance();
                return Ok(Ty::RefMut(k, Box::new(self.ty_prefix()?)));
            }
            return Ok(Ty::Ref(k, Box::new(self.ty_prefix()?)));
        }
        if self.is_kw("Int") {
            self.advance();
            return Ok(Ty::Int);
        }
        if self.is_kw("Unit") {
            self.advance();
            return Ok(Ty::Unit);
        }
        if self.is_sym("(") {
            self.advance();
            let t = self.ty()?;
            self.expect_sym(")")?;
            return Ok(t);
        }
        self.error(format!("expected a type, found {}", self.peek()))
    }

    fn term(&mut self) -> Result<Term, ParseError> {
        if self.is_kw("let") {
            self.advance();
            if self.is_sym("(") {
                self.advance();
                let x = self.ident()?;
                self.expect_sym(",")?;
                let y = self.ident()?;
                self.expect_sym(")")?;
                self.expect_sym("=")?;
                let e1 = self.term()?;
                self.expect_kw("in")?;
                let e2 = self.term()?;
                return Ok(Term::let_pair(&x, &y, e1, e2));
            }
            let x = self.ident()?;
            self.expect_sym("=")?;
            let e1 = self.term()?;
            self.expect_kw("in")?;
            let e2 = self.term()?;
            return Ok(Term::let_in(&x, e1, e2));
        }
        if self.is_kw("borrow") {
            self.advance();
            let y = self.ident()?;
            self.expect_sym("=")?;
            self.expect_sym("&")?;
            let lt = self.lifetime()?;
            let mut kind = BorrowKind::Shared;
            if self.is_kw("mut") {
                self.advance();
                kind = BorrowKind::Mut;
                if self.is_sym("*") {
                    self.advance();
                    kind = BorrowKind::Reborrow;
                }
            }
            let owner = self.unary()?;
            self.expect_kw("in")?;
            let body = self.term()?;
            return Ok(Term::borrow(kind, &lt, &y, owner, body));
        }
        let e = self.unary()?;
        if self.is_sym(":=") {
            return match e {
                Term::Deref(target) => {
                    self.advance();
                    let value = self.term()?;
                    Ok(Term::Assign(target, Box::new(value)))
                }
                _ => self.error("the left side of `:=` must have the form `*e`".into()),
            };
        }
        Ok(e)
    }

    fn unary(&mut self) -> Result<Term, ParseError> {
        if self.is_sym("*") {
            self.advance();
            return Ok(Term::Deref(Box::new(self.unary()?)));
        }
        if self.is_kw("new") {
            self.advance();
            return Ok(Term::New(Box::new(self.unary()?)));
        }
        if self.is_kw("drop") {
            self.advance();
            return Ok(Term::Drop(Box::new(self.unary()?)));
        }
        self.atom()
    }

    fn atom(&mut self) -> Result<Term, ParseError> {
        match self.peek().clone() {
            Tok::Int(n) => {
                self.advance();
                Ok(Term::Lit(n))
            }
            Tok::Ident(_) => Ok(Term::Var(self.ident()?)),
            Tok::Sym("(") => {
                self.advance();
                if self.is_sym(")") {
                    self.advance();
                    return Ok(Term::Unit);
                }
                let a = self.term()?;
                if self.is_sym(",") {
                    self.advance();
                    let b = self.term()?;
                    self.expect_sym(")")?;
                    return Ok(Term::pair(a, b));
                }
                self.expect_sym(")")?;
                Ok(a)
            }
            t => self.error(format!("expected a term, found {t}")),
        }
    }

    fn finish<T>(&mut self, value: T) -> Result<T, ParseError> {
        match self.peek() {
            Tok::End => Ok(value),
            t => self.error(format!("unexpected {t} after the end")),
        }
    }
}

/// Parse a whole program `fn name<'a>(x: τ) { e }`.
pub fn parse_program(src: &str) -> Result<Program, ParseError> {
    let mut p = Parser {
        toks: lex(src)?,
        pos: 0,
    };
    let prog = p.program()?;
    p.finish(prog)
}

/// Parse a single term.
pub fn parse_term(src: &str) -> Result<Term, ParseError> {
    let mut p = Parser {
        toks: lex(src)?,
        pos: 0,
    };
    let e = p.term()?;
    p.finish(e)
}

/// Parse a single type.
pub fn parse_ty(src: &str) -> Result<Ty, ParseError> {
    let mut p = Parser {
        toks: lex(src)?,
        pos: 0,
    };
    let t = p.ty()?;
    p.finish(t)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn types_round_trip() {
        for src in [
            "Int",
            "Box Int ⊗ Unit",
            "&'a mut Int",
            "&'a (Int ⊗ &'b Unit)",
        ] {
            let t = parse_ty(src).unwrap();
            assert_eq!(t.to_string(), src);
        }
    }

    #[test]
    fn terms_round_trip() {
        for src in [
            "borrow y = &'b mut *r in *y := 1",
            "let (r1, u1) = (borrow y = &'b mut *r in *y := 1) in ()",
            "let x = new 5 in drop x",
            "borrow f = &'a v in *f",
            "(s, s)",
        ] {
            let e = parse_term(src).unwrap();
            assert_eq!(e.to_string(), src);
        }
    }

    #[test]
    fn programs() {
        let p = parse_program("fn f<'a>(r: &'a mut Int, n: Int) { *r := n }").unwrap();
        assert_eq!(p.lifetimes, vec!["a".to_string()]);
        assert_eq!(p.params.len(), 2);
        assert_eq!(p.body.to_string(), "*r := n");
    }

    #[test]
    fn errors_have_positions() {
        let e = parse_term("let x = 1\n in in").unwrap_err();
        assert_eq!((e.line, e.column), (2, 5));
        assert!(parse_term("x := 1").is_err());
    }
}
