//! A lexer and a recursive-descent parser for mini-ML.
//!
//! The concrete syntax, from loosest to tightest binding:
//!
//! ```text
//! expr    ::= fun x1 ... xn -> expr
//!           | let [rec] f x1 ... xn = expr in expr
//!           | if expr then expr else expr
//!           | compare
//! compare ::= cons [(== | <) cons]
//! cons    ::= sum [:: cons]                         (right associative)
//! sum     ::= product ((+ | -) product)*
//! product ::= app (* app)*
//! app     ::= atom atom*                            (left associative)
//! atom    ::= int | true | false | x | (expr) | (expr, expr)
//!           | [] | [expr, ..., expr]
//! ```

use crate::diagnostic::Diagnostic;
use crate::syntax::{Expr, ExprKind, Span};
use crate::types::{TyVar, Type};

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Int(i64),
    Ident(String),
    Keyword(&'static str),
    Symbol(&'static str),
    Eof,
}

const KEYWORDS: [&str; 10] = [
    "fun", "let", "rec", "in", "if", "then", "else", "true", "false", "_",
];
/// Longest symbols first, so that `->` is not read as `-` followed by `>`.
const SYMBOLS: [&str; 13] = [
    "->", "==", "::", "<", "+", "-", "*", "=", "(", ")", "[", "]", ",",
];

fn lex(source: &str) -> Result<Vec<(Tok, Span)>, Diagnostic> {
    let bytes = source.as_bytes();
    let mut tokens = Vec::new();
    let mut i = 0;
    'outer: while i < bytes.len() {
        let c = bytes[i] as char;
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        let start = i;
        if c.is_ascii_digit() {
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                i += 1;
            }
            let span = Span::new(start, i);
            let n = source[start..i].parse::<i64>().map_err(|_| {
                Diagnostic::error("integer literal too large")
                    .primary(span, "does not fit in 64 bits")
            })?;
            tokens.push((Tok::Int(n), span));
            continue;
        }
        if c.is_ascii_alphabetic() || c == '_' {
            while i < bytes.len()
                && (bytes[i].is_ascii_alphanumeric()
                    || bytes[i] == b'_'
                    || bytes[i] == b'\'')
            {
                i += 1;
            }
            let word = &source[start..i];
            let tok = match KEYWORDS.iter().find(|k| **k == word) {
                Some(k) => Tok::Keyword(k),
                None => Tok::Ident(word.to_string()),
            };
            tokens.push((tok, Span::new(start, i)));
            continue;
        }
        for sym in SYMBOLS {
            if source[i..].starts_with(sym) {
                i += sym.len();
                tokens.push((Tok::Symbol(sym), Span::new(start, i)));
                continue 'outer;
            }
        }
        let width = c.len_utf8();
        let span = Span::new(start, start + width);
        return Err(Diagnostic::error(format!("unexpected character `{c}`"))
            .primary(span, "not part of mini-ML"));
    }
    tokens.push((Tok::Eof, Span::new(source.len(), source.len())));
    Ok(tokens)
}

struct Parser {
    tokens: Vec<(Tok, Span)>,
    pos: usize,
}

/// Parses a complete mini-ML program (one expression).
pub fn parse(source: &str) -> Result<Expr, Diagnostic> {
    let mut parser = Parser {
        tokens: lex(source)?,
        pos: 0,
    };
    let expr = parser.expr()?;
    match parser.peek() {
        Tok::Eof => Ok(expr),
        _ => Err(parser.unexpected("the end of the program")),
    }
}

impl Parser {
    fn peek(&self) -> &Tok {
        &self.tokens[self.pos].0
    }

    fn span(&self) -> Span {
        self.tokens[self.pos].1
    }

    fn advance(&mut self) -> (Tok, Span) {
        let tok = self.tokens[self.pos].clone();
        if self.pos + 1 < self.tokens.len() {
            self.pos += 1;
        }
        tok
    }

    fn is(&self, tok: &Tok) -> bool {
        self.peek() == tok
    }

    fn unexpected(&self, wanted: &str) -> Diagnostic {
        let found = match self.peek() {
            Tok::Int(n) => format!("`{n}`"),
            Tok::Ident(x) => format!("`{x}`"),
            Tok::Keyword(k) | Tok::Symbol(k) => format!("`{k}`"),
            Tok::Eof => "the end of the program".to_string(),
        };
        Diagnostic::error(format!("expected {wanted}, found {found}"))
            .primary(self.span(), format!("expected {wanted}"))
    }

    fn expect(&mut self, tok: Tok, what: &str) -> Result<Span, Diagnostic> {
        if self.is(&tok) {
            Ok(self.advance().1)
        } else {
            Err(self.unexpected(what))
        }
    }

    fn ident(&mut self) -> Result<(String, Span), Diagnostic> {
        match self.peek().clone() {
            Tok::Ident(x) => Ok((x, self.advance().1)),
            Tok::Keyword("_") => Ok(("_".to_string(), self.advance().1)),
            _ => Err(self.unexpected("a name")),
        }
    }

    fn params(&mut self) -> Result<Vec<(String, Span)>, Diagnostic> {
        let mut params = Vec::new();
        while matches!(self.peek(), Tok::Ident(_) | Tok::Keyword("_")) {
            params.push(self.ident()?);
        }
        Ok(params)
    }

    fn expr(&mut self) -> Result<Expr, Diagnostic> {
        match self.peek() {
            Tok::Keyword("fun") => {
                let start = self.advance().1;
                let params = self.params()?;
                if params.is_empty() {
                    return Err(self.unexpected("a parameter name"));
                }
                self.expect(Tok::Symbol("->"), "`->`")?;
                let body = self.expr()?;
                let span = start.to(body.span);
                Ok(curry(params, body, span))
            }
            Tok::Keyword("let") => {
                let start = self.advance().1;
                let recursive = self.is(&Tok::Keyword("rec"));
                if recursive {
                    self.advance();
                }
                let (name, _) = self.ident()?;
                let params = self.params()?;
                self.expect(Tok::Symbol("="), "`=`")?;
                let mut bound = self.expr()?;
                if let Some((_, first)) = params.first() {
                    let span = first.to(bound.span);
                    bound = curry(params, bound, span);
                }
                self.expect(Tok::Keyword("in"), "`in`")?;
                let body = self.expr()?;
                let span = start.to(body.span);
                let kind = if recursive {
                    ExprKind::LetRec(name, Box::new(bound), Box::new(body))
                } else {
                    ExprKind::Let(name, Box::new(bound), Box::new(body))
                };
                Ok(Expr::new(kind, span))
            }
            Tok::Keyword("if") => {
                let start = self.advance().1;
                let cond = self.expr()?;
                self.expect(Tok::Keyword("then"), "`then`")?;
                let then_branch = self.expr()?;
                self.expect(Tok::Keyword("else"), "`else`")?;
                let else_branch = self.expr()?;
                let span = start.to(else_branch.span);
                let kind = ExprKind::If(
                    Box::new(cond),
                    Box::new(then_branch),
                    Box::new(else_branch),
                );
                Ok(Expr::new(kind, span))
            }
            _ => self.compare(),
        }
    }

    fn compare(&mut self) -> Result<Expr, Diagnostic> {
        let left = self.cons()?;
        for op in ["==", "<"] {
            if self.is(&Tok::Symbol(op)) {
                let op_span = self.advance().1;
                let right = self.cons()?;
                return Ok(binary(op, op_span, left, right));
            }
        }
        Ok(left)
    }

    fn cons(&mut self) -> Result<Expr, Diagnostic> {
        let head = self.sum()?;
        if self.is(&Tok::Symbol("::")) {
            let op_span = self.advance().1;
            let tail = self.cons()?;
            return Ok(binary("cons", op_span, head, tail));
        }
        Ok(head)
    }

    fn sum(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.product()?;
        while let Tok::Symbol(op @ ("+" | "-")) = self.peek().clone() {
            let op_span = self.advance().1;
            let right = self.product()?;
            left = binary(op, op_span, left, right);
        }
        Ok(left)
    }

    fn product(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.app()?;
        while self.is(&Tok::Symbol("*")) {
            let op_span = self.advance().1;
            let right = self.app()?;
            left = binary("*", op_span, left, right);
        }
        Ok(left)
    }

    fn starts_atom(&self) -> bool {
        matches!(
            self.peek(),
            Tok::Int(_)
                | Tok::Ident(_)
                | Tok::Keyword("true" | "false")
                | Tok::Symbol("(" | "[")
        )
    }

    fn app(&mut self) -> Result<Expr, Diagnostic> {
        let mut func = self.atom()?;
        while self.starts_atom() {
            let arg = self.atom()?;
            let span = func.span.to(arg.span);
            func = Expr::new(ExprKind::App(Box::new(func), Box::new(arg)), span);
        }
        Ok(func)
    }

    fn atom(&mut self) -> Result<Expr, Diagnostic> {
        let (tok, span) = (self.peek().clone(), self.span());
        match tok {
            Tok::Int(n) => {
                self.advance();
                Ok(Expr::new(ExprKind::Int(n), span))
            }
            Tok::Keyword(b @ ("true" | "false")) => {
                self.advance();
                Ok(Expr::new(ExprKind::Bool(b == "true"), span))
            }
            Tok::Ident(x) => {
                self.advance();
                Ok(Expr::new(ExprKind::Var(x), span))
            }
            Tok::Symbol("(") => {
                self.advance();
                let first = self.expr()?;
                if self.is(&Tok::Symbol(",")) {
                    self.advance();
                    let second = self.expr()?;
                    let end = self.expect(Tok::Symbol(")"), "`)`")?;
                    let kind = ExprKind::Pair(Box::new(first), Box::new(second));
                    return Ok(Expr::new(kind, span.to(end)));
                }
                let end = self.expect(Tok::Symbol(")"), "`)` or `,`")?;
                // Keep the parentheses in the span: errors then underline them too.
                Ok(Expr::new(first.kind, span.to(end)))
            }
            Tok::Symbol("[") => {
                self.advance();
                let mut items = Vec::new();
                if !self.is(&Tok::Symbol("]")) {
                    items.push(self.expr()?);
                    while self.is(&Tok::Symbol(",")) {
                        self.advance();
                        items.push(self.expr()?);
                    }
                }
                let end = self.expect(Tok::Symbol("]"), "`]` or `,`")?;
                Ok(list_literal(items, span.to(end)))
            }
            _ => Err(self.unexpected("an expression")),
        }
    }
}

/// `fun x y -> e` is `fun x -> fun y -> e`.
fn curry(params: Vec<(String, Span)>, body: Expr, span: Span) -> Expr {
    params
        .into_iter()
        .rev()
        .fold(body, |body, (param, param_span)| {
            let lam_span = param_span.to(body.span);
            Expr::new(ExprKind::Lam(param, Box::new(body)), lam_span)
        })
        .with_span(span)
}

/// `a op b` is the application `op a b` of the operator's name.
fn binary(op: &str, op_span: Span, left: Expr, right: Expr) -> Expr {
    let func = Expr::new(ExprKind::Var(op.to_string()), op_span);
    let partial_span = left.span.to(op_span);
    let partial =
        Expr::new(ExprKind::App(Box::new(func), Box::new(left)), partial_span);
    let span = partial_span.to(right.span);
    Expr::new(ExprKind::App(Box::new(partial), Box::new(right)), span)
}

/// `[a, b]` is `cons a (cons b nil)`; every node gets the span of the literal.
fn list_literal(items: Vec<Expr>, span: Span) -> Expr {
    let nil = Expr::new(ExprKind::Var("nil".to_string()), span);
    items.into_iter().rev().fold(nil, |tail, head| {
        let cons = Expr::new(ExprKind::Var("cons".to_string()), span);
        let partial = Expr::new(ExprKind::App(Box::new(cons), Box::new(head)), span);
        Expr::new(ExprKind::App(Box::new(partial), Box::new(tail)), span)
    })
}

impl Expr {
    fn with_span(mut self, span: Span) -> Expr {
        self.span = span;
        self
    }
}

/// Parses a type written with inference variables, such as
/// `?0 -> List ?1 * Int`. Used by the unification examples and the tests.
/// `->` associates to the right and binds loosest; `*` binds tighter, and
/// `List` tightest.
pub fn parse_type(text: &str) -> Result<Type, String> {
    let spaced = text
        .replace("->", " -> ")
        .replace('(', " ( ")
        .replace(')', " ) ");
    let tokens: Vec<String> = spaced
        .replace('*', " * ")
        .split_whitespace()
        .map(str::to_string)
        .collect();
    let mut pos = 0;
    let ty = type_arrow(&tokens, &mut pos)?;
    if pos != tokens.len() {
        return Err(format!("unexpected `{}` in type", tokens[pos]));
    }
    Ok(ty)
}

fn type_arrow(tokens: &[String], pos: &mut usize) -> Result<Type, String> {
    let arg = type_pair(tokens, pos)?;
    if tokens.get(*pos).map(String::as_str) == Some("->") {
        *pos += 1;
        return Ok(Type::fun(arg, type_arrow(tokens, pos)?));
    }
    Ok(arg)
}

fn type_pair(tokens: &[String], pos: &mut usize) -> Result<Type, String> {
    let mut left = type_list(tokens, pos)?;
    while tokens.get(*pos).map(String::as_str) == Some("*") {
        *pos += 1;
        left = Type::pair(left, type_list(tokens, pos)?);
    }
    Ok(left)
}

fn type_list(tokens: &[String], pos: &mut usize) -> Result<Type, String> {
    if tokens.get(*pos).map(String::as_str) == Some("List") {
        *pos += 1;
        return Ok(Type::list(type_list(tokens, pos)?));
    }
    type_atom(tokens, pos)
}

fn type_atom(tokens: &[String], pos: &mut usize) -> Result<Type, String> {
    let token = tokens.get(*pos).ok_or("unexpected end of type")?;
    *pos += 1;
    match token.as_str() {
        "Int" => Ok(Type::int()),
        "Bool" => Ok(Type::bool()),
        "(" => {
            let inner = type_arrow(tokens, pos)?;
            match tokens.get(*pos).map(String::as_str) {
                Some(")") => {
                    *pos += 1;
                    Ok(inner)
                }
                _ => Err("expected `)` in type".to_string()),
            }
        }
        var if var.starts_with('?') => var[1..]
            .parse()
            .map(|n| Type::Var(TyVar(n)))
            .map_err(|_| format!("bad type variable `{var}`")),
        other => Err(format!("unexpected `{other}` in type")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn shape(e: &Expr) -> String {
        match &e.kind {
            ExprKind::Int(n) => n.to_string(),
            ExprKind::Bool(b) => b.to_string(),
            ExprKind::Var(x) => x.clone(),
            ExprKind::Lam(x, b) => format!("(fun {x} -> {})", shape(b)),
            ExprKind::App(f, a) => format!("({} {})", shape(f), shape(a)),
            ExprKind::Let(x, a, b) => {
                format!("(let {x} = {} in {})", shape(a), shape(b))
            }
            ExprKind::LetRec(x, a, b) => {
                format!("(let rec {x} = {} in {})", shape(a), shape(b))
            }
            ExprKind::If(c, a, b) => {
                format!("(if {} then {} else {})", shape(c), shape(a), shape(b))
            }
            ExprKind::Pair(a, b) => format!("({}, {})", shape(a), shape(b)),
        }
    }

    fn parsed(src: &str) -> String {
        shape(&parse(src).unwrap())
    }

    #[test]
    fn application_is_left_associative_and_binds_tightest() {
        assert_eq!(parsed("f x y + 1"), "((+ ((f x) y)) 1)");
    }

    #[test]
    fn sugar_is_expanded() {
        assert_eq!(parsed("fun f x -> f x"), "(fun f -> (fun x -> (f x)))");
        assert_eq!(
            parsed("let k x y = x in k"),
            "(let k = (fun x -> (fun y -> x)) in k)"
        );
        assert_eq!(parsed("[1, 2]"), "((cons 1) ((cons 2) nil))");
        assert_eq!(parsed("1 :: 2 :: []"), "((cons 1) ((cons 2) nil))");
        assert_eq!(parsed("(1, true)"), "(1, true)");
    }

    #[test]
    fn spans_cover_the_source() {
        let src = "let id = fun x -> x in id 1";
        let e = parse(src).unwrap();
        assert_eq!(e.text(src), src);
        let ExprKind::Let(_, bound, body) = &e.kind else {
            panic!()
        };
        assert_eq!(bound.text(src), "fun x -> x");
        assert_eq!(body.text(src), "id 1");
    }

    #[test]
    fn types_parse_with_the_usual_precedence() {
        let t = parse_type("(?0 -> ?1) -> List ?0 * Int -> Bool").unwrap();
        assert_eq!(t.to_string(), "(?0 -> ?1) -> List ?0 * Int -> Bool");
        let expected = Type::fun(
            Type::fun(Type::Var(TyVar(0)), Type::Var(TyVar(1))),
            Type::fun(
                Type::pair(Type::list(Type::Var(TyVar(0))), Type::int()),
                Type::bool(),
            ),
        );
        assert_eq!(t, expected);
        assert!(parse_type("Int ->").is_err());
    }

    #[test]
    fn syntax_errors_point_at_the_token() {
        let err = parse("let x = 1 x").unwrap_err();
        assert_eq!(err.message, "expected `in`, found the end of the program");
        let err = parse("fun -> x").unwrap_err();
        assert_eq!(err.message, "expected a parameter name, found `->`");
    }
}
