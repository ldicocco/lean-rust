//! A small recursive-descent parser for the checker's input language.
//!
//! ```text
//! program := item*
//! item    := ("#[derive(" ident,* ")]")? "struct" Name "{" (field ":" ty),* "}"
//!          | "impl" "Drop" "for" Name "{" "}"
//!          | "fn" name "(" (x ":" ty),* ")" ("->" ty)? (block | ";")
//! ty      := "()" | "(" ty "," ty ")" | "FnOnce(" ty ")" "->" ty
//!          | "With<" ty "," ty ">" | "Either<" ty "," ty ">"
//!          | "&" ty | "&mut" ty | "Rc<" ty ">" | Name
//! block   := "{" (("let" pat (":" ty)? "=" expr | expr) ";")* expr? "}"
//! pat     := x | "(" x "," y ")" | "_"
//! expr    := "|" x ":" ty "|" expr
//!          | "match" expr "{" "Left(" x ")" "=>" expr "," "Right(" y ")" "=>" expr ","? "}"
//!          | postfix
//! postfix := primary ("(" expr,* ")" | "." n | "." name | ".clone()")*
//! primary := x | n | "()" | "(" expr ")" | "(" expr "," expr ")" | block
//!          | "with(" expr "," expr ")" | "Left(" expr ")" | "Right(" expr ")"
//!          | Name "{" (field ":" expr),* "}"
//! ```

use crate::diagnostic::{Diagnostic, Label};
use crate::syntax::*;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok {
    Ident(String),
    Int(i64),
    Sym(&'static str),
    Eof,
}

#[derive(Clone, Debug)]
struct Token {
    tok: Tok,
    span: Span,
}

const SYMBOLS: [&str; 20] = [
    "->", "=>", "(", ")", "{", "}", "<", ">", ",", ";", ":", ".", "|", "=", "&", "#",
    "[", "]", "_", "!",
];

fn lex(src: &str) -> Result<Vec<Token>, Diagnostic> {
    let bytes = src.as_bytes();
    let mut tokens = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i] as char;
        if c.is_whitespace() {
            i += 1;
        } else if src[i..].starts_with("//") {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
        } else if c.is_ascii_alphabetic() || (c == '_' && is_ident_char(bytes, i + 1)) {
            let start = i;
            while is_ident_char(bytes, i) {
                i += 1;
            }
            let span = Span::new(start, i);
            tokens.push(Token {
                tok: Tok::Ident(src[start..i].to_string()),
                span,
            });
        } else if c.is_ascii_digit() {
            let start = i;
            while i < bytes.len() && (bytes[i] as char).is_ascii_digit() {
                i += 1;
            }
            let n = src[start..i].parse().unwrap_or(i64::MAX);
            tokens.push(Token {
                tok: Tok::Int(n),
                span: Span::new(start, i),
            });
        } else if let Some(sym) = SYMBOLS.iter().find(|s| src[i..].starts_with(**s)) {
            tokens.push(Token {
                tok: Tok::Sym(sym),
                span: Span::new(i, i + sym.len()),
            });
            i += sym.len();
        } else {
            let span = Span::new(i, i + c.len_utf8());
            return Err(Diagnostic::error(&format!("unknown start of token: {c}"))
                .with(Label::primary(span, "")));
        }
    }
    tokens.push(Token {
        tok: Tok::Eof,
        span: Span::new(src.len(), src.len()),
    });
    Ok(tokens)
}

fn is_ident_char(bytes: &[u8], i: usize) -> bool {
    i < bytes.len() && ((bytes[i] as char).is_ascii_alphanumeric() || bytes[i] == b'_')
}

/// Parse a whole program.
pub fn parse_program(src: &str) -> Result<Program, Diagnostic> {
    let mut p = Parser {
        tokens: lex(src)?,
        pos: 0,
    };
    let mut items = Vec::new();
    while p.peek() != &Tok::Eof {
        items.push(p.item()?);
    }
    Ok(Program { items })
}

/// Parse a single expression (used by the tests).
pub fn parse_expr(src: &str) -> Result<Expr, Diagnostic> {
    let mut p = Parser {
        tokens: lex(src)?,
        pos: 0,
    };
    let e = p.expr()?;
    p.expect_eof()?;
    Ok(e)
}

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

const KEYWORDS: [&str; 10] = [
    "fn", "let", "match", "struct", "impl", "for", "mut", "with", "Left", "Right",
];

impl Parser {
    fn peek(&self) -> &Tok {
        &self.tokens[self.pos].tok
    }

    fn peek_at(&self, k: usize) -> &Tok {
        let i = (self.pos + k).min(self.tokens.len() - 1);
        &self.tokens[i].tok
    }

    fn span(&self) -> Span {
        self.tokens[self.pos].span
    }

    fn prev_span(&self) -> Span {
        self.tokens[self.pos.saturating_sub(1)].span
    }

    fn bump(&mut self) -> Token {
        let t = self.tokens[self.pos].clone();
        if self.pos + 1 < self.tokens.len() {
            self.pos += 1;
        }
        t
    }

    fn is_sym(&self, s: &str) -> bool {
        matches!(self.peek(), Tok::Sym(x) if *x == s)
    }

    fn is_kw(&self, k: &str) -> bool {
        matches!(self.peek(), Tok::Ident(x) if x == k)
    }

    fn eat_sym(&mut self, s: &str) -> bool {
        if self.is_sym(s) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn found(&self) -> String {
        match self.peek() {
            Tok::Ident(x) => format!("`{x}`"),
            Tok::Int(n) => format!("`{n}`"),
            Tok::Sym(s) => format!("`{s}`"),
            Tok::Eof => "end of input".to_string(),
        }
    }

    fn error(&self, expected: &str) -> Diagnostic {
        let msg = format!("expected {expected}, found {}", self.found());
        Diagnostic::error(&msg)
            .with(Label::primary(self.span(), &format!("expected {expected}")))
    }

    fn expect_sym(&mut self, s: &str) -> Result<Span, Diagnostic> {
        if self.is_sym(s) {
            Ok(self.bump().span)
        } else {
            Err(self.error(&format!("`{s}`")))
        }
    }

    fn expect_kw(&mut self, k: &str) -> Result<Span, Diagnostic> {
        if self.is_kw(k) {
            Ok(self.bump().span)
        } else {
            Err(self.error(&format!("`{k}`")))
        }
    }

    fn expect_eof(&self) -> Result<(), Diagnostic> {
        if self.peek() == &Tok::Eof {
            Ok(())
        } else {
            Err(self.error("end of input"))
        }
    }

    fn ident(&mut self) -> Result<Ident, Diagnostic> {
        match self.peek().clone() {
            Tok::Ident(name) if !KEYWORDS.contains(&name.as_str()) => {
                let span = self.bump().span;
                Ok(Ident { name, span })
            }
            _ => Err(self.error("an identifier")),
        }
    }

    // ---------------------------------------------------------------- items

    fn item(&mut self) -> Result<Item, Diagnostic> {
        let mut derives = Vec::new();
        if self.eat_sym("#") {
            self.expect_sym("[")?;
            self.expect_kw("derive")?;
            self.expect_sym("(")?;
            while !self.is_sym(")") {
                derives.push(self.ident()?);
                if !self.eat_sym(",") {
                    break;
                }
            }
            self.expect_sym(")")?;
            self.expect_sym("]")?;
        }
        if self.is_kw("struct") {
            self.bump();
            let name = self.ident()?;
            self.expect_sym("{")?;
            let mut fields = Vec::new();
            while !self.is_sym("}") {
                let f = self.ident()?;
                self.expect_sym(":")?;
                let ty = self.ty()?;
                let span = f.span.to(self.prev_span());
                fields.push((f, ty, span));
                if !self.eat_sym(",") {
                    break;
                }
            }
            self.expect_sym("}")?;
            return Ok(Item::Struct(StructDef {
                name,
                derives,
                fields,
            }));
        }
        if !derives.is_empty() {
            return Err(self.error("`struct` after a derive attribute"));
        }
        if self.is_kw("impl") {
            let start = self.bump().span;
            self.expect_kw("Drop")?;
            self.expect_kw("for")?;
            let ty = self.ident()?;
            self.expect_sym("{")?;
            let end = self.expect_sym("}")?;
            return Ok(Item::DropImpl {
                ty,
                span: start.to(end),
            });
        }
        self.expect_kw("fn")?;
        let name = self.ident()?;
        self.expect_sym("(")?;
        let mut params = Vec::new();
        while !self.is_sym(")") {
            let x = self.ident()?;
            self.expect_sym(":")?;
            params.push((x, self.ty()?));
            if !self.eat_sym(",") {
                break;
            }
        }
        self.expect_sym(")")?;
        let ret = if self.eat_sym("->") {
            self.ty()?
        } else {
            Ty::Unit
        };
        let body = if self.eat_sym(";") {
            None
        } else {
            Some(self.block()?)
        };
        Ok(Item::Fn(FnDef {
            name,
            params,
            ret,
            body,
        }))
    }

    // ---------------------------------------------------------------- types

    fn ty(&mut self) -> Result<Ty, Diagnostic> {
        if self.eat_sym("(") {
            if self.eat_sym(")") {
                return Ok(Ty::Unit);
            }
            let a = self.ty()?;
            if self.eat_sym(")") {
                return Ok(a);
            }
            self.expect_sym(",")?;
            let b = self.ty()?;
            self.expect_sym(")")?;
            return Ok(Ty::tuple(a, b));
        }
        if self.eat_sym("&") {
            let mutable = if self.is_kw("mut") {
                self.bump();
                true
            } else {
                false
            };
            let inner = Box::new(self.ty()?);
            return Ok(Ty::Ref { mutable, inner });
        }
        let name = match self.peek().clone() {
            Tok::Ident(name) => name,
            _ => return Err(self.error("a type")),
        };
        self.bump();
        match name.as_str() {
            "FnOnce" => {
                self.expect_sym("(")?;
                let a = self.ty()?;
                self.expect_sym(")")?;
                self.expect_sym("->")?;
                let b = self.ty()?;
                Ok(Ty::func(a, b))
            }
            "With" | "Either" => {
                self.expect_sym("<")?;
                let a = Box::new(self.ty()?);
                self.expect_sym(",")?;
                let b = Box::new(self.ty()?);
                self.expect_sym(">")?;
                Ok(if name == "With" {
                    Ty::With(a, b)
                } else {
                    Ty::Either(a, b)
                })
            }
            "Rc" => {
                self.expect_sym("<")?;
                let a = self.ty()?;
                self.expect_sym(">")?;
                Ok(Ty::Rc(Box::new(a)))
            }
            _ => Ok(Ty::Named(name)),
        }
    }

    // ---------------------------------------------------------------- expressions

    fn block(&mut self) -> Result<Expr, Diagnostic> {
        let open = self.expect_sym("{")?;
        // Statements, collected first and folded into nested `Let`s at the end.
        let mut stmts: Vec<(Pat, Option<Ty>, Expr, Span)> = Vec::new();
        let tail;
        loop {
            if self.is_sym("}") {
                let span = self.span();
                tail = Expr {
                    kind: ExprKind::Unit,
                    span: Span::new(span.start, span.start),
                };
                break;
            }
            if self.is_kw("let") {
                let start = self.bump().span;
                let pat = if self.eat_sym("_") {
                    Pat::Wild
                } else if self.eat_sym("(") {
                    let x = self.ident()?;
                    self.expect_sym(",")?;
                    let y = self.ident()?;
                    self.expect_sym(")")?;
                    Pat::Pair(x, y)
                } else {
                    Pat::Var(self.ident()?)
                };
                let ty = if self.eat_sym(":") {
                    Some(self.ty()?)
                } else {
                    None
                };
                self.expect_sym("=")?;
                let value = self.expr()?;
                let end = self.expect_sym(";")?;
                stmts.push((pat, ty, value, start.to(end)));
                continue;
            }
            let e = self.expr()?;
            if self.is_sym(";") {
                let end = self.bump().span;
                let span = e.span.to(end);
                stmts.push((Pat::Wild, None, e, span));
            } else {
                tail = e;
                break;
            }
        }
        let close = self.expect_sym("}")?;
        let mut body = tail;
        for (pat, ty, value, span) in stmts.into_iter().rev() {
            let span = span.to(body.span);
            body = Expr {
                kind: ExprKind::Let {
                    pat,
                    ty,
                    value: Box::new(value),
                    body: Box::new(body),
                },
                span,
            };
        }
        if !matches!(body.kind, ExprKind::Let { .. })
            && body.span.start == body.span.end
        {
            body.span = open.to(close);
        }
        Ok(body)
    }

    fn expr(&mut self) -> Result<Expr, Diagnostic> {
        if self.is_sym("|") {
            let start = self.bump().span;
            let param = self.ident()?;
            self.expect_sym(":")?;
            let ty = self.ty()?;
            let head_end = self.expect_sym("|")?;
            let body = self.expr()?;
            let span = start.to(body.span);
            return Ok(Expr {
                kind: ExprKind::Closure {
                    param,
                    ty,
                    body: Box::new(body),
                    head: start.to(head_end),
                },
                span,
            });
        }
        self.postfix()
    }

    fn postfix(&mut self) -> Result<Expr, Diagnostic> {
        let mut e = self.primary()?;
        loop {
            if self.is_sym("(") {
                let callee = match &e.kind {
                    ExprKind::Var(name) => Ident {
                        name: name.clone(),
                        span: e.span,
                    },
                    _ => {
                        return Err(
                            self.error("`;` (only named functions can be called)")
                        );
                    }
                };
                self.bump();
                let mut args = Vec::new();
                while !self.is_sym(")") {
                    args.push(self.expr()?);
                    if !self.eat_sym(",") {
                        break;
                    }
                }
                let end = self.expect_sym(")")?;
                e = Expr {
                    span: e.span.to(end),
                    kind: ExprKind::Call { callee, args },
                };
            } else if self.is_sym(".") {
                let dot = self.bump().span;
                match self.peek().clone() {
                    Tok::Int(n) => {
                        let end = self.bump().span;
                        e = Expr {
                            span: e.span.to(end),
                            kind: ExprKind::Field(
                                Box::new(e),
                                Proj::Index(n as usize),
                                dot.to(end),
                            ),
                        };
                    }
                    Tok::Ident(name)
                        if name == "clone" && self.peek_at(1) == &Tok::Sym("(") =>
                    {
                        self.bump();
                        self.bump();
                        let end = self.expect_sym(")")?;
                        e = Expr {
                            span: e.span.to(end),
                            kind: ExprKind::Clone(Box::new(e)),
                        };
                    }
                    Tok::Ident(name) => {
                        let end = self.bump().span;
                        e = Expr {
                            span: e.span.to(end),
                            kind: ExprKind::Field(
                                Box::new(e),
                                Proj::Field(name),
                                dot.to(end),
                            ),
                        };
                    }
                    _ => return Err(self.error("a field name")),
                }
            } else {
                return Ok(e);
            }
        }
    }

    fn primary(&mut self) -> Result<Expr, Diagnostic> {
        let start = self.span();
        match self.peek().clone() {
            Tok::Int(n) => {
                self.bump();
                Ok(Expr {
                    kind: ExprKind::Int(n),
                    span: start,
                })
            }
            Tok::Sym("(") => {
                self.bump();
                if self.is_sym(")") {
                    let end = self.bump().span;
                    return Ok(Expr {
                        kind: ExprKind::Unit,
                        span: start.to(end),
                    });
                }
                let a = self.expr()?;
                if self.is_sym(")") {
                    self.bump();
                    return Ok(a);
                }
                self.expect_sym(",")?;
                let b = self.expr()?;
                let end = self.expect_sym(")")?;
                Ok(Expr {
                    kind: ExprKind::Tuple(Box::new(a), Box::new(b)),
                    span: start.to(end),
                })
            }
            Tok::Sym("{") => self.block(),
            Tok::Ident(kw) if kw == "match" => {
                self.bump();
                let scrutinee = self.expr()?;
                self.expect_sym("{")?;
                self.expect_kw("Left")?;
                self.expect_sym("(")?;
                let x = self.ident()?;
                self.expect_sym(")")?;
                self.expect_sym("=>")?;
                let left = self.expr()?;
                self.expect_sym(",")?;
                self.expect_kw("Right")?;
                self.expect_sym("(")?;
                let y = self.ident()?;
                self.expect_sym(")")?;
                self.expect_sym("=>")?;
                let right = self.expr()?;
                self.eat_sym(",");
                let end = self.expect_sym("}")?;
                Ok(Expr {
                    kind: ExprKind::Match {
                        scrutinee: Box::new(scrutinee),
                        left: (x, Box::new(left)),
                        right: (y, Box::new(right)),
                    },
                    span: start.to(end),
                })
            }
            Tok::Ident(kw) if kw == "with" => {
                self.bump();
                self.expect_sym("(")?;
                let a = self.expr()?;
                self.expect_sym(",")?;
                let b = self.expr()?;
                let end = self.expect_sym(")")?;
                Ok(Expr {
                    kind: ExprKind::With(Box::new(a), Box::new(b)),
                    span: start.to(end),
                })
            }
            Tok::Ident(kw) if kw == "Left" || kw == "Right" => {
                self.bump();
                self.expect_sym("(")?;
                let a = Box::new(self.expr()?);
                let end = self.expect_sym(")")?;
                let kind = if kw == "Left" {
                    ExprKind::Left(a)
                } else {
                    ExprKind::Right(a)
                };
                Ok(Expr {
                    kind,
                    span: start.to(end),
                })
            }
            Tok::Ident(name)
                if name.starts_with(|c: char| c.is_ascii_uppercase())
                    && self.peek_at(1) == &Tok::Sym("{") =>
            {
                let name = self.ident()?;
                self.expect_sym("{")?;
                let mut fields = Vec::new();
                while !self.is_sym("}") {
                    let f = self.ident()?;
                    self.expect_sym(":")?;
                    fields.push((f, self.expr()?));
                    if !self.eat_sym(",") {
                        break;
                    }
                }
                let end = self.expect_sym("}")?;
                Ok(Expr {
                    kind: ExprKind::StructLit { name, fields },
                    span: start.to(end),
                })
            }
            Tok::Ident(_) => {
                let x = self.ident()?;
                Ok(Expr {
                    kind: ExprKind::Var(x.name),
                    span: x.span,
                })
            }
            _ => Err(self.error("an expression")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_blocks_into_lets() {
        let e = parse_expr("{ let (x, y) = p; (y, x) }").unwrap();
        assert_eq!(show_expr(&e), "let (x, y) = p; (y, x)");
    }

    #[test]
    fn parses_closures_calls_and_projections() {
        let e = parse_expr("|s: String| send(c, s.0, w.fst)").unwrap();
        assert_eq!(show_expr(&e), "|s: String| send(c, s.0, w.fst)");
        let e = parse_expr("match m { Left(a) => a, Right(b) => b.clone() }").unwrap();
        assert_eq!(
            show_expr(&e),
            "match m { Left(a) => a, Right(b) => b.clone() }"
        );
    }

    #[test]
    fn parses_items_and_types() {
        let p = parse_program(
            "#[derive(Clone, Copy)] struct P { x: i32, y: (i32, bool) }
             impl Drop for Guard {}
             fn close(f: File);
             fn f(g: FnOnce(&mut String) -> With<Rc<A>, Either<B, ()>>) -> () { () }",
        )
        .unwrap();
        assert_eq!(p.items.len(), 4);
        let f = p.function("f").unwrap();
        assert_eq!(
            f.params[0].1.to_string(),
            "FnOnce(&mut String) -> With<Rc<A>, Either<B, ()>>"
        );
        assert!(p.has_drop("Guard"));
        assert_eq!(p.structure("P").unwrap().fields.len(), 2);
    }

    #[test]
    fn reports_parse_errors() {
        let err = parse_program("fn f(x: A) -> A { let y = x }").unwrap_err();
        assert_eq!(err.message, "expected `;`, found `}`");
    }
}
