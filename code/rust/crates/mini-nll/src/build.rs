//! A small builder for writing MIR bodies by hand.
//!
//! Spans are given by *content* rather than by line and column: `span("let
//! first", "readings")` is the first occurrence of `readings` in the first line
//! of the function that contains `let first`. The source files can then change
//! (a doc comment added above the function) without breaking the programs.

use crate::mir::*;

pub struct Builder {
    body: Body,
    lines: Vec<&'static str>,
    /// Index of the line where the function starts.
    fn_start: usize,
}

impl Builder {
    /// Start a body for `fn name` defined in `source` (the text of `file`).
    pub fn new(
        name: &'static str,
        file: &'static str,
        source: &'static str,
    ) -> Builder {
        let lines: Vec<&'static str> = source.lines().collect();
        let header = format!("fn {name}");
        let fn_start = lines
            .iter()
            .position(|l| l.contains(&header))
            .unwrap_or_else(|| panic!("`{header}` not found in {file}"));
        Builder {
            body: Body {
                name,
                file,
                source,
                arg_count: 0,
                locals: Vec::new(),
                regions: Vec::new(),
                blocks: Vec::new(),
            },
            lines,
            fn_start,
        }
    }

    /// The first occurrence of `needle` in the first line of the function
    /// that contains `line`.
    pub fn span(&self, line: &str, needle: &str) -> Span {
        self.span_nth(line, needle, 0)
    }

    /// The `nth` (0-based) occurrence of `needle` in that line.
    pub fn span_nth(&self, line: &str, needle: &str, nth: usize) -> Span {
        let (index, text) = self
            .lines
            .iter()
            .enumerate()
            .skip(self.fn_start)
            .find(|(_, l)| l.contains(line))
            .unwrap_or_else(|| {
                panic!("no line containing `{line}` in {}", self.body.name)
            });
        let byte = text
            .match_indices(needle)
            .nth(nth)
            .unwrap_or_else(|| panic!("`{needle}` not found in `{text}`"))
            .0;
        let start = text[..byte].chars().count();
        Span {
            line: index + 1,
            start,
            end: start + needle.chars().count(),
        }
    }

    /// The first line of the function that is exactly `line` (for lines
    /// such as `    log` that occur inside longer ones), as a span from its
    /// first non-blank character.
    pub fn span_exact(&self, line: &str) -> Span {
        let index = (self.fn_start..self.lines.len())
            .find(|&i| self.lines[i] == line)
            .unwrap_or_else(|| panic!("no line `{line}` in {}", self.body.name));
        let text = line.trim_start();
        let start = line.chars().count() - text.chars().count();
        Span {
            line: index + 1,
            start,
            end: start + text.chars().count(),
        }
    }

    /// The closing brace of the function: the first line after its start
    /// that is exactly `}`.
    pub fn closing_brace(&self) -> Span {
        self.span_exact("}")
    }

    /// A fresh region inference variable.
    pub fn region(&mut self) -> RegionVid {
        self.body.regions.push(RegionDecl {
            name: None,
            span: None,
        });
        RegionVid(self.body.regions.len() - 1)
    }

    /// A named lifetime parameter of the function, such as `'r`.
    pub fn universal(&mut self, name: &'static str, span: Span) -> RegionVid {
        self.body.regions.push(RegionDecl {
            name: Some(name),
            span: Some(span),
        });
        RegionVid(self.body.regions.len() - 1)
    }

    /// `&'? T` with a fresh region.
    pub fn shared(&mut self, ty: Ty) -> Ty {
        Ty::Ref(self.region(), Mutability::Not, Box::new(ty))
    }

    /// `&'? mut T` with a fresh region.
    pub fn mutable(&mut self, ty: Ty) -> Ty {
        Ty::Ref(self.region(), Mutability::Mut, Box::new(ty))
    }

    fn push_local(
        &mut self,
        name: Option<&'static str>,
        ty: Ty,
        span: Option<Span>,
    ) -> Local {
        self.body.locals.push(LocalDecl { name, ty, span });
        Local(self.body.locals.len() - 1)
    }

    /// The return place `_0`; must be declared first.
    pub fn ret(&mut self, ty: Ty) -> Local {
        assert!(self.body.locals.is_empty(), "the return place is `_0`");
        self.push_local(None, ty, None)
    }

    /// An argument; arguments are declared right after the return place.
    pub fn arg(&mut self, name: &'static str, ty: Ty, span: Span) -> Local {
        assert_eq!(self.body.locals.len(), self.body.arg_count + 1);
        self.body.arg_count += 1;
        self.push_local(Some(name), ty, Some(span))
    }

    /// A user variable, with the span of its binding.
    pub fn var(&mut self, name: &'static str, ty: Ty, span: Span) -> Local {
        self.push_local(Some(name), ty, Some(span))
    }

    /// A compiler temporary.
    pub fn temp(&mut self, ty: Ty) -> Local {
        self.push_local(None, ty, None)
    }

    pub fn block(&mut self) -> BlockId {
        self.body.blocks.push(BasicBlock {
            statements: Vec::new(),
            terminator: Terminator {
                kind: TerminatorKind::Return,
                span: None,
                callee_span: None,
            },
        });
        BlockId(self.body.blocks.len() - 1)
    }

    pub fn statement(&mut self, bb: BlockId, kind: StatementKind, span: Option<Span>) {
        self.body.blocks[bb.0]
            .statements
            .push(Statement { kind, span });
    }

    pub fn storage_live(&mut self, bb: BlockId, local: Local) {
        self.statement(bb, StatementKind::StorageLive(local), None);
    }

    pub fn storage_dead(&mut self, bb: BlockId, local: Local) {
        self.statement(bb, StatementKind::StorageDead(local), None);
    }

    /// `StorageDead` of a user variable at the end of its scope, with the
    /// span of the closing brace (used by the lexical checker's messages).
    pub fn storage_dead_at(&mut self, bb: BlockId, local: Local, span: Span) {
        self.statement(bb, StatementKind::StorageDead(local), Some(span));
    }

    pub fn fake_read(&mut self, bb: BlockId, local: Local) {
        self.statement(bb, StatementKind::FakeRead(local), None);
    }

    pub fn assign(
        &mut self,
        bb: BlockId,
        dest: impl Into<Place>,
        rv: Rvalue,
        span: Option<Span>,
    ) {
        self.statement(bb, StatementKind::Assign(dest.into(), rv), span);
    }

    /// `dest = &'k place` (or `&'k mut place`), with a fresh loan region `'k`.
    pub fn borrow(
        &mut self,
        bb: BlockId,
        dest: impl Into<Place>,
        kind: BorrowKind,
        place: impl Into<Place>,
        span: Span,
    ) {
        let k = self.region();
        self.assign(bb, dest, Rvalue::Ref(k, kind, place.into()), Some(span));
    }

    fn terminate(&mut self, bb: BlockId, kind: TerminatorKind, span: Option<Span>) {
        let term = &mut self.body.blocks[bb.0].terminator;
        term.kind = kind;
        term.span = span;
    }

    /// `dest = func(args) -> target`. Returns a handle to add the spans and,
    /// for functions that return a borrow, the argument it borrows from.
    pub fn call(
        &mut self,
        bb: BlockId,
        dest: impl Into<Place>,
        func: &'static str,
        args: Vec<Operand>,
        target: BlockId,
    ) -> CallRef<'_> {
        let kind = TerminatorKind::Call {
            func,
            args,
            dest: dest.into(),
            target,
            result_borrows_from: None,
        };
        self.terminate(bb, kind, None);
        CallRef {
            term: &mut self.body.blocks[bb.0].terminator,
        }
    }

    pub fn goto(&mut self, bb: BlockId, target: BlockId) {
        self.terminate(bb, TerminatorKind::Goto(target), None);
    }

    pub fn switch(
        &mut self,
        bb: BlockId,
        discr: Operand,
        targets: Vec<(&'static str, BlockId)>,
    ) {
        self.terminate(bb, TerminatorKind::SwitchInt { discr, targets }, None);
    }

    pub fn drop(&mut self, bb: BlockId, place: impl Into<Place>, target: BlockId) {
        let kind = TerminatorKind::Drop {
            place: place.into(),
            target,
        };
        self.terminate(bb, kind, None);
    }

    pub fn ret_term(&mut self, bb: BlockId) {
        self.terminate(bb, TerminatorKind::Return, None);
    }

    pub fn finish(self) -> Body {
        self.body
    }
}

/// A call terminator under construction.
pub struct CallRef<'a> {
    term: &'a mut Terminator,
}

impl CallRef<'_> {
    /// The span of the whole call and of the function or method name.
    pub fn spans(self, call: Span, callee: Span) -> Self {
        self.term.span = Some(call);
        self.term.callee_span = Some(callee);
        self
    }

    /// The signature ties the result's regions to argument `arg`'s, as in
    /// `fn index<'a>(&'a Vec<T>, usize) -> &'a T`.
    pub fn borrows_from(self, arg: usize) -> Self {
        if let TerminatorKind::Call {
            result_borrows_from,
            ..
        } = &mut self.term.kind
        {
            *result_borrows_from = Some(arg);
        }
        self
    }
}

/// `copy p`
pub fn copy(p: impl Into<Place>) -> Operand {
    Operand::Copy(p.into())
}

/// `move p`
pub fn mv(p: impl Into<Place>) -> Operand {
    Operand::Move(p.into())
}

/// `const c`
pub fn cst(c: &'static str) -> Operand {
    Operand::Const(c)
}

/// The place `*p`.
pub fn deref(p: Local) -> Place {
    Place::from(p).deref()
}
