//! The miniature MIR: locals, places, operands, statements, terminators and
//! basic blocks.
//!
//! The shapes follow rustc's MIR closely enough that the hand-built bodies in
//! `programs.rs` read like trimmed dumps of the real thing. Everything the
//! analyses of Chapter 29 do not need is left out: unwinding edges and cleanup
//! blocks, most rvalues, and the real type system (a type here is just enough
//! to know which regions it mentions, whether it is `Copy` and whether it has a
//! destructor).

use std::fmt;

// ANCHOR: ids
/// A local: `_0` is the return place, `_1 ..= _n` are the arguments, and the
/// rest are user variables and compiler temporaries.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Local(pub usize);

/// A basic block, printed `bb3`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BlockId(pub usize);

/// A program point: statement `index` of `block`. The terminator of a block
/// with `n` statements is at index `n`. Printed `bb3[1]`, as rustc does.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Location {
    pub block: BlockId,
    pub index: usize,
}

/// A region (lifetime) variable, printed `'?4` like rustc's inference
/// variables, or by its name (`'r`) if it is a named lifetime parameter.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RegionVid(pub usize);
// ANCHOR_END: ids

// ANCHOR: place
/// One step of a path into memory.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProjectionElem {
    /// `*p`: follow a reference.
    Deref,
    /// `p.0`, `p.1`: a field of a struct, a tuple or an enum variant.
    Field(usize),
    /// `(p as Some)`: view an enum value as one of its variants.
    Downcast(&'static str),
}

/// A place: a local followed by projections, such as `_1`, `(*_1)` or
/// `(_3 as Some).0`. Moves, borrows and assignments all act on places.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Place {
    pub local: Local,
    pub projection: Vec<ProjectionElem>,
}
// ANCHOR_END: place

impl Place {
    pub fn deref(mut self) -> Place {
        self.projection.push(ProjectionElem::Deref);
        self
    }

    pub fn field(mut self, index: usize) -> Place {
        self.projection.push(ProjectionElem::Field(index));
        self
    }

    pub fn downcast(mut self, variant: &'static str) -> Place {
        self.projection.push(ProjectionElem::Downcast(variant));
        self
    }

    /// `self` is `other` or a path that `other` extends: `_3` is a prefix of
    /// `(_3 as Some).0`.
    pub fn is_prefix_of(&self, other: &Place) -> bool {
        self.local == other.local
            && self.projection.len() <= other.projection.len()
            && other.projection[..self.projection.len()] == self.projection[..]
    }

    pub fn has_deref(&self) -> bool {
        self.projection.contains(&ProjectionElem::Deref)
    }

    /// The *move path* of a place: the place cut at its first dereference.
    /// Moves and initialization are tracked for move paths only: what lies
    /// behind a reference is not owned by this function.
    pub fn move_path(&self) -> Place {
        let end = self
            .projection
            .iter()
            .position(|p| *p == ProjectionElem::Deref)
            .unwrap_or(self.projection.len());
        Place {
            local: self.local,
            projection: self.projection[..end].to_vec(),
        }
    }
}

impl From<Local> for Place {
    fn from(local: Local) -> Place {
        Place {
            local,
            projection: Vec::new(),
        }
    }
}

// ANCHOR: ty
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mutability {
    Not,
    Mut,
}

/// Just enough of a type to know the regions it mentions, whether it is
/// `Copy`, and whether it has a destructor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    /// `i32`, `usize`, `bool`, `()`: `Copy`, no destructor.
    Scalar(&'static str),
    /// `String`, `Vec<i32>`, `HashMap<u32, String>`: owns memory, is not
    /// `Copy`, has a destructor, and mentions no regions.
    Owned(&'static str),
    /// `&'a T` and `&'a mut T`.
    Ref(RegionVid, Mutability, Box<Ty>),
    /// A generic enum or struct applied to arguments: `Option<&'a mut String>`.
    Adt(&'static str, Vec<Ty>),
}
// ANCHOR_END: ty

impl Ty {
    /// Every region the type mentions, outermost first.
    pub fn regions(&self) -> Vec<RegionVid> {
        let mut out = Vec::new();
        self.collect_regions(&mut out);
        out
    }

    fn collect_regions(&self, out: &mut Vec<RegionVid>) {
        match self {
            Ty::Scalar(_) | Ty::Owned(_) => {}
            Ty::Ref(r, _, pointee) => {
                out.push(*r);
                pointee.collect_regions(out);
            }
            Ty::Adt(_, args) => args.iter().for_each(|a| a.collect_regions(out)),
        }
    }

    /// `Copy` types may be used again after being "moved".
    pub fn is_copy(&self) -> bool {
        match self {
            Ty::Scalar(_) => true,
            Ty::Owned(_) => false,
            Ty::Ref(_, Mutability::Not, _) => true,
            Ty::Ref(_, Mutability::Mut, _) => false,
            Ty::Adt(_, args) => args.iter().all(Ty::is_copy),
        }
    }

    /// Does dropping a value of this type run code?
    pub fn needs_drop(&self) -> bool {
        match self {
            Ty::Scalar(_) | Ty::Ref(..) => false,
            Ty::Owned(_) => true,
            Ty::Adt(_, args) => args.iter().any(Ty::needs_drop),
        }
    }

    /// The type of `place.elem` when `place` has type `self`.
    pub fn project(&self, elem: ProjectionElem) -> Ty {
        match (self, elem) {
            (Ty::Ref(_, _, pointee), ProjectionElem::Deref) => (**pointee).clone(),
            (_, ProjectionElem::Downcast(_)) => self.clone(),
            (Ty::Adt(_, args), ProjectionElem::Field(i)) => args[i].clone(),
            _ => panic!("cannot project {elem:?} out of {self:?}"),
        }
    }
}

/// Shorthands used by the hand-built programs.
pub fn scalar(name: &'static str) -> Ty {
    Ty::Scalar(name)
}

pub fn owned(name: &'static str) -> Ty {
    Ty::Owned(name)
}

pub fn adt(name: &'static str, args: Vec<Ty>) -> Ty {
    Ty::Adt(name, args)
}

// ANCHOR: rvalue
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BorrowKind {
    /// `&p`
    Shared,
    /// `&mut p`
    Mut,
    /// A `&mut p` inserted by the compiler (method receivers, implicit
    /// reborrows of arguments, overloaded compound assignment). It is only
    /// *reserved* when created and *activated* at its first use.
    TwoPhaseMut,
}

/// An operand: how a value is read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Operand {
    /// Read a `Copy` value; the place stays initialized.
    Copy(Place),
    /// Move the value out; the place becomes uninitialized.
    Move(Place),
    /// A constant such as `const 40_i32`.
    Const(&'static str),
}

/// The right-hand side of an assignment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Rvalue {
    Use(Operand),
    /// `&'k p` or `&'k mut p`. Every borrow expression creates a *loan*, and
    /// `'k` is the loan's region.
    Ref(RegionVid, BorrowKind, Place),
    BinaryOp(&'static str, Operand, Operand),
    /// `discriminant(p)`: which variant an enum value is (used by `match`).
    Discriminant(Place),
}
// ANCHOR_END: rvalue

impl Operand {
    pub fn place(&self) -> Option<&Place> {
        match self {
            Operand::Copy(p) | Operand::Move(p) => Some(p),
            Operand::Const(_) => None,
        }
    }
}

impl Rvalue {
    /// The operands the rvalue reads.
    pub fn operands(&self) -> Vec<&Operand> {
        match self {
            Rvalue::Use(op) => vec![op],
            Rvalue::BinaryOp(_, a, b) => vec![a, b],
            Rvalue::Ref(..) | Rvalue::Discriminant(_) => vec![],
        }
    }

    /// Every place the rvalue mentions (read, moved or borrowed).
    pub fn places(&self) -> Vec<&Place> {
        match self {
            Rvalue::Ref(_, _, p) | Rvalue::Discriminant(p) => vec![p],
            _ => self
                .operands()
                .into_iter()
                .filter_map(Operand::place)
                .collect(),
        }
    }
}

/// A region of the source text: 1-based `line`, 0-based columns
/// `start..end` (in characters).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Span {
    pub line: usize,
    pub start: usize,
    pub end: usize,
}

// ANCHOR: statement
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StatementKind {
    Assign(Place, Rvalue),
    /// The local's storage is allocated: it is now in scope, uninitialized.
    StorageLive(Local),
    /// The local's storage is freed: it goes out of scope.
    StorageDead(Local),
    /// `let x = ...;` marks the binding as read (rustc's `FakeRead(ForLet)`).
    FakeRead(Local),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TerminatorKind {
    Goto(BlockId),
    /// Jump on the value of an integer: `[0: bb4, otherwise: bb2]`.
    SwitchInt {
        discr: Operand,
        targets: Vec<(&'static str, BlockId)>,
    },
    /// `dest = func(args) -> target`. If `result_borrows_from` is
    /// `Some(i)`, the signature ties the regions of the result to the regions
    /// of argument `i`, as in `fn index<'a>(&'a Vec<T>, usize) -> &'a T`.
    Call {
        func: &'static str,
        args: Vec<Operand>,
        dest: Place,
        target: BlockId,
        result_borrows_from: Option<usize>,
    },
    /// Run the destructor of `place` (if it is still initialized).
    Drop {
        place: Place,
        target: BlockId,
    },
    Return,
}
// ANCHOR_END: statement

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Statement {
    pub kind: StatementKind,
    pub span: Option<Span>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Terminator {
    pub kind: TerminatorKind,
    /// The whole call expression (or other source construct).
    pub span: Option<Span>,
    /// For calls: the name of the function or method, for "used by call".
    pub callee_span: Option<Span>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BasicBlock {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalDecl {
    /// The user variable this local stands for (`debug job => _2`).
    pub name: Option<&'static str>,
    pub ty: Ty,
    pub span: Option<Span>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegionDecl {
    /// `Some("'r")` for a named lifetime parameter of the function: a
    /// *universal* region, chosen by the caller. `None` for an inference
    /// variable.
    pub name: Option<&'static str>,
    pub span: Option<Span>,
}

// ANCHOR: body
/// A function body: a control-flow graph of basic blocks over a set of locals.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Body {
    pub name: &'static str,
    /// The source file the body was hand-translated from, and its text, for
    /// diagnostics.
    pub file: &'static str,
    pub source: &'static str,
    pub arg_count: usize,
    pub locals: Vec<LocalDecl>,
    pub regions: Vec<RegionDecl>,
    pub blocks: Vec<BasicBlock>,
}
// ANCHOR_END: body

impl Body {
    pub fn decl(&self, local: Local) -> &LocalDecl {
        &self.locals[local.0]
    }

    pub fn block_ids(&self) -> impl Iterator<Item = BlockId> + '_ {
        (0..self.blocks.len()).map(BlockId)
    }

    pub fn successors(&self, bb: BlockId) -> Vec<BlockId> {
        match &self.blocks[bb.0].terminator.kind {
            TerminatorKind::Goto(t) => vec![*t],
            TerminatorKind::SwitchInt { targets, .. } => {
                targets.iter().map(|(_, t)| *t).collect()
            }
            TerminatorKind::Call { target, .. }
            | TerminatorKind::Drop { target, .. } => {
                vec![*target]
            }
            TerminatorKind::Return => vec![],
        }
    }

    pub fn predecessors(&self) -> Vec<Vec<BlockId>> {
        let mut preds = vec![Vec::new(); self.blocks.len()];
        for bb in self.block_ids() {
            for succ in self.successors(bb) {
                if !preds[succ.0].contains(&bb) {
                    preds[succ.0].push(bb);
                }
            }
        }
        preds
    }

    pub fn terminator_location(&self, bb: BlockId) -> Location {
        Location {
            block: bb,
            index: self.blocks[bb.0].statements.len(),
        }
    }

    pub fn is_terminator(&self, loc: Location) -> bool {
        loc.index == self.blocks[loc.block.0].statements.len()
    }

    /// Every program point, block by block.
    pub fn locations(&self) -> Vec<Location> {
        let mut out = Vec::new();
        for bb in self.block_ids() {
            for index in 0..=self.blocks[bb.0].statements.len() {
                out.push(Location { block: bb, index });
            }
        }
        out
    }

    pub fn successor_locations(&self, loc: Location) -> Vec<Location> {
        if self.is_terminator(loc) {
            self.successors(loc.block)
                .into_iter()
                .map(|block| Location { block, index: 0 })
                .collect()
        } else {
            vec![Location {
                block: loc.block,
                index: loc.index + 1,
            }]
        }
    }

    pub fn predecessor_locations(&self, loc: Location) -> Vec<Location> {
        if loc.index > 0 {
            vec![Location {
                block: loc.block,
                index: loc.index - 1,
            }]
        } else {
            self.predecessors()[loc.block.0]
                .iter()
                .map(|&bb| self.terminator_location(bb))
                .collect()
        }
    }

    pub fn place_ty(&self, place: &Place) -> Ty {
        let mut ty = self.decl(place.local).ty.clone();
        for elem in &place.projection {
            ty = ty.project(*elem);
        }
        ty
    }

    pub fn is_universal(&self, r: RegionVid) -> bool {
        self.regions[r.0].name.is_some()
    }

    pub fn universal_regions(&self) -> Vec<RegionVid> {
        (0..self.regions.len())
            .map(RegionVid)
            .filter(|r| self.is_universal(*r))
            .collect()
    }

    pub fn region_name(&self, r: RegionVid) -> String {
        match self.regions[r.0].name {
            Some(name) => name.to_string(),
            None => format!("'?{}", r.0),
        }
    }

    /// The place as the user would write it: `readings`, `*cache`.
    pub fn describe_place(&self, place: &Place) -> String {
        let mut s = match self.decl(place.local).name {
            Some(name) => name.to_string(),
            None => format!("{}", place.local),
        };
        for (i, elem) in place.projection.iter().enumerate() {
            s = match elem {
                ProjectionElem::Deref if i == 0 => format!("*{s}"),
                ProjectionElem::Deref => format!("(*{s})"),
                ProjectionElem::Field(f) => format!("{s}.{f}"),
                ProjectionElem::Downcast(v) => format!("({s} as {v})"),
            };
        }
        s
    }

    pub fn fmt_ty(&self, ty: &Ty) -> String {
        match ty {
            Ty::Scalar(name) | Ty::Owned(name) => name.to_string(),
            Ty::Ref(r, m, pointee) => {
                let m = if *m == Mutability::Mut { "mut " } else { "" };
                format!("&{} {m}{}", self.region_name(*r), self.fmt_ty(pointee))
            }
            Ty::Adt(name, args) => {
                let args: Vec<String> = args.iter().map(|a| self.fmt_ty(a)).collect();
                format!("{name}<{}>", args.join(", "))
            }
        }
    }

    pub fn fmt_rvalue(&self, rv: &Rvalue) -> String {
        match rv {
            Rvalue::Use(op) => op.to_string(),
            Rvalue::Ref(r, kind, place) => {
                let m = if *kind == BorrowKind::Shared {
                    ""
                } else {
                    "mut "
                };
                format!("&{} {m}{place}", self.region_name(*r))
            }
            Rvalue::BinaryOp(op, a, b) => format!("{op}({a}, {b})"),
            Rvalue::Discriminant(place) => format!("discriminant({place})"),
        }
    }

    /// `&'k place` for a loan, with its location: `&'?6 _1 at bb1[3]`.
    pub fn fmt_rvalue_of_loan(&self, loan: &crate::borrowck::Loan) -> String {
        let rv = Rvalue::Ref(loan.region, loan.kind, loan.place.clone());
        format!("{} at {}", self.fmt_rvalue(&rv), loan.location)
    }

    pub fn fmt_statement(&self, stmt: &Statement) -> String {
        match &stmt.kind {
            StatementKind::Assign(place, rv) => {
                let note = match rv {
                    Rvalue::Ref(_, BorrowKind::TwoPhaseMut, _) => "    // two-phase",
                    _ => "",
                };
                format!("{place} = {};{note}", self.fmt_rvalue(rv))
            }
            StatementKind::StorageLive(l) => format!("StorageLive({l});"),
            StatementKind::StorageDead(l) => format!("StorageDead({l});"),
            StatementKind::FakeRead(l) => format!("FakeRead(ForLet, {l});"),
        }
    }

    pub fn fmt_terminator(&self, term: &Terminator) -> String {
        match &term.kind {
            TerminatorKind::Goto(t) => format!("goto -> {t};"),
            TerminatorKind::SwitchInt { discr, targets } => {
                let ts: Vec<String> =
                    targets.iter().map(|(v, t)| format!("{v}: {t}")).collect();
                format!("switchInt({discr}) -> [{}];", ts.join(", "))
            }
            TerminatorKind::Call {
                func,
                args,
                dest,
                target,
                ..
            } => {
                let args: Vec<String> = args.iter().map(|a| a.to_string()).collect();
                format!("{dest} = {func}({}) -> {target};", args.join(", "))
            }
            TerminatorKind::Drop { place, target } => {
                format!("drop({place}) -> {target};")
            }
            TerminatorKind::Return => "return;".to_string(),
        }
    }

    /// The text of the statement or terminator at `loc`.
    pub fn fmt_location(&self, loc: Location) -> String {
        let block = &self.blocks[loc.block.0];
        match block.statements.get(loc.index) {
            Some(stmt) => self.fmt_statement(stmt),
            None => self.fmt_terminator(&block.terminator),
        }
    }

    pub fn span_at(&self, loc: Location) -> Option<Span> {
        let block = &self.blocks[loc.block.0];
        match block.statements.get(loc.index) {
            Some(stmt) => stmt.span,
            None => block.terminator.span,
        }
    }
}

impl fmt::Display for Local {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "_{}", self.0)
    }
}

impl fmt::Display for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bb{}", self.0)
    }
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}[{}]", self.block, self.index)
    }
}

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = self.local.to_string();
        for elem in &self.projection {
            s = match elem {
                ProjectionElem::Deref => format!("(*{s})"),
                ProjectionElem::Field(i) => format!("{s}.{i}"),
                ProjectionElem::Downcast(v) => format!("({s} as {v})"),
            };
        }
        write!(f, "{s}")
    }
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operand::Copy(p) => write!(f, "copy {p}"),
            Operand::Move(p) => write!(f, "move {p}"),
            Operand::Const(c) => write!(f, "const {c}"),
        }
    }
}

// ANCHOR: display_body
impl fmt::Display for Body {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let args: Vec<String> = (1..=self.arg_count)
            .map(|i| format!("_{i}: {}", self.fmt_ty(&self.locals[i].ty)))
            .collect();
        let ret = self.fmt_ty(&self.locals[0].ty);
        writeln!(f, "fn {}({}) -> {ret} {{", self.name, args.join(", "))?;
        for (i, decl) in self.locals.iter().enumerate() {
            if let Some(name) = decl.name {
                writeln!(f, "    debug {name} => _{i};")?;
            }
        }
        for (i, decl) in self.locals.iter().enumerate() {
            // The arguments are declared in the signature line.
            if i == 0 || i > self.arg_count {
                writeln!(f, "    let _{i}: {};", self.fmt_ty(&decl.ty))?;
            }
        }
        for (i, block) in self.blocks.iter().enumerate() {
            writeln!(f)?;
            writeln!(f, "    bb{i}: {{")?;
            for stmt in &block.statements {
                writeln!(f, "        {}", self.fmt_statement(stmt))?;
            }
            writeln!(f, "        {}", self.fmt_terminator(&block.terminator))?;
            writeln!(f, "    }}")?;
        }
        write!(f, "}}")
    }
}
// ANCHOR_END: display_body
