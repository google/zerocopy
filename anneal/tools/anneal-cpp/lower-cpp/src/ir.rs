// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Rust mirror of `Trusted.CppAst` (one variant per Lean constructor, with
//! identical field order) and its deterministic Lean rendering.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Write as _,
};

use anneal_lower_common::{chunk, scc};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Width {
    W8,
    W16,
    W32,
    W64,
    W128,
}

impl Width {
    pub fn from_bits(bits: u64) -> Option<Width> {
        Some(match bits {
            8 => Width::W8,
            16 => Width::W16,
            32 => Width::W32,
            64 => Width::W64,
            128 => Width::W128,
            _ => return None,
        })
    }

    pub fn bits(self) -> u32 {
        match self {
            Width::W8 => 8,
            Width::W16 => 16,
            Width::W32 => 32,
            Width::W64 => 64,
            Width::W128 => 128,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sign {
    Signed,
    Unsigned,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SignedOverflowMode {
    IsoUB,
    Wrapv,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LangPolicy {
    pub pointer_width_bits: u64,
    pub char_is_signed: bool,
    pub strict_aliasing: bool,
    pub signed_overflow: SignedOverflowMode,
    pub exceptions_off: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    Void,
    Bool,
    Int(Width, Sign, bool),
    Ptr(Box<Ty>, bool, bool, bool),
    Array(Box<Ty>, u64),
    Record(String),
}

impl Ty {
    pub const I32: Ty = Ty::Int(Width::W32, Sign::Signed, false);
    pub const U32: Ty = Ty::Int(Width::W32, Sign::Unsigned, false);
    pub const I64: Ty = Ty::Int(Width::W64, Sign::Signed, false);

    pub fn int_parts(&self) -> Option<(Width, Sign, bool)> {
        match self {
            Ty::Int(w, s, c) => Some((*w, *s, *c)),
            _ => None,
        }
    }

    pub fn pointee(&self) -> Option<&Ty> {
        match self {
            Ty::Ptr(p, ..) => Some(p),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldDecl {
    pub name: String,
    pub offset_bits: u64,
    pub bit_width: Option<u64>,
    pub ty: Ty,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordDef {
    pub record_id: String,
    pub is_union: bool,
    pub size_bytes: u64,
    pub align_bytes: u64,
    pub fields: Vec<FieldDecl>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Proj {
    Deref,
    Field(String, u32, Ty),
    Index(Ty, usize),
    /// Bit-field `(record, field index, offset bits, width, signed)`; last
    /// projection only.
    Bitfield(String, u32, u64, u64, bool),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Place {
    pub base: usize,
    pub projs: Vec<Proj>,
}

impl Place {
    pub fn local(base: usize) -> Place {
        Place { base, projs: vec![] }
    }

    pub fn with(mut self, p: Proj) -> Place {
        self.projs.push(p);
        self
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    BitNot,
    LogNot,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Shl,
    Shr,
    BitAnd,
    BitOr,
    BitXor,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    ConstInt(Width, Sign, bool, i128),
    ConstBool(bool),
    NullPtr(Ty),
    ReadPlace(Place, Ty),
    AddrOf(Place, Ty),
    Unary(UnOp, Ty, Box<Expr>),
    Binary(BinOp, Ty, Box<Expr>, Box<Expr>),
    IntCast(Width, Sign, Width, Sign, bool, Box<Expr>),
    IntToBool(Box<Expr>),
    BoolToInt(Width, Sign, Box<Expr>),
    PtrAdd(Ty, Ty, Box<Expr>, Box<Expr>),
    PtrCast(Ty, Box<Expr>),
    /// `__builtin_bit_cast` from the first type to the second.
    BitCast(Ty, Ty, Box<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    StorageLive(usize),
    StorageDead(usize),
    Assign(Place, Ty, Expr),
    /// C++ zero-initialization of a place.
    ZeroInit(Place, Ty),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Terminator {
    Goto(usize),
    Branch(Expr, usize, usize),
    Call(String, Vec<Expr>, Option<(Place, Ty)>, usize),
    Ret,
    Unreachable,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub term: Terminator,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalDecl {
    pub ty: Ty,
    pub is_param: bool,
    /// Source-level name, for comments only (not part of `Trusted.CppAst`).
    pub debug_name: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Signature {
    pub params: Vec<Ty>,
    pub ret: Ty,
    /// Itanium C++ ABI (C++ functions without `extern "C"`).
    pub abi_cxx: bool,
    /// Per parameter: a C++ reference or `this` (non-null pointer).
    pub param_non_null: Vec<bool>,
}

impl Signature {
    pub fn c(params: Vec<Ty>, ret: Ty) -> Signature {
        Signature { params, ret, abi_cxx: false, param_non_null: Vec::new() }
    }

    fn lean(&self) -> String {
        let abi = if self.abi_cxx { "CppAbiKind.cxxItanium" } else { "CppAbiKind.c" };
        let params = lean_list(self.params.iter().map(Ty::lean).collect());
        if self.param_non_null.iter().any(|b| *b) {
            format!(
                "{{ abi := {abi}, params := {params}, ret := {}, paramNonNull := {} }}",
                self.ret.lean(),
                lean_list(self.param_non_null.iter().map(|b| lean_bool(*b).to_owned()).collect())
            )
        } else {
            format!("{{ abi := {abi}, params := {params}, ret := {} }}", self.ret.lean())
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Body {
    pub identity: String,
    pub is_external: bool,
    pub sig: Signature,
    pub locals: Vec<LocalDecl>,
    pub blocks: Vec<Block>,
    pub entry_block: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub policy: LangPolicy,
    pub is_partial: bool,
    pub records: Vec<RecordDef>,
    pub bodies: Vec<Body>,
    pub entry_def_id: usize,
}

// -------------------------------------------------------------------------
// Lean rendering
// -------------------------------------------------------------------------

fn lean_str(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            ' '..='~' => out.push(c),
            c if (c as u32) < 0x80 => {
                let _ = write!(out, "\\x{:02x}", c as u32);
            }
            // Every other Basic Multilingual Plane character, including all
            // bidirectional and other format controls, is escaped so the
            // emitted source reads the same in every viewer. Lean has no
            // escape for supplementary-plane characters; none of them is a
            // bidirectional control, and inside a string literal they cannot
            // end the literal.
            c if (c as u32) <= 0xffff => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Text from the bundle made safe to place inside a Lean comment: anything
/// but printable ASCII becomes `?` (so no newline ends a line comment and no
/// format character hides text), and `-/` and `/-` are split so a block
/// comment can neither close nor nest.
pub(crate) fn comment_text(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        let c = if matches!(c, ' '..='~') { c } else { '?' };
        if matches!((out.chars().last(), c), (Some('-'), '/') | (Some('/'), '-')) {
            out.push(' ');
        }
        out.push(c);
    }
    out
}

fn lean_bool(b: bool) -> &'static str {
    if b {
        "true"
    } else {
        "false"
    }
}

/// `Int` literals are spelled with constructors so the file needs no `Neg` /
/// `OfNat Int` instances beyond the prelude.
fn lean_int(v: i128) -> String {
    if v >= 0 {
        format!("(Int.ofNat {v})")
    } else {
        format!("(Int.negSucc {})", (-(v + 1)) as u128)
    }
}

fn lean_list(items: Vec<String>) -> String {
    if items.is_empty() {
        "[]".to_owned()
    } else {
        format!("[{}]", items.join(", "))
    }
}

impl Width {
    fn lean(self) -> &'static str {
        match self {
            Width::W8 => "CppIntWidth.w8",
            Width::W16 => "CppIntWidth.w16",
            Width::W32 => "CppIntWidth.w32",
            Width::W64 => "CppIntWidth.w64",
            Width::W128 => "CppIntWidth.w128",
        }
    }
}

impl Sign {
    fn lean(self) -> &'static str {
        match self {
            Sign::Signed => "Signedness.signed",
            Sign::Unsigned => "Signedness.unsigned",
        }
    }
}

impl Ty {
    pub fn lean(&self) -> String {
        match self {
            Ty::Void => "CppTy.void".to_owned(),
            Ty::Bool => "CppTy.bool".to_owned(),
            Ty::Int(w, s, c) => format!("(CppTy.int {} {} {})", w.lean(), s.lean(), lean_bool(*c)),
            Ty::Ptr(p, c, r, a) => format!(
                "(CppTy.ptr {} {} {} {})",
                p.lean(),
                lean_bool(*c),
                lean_bool(*r),
                lean_bool(*a)
            ),
            Ty::Array(e, n) => format!("(CppTy.array {} {n})", e.lean()),
            Ty::Record(id) => format!("(CppTy.record {})", lean_str(id)),
        }
    }
}

impl Proj {
    fn lean(&self) -> String {
        match self {
            Proj::Deref => "CppProjElem.deref".to_owned(),
            Proj::Field(r, i, t) => format!("(CppProjElem.field {} {i} {})", lean_str(r), t.lean()),
            Proj::Index(t, l) => format!("(CppProjElem.index {} {l})", t.lean()),
            Proj::Bitfield(r, i, o, w, s) => {
                format!("(CppProjElem.bitfield {} {i} {o} {w} {})", lean_str(r), lean_bool(*s))
            }
        }
    }
}

impl Place {
    fn lean(&self) -> String {
        format!(
            "{{ base := {}, projs := {} }}",
            self.base,
            lean_list(self.projs.iter().map(Proj::lean).collect())
        )
    }
}

impl UnOp {
    fn lean(self) -> &'static str {
        match self {
            UnOp::Neg => "CppUnOp.neg",
            UnOp::BitNot => "CppUnOp.bitNot",
            UnOp::LogNot => "CppUnOp.logNot",
        }
    }
}

impl BinOp {
    fn lean(self) -> &'static str {
        match self {
            BinOp::Add => "CppBinOp.add",
            BinOp::Sub => "CppBinOp.sub",
            BinOp::Mul => "CppBinOp.mul",
            BinOp::Div => "CppBinOp.div",
            BinOp::Rem => "CppBinOp.rem",
            BinOp::Shl => "CppBinOp.shl",
            BinOp::Shr => "CppBinOp.shr",
            BinOp::BitAnd => "CppBinOp.bitAnd",
            BinOp::BitOr => "CppBinOp.bitOr",
            BinOp::BitXor => "CppBinOp.bitXor",
            BinOp::Eq => "CppBinOp.eq",
            BinOp::Ne => "CppBinOp.ne",
            BinOp::Lt => "CppBinOp.lt",
            BinOp::Le => "CppBinOp.le",
            BinOp::Gt => "CppBinOp.gt",
            BinOp::Ge => "CppBinOp.ge",
        }
    }
}

impl Expr {
    pub fn lean(&self) -> String {
        match self {
            Expr::ConstInt(w, s, c, v) => format!(
                "(CppExpr.constInt {} {} {} {})",
                w.lean(),
                s.lean(),
                lean_bool(*c),
                lean_int(*v)
            ),
            Expr::ConstBool(b) => format!("(CppExpr.constBool {})", lean_bool(*b)),
            Expr::NullPtr(t) => format!("(CppExpr.nullPtr {})", t.lean()),
            Expr::ReadPlace(p, t) => format!("(CppExpr.readPlace {} {})", p.lean(), t.lean()),
            Expr::AddrOf(p, t) => format!("(CppExpr.addrOf {} {})", p.lean(), t.lean()),
            Expr::Unary(op, t, a) => {
                format!("(CppExpr.unary {} {} {})", op.lean(), t.lean(), a.lean())
            }
            Expr::Binary(op, t, l, r) => {
                format!("(CppExpr.binary {} {} {} {})", op.lean(), t.lean(), l.lean(), r.lean())
            }
            Expr::IntCast(fw, fs, tw, ts, tc, a) => format!(
                "(CppExpr.intCast {} {} {} {} {} {})",
                fw.lean(),
                fs.lean(),
                tw.lean(),
                ts.lean(),
                lean_bool(*tc),
                a.lean()
            ),
            Expr::IntToBool(a) => format!("(CppExpr.intToBool {})", a.lean()),
            Expr::BoolToInt(w, s, a) => {
                format!("(CppExpr.boolToInt {} {} {})", w.lean(), s.lean(), a.lean())
            }
            Expr::PtrAdd(e, p, b, o) => {
                format!("(CppExpr.ptrAdd {} {} {} {})", e.lean(), p.lean(), b.lean(), o.lean())
            }
            Expr::PtrCast(t, a) => format!("(CppExpr.ptrCast {} {})", t.lean(), a.lean()),
            Expr::BitCast(f, t, a) => {
                format!("(CppExpr.bitCast {} {} {})", f.lean(), t.lean(), a.lean())
            }
        }
    }
}

impl Stmt {
    fn lean(&self) -> String {
        match self {
            Stmt::StorageLive(l) => format!("CppStmt.storageLive {l}"),
            Stmt::StorageDead(l) => format!("CppStmt.storageDead {l}"),
            Stmt::Assign(p, t, e) => {
                format!("CppStmt.assign {} {} {}", p.lean(), t.lean(), e.lean())
            }
            Stmt::ZeroInit(p, t) => format!("CppStmt.zeroInit {} {}", p.lean(), t.lean()),
        }
    }
}

impl Terminator {
    fn lean(&self) -> String {
        match self {
            Terminator::Goto(b) => format!("CppTerminator.goto {b}"),
            Terminator::Branch(c, t, f) => format!("CppTerminator.branch {} {t} {f}", c.lean()),
            Terminator::Call(callee, args, dst, next) => format!(
                "CppTerminator.call {} {} {} {next}",
                lean_str(callee),
                lean_list(args.iter().map(Expr::lean).collect()),
                match dst {
                    None => "none".to_owned(),
                    Some((p, t)) => format!("(some ({}, {}))", p.lean(), t.lean()),
                }
            ),
            Terminator::Ret => "CppTerminator.ret".to_owned(),
            Terminator::Unreachable => "CppTerminator.unreachable".to_owned(),
        }
    }
}

fn lean_ident_suffix(s: &str) -> String {
    s.chars().map(|c| if c.is_ascii_alphanumeric() { c } else { '_' }).collect()
}

impl LocalDecl {
    fn lean(&self) -> String {
        format!("{{ ty := {}, isParam := {} }}", self.ty.lean(), lean_bool(self.is_param))
    }
}

impl Block {
    /// Renders the block; statement lists longer than
    /// `chunk::INLINE_LIMIT` are hoisted into `{prefix}_stmts_*` definitions
    /// appended to `defs`.
    fn lean_compact(&self, prefix: &str, defs: &mut Vec<String>) -> String {
        let stmts: Vec<String> = self.stmts.iter().map(Stmt::lean).collect();
        let stmts = if stmts.len() > chunk::INLINE_LIMIT {
            let h = chunk::hoist_list(&format!("{prefix}_stmts"), "CppStmt", &stmts);
            defs.extend(h.defs);
            h.expr
        } else {
            lean_list(stmts)
        };
        format!("{{ stmts := {stmts}, term := {} }}", self.term.lean())
    }
}

impl Body {
    fn is_large(&self) -> bool {
        self.locals.len() > chunk::INLINE_LIMIT
            || self.blocks.len() > chunk::INLINE_LIMIT
            || self.blocks.iter().any(|b| b.stmts.len() > chunk::INLINE_LIMIT)
    }

    /// Renders `def {name} : CppBody`, preceded by hoisted chunk definitions
    /// when any list exceeds `chunk::INLINE_LIMIT`.
    fn lean_def(&self, name: &str) -> String {
        let mut out = String::new();
        let mut defs = Vec::new();
        let (locals, blocks) = if self.is_large() {
            let locals: Vec<String> = self.locals.iter().map(LocalDecl::lean).collect();
            let locals = if locals.len() > chunk::INLINE_LIMIT {
                let h = chunk::hoist_list(&format!("{name}_locals"), "CppLocalDecl", &locals);
                defs.extend(h.defs);
                h.expr
            } else {
                lean_list(locals)
            };
            let blocks: Vec<String> = self
                .blocks
                .iter()
                .enumerate()
                .map(|(j, b)| b.lean_compact(&format!("{name}_bb{j}"), &mut defs))
                .collect();
            let blocks = if blocks.len() > chunk::INLINE_LIMIT {
                let h = chunk::hoist_list(&format!("{name}_blocks"), "CppBlock", &blocks);
                defs.extend(h.defs);
                h.expr
            } else {
                lean_list(blocks)
            };
            (format!("  locals := {locals}\n"), format!("  blocks := {blocks}\n"))
        } else {
            (self.lean_inline_locals(), self.lean_inline_blocks())
        };
        for d in defs {
            out.push_str(&d);
            out.push('\n');
        }
        let _ = writeln!(out, "/-- `{}` -/", comment_text(&self.identity));
        let _ = writeln!(out, "def {name} : CppBody := {{");
        let _ = writeln!(out, "  identity := {}", lean_str(&self.identity));
        let _ = writeln!(out, "  isExternal := {}", lean_bool(self.is_external));
        let _ = writeln!(out, "  sig := {}", self.sig.lean());
        out.push_str(&locals);
        out.push_str(&blocks);
        let _ = writeln!(out, "  entryBlock := {}", self.entry_block);
        out.push_str("}\n\n");
        out
    }

    fn lean_inline_locals(&self) -> String {
        let mut out = String::from("  locals := [");
        for (j, l) in self.locals.iter().enumerate() {
            out.push_str(if j == 0 { "\n" } else { ",\n" });
            let _ = write!(out, "    -- _{j}: {}\n    {}", comment_text(&l.debug_name), l.lean());
        }
        out.push_str(if self.locals.is_empty() { "]\n" } else { "\n  ]\n" });
        out
    }

    fn lean_inline_blocks(&self) -> String {
        let mut out = String::from("  blocks := [");
        for (j, blk) in self.blocks.iter().enumerate() {
            out.push_str(if j == 0 { "\n" } else { ",\n" });
            let _ = writeln!(out, "    -- bb{j}");
            out.push_str("    { stmts := [");
            for (k, s) in blk.stmts.iter().enumerate() {
                out.push_str(if k == 0 { "\n" } else { ",\n" });
                let _ = write!(out, "        {}", s.lean());
            }
            out.push_str("]\n");
            let _ = write!(out, "      term := {} }}", blk.term.lean());
        }
        out.push_str(if self.blocks.is_empty() { "]\n" } else { "\n  ]\n" });
        out
    }
}

impl Program {
    /// Body indices in callee-first SCC order over direct calls. Falls back
    /// to capture order if identities are not unique.
    fn body_emission_order(&self) -> Vec<usize> {
        let identities: Vec<String> = self.bodies.iter().map(|b| b.identity.clone()).collect();
        let mut edges: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for b in &self.bodies {
            for blk in &b.blocks {
                if let Terminator::Call(callee, ..) = &blk.term {
                    edges.entry(b.identity.clone()).or_default().insert(callee.clone());
                }
            }
        }
        let Ok(sccs) = scc::callee_first_sccs(&identities, &edges) else {
            return (0..self.bodies.len()).collect();
        };
        let position: BTreeMap<&str, usize> =
            identities.iter().enumerate().map(|(i, s)| (s.as_str(), i)).collect();
        sccs.iter().flat_map(|c| c.members.iter().map(|m| position[m.as_str()])).collect()
    }
}

/// Header metadata recorded as comments in the generated file.
pub struct EmitMeta<'a> {
    pub namespace: &'a str,
    pub tu_main_file: &'a str,
    pub target_triple: &'a str,
    pub lang_standard: &'a str,
}

impl Program {
    pub fn lean(&self, meta: &EmitMeta<'_>) -> String {
        let mut out = String::new();
        let _ = writeln!(out, "-- Generated by anneal-lower-cpp from a RawCppBundle (schema v1).");
        let _ =
            writeln!(out, "-- DO NOT EDIT: regenerate with anneal-clang-dump | anneal-lower-cpp.");
        let _ = writeln!(out, "-- tu_main_file: {}", comment_text(meta.tu_main_file));
        let _ = writeln!(out, "-- target_triple: {}", comment_text(meta.target_triple));
        let _ = writeln!(out, "-- lang_standard: {}", comment_text(meta.lang_standard));
        // `prelude` plus explicit `Init` imports avoids an implicit `Init`
        // import; `Trusted.CppAst` is defined by the companion C/C++
        // semantics stack.
        out.push_str(
            "module\nprelude\npublic import Init.NotationExtra\npublic import Trusted.CppAst\n\n\
             @[expose] public section\n\n",
        );
        let _ = writeln!(out, "namespace {}", meta.namespace);
        out.push_str("open Trusted.CppAst\n\n");

        let p = &self.policy;
        out.push_str("def policy : CppLangPolicy := {\n");
        let _ = writeln!(out, "  pointerWidthBits := {}", p.pointer_width_bits);
        let _ = writeln!(out, "  charIsSigned := {}", lean_bool(p.char_is_signed));
        let _ = writeln!(out, "  strictAliasing := {}", lean_bool(p.strict_aliasing));
        let _ = writeln!(
            out,
            "  signedOverflow := {}",
            match p.signed_overflow {
                SignedOverflowMode::IsoUB => "SignedOverflowMode.isoUB",
                SignedOverflowMode::Wrapv => "SignedOverflowMode.wrapv",
            }
        );
        let _ = writeln!(out, "  exceptionsOff := {}", lean_bool(p.exceptions_off));
        out.push_str("}\n\n");

        out.push_str("def records : List CppRecordDef := [");
        for (i, r) in self.records.iter().enumerate() {
            out.push_str(if i == 0 { "\n" } else { ",\n" });
            let _ = writeln!(out, "  {{ recordId := {}", lean_str(&r.record_id));
            let _ = writeln!(out, "    isUnion := {}", lean_bool(r.is_union));
            let _ = writeln!(out, "    sizeBytes := {}", r.size_bytes);
            let _ = writeln!(out, "    alignBytes := {}", r.align_bytes);
            out.push_str("    fields := [");
            for (j, f) in r.fields.iter().enumerate() {
                out.push_str(if j == 0 { "\n" } else { ",\n" });
                let _ = write!(
                    out,
                    "      {{ name := {}, offsetBits := {}, bitWidth := {}, ty := {} }}",
                    lean_str(&f.name),
                    f.offset_bits,
                    match f.bit_width {
                        None => "none".to_owned(),
                        Some(w) => format!("(some {w})"),
                    },
                    f.ty.lean()
                );
            }
            out.push_str("] }");
        }
        out.push_str(if self.records.is_empty() { "]\n\n" } else { "\n]\n\n" });

        // Body definitions are emitted callee-first by SCC (deterministic and
        // independent of capture order); `program.bodies` keeps the captured
        // order, which fixes every `defId`.
        let body_names: Vec<String> = self
            .bodies
            .iter()
            .enumerate()
            .map(|(i, b)| format!("body_{}_{}", i, lean_ident_suffix(&b.identity)))
            .collect();
        for i in self.body_emission_order() {
            out.push_str(&self.bodies[i].lean_def(&body_names[i]));
        }

        out.push_str("def program : CppProgram := {\n");
        out.push_str("  policy := policy\n");
        let _ = writeln!(out, "  isPartial := {}", lean_bool(self.is_partial));
        out.push_str("  records := records\n");
        let _ = writeln!(out, "  bodies := {}", lean_list(body_names));
        let _ = writeln!(out, "  entryDefId := {}", self.entry_def_id);
        out.push_str("}\n\n");
        let _ = writeln!(out, "end {}", meta.namespace);
        out.push_str("\nend\n");
        out
    }
}
