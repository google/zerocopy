// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pure memory-safe Rust NDJSON comparator (Action `5c`, `AnnealVerifyNdjson`).
//!
//! # Why This Module Exists
//!
//! Lean 4's binary `.olean` loader (`CompactedRegion.read`) maps raw pointer
//! graphs directly into the reader's address space, and upstream Lean documents
//! in `Lake/CLI/Check.lean` that adversarial code must be built and exported
//! inside an OS sandbox so that no untrusted `.olean` is ever mapped into the
//! verdict-producing process. Only plain UTF-8 NDJSON exported by `leanexport`
//! crosses the isolation boundary.
//!
//! This module implements the verdict side of Anneal's three-action split
//! (`5a` trusted expected export, `5b` sandboxed proof export, `5c` pure-Rust
//! comparator + dual independent kernels):
//!
//! 1. **Canonical hash-consed DAG identity (`5a` vs. `5b`):** Every constant in
//!    `expected_cone.ndjson` (exported with zero `Proof.*` or `Anneal.*`
//!    modules mounted) must appear structurally identically in
//!    `proof_full.ndjson`, normalizing away per-file integer table indices.
//! 2. **Full 39-primitive `Init` pinning:** Every constant in
//!    `init_primitives_cone.ndjson` (covering all 39 kernel-accelerated and
//!    elaborator-parameter primitives) that appears in `expected_cone.ndjson`
//!    or `proof_full.ndjson` must match the clean sysroot definition
//!    identically. This prevents an untrusted export from redefining an unused
//!    kernel primitive (such as `Nat.gcd` or `String.ofList`) that an external
//!    checker reduces natively.
//! 3. **Explicit `Quot.{mk,lift,ind}` post-check:** Verifies the four quotient
//!    primitive kinds and types against the pinned sysroot definitions and
//!    forbids any foreign `.quotInfo` declaration.
//! 4. **`.opaqueInfo` cone ban and unsafe/partial ban:** Lean's standard
//!    `CollectAxioms` traversal skips `.opaqueInfo` bodies; banning every
//!    `.opaqueInfo`, `unsafe`, and `partial` declaration in the export and
//!    transitive closure closes that blind spot structurally.
//! 5. **Closed positive axiom allowlist:** Only `Classical.choice`,
//!    `Quot.sound`, and `propext` are permitted (`sorryAx` is admitted strictly
//!    on proof-only declarations when `allow_sorry_in_proof` is explicitly set,
//!    and never inside `expected_cone`).
//! 6. **Dual independent kernels by default:** Invokes `nanoda_bin` (with
//!    `"unpermitted_axiom_hard_error": true`) and `con-ron` (`--verified`) over
//!    `proof_full.ndjson`, plus optional `--paranoid-quorum` running
//!    `con-leche` and `lean4lean --import` directly inside `ExecSeal`.
//! 7. **Strict verdict schema:** Serializes and validates verdicts through
//!    `#[serde(deny_unknown_fields)]` Rust structs rather than untyped JSON
//!    maps.

use std::{
    collections::{BTreeMap, BTreeSet, HashMap, VecDeque},
    fs,
    io::{BufRead, BufReader},
    path::Path,
};

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::toolchain::{Failure, sha256_bytes};

/// Supported Lean 4 NDJSON export format version emitted by `leanexport`.
pub const SUPPORTED_EXPORT_FORMAT_VERSION: &str = "3.1.0";

/// Maximum size in bytes accepted for a single NDJSON export stream (256 MiB).
pub const MAX_NDJSON_BYTES: u64 = 256 * 1024 * 1024;

/// Maximum number of lines accepted in a single NDJSON export stream.
///
/// Bounding total records prevents a hostile `5b` export from exhausting host
/// memory with millions of tiny unused table entries.
pub const MAX_NDJSON_LINES: usize = 20_000_000;

/// Closed 3-element set of standard Lean 4 axioms permitted in untainted
/// proofs.
pub const STANDARD_PERMITTED_AXIOMS: [&str; 3] = ["Classical.choice", "Quot.sound", "propext"];

/// Complete 39-element union of kernel-accelerated `Init` primitives trusted by
/// `nanoda_bin` (`nat_extension`, `string_extension`, `Quot`) and Lean's
/// `Lake/CLI/Check.lean` (`primitiveTargets` + `builtinTargets`).
///
/// Pinning every name in this list against a clean sysroot export ensures that
/// a sandboxed `5b` exporter cannot inject an altered definition for a
/// primitive (such as `Nat.gcd` or `eagerReduce`) that `Expected.claim` does
/// not directly reference.
pub const PINNED_INIT_PRIMITIVES: [&str; 39] = [
    "Nat",
    "Nat.zero",
    "Nat.succ",
    "Nat.add",
    "Nat.sub",
    "Nat.mul",
    "Nat.pow",
    "Nat.gcd",
    "Nat.div",
    "Nat.mod",
    "Nat.beq",
    "Nat.ble",
    "Nat.land",
    "Nat.lor",
    "Nat.xor",
    "Nat.shiftLeft",
    "Nat.shiftRight",
    "String",
    "String.mk",
    "String.ofList",
    "Char",
    "Char.ofNat",
    "List",
    "List.nil",
    "List.cons",
    "Bool",
    "Bool.true",
    "Bool.false",
    "Eq",
    "Eq.refl",
    "Quot",
    "Quot.mk",
    "Quot.lift",
    "Quot.ind",
    "eagerReduce",
    "optParam",
    "autoParam",
    "semiOutParam",
    "outParam",
];

/// Exact expected `(name, kind)` pairs for Lean's four quotient primitives.
const QUOT_PRIMITIVES: [(&str, QuotKind); 4] = [
    ("Quot", QuotKind::Type),
    ("Quot.mk", QuotKind::Ctor),
    ("Quot.lift", QuotKind::Lift),
    ("Quot.ind", QuotKind::Ind),
];

/// Canonical constructor name for the crate pair inside `Expected.claim`.
const CRATE_MK_NAME: &str = "Trusted.MirSemantics.Crate.mk";

// ---------------------------------------------------------------------------
// Canonical hash-consed arena (index-independent DAG identity)
// ---------------------------------------------------------------------------

/// Interned canonical identifier for a Lean `Name` in [`CanonicalArena`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CanonNameId(u32);

/// Interned canonical identifier for a Lean `Level` in [`CanonicalArena`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CanonLevelId(u32);

/// Interned canonical identifier for a Lean `Expr` in [`CanonicalArena`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CanonExprId(u32);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum CanonName {
    Anonymous,
    Str(CanonNameId, String),
    Num(CanonNameId, u64),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum CanonLevel {
    Zero,
    Succ(CanonLevelId),
    Max(CanonLevelId, CanonLevelId),
    IMax(CanonLevelId, CanonLevelId),
    Param(CanonNameId),
}

/// Lean binder visibility annotation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinderInfo {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

/// Canonical kernel `Expr` node interned in [`CanonicalArena`].
///
/// Matches Lean 4's kernel alpha-equivalence (`Expr.eqv` / `BEq Expr`):
/// `leanexport` deduplicates expressions in a `HashMap Expr Nat` keyed by
/// `Expr.eqv`, which intentionally ignores cosmetic binder names, `binderInfo`
/// annotations, `letE.nondep`, and `mdata` wrappers because de Bruijn indices
/// alone determine kernel binding and reduction. Consequently, two independent
/// exports of the same constant (`5-init` vs. `5a` vs. `5b`) may emit
/// different cosmetic binder names for the exact same kernel subterm depending
/// on export traversal order. All fields are still strictly validated during
/// NDJSON parsing before interning.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum CanonExpr {
    BVar(u64),
    Sort(CanonLevelId),
    Const(CanonNameId, Vec<CanonLevelId>),
    App(CanonExprId, CanonExprId),
    Lam {
        ty: CanonExprId,
        body: CanonExprId,
    },
    ForallE {
        ty: CanonExprId,
        body: CanonExprId,
    },
    LetE {
        ty: CanonExprId,
        value: CanonExprId,
        body: CanonExprId,
    },
    Proj {
        type_name: CanonNameId,
        idx: u64,
        struct_expr: CanonExprId,
    },
    /// Arbitrary-precision natural number literal stored as canonical decimal
    /// ASCII digits to avoid fixed-width integer overflow on wide `BitVec`
    /// constants.
    NatLit(String),
    StrLit(String),
}

/// Lean definition reducibility hints.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ReducibilityHints {
    Opaque,
    Abbrev,
    Regular(u32),
}

/// Lean definition safety classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DefinitionSafety {
    Safe,
    Unsafe,
    Partial,
}

/// Lean quotient primitive classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum QuotKind {
    Type,
    Ctor,
    Lift,
    Ind,
}

/// Single recursor reduction rule in a `RecVal`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RecursorRule {
    pub ctor: CanonNameId,
    pub nfields: u64,
    pub rhs: CanonExprId,
}

/// Canonicalized kernel `ConstantInfo` with all `Name`, `Level`, and `Expr`
/// references interned into a shared [`CanonicalArena`].
///
/// Because every subterm is interned into one shared arena across
/// `init_primitives_cone.ndjson`, `expected_cone.ndjson`, and
/// `proof_full.ndjson`, structural DAG equality across files reduces to `O(1)`
/// value equality with zero recursive traversal and zero stack-overflow risk.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CanonConstInfo {
    Axiom {
        name: CanonNameId,
        level_params: Vec<CanonNameId>,
        ty: CanonExprId,
        is_unsafe: bool,
    },
    Defn {
        name: CanonNameId,
        level_params: Vec<CanonNameId>,
        ty: CanonExprId,
        value: CanonExprId,
        hints: ReducibilityHints,
        safety: DefinitionSafety,
        all: Vec<CanonNameId>,
    },
    Thm {
        name: CanonNameId,
        level_params: Vec<CanonNameId>,
        ty: CanonExprId,
        value: CanonExprId,
        all: Vec<CanonNameId>,
    },
    Opaque {
        name: CanonNameId,
        level_params: Vec<CanonNameId>,
        ty: CanonExprId,
        value: CanonExprId,
        is_unsafe: bool,
        all: Vec<CanonNameId>,
    },
    Quot {
        name: CanonNameId,
        level_params: Vec<CanonNameId>,
        ty: CanonExprId,
        kind: QuotKind,
    },
    Induct {
        name: CanonNameId,
        level_params: Vec<CanonNameId>,
        ty: CanonExprId,
        num_params: u64,
        num_indices: u64,
        all: Vec<CanonNameId>,
        ctors: Vec<CanonNameId>,
        num_nested: u64,
        is_rec: bool,
        is_unsafe: bool,
        is_reflexive: bool,
    },
    Ctor {
        name: CanonNameId,
        level_params: Vec<CanonNameId>,
        ty: CanonExprId,
        induct: CanonNameId,
        cidx: u64,
        num_params: u64,
        num_fields: u64,
        is_unsafe: bool,
    },
    Rec {
        name: CanonNameId,
        level_params: Vec<CanonNameId>,
        ty: CanonExprId,
        all: Vec<CanonNameId>,
        num_params: u64,
        num_indices: u64,
        num_motives: u64,
        num_minors: u64,
        rules: Vec<RecursorRule>,
        k: bool,
        is_unsafe: bool,
    },
}

impl CanonConstInfo {
    fn kind_label(&self) -> &'static str {
        match self {
            Self::Axiom { .. } => "axiom",
            Self::Defn { .. } => "def",
            Self::Thm { .. } => "thm",
            Self::Opaque { .. } => "opaque",
            Self::Quot { .. } => "quot",
            Self::Induct { .. } => "inductive",
            Self::Ctor { .. } => "ctor",
            Self::Rec { .. } => "rec",
        }
    }

    fn is_unsafe_or_partial(&self) -> bool {
        match self {
            Self::Axiom { is_unsafe, .. }
            | Self::Opaque { is_unsafe, .. }
            | Self::Induct { is_unsafe, .. }
            | Self::Ctor { is_unsafe, .. }
            | Self::Rec { is_unsafe, .. } => *is_unsafe,
            Self::Defn { safety, .. } => *safety != DefinitionSafety::Safe,
            Self::Thm { .. } | Self::Quot { .. } => false,
        }
    }
}

/// Shared hash-consing arena normalizing per-file NDJSON table indices into
/// canonical identities.
#[derive(Debug)]
pub struct CanonicalArena {
    names: Vec<CanonName>,
    name_ids: HashMap<CanonName, CanonNameId>,
    name_strings: Vec<String>,
    string_to_name: HashMap<String, CanonNameId>,
    levels: Vec<CanonLevel>,
    level_ids: HashMap<CanonLevel, CanonLevelId>,
    exprs: Vec<CanonExpr>,
    expr_ids: HashMap<CanonExpr, CanonExprId>,
    anonymous_name: CanonNameId,
    zero_level: CanonLevelId,
    nat_name: CanonNameId,
    string_name: CanonNameId,
    opt_param_name: CanonNameId,
}

impl CanonicalArena {
    /// Construct an arena pre-seeded with `Name.anonymous`, `Level.zero`,
    /// `Nat`, `String`, and `optParam`.
    pub fn new() -> Self {
        let mut arena = Self {
            names: Vec::with_capacity(4096),
            name_ids: HashMap::with_capacity(4096),
            name_strings: Vec::with_capacity(4096),
            string_to_name: HashMap::with_capacity(4096),
            levels: Vec::with_capacity(256),
            level_ids: HashMap::with_capacity(256),
            exprs: Vec::with_capacity(16384),
            expr_ids: HashMap::with_capacity(16384),
            anonymous_name: CanonNameId(0),
            zero_level: CanonLevelId(0),
            nat_name: CanonNameId(0),
            string_name: CanonNameId(0),
            opt_param_name: CanonNameId(0),
        };
        arena.anonymous_name = arena.intern_name(CanonName::Anonymous);
        arena.zero_level = arena.intern_level(CanonLevel::Zero);
        arena.nat_name = arena.intern_dotted_name("Nat");
        arena.string_name = arena.intern_dotted_name("String");
        arena.opt_param_name = arena.intern_dotted_name("optParam");
        arena
    }

    fn intern_name(&mut self, name: CanonName) -> CanonNameId {
        if let Some(&id) = self.name_ids.get(&name) {
            return id;
        }
        let rendered = match &name {
            CanonName::Anonymous => String::new(),
            CanonName::Str(pre, s) => {
                let prefix = &self.name_strings[pre.0 as usize];
                if prefix.is_empty() { s.clone() } else { format!("{prefix}.{s}") }
            }
            CanonName::Num(pre, n) => {
                let prefix = &self.name_strings[pre.0 as usize];
                if prefix.is_empty() { n.to_string() } else { format!("{prefix}.{n}") }
            }
        };
        let id = CanonNameId(self.names.len() as u32);
        self.names.push(name.clone());
        self.name_ids.insert(name, id);
        self.string_to_name.insert(rendered.clone(), id);
        self.name_strings.push(rendered);
        id
    }

    /// Intern a dotted ASCII Lean name such as `"Expected.claim"`.
    pub fn intern_dotted_name(&mut self, dotted: &str) -> CanonNameId {
        if let Some(&id) = self.string_to_name.get(dotted) {
            return id;
        }
        let mut cur = self.anonymous_name;
        for seg in dotted.split('.') {
            cur = self.intern_name(CanonName::Str(cur, seg.to_owned()));
        }
        cur
    }

    /// Render a canonical name ID back to its dotted Lean spelling.
    pub fn name_str(&self, id: CanonNameId) -> &str {
        &self.name_strings[id.0 as usize]
    }

    /// Strip Lean's `_private.<module>.<idx>` prefix and any `_root_` prefix,
    /// mirroring `TrustedBoundary.privateToUserName`.
    fn strip_private_and_root(&self, id: CanonNameId) -> &str {
        let mut parts: Vec<(bool, &str)> = Vec::new();
        let mut cur = id;
        loop {
            match &self.names[cur.0 as usize] {
                CanonName::Anonymous => break,
                CanonName::Str(pre, s) => {
                    parts.push((false, s.as_str()));
                    cur = *pre;
                }
                CanonName::Num(pre, _) => {
                    parts.push((true, ""));
                    cur = *pre;
                }
            }
        }
        parts.reverse();
        let full = self.name_str(id);
        let after_private = if parts.first() == Some(&(false, "_private"))
            && let Some(num_pos) = parts.iter().position(|(is_num, _)| *is_num)
        {
            let mut rest = full;
            let mut offset = 0usize;
            for (i, seg) in full.split('.').enumerate() {
                if i > 0 {
                    offset += 1;
                }
                offset += seg.len();
                if i == num_pos {
                    rest = full.get(offset + 1..).unwrap_or("");
                    break;
                }
            }
            rest
        } else {
            full
        };
        after_private.strip_prefix("_root_.").unwrap_or(after_private)
    }

    /// Return `true` if constant `id` belongs to `module` (either as
    /// `<module>.*` / `<module>` or `_private.<module>.<idx>.*`).
    fn belongs_to_module(&self, id: CanonNameId, module: &str) -> bool {
        let full = self.name_str(id);
        if full == module
            || (full.starts_with(module) && full.as_bytes().get(module.len()) == Some(&b'.'))
        {
            return true;
        }
        if let Some(rest) = full.strip_prefix("_private.")
            && let Some(after_mod) = rest.strip_prefix(module)
            && let Some(after_dot) = after_mod.strip_prefix('.')
            && let Some((digits, _tail)) = after_dot.split_once('.')
        {
            return !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit());
        }
        false
    }

    /// Return the root component of a canonical name (for example `"Nat"` for
    /// `"Nat.add"`, or `""` for `Name.anonymous`).
    pub fn name_root(&self, id: CanonNameId) -> &str {
        let mut cur = id;
        loop {
            match &self.names[cur.0 as usize] {
                CanonName::Anonymous => return "",
                CanonName::Str(pre, s) if *pre == self.anonymous_name => return s.as_str(),
                CanonName::Str(pre, _) | CanonName::Num(pre, _) => cur = *pre,
            }
        }
    }

    fn intern_level(&mut self, level: CanonLevel) -> CanonLevelId {
        if let Some(&id) = self.level_ids.get(&level) {
            return id;
        }
        let id = CanonLevelId(self.levels.len() as u32);
        self.levels.push(level.clone());
        self.level_ids.insert(level, id);
        id
    }

    fn intern_expr(&mut self, expr: CanonExpr) -> CanonExprId {
        if let Some(&id) = self.expr_ids.get(&expr) {
            return id;
        }
        let id = CanonExprId(self.exprs.len() as u32);
        self.exprs.push(expr.clone());
        self.expr_ids.insert(expr, id);
        id
    }

    /// Collect all constant names referenced by `root_expr` using an iterative
    /// worklist.
    ///
    /// When `strip_opt_params` is `true`, applications of `optParam α d` skip
    /// the elaboration-only default term `d` and traverse only `α` (matching
    /// `ProofLib/TrustedClosure.lean`), preventing elaboration defaults from
    /// polluting statement-origin checks.
    fn collect_expr_consts(
        &self,
        root_expr: CanonExprId,
        strip_opt_params: bool,
        out: &mut BTreeSet<CanonNameId>,
    ) {
        let mut stack = vec![root_expr];
        let mut seen = BTreeSet::new();
        while let Some(eid) = stack.pop() {
            if !seen.insert(eid) {
                continue;
            }
            if strip_opt_params
                && let CanonExpr::App(fn_id, _default_arg) = &self.exprs[eid.0 as usize]
                && let CanonExpr::App(opt_const, ty_arg) = &self.exprs[fn_id.0 as usize]
                && let CanonExpr::Const(name, _) = &self.exprs[opt_const.0 as usize]
                && *name == self.opt_param_name
            {
                stack.push(*ty_arg);
                continue;
            }
            match &self.exprs[eid.0 as usize] {
                CanonExpr::BVar(_) | CanonExpr::Sort(_) => {}
                CanonExpr::Const(name, _) => {
                    out.insert(*name);
                }
                CanonExpr::App(f, a) => {
                    stack.push(*f);
                    stack.push(*a);
                }
                CanonExpr::Lam { ty, body, .. } | CanonExpr::ForallE { ty, body, .. } => {
                    stack.push(*ty);
                    stack.push(*body);
                }
                CanonExpr::LetE { ty, value, body, .. } => {
                    stack.push(*ty);
                    stack.push(*value);
                    stack.push(*body);
                }
                CanonExpr::Proj { type_name, struct_expr, .. } => {
                    out.insert(*type_name);
                    stack.push(*struct_expr);
                }
                CanonExpr::NatLit(_) => {
                    out.insert(self.nat_name);
                }
                CanonExpr::StrLit(_) => {
                    out.insert(self.string_name);
                }
            }
        }
    }

    /// Collect every constant referenced by a declaration's type, value,
    /// mutual-block peers, and inductive/recursor metadata.
    fn collect_const_deps(
        &self,
        info: &CanonConstInfo,
        strip_opt_params: bool,
    ) -> BTreeSet<CanonNameId> {
        let mut deps = BTreeSet::new();
        match info {
            CanonConstInfo::Axiom { ty, .. } | CanonConstInfo::Quot { ty, .. } => {
                self.collect_expr_consts(*ty, strip_opt_params, &mut deps);
            }
            CanonConstInfo::Defn { ty, value, all, .. }
            | CanonConstInfo::Thm { ty, value, all, .. }
            | CanonConstInfo::Opaque { ty, value, all, .. } => {
                self.collect_expr_consts(*ty, strip_opt_params, &mut deps);
                self.collect_expr_consts(*value, strip_opt_params, &mut deps);
                deps.extend(all.iter().copied());
            }
            CanonConstInfo::Induct { ty, all, ctors, .. } => {
                self.collect_expr_consts(*ty, strip_opt_params, &mut deps);
                deps.extend(all.iter().copied());
                deps.extend(ctors.iter().copied());
            }
            CanonConstInfo::Ctor { ty, induct, .. } => {
                self.collect_expr_consts(*ty, strip_opt_params, &mut deps);
                deps.insert(*induct);
            }
            CanonConstInfo::Rec { ty, all, rules, .. } => {
                self.collect_expr_consts(*ty, strip_opt_params, &mut deps);
                deps.extend(all.iter().copied());
                for rule in rules {
                    deps.insert(rule.ctor);
                    self.collect_expr_consts(rule.rhs, strip_opt_params, &mut deps);
                }
            }
        }
        deps
    }

    /// Build the canonical `Expected.claim` application expression:
    /// `canonical_root (Trusted.MirSemantics.Crate.mk subject specification)`.
    fn build_canonical_claim_expr(
        &mut self,
        canonical_root: &str,
        subject: &str,
        specification: &str,
    ) -> CanonExprId {
        let root_id = self.intern_dotted_name(canonical_root);
        let crate_mk_id = self.intern_dotted_name(CRATE_MK_NAME);
        let subject_id = self.intern_dotted_name(subject);
        let spec_id = self.intern_dotted_name(specification);

        let root_expr = self.intern_expr(CanonExpr::Const(root_id, Vec::new()));
        let crate_mk_expr = self.intern_expr(CanonExpr::Const(crate_mk_id, Vec::new()));
        let subject_expr = self.intern_expr(CanonExpr::Const(subject_id, Vec::new()));
        let spec_expr = self.intern_expr(CanonExpr::Const(spec_id, Vec::new()));

        let crate_arg1 = self.intern_expr(CanonExpr::App(crate_mk_expr, subject_expr));
        let crate_val = self.intern_expr(CanonExpr::App(crate_arg1, spec_expr));
        self.intern_expr(CanonExpr::App(root_expr, crate_val))
    }
}

impl Default for CanonicalArena {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Streaming NDJSON v3.1.0 parser
// ---------------------------------------------------------------------------

/// Metadata line (`line 1`) of a Lean 4 NDJSON export file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExportMeta {
    pub exporter_name: String,
    pub exporter_version: String,
    pub format_version: String,
    pub lean_version: String,
    pub lean_githash: String,
}

/// Parsed constant table from one NDJSON export file, interned into a shared
/// [`CanonicalArena`].
#[derive(Debug)]
pub struct ExportedEnv {
    pub meta: ExportMeta,
    pub constants: HashMap<CanonNameId, CanonConstInfo>,
    pub const_order: Vec<CanonNameId>,
}

/// Parse one NDJSON export stream into `arena`, failing closed on malformed
/// JSON, unsupported format versions, duplicate table bindings, dangling
/// back-references, unknown object tags, or duplicate constant names.
pub fn parse_ndjson_reader<R: BufRead>(
    reader: R,
    arena: &mut CanonicalArena,
    label: &str,
) -> Result<ExportedEnv, Failure> {
    let mut name_map: HashMap<u64, CanonNameId> = HashMap::with_capacity(4096);
    name_map.insert(0, arena.anonymous_name);
    let mut level_map: HashMap<u64, CanonLevelId> = HashMap::with_capacity(256);
    level_map.insert(0, arena.zero_level);
    let mut expr_map: HashMap<u64, CanonExprId> = HashMap::with_capacity(16384);
    let mut constants: HashMap<CanonNameId, CanonConstInfo> = HashMap::with_capacity(1024);
    let mut const_order: Vec<CanonNameId> = Vec::with_capacity(1024);

    let mut lines = reader.lines();
    let first_line = lines
        .next()
        .ok_or_else(|| Failure::policy(label, format!("{label}: empty NDJSON export")))?
        .map_err(|e| Failure::operational(label, format!("{label}: I/O error reading line 1: {e}")))?;
    let meta = parse_meta_line(&first_line, label)?;

    let mut line_no: usize = 1;
    for raw in lines {
        line_no += 1;
        if line_no > MAX_NDJSON_LINES {
            return Err(Failure::policy(
                label,
                format!("{label}: NDJSON export exceeds maximum line count ({MAX_NDJSON_LINES})"),
            ));
        }
        let line = raw.map_err(|e| {
            Failure::operational(label, format!("{label}:{line_no}: I/O error: {e}"))
        })?;
        if line.is_empty() {
            continue;
        }
        let val: Value = serde_json::from_str(&line).map_err(|e| {
            Failure::policy(label, format!("{label}:{line_no}: invalid JSON: {e}"))
        })?;
        let obj = val.as_object().ok_or_else(|| {
            Failure::policy(label, format!("{label}:{line_no}: expected JSON object"))
        })?;
        parse_record(
            obj,
            arena,
            &mut name_map,
            &mut level_map,
            &mut expr_map,
            &mut constants,
            &mut const_order,
            label,
            line_no,
        )?;
    }

    Ok(ExportedEnv { meta, constants, const_order })
}

/// Parse an NDJSON export file from disk while enforcing [`MAX_NDJSON_BYTES`]
/// and returning both the parsed environment and its SHA-256 hex digest.
pub fn parse_ndjson_file(
    path: &Path,
    arena: &mut CanonicalArena,
    label: &str,
) -> Result<(ExportedEnv, String), Failure> {
    let meta = fs::metadata(path).map_err(|e| {
        Failure::operational(label, format!("{label}: cannot stat {}: {e}", path.display()))
    })?;
    if !meta.is_file() {
        return Err(Failure::policy(
            label,
            format!("{label}: {} is not a regular file", path.display()),
        ));
    }
    if meta.len() > MAX_NDJSON_BYTES {
        return Err(Failure::policy(
            label,
            format!(
                "{label}: {} exceeds maximum NDJSON size ({} > {MAX_NDJSON_BYTES} bytes)",
                path.display(),
                meta.len()
            ),
        ));
    }
    let bytes = fs::read(path).map_err(|e| {
        Failure::operational(label, format!("{label}: cannot read {}: {e}", path.display()))
    })?;
    if (bytes.len() as u64) > MAX_NDJSON_BYTES {
        return Err(Failure::policy(
            label,
            format!("{label}: {} grew past maximum NDJSON size", path.display()),
        ));
    }
    let sha = sha256_bytes(&bytes);
    let env = parse_ndjson_reader(BufReader::new(bytes.as_slice()), arena, label)?;
    Ok((env, sha))
}

fn parse_meta_line(line: &str, label: &str) -> Result<ExportMeta, Failure> {
    let val: Value = serde_json::from_str(line)
        .map_err(|e| Failure::policy(label, format!("{label}:1: invalid metadata JSON: {e}")))?;
    let root = val.as_object().ok_or_else(|| {
        Failure::policy(label, format!("{label}:1: metadata line must be a JSON object"))
    })?;
    if root.len() != 1 {
        return Err(Failure::policy(
            label,
            format!("{label}:1: metadata line must contain only the `meta` key"),
        ));
    }
    let meta = root
        .get("meta")
        .and_then(Value::as_object)
        .ok_or_else(|| Failure::policy(label, format!("{label}:1: missing `meta` header")))?;
    let exporter = meta.get("exporter").and_then(Value::as_object).ok_or_else(|| {
        Failure::policy(label, format!("{label}:1: missing `meta.exporter` object"))
    })?;
    let format = meta.get("format").and_then(Value::as_object).ok_or_else(|| {
        Failure::policy(label, format!("{label}:1: missing `meta.format` object"))
    })?;
    let lean = meta
        .get("lean")
        .and_then(Value::as_object)
        .ok_or_else(|| Failure::policy(label, format!("{label}:1: missing `meta.lean` object")))?;

    let format_version = req_str(format, "version", label, 1)?;
    if format_version != SUPPORTED_EXPORT_FORMAT_VERSION {
        return Err(Failure::policy(
            label,
            format!(
                "{label}:1: unsupported NDJSON format version `{format_version}` \
                 (expected `{SUPPORTED_EXPORT_FORMAT_VERSION}`)"
            ),
        ));
    }
    Ok(ExportMeta {
        exporter_name: req_str(exporter, "name", label, 1)?.to_owned(),
        exporter_version: req_str(exporter, "version", label, 1)?.to_owned(),
        format_version: format_version.to_owned(),
        lean_version: req_str(lean, "version", label, 1)?.to_owned(),
        lean_githash: req_str(lean, "githash", label, 1)?.to_owned(),
    })
}

fn req_u64(
    obj: &serde_json::Map<String, Value>,
    key: &str,
    label: &str,
    line_no: usize,
) -> Result<u64, Failure> {
    obj.get(key)
        .and_then(Value::as_u64)
        .ok_or_else(|| Failure::policy(label, format!("{label}:{line_no}: invalid u64 `{key}`")))
}

fn req_str<'a>(
    obj: &'a serde_json::Map<String, Value>,
    key: &str,
    label: &str,
    line_no: usize,
) -> Result<&'a str, Failure> {
    obj.get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| Failure::policy(label, format!("{label}:{line_no}: invalid string `{key}`")))
}

fn req_bool(
    obj: &serde_json::Map<String, Value>,
    key: &str,
    label: &str,
    line_no: usize,
) -> Result<bool, Failure> {
    obj.get(key)
        .and_then(Value::as_bool)
        .ok_or_else(|| Failure::policy(label, format!("{label}:{line_no}: invalid bool `{key}`")))
}

fn req_arr<'a>(
    obj: &'a serde_json::Map<String, Value>,
    key: &str,
    label: &str,
    line_no: usize,
) -> Result<&'a [Value], Failure> {
    obj.get(key)
        .and_then(Value::as_array)
        .map(Vec::as_slice)
        .ok_or_else(|| Failure::policy(label, format!("{label}:{line_no}: invalid array `{key}`")))
}

fn req_obj<'a>(
    val: &'a Value,
    ctx: &str,
    label: &str,
    line_no: usize,
) -> Result<&'a serde_json::Map<String, Value>, Failure> {
    val.as_object()
        .ok_or_else(|| Failure::policy(label, format!("{label}:{line_no}: expected object in {ctx}")))
}

fn lookup_name(
    name_map: &HashMap<u64, CanonNameId>,
    idx: u64,
    label: &str,
    line_no: usize,
) -> Result<CanonNameId, Failure> {
    name_map
        .get(&idx)
        .copied()
        .ok_or_else(|| Failure::policy(label, format!("{label}:{line_no}: missing name idx {idx}")))
}

fn lookup_level(
    level_map: &HashMap<u64, CanonLevelId>,
    idx: u64,
    label: &str,
    line_no: usize,
) -> Result<CanonLevelId, Failure> {
    level_map.get(&idx).copied().ok_or_else(|| {
        Failure::policy(label, format!("{label}:{line_no}: missing level idx {idx}"))
    })
}

fn lookup_expr(
    expr_map: &HashMap<u64, CanonExprId>,
    idx: u64,
    label: &str,
    line_no: usize,
) -> Result<CanonExprId, Failure> {
    expr_map
        .get(&idx)
        .copied()
        .ok_or_else(|| Failure::policy(label, format!("{label}:{line_no}: missing expr idx {idx}")))
}

fn lookup_name_list(
    arr: &[Value],
    name_map: &HashMap<u64, CanonNameId>,
    label: &str,
    line_no: usize,
) -> Result<Vec<CanonNameId>, Failure> {
    let mut out = Vec::with_capacity(arr.len());
    for v in arr {
        let idx = v.as_u64().ok_or_else(|| {
            Failure::policy(label, format!("{label}:{line_no}: invalid name index in list"))
        })?;
        out.push(lookup_name(name_map, idx, label, line_no)?);
    }
    Ok(out)
}

fn parse_binder_info(s: &str, label: &str, line_no: usize) -> Result<BinderInfo, Failure> {
    match s {
        "default" => Ok(BinderInfo::Default),
        "implicit" => Ok(BinderInfo::Implicit),
        "strictImplicit" => Ok(BinderInfo::StrictImplicit),
        "instImplicit" => Ok(BinderInfo::InstImplicit),
        _ => Err(Failure::policy(label, format!("{label}:{line_no}: invalid binderInfo `{s}`"))),
    }
}

fn insert_const(
    constants: &mut HashMap<CanonNameId, CanonConstInfo>,
    const_order: &mut Vec<CanonNameId>,
    arena: &CanonicalArena,
    name: CanonNameId,
    info: CanonConstInfo,
    label: &str,
    line_no: usize,
) -> Result<(), Failure> {
    if constants.contains_key(&name) {
        return Err(Failure::policy(
            label,
            format!("{label}:{line_no}: duplicate declaration `{}`", arena.name_str(name)),
        ));
    }
    constants.insert(name, info);
    const_order.push(name);
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn parse_record(
    obj: &serde_json::Map<String, Value>,
    arena: &mut CanonicalArena,
    name_map: &mut HashMap<u64, CanonNameId>,
    level_map: &mut HashMap<u64, CanonLevelId>,
    expr_map: &mut HashMap<u64, CanonExprId>,
    constants: &mut HashMap<CanonNameId, CanonConstInfo>,
    const_order: &mut Vec<CanonNameId>,
    label: &str,
    line_no: usize,
) -> Result<(), Failure> {
    // 1. Name table entries: `{"in": idx, "str": ...}` or `{"in": idx, "num": ...}`.
    if let Some(idx_val) = obj.get("in") {
        if obj.len() != 2 {
            return Err(Failure::policy(
                label,
                format!("{label}:{line_no}: name record must have exactly 2 keys"),
            ));
        }
        let idx = idx_val.as_u64().ok_or_else(|| {
            Failure::policy(label, format!("{label}:{line_no}: invalid `in` index"))
        })?;
        if name_map.contains_key(&idx) {
            return Err(Failure::policy(
                label,
                format!("{label}:{line_no}: name index {idx} bound twice"),
            ));
        }
        let canon = if let Some(data) = obj.get("str") {
            let d = req_obj(data, "Name.str", label, line_no)?;
            let pre = lookup_name(name_map, req_u64(d, "pre", label, line_no)?, label, line_no)?;
            let s = req_str(d, "str", label, line_no)?.to_owned();
            arena.intern_name(CanonName::Str(pre, s))
        } else if let Some(data) = obj.get("num") {
            let d = req_obj(data, "Name.num", label, line_no)?;
            let pre = lookup_name(name_map, req_u64(d, "pre", label, line_no)?, label, line_no)?;
            let i = req_u64(d, "i", label, line_no)?;
            arena.intern_name(CanonName::Num(pre, i))
        } else {
            return Err(Failure::policy(
                label,
                format!("{label}:{line_no}: unknown name record variant"),
            ));
        };
        name_map.insert(idx, canon);
        return Ok(());
    }

    // 2. Universe level table entries: `{"il": idx, "succ"|"max"|"imax"|"param": ...}`.
    if let Some(idx_val) = obj.get("il") {
        if obj.len() != 2 {
            return Err(Failure::policy(
                label,
                format!("{label}:{line_no}: level record must have exactly 2 keys"),
            ));
        }
        let idx = idx_val.as_u64().ok_or_else(|| {
            Failure::policy(label, format!("{label}:{line_no}: invalid `il` index"))
        })?;
        if level_map.contains_key(&idx) {
            return Err(Failure::policy(
                label,
                format!("{label}:{line_no}: level index {idx} bound twice"),
            ));
        }
        let canon = if let Some(v) = obj.get("succ") {
            let inner = v.as_u64().ok_or_else(|| {
                Failure::policy(label, format!("{label}:{line_no}: invalid Level.succ"))
            })?;
            let l = lookup_level(level_map, inner, label, line_no)?;
            arena.intern_level(CanonLevel::Succ(l))
        } else if let Some(v) = obj.get("max") {
            let arr = v.as_array().ok_or_else(|| {
                Failure::policy(label, format!("{label}:{line_no}: invalid Level.max"))
            })?;
            if arr.len() != 2 {
                return Err(Failure::policy(
                    label,
                    format!("{label}:{line_no}: Level.max expects 2 elements"),
                ));
            }
            let a = lookup_level(
                level_map,
                arr[0].as_u64().ok_or_else(|| {
                    Failure::policy(label, format!("{label}:{line_no}: invalid Level.max[0]"))
                })?,
                label,
                line_no,
            )?;
            let b = lookup_level(
                level_map,
                arr[1].as_u64().ok_or_else(|| {
                    Failure::policy(label, format!("{label}:{line_no}: invalid Level.max[1]"))
                })?,
                label,
                line_no,
            )?;
            arena.intern_level(CanonLevel::Max(a, b))
        } else if let Some(v) = obj.get("imax") {
            let arr = v.as_array().ok_or_else(|| {
                Failure::policy(label, format!("{label}:{line_no}: invalid Level.imax"))
            })?;
            if arr.len() != 2 {
                return Err(Failure::policy(
                    label,
                    format!("{label}:{line_no}: Level.imax expects 2 elements"),
                ));
            }
            let a = lookup_level(
                level_map,
                arr[0].as_u64().ok_or_else(|| {
                    Failure::policy(label, format!("{label}:{line_no}: invalid Level.imax[0]"))
                })?,
                label,
                line_no,
            )?;
            let b = lookup_level(
                level_map,
                arr[1].as_u64().ok_or_else(|| {
                    Failure::policy(label, format!("{label}:{line_no}: invalid Level.imax[1]"))
                })?,
                label,
                line_no,
            )?;
            arena.intern_level(CanonLevel::IMax(a, b))
        } else if let Some(v) = obj.get("param") {
            let n_idx = v.as_u64().ok_or_else(|| {
                Failure::policy(label, format!("{label}:{line_no}: invalid Level.param"))
            })?;
            let n = lookup_name(name_map, n_idx, label, line_no)?;
            arena.intern_level(CanonLevel::Param(n))
        } else {
            return Err(Failure::policy(
                label,
                format!("{label}:{line_no}: unknown level record variant"),
            ));
        };
        level_map.insert(idx, canon);
        return Ok(());
    }

    // 3. Expression table entries: `{"ie": idx, <variant>: ...}`.
    if let Some(idx_val) = obj.get("ie") {
        if obj.len() != 2 {
            return Err(Failure::policy(
                label,
                format!("{label}:{line_no}: expr record must have exactly 2 keys"),
            ));
        }
        let idx = idx_val.as_u64().ok_or_else(|| {
            Failure::policy(label, format!("{label}:{line_no}: invalid `ie` index"))
        })?;
        if expr_map.contains_key(&idx) {
            return Err(Failure::policy(
                label,
                format!("{label}:{line_no}: expr index {idx} bound twice"),
            ));
        }
        let canon_expr = if let Some(v) = obj.get("bvar") {
            let db = v.as_u64().ok_or_else(|| {
                Failure::policy(label, format!("{label}:{line_no}: invalid Expr.bvar"))
            })?;
            CanonExpr::BVar(db)
        } else if let Some(v) = obj.get("sort") {
            let u = v.as_u64().ok_or_else(|| {
                Failure::policy(label, format!("{label}:{line_no}: invalid Expr.sort"))
            })?;
            CanonExpr::Sort(lookup_level(level_map, u, label, line_no)?)
        } else if let Some(v) = obj.get("const") {
            let d = req_obj(v, "Expr.const", label, line_no)?;
            let name = lookup_name(name_map, req_u64(d, "name", label, line_no)?, label, line_no)?;
            let us_raw = req_arr(d, "us", label, line_no)?;
            let mut us = Vec::with_capacity(us_raw.len());
            for u in us_raw {
                let uidx = u.as_u64().ok_or_else(|| {
                    Failure::policy(label, format!("{label}:{line_no}: invalid level idx in const"))
                })?;
                us.push(lookup_level(level_map, uidx, label, line_no)?);
            }
            CanonExpr::Const(name, us)
        } else if let Some(v) = obj.get("app") {
            let d = req_obj(v, "Expr.app", label, line_no)?;
            let f = lookup_expr(expr_map, req_u64(d, "fn", label, line_no)?, label, line_no)?;
            let a = lookup_expr(expr_map, req_u64(d, "arg", label, line_no)?, label, line_no)?;
            CanonExpr::App(f, a)
        } else if let Some(v) = obj.get("lam") {
            let d = req_obj(v, "Expr.lam", label, line_no)?;
            let _name = lookup_name(name_map, req_u64(d, "name", label, line_no)?, label, line_no)?;
            let _binder_info =
                parse_binder_info(req_str(d, "binderInfo", label, line_no)?, label, line_no)?;
            CanonExpr::Lam {
                ty: lookup_expr(expr_map, req_u64(d, "type", label, line_no)?, label, line_no)?,
                body: lookup_expr(expr_map, req_u64(d, "body", label, line_no)?, label, line_no)?,
            }
        } else if let Some(v) = obj.get("forallE") {
            let d = req_obj(v, "Expr.forallE", label, line_no)?;
            let _name = lookup_name(name_map, req_u64(d, "name", label, line_no)?, label, line_no)?;
            let _binder_info =
                parse_binder_info(req_str(d, "binderInfo", label, line_no)?, label, line_no)?;
            CanonExpr::ForallE {
                ty: lookup_expr(expr_map, req_u64(d, "type", label, line_no)?, label, line_no)?,
                body: lookup_expr(expr_map, req_u64(d, "body", label, line_no)?, label, line_no)?,
            }
        } else if let Some(v) = obj.get("letE") {
            let d = req_obj(v, "Expr.letE", label, line_no)?;
            let _name = lookup_name(name_map, req_u64(d, "name", label, line_no)?, label, line_no)?;
            let _nondep = req_bool(d, "nondep", label, line_no)?;
            CanonExpr::LetE {
                ty: lookup_expr(expr_map, req_u64(d, "type", label, line_no)?, label, line_no)?,
                value: lookup_expr(expr_map, req_u64(d, "value", label, line_no)?, label, line_no)?,
                body: lookup_expr(expr_map, req_u64(d, "body", label, line_no)?, label, line_no)?,
            }
        } else if let Some(v) = obj.get("proj") {
            let d = req_obj(v, "Expr.proj", label, line_no)?;
            CanonExpr::Proj {
                type_name: lookup_name(
                    name_map,
                    req_u64(d, "typeName", label, line_no)?,
                    label,
                    line_no,
                )?,
                idx: req_u64(d, "idx", label, line_no)?,
                struct_expr: lookup_expr(
                    expr_map,
                    req_u64(d, "struct", label, line_no)?,
                    label,
                    line_no,
                )?,
            }
        } else if let Some(v) = obj.get("natVal") {
            let s = v.as_str().ok_or_else(|| {
                Failure::policy(label, format!("{label}:{line_no}: invalid Expr.natVal"))
            })?;
            if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
                return Err(Failure::policy(
                    label,
                    format!("{label}:{line_no}: non-decimal natVal `{s}`"),
                ));
            }
            CanonExpr::NatLit(s.to_owned())
        } else if let Some(v) = obj.get("strVal") {
            let s = v.as_str().ok_or_else(|| {
                Failure::policy(label, format!("{label}:{line_no}: invalid Expr.strVal"))
            })?;
            CanonExpr::StrLit(s.to_owned())
        } else if let Some(v) = obj.get("mdata") {
            let d = req_obj(v, "Expr.mdata", label, line_no)?;
            let expr = lookup_expr(expr_map, req_u64(d, "expr", label, line_no)?, label, line_no)?;
            let kv_obj = d.get("data").and_then(Value::as_object).ok_or_else(|| {
                Failure::policy(label, format!("{label}:{line_no}: invalid Expr.mdata.data"))
            })?;
            for val in kv_obj.values() {
                if !val.is_string() {
                    return Err(Failure::policy(
                        label,
                        format!("{label}:{line_no}: non-string value in Expr.mdata.data"),
                    ));
                }
            }
            // `Expr.mdata` is transparent in Lean's kernel (`Expr.eqv` ignores
            // metadata wrappers). Map the index directly to the inner canonical
            // expression after validating the metadata object shape.
            expr_map.insert(idx, expr);
            return Ok(());
        } else {
            return Err(Failure::policy(
                label,
                format!("{label}:{line_no}: unknown expr record variant"),
            ));
        };
        let id = arena.intern_expr(canon_expr);
        expr_map.insert(idx, id);
        return Ok(());
    }

    // 4. Declaration records: single-key objects (`axiom`, `def`, `thm`,
    // `opaque`, `quot`, `inductive`).
    if obj.len() != 1 {
        return Err(Failure::policy(
            label,
            format!("{label}:{line_no}: unexpected top-level record keys"),
        ));
    }
    if let Some(v) = obj.get("axiom") {
        let d = req_obj(v, "axiom", label, line_no)?;
        let name = lookup_name(name_map, req_u64(d, "name", label, line_no)?, label, line_no)?;
        let level_params =
            lookup_name_list(req_arr(d, "levelParams", label, line_no)?, name_map, label, line_no)?;
        let ty = lookup_expr(expr_map, req_u64(d, "type", label, line_no)?, label, line_no)?;
        let is_unsafe = req_bool(d, "isUnsafe", label, line_no)?;
        return insert_const(
            constants,
            const_order,
            arena,
            name,
            CanonConstInfo::Axiom { name, level_params, ty, is_unsafe },
            label,
            line_no,
        );
    }
    if let Some(v) = obj.get("def") {
        let d = req_obj(v, "def", label, line_no)?;
        let name = lookup_name(name_map, req_u64(d, "name", label, line_no)?, label, line_no)?;
        let level_params =
            lookup_name_list(req_arr(d, "levelParams", label, line_no)?, name_map, label, line_no)?;
        let ty = lookup_expr(expr_map, req_u64(d, "type", label, line_no)?, label, line_no)?;
        let value = lookup_expr(expr_map, req_u64(d, "value", label, line_no)?, label, line_no)?;
        let hints = parse_hints(d.get("hints"), label, line_no)?;
        let safety = match req_str(d, "safety", label, line_no)? {
            "safe" => DefinitionSafety::Safe,
            "unsafe" => DefinitionSafety::Unsafe,
            "partial" => DefinitionSafety::Partial,
            other => {
                return Err(Failure::policy(
                    label,
                    format!("{label}:{line_no}: unknown def safety `{other}`"),
                ));
            }
        };
        let all = lookup_name_list(req_arr(d, "all", label, line_no)?, name_map, label, line_no)?;
        return insert_const(
            constants,
            const_order,
            arena,
            name,
            CanonConstInfo::Defn { name, level_params, ty, value, hints, safety, all },
            label,
            line_no,
        );
    }
    if let Some(v) = obj.get("thm") {
        let d = req_obj(v, "thm", label, line_no)?;
        let name = lookup_name(name_map, req_u64(d, "name", label, line_no)?, label, line_no)?;
        let level_params =
            lookup_name_list(req_arr(d, "levelParams", label, line_no)?, name_map, label, line_no)?;
        let ty = lookup_expr(expr_map, req_u64(d, "type", label, line_no)?, label, line_no)?;
        let value = lookup_expr(expr_map, req_u64(d, "value", label, line_no)?, label, line_no)?;
        let all = lookup_name_list(req_arr(d, "all", label, line_no)?, name_map, label, line_no)?;
        return insert_const(
            constants,
            const_order,
            arena,
            name,
            CanonConstInfo::Thm { name, level_params, ty, value, all },
            label,
            line_no,
        );
    }
    if let Some(v) = obj.get("opaque") {
        let d = req_obj(v, "opaque", label, line_no)?;
        let name = lookup_name(name_map, req_u64(d, "name", label, line_no)?, label, line_no)?;
        let level_params =
            lookup_name_list(req_arr(d, "levelParams", label, line_no)?, name_map, label, line_no)?;
        let ty = lookup_expr(expr_map, req_u64(d, "type", label, line_no)?, label, line_no)?;
        let value = lookup_expr(expr_map, req_u64(d, "value", label, line_no)?, label, line_no)?;
        // Lean's `LeanExport/Parse.lean` treats missing `isUnsafe` on `opaque`
        // as `false`; any present non-boolean value still fails closed.
        let is_unsafe = match d.get("isUnsafe") {
            None => false,
            Some(Value::Bool(b)) => *b,
            Some(_) => {
                return Err(Failure::policy(
                    label,
                    format!("{label}:{line_no}: invalid bool `isUnsafe` in opaque"),
                ));
            }
        };
        let all = lookup_name_list(req_arr(d, "all", label, line_no)?, name_map, label, line_no)?;
        return insert_const(
            constants,
            const_order,
            arena,
            name,
            CanonConstInfo::Opaque { name, level_params, ty, value, is_unsafe, all },
            label,
            line_no,
        );
    }
    if let Some(v) = obj.get("quot") {
        let d = req_obj(v, "quot", label, line_no)?;
        let name = lookup_name(name_map, req_u64(d, "name", label, line_no)?, label, line_no)?;
        let level_params =
            lookup_name_list(req_arr(d, "levelParams", label, line_no)?, name_map, label, line_no)?;
        let ty = lookup_expr(expr_map, req_u64(d, "type", label, line_no)?, label, line_no)?;
        let kind = match req_str(d, "kind", label, line_no)? {
            "type" => QuotKind::Type,
            "ctor" => QuotKind::Ctor,
            "lift" => QuotKind::Lift,
            "ind" => QuotKind::Ind,
            other => {
                return Err(Failure::policy(
                    label,
                    format!("{label}:{line_no}: unknown quot kind `{other}`"),
                ));
            }
        };
        return insert_const(
            constants,
            const_order,
            arena,
            name,
            CanonConstInfo::Quot { name, level_params, ty, kind },
            label,
            line_no,
        );
    }
    if let Some(v) = obj.get("inductive") {
        let d = req_obj(v, "inductive", label, line_no)?;
        for t in req_arr(d, "types", label, line_no)? {
            let td = req_obj(t, "inductInfo", label, line_no)?;
            let name = lookup_name(name_map, req_u64(td, "name", label, line_no)?, label, line_no)?;
            let level_params = lookup_name_list(
                req_arr(td, "levelParams", label, line_no)?,
                name_map,
                label,
                line_no,
            )?;
            let ty = lookup_expr(expr_map, req_u64(td, "type", label, line_no)?, label, line_no)?;
            let num_params = req_u64(td, "numParams", label, line_no)?;
            let num_indices = req_u64(td, "numIndices", label, line_no)?;
            let all =
                lookup_name_list(req_arr(td, "all", label, line_no)?, name_map, label, line_no)?;
            let ctors =
                lookup_name_list(req_arr(td, "ctors", label, line_no)?, name_map, label, line_no)?;
            let num_nested = req_u64(td, "numNested", label, line_no)?;
            let is_rec = req_bool(td, "isRec", label, line_no)?;
            let is_unsafe = req_bool(td, "isUnsafe", label, line_no)?;
            let is_reflexive = req_bool(td, "isReflexive", label, line_no)?;
            insert_const(
                constants,
                const_order,
                arena,
                name,
                CanonConstInfo::Induct {
                    name,
                    level_params,
                    ty,
                    num_params,
                    num_indices,
                    all,
                    ctors,
                    num_nested,
                    is_rec,
                    is_unsafe,
                    is_reflexive,
                },
                label,
                line_no,
            )?;
        }
        for c in req_arr(d, "ctors", label, line_no)? {
            let cd = req_obj(c, "ctorInfo", label, line_no)?;
            let name = lookup_name(name_map, req_u64(cd, "name", label, line_no)?, label, line_no)?;
            let level_params = lookup_name_list(
                req_arr(cd, "levelParams", label, line_no)?,
                name_map,
                label,
                line_no,
            )?;
            let ty = lookup_expr(expr_map, req_u64(cd, "type", label, line_no)?, label, line_no)?;
            let induct =
                lookup_name(name_map, req_u64(cd, "induct", label, line_no)?, label, line_no)?;
            let cidx = req_u64(cd, "cidx", label, line_no)?;
            let num_params = req_u64(cd, "numParams", label, line_no)?;
            let num_fields = req_u64(cd, "numFields", label, line_no)?;
            let is_unsafe = req_bool(cd, "isUnsafe", label, line_no)?;
            insert_const(
                constants,
                const_order,
                arena,
                name,
                CanonConstInfo::Ctor {
                    name,
                    level_params,
                    ty,
                    induct,
                    cidx,
                    num_params,
                    num_fields,
                    is_unsafe,
                },
                label,
                line_no,
            )?;
        }
        for r in req_arr(d, "recs", label, line_no)? {
            let rd = req_obj(r, "recInfo", label, line_no)?;
            let name = lookup_name(name_map, req_u64(rd, "name", label, line_no)?, label, line_no)?;
            let level_params = lookup_name_list(
                req_arr(rd, "levelParams", label, line_no)?,
                name_map,
                label,
                line_no,
            )?;
            let ty = lookup_expr(expr_map, req_u64(rd, "type", label, line_no)?, label, line_no)?;
            let all =
                lookup_name_list(req_arr(rd, "all", label, line_no)?, name_map, label, line_no)?;
            let num_params = req_u64(rd, "numParams", label, line_no)?;
            let num_indices = req_u64(rd, "numIndices", label, line_no)?;
            let num_motives = req_u64(rd, "numMotives", label, line_no)?;
            let num_minors = req_u64(rd, "numMinors", label, line_no)?;
            let k = req_bool(rd, "k", label, line_no)?;
            let is_unsafe = req_bool(rd, "isUnsafe", label, line_no)?;
            let raw_rules = req_arr(rd, "rules", label, line_no)?;
            let mut rules = Vec::with_capacity(raw_rules.len());
            for rule in raw_rules {
                let ruled = req_obj(rule, "recInfo.rule", label, line_no)?;
                rules.push(RecursorRule {
                    ctor: lookup_name(
                        name_map,
                        req_u64(ruled, "ctor", label, line_no)?,
                        label,
                        line_no,
                    )?,
                    nfields: req_u64(ruled, "nfields", label, line_no)?,
                    rhs: lookup_expr(
                        expr_map,
                        req_u64(ruled, "rhs", label, line_no)?,
                        label,
                        line_no,
                    )?,
                });
            }
            insert_const(
                constants,
                const_order,
                arena,
                name,
                CanonConstInfo::Rec {
                    name,
                    level_params,
                    ty,
                    all,
                    num_params,
                    num_indices,
                    num_motives,
                    num_minors,
                    rules,
                    k,
                    is_unsafe,
                },
                label,
                line_no,
            )?;
        }
        return Ok(());
    }
    Err(Failure::policy(
        label,
        format!("{label}:{line_no}: unknown NDJSON export record tag"),
    ))
}

fn parse_hints(
    val: Option<&Value>,
    label: &str,
    line_no: usize,
) -> Result<ReducibilityHints, Failure> {
    match val {
        Some(Value::String(s)) if s == "opaque" => Ok(ReducibilityHints::Opaque),
        Some(Value::String(s)) if s == "abbrev" => Ok(ReducibilityHints::Abbrev),
        Some(Value::Object(obj)) if obj.len() == 1 => {
            let level = req_u64(obj, "regular", label, line_no)?;
            let level_u32 = u32::try_from(level).map_err(|_| {
                Failure::policy(
                    label,
                    format!("{label}:{line_no}: regular hint height exceeds u32: {level}"),
                )
            })?;
            Ok(ReducibilityHints::Regular(level_u32))
        }
        _ => Err(Failure::policy(label, format!("{label}:{line_no}: invalid def `hints`"))),
    }
}

// ---------------------------------------------------------------------------
// Strict `#[serde(deny_unknown_fields)]` verdict schemas
// ---------------------------------------------------------------------------

/// One declaration-to-module attribution entry reported in closure inventories.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ClosureEntry {
    pub name: String,
    pub module: String,
}

/// Records an independent kernel that was deliberately skipped and why.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct SkippedKernel {
    pub kernel: String,
    pub reason: String,
}

/// Per-stage wall-clock latency measurements (in milliseconds) for Action
/// `5-init` + `5a` + `5b` + `5c`.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct NdjsonTimingMs {
    pub init_primitives: u64,
    pub export_expected: u64,
    pub export_proof: u64,
    pub rust_compare: u64,
    pub nanoda: u64,
    pub con_ron: u64,
    pub paranoid_quorum: u64,
    pub total: u64,
}

/// Strict typed verdict emitted by Action `5c` (`AnnealVerifyNdjson`).
///
/// `#[serde(deny_unknown_fields)]` ensures that neither malformed JSON nor
/// injected fields can slip past verdict deserialization.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct NdjsonAuditVerdict {
    pub audit_mode: String,
    pub theorem: String,
    pub canonical_root: String,
    pub subject: String,
    pub specification: String,
    pub expected: String,
    pub axioms: Vec<String>,
    pub sorry_declarations: Vec<String>,
    pub replay: bool,
    pub exact_type: bool,
    pub replayed_declarations: usize,
    pub expected_cone_declarations: usize,
    pub pinned_primitives_count: usize,
    pub expected_cone_sha256: String,
    pub proof_ndjson_sha256: String,
    pub init_primitives_sha256: String,
    pub kernels_passed: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub kernels_skipped: Vec<SkippedKernel>,
    pub paranoid_quorum: bool,
    pub timing_ms: NdjsonTimingMs,
    pub subject_closure: Vec<ClosureEntry>,
    pub model_closure: Vec<ClosureEntry>,
    pub specification_closure: Vec<ClosureEntry>,
}

/// Single advisory anti-vacuity warning emitted by legacy `"target-audit"`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct LegacySpecWarning {
    pub code: String,
    pub declaration: String,
    pub message: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub body: Option<String>,
}

/// Closed set of anti-vacuity warning codes emitted by legacy `"target-audit"`.
const VALID_LEGACY_SPEC_WARNING_CODES: &[&str] =
    &["unsatisfiable_safety", "trivial_property", "unused_spec_binding"];

/// Strict typed verdict validator for legacy `TrustedBoundary.lean`
/// `"target-audit"` responses on toolchains predating `v4.35.0`.
///
/// Replacing untyped `Map<String, Value>` inspection with a
/// `#[serde(deny_unknown_fields)]` struct ensures every required boolean and
/// identity field is present and matches the requested claim before acceptance.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct LegacyTargetAuditVerdict {
    pub theorem: String,
    pub canonical_root: String,
    pub subject: String,
    pub specification: String,
    pub graph: BTreeMap<String, Vec<crate::toolchain::ImportEdge>>,
    pub expected: String,
    pub axioms: Vec<String>,
    pub sorry_declarations: Vec<String>,
    pub replay: bool,
    pub exact_type: bool,
    pub replayed_declarations: usize,
    pub checked_alternate_proofs: usize,
    pub subject_closure: Vec<ClosureEntry>,
    pub model_closure: Vec<ClosureEntry>,
    pub specification_closure: Vec<ClosureEntry>,
    #[serde(default)]
    pub spec_warnings: Vec<LegacySpecWarning>,
}

/// Validate a legacy `"target-audit"` JSON payload against exact expected claim
/// fields and closed axiom rules.
pub fn validate_legacy_target_verdict(
    raw: &Value,
    expected_theorem: &str,
    expected_canonical_root: &str,
    expected_subject: &str,
    expected_specification: &str,
    expected_decl: &str,
    allow_sorry_in_proof: bool,
) -> Result<LegacyTargetAuditVerdict, Failure> {
    let verdict: LegacyTargetAuditVerdict = serde_json::from_value(raw.clone()).map_err(|e| {
        Failure::operational(
            "target-audit",
            format!("inspector result failed strict schema validation: {e}"),
        )
    })?;
    if !verdict.replay || !verdict.exact_type {
        return Err(Failure::policy(
            "target-audit",
            "inspector result did not certify replay and exactType",
        ));
    }
    if verdict.replayed_declarations == 0 {
        return Err(Failure::policy(
            "target-audit",
            "inspector result reported zero replayed declarations",
        ));
    }
    if verdict.theorem != expected_theorem
        || verdict.canonical_root != expected_canonical_root
        || verdict.subject != expected_subject
        || verdict.specification != expected_specification
        || verdict.expected != expected_decl
    {
        return Err(Failure::policy(
            "target-audit",
            "inspector result claim identities differ from request",
        ));
    }
    for (label, closure) in [
        ("subjectClosure", &verdict.subject_closure),
        ("modelClosure", &verdict.model_closure),
        ("specificationClosure", &verdict.specification_closure),
    ] {
        if closure.is_empty() || closure.iter().any(|e| e.name.is_empty() || e.module.is_empty()) {
            return Err(Failure::policy(
                "target-audit",
                format!("inspector result reported empty or malformed {label}"),
            ));
        }
    }
    let uses_sorry_ax = validate_axiom_list(&verdict.axioms, allow_sorry_in_proof, "target-audit")?;
    if verdict.sorry_declarations.iter().any(String::is_empty) {
        return Err(Failure::policy(
            "target-audit",
            "malformed entry in sorryDeclarations",
        ));
    }
    if allow_sorry_in_proof {
        if uses_sorry_ax != !verdict.sorry_declarations.is_empty() {
            return Err(Failure::policy(
                "target-audit",
                "mismatch between sorryAx axiom and sorryDeclarations",
            ));
        }
    } else if !verdict.sorry_declarations.is_empty() {
        return Err(Failure::policy(
            "target-audit",
            "unexpected sorryDeclarations when allow_sorry_in_proof is false",
        ));
    }
    for warning in &verdict.spec_warnings {
        if !VALID_LEGACY_SPEC_WARNING_CODES.contains(&warning.code.as_str()) {
            return Err(Failure::operational(
                "target-audit",
                format!("inspector result reported unknown specWarnings code `{}`", warning.code),
            ));
        }
        if warning.declaration.is_empty() || warning.message.is_empty() {
            return Err(Failure::operational(
                "target-audit",
                "inspector result reported malformed specWarnings entry with empty declaration/message",
            ));
        }
        if warning.body.as_deref().is_some_and(str::is_empty) {
            return Err(Failure::operational(
                "target-audit",
                "inspector result reported malformed specWarnings entry with empty body label",
            ));
        }
    }
    Ok(verdict)
}

/// Validate an [`NdjsonAuditVerdict`] round-tripped through JSON to guarantee
/// schema invariants hold unconditionally.
pub fn validate_ndjson_verdict(
    verdict: &NdjsonAuditVerdict,
    expected_theorem: &str,
    expected_canonical_root: &str,
    expected_subject: &str,
    expected_specification: &str,
    expected_decl: &str,
    allow_sorry_in_proof: bool,
) -> Result<(), Failure> {
    if verdict.audit_mode != "ndjson_comparator" {
        return Err(Failure::operational("ndjson-comparator", "unexpected auditMode"));
    }
    if !verdict.replay || !verdict.exact_type {
        return Err(Failure::policy(
            "ndjson-comparator",
            "verdict did not certify replay and exactType",
        ));
    }
    if verdict.replayed_declarations == 0 {
        return Err(Failure::policy(
            "ndjson-comparator",
            "verdict reported zero replayed declarations",
        ));
    }
    if verdict.theorem != expected_theorem
        || verdict.canonical_root != expected_canonical_root
        || verdict.subject != expected_subject
        || verdict.specification != expected_specification
        || verdict.expected != expected_decl
    {
        return Err(Failure::policy(
            "ndjson-comparator",
            "verdict claim identities differ from request",
        ));
    }
    for (label, closure) in [
        ("subjectClosure", &verdict.subject_closure),
        ("modelClosure", &verdict.model_closure),
        ("specificationClosure", &verdict.specification_closure),
    ] {
        if closure.is_empty() || closure.iter().any(|e| e.name.is_empty() || e.module.is_empty()) {
            return Err(Failure::policy(
                "ndjson-comparator",
                format!("verdict reported empty or malformed {label}"),
            ));
        }
    }
    if verdict.pinned_primitives_count != PINNED_INIT_PRIMITIVES.len() {
        return Err(Failure::policy(
            "ndjson-comparator",
            format!(
                "expected {} pinned primitives, found {}",
                PINNED_INIT_PRIMITIVES.len(),
                verdict.pinned_primitives_count
            ),
        ));
    }
    let sorry_used =
        validate_axiom_list(&verdict.axioms, allow_sorry_in_proof, "ndjson-comparator")?;
    if verdict.sorry_declarations.iter().any(String::is_empty) {
        return Err(Failure::policy(
            "ndjson-comparator",
            "malformed entry in sorryDeclarations",
        ));
    }
    if allow_sorry_in_proof {
        if sorry_used != !verdict.sorry_declarations.is_empty() {
            return Err(Failure::policy(
                "ndjson-comparator",
                "mismatch between sorryAx axiom and sorryDeclarations",
            ));
        }
    } else if !verdict.sorry_declarations.is_empty() {
        return Err(Failure::policy(
            "ndjson-comparator",
            "unexpected sorryDeclarations when allow_sorry_in_proof is false",
        ));
    }
    if !verdict.kernels_passed.iter().any(|k| k == "nanoda_bin") {
        return Err(Failure::policy("ndjson-comparator", "nanoda_bin kernel check missing"));
    }
    if !sorry_used && !verdict.kernels_passed.iter().any(|k| k == "con-ron") {
        return Err(Failure::policy("ndjson-comparator", "con-ron kernel check missing"));
    }
    if verdict.paranoid_quorum {
        if !verdict.kernels_passed.iter().any(|k| k == "lean4lean") {
            return Err(Failure::policy("ndjson-comparator", "lean4lean quorum check missing"));
        }
        if !sorry_used && !verdict.kernels_passed.iter().any(|k| k == "con-leche") {
            return Err(Failure::policy("ndjson-comparator", "con-leche quorum check missing"));
        }
    }
    Ok(())
}

fn validate_axiom_list(
    axioms: &[String],
    allow_sorry_in_proof: bool,
    phase: &str,
) -> Result<bool, Failure> {
    let mut seen = BTreeSet::new();
    let mut uses_sorry_ax = false;
    for ax in axioms {
        if !seen.insert(ax.as_str()) {
            return Err(Failure::policy(phase, format!("duplicate axiom `{ax}` in verdict")));
        }
        if ax == "sorryAx" {
            if !allow_sorry_in_proof {
                return Err(Failure::policy(phase, format!("unpermitted axiom `{ax}` in verdict")));
            }
            uses_sorry_ax = true;
        } else if !STANDARD_PERMITTED_AXIOMS.contains(&ax.as_str()) {
            return Err(Failure::policy(phase, format!("unpermitted axiom `{ax}` in verdict")));
        }
    }
    Ok(uses_sorry_ax)
}

// ---------------------------------------------------------------------------
// Structural verification core (pure safe Rust, zero external processes)
// ---------------------------------------------------------------------------

/// Input specification for pure-Rust structural comparison of `5a`, `5-init`,
/// and `5b` exports prior to executing the external independent kernels.
#[derive(Debug, Clone)]
pub struct StructuralCompareRequest<'a> {
    pub theorem_name: &'a str,
    pub expected_declaration: &'a str,
    pub canonical_root: &'a str,
    pub subject_declaration: &'a str,
    pub specification_declaration: &'a str,
    pub allow_sorry_in_proof: bool,
    /// Root namespace prefixes reserved for `TargetRole::Proof` modules
    /// (for example `"Anneal"`, `"Proof"`, or custom authored proof modules)
    /// that must never appear in `expected_cone`.
    pub forbidden_expected_roots: BTreeSet<String>,
    /// Exact `TargetRole::Proof` module names whose declarations must never
    /// appear in `expected_cone` (allowing sibling hierarchies such as
    /// `MyCrate.Spec` beside `MyCrate.Proof`).
    pub forbidden_expected_modules: BTreeSet<String>,
    /// Retained target module names partitioned by role for closure reporting.
    pub capture_modules: Vec<String>,
    pub model_modules: Vec<String>,
    pub specification_modules: Vec<String>,
}

/// Verified structural summary produced by [`verify_ndjson_structure`].
#[derive(Debug, Clone)]
pub struct StructuralCompareSummary {
    pub axioms: Vec<String>,
    pub sorry_declarations: Vec<String>,
    pub sorry_used: bool,
    pub checked_declarations: usize,
    pub expected_cone_declarations: usize,
    pub subject_closure: Vec<ClosureEntry>,
    pub model_closure: Vec<ClosureEntry>,
    pub specification_closure: Vec<ClosureEntry>,
}

/// Perform all pure-Rust structural invariants of Action `5c` over parsed
/// `init_primitives_cone`, `expected_cone`, and `proof_full` environments:
///
/// 1. Verify all 39 [`PINNED_INIT_PRIMITIVES`] exist in `init_primitives`.
/// 2. Verify every constant in `expected_cone` exists in `proof_full` with
///    exact canonical hash-consed DAG identity.
/// 3. Verify every constant in `expected_cone` or `proof_full` whose name
///    appears in `init_primitives` matches `init_primitives` DAG-identically
///    (closing unused-primitive injection for `nanoda_bin`'s native reducers).
/// 4. Run the explicit `Quot.{mk,lift,ind}` post-check against
///    `init_primitives` and reject any foreign `.quotInfo` declaration.
/// 5. Verify `expected_declaration` is a closed `Prop` definition whose body is
///    the exact canonical root application
///    `canonical_root (Trusted.MirSemantics.Crate.mk subject specification)`, and
///    verify zero `TargetRole::Proof` / `Anneal` roots appear in
///    `expected_cone` (with `optParam` default arguments stripped).
/// 6. Verify `theorem_name` is a universe-monomorphic `.thmInfo` whose type is
///    either `expected_declaration` or its exact canonical root application.
/// 7. Traverse the full transitive closure of `expected_declaration` and
///    `theorem_name` (and scan all exported constants) to enforce:
///    - zero `.opaqueInfo` declarations (closing `CollectAxioms.lean`'s opaque
///      traversal omission),
///    - zero `unsafe` or `partial` declarations,
///    - closed positive axiom allowlist (`{Classical.choice, Quot.sound,
///      propext}`, plus `sorryAx` strictly on proof-only edges when
///      `allow_sorry_in_proof` is `true`).
pub fn verify_ndjson_structure(
    arena: &mut CanonicalArena,
    init_primitives: &ExportedEnv,
    expected_cone: &ExportedEnv,
    proof_full: &ExportedEnv,
    req: &StructuralCompareRequest<'_>,
) -> Result<StructuralCompareSummary, Failure> {
    let phase = "ndjson-comparator";

    // 1. Confirm the clean sysroot primitive cone pins all 39 required names.
    for prim in PINNED_INIT_PRIMITIVES {
        let id = arena.intern_dotted_name(prim);
        if !init_primitives.constants.contains_key(&id) {
            return Err(Failure::operational(
                phase,
                format!("init_primitives_cone is missing required primitive `{prim}`"),
            ));
        }
    }

    // 2. Explicit `Quot.{mk,lift,ind}` post-check baseline on `init_primitives`.
    let mut quot_ids = BTreeMap::new();
    for (qname, expected_kind) in QUOT_PRIMITIVES {
        let qid = arena.intern_dotted_name(qname);
        match init_primitives.constants.get(&qid) {
            Some(CanonConstInfo::Quot { kind, .. }) if *kind == expected_kind => {
                quot_ids.insert(qid, (qname, expected_kind));
            }
            Some(other) => {
                return Err(Failure::operational(
                    phase,
                    format!(
                        "init_primitives_cone has malformed quotient `{qname}` ({})",
                        other.kind_label()
                    ),
                ));
            }
            None => {
                return Err(Failure::operational(
                    phase,
                    format!("init_primitives_cone missing quotient `{qname}`"),
                ));
            }
        }
    }

    // 3. Verify `expected_cone ⊆ proof_full` with exact canonical DAG identity.
    for &name_id in &expected_cone.const_order {
        let expected_ci = &expected_cone.constants[&name_id];
        let Some(proof_ci) = proof_full.constants.get(&name_id) else {
            return Err(Failure::policy(
                phase,
                format!(
                    "expected declaration `{}` missing from proof export",
                    arena.name_str(name_id)
                ),
            ));
        };
        if expected_ci != proof_ci {
            return Err(Failure::policy(
                phase,
                format!(
                    "declaration `{}` differs between trusted expected export and proof export",
                    arena.name_str(name_id)
                ),
            ));
        }
    }

    // 4. Pin every `init_primitives` constant appearing in `expected_cone` or
    // `proof_full` to exact canonical DAG identity. This blocks injection of
    // altered definitions for kernel-accelerated primitives (`Nat.gcd`,
    // `String.ofList`, `eagerReduce`, `optParam`, etc.) even when `Expected`
    // does not reference them.
    for (label, env) in [("expected_cone", expected_cone), ("proof_full", proof_full)] {
        for &name_id in &env.const_order {
            let ci = &env.constants[&name_id];
            if let Some(pinned_ci) = init_primitives.constants.get(&name_id)
                && ci != pinned_ci
            {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "pinned Init primitive `{}` in {label} differs from clean sysroot definition",
                        arena.name_str(name_id)
                    ),
                ));
            }
            // Reject any foreign `.quotInfo` declaration outside the four
            // standard `Quot` primitives.
            if let CanonConstInfo::Quot { kind, .. } = ci {
                match quot_ids.get(&name_id) {
                    Some((_, expected_kind)) if expected_kind == kind => {}
                    _ => {
                        return Err(Failure::policy(
                            phase,
                            format!(
                                "unexpected quotient declaration `{}` in {label}",
                                arena.name_str(name_id)
                            ),
                        ));
                    }
                }
            }
        }
    }

    // Explicit Quotient post-check: whenever `Quot.sound` or any `Quot*`
    // primitive is present in `proof_full`, verify every present `Quot`
    // primitive matches the exact sysroot `.quotInfo` kind and definition.
    let quot_sound_id = arena.intern_dotted_name("Quot.sound");
    let any_quot_present = proof_full.constants.contains_key(&quot_sound_id)
        || quot_ids.keys().any(|id| proof_full.constants.contains_key(id));
    if any_quot_present {
        for (&qid, &(qname, expected_kind)) in &quot_ids {
            if let Some(proof_ci) = proof_full.constants.get(&qid) {
                let pinned_ci = &init_primitives.constants[&qid];
                match proof_ci {
                    CanonConstInfo::Quot { kind, .. }
                        if *kind == expected_kind && proof_ci == pinned_ci => {}
                    _ => {
                        return Err(Failure::policy(
                            phase,
                            format!(
                                "quotient post-check failed for `{qname}` in proof export"
                            ),
                        ));
                    }
                }
            }
        }
    }

    // 5. Verify `expected_declaration` shape and exact canonical root body.
    let expected_decl_id = arena.intern_dotted_name(req.expected_declaration);
    let expected_ci = expected_cone.constants.get(&expected_decl_id).ok_or_else(|| {
        Failure::policy(
            phase,
            format!("expected declaration `{}` missing from expected_cone", req.expected_declaration),
        )
    })?;
    let prop_sort = arena.intern_expr(CanonExpr::Sort(arena.zero_level));
    let canonical_expr = arena.build_canonical_claim_expr(
        req.canonical_root,
        req.subject_declaration,
        req.specification_declaration,
    );
    let expected_body = match expected_ci {
        CanonConstInfo::Defn { level_params, ty, value, safety, .. } => {
            if !level_params.is_empty() {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "expected declaration `{}` must not have universe parameters",
                        req.expected_declaration
                    ),
                ));
            }
            if *safety != DefinitionSafety::Safe {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "expected declaration `{}` must be safe",
                        req.expected_declaration
                    ),
                ));
            }
            if *ty != prop_sort {
                return Err(Failure::policy(
                    phase,
                    format!("expected declaration `{}` must have type Prop", req.expected_declaration),
                ));
            }
            if *value != canonical_expr {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "compiled expected body of `{}` differs from canonical root application",
                        req.expected_declaration
                    ),
                ));
            }
            *value
        }
        other => {
            return Err(Failure::policy(
                phase,
                format!(
                    "expected declaration `{}` must be a definition (found {})",
                    req.expected_declaration,
                    other.kind_label()
                ),
            ));
        }
    };

    // Statement-origin isolation on `expected_cone` (with `optParam` default
    // stripping): reject any constant belonging to a `Proof` / `Anneal`
    // namespace or any `TargetRole::Proof` module.
    let expected_cone_set: BTreeSet<CanonNameId> =
        expected_cone.constants.keys().copied().collect();
    let is_forbidden_expected_const = |arena: &CanonicalArena, cid: CanonNameId| -> bool {
        let root = arena.name_root(cid);
        if req.forbidden_expected_roots.contains(root) {
            return true;
        }
        req.forbidden_expected_modules
            .iter()
            .any(|m| arena.belongs_to_module(cid, m))
    };
    for &cid in &expected_cone.const_order {
        if is_forbidden_expected_const(arena, cid) {
            return Err(Failure::policy(
                phase,
                format!(
                    "expected cone contains forbidden proof-origin constant `{}`",
                    arena.name_str(cid)
                ),
            ));
        }
        let stripped_deps = arena.collect_const_deps(&expected_cone.constants[&cid], true);
        for dep in stripped_deps {
            if is_forbidden_expected_const(arena, dep) {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "expected declaration `{}` references forbidden proof-origin constant `{}`",
                        arena.name_str(cid),
                        arena.name_str(dep)
                    ),
                ));
            }
        }
    }

    // Mirror #4130's direct Phase 1 `TargetRole::Specification` constant check:
    // reject any `Specification` declaration directly referencing `Lean.Syntax*`
    // or runtime `panic*` primitives (`panic`, `panicCore`, `panicWithPos`,
    // `panicWithPosWithDecl`), while still allowing `Init.Data.String` helpers
    // reached by `deriving Repr` to reference `panicWithPosWithDecl` internally.
    for &cid in &expected_cone.const_order {
        let is_spec_const = req
            .specification_modules
            .iter()
            .any(|m| arena.belongs_to_module(cid, m));
        if is_spec_const {
            let deps = arena.collect_const_deps(&expected_cone.constants[&cid], false);
            for dep in deps {
                let user_dep = arena.strip_private_and_root(dep);
                let is_lean_syntax =
                    user_dep == "Lean.Syntax" || user_dep.starts_with("Lean.Syntax.");
                let is_panic_const = matches!(
                    user_dep,
                    "panic" | "panicCore" | "panicWithPos" | "panicWithPosWithDecl"
                );
                if is_lean_syntax || is_panic_const {
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "specification declaration `{}` cannot reference `{}`",
                            arena.name_str(cid),
                            arena.name_str(dep)
                        ),
                    ));
                }
            }
        }
    }

    // 6. Verify `theorem_name` is a closed `.thmInfo` proving `Expected.claim`
    // (or its exact unfolded canonical root application).
    let theorem_id = arena.intern_dotted_name(req.theorem_name);
    let expected_const_expr = arena.intern_expr(CanonExpr::Const(expected_decl_id, Vec::new()));
    let theorem_ci = proof_full.constants.get(&theorem_id).ok_or_else(|| {
        Failure::policy(
            phase,
            format!("target theorem `{}` missing from proof export", req.theorem_name),
        )
    })?;
    match theorem_ci {
        CanonConstInfo::Thm { level_params, ty, .. } => {
            if !level_params.is_empty() {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "target theorem `{}` must not have universe parameters",
                        req.theorem_name
                    ),
                ));
            }
            if *ty != expected_const_expr && *ty != expected_body {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "target theorem `{}` type differs from `{}` / canonical root",
                        req.theorem_name, req.expected_declaration
                    ),
                ));
            }
        }
        other => {
            return Err(Failure::policy(
                phase,
                format!(
                    "target root `{}` must be a theorem (found {})",
                    req.theorem_name,
                    other.kind_label()
                ),
            ));
        }
    }

    // 7. Scan every exported declaration in `proof_full` and perform BFS from
    // `expected_declaration` and `theorem_name` so that:
    // - zero `.opaqueInfo` declarations exist anywhere in the cone or export,
    // - zero `unsafe` or `partial` declarations exist anywhere in the export,
    // - every `.axiomInfo` is inside the closed allowlist, and
    // - any violation reports an exact shortest-path blame chain.
    let sorry_ax_id = arena.intern_dotted_name("sorryAx");
    let standard_axiom_ids: BTreeSet<CanonNameId> = STANDARD_PERMITTED_AXIOMS
        .iter()
        .map(|name| arena.intern_dotted_name(name))
        .collect();

    // First verify the expected cone strictly under the 3-axiom ceiling (never
    // permitting `sorryAx` in specifications, model, capture, or expected).
    let expected_bfs = bfs_cone(arena, expected_cone, &[expected_decl_id]);
    for &cid in &expected_bfs.visited {
        let ci = &expected_cone.constants[&cid];
        if matches!(ci, CanonConstInfo::Opaque { .. }) {
            let chain = format_blame_path(arena, &expected_bfs.parent, cid);
            return Err(Failure::policy(
                phase,
                format!(
                    "opaque declaration `{}` forbidden in expected cone (blame: {chain})",
                    arena.name_str(cid)
                ),
            ));
        }
        if ci.is_unsafe_or_partial() {
            let chain = format_blame_path(arena, &expected_bfs.parent, cid);
            return Err(Failure::policy(
                phase,
                format!(
                    "unsafe or partial declaration `{}` forbidden in expected cone (blame: {chain})",
                    arena.name_str(cid)
                ),
            ));
        }
        if matches!(ci, CanonConstInfo::Axiom { .. }) && !standard_axiom_ids.contains(&cid) {
            let chain = format_blame_path(arena, &expected_bfs.parent, cid);
            return Err(Failure::policy(
                phase,
                format!(
                    "unpermitted axiom `{}` in expected cone (blame: {chain})",
                    arena.name_str(cid)
                ),
            ));
        }
    }

    // Traverse the proof cone from `theorem_name` and `expected_declaration`.
    let proof_bfs = bfs_cone(arena, proof_full, &[theorem_id, expected_decl_id]);
    let mut axioms = BTreeSet::new();
    let mut sorry_declarations = BTreeSet::new();

    // Check every constant present anywhere in `proof_full` (not only BFS-
    // reached ones) so a compromised `5b` cannot smuggle an unreached `.opaque`
    // or illegal axiom past structural checks.
    for &cid in &proof_full.const_order {
        let ci = &proof_full.constants[&cid];
        if matches!(ci, CanonConstInfo::Opaque { .. }) {
            let chain = format_blame_path(arena, &proof_bfs.parent, cid);
            return Err(Failure::policy(
                phase,
                format!(
                    "opaque declaration `{}` forbidden in proof export (blame: {chain})",
                    arena.name_str(cid)
                ),
            ));
        }
        if ci.is_unsafe_or_partial() {
            let chain = format_blame_path(arena, &proof_bfs.parent, cid);
            return Err(Failure::policy(
                phase,
                format!(
                    "unsafe or partial declaration `{}` forbidden in proof export (blame: {chain})",
                    arena.name_str(cid)
                ),
            ));
        }
        if matches!(ci, CanonConstInfo::Axiom { .. }) {
            let allowed = standard_axiom_ids.contains(&cid)
                || (req.allow_sorry_in_proof && cid == sorry_ax_id);
            if !allowed {
                let chain = format_blame_path(arena, &proof_bfs.parent, cid);
                return Err(Failure::policy(
                    phase,
                    format!(
                        "unpermitted axiom `{}` in proof export (blame: {chain})",
                        arena.name_str(cid)
                    ),
                ));
            }
            if proof_bfs.visited.contains(&cid) {
                axioms.insert(arena.name_str(cid).to_owned());
            }
        }
        if proof_bfs.visited.contains(&cid) && cid != sorry_ax_id {
            let deps = arena.collect_const_deps(ci, false);
            if deps.contains(&sorry_ax_id) {
                if !req.allow_sorry_in_proof || expected_cone_set.contains(&cid) {
                    let chain = format_blame_path(arena, &proof_bfs.parent, cid);
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "unpermitted sorryAx reference in `{}` (blame: {chain})",
                            arena.name_str(cid)
                        ),
                    ));
                }
                sorry_declarations.insert(arena.name_str(cid).to_owned());
            }
        }
    }

    // Reject unreached `sorryAx` injected into `proof_full` even when
    // `allow_sorry_in_proof` is true so `axioms` and `sorryDeclarations` remain
    // strictly consistent with kernel coverage.
    if proof_full.constants.contains_key(&sorry_ax_id) && !proof_bfs.visited.contains(&sorry_ax_id)
    {
        return Err(Failure::policy(
            phase,
            "unpermitted unreached sorryAx declaration in proof export",
        ));
    }
    let sorry_used = axioms.contains("sorryAx");

    // Build closure inventories for Receipt v3 `moduleIdentities` provenance.
    let subject_id = arena.intern_dotted_name(req.subject_declaration);
    let spec_id = arena.intern_dotted_name(req.specification_declaration);
    let subject_bfs = bfs_cone(arena, expected_cone, &[subject_id]);
    let spec_bfs = bfs_cone(arena, expected_cone, &[spec_id]);

    let subject_closure = build_closure_entries(
        arena,
        &subject_bfs.visited,
        &req.capture_modules,
        Some((req.subject_declaration, req.capture_modules.first().map(String::as_str))),
    );
    let model_closure = build_closure_entries(
        arena,
        &expected_bfs.visited,
        &req.model_modules,
        None,
    );
    let specification_closure = build_closure_entries(
        arena,
        &spec_bfs.visited,
        &req.specification_modules,
        Some((req.specification_declaration, req.specification_modules.first().map(String::as_str))),
    );

    Ok(StructuralCompareSummary {
        axioms: axioms.into_iter().collect(),
        sorry_declarations: sorry_declarations.into_iter().collect(),
        sorry_used,
        checked_declarations: proof_full.const_order.len(),
        expected_cone_declarations: expected_cone.const_order.len(),
        subject_closure,
        model_closure,
        specification_closure,
    })
}

struct BfsResult {
    visited: BTreeSet<CanonNameId>,
    parent: HashMap<CanonNameId, CanonNameId>,
}

fn bfs_cone(arena: &CanonicalArena, env: &ExportedEnv, roots: &[CanonNameId]) -> BfsResult {
    let mut visited = BTreeSet::new();
    let mut parent = HashMap::new();
    let mut queue = VecDeque::new();
    for &root in roots {
        if env.constants.contains_key(&root) && visited.insert(root) {
            queue.push_back(root);
        }
    }
    while let Some(curr) = queue.pop_front() {
        let Some(ci) = env.constants.get(&curr) else {
            continue;
        };
        let deps = arena.collect_const_deps(ci, false);
        for dep in deps {
            if env.constants.contains_key(&dep) && visited.insert(dep) {
                parent.insert(dep, curr);
                queue.push_back(dep);
            }
        }
    }
    BfsResult { visited, parent }
}

/// Format a shortest-path dependency chain from a root declaration to `target`
/// (harvested from `ProofLib/TrustedClosure.lean`'s `findBlamePath`).
fn format_blame_path(
    arena: &CanonicalArena,
    parent: &HashMap<CanonNameId, CanonNameId>,
    target: CanonNameId,
) -> String {
    let mut chain = vec![arena.name_str(target).to_owned()];
    let mut cur = target;
    let mut guard = 0usize;
    while let Some(&p) = parent.get(&cur) {
        chain.push(arena.name_str(p).to_owned());
        cur = p;
        guard += 1;
        if guard > 256 {
            chain.push("...".to_owned());
            break;
        }
    }
    chain.reverse();
    chain.join(" -> ")
}

fn build_closure_entries(
    arena: &CanonicalArena,
    visited: &BTreeSet<CanonNameId>,
    role_modules: &[String],
    required_root: Option<(&str, Option<&str>)>,
) -> Vec<ClosureEntry> {
    let mut entries: Vec<ClosureEntry> = Vec::new();
    let mut covered_modules: BTreeSet<&str> = BTreeSet::new();
    let mut sorted_mods: Vec<&str> = role_modules.iter().map(String::as_str).collect();
    // Match longest module prefix first so `Trusted.MirSemantics.Memory` wins
    // over `Trusted.MirSemantics` and `Trusted`.
    sorted_mods.sort_by(|a, b| b.len().cmp(&a.len()).then_with(|| a.cmp(b)));

    for &cid in visited {
        let name = arena.name_str(cid);
        if let Some(&module) = sorted_mods
            .iter()
            .find(|&&m| name == m || (name.starts_with(m) && name.as_bytes().get(m.len()) == Some(&b'.')))
        {
            covered_modules.insert(module);
            entries.push(ClosureEntry { name: name.to_owned(), module: module.to_owned() });
        }
    }
    if let Some((root_name, Some(root_mod))) = required_root
        && !entries.iter().any(|e| e.name == root_name)
    {
        covered_modules.insert(root_mod);
        entries.push(ClosureEntry { name: root_name.to_owned(), module: root_mod.to_owned() });
    }
    // Ensure every retained module of this role is represented in provenance so
    // `moduleIdentities` binds every authenticated source file of that role.
    for m in role_modules {
        if !covered_modules.contains(m.as_str()) {
            entries.push(ClosureEntry { name: m.clone(), module: m.clone() });
        }
    }
    entries.sort_by(|a, b| a.name.cmp(&b.name).then_with(|| a.module.cmp(&b.module)));
    entries.dedup();
    entries
}

/// Render the `nanoda_bin` JSON configuration payload.
///
/// Always sets `"unpermitted_axiom_hard_error": true` so `nanoda_bin` aborts
/// immediately if any axiom outside `permitted_axioms` appears anywhere in the
/// export, even if unreferenced.
pub fn build_nanoda_config_json(
    export_file_path: &str,
    allow_sorry_in_proof: bool,
    num_threads: usize,
) -> Value {
    let mut permitted: Vec<&str> = STANDARD_PERMITTED_AXIOMS.to_vec();
    if allow_sorry_in_proof {
        permitted.push("sorryAx");
    }
    serde_json::json!({
        "use_stdin": false,
        "export_file_path": export_file_path,
        "permitted_axioms": permitted,
        "unpermitted_axiom_hard_error": true,
        "num_threads": num_threads.max(1),
        "nat_extension": true,
        "string_extension": true,
    })
}

// ---------------------------------------------------------------------------
// Unit tests (positive + negative adversarial matrix)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Synthesize a minimal, self-contained v3.1.0 NDJSON export defining the
    /// 39 pinned primitives (as trivial placeholder defs/quots for unit
    /// testing) plus `Expected.claim` and `Proof.verify`.
    fn synthetic_ndjson_fixture() -> (String, String, String) {
        let meta = r#"{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"0000000000000000000000000000000000000000","version":"4.35.0"}}}"#;

        // Build `init_primitives_cone.ndjson` containing all 39 primitives.
        let mut init_lines = vec![meta.to_owned()];
        let mut next_in = 1u64;
        let mut name_idx: HashMap<String, u64> = HashMap::new();
        let mut ensure_name = |lines: &mut Vec<String>, dotted: &str| -> u64 {
            if let Some(&id) = name_idx.get(dotted) {
                return id;
            }
            let mut cur = 0u64;
            let mut prefix = String::new();
            for seg in dotted.split('.') {
                if !prefix.is_empty() {
                    prefix.push('.');
                }
                prefix.push_str(seg);
                if let Some(&id) = name_idx.get(&prefix) {
                    cur = id;
                } else {
                    let id = next_in;
                    next_in += 1;
                    lines.push(format!(
                        r#"{{"in":{id},"str":{{"pre":{cur},"str":"{seg}"}}}}"#
                    ));
                    name_idx.insert(prefix.clone(), id);
                    cur = id;
                }
            }
            cur
        };

        // ie 0 = Sort 0 (Prop)
        init_lines.push(r#"{"ie":0,"sort":0}"#.to_owned());
        // il 1 = Succ 0 (Type 0), ie 1 = Sort 1
        init_lines.push(r#"{"il":1,"succ":0}"#.to_owned());
        init_lines.push(r#"{"ie":1,"sort":1}"#.to_owned());

        for prim in PINNED_INIT_PRIMITIVES {
            let nid = ensure_name(&mut init_lines, prim);
            if let Some((_, qkind)) = QUOT_PRIMITIVES.iter().find(|(n, _)| *n == prim) {
                let kind_str = match qkind {
                    QuotKind::Type => "type",
                    QuotKind::Ctor => "ctor",
                    QuotKind::Lift => "lift",
                    QuotKind::Ind => "ind",
                };
                init_lines.push(format!(
                    r#"{{"quot":{{"kind":"{kind_str}","levelParams":[],"name":{nid},"type":1}}}}"#
                ));
            } else {
                init_lines.push(format!(
                    r#"{{"def":{{"all":[{nid}],"hints":"abbrev","levelParams":[],"name":{nid},"safety":"safe","type":1,"value":0}}}}"#
                ));
            }
        }
        let init_ndjson = init_lines.join("\n") + "\n";

        // Build `expected_cone.ndjson` with intentionally shifted indices to
        // verify index-independent canonical DAG identity.
        let expected_ndjson = [
            meta,
            r#"{"in":10,"str":{"pre":0,"str":"Trusted"}}"#,
            r#"{"in":11,"str":{"pre":10,"str":"MirSemantics"}}"#,
            r#"{"in":12,"str":{"pre":11,"str":"UnitTheorem"}}"#,
            r#"{"in":13,"str":{"pre":11,"str":"Crate"}}"#,
            r#"{"in":14,"str":{"pre":13,"str":"mk"}}"#,
            r#"{"in":15,"str":{"pre":0,"str":"Captured"}}"#,
            r#"{"in":16,"str":{"pre":15,"str":"program"}}"#,
            r#"{"in":17,"str":{"pre":0,"str":"Spec"}}"#,
            r#"{"in":18,"str":{"pre":17,"str":"specs"}}"#,
            r#"{"in":19,"str":{"pre":0,"str":"Expected"}}"#,
            r#"{"in":20,"str":{"pre":19,"str":"claim"}}"#,
            r#"{"ie":10,"sort":0}"#,
            r#"{"ie":11,"const":{"name":12,"us":[]}}"#,
            r#"{"ie":12,"const":{"name":14,"us":[]}}"#,
            r#"{"ie":13,"const":{"name":16,"us":[]}}"#,
            r#"{"ie":14,"const":{"name":18,"us":[]}}"#,
            r#"{"ie":15,"app":{"arg":13,"fn":12}}"#,
            r#"{"ie":16,"app":{"arg":14,"fn":15}}"#,
            r#"{"ie":17,"app":{"arg":16,"fn":11}}"#,
            r#"{"def":{"all":[12],"hints":"abbrev","levelParams":[],"name":12,"safety":"safe","type":10,"value":10}}"#,
            r#"{"def":{"all":[14],"hints":"abbrev","levelParams":[],"name":14,"safety":"safe","type":10,"value":10}}"#,
            r#"{"def":{"all":[16],"hints":"abbrev","levelParams":[],"name":16,"safety":"safe","type":10,"value":10}}"#,
            r#"{"def":{"all":[18],"hints":"abbrev","levelParams":[],"name":18,"safety":"safe","type":10,"value":10}}"#,
            r#"{"def":{"all":[20],"hints":"abbrev","levelParams":[],"name":20,"safety":"safe","type":10,"value":17}}"#,
        ]
        .join("\n")
            + "\n";

        // Build `proof_full.ndjson` with different indices (100+) matching
        // `expected_cone` plus `Proof.verify : Expected.claim`.
        let proof_ndjson = [
            meta,
            r#"{"in":100,"str":{"pre":0,"str":"Trusted"}}"#,
            r#"{"in":101,"str":{"pre":100,"str":"MirSemantics"}}"#,
            r#"{"in":102,"str":{"pre":101,"str":"UnitTheorem"}}"#,
            r#"{"in":103,"str":{"pre":101,"str":"Crate"}}"#,
            r#"{"in":104,"str":{"pre":103,"str":"mk"}}"#,
            r#"{"in":105,"str":{"pre":0,"str":"Captured"}}"#,
            r#"{"in":106,"str":{"pre":105,"str":"program"}}"#,
            r#"{"in":107,"str":{"pre":0,"str":"Spec"}}"#,
            r#"{"in":108,"str":{"pre":107,"str":"specs"}}"#,
            r#"{"in":109,"str":{"pre":0,"str":"Expected"}}"#,
            r#"{"in":110,"str":{"pre":109,"str":"claim"}}"#,
            r#"{"in":111,"str":{"pre":0,"str":"Proof"}}"#,
            r#"{"in":112,"str":{"pre":111,"str":"verify"}}"#,
            r#"{"ie":100,"sort":0}"#,
            r#"{"ie":101,"const":{"name":102,"us":[]}}"#,
            r#"{"ie":102,"const":{"name":104,"us":[]}}"#,
            r#"{"ie":103,"const":{"name":106,"us":[]}}"#,
            r#"{"ie":104,"const":{"name":108,"us":[]}}"#,
            r#"{"ie":105,"app":{"arg":103,"fn":102}}"#,
            r#"{"ie":106,"app":{"arg":104,"fn":105}}"#,
            r#"{"ie":107,"app":{"arg":106,"fn":101}}"#,
            r#"{"ie":108,"const":{"name":110,"us":[]}}"#,
            r#"{"def":{"all":[102],"hints":"abbrev","levelParams":[],"name":102,"safety":"safe","type":100,"value":100}}"#,
            r#"{"def":{"all":[104],"hints":"abbrev","levelParams":[],"name":104,"safety":"safe","type":100,"value":100}}"#,
            r#"{"def":{"all":[106],"hints":"abbrev","levelParams":[],"name":106,"safety":"safe","type":100,"value":100}}"#,
            r#"{"def":{"all":[108],"hints":"abbrev","levelParams":[],"name":108,"safety":"safe","type":100,"value":100}}"#,
            r#"{"def":{"all":[110],"hints":"abbrev","levelParams":[],"name":110,"safety":"safe","type":100,"value":107}}"#,
            r#"{"thm":{"all":[112],"levelParams":[],"name":112,"type":108,"value":100}}"#,
        ]
        .join("\n")
            + "\n";

        (init_ndjson, expected_ndjson, proof_ndjson)
    }

    fn default_req(allow_sorry: bool) -> StructuralCompareRequest<'static> {
        StructuralCompareRequest {
            theorem_name: "Proof.verify",
            expected_declaration: "Expected.claim",
            canonical_root: "Trusted.MirSemantics.UnitTheorem",
            subject_declaration: "Captured.program",
            specification_declaration: "Spec.specs",
            allow_sorry_in_proof: allow_sorry,
            forbidden_expected_roots: BTreeSet::from(["Anneal".to_owned(), "Proof".to_owned()]),
            forbidden_expected_modules: BTreeSet::from(["Proof".to_owned()]),
            capture_modules: vec!["Captured".to_owned()],
            model_modules: vec!["Trusted.MirSemantics".to_owned()],
            specification_modules: vec!["Spec".to_owned()],
        }
    }

    fn run_compare(
        init_s: &str,
        expected_s: &str,
        proof_s: &str,
        allow_sorry: bool,
    ) -> Result<StructuralCompareSummary, Failure> {
        let mut arena = CanonicalArena::new();
        let init_env = parse_ndjson_reader(BufReader::new(init_s.as_bytes()), &mut arena, "init")?;
        let expected_env =
            parse_ndjson_reader(BufReader::new(expected_s.as_bytes()), &mut arena, "expected")?;
        let proof_env =
            parse_ndjson_reader(BufReader::new(proof_s.as_bytes()), &mut arena, "proof")?;
        let req = default_req(allow_sorry);
        verify_ndjson_structure(&mut arena, &init_env, &expected_env, &proof_env, &req)
    }

    #[test]
    fn accepts_valid_index_shifted_exports() {
        let (init_s, expected_s, proof_s) = synthetic_ndjson_fixture();
        let summary = run_compare(&init_s, &expected_s, &proof_s, false).unwrap();
        assert!(summary.axioms.is_empty());
        assert!(summary.sorry_declarations.is_empty());
        assert!(!summary.sorry_used);
        assert_eq!(summary.expected_cone_declarations, 5);
        assert_eq!(summary.checked_declarations, 6);
    }

    #[test]
    fn rejects_mutated_expected_theorem() {
        let (init_s, expected_s, proof_s) = synthetic_ndjson_fixture();
        // Mutate `Expected.claim` in `proof_full` so its value is `Prop`
        // (`ie: 100`) rather than the canonical application (`ie: 107`).
        let tampered = proof_s.replace(
            r#""name":110,"safety":"safe","type":100,"value":107"#,
            r#""name":110,"safety":"safe","type":100,"value":100"#,
        );
        let err = run_compare(&init_s, &expected_s, &tampered, false).unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("Expected.claim"), "{err}");
    }

    #[test]
    fn rejects_injected_nat_gcd_primitive() {
        let (init_s, expected_s, mut proof_s) = synthetic_ndjson_fixture();
        // Inject a forged `Nat.gcd` with type `Sort 0` instead of the pinned
        // `Sort 1` from `init_primitives_cone`.
        proof_s.push_str(
            r#"{"in":200,"str":{"pre":0,"str":"Nat"}}
{"in":201,"str":{"pre":200,"str":"gcd"}}
{"def":{"all":[201],"hints":"abbrev","levelParams":[],"name":201,"safety":"safe","type":100,"value":100}}
"#,
        );
        let err = run_compare(&init_s, &expected_s, &proof_s, false).unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("Nat.gcd"), "{err}");
    }

    #[test]
    fn rejects_opaque_stub_in_proof_export() {
        let (init_s, expected_s, mut proof_s) = synthetic_ndjson_fixture();
        proof_s.push_str(
            r#"{"in":210,"str":{"pre":111,"str":"stub"}}
{"opaque":{"all":[210],"isUnsafe":false,"levelParams":[],"name":210,"type":100,"value":100}}
"#,
        );
        let err = run_compare(&init_s, &expected_s, &proof_s, false).unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("opaque declaration"), "{err}");
    }

    #[test]
    fn rejects_unpermitted_axiom_and_sorry_unless_explicitly_allowed() {
        let (init_s, expected_s, proof_s) = synthetic_ndjson_fixture();

        // 1. Custom axiom always rejected.
        let mut custom_ax = proof_s.clone();
        custom_ax.push_str(
            r#"{"in":220,"str":{"pre":0,"str":"BogusAxiom"}}
{"axiom":{"isUnsafe":false,"levelParams":[],"name":220,"type":100}}
"#,
        );
        let err = run_compare(&init_s, &expected_s, &custom_ax, false).unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("BogusAxiom"), "{err}");

        // 2. `sorryAx` rejected by default, accepted and tracked when allowed.
        let sorry_proof = proof_s.replace(
            r#"{"thm":{"all":[112],"levelParams":[],"name":112,"type":108,"value":100}}"#,
            r#"{"in":230,"str":{"pre":0,"str":"sorryAx"}}
{"ie":230,"const":{"name":230,"us":[]}}
{"axiom":{"isUnsafe":false,"levelParams":[],"name":230,"type":100}}
{"thm":{"all":[112],"levelParams":[],"name":112,"type":108,"value":230}}"#,
        );
        let err = run_compare(&init_s, &expected_s, &sorry_proof, false).unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("sorryAx"), "{err}");

        let ok = run_compare(&init_s, &expected_s, &sorry_proof, true).unwrap();
        assert!(ok.sorry_used);
        assert_eq!(ok.axioms, vec!["sorryAx"]);
        assert_eq!(ok.sorry_declarations, vec!["Proof.verify"]);
    }

    #[test]
    fn rejects_malformed_ndjson_and_foreign_quot() {
        let (init_s, expected_s, mut proof_s) = synthetic_ndjson_fixture();

        // Malformed JSON line.
        let bad_json = format!("{proof_s}{{not-json\n");
        let err = run_compare(&init_s, &expected_s, &bad_json, false).unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("invalid JSON"), "{err}");

        // Foreign `quot` declaration outside `Quot.{mk,lift,ind}`.
        proof_s.push_str(
            r#"{"in":240,"str":{"pre":0,"str":"FakeQuot"}}
{"quot":{"kind":"type","levelParams":[],"name":240,"type":100}}
"#,
        );
        let err = run_compare(&init_s, &expected_s, &proof_s, false).unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("FakeQuot"), "{err}");
    }

    #[test]
    fn strict_verdict_schema_rejects_unknown_fields() {
        let raw = serde_json::json!({
            "auditMode": "ndjson_comparator",
            "theorem": "Proof.verify",
            "canonicalRoot": "Trusted.MirSemantics.UnitTheorem",
            "subject": "Captured.program",
            "specification": "Spec.specs",
            "expected": "Expected.claim",
            "axioms": [],
            "sorryDeclarations": [],
            "replay": true,
            "exactType": true,
            "replayedDeclarations": 6,
            "expectedConeDeclarations": 5,
            "pinnedPrimitivesCount": 39,
            "expectedConeSha256": "0".repeat(64),
            "proofNdjsonSha256": "0".repeat(64),
            "initPrimitivesSha256": "0".repeat(64),
            "kernelsPassed": ["nanoda_bin", "con-ron"],
            "paranoidQuorum": false,
            "timingMs": {
                "initPrimitives": 0,
                "exportExpected": 100,
                "exportProof": 100,
                "rustCompare": 20,
                "nanoda": 150,
                "conRon": 150,
                "paranoidQuorum": 0,
                "total": 520
            },
            "subjectClosure": [],
            "modelClosure": [],
            "specificationClosure": [],
            "injectedUnknownField": true
        });
        let parsed: Result<NdjsonAuditVerdict, _> = serde_json::from_value(raw);
        assert!(parsed.is_err(), "deny_unknown_fields must reject extra fields");
    }

    #[test]
    fn legacy_verdict_validates_and_preserves_spec_warnings() {
        let base = serde_json::json!({
            "theorem": "Proof.verify",
            "canonicalRoot": "Trusted.MirSemantics.UnitTheorem",
            "subject": "Captured.program",
            "specification": "Spec.specs",
            "graph": {},
            "expected": "Expected.claim",
            "axioms": ["propext"],
            "sorryDeclarations": [],
            "replay": true,
            "exactType": true,
            "replayedDeclarations": 6,
            "checkedAlternateProofs": 0,
            "subjectClosure": [{"name": "Captured.program", "module": "Captured"}],
            "modelClosure": [{"name": "Trusted.MirSemantics.UnitTheorem", "module": "Trusted.MirSemantics"}],
            "specificationClosure": [{"name": "Spec.specs", "module": "Spec"}],
            "specWarnings": [{
                "code": "unsatisfiable_safety",
                "declaration": "Spec.specs",
                "message": "safety precondition reduces to False",
                "body": "rust-path-v1::locked"
            }]
        });
        let valid = validate_legacy_target_verdict(
            &base,
            "Proof.verify",
            "Trusted.MirSemantics.UnitTheorem",
            "Captured.program",
            "Spec.specs",
            "Expected.claim",
            false,
        )
        .expect("valid specWarnings entry should be preserved");
        assert_eq!(valid.spec_warnings.len(), 1);
        assert_eq!(valid.spec_warnings[0].code, "unsatisfiable_safety");
        assert_eq!(valid.spec_warnings[0].body.as_deref(), Some("rust-path-v1::locked"));

        for bad_entry in [
            serde_json::json!({"code": "bogus", "declaration": "Spec.specs", "message": "m"}),
            serde_json::json!({"code": "trivial_property", "declaration": "", "message": "m"}),
            serde_json::json!({"code": "trivial_property", "declaration": "Spec.specs", "message": ""}),
            serde_json::json!({"code": "unsatisfiable_safety", "declaration": "Spec.specs", "message": "m", "body": ""}),
            serde_json::json!({"code": "trivial_property", "declaration": "Spec.specs", "message": "m", "extra": 1}),
        ] {
            let mut mutated = base.clone();
            mutated["specWarnings"] = serde_json::json!([bad_entry]);
            assert!(
                validate_legacy_target_verdict(
                    &mutated,
                    "Proof.verify",
                    "Trusted.MirSemantics.UnitTheorem",
                    "Captured.program",
                    "Spec.specs",
                    "Expected.claim",
                    false,
                )
                .is_err(),
                "malformed specWarnings entry must be rejected: {bad_entry}"
            );
        }
    }

    #[test]
    fn nanoda_config_enforces_unpermitted_axiom_hard_error() {
        let cfg = build_nanoda_config_json("/work/in/proof.ndjson", false, 4);
        assert_eq!(cfg["unpermitted_axiom_hard_error"], Value::Bool(true));
        assert_eq!(cfg["nat_extension"], Value::Bool(true));
        assert_eq!(cfg["string_extension"], Value::Bool(true));
        assert_eq!(
            cfg["permitted_axioms"],
            serde_json::json!(["Classical.choice", "Quot.sound", "propext"])
        );
    }

    #[test]
    fn rejects_spec_referencing_panic_core_and_private_proof_helpers() {
        let (init_s, expected_s, proof_s) = synthetic_ndjson_fixture();

        // 1. Direct `Spec.specs -> panicCore` reference must fail closed.
        let inject_panic_expected = expected_s.replace(
            r#"{"def":{"all":[18],"hints":"abbrev","levelParams":[],"name":18,"safety":"safe","type":10,"value":10}}"#,
            r#"{"in":90,"str":{"pre":0,"str":"panicCore"}}
{"ie":90,"const":{"name":90,"us":[]}}
{"def":{"all":[90],"hints":"abbrev","levelParams":[],"name":90,"safety":"safe","type":10,"value":10}}
{"def":{"all":[18],"hints":"abbrev","levelParams":[],"name":18,"safety":"safe","type":10,"value":90}}"#,
        );
        let inject_panic_proof = proof_s.replace(
            r#"{"def":{"all":[108],"hints":"abbrev","levelParams":[],"name":108,"safety":"safe","type":100,"value":100}}"#,
            r#"{"in":190,"str":{"pre":0,"str":"panicCore"}}
{"ie":190,"const":{"name":190,"us":[]}}
{"def":{"all":[190],"hints":"abbrev","levelParams":[],"name":190,"safety":"safe","type":100,"value":100}}
{"def":{"all":[108],"hints":"abbrev","levelParams":[],"name":108,"safety":"safe","type":100,"value":190}}"#,
        );
        let err =
            run_compare(&init_s, &inject_panic_expected, &inject_panic_proof, false).unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("cannot reference"), "{err}");

        // 2. Forbidden proof module wrapped under `_private.<mod>.<idx>.*` in
        // `expected_cone` must still be caught by `forbidden_expected_modules`.
        let priv_expected = format!(
            "{expected_s}{}",
            r#"{"in":91,"str":{"pre":0,"str":"_private"}}
{"in":92,"str":{"pre":91,"str":"Proof"}}
{"in":93,"str":{"pre":92,"str":"0"}}
{"in":94,"str":{"pre":93,"str":"Proof"}}
{"in":95,"str":{"pre":94,"str":"helper"}}
{"def":{"all":[95],"hints":"abbrev","levelParams":[],"name":95,"safety":"safe","type":10,"value":10}}
"#
        );
        let priv_proof = format!(
            "{proof_s}{}",
            r#"{"in":191,"str":{"pre":0,"str":"_private"}}
{"in":192,"str":{"pre":191,"str":"Proof"}}
{"in":193,"str":{"pre":192,"str":"0"}}
{"in":194,"str":{"pre":193,"str":"Proof"}}
{"in":195,"str":{"pre":194,"str":"helper"}}
{"def":{"all":[195],"hints":"abbrev","levelParams":[],"name":195,"safety":"safe","type":100,"value":100}}
"#
        );
        let err = run_compare(&init_s, &priv_expected, &priv_proof, false).unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("forbidden proof-origin constant"), "{err}");
    }

    #[test]
    fn allows_crate_spec_module_sharing_root_with_proof_module() {
        let (init_s, expected_s, proof_s) = synthetic_ndjson_fixture();
        // Replace `Spec.specs` -> `MyCrate.Spec.specs` and `Proof.verify` ->
        // `MyCrate.Proof.verify`; both share `MyCrate` as their first segment,
        // so module-granular `forbidden_expected_modules` (`MyCrate.Proof`)
        // must NOT block `MyCrate.Spec`.
        let mut arena = CanonicalArena::new();
        let init_env = parse_ndjson_reader(BufReader::new(init_s.as_bytes()), &mut arena, "init")
            .expect("init");
        let expected_s = expected_s
            .replace(r#"{"in":17,"str":{"pre":0,"str":"Spec"}}"#, r#"{"in":169,"str":{"pre":0,"str":"MyCrate"}}
{"in":17,"str":{"pre":169,"str":"Spec"}}"#);
        let proof_s = proof_s
            .replace(r#"{"in":107,"str":{"pre":0,"str":"Spec"}}"#, r#"{"in":196,"str":{"pre":0,"str":"MyCrate"}}
{"in":107,"str":{"pre":196,"str":"Spec"}}"#)
            .replace(r#"{"in":111,"str":{"pre":0,"str":"Proof"}}"#, r#"{"in":111,"str":{"pre":196,"str":"Proof"}}"#);
        let expected_env =
            parse_ndjson_reader(BufReader::new(expected_s.as_bytes()), &mut arena, "expected")
                .expect("expected");
        let proof_env =
            parse_ndjson_reader(BufReader::new(proof_s.as_bytes()), &mut arena, "proof")
                .expect("proof");
        let req = StructuralCompareRequest {
            theorem_name: "MyCrate.Proof.verify",
            expected_declaration: "Expected.claim",
            canonical_root: "Trusted.MirSemantics.UnitTheorem",
            subject_declaration: "Captured.program",
            specification_declaration: "MyCrate.Spec.specs",
            allow_sorry_in_proof: false,
            forbidden_expected_roots: BTreeSet::from(["Anneal".to_owned(), "Proof".to_owned()]),
            forbidden_expected_modules: BTreeSet::from(["MyCrate.Proof".to_owned()]),
            capture_modules: vec!["Captured".to_owned()],
            model_modules: vec!["Trusted.MirSemantics".to_owned()],
            specification_modules: vec!["MyCrate.Spec".to_owned()],
        };
        let summary =
            verify_ndjson_structure(&mut arena, &init_env, &expected_env, &proof_env, &req)
                .expect("MyCrate.Spec sharing top root with MyCrate.Proof should succeed");
        assert_eq!(summary.specification_closure[0].name, "MyCrate.Spec.specs");
    }

    #[test]
    fn validate_ndjson_verdict_enforces_schema_and_quorum_invariants() {
        let base = NdjsonAuditVerdict {
            audit_mode: "ndjson_comparator".to_owned(),
            theorem: "Proof.verify".to_owned(),
            canonical_root: "Trusted.MirSemantics.UnitTheorem".to_owned(),
            subject: "Captured.program".to_owned(),
            specification: "Spec.specs".to_owned(),
            expected: "Expected.claim".to_owned(),
            axioms: vec![],
            sorry_declarations: vec![],
            replay: true,
            exact_type: true,
            replayed_declarations: 6,
            expected_cone_declarations: 5,
            pinned_primitives_count: PINNED_INIT_PRIMITIVES.len(),
            expected_cone_sha256: "0".repeat(64),
            proof_ndjson_sha256: "0".repeat(64),
            init_primitives_sha256: "0".repeat(64),
            kernels_passed: vec!["nanoda_bin".to_owned(), "con-ron".to_owned()],
            kernels_skipped: vec![],
            paranoid_quorum: false,
            timing_ms: NdjsonTimingMs {
                init_primitives: 0,
                export_expected: 10,
                export_proof: 10,
                rust_compare: 5,
                nanoda: 10,
                con_ron: 10,
                paranoid_quorum: 0,
                total: 45,
            },
            subject_closure: vec![ClosureEntry {
                name: "Captured.program".to_owned(),
                module: "Captured".to_owned(),
            }],
            model_closure: vec![ClosureEntry {
                name: "Trusted.MirSemantics.UnitTheorem".to_owned(),
                module: "Trusted.MirSemantics".to_owned(),
            }],
            specification_closure: vec![ClosureEntry {
                name: "Spec.specs".to_owned(),
                module: "Spec".to_owned(),
            }],
        };
        let check = |v: &NdjsonAuditVerdict, allow_sorry: bool| {
            validate_ndjson_verdict(
                v,
                "Proof.verify",
                "Trusted.MirSemantics.UnitTheorem",
                "Captured.program",
                "Spec.specs",
                "Expected.claim",
                allow_sorry,
            )
        };
        check(&base, false).unwrap();

        let mut bad_mode = base.clone();
        bad_mode.audit_mode = "other".to_owned();
        assert!(check(&bad_mode, false).is_err());

        let mut zero_replayed = base.clone();
        zero_replayed.replayed_declarations = 0;
        assert!(check(&zero_replayed, false).is_err());

        let mut dup_ax = base.clone();
        dup_ax.axioms = vec!["propext".to_owned(), "propext".to_owned()];
        assert!(check(&dup_ax, false).is_err());

        let mut bad_quorum = base.clone();
        bad_quorum.paranoid_quorum = true;
        assert!(check(&bad_quorum, false).is_err());
        bad_quorum.kernels_passed.extend(["lean4lean".to_owned(), "con-leche".to_owned()]);
        check(&bad_quorum, false).unwrap();

        let mut sorry_ok = base.clone();
        sorry_ok.axioms = vec!["sorryAx".to_owned()];
        sorry_ok.sorry_declarations = vec!["Proof.verify".to_owned()];
        sorry_ok.kernels_passed = vec!["nanoda_bin".to_owned()];
        assert!(check(&sorry_ok, false).is_err());
        check(&sorry_ok, true).unwrap();
    }
}
