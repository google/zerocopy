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
//! This module implements the verdict side of Anneal's split between trusted
//! exports (`5-init` clean sysroot primitives, `5a` trusted expected export,
//! `5-pin` clean sysroot re-export), the sandboxed proof export (`5b`), and
//! the verdict (`5c`: this pure-Rust comparator plus dual independent
//! kernels):
//!
//! 1. **Well-formed exports and canonical DAG identity (`5a` vs. `5b`):**
//!    Every export must declare each constant's dependencies before it
//!    (except within one inductive record), and each inductive record must
//!    be a consistent mutual block. Every constant in
//!    `expected_cone.ndjson` (exported with zero `Proof.*` or `Anneal.*`
//!    modules mounted) that also appears in `proof_full.ndjson` must be
//!    structurally identical there, and the whole cone of the expected
//!    declaration must appear, normalizing away per-file table indices.
//! 2. **Authenticated origin of every constant:** A constant whose name is in
//!    the authenticated sysroot inventory must equal its clean-sysroot
//!    re-export (`5-pin`, plus the 39 `5-init` primitives such as `Nat.gcd`
//!    or `String.ofList` that external checkers reduce natively), so sysroot
//!    status is never granted by name alone. A constant declared by a
//!    retained `Model`, `Capture`, `Specification`, or `Expected` module (per
//!    the exact `"target-consts"` module index) must appear in the trusted
//!    `5a` export. Every other `proof_full` constant is proof-origin and may
//!    not occupy the `Trusted` root, a reserved kernel/sysroot root, or a
//!    kernel-accelerated name.
//! 3. **Explicit `Quot.{mk,lift,ind}` post-check:** Verifies the four quotient
//!    primitive kinds and types against the pinned sysroot definitions and
//!    forbids any foreign `.quotInfo` declaration.
//! 4. **`.opaqueInfo` and unsafe/partial bans:** Lean's standard
//!    `CollectAxioms` traversal skips `.opaqueInfo` bodies, so every
//!    `.opaqueInfo` is rejected except non-unsafe sysroot constants (such as
//!    `System.Platform.getNumBits`) whose content item 2 pins to the clean
//!    sysroot. Every `unsafe` and `partial` declaration is rejected.
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
    collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque},
    fs,
    io::{BufRead, BufReader},
    path::Path,
};

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::toolchain::{Failure, ImportEdge, sha256_bytes};

/// Supported Lean 4 NDJSON export format version emitted by `leanexport`.
pub const SUPPORTED_EXPORT_FORMAT_VERSION: &str = "3.1.0";

/// Maximum size in bytes accepted for a single NDJSON export stream (256 MiB).
pub const MAX_NDJSON_BYTES: u64 = 256 * 1024 * 1024;

/// Maximum number of lines accepted in a single NDJSON export stream.
///
/// Together with [`MAX_NDJSON_BYTES`], this bounds the number of records a
/// hostile `5b` export can make the parser intern. It does not bound memory
/// tightly: each interned name also stores its full dotted rendering, so
/// deeply nested names cost memory quadratic in their depth.
pub const MAX_NDJSON_LINES: usize = 20_000_000;

/// Closed 3-element set of standard Lean 4 axioms permitted in untainted
/// proofs.
pub const STANDARD_PERMITTED_AXIOMS: [&str; 3] = ["Classical.choice", "Quot.sound", "propext"];

/// Exact `System.Platform` declarations admitted in target specifications
/// and pinned against the clean sysroot (`System.Platform.getNumBits` is an
/// `Init` `opaque`).
pub const PINNED_SYSTEM_PLATFORM_DECLS: [&str; 3] = [
    "System.Platform.numBits",
    "System.Platform.getNumBits",
    "System.Platform.numBits_eq",
];

/// Complete 39-element union of kernel-accelerated `Init` primitives trusted by
/// `nanoda_bin` (`nat_extension`, `string_extension`, `Quot`) and Lean's
/// `Lake/CLI/Check.lean` (`primitiveTargets` + `builtinTargets`).
///
/// Upstream pinned references (Lean `v4.35.0`, commit
/// `https://github.com/leanprover/lean4/tree/eb6cafb7290e8bd5f2937522d8d804f58f02bafc`):
/// - `src/lake/Lake/CLI/Check.lean` (`primitiveTargets` / `builtinTargets`)
/// - `src/kernel/expr_eq_fn.cpp` (`Expr.eqv` / `BEq Expr` alpha-equivalence)
/// - `src/Lean/Util/CollectAxioms.lean` (`CollectAxioms` skips `.opaqueInfo`)
/// - `src/LeanExport/Parse.lean` (`opaque` defaults missing `isUnsafe` to
///   `false`)
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

/// The canonical roots `Expected.claim` may apply, each paired with the
/// constructor of the crate value it applies the root to (mirroring
/// `TrustedBoundary.lean`'s `"target-audit"` canonical root check). Any other
/// root fails closed.
const CANONICAL_ROOTS: [(&str, &str); 4] = [
    ("Trusted.MirSemantics.CrateTheorem", "Trusted.MirSemantics.Crate.mk"),
    ("Trusted.MirSemantics.UnitTheorem", "Trusted.MirSemantics.Crate.mk"),
    ("Trusted.MirSemantics.CrateTheoremV2", "Trusted.MirSemantics.CrateV2.mk"),
    ("Trusted.MirSemantics.UnitTheoremV2", "Trusted.MirSemantics.CrateV2.mk"),
];

/// Return the crate constructor `canonical_root` applies, or `None` when
/// `canonical_root` is not an admitted canonical root.
fn canonical_crate_ctor(canonical_root: &str) -> Option<&'static str> {
    CANONICAL_ROOTS.iter().find(|(root, _)| *root == canonical_root).map(|(_, ctor)| *ctor)
}

/// Top-level namespaces reserved for the Lean kernel and standard library
/// (mirroring `TrustedBoundary.reservedKernelRoots`). Only sysroot-named
/// constants pinned to the clean sysroot re-export may live beneath these
/// roots, plus compiler-generated equation/splitter helpers attached to such
/// a sysroot compound constant.
const RESERVED_KERNEL_ROOTS: &[&str] = &[
    "Nat", "String", "Char", "Bool", "Int", "Int8", "Int16", "Int32", "Int64", "ISize", "UInt8",
    "UInt16", "UInt32", "UInt64", "USize", "BitVec", "Float", "Float32", "ByteArray", "Subarray",
    "Array", "List", "Option", "Sum", "Prod", "Fin", "Subtype", "Eq", "HEq", "Quot", "Classical",
    "Lean", "Init", "Std", "Lake", "LeanExport", "LeanIR", "System", "IO", "Task", "Thunk",
    "Unit", "PUnit", "Empty", "PEmpty", "True", "False", "And", "Or", "Not", "Iff", "Exists",
    "Sigma", "PSigma", "Decidable", "Nonempty", "Ordering", "Rat", "Except", "EStateM", "StateM",
];

/// Kernel-accelerated constant names in Lean's C++ reducer (`reduce_nat` and
/// `reduce_string`). Only the clean-sysroot definition may use these names.
const KERNEL_ACCELERATED_NAMES: &[&str] = &[
    "Nat.zero",
    "Nat.succ",
    "Nat.add",
    "Nat.sub",
    "Nat.mul",
    "Nat.pow",
    "Nat.gcd",
    "Nat.mod",
    "Nat.div",
    "Nat.beq",
    "Nat.ble",
    "Nat.land",
    "Nat.lor",
    "Nat.xor",
    "Nat.shiftLeft",
    "Nat.shiftRight",
    "String.ofList",
];

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
    fn level_params(&self) -> &[CanonNameId] {
        match self {
            Self::Axiom { level_params, .. }
            | Self::Defn { level_params, .. }
            | Self::Thm { level_params, .. }
            | Self::Opaque { level_params, .. }
            | Self::Quot { level_params, .. }
            | Self::Induct { level_params, .. }
            | Self::Ctor { level_params, .. }
            | Self::Rec { level_params, .. } => level_params,
        }
    }

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
///
/// Name lookup is strictly structural via `name_ids` (`CanonName` tree) and
/// never keys on rendered dot-joined strings, preventing component collisions
/// (such as `Str(Anonymous, "Classical.choice")` vs `Classical.choice` or
/// `Num(pre, 0)` vs `Str(pre, "0")`).
#[derive(Debug)]
pub struct CanonicalArena {
    names: Vec<CanonName>,
    name_ids: HashMap<CanonName, CanonNameId>,
    name_strings: Vec<String>,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NamePart<'a> {
    Str(&'a str),
    Num(u64),
}

impl CanonicalArena {
    /// Construct an arena pre-seeded with `Name.anonymous`, `Level.zero`,
    /// `Nat`, `String`, and `optParam`.
    pub fn new() -> Self {
        let mut arena = Self {
            names: Vec::with_capacity(4096),
            name_ids: HashMap::with_capacity(4096),
            name_strings: Vec::with_capacity(4096),
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
        self.name_strings.push(rendered);
        id
    }

    /// Intern a dotted ASCII Lean `Str`-component name such as
    /// `"Expected.claim"` structurally by splitting on `.`.
    pub fn intern_dotted_name(&mut self, dotted: &str) -> CanonNameId {
        let mut cur = self.anonymous_name;
        if dotted.is_empty() {
            return cur;
        }
        for seg in dotted.split('.') {
            cur = self.intern_name(CanonName::Str(cur, seg.to_owned()));
        }
        cur
    }

    /// Decode and intern an unambiguously encoded name emitted by
    /// `SpecPreflight.encodeCanonName` (`#<digits>` for numeric components,
    /// `\`-escaped `\.`, `\#`, `\\` inside string components).
    pub fn intern_encoded_name(&mut self, encoded: &str) -> CanonNameId {
        let mut cur = self.anonymous_name;
        if encoded.is_empty() {
            return cur;
        }
        let mut seg = String::new();
        let mut is_num = false;
        let mut at_seg_start = true;
        let mut chars = encoded.chars().peekable();
        let push_seg = |arena: &mut Self, cur: CanonNameId, seg: &str, is_num: bool| -> CanonNameId {
            if is_num && let Ok(n) = seg.parse::<u64>() {
                arena.intern_name(CanonName::Num(cur, n))
            } else {
                arena.intern_name(CanonName::Str(cur, seg.to_owned()))
            }
        };
        while let Some(c) = chars.next() {
            if at_seg_start && c == '#' {
                is_num = true;
                at_seg_start = false;
                continue;
            }
            at_seg_start = false;
            if c == '\\'
                && let Some(next) = chars.next()
            {
                seg.push(next);
                continue;
            }
            if c == '.' {
                cur = push_seg(self, cur, &seg, is_num);
                seg.clear();
                is_num = false;
                at_seg_start = true;
                continue;
            }
            seg.push(c);
        }
        push_seg(self, cur, &seg, is_num)
    }

    /// Render a canonical name ID back to its dotted Lean spelling.
    pub fn name_str(&self, id: CanonNameId) -> &str {
        &self.name_strings[id.0 as usize]
    }

    /// Encode a canonical name ID into the unambiguous `SpecPreflight`
    /// `encodeCanonName` wire format (`#<digits>` for numeric segments,
    /// `\`-escaped `\`, `.`, and `#` inside string segments).
    pub fn encode_canon_name(&self, id: CanonNameId) -> String {
        let parts = self.name_parts(id);
        Self::encode_parts(&parts)
    }

    fn encode_parts(parts: &[NamePart<'_>]) -> String {
        let mut out = String::new();
        for (i, part) in parts.iter().enumerate() {
            if i > 0 {
                out.push('.');
            }
            match *part {
                NamePart::Str(s) => {
                    for c in s.chars() {
                        if matches!(c, '\\' | '.' | '#') {
                            out.push('\\');
                        }
                        out.push(c);
                    }
                }
                NamePart::Num(n) => {
                    out.push('#');
                    out.push_str(&n.to_string());
                }
            }
        }
        out
    }

    fn name_parts(&self, id: CanonNameId) -> Vec<NamePart<'_>> {
        let mut parts = Vec::new();
        let mut cur = id;
        loop {
            match &self.names[cur.0 as usize] {
                CanonName::Anonymous => break,
                CanonName::Str(pre, s) => {
                    parts.push(NamePart::Str(s.as_str()));
                    cur = *pre;
                }
                CanonName::Num(pre, n) => {
                    parts.push(NamePart::Num(*n));
                    cur = *pre;
                }
            }
        }
        parts.reverse();
        parts
    }

    fn is_private_parts(parts: &[NamePart<'_>]) -> bool {
        parts.first() == Some(&NamePart::Str("_private"))
            && parts.iter().skip(1).any(|p| matches!(p, NamePart::Num(_)))
    }

    /// Strip Lean's structural `_private.<module>.<idx>` prefix (mirroring
    /// `TrustedBoundary.privateToUserName`).
    fn parts_without_private<'a, 'b>(parts: &'b [NamePart<'a>]) -> &'b [NamePart<'a>] {
        if parts.first() == Some(&NamePart::Str("_private"))
            && let Some(num_pos) = parts.iter().skip(1).position(|p| matches!(p, NamePart::Num(_)))
        {
            &parts[num_pos + 2..]
        } else {
            parts
        }
    }

    /// Strip Lean's structural `_private.<module>.<idx>` prefix and any
    /// `_root_` prefix.
    fn user_parts<'a, 'b>(parts: &'b [NamePart<'a>]) -> &'b [NamePart<'a>] {
        let after_private = Self::parts_without_private(parts);
        if after_private.first() == Some(&NamePart::Str("_root_")) {
            &after_private[1..]
        } else {
            after_private
        }
    }

    /// Return the user-visible root component of `id` after stripping any
    /// `_private.<module>.<idx>` and `_root_` prefixes.
    fn user_name_root(&self, id: CanonNameId) -> &str {
        let parts = self.name_parts(id);
        match Self::user_parts(&parts).first() {
            Some(NamePart::Str(s)) => s,
            _ => "",
        }
    }

    fn user_dotted_string(&self, id: CanonNameId) -> String {
        let parts = self.name_parts(id);
        Self::user_parts(&parts)
            .iter()
            .map(|p| match *p {
                NamePart::Str(s) => s.to_owned(),
                NamePart::Num(n) => n.to_string(),
            })
            .collect::<Vec<_>>()
            .join(".")
    }

    fn belongs_to_module_parts(parts: &[NamePart<'_>], module: &str) -> bool {
        let mod_segs: Vec<&str> = module.split('.').collect();
        if mod_segs.is_empty() {
            return false;
        }
        let matches_prefix = |slice: &[NamePart<'_>]| -> bool {
            slice.len() >= mod_segs.len()
                && slice
                    .iter()
                    .zip(mod_segs.iter())
                    .all(|(p, m)| matches!(p, NamePart::Str(s) if s == m))
        };
        if matches_prefix(parts) {
            return true;
        }
        if parts.first() == Some(&NamePart::Str("_private"))
            && parts.len() > mod_segs.len() + 1
            && matches_prefix(&parts[1..1 + mod_segs.len()])
            && matches!(parts[1 + mod_segs.len()], NamePart::Num(_))
        {
            return true;
        }
        false
    }

    /// Mirror `TrustedBoundary.isGeneratedEqHelper`: permit lazily-synthesized
    /// equation theorems and private matcher/splitter auxiliaries attached to
    /// an authenticated parent constant satisfying `is_origin`.
    fn is_generated_eq_helper<F>(
        &self,
        cid: CanonNameId,
        info: &CanonConstInfo,
        is_origin: &F,
    ) -> bool
    where
        F: Fn(&[NamePart<'_>]) -> bool,
    {
        let parts = self.name_parts(cid);
        let is_priv = Self::is_private_parts(&parts);
        let user = Self::parts_without_private(&parts);
        match info {
            CanonConstInfo::Thm { .. } => {
                if let Some((&NamePart::Str(suffix), parent)) = user.split_last()
                    && parent.len() >= 2
                    && is_generated_eq_theorem_suffix(suffix)
                    && is_origin(parent)
                {
                    return true;
                }
                is_priv && is_generated_splitter_subtree(is_origin, user)
            }
            CanonConstInfo::Defn { .. } => is_priv && is_generated_splitter_subtree(is_origin, user),
            _ => false,
        }
    }

    fn is_lean_syntax_const(&self, cid: CanonNameId) -> bool {
        let parts = self.name_parts(cid);
        let u = Self::user_parts(&parts);
        u.len() >= 2
            && matches!(u[0], NamePart::Str("Lean"))
            && matches!(u[1], NamePart::Str("Syntax"))
    }

    fn is_panic_spec_const(&self, cid: CanonNameId) -> bool {
        let parts = self.name_parts(cid);
        let u = Self::user_parts(&parts);
        if u.iter().any(|p| matches!(p, NamePart::Str(s) if s.contains('!'))) {
            return true;
        }
        matches!(
            u,
            [NamePart::Str("panic")]
                | [NamePart::Str("panicCore")]
                | [NamePart::Str("panicWithPos")]
                | [NamePart::Str("panicWithPosWithDecl")]
                | [NamePart::Str("outOfBounds")]
                | [NamePart::Str("String"), NamePart::Str("Pos"), NamePart::Str("sliceOrPanic")]
                | [
                    NamePart::Str("String"),
                    NamePart::Str("Slice"),
                    NamePart::Str("Pos"),
                    NamePart::Str("sliceOrPanic")
                ]
        )
    }

    fn is_forbidden_spec_transitive_const(&self, cid: CanonNameId) -> bool {
        let parts = self.name_parts(cid);
        let u = Self::user_parts(&parts);
        if let Some(NamePart::Str(root)) = u.first()
            && matches!(*root, "IO" | "BaseIO" | "EIO" | "EST" | "ST" | "Task" | "Dynlib")
        {
            return true;
        }
        let has_prefix2 = |a: &str, b: &str| {
            u.len() >= 2 && matches!(u[0], NamePart::Str(x) if x == a) && matches!(u[1], NamePart::Str(y) if y == b)
        };
        let has_prefix3 = |a: &str, b: &str, c: &str| {
            u.len() >= 3
                && matches!(u[0], NamePart::Str(x) if x == a)
                && matches!(u[1], NamePart::Str(y) if y == b)
                && matches!(u[2], NamePart::Str(z) if z == c)
        };
        if has_prefix2("Lean", "Macro")
            || has_prefix2("Lean", "Elab")
            || has_prefix2("Lean", "Core")
            || has_prefix2("Lean", "Meta")
            || has_prefix2("Lean", "Environment")
            || has_prefix2("Lean", "Compiler")
            || has_prefix2("Lean", "Internal")
            || has_prefix2("Lean", "Loop")
            || has_prefix2("Lean", "LoadDynlib")
            || has_prefix2("Lean", "loadDynlib")
            || has_prefix2("Lean", "loadPlugin")
            || has_prefix2("Lean", "Dynlib")
            || has_prefix2("Lean", "getGithash")
            || has_prefix2("Lean", "version")
            || has_prefix2("Init", "System")
            || has_prefix3("Std", "Internal", "UV")
            || matches!(u.first(), Some(NamePart::Str("repeatM")))
        {
            return true;
        }
        if matches!(u.first(), Some(NamePart::Str("System"))) {
            let allowed = has_prefix2("System", "Platform")
                && u.len() >= 3
                && matches!(
                    u[2],
                    NamePart::Str("numBits" | "getNumBits" | "numBits_eq")
                );
            return !allowed;
        }
        matches!(
            u,
            [NamePart::Str(
                "dbgTrace"
                    | "dbgTraceVal"
                    | "dbgTraceIfShared"
                    | "dbgSleep"
                    | "dbgStackTrace"
                    | "dbgStackTraceIf"
                    | "lean_dbg_trace"
                    | "lean_dbg_trace_if_shared"
                    | "lean_dbg_stack_trace"
                    | "lean_dbg_sleep"
                    | "loadDynlib"
                    | "loadPlugin"
                    | "lean_load_dynlib"
                    | "lean_load_plugin"
                    | "lean_dynlib_load"
                    | "lean_dynlib_get"
                    | "lean_dynlib_symbol_run_as_init"
                    | "includeStr"
            )]
        )
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

    /// Collect the dependencies `leanexport` must export alongside `info`.
    ///
    /// Unlike [`Self::collect_const_deps`], this omits the mutual-block `all`
    /// names of definitions, theorems, and opaques: `leanexport` records them
    /// as names only (`dumpNames val.all`), so a peer the value never uses is
    /// legitimately absent. Inductive and recursor `all` blocks, constructor
    /// lists, and constructor parents are exported as a unit and stay required.
    fn collect_required_deps(&self, info: &CanonConstInfo) -> BTreeSet<CanonNameId> {
        let mut deps = BTreeSet::new();
        match info {
            CanonConstInfo::Defn { ty, value, .. }
            | CanonConstInfo::Thm { ty, value, .. }
            | CanonConstInfo::Opaque { ty, value, .. } => {
                self.collect_expr_consts(*ty, false, &mut deps);
                self.collect_expr_consts(*value, false, &mut deps);
            }
            other => deps = self.collect_const_deps(other, false),
        }
        deps
    }

    /// Build the canonical `Expected.claim` application expression:
    /// `canonical_root (crate_ctor subject specification)`.
    fn build_canonical_claim_expr(
        &mut self,
        canonical_root: &str,
        crate_ctor: &str,
        subject: &str,
        specification: &str,
    ) -> CanonExprId {
        let root_id = self.intern_dotted_name(canonical_root);
        let crate_mk_id = self.intern_dotted_name(crate_ctor);
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

/// The types, constructors, and recursors of one `"inductive"` record, which
/// `leanexport` emits together as a unit, in record order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InductiveBlock {
    pub types: Vec<CanonNameId>,
    pub ctors: Vec<CanonNameId>,
    pub recs: Vec<CanonNameId>,
}

/// Parsed constant table from one NDJSON export file, interned into a shared
/// [`CanonicalArena`].
#[derive(Debug)]
pub struct ExportedEnv {
    pub meta: ExportMeta,
    pub constants: HashMap<CanonNameId, CanonConstInfo>,
    /// Constants in export order.
    pub const_order: Vec<CanonNameId>,
    /// Every `"inductive"` record, in export order.
    pub inductive_blocks: Vec<InductiveBlock>,
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
    let mut inductive_blocks: Vec<InductiveBlock> = Vec::new();

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
        // `leanexport` never writes an empty line; reject one rather than
        // guess how the external kernels' parsers would treat it.
        if line.is_empty() {
            return Err(Failure::policy(label, format!("{label}:{line_no}: empty NDJSON line")));
        }
        let val = parse_json_no_duplicate_keys(&line).map_err(|e| {
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
            &mut inductive_blocks,
            label,
            line_no,
        )?;
    }

    Ok(ExportedEnv { meta, constants, const_order, inductive_blocks })
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

/// Parse a JSON document while rejecting duplicate object keys at any nesting
/// depth so Rust and external kernels cannot diverge.
fn parse_json_no_duplicate_keys(input: &str) -> Result<Value, String> {
    use serde::de::{self, DeserializeSeed, MapAccess, SeqAccess, Visitor};

    struct StrictValueSeed;

    impl<'de> DeserializeSeed<'de> for StrictValueSeed {
        type Value = Value;

        fn deserialize<D>(self, deserializer: D) -> Result<Value, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            struct StrictVisitor;

            impl<'de> Visitor<'de> for StrictVisitor {
                type Value = Value;

                fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    f.write_str("any valid JSON value with unique object keys")
                }

                fn visit_bool<E: de::Error>(self, v: bool) -> Result<Value, E> {
                    Ok(Value::Bool(v))
                }

                fn visit_i64<E: de::Error>(self, v: i64) -> Result<Value, E> {
                    Ok(Value::Number(v.into()))
                }

                fn visit_u64<E: de::Error>(self, v: u64) -> Result<Value, E> {
                    Ok(Value::Number(v.into()))
                }

                fn visit_f64<E: de::Error>(self, v: f64) -> Result<Value, E> {
                    serde_json::Number::from_f64(v)
                        .map(Value::Number)
                        .ok_or_else(|| de::Error::custom("non-finite JSON number"))
                }

                fn visit_str<E: de::Error>(self, v: &str) -> Result<Value, E> {
                    Ok(Value::String(v.to_owned()))
                }

                fn visit_string<E: de::Error>(self, v: String) -> Result<Value, E> {
                    Ok(Value::String(v))
                }

                fn visit_unit<E: de::Error>(self) -> Result<Value, E> {
                    Ok(Value::Null)
                }

                fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Value, A::Error> {
                    let mut out = Vec::new();
                    while let Some(elem) = seq.next_element_seed(StrictValueSeed)? {
                        out.push(elem);
                    }
                    Ok(Value::Array(out))
                }

                fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Value, A::Error> {
                    let mut out = serde_json::Map::new();
                    while let Some(key) = map.next_key::<String>()? {
                        if out.contains_key(&key) {
                            return Err(de::Error::custom(format!("duplicate JSON key `{key}`")));
                        }
                        let val = map.next_value_seed(StrictValueSeed)?;
                        out.insert(key, val);
                    }
                    Ok(Value::Object(out))
                }
            }

            deserializer.deserialize_any(StrictVisitor)
        }
    }

    let mut de = serde_json::Deserializer::from_str(input);
    let val = StrictValueSeed.deserialize(&mut de).map_err(|e| e.to_string())?;
    de.end().map_err(|e| e.to_string())?;
    Ok(val)
}

fn parse_meta_line(line: &str, label: &str) -> Result<ExportMeta, Failure> {
    let val = parse_json_no_duplicate_keys(line)
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
    inductive_blocks: &mut Vec<InductiveBlock>,
    label: &str,
    line_no: usize,
) -> Result<(), Failure> {
    // 1. Name table entries (`"str"` or `"num"` variants).
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

    // 2. Universe level table entries (`"succ"|"max"|"imax"|"param"`).
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
        let block_start = const_order.len();
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
        let n_types = req_arr(d, "types", label, line_no)?.len();
        let n_ctors = req_arr(d, "ctors", label, line_no)?.len();
        let members = &const_order[block_start..];
        inductive_blocks.push(InductiveBlock {
            types: members[..n_types].to_vec(),
            ctors: members[n_types..n_types + n_ctors].to_vec(),
            recs: members[n_types + n_ctors..].to_vec(),
        });
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

/// Per-stage wall-clock latency measurements (in milliseconds) for Actions
/// `5-init`, `target-consts`, `5b`, `5a`, `5-pin`, and `5c`.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct NdjsonTimingMs {
    pub init_primitives: u64,
    pub target_consts: u64,
    pub sysroot_pins: u64,
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
    /// Admitted module import graph (`module -> imports`) of the verified
    /// target DAG, in the shape of `TrustedBoundary.lean`'s `"target-audit"`
    /// `graph`, from which `verify` enforces the bundled-model trust tiers.
    pub graph: BTreeMap<String, Vec<ImportEdge>>,
    pub expected: String,
    pub axioms: Vec<String>,
    pub sorry_declarations: Vec<String>,
    pub replay: bool,
    pub exact_type: bool,
    pub replayed_declarations: usize,
    pub expected_cone_declarations: usize,
    pub pinned_primitives_count: usize,
    /// Number of sysroot-named `expected_cone` / `proof_full` constant
    /// occurrences pinned to the clean sysroot re-export.
    pub sysroot_pinned_declarations: usize,
    pub expected_cone_sha256: String,
    pub proof_ndjson_sha256: String,
    pub init_primitives_sha256: String,
    pub sysroot_pins_sha256: String,
    pub leanexport_sha256: String,
    pub nanoda_bin_sha256: String,
    pub con_ron_sha256: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub con_leche_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub lean4lean_sha256: Option<String>,
    pub kernels_passed: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub kernels_skipped: Vec<SkippedKernel>,
    pub paranoid_quorum: bool,
    pub timing_ms: NdjsonTimingMs,
    pub subject_closure: Vec<ClosureEntry>,
    pub model_closure: Vec<ClosureEntry>,
    pub specification_closure: Vec<ClosureEntry>,
}

fn is_non_empty_digits(s: &str) -> bool {
    !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit())
}

fn is_generated_eq_theorem_suffix(s: &str) -> bool {
    matches!(
        s,
        "eq_def"
            | "eq_unfold"
            | "else_eq"
            | "induct"
            | "induct_unfolding"
            | "fun_cases"
            | "fun_cases_unfolding"
            | "congr_simp"
            | "hinj"
    ) || s.strip_prefix("eq_").is_some_and(is_non_empty_digits)
        || s.strip_prefix("hcongr_").is_some_and(is_non_empty_digits)
        || s.strip_prefix("congr_eq_").is_some_and(is_non_empty_digits)
}

fn is_generated_splitter_child_suffix(s: &str) -> bool {
    is_generated_eq_theorem_suffix(s)
        || s == "splitter"
        || s.strip_prefix("match_").is_some_and(is_non_empty_digits)
        || s.strip_prefix("_sparseCasesOn_").is_some_and(is_non_empty_digits)
        || s.strip_prefix("congr_").is_some_and(is_non_empty_digits)
}

fn is_generated_splitter_subtree<F>(is_origin: &F, parts: &[NamePart<'_>]) -> bool
where
    F: Fn(&[NamePart<'_>]) -> bool,
{
    let Some((&NamePart::Str(last), parent)) = parts.split_last() else {
        return false;
    };
    if last == "splitter" {
        return parent.len() >= 2 && is_origin(parent);
    }
    is_generated_splitter_child_suffix(last) && is_generated_splitter_subtree(is_origin, parent)
}

fn is_sha256_hex(s: &str) -> bool {
    s.len() == 64 && s.bytes().all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
}

/// Validate an [`NdjsonAuditVerdict`] against expected claim fields, closed
/// axiom rules, and required comparator binary digests.
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
    for (label, digest) in [
        ("expectedConeSha256", verdict.expected_cone_sha256.as_str()),
        ("proofNdjsonSha256", verdict.proof_ndjson_sha256.as_str()),
        ("initPrimitivesSha256", verdict.init_primitives_sha256.as_str()),
        ("sysrootPinsSha256", verdict.sysroot_pins_sha256.as_str()),
        ("leanexportSha256", verdict.leanexport_sha256.as_str()),
        ("nanodaBinSha256", verdict.nanoda_bin_sha256.as_str()),
        ("conRonSha256", verdict.con_ron_sha256.as_str()),
    ] {
        if !is_sha256_hex(digest) {
            return Err(Failure::operational(
                "ndjson-comparator",
                format!("verdict missing valid SHA-256 digest for {label}"),
            ));
        }
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
        // Every closure module must be a node of the admitted import graph,
        // as in `TrustedBoundary.lean`, whose closure origins are modules of
        // the imported environment that `graph` describes.
        if let Some(e) = closure.iter().find(|e| !verdict.graph.contains_key(&e.module)) {
            return Err(Failure::policy(
                "ndjson-comparator",
                format!("{label} module {} is absent from the verdict graph", e.module),
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
    if let Some(sha) = verdict.con_leche_sha256.as_deref()
        && !is_sha256_hex(sha)
    {
        return Err(Failure::operational(
            "ndjson-comparator",
            "verdict reported malformed conLecheSha256",
        ));
    }
    if let Some(sha) = verdict.lean4lean_sha256.as_deref()
        && !is_sha256_hex(sha)
    {
        return Err(Failure::operational(
            "ndjson-comparator",
            "verdict reported malformed lean4leanSha256",
        ));
    }
    if verdict.paranoid_quorum {
        if !verdict.kernels_passed.iter().any(|k| k == "lean4lean") {
            return Err(Failure::policy("ndjson-comparator", "lean4lean quorum check missing"));
        }
        if verdict.lean4lean_sha256.is_none() {
            return Err(Failure::operational(
                "ndjson-comparator",
                "verdict missing lean4leanSha256 under paranoidQuorum",
            ));
        }
        if !sorry_used && !verdict.kernels_passed.iter().any(|k| k == "con-leche") {
            return Err(Failure::policy("ndjson-comparator", "con-leche quorum check missing"));
        }
        if !sorry_used && verdict.con_leche_sha256.is_none() {
            return Err(Failure::operational(
                "ndjson-comparator",
                "verdict missing conLecheSha256 under paranoidQuorum",
            ));
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

/// Defining role of a retained non-`Proof` target module, as recorded by the
/// `SpecPreflight` `"target-consts"` module index.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum TargetOriginRole {
    Model,
    Capture,
    Specification,
    Expected,
}

/// Authenticated defining module of one retained non-`Proof` target constant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TargetConstOrigin {
    pub module: String,
    pub role: TargetOriginRole,
    /// `true` for a paired well-founded auxiliary `p._unsafe_rec` (safe but
    /// `partial`), which is never re-exported: any export containing it is
    /// rejected by the `partial` ban. `"target-consts"` already rejects every
    /// `unsafe` target constant.
    pub paired_unsafe_rec: bool,
}

impl TargetOriginRole {
    /// Mirror `TargetRole::allows` (and `TrustedBoundary.TargetRole.allows`)
    /// for compiled declaration edges between retained non-`Proof` modules:
    /// a constant of role `self` may reference a constant of role `dep`.
    pub fn allows(self, dep: Self) -> bool {
        match self {
            Self::Model => dep == Self::Model,
            Self::Capture => matches!(dep, Self::Model | Self::Capture),
            Self::Specification => matches!(dep, Self::Model | Self::Specification),
            Self::Expected => true,
        }
    }
}

/// Module index of the retained non-`Proof` target modules returned by
/// `SpecPreflight` `"target-consts"`.
#[derive(Debug, Clone, Default)]
pub struct TargetConstIndex {
    /// `encodeCanonName -> origin` for every target-module constant.
    pub origins: HashMap<String, TargetConstOrigin>,
    /// Encoded names of constants that a target module marks with
    /// `@[implemented_by]`, `@[extern]`, or `@[csimp]`.
    pub compiler_overrides: BTreeSet<String>,
}

/// Input specification for pure-Rust structural comparison of `5-init`,
/// `5-pin`, `5a`, and `5b` exports prior to executing the external kernels.
#[derive(Debug, Clone)]
pub struct StructuralCompareRequest<'a> {
    pub theorem_name: &'a str,
    pub expected_module: &'a str,
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
    /// Authenticated sysroot `encodeCanonName -> module_name` inventory
    /// collected from `Init`/`Std` `.olean`s with zero target code loaded.
    pub sysroot_const_to_module: &'a HashMap<String, String>,
    /// Exact `encodeCanonName -> origin` index of every constant declared by a
    /// retained `Model`, `Capture`, `Specification`, or `Expected` module
    /// (`SpecPreflight` `"target-consts"`).
    pub target_const_origins: &'a HashMap<String, TargetConstOrigin>,
    /// Encoded names of target-module constants carrying compiler overrides
    /// (`@[implemented_by]`, `@[extern]`, `@[csimp]`); none may be reached.
    pub target_compiler_overrides: &'a BTreeSet<String>,
}

/// Verified structural summary produced by [`verify_ndjson_structure`].
#[derive(Debug, Clone)]
pub struct StructuralCompareSummary {
    pub axioms: Vec<String>,
    pub sorry_declarations: Vec<String>,
    pub sorry_used: bool,
    pub checked_declarations: usize,
    pub expected_cone_declarations: usize,
    pub sysroot_pinned_declarations: usize,
    pub subject_closure: Vec<ClosureEntry>,
    pub model_closure: Vec<ClosureEntry>,
    pub specification_closure: Vec<ClosureEntry>,
}

/// Defining-module and command-line arguments for one sandboxed `leanexport`
/// run (`5a` or `5-pin`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExportPlan {
    /// Modules to import (`leanexport <modules...> -- <roots...>`).
    pub modules: Vec<String>,
    /// Root constant names, rendered as Lean name literals.
    pub roots: Vec<String>,
}

/// Render `id` as a Lean name literal that `leanexport` decodes with
/// `Syntax.decodeNameLit` back to exactly `id`, or `None` when no such
/// spelling exists. Numeric components are written as decimal digits and
/// string components that are not plain ASCII identifiers use `«...»`.
/// Callers never rely on this rendering for soundness: every root must reach
/// the export under its canonical identity or the comparator fails closed.
pub fn render_leanexport_name(arena: &CanonicalArena, id: CanonNameId) -> Option<String> {
    let parts = arena.name_parts(id);
    if parts.is_empty() {
        return None;
    }
    let mut out = String::new();
    for (i, part) in parts.iter().enumerate() {
        if i > 0 {
            out.push('.');
        }
        match *part {
            NamePart::Num(n) => {
                if i == 0 {
                    return None;
                }
                out.push_str(&n.to_string());
            }
            NamePart::Str(s) => {
                let plain = s.chars().next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                    && s != "_"
                    && s.chars().all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '\'' | '!' | '?'));
                if plain {
                    out.push_str(s);
                } else if s.contains(['«', '»', '\n', '\r']) {
                    return None;
                } else {
                    out.push('«');
                    out.push_str(s);
                    out.push('»');
                }
            }
        }
    }
    Some(out)
}

/// Return root constants for re-exporting every member of `subset` within
/// `env`: members referenced by a constant outside `subset`, plus, in export
/// order, any member not reachable from earlier roots through `subset`
/// edges. In an honest export each member's clean re-export then includes
/// it; anything the clean re-export lacks is later reported as absent.
fn subset_roots<F>(arena: &CanonicalArena, env: &ExportedEnv, in_subset: F) -> BTreeSet<CanonNameId>
where
    F: Fn(CanonNameId) -> bool,
{
    let mut roots = BTreeSet::new();
    for &cid in &env.const_order {
        if in_subset(cid) {
            continue;
        }
        for dep in arena.collect_const_deps(&env.constants[&cid], false) {
            if in_subset(dep) && env.constants.contains_key(&dep) {
                roots.insert(dep);
            }
        }
    }
    let mut covered = BTreeSet::new();
    let cover_from = |start: CanonNameId, covered: &mut BTreeSet<CanonNameId>| {
        let mut stack = vec![start];
        while let Some(cur) = stack.pop() {
            if !covered.insert(cur) {
                continue;
            }
            for dep in arena.collect_const_deps(&env.constants[&cur], false) {
                if in_subset(dep) && env.constants.contains_key(&dep) && !covered.contains(&dep) {
                    stack.push(dep);
                }
            }
        }
    };
    for &root in &roots {
        cover_from(root, &mut covered);
    }
    for &cid in &env.const_order {
        if in_subset(cid) && !covered.contains(&cid) {
            roots.insert(cid);
            cover_from(cid, &mut covered);
        }
    }
    roots
}

/// Plan the clean-sysroot `5-pin` export covering every constant of
/// `exports` whose name appears in the authenticated sysroot inventory.
pub fn plan_sysroot_pin_export(
    arena: &CanonicalArena,
    exports: &[&ExportedEnv],
    sysroot_const_to_module: &HashMap<String, String>,
) -> Result<ExportPlan, Failure> {
    let mut modules = BTreeSet::new();
    let mut roots = BTreeSet::new();
    for env in exports {
        let frontier = subset_roots(arena, env, |cid| {
            sysroot_const_to_module.contains_key(&arena.encode_canon_name(cid))
        });
        for cid in frontier {
            let module = &sysroot_const_to_module[&arena.encode_canon_name(cid)];
            let rendered = render_leanexport_name(arena, cid).ok_or_else(|| {
                Failure::policy(
                    "ndjson-sysroot-pins",
                    format!("cannot name sysroot constant `{}` for re-export", arena.name_str(cid)),
                )
            })?;
            modules.insert(module.clone());
            roots.insert(rendered);
        }
    }
    Ok(ExportPlan { modules: modules.into_iter().collect(), roots: roots.into_iter().collect() })
}

/// Plan the trusted `5a` export: `expected_declaration`, every
/// `Specification` constant except paired well-founded `_unsafe_rec`
/// auxiliaries (which are `partial`), and roots covering every retained target
/// constant that `proof_full` contains, so `5c` can pin each target-module
/// constant in `proof_full` to the trusted export.
pub fn plan_expected_export(
    arena: &mut CanonicalArena,
    proof_full: &ExportedEnv,
    target_const_origins: &HashMap<String, TargetConstOrigin>,
    trusted_modules: &[String],
    expected_declaration: &str,
) -> Result<ExportPlan, Failure> {
    let phase = "ndjson-export-expected";
    let mut ids = BTreeSet::new();
    ids.insert(arena.intern_dotted_name(expected_declaration));
    let mut spec_encoded: Vec<&str> = target_const_origins
        .iter()
        .filter(|(_, o)| o.role == TargetOriginRole::Specification && !o.paired_unsafe_rec)
        .map(|(enc, _)| enc.as_str())
        .collect();
    spec_encoded.sort_unstable();
    for enc in spec_encoded {
        ids.insert(arena.intern_encoded_name(enc));
    }
    let frontier = subset_roots(arena, proof_full, |cid| {
        target_const_origins
            .get(&arena.encode_canon_name(cid))
            .is_some_and(|o| !o.paired_unsafe_rec)
    });
    ids.extend(frontier);
    let mut roots = Vec::with_capacity(ids.len());
    for cid in ids {
        roots.push(render_leanexport_name(arena, cid).ok_or_else(|| {
            Failure::policy(
                phase,
                format!("cannot name target constant `{}` for re-export", arena.name_str(cid)),
            )
        })?);
    }
    roots.sort();
    roots.dedup();
    let mut modules: Vec<String> = trusted_modules.to_vec();
    modules.sort();
    modules.dedup();
    Ok(ExportPlan { modules, roots })
}

/// Fail closed unless `env` is a well-formed `leanexport` stream:
///
/// - Closed and ordered: every required dependency (see
///   `collect_required_deps`) of every constant is declared earlier in `env`,
///   or is a member of the constant's own `"inductive"` record.
///   `leanexport` writes each constant's dependencies before the constant,
///   and only the types, constructors, and recursors of one inductive record
///   refer to one another, so an open, forward, or cyclic reference means the
///   export is truncated or forged.
/// - Grouped: each `"inductive"` record is one mutual block (see
///   [`check_inductive_block`]).
fn check_export_well_formed(
    arena: &CanonicalArena,
    env: &ExportedEnv,
    label: &str,
    operational: bool,
) -> Result<(), Failure> {
    let fail = |msg: String| {
        if operational {
            Failure::operational("ndjson-comparator", msg)
        } else {
            Failure::policy("ndjson-comparator", msg)
        }
    };
    let mut block_of: HashMap<CanonNameId, usize> = HashMap::new();
    for (idx, block) in env.inductive_blocks.iter().enumerate() {
        for &cid in block.types.iter().chain(&block.ctors).chain(&block.recs) {
            block_of.insert(cid, idx);
        }
        check_inductive_block(arena, env, block)
            .map_err(|msg| fail(format!("{label} has a malformed inductive record: {msg}")))?;
    }
    let mut declared: HashSet<CanonNameId> = HashSet::with_capacity(env.const_order.len());
    for &cid in &env.const_order {
        let block = block_of.get(&cid);
        for dep in arena.collect_required_deps(&env.constants[&cid]) {
            if declared.contains(&dep) || (block.is_some() && block_of.get(&dep) == block) {
                continue;
            }
            return Err(fail(if dep == cid {
                format!(
                    "{label} is not in dependency order: `{}` refers to itself",
                    arena.name_str(cid)
                )
            } else if env.constants.contains_key(&dep) {
                format!(
                    "{label} is not in dependency order: `{}` refers to `{}`, which it \
                     declares later",
                    arena.name_str(cid),
                    arena.name_str(dep)
                )
            } else {
                format!(
                    "{label} is not closed: `{}` depends on `{}`, which it does not declare",
                    arena.name_str(cid),
                    arena.name_str(dep)
                )
            }));
        }
        declared.insert(cid);
    }
    Ok(())
}

/// Check that one `"inductive"` record is a consistent mutual block, as
/// `leanexport` emits it: every type lists exactly the record's types as
/// `all` and shares the first type's universe and parameter counts; the
/// types' constructor lists concatenate to exactly the record's
/// constructors; each constructor names its type, its index in that type's
/// list, and the type's universe and parameter counts; and the record has at
/// least one recursor, each listing exactly the record's types as `all`.
/// Recursor rules name only the record's constructors, except that an
/// auxiliary recursor of a nested block has rules for the nested container's
/// constructors, which must still be constructors.
fn check_inductive_block(
    arena: &CanonicalArena,
    env: &ExportedEnv,
    block: &InductiveBlock,
) -> Result<(), String> {
    let name = |cid: CanonNameId| arena.name_str(cid).to_owned();
    let Some(&first) = block.types.first() else {
        return Err("record declares no types".to_owned());
    };
    let mut header: Option<(&[CanonNameId], u64)> = None;
    let mut nested = false;
    let mut type_ctors: Vec<CanonNameId> = Vec::with_capacity(block.ctors.len());
    for &ty in &block.types {
        let Some(CanonConstInfo::Induct {
            level_params, num_params, all, ctors, num_nested, ..
        }) = env.constants.get(&ty)
        else {
            return Err(format!("`{}` is not an inductive type", name(ty)));
        };
        if all != &block.types {
            return Err(format!("the mutual types of `{}` differ from the record's", name(ty)));
        }
        match header {
            None => header = Some((level_params, *num_params)),
            Some((lps, nps)) if lps == level_params.as_slice() && nps == *num_params => {}
            Some(_) => {
                return Err(format!(
                    "`{}` has other universe or parameters than `{}`",
                    name(ty),
                    name(first)
                ));
            }
        }
        nested |= *num_nested != 0;
        for (idx, &ctor) in ctors.iter().enumerate() {
            let Some(CanonConstInfo::Ctor {
                induct,
                cidx,
                num_params: ctor_params,
                level_params: ctor_lps,
                ..
            }) = env.constants.get(&ctor)
            else {
                return Err(format!("`{}` of `{}` is not a constructor", name(ctor), name(ty)));
            };
            if *induct != ty
                || usize::try_from(*cidx).ok() != Some(idx)
                || ctor_params != num_params
                || ctor_lps != level_params
            {
                return Err(format!(
                    "constructor `{}` does not match its position in `{}`",
                    name(ctor),
                    name(ty)
                ));
            }
            type_ctors.push(ctor);
        }
    }
    if type_ctors != block.ctors {
        return Err(format!(
            "the constructors of `{}`'s record are not exactly its types' constructors",
            name(first)
        ));
    }
    if block.recs.is_empty() {
        return Err(format!("the record of `{}` has no recursor", name(first)));
    }
    for &rec in &block.recs {
        let Some(CanonConstInfo::Rec { all, rules, .. }) = env.constants.get(&rec) else {
            return Err(format!("`{}` is not a recursor", name(rec)));
        };
        if all != &block.types {
            return Err(format!("the types of recursor `{}` differ from the record's", name(rec)));
        }
        for rule in rules {
            let in_record = block.ctors.contains(&rule.ctor);
            let is_ctor =
                matches!(env.constants.get(&rule.ctor), Some(CanonConstInfo::Ctor { .. }));
            if !(in_record || nested && is_ctor) {
                return Err(format!(
                    "recursor `{}` has a rule for `{}`, which is not a constructor of the record",
                    name(rec),
                    name(rule.ctor)
                ));
            }
        }
    }
    Ok(())
}

/// Perform all pure-Rust structural invariants of Action `5c` over parsed
/// `init_primitives_cone`, `sysroot_pins`, `expected_cone`, and `proof_full`:
///
/// 1. Require identical export metadata, and require every export to be
///    closed and in dependency order with consistent inductive records
///    ([`check_export_well_formed`]).
/// 2. Verify all 39 [`PINNED_INIT_PRIMITIVES`], the 3 standard axioms, and
///    [`PINNED_SYSTEM_PLATFORM_DECLS`] exist in `init_primitives`, and run the
///    `Quot.{mk,lift,ind}` baseline check.
/// 3. Verify every constant in `expected_cone` that also appears in
///    `proof_full` is identical there, and that the whole cone of
///    `expected_declaration` appears in `proof_full`.
/// 4. Classify every constant by authenticated origin. A constant whose name
///    is in the sysroot inventory must equal its clean `5-pin` (or `5-init`)
///    re-export. A constant declared by a retained target module must, in
///    `proof_full`, also appear in `expected_cone`. Every `expected_cone`
///    constant must have one of these two origins. Any other `proof_full`
///    constant is proof-origin and may not use a kernel-accelerated name, a
///    reserved kernel/sysroot root, or the `Trusted` root (except generated
///    equation/splitter helpers of a pinned parent).
/// 5. Verify `expected_declaration` is a closed `Prop` definition from the
///    `Expected` module whose body is `canonical_root (ctor subject
///    specification)`, where `canonical_root` is a `CANONICAL_ROOTS` entry
///    and `ctor` is its crate constructor (`Crate.mk`, or `CrateV2.mk` for
///    Profile v2 roots), with each canonical input declared by its required
///    role.
/// 6. Apply the direct and transitive specification bans to every
///    `Specification` constant (each, except paired `_unsafe_rec`
///    auxiliaries, must appear in `expected_cone`).
/// 7. Verify `theorem_name` is a proof-origin, universe-monomorphic
///    `.thmInfo` whose type is `expected_declaration` or its canonical body.
/// 8. Scan both exports so that `.opaqueInfo` appears only for non-unsafe,
///    content-pinned sysroot constants (such as `System.Platform.getNumBits`),
///    no `unsafe` or `partial` declaration appears, and axioms stay in the
///    closed allowlist (`sorryAx` only on proof-only declarations when
///    `allow_sorry_in_proof` is set).
pub fn verify_ndjson_structure(
    arena: &mut CanonicalArena,
    init_primitives: &ExportedEnv,
    sysroot_pins: &ExportedEnv,
    expected_cone: &ExportedEnv,
    proof_full: &ExportedEnv,
    req: &StructuralCompareRequest<'_>,
) -> Result<StructuralCompareSummary, Failure> {
    let phase = "ndjson-comparator";

    // 1. Cross-check NDJSON header metadata across all exports so mixed
    // exporter or Lean toolchain runs fail closed before comparing graphs,
    // and require each export to be closed, ordered, and well grouped.
    for (label, env) in [
        ("sysroot_pins", sysroot_pins),
        ("expected_cone", expected_cone),
        ("proof_full", proof_full),
    ] {
        if env.meta != init_primitives.meta {
            return Err(Failure::operational(
                phase,
                format!("{label} NDJSON metadata differs from init_primitives_cone"),
            ));
        }
    }
    check_export_well_formed(arena, init_primitives, "init_primitives_cone", true)?;
    check_export_well_formed(arena, sysroot_pins, "sysroot_pins", true)?;
    check_export_well_formed(arena, expected_cone, "expected_cone", false)?;
    check_export_well_formed(arena, proof_full, "proof_full", false)?;

    // 2. Confirm the clean sysroot primitive cone pins all 39 required
    // primitives, the 3 standard foundation axioms, and `System.Platform`
    // (`getNumBits` is an `Init` `opaque`).
    for prim in PINNED_INIT_PRIMITIVES {
        let id = arena.intern_dotted_name(prim);
        if !init_primitives.constants.contains_key(&id) {
            return Err(Failure::operational(
                phase,
                format!("init_primitives_cone is missing required primitive `{prim}`"),
            ));
        }
    }
    for ax in STANDARD_PERMITTED_AXIOMS {
        let id = arena.intern_dotted_name(ax);
        match init_primitives.constants.get(&id) {
            Some(CanonConstInfo::Axiom { is_unsafe: false, .. }) => {}
            Some(other) => {
                return Err(Failure::operational(
                    phase,
                    format!(
                        "init_primitives_cone has unexpected kind `{}` for standard axiom `{ax}`",
                        other.kind_label()
                    ),
                ));
            }
            None => {
                return Err(Failure::operational(
                    phase,
                    format!("init_primitives_cone is missing standard axiom `{ax}`"),
                ));
            }
        }
    }
    for decl in PINNED_SYSTEM_PLATFORM_DECLS {
        let id = arena.intern_dotted_name(decl);
        if !init_primitives.constants.contains_key(&id) {
            return Err(Failure::operational(
                phase,
                format!("init_primitives_cone is missing System.Platform decl `{decl}`"),
            ));
        }
    }
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

    // 3. Every `expected_cone` constant also present in `proof_full` must be
    // DAG-identical there, and the cone of `expected_declaration` must appear
    // in `proof_full` in full.
    let expected_decl_id = arena.intern_dotted_name(req.expected_declaration);
    let expected_bfs = bfs_cone(arena, expected_cone, &[expected_decl_id], "expected_cone")?;
    for &name_id in &expected_bfs.visited {
        if !proof_full.constants.contains_key(&name_id) {
            return Err(Failure::policy(
                phase,
                format!(
                    "expected declaration `{}` missing from proof export",
                    arena.name_str(name_id)
                ),
            ));
        }
    }
    for &name_id in &expected_cone.const_order {
        if let Some(proof_ci) = proof_full.constants.get(&name_id)
            && &expected_cone.constants[&name_id] != proof_ci
        {
            return Err(Failure::policy(
                phase,
                format!(
                    "declaration `{}` differs between trusted expected export and proof export",
                    arena.name_str(name_id)
                ),
            ));
        }
    }

    // Statement-origin isolation on `expected_cone` (with `optParam` default
    // stripping): reject any constant belonging to a `Proof` / `Anneal`
    // namespace or any `TargetRole::Proof` module.
    let is_forbidden_expected_const = |arena: &CanonicalArena, cid: CanonNameId| -> bool {
        let root = arena.user_name_root(cid);
        if req.forbidden_expected_roots.contains(root) {
            return true;
        }
        let parts = arena.name_parts(cid);
        let user = CanonicalArena::user_parts(&parts);
        req.forbidden_expected_modules.iter().any(|m| {
            CanonicalArena::belongs_to_module_parts(&parts, m)
                || CanonicalArena::belongs_to_module_parts(user, m)
        })
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

    // 4. Authenticated origin of every constant. Sysroot status is never
    // granted by name alone: a sysroot-named constant must equal the clean
    // sysroot re-export (`5-pin`, plus the `5-init` primitives), so neither
    // export can shadow a sysroot name, including one a kernel evaluates
    // natively, with different content.
    let is_sysroot_id = |arena: &CanonicalArena, cid: CanonNameId| -> bool {
        req.sysroot_const_to_module.contains_key(&arena.encode_canon_name(cid))
    };
    let target_origin = |arena: &CanonicalArena, cid: CanonNameId| -> Option<&TargetConstOrigin> {
        req.target_const_origins.get(&arena.encode_canon_name(cid))
    };
    let is_sysroot_parts = |parts: &[NamePart<'_>]| -> bool {
        req.sysroot_const_to_module.contains_key(&CanonicalArena::encode_parts(parts))
    };
    let is_model_parts = |parts: &[NamePart<'_>]| -> bool {
        req.target_const_origins
            .get(&CanonicalArena::encode_parts(parts))
            .is_some_and(|o| o.role == TargetOriginRole::Model)
    };
    let mut sysroot_pinned = 0usize;
    for (label, env) in [("expected_cone", expected_cone), ("proof_full", proof_full)] {
        for &cid in &env.const_order {
            let ci = &env.constants[&cid];
            if let Some(pinned_ci) = init_primitives.constants.get(&cid)
                && ci != pinned_ci
            {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "pinned Init primitive `{}` in {label} differs from clean sysroot definition",
                        arena.name_str(cid)
                    ),
                ));
            }
            if let CanonConstInfo::Quot { kind, .. } = ci {
                match quot_ids.get(&cid) {
                    Some((_, expected_kind)) if expected_kind == kind => {}
                    _ => {
                        return Err(Failure::policy(
                            phase,
                            format!(
                                "unexpected quotient declaration `{}` in {label}",
                                arena.name_str(cid)
                            ),
                        ));
                    }
                }
            }
            if is_sysroot_id(arena, cid) {
                let pinned = sysroot_pins
                    .constants
                    .get(&cid)
                    .or_else(|| init_primitives.constants.get(&cid));
                match pinned {
                    Some(pinned_ci) if pinned_ci == ci => sysroot_pinned += 1,
                    Some(_) => {
                        return Err(Failure::policy(
                            phase,
                            format!(
                                "sysroot-named constant `{}` in {label} differs from clean sysroot definition",
                                arena.name_str(cid)
                            ),
                        ));
                    }
                    None => {
                        return Err(Failure::policy(
                            phase,
                            format!(
                                "sysroot-named constant `{}` in {label} is absent from the clean sysroot re-export",
                                arena.name_str(cid)
                            ),
                        ));
                    }
                }
                continue;
            }
            let origin = target_origin(arena, cid);
            if label == "expected_cone" && origin.is_none() {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "expected_cone constant `{}` has no authenticated sysroot or target-module origin",
                        arena.name_str(cid)
                    ),
                ));
            }
            if label == "proof_full" && origin.is_some() && !expected_cone.constants.contains_key(&cid)
            {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "proof export declares target-module constant `{}` absent from the trusted expected export",
                        arena.name_str(cid)
                    ),
                ));
            }
            let user_dotted = arena.user_dotted_string(cid);
            if KERNEL_ACCELERATED_NAMES.contains(&user_dotted.as_str()) {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "{label} declares reserved kernel-accelerated name `{}` outside sysroot",
                        arena.name_str(cid)
                    ),
                ));
            }
            let root = arena.user_name_root(cid);
            if RESERVED_KERNEL_ROOTS.contains(&root)
                && !arena.is_generated_eq_helper(cid, ci, &is_sysroot_parts)
            {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "{label} declares constant `{}` under reserved kernel/sysroot root `{root}`",
                        arena.name_str(cid)
                    ),
                ));
            }
            if root == "Trusted"
                && !origin.is_some_and(|o| o.role == TargetOriginRole::Model)
                && !arena.is_generated_eq_helper(cid, ci, &is_model_parts)
            {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "{label} declares constant `{}` in reserved Trusted namespace outside model modules",
                        arena.name_str(cid)
                    ),
                ));
            }
        }
    }

    // Compiled declaration edges must respect target-role authority (the
    // second of `TargetRole::allows`'s two enforcement points; imports were
    // checked before elaboration), and sysroot constants, already pinned to
    // the clean re-export, may never reference target-module constants.
    // Both exports are walked, so a sysroot-named constant present only in
    // `proof_full` is checked too.
    for cone in [expected_cone, proof_full] {
        for &cid in &cone.const_order {
            let src = target_origin(arena, cid);
            let src_is_sysroot = src.is_none() && is_sysroot_id(arena, cid);
            for dep in arena.collect_const_deps(&cone.constants[&cid], false) {
                let Some(dst) = target_origin(arena, dep) else {
                    continue;
                };
                let allowed = match src {
                    Some(src) => src.role.allows(dst.role),
                    None => !src_is_sysroot,
                };
                if !allowed {
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "target authority violation: `{}` references `{}`",
                            arena.name_str(cid),
                            arena.name_str(dep)
                        ),
                    ));
                }
            }
        }
    }

    // 5. Verify `expected_declaration` shape, exact canonical root body, and
    // the defining role of every canonical input.
    let expected_ci = expected_cone.constants.get(&expected_decl_id).ok_or_else(|| {
        Failure::policy(
            phase,
            format!("expected declaration `{}` missing from expected_cone", req.expected_declaration),
        )
    })?;
    let Some(crate_mk_name) = canonical_crate_ctor(req.canonical_root) else {
        return Err(Failure::policy(
            phase,
            format!("unexpected canonical root `{}`", req.canonical_root),
        ));
    };
    for (name, required_role, required_module) in [
        (req.expected_declaration, TargetOriginRole::Expected, Some(req.expected_module)),
        (req.canonical_root, TargetOriginRole::Model, None),
        (crate_mk_name, TargetOriginRole::Model, None),
        (req.subject_declaration, TargetOriginRole::Capture, None),
        (req.specification_declaration, TargetOriginRole::Specification, None),
    ] {
        let cid = arena.intern_dotted_name(name);
        let origin_ok = target_origin(arena, cid).is_some_and(|o| {
            o.role == required_role && required_module.is_none_or(|m| o.module == m)
        });
        if !origin_ok {
            return Err(Failure::policy(phase, format!("incorrect canonical input origin `{name}`")));
        }
        match expected_cone.constants.get(&cid) {
            Some(ci) if ci.level_params().is_empty() => {}
            Some(_) => {
                return Err(Failure::policy(
                    phase,
                    format!("canonical input `{name}` has universe parameters"),
                ));
            }
            None => {
                return Err(Failure::policy(
                    phase,
                    format!("canonical input `{name}` missing from expected_cone"),
                ));
            }
        }
    }
    let prop_sort = arena.intern_expr(CanonExpr::Sort(arena.zero_level));
    let canonical_expr = arena.build_canonical_claim_expr(
        req.canonical_root,
        crate_mk_name,
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

    // 6. Specification restrictions over every constant the `Specification`
    // modules declare (including compiler-generated instances, constructors,
    // projections, matchers, and `where`/`let rec` auxiliaries), matching
    // `TrustedBoundary.lean`'s Phase 1 direct and transitive bans.
    let spec_id = arena.intern_dotted_name(req.specification_declaration);
    let mut spec_roots_set: BTreeSet<CanonNameId> = BTreeSet::from([spec_id]);
    let mut spec_encoded: Vec<&str> = req
        .target_const_origins
        .iter()
        .filter(|(_, o)| o.role == TargetOriginRole::Specification && !o.paired_unsafe_rec)
        .map(|(enc, _)| enc.as_str())
        .collect();
    spec_encoded.sort_unstable();
    for enc in spec_encoded {
        let cid = arena.intern_encoded_name(enc);
        if !expected_cone.constants.contains_key(&cid) {
            return Err(Failure::policy(
                phase,
                format!(
                    "specification constant `{}` is absent from the trusted expected export",
                    arena.name_str(cid)
                ),
            ));
        }
        spec_roots_set.insert(cid);
    }
    for &cid in &spec_roots_set {
        let deps = arena.collect_const_deps(&expected_cone.constants[&cid], false);
        for dep in deps {
            if arena.is_lean_syntax_const(dep) || arena.is_panic_spec_const(dep) {
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
    let spec_roots_vec: Vec<CanonNameId> = spec_roots_set.iter().copied().collect();
    let spec_bfs = bfs_cone(arena, expected_cone, &spec_roots_vec, "expected_cone")?;
    for &cid in &spec_bfs.visited {
        if arena.is_forbidden_spec_transitive_const(cid) {
            let chain = format_blame_path(arena, &spec_bfs.parent, cid);
            return Err(Failure::policy(
                phase,
                format!(
                    "specification closure references forbidden constant `{}` (blame: {chain})",
                    arena.name_str(cid)
                ),
            ));
        }
    }

    // 7. Verify `theorem_name` is a proof-origin closed `.thmInfo` proving
    // `Expected.claim` (or its exact unfolded canonical root application).
    let theorem_id = arena.intern_dotted_name(req.theorem_name);
    if is_sysroot_id(arena, theorem_id) || target_origin(arena, theorem_id).is_some() {
        return Err(Failure::policy(
            phase,
            format!("target theorem `{}` is not declared by a proof module", req.theorem_name),
        ));
    }
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

    // 8. Scan every declaration of both exports so that:
    // - `.opaqueInfo` appears only for non-unsafe sysroot constants, which
    //   step 4 already pinned to the clean sysroot re-export (such as
    //   `System.Platform.getNumBits`); every other opaque is rejected,
    // - zero `unsafe` or `partial` declarations exist,
    // - every `.axiomInfo` is inside the closed allowlist, and
    // - any violation reports an exact shortest-path blame chain.
    let sorry_ax_id = arena.intern_dotted_name("sorryAx");
    let standard_axiom_ids: BTreeSet<CanonNameId> = STANDARD_PERMITTED_AXIOMS
        .iter()
        .map(|name| arena.intern_dotted_name(name))
        .collect();
    let expected_cone_set: BTreeSet<CanonNameId> =
        expected_cone.constants.keys().copied().collect();

    // First verify the entire `expected_cone` (claim + specification closure)
    // strictly under the 3-axiom ceiling (never permitting `sorryAx` in
    // specifications, model, capture, or expected).
    for &cid in &expected_cone.const_order {
        let ci = &expected_cone.constants[&cid];
        let parent_map = if expected_bfs.visited.contains(&cid) {
            &expected_bfs.parent
        } else {
            &spec_bfs.parent
        };
        if let CanonConstInfo::Opaque { is_unsafe, .. } = ci
            && (*is_unsafe || !is_sysroot_id(arena, cid))
        {
            let chain = format_blame_path(arena, parent_map, cid);
            return Err(Failure::policy(
                phase,
                format!(
                    "opaque declaration `{}` forbidden in expected cone (blame: {chain})",
                    arena.name_str(cid)
                ),
            ));
        }
        if ci.is_unsafe_or_partial() {
            let chain = format_blame_path(arena, parent_map, cid);
            return Err(Failure::policy(
                phase,
                format!(
                    "unsafe or partial declaration `{}` forbidden in expected cone (blame: {chain})",
                    arena.name_str(cid)
                ),
            ));
        }
        if matches!(ci, CanonConstInfo::Axiom { .. }) && !standard_axiom_ids.contains(&cid) {
            let chain = format_blame_path(arena, parent_map, cid);
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
    let proof_bfs = bfs_cone(arena, proof_full, &[theorem_id, expected_decl_id], "proof_full")?;
    let mut axioms = BTreeSet::new();
    let mut sorry_declarations = BTreeSet::new();

    // Check every constant present anywhere in `proof_full` (not only BFS-
    // reached ones) so a compromised `5b` cannot smuggle an unreached `.opaque`
    // or illegal axiom past structural checks.
    for &cid in &proof_full.const_order {
        let ci = &proof_full.constants[&cid];
        if let CanonConstInfo::Opaque { is_unsafe, .. } = ci
            && (*is_unsafe || !is_sysroot_id(arena, cid))
        {
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
                if !req.allow_sorry_in_proof
                    || expected_cone_set.contains(&cid)
                    || req.sysroot_const_to_module.contains_key(&arena.encode_canon_name(cid))
                {
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

    // Compiler replacement attributes do not affect kernel reduction, but, as
    // in `TrustedBoundary.lean`'s `"target-audit"`, no reached declaration
    // authored by a retained non-`Proof` target module may carry one.
    for reached in [&expected_bfs.visited, &spec_bfs.visited, &proof_bfs.visited] {
        for &cid in reached {
            if req.target_compiler_overrides.contains(&arena.encode_canon_name(cid)) {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "compiler override on reached target declaration `{}`",
                        arena.name_str(cid)
                    ),
                ));
            }
        }
    }

    // Build closure inventories for Receipt v3 `moduleIdentities` provenance
    // from the exact target-module index and sysroot inventory. As in
    // `TrustedBoundary.lean`'s `"target-audit"`, the model and specification
    // closures start from that role's declarations reached by the expected
    // claim, and the subject closure from the subject declaration.
    let reached_roots = |role: TargetOriginRole| -> Vec<CanonNameId> {
        expected_bfs
            .visited
            .iter()
            .copied()
            .filter(|&cid| {
                req.target_const_origins
                    .get(&arena.encode_canon_name(cid))
                    .is_some_and(|o| o.role == role)
            })
            .collect()
    };
    let model_roots = reached_roots(TargetOriginRole::Model);
    let spec_report_roots = reached_roots(TargetOriginRole::Specification);
    let subject_id = arena.intern_dotted_name(req.subject_declaration);
    let subject_bfs = bfs_cone(arena, expected_cone, &[subject_id], "expected_cone")?;
    let model_bfs = bfs_cone(arena, expected_cone, &model_roots, "expected_cone")?;
    let spec_report_bfs = bfs_cone(arena, expected_cone, &spec_report_roots, "expected_cone")?;
    let subject_closure =
        build_closure_entries(arena, &subject_bfs.visited, "subjectClosure", req)?;
    let model_closure = build_closure_entries(arena, &model_bfs.visited, "modelClosure", req)?;
    let specification_closure =
        build_closure_entries(arena, &spec_report_bfs.visited, "specificationClosure", req)?;

    Ok(StructuralCompareSummary {
        axioms: axioms.into_iter().collect(),
        sorry_declarations: sorry_declarations.into_iter().collect(),
        sorry_used,
        checked_declarations: proof_full.const_order.len(),
        expected_cone_declarations: expected_cone.const_order.len(),
        sysroot_pinned_declarations: sysroot_pinned,
        subject_closure,
        model_closure,
        specification_closure,
    })
}

struct BfsResult {
    visited: BTreeSet<CanonNameId>,
    parent: HashMap<CanonNameId, CanonNameId>,
}

/// Breadth-first dependency cone of `roots` within `env`, failing closed if
/// a root or any reached required dependency is absent from `env`.
fn bfs_cone(
    arena: &CanonicalArena,
    env: &ExportedEnv,
    roots: &[CanonNameId],
    label: &str,
) -> Result<BfsResult, Failure> {
    let mut visited = BTreeSet::new();
    let mut parent = HashMap::new();
    let mut queue = VecDeque::new();
    for &root in roots {
        if !env.constants.contains_key(&root) {
            return Err(Failure::policy(
                "ndjson-comparator",
                format!("root `{}` is missing from {label}", arena.name_str(root)),
            ));
        }
        if visited.insert(root) {
            queue.push_back(root);
        }
    }
    while let Some(curr) = queue.pop_front() {
        let ci = &env.constants[&curr];
        let required = arena.collect_required_deps(ci);
        for dep in arena.collect_const_deps(ci, false) {
            if !env.constants.contains_key(&dep) {
                // Names-only mutual-block peers may be absent; see
                // `collect_required_deps`.
                if !required.contains(&dep) {
                    continue;
                }
                return Err(Failure::policy(
                    "ndjson-comparator",
                    format!(
                        "dependency `{}` of `{}` is missing from {label}",
                        arena.name_str(dep),
                        arena.name_str(curr)
                    ),
                ));
            }
            if visited.insert(dep) {
                parent.insert(dep, curr);
                queue.push_back(dep);
            }
        }
    }
    Ok(BfsResult { visited, parent })
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

/// Attribute every constant of `visited` to its exact defining module (a
/// retained non-`Proof` target module or a sysroot module), failing closed on
/// any constant without a known origin (already rejected for every
/// `expected_cone` constant; rechecked here as defense in depth).
///
/// Mirrors `TrustedBoundary.lean`'s `"target-audit"` closures, which report
/// each reached declaration with its `originOf` module and nothing else, so
/// `moduleIdentities` binds exactly the modules determining the closure and
/// `verify` derives `candidate:*` features only from reached `Model` modules.
fn build_closure_entries(
    arena: &CanonicalArena,
    visited: &BTreeSet<CanonNameId>,
    label: &str,
    req: &StructuralCompareRequest<'_>,
) -> Result<Vec<ClosureEntry>, Failure> {
    let mut entries: Vec<ClosureEntry> = Vec::with_capacity(visited.len());
    for &cid in visited {
        let name = arena.name_str(cid);
        let encoded = arena.encode_canon_name(cid);
        let module = if let Some(origin) = req.target_const_origins.get(&encoded) {
            origin.module.clone()
        } else if let Some(sys_mod) = req.sysroot_const_to_module.get(&encoded) {
            sys_mod.clone()
        } else {
            return Err(Failure::policy(
                "ndjson-comparator",
                format!("missing origin for `{name}` in {label}"),
            ));
        };
        entries.push(ClosureEntry { name: name.to_owned(), module });
    }
    entries.sort_by(|a, b| a.name.cmp(&b.name).then_with(|| a.module.cmp(&b.module)));
    entries.dedup();
    Ok(entries)
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
        for ax in STANDARD_PERMITTED_AXIOMS {
            let nid = ensure_name(&mut init_lines, ax);
            init_lines.push(format!(
                r#"{{"axiom":{{"isUnsafe":false,"levelParams":[],"name":{nid},"type":0}}}}"#
            ));
        }
        for decl in PINNED_SYSTEM_PLATFORM_DECLS {
            let nid = ensure_name(&mut init_lines, decl);
            if decl == "System.Platform.getNumBits" {
                init_lines.push(format!(
                    r#"{{"opaque":{{"all":[{nid}],"isUnsafe":false,"levelParams":[],"name":{nid},"type":1,"value":0}}}}"#
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

    fn default_sysroot_map() -> HashMap<String, String> {
        let mut map = HashMap::new();
        for prim in PINNED_INIT_PRIMITIVES {
            map.insert((*prim).to_owned(), "Init.Prelude".to_owned());
        }
        for ax in STANDARD_PERMITTED_AXIOMS {
            map.insert((*ax).to_owned(), "Init.Core".to_owned());
        }
        for decl in PINNED_SYSTEM_PLATFORM_DECLS {
            map.insert((*decl).to_owned(), "Init.Prelude".to_owned());
        }
        map
    }

    static NO_OVERRIDES: BTreeSet<String> = BTreeSet::new();

    fn origin(module: &str, role: TargetOriginRole) -> TargetConstOrigin {
        TargetConstOrigin { module: module.to_owned(), role, paired_unsafe_rec: false }
    }

    fn default_origins() -> HashMap<String, TargetConstOrigin> {
        HashMap::from([
            (
                "Trusted.MirSemantics.UnitTheorem".to_owned(),
                origin("Trusted.MirSemantics", TargetOriginRole::Model),
            ),
            (
                "Trusted.MirSemantics.Crate.mk".to_owned(),
                origin("Trusted.MirSemantics", TargetOriginRole::Model),
            ),
            ("Captured.program".to_owned(), origin("Captured", TargetOriginRole::Capture)),
            ("Spec.specs".to_owned(), origin("Spec", TargetOriginRole::Specification)),
            ("Expected.claim".to_owned(), origin("Expected", TargetOriginRole::Expected)),
        ])
    }

    fn default_req<'a>(
        allow_sorry: bool,
        sysroot_const_to_module: &'a HashMap<String, String>,
        target_const_origins: &'a HashMap<String, TargetConstOrigin>,
    ) -> StructuralCompareRequest<'a> {
        StructuralCompareRequest {
            theorem_name: "Proof.verify",
            expected_module: "Expected",
            expected_declaration: "Expected.claim",
            canonical_root: "Trusted.MirSemantics.UnitTheorem",
            subject_declaration: "Captured.program",
            specification_declaration: "Spec.specs",
            allow_sorry_in_proof: allow_sorry,
            forbidden_expected_roots: BTreeSet::from(["Anneal".to_owned(), "Proof".to_owned()]),
            forbidden_expected_modules: BTreeSet::from(["Proof".to_owned()]),
            sysroot_const_to_module,
            target_const_origins,
            target_compiler_overrides: &NO_OVERRIDES,
        }
    }

    fn run_compare(
        init_s: &str,
        expected_s: &str,
        proof_s: &str,
        allow_sorry: bool,
    ) -> Result<StructuralCompareSummary, Failure> {
        let sysroot = default_sysroot_map();
        let origins = default_origins();
        let req = default_req(allow_sorry, &sysroot, &origins);
        run_compare_with(init_s, expected_s, proof_s, &req)
    }

    /// Compare with the clean `init_s` export doubling as `sysroot_pins`.
    fn run_compare_with(
        init_s: &str,
        expected_s: &str,
        proof_s: &str,
        req: &StructuralCompareRequest<'_>,
    ) -> Result<StructuralCompareSummary, Failure> {
        run_compare_pinned(init_s, init_s, expected_s, proof_s, req)
    }

    fn run_compare_pinned(
        init_s: &str,
        pins_s: &str,
        expected_s: &str,
        proof_s: &str,
        req: &StructuralCompareRequest<'_>,
    ) -> Result<StructuralCompareSummary, Failure> {
        let mut arena = CanonicalArena::new();
        let init_env = parse_ndjson_reader(BufReader::new(init_s.as_bytes()), &mut arena, "init")?;
        let pins_env = parse_ndjson_reader(BufReader::new(pins_s.as_bytes()), &mut arena, "pins")?;
        let expected_env =
            parse_ndjson_reader(BufReader::new(expected_s.as_bytes()), &mut arena, "expected")?;
        let proof_env =
            parse_ndjson_reader(BufReader::new(proof_s.as_bytes()), &mut arena, "proof")?;
        verify_ndjson_structure(&mut arena, &init_env, &pins_env, &expected_env, &proof_env, req)
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
    fn reports_only_reached_declarations_in_role_closures() {
        let (init_s, expected_s, proof_s) = synthetic_ndjson_fixture();
        let sysroot = default_sysroot_map();
        // A retained model module that the claim never reaches.
        let mut origins = default_origins();
        origins.insert(
            "Trusted.Unreached.helper".to_owned(),
            origin("Trusted.Unreached", TargetOriginRole::Model),
        );
        let req = default_req(false, &sysroot, &origins);
        let summary = run_compare_with(&init_s, &expected_s, &proof_s, &req).unwrap();
        let modules = |closure: &[ClosureEntry]| -> BTreeSet<String> {
            closure.iter().map(|e| e.module.clone()).collect()
        };
        let names = |closure: &[ClosureEntry]| -> BTreeSet<String> {
            closure.iter().map(|e| e.name.clone()).collect()
        };
        for closure in
            [&summary.subject_closure, &summary.model_closure, &summary.specification_closure]
        {
            assert!(!modules(closure).contains("Trusted.Unreached"), "{closure:?}");
            assert!(closure.iter().all(|e| e.name != e.module), "{closure:?}");
        }
        assert!(names(&summary.model_closure).contains("Trusted.MirSemantics.UnitTheorem"));
        assert!(
            modules(&summary.model_closure)
                .iter()
                .all(|m| m != "Captured" && m != "Spec" && m != "Expected")
        );
        assert!(names(&summary.subject_closure).contains("Captured.program"));
        assert!(names(&summary.specification_closure).contains("Spec.specs"));

        // A reached declaration without a known origin fails closed before any
        // closure is reported.
        let mut no_origin = default_origins();
        no_origin.remove("Captured.program");
        let req = default_req(false, &sysroot, &no_origin);
        let err = run_compare_with(&init_s, &expected_s, &proof_s, &req).unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert!(
            err.message.contains("`Captured.program` has no authenticated sysroot or target"),
            "{err}"
        );
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
    fn inspect_schema_pins_the_primitive_count() {
        assert_eq!(
            crate::core::inspect::schema::NDJSON_PINNED_PRIMITIVE_COUNT,
            PINNED_INIT_PRIMITIVES.len() as u64
        );
    }

    #[test]
    fn rejects_empty_lines_in_exports() {
        let (init_s, expected_s, proof_s) = synthetic_ndjson_fixture();
        let blank = proof_s.replacen('\n', "\n\n", 1);
        let err = run_compare(&init_s, &expected_s, &blank, false).unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert!(err.message.contains("proof:2: empty NDJSON line"), "{err}");
    }

    #[test]
    fn rejects_forward_and_cyclic_references_in_exports() {
        let (init_s, expected_s, proof_s) = synthetic_ndjson_fixture();
        let names = r#"{"in":230,"str":{"pre":111,"str":"A"}}
{"in":231,"str":{"pre":111,"str":"B"}}
{"ie":230,"const":{"name":231,"us":[]}}
{"ie":231,"const":{"name":230,"us":[]}}
"#;
        let def = |name: u32, value: u32| {
            format!(
                r#"{{"def":{{"all":[{name}],"hints":"abbrev","levelParams":[],"name":{name},"safety":"safe","type":100,"value":{value}}}}}"#
            )
        };
        // `Proof.B` before `Proof.A := Proof.B` is in dependency order.
        let ordered = format!("{proof_s}{names}{}\n{}\n", def(231, 100), def(230, 230));
        run_compare(&init_s, &expected_s, &ordered, false).unwrap();
        // `Proof.A := Proof.B` before `Proof.B` is a forward reference.
        let forward = format!("{proof_s}{names}{}\n{}\n", def(230, 230), def(231, 100));
        // `Proof.A := Proof.B` and `Proof.B := Proof.A` form a cycle.
        let cyclic = format!("{proof_s}{names}{}\n{}\n", def(230, 230), def(231, 231));
        for export in [forward, cyclic] {
            let err = run_compare(&init_s, &expected_s, &export, false).unwrap_err();
            assert_eq!(err.code, 1, "{err}");
            assert!(
                err.message.contains("proof_full is not in dependency order")
                    && err.message.contains("`Proof.A` refers to `Proof.B`"),
                "{err}"
            );
        }
        // `Proof.A := Proof.A` and `Proof.verify := Proof.verify` refer to
        // themselves.
        let self_def = format!("{proof_s}{names}{}\n", def(230, 231));
        let self_thm = proof_s.replace(
            r#"{"thm":{"all":[112],"levelParams":[],"name":112,"type":108,"value":100}}"#,
            "{\"ie\":232,\"const\":{\"name\":112,\"us\":[]}}\n\
             {\"thm\":{\"all\":[112],\"levelParams\":[],\"name\":112,\"type\":108,\"value\":232}}",
        );
        assert_ne!(self_thm, proof_s);
        for (export, culprit) in [(self_def, "Proof.A"), (self_thm, "Proof.verify")] {
            let err = run_compare(&init_s, &expected_s, &export, false).unwrap_err();
            assert_eq!(err.code, 1, "{err}");
            assert!(err.message.contains(&format!("`{culprit}` refers to itself")), "{err}");
        }
        // The trusted export is held to the same order: move `Expected.claim`
        // ahead of the declarations its value uses.
        let lines: Vec<&str> = expected_s.lines().collect();
        let (claim, rest) = lines.split_last().unwrap();
        let split = rest.iter().position(|l| l.starts_with(r#"{"def""#)).unwrap();
        let reordered = [&rest[..split], &[*claim], &rest[split..]].concat().join("\n") + "\n";
        let err = run_compare(&init_s, &reordered, &proof_s, false).unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert!(err.message.contains("expected_cone is not in dependency order"), "{err}");
    }

    #[test]
    fn checks_inductive_record_consistency() {
        let (init_s, expected_s, proof_s) = synthetic_ndjson_fixture();
        // `Proof.T` with constructor `Proof.T.mk` and recursor `Proof.T.rec`.
        let names = r#"{"in":240,"str":{"pre":111,"str":"T"}}
{"in":241,"str":{"pre":240,"str":"mk"}}
{"in":242,"str":{"pre":240,"str":"rec"}}
{"in":243,"str":{"pre":111,"str":"U"}}
{"ie":240,"const":{"name":240,"us":[]}}
"#;
        let record = |all: &str, ty_ctors: &str, ctors: &str, cidx: u32, recs: &str| {
            format!(
                r#"{names}{{"inductive":{{"types":[{{"name":240,"levelParams":[],"type":100,"numParams":0,"numIndices":0,"all":{all},"ctors":{ty_ctors},"numNested":0,"isRec":false,"isUnsafe":false,"isReflexive":false}}],"ctors":{ctors},"recs":{recs}}}}}"#
            )
            .replace("CIDX", &cidx.to_string())
        };
        let ctor = r#"[{"name":241,"levelParams":[],"type":240,"induct":240,"cidx":CIDX,"numParams":0,"numFields":0,"isUnsafe":false}]"#;
        let rec = |all: &str, rule_ctor: u32| {
            format!(
                r#"[{{"name":242,"levelParams":[],"type":100,"all":{all},"numParams":0,"numIndices":0,"numMotives":1,"numMinors":1,"rules":[{{"ctor":{rule_ctor},"nfields":0,"rhs":100}}],"k":false,"isUnsafe":false}}]"#
            )
        };
        let good = record("[240]", "[241]", ctor, 0, &rec("[240]", 241));
        run_compare(&init_s, &expected_s, &format!("{proof_s}{good}\n"), false).unwrap();
        let cases = [
            // A constructor its type does not list (an orphan).
            (
                record("[240]", "[]", ctor, 0, &rec("[240]", 241)),
                "not exactly its types' constructors",
            ),
            // A constructor at the wrong index.
            (record("[240]", "[241]", ctor, 1, &rec("[240]", 241)), "does not match its position"),
            // A type whose mutual block is not the record's.
            (
                record("[240,243]", "[241]", ctor, 0, &rec("[240]", 241)),
                "mutual types of `Proof.T`",
            ),
            // A recursor of another block (an orphan).
            (
                record("[240]", "[241]", ctor, 0, &rec("[243]", 241)),
                "types of recursor `Proof.T.rec`",
            ),
            // A recursor rule for a foreign constructor.
            (record("[240]", "[241]", ctor, 0, &rec("[240]", 112)), "rule for `Proof.verify`"),
            // No recursor.
            (record("[240]", "[241]", ctor, 0, "[]"), "has no recursor"),
            // A nested block's recursor rule for a non-constructor.
            (
                record("[240]", "[241]", ctor, 0, &rec("[240]", 112))
                    .replace(r#""numNested":0"#, r#""numNested":1"#),
                "rule for `Proof.verify`",
            ),
        ];
        for (bad, needle) in cases {
            let err =
                run_compare(&init_s, &expected_s, &format!("{proof_s}{bad}\n"), false).unwrap_err();
            assert_eq!(err.code, 1, "{needle}: {err}");
            assert!(
                err.message.contains("proof_full has a malformed inductive record")
                    && err.message.contains(needle),
                "{needle}: {err}"
            );
        }
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

        // 3. Forged standard axiom (`Classical.choice` with `Sort 1` instead
        // of sysroot `Sort 0`) must fail closed against Step 4 pinning.
        let mut forged_choice = proof_s.clone();
        forged_choice.push_str(
            r#"{"il":101,"succ":0}
{"ie":109,"sort":101}
{"in":235,"str":{"pre":0,"str":"Classical"}}
{"in":236,"str":{"pre":235,"str":"choice"}}
{"axiom":{"isUnsafe":false,"levelParams":[],"name":236,"type":109}}
"#,
        );
        let err = run_compare(&init_s, &expected_s, &forged_choice, false).unwrap_err();
        assert_eq!(err.code, 1);
        assert!(
            err.message.contains("Classical.choice")
                && err.message.contains("differs from clean sysroot"),
            "{err}"
        );
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
            "graph": {"Spec": []},
            "expected": "Expected.claim",
            "axioms": [],
            "sorryDeclarations": [],
            "replay": true,
            "exactType": true,
            "replayedDeclarations": 6,
            "expectedConeDeclarations": 5,
            "pinnedPrimitivesCount": 39,
            "sysrootPinnedDeclarations": 0,
            "expectedConeSha256": "0".repeat(64),
            "proofNdjsonSha256": "0".repeat(64),
            "initPrimitivesSha256": "0".repeat(64),
            "sysrootPinsSha256": "0".repeat(64),
            "leanexportSha256": "0".repeat(64),
            "nanodaBinSha256": "0".repeat(64),
            "conRonSha256": "0".repeat(64),
            "kernelsPassed": ["nanoda_bin", "con-ron"],
            "paranoidQuorum": false,
            "timingMs": {
                "initPrimitives": 0,
                "targetConsts": 10,
                "sysrootPins": 10,
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
        let mut accepted = raw.clone();
        accepted.as_object_mut().unwrap().remove("injectedUnknownField");
        serde_json::from_value::<NdjsonAuditVerdict>(accepted)
            .expect("the same verdict without the injected field must parse");
        let parsed: Result<NdjsonAuditVerdict, _> = serde_json::from_value(raw);
        assert!(parsed.is_err(), "deny_unknown_fields must reject extra fields");
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
        let mut sysroot_with_panic = default_sysroot_map();
        sysroot_with_panic.insert("panicCore".to_owned(), "Init.Prelude".to_owned());
        let origins = default_origins();
        let req_panic = default_req(false, &sysroot_with_panic, &origins);
        let err = run_compare_pinned(
            &init_s,
            &inject_panic_expected,
            &inject_panic_expected,
            &inject_panic_proof,
            &req_panic,
        )
        .unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("cannot reference"), "{err}");

        // 2. Forbidden proof module wrapped under `_private.<mod>.<idx>.*` in
        // `expected_cone` must still be caught by `forbidden_expected_modules`.
        let priv_expected = format!(
            "{expected_s}{}",
            r#"{"in":91,"str":{"pre":0,"str":"_private"}}
{"in":92,"str":{"pre":91,"str":"Proof"}}
{"in":93,"num":{"pre":92,"i":0}}
{"in":94,"str":{"pre":93,"str":"Proof"}}
{"in":95,"str":{"pre":94,"str":"helper"}}
{"def":{"all":[95],"hints":"abbrev","levelParams":[],"name":95,"safety":"safe","type":10,"value":10}}
"#
        );
        let priv_proof = format!(
            "{proof_s}{}",
            r#"{"in":191,"str":{"pre":0,"str":"_private"}}
{"in":192,"str":{"pre":191,"str":"Proof"}}
{"in":193,"num":{"pre":192,"i":0}}
{"in":194,"str":{"pre":193,"str":"Proof"}}
{"in":195,"str":{"pre":194,"str":"helper"}}
{"def":{"all":[195],"hints":"abbrev","levelParams":[],"name":195,"safety":"safe","type":100,"value":100}}
"#
        );
        let err = run_compare(&init_s, &priv_expected, &priv_proof, false).unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("forbidden proof-origin constant"), "{err}");

        // 2b. `private def Anneal.foo` inside `Spec.lean` compiles as
        // `_private.Spec.0.Anneal.foo`, which is NOT in
        // `forbidden_expected_modules` and must be caught after stripping
        // `_private.<mod>.<idx>` via `forbidden_expected_roots`.
        let priv_spec_anneal_expected = format!(
            "{expected_s}{}",
            r#"{"in":91,"str":{"pre":0,"str":"_private"}}
{"in":92,"str":{"pre":91,"str":"Spec"}}
{"in":93,"num":{"pre":92,"i":0}}
{"in":94,"str":{"pre":93,"str":"Anneal"}}
{"in":95,"str":{"pre":94,"str":"foo"}}
{"def":{"all":[95],"hints":"abbrev","levelParams":[],"name":95,"safety":"safe","type":10,"value":10}}
"#
        );
        let err = run_compare(&init_s, &priv_spec_anneal_expected, &proof_s, false).unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("forbidden proof-origin constant"), "{err}");

        // 3. Pure-signature `#4176` transitive specification bans
        // (`Init.System`, `Std.Internal.UV`, `Lean.LoadDynlib`,
        // `lean_dbg_trace`, `includeStr`, and non-Platform `System.*`) must
        // fail closed via `Spec.specs` cone even when present in
        // `sysroot_const_to_module`.
        let mut sysroot_with_banned = default_sysroot_map();
        for (tag, _, _) in [
            ("Init.System.IO", "", 0usize),
            ("Std.Internal.UV.Loop", "", 0),
            ("Lean.LoadDynlib", "", 0),
            ("lean_dbg_trace", "", 0),
            ("includeStr", "", 0),
            ("System.IO", "", 0),
        ] {
            sysroot_with_banned.insert(tag.to_owned(), "Init.Util".to_owned());
        }
        let req_with_banned = default_req(false, &sysroot_with_banned, &origins);
        for (tag, mod_prefix, leaf) in [
            ("Init.System.IO", r#"{"in":96,"str":{"pre":0,"str":"Init"}}
{"in":97,"str":{"pre":96,"str":"System"}}
{"in":98,"str":{"pre":97,"str":"IO"}}"#, 98),
            ("Std.Internal.UV.Loop", r#"{"in":96,"str":{"pre":0,"str":"Std"}}
{"in":97,"str":{"pre":96,"str":"Internal"}}
{"in":98,"str":{"pre":97,"str":"UV"}}
{"in":99,"str":{"pre":98,"str":"Loop"}}"#, 99),
            ("Lean.LoadDynlib", r#"{"in":96,"str":{"pre":0,"str":"Lean"}}
{"in":97,"str":{"pre":96,"str":"LoadDynlib"}}"#, 97),
            ("lean_dbg_trace", r#"{"in":96,"str":{"pre":0,"str":"lean_dbg_trace"}}"#, 96),
            ("includeStr", r#"{"in":96,"str":{"pre":0,"str":"includeStr"}}"#, 96),
            ("System.IO", r#"{"in":96,"str":{"pre":0,"str":"System"}}
{"in":97,"str":{"pre":96,"str":"IO"}}"#, 97),
        ] {
            let exp_bad = expected_s.replace(
                r#"{"def":{"all":[18],"hints":"abbrev","levelParams":[],"name":18,"safety":"safe","type":10,"value":10}}"#,
                &format!(
                    "{mod_prefix}\n{{\"ie\":{leaf},\"const\":{{\"name\":{leaf},\"us\":[]}}}}\n\
                     {{\"def\":{{\"all\":[{leaf}],\"hints\":\"abbrev\",\"levelParams\":[],\"name\":{leaf},\"safety\":\"safe\",\"type\":10,\"value\":10}}}}\n\
                     {{\"def\":{{\"all\":[18],\"hints\":\"abbrev\",\"levelParams\":[],\"name\":18,\"safety\":\"safe\",\"type\":10,\"value\":{leaf}}}}}"
                ),
            );
            let proof_bad = proof_s.replace(
                r#"{"def":{"all":[108],"hints":"abbrev","levelParams":[],"name":108,"safety":"safe","type":100,"value":100}}"#,
                &format!(
                    "{mod_prefix}\n{{\"ie\":{leaf},\"const\":{{\"name\":{leaf},\"us\":[]}}}}\n\
                     {{\"def\":{{\"all\":[{leaf}],\"hints\":\"abbrev\",\"levelParams\":[],\"name\":{leaf},\"safety\":\"safe\",\"type\":100,\"value\":100}}}}\n\
                     {{\"def\":{{\"all\":[108],\"hints\":\"abbrev\",\"levelParams\":[],\"name\":108,\"safety\":\"safe\",\"type\":100,\"value\":{leaf}}}}}"
                ),
            );
            let err = run_compare_pinned(&init_s, &exp_bad, &exp_bad, &proof_bad, &req_with_banned)
                .unwrap_err();
            assert_eq!(err.code, 1, "{tag}: {err}");
            assert!(err.message.contains("specification closure references forbidden constant"), "{tag}: {err}");
        }
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
        let sysroot = default_sysroot_map();
        let mut origins = default_origins();
        origins.remove("Spec.specs");
        origins.insert(
            "MyCrate.Spec.specs".to_owned(),
            origin("MyCrate.Spec", TargetOriginRole::Specification),
        );
        let pins_env = parse_ndjson_reader(BufReader::new(init_s.as_bytes()), &mut arena, "pins")
            .expect("pins");
        let req = StructuralCompareRequest {
            theorem_name: "MyCrate.Proof.verify",
            expected_module: "Expected",
            expected_declaration: "Expected.claim",
            canonical_root: "Trusted.MirSemantics.UnitTheorem",
            subject_declaration: "Captured.program",
            specification_declaration: "MyCrate.Spec.specs",
            allow_sorry_in_proof: false,
            forbidden_expected_roots: BTreeSet::from(["Anneal".to_owned(), "Proof".to_owned()]),
            forbidden_expected_modules: BTreeSet::from(["MyCrate.Proof".to_owned()]),
            sysroot_const_to_module: &sysroot,
            target_const_origins: &origins,
            target_compiler_overrides: &NO_OVERRIDES,
        };
        let summary =
            verify_ndjson_structure(&mut arena, &init_env, &pins_env, &expected_env, &proof_env, &req)
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
            graph: BTreeMap::from([
                ("Captured".to_owned(), vec![]),
                ("Spec".to_owned(), vec![]),
                ("Trusted.MirSemantics".to_owned(), vec![]),
            ]),
            expected: "Expected.claim".to_owned(),
            axioms: vec![],
            sorry_declarations: vec![],
            replay: true,
            exact_type: true,
            replayed_declarations: 6,
            expected_cone_declarations: 5,
            pinned_primitives_count: PINNED_INIT_PRIMITIVES.len(),
            sysroot_pinned_declarations: 0,
            expected_cone_sha256: "0".repeat(64),
            proof_ndjson_sha256: "0".repeat(64),
            init_primitives_sha256: "0".repeat(64),
            sysroot_pins_sha256: "0".repeat(64),
            leanexport_sha256: "0".repeat(64),
            nanoda_bin_sha256: "0".repeat(64),
            con_ron_sha256: "0".repeat(64),
            con_leche_sha256: None,
            lean4lean_sha256: None,
            kernels_passed: vec!["nanoda_bin".to_owned(), "con-ron".to_owned()],
            kernels_skipped: vec![],
            paranoid_quorum: false,
            timing_ms: NdjsonTimingMs {
                init_primitives: 0,
                target_consts: 5,
                sysroot_pins: 5,
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

        // Every closure module must be a node of the reported import graph.
        let mut no_graph = base.clone();
        no_graph.graph.clear();
        let err = check(&no_graph, false).unwrap_err();
        assert!(err.message.contains("absent from the verdict graph"), "{err}");
        let mut no_model_node = base.clone();
        no_model_node.graph.remove("Trusted.MirSemantics");
        let err = check(&no_model_node, false).unwrap_err();
        assert!(err.message.contains("modelClosure module Trusted.MirSemantics"), "{err}");

        let mut dup_ax = base.clone();
        dup_ax.axioms = vec!["propext".to_owned(), "propext".to_owned()];
        assert!(check(&dup_ax, false).is_err());

        let mut bad_sha = base.clone();
        bad_sha.nanoda_bin_sha256 = "not-a-sha".to_owned();
        assert!(check(&bad_sha, false).is_err());

        let mut bad_pins_sha = base.clone();
        bad_pins_sha.sysroot_pins_sha256 = String::new();
        assert!(check(&bad_pins_sha, false).is_err());

        let mut bad_quorum = base.clone();
        bad_quorum.paranoid_quorum = true;
        assert!(check(&bad_quorum, false).is_err());
        bad_quorum.kernels_passed.extend(["lean4lean".to_owned(), "con-leche".to_owned()]);
        assert!(check(&bad_quorum, false).is_err());
        bad_quorum.lean4lean_sha256 = Some("0".repeat(64));
        bad_quorum.con_leche_sha256 = Some("0".repeat(64));
        check(&bad_quorum, false).unwrap();

        let mut sorry_ok = base.clone();
        sorry_ok.axioms = vec!["sorryAx".to_owned()];
        sorry_ok.sorry_declarations = vec!["Proof.verify".to_owned()];
        sorry_ok.kernels_passed = vec!["nanoda_bin".to_owned()];
        assert!(check(&sorry_ok, false).is_err());
        check(&sorry_ok, true).unwrap();
    }

    #[test]
    fn rejects_flat_string_name_collision_and_duplicate_json_keys() {
        // 1. Flat single-segment `"Classical.choice"` must not satisfy
        // structural lookup for `Classical` -> `choice`.
        let (init_s, expected_s, proof_s) = synthetic_ndjson_fixture();
        let flat_init = init_s.replace(
            r#""str":"Classical"}}"#,
            r#""str":"Classical_other"}}"#,
        );
        let flat_init = format!(
            "{flat_init}{{\"in\":999,\"str\":{{\"pre\":0,\"str\":\"Classical.choice\"}}}}\n\
             {{\"axiom\":{{\"isUnsafe\":false,\"levelParams\":[],\"name\":999,\"type\":0}}}}\n"
        );
        let err = run_compare(&flat_init, &expected_s, &proof_s, false).unwrap_err();
        assert!(err.message.contains("missing standard axiom"), "{err}");

        // 2. Duplicate JSON keys inside NDJSON must fail closed.
        let dup_proof = format!("{proof_s}{{\"in\":250,\"in\":251,\"str\":{{\"pre\":0,\"str\":\"X\"}}}}\n");
        let err = run_compare(&init_s, &expected_s, &dup_proof, false).unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("duplicate JSON key"), "{err}");

        // 3. Mismatched `ExportMeta` across 5a and 5b fails closed.
        let skewed_proof = proof_s.replace(r#""version":"4.35.0""#, r#""version":"4.35.1""#);
        let err = run_compare(&init_s, &expected_s, &skewed_proof, false).unwrap_err();
        assert!(err.message.contains("NDJSON metadata differs"), "{err}");
    }

    #[test]
    fn enforces_spec_declared_custom_namespace_and_private_root_isolation() {
        let (init_s, expected_s, proof_s) = synthetic_ndjson_fixture();

        // 1. Unused custom-namespace spec helper calling `dbgTrace` fails
        // closed when registered via `spec_declared_consts`.
        let custom_expected = format!(
            "{expected_s}{}",
            r#"{"in":91,"str":{"pre":0,"str":"Contract"}}
{"in":92,"str":{"pre":91,"str":"badHelper"}}
{"in":93,"str":{"pre":0,"str":"dbgTrace"}}
{"ie":93,"const":{"name":93,"us":[]}}
{"def":{"all":[93],"hints":"abbrev","levelParams":[],"name":93,"safety":"safe","type":10,"value":10}}
{"def":{"all":[92],"hints":"abbrev","levelParams":[],"name":92,"safety":"safe","type":10,"value":93}}
"#
        );
        let mut sysroot = default_sysroot_map();
        sysroot.insert("dbgTrace".to_owned(), "Init.Util".to_owned());
        let mut origins = default_origins();
        origins.insert(
            "Contract.badHelper".to_owned(),
            origin("Spec", TargetOriginRole::Specification),
        );
        let req = default_req(false, &sysroot, &origins);
        let err =
            run_compare_pinned(&init_s, &custom_expected, &custom_expected, &proof_s, &req)
                .unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("dbgTrace"), "{err}");

        // 2. `_root_.Proof.evil` in `expected_cone` must be caught by
        // `user_name_root`.
        let rooted_expected = format!(
            "{expected_s}{}",
            r#"{"in":94,"str":{"pre":0,"str":"_root_"}}
{"in":95,"str":{"pre":94,"str":"Proof"}}
{"in":96,"str":{"pre":95,"str":"evil"}}
{"def":{"all":[96],"hints":"abbrev","levelParams":[],"name":96,"safety":"safe","type":10,"value":10}}
"#
        );
        let err = run_compare(&init_s, &rooted_expected, &proof_s, false).unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("forbidden proof-origin constant"), "{err}");
    }

    #[test]
    fn permits_sysroot_opaque_platform_and_eq_helpers_while_blocking_forged_reserved_roots() {
        let (init_s, expected_s, proof_s) = synthetic_ndjson_fixture();

        // 1. `System.Platform.getNumBits` `.opaqueInfo` permitted when in
        // `sysroot_const_to_module` + pinned in `init_primitives`.
        let sys_expected = expected_s.replace(
            r#"{"def":{"all":[18],"hints":"abbrev","levelParams":[],"name":18,"safety":"safe","type":10,"value":10}}"#,
            r#"{"in":80,"str":{"pre":0,"str":"System"}}
{"in":81,"str":{"pre":80,"str":"Platform"}}
{"in":82,"str":{"pre":81,"str":"getNumBits"}}
{"il":11,"succ":0}
{"ie":18,"sort":11}
{"ie":82,"const":{"name":82,"us":[]}}
{"opaque":{"all":[82],"isUnsafe":false,"levelParams":[],"name":82,"type":18,"value":10}}
{"def":{"all":[18],"hints":"abbrev","levelParams":[],"name":18,"safety":"safe","type":10,"value":82}}"#,
        );
        let sys_proof = proof_s.replace(
            r#"{"def":{"all":[108],"hints":"abbrev","levelParams":[],"name":108,"safety":"safe","type":100,"value":100}}"#,
            r#"{"in":180,"str":{"pre":0,"str":"System"}}
{"in":181,"str":{"pre":180,"str":"Platform"}}
{"in":182,"str":{"pre":181,"str":"getNumBits"}}
{"il":101,"succ":0}
{"ie":181,"sort":101}
{"ie":182,"const":{"name":182,"us":[]}}
{"opaque":{"all":[182],"isUnsafe":false,"levelParams":[],"name":182,"type":181,"value":100}}
{"def":{"all":[108],"hints":"abbrev","levelParams":[],"name":108,"safety":"safe","type":100,"value":182}}"#,
        );
        let mut sysroot = default_sysroot_map();
        sysroot.insert("Nat.add".to_owned(), "Init.Data.Nat.Basic".to_owned());
        // Generated `Nat.add.eq_1` theorem in `proof_full` is also permitted.
        let sys_proof_with_eq = format!(
            "{sys_proof}{}",
            r#"{"in":280,"str":{"pre":0,"str":"Nat"}}
{"in":281,"str":{"pre":280,"str":"add"}}
{"in":282,"str":{"pre":281,"str":"eq_1"}}
{"thm":{"all":[282],"levelParams":[],"name":282,"type":100,"value":100}}
"#
        );
        let origins = default_origins();
        let req = default_req(false, &sysroot, &origins);
        let summary =
            run_compare_with(&init_s, &sys_expected, &sys_proof_with_eq, &req).unwrap();
        assert!(summary
            .specification_closure
            .iter()
            .any(|e| e.name == "System.Platform.getNumBits" && e.module == "Init.Prelude"));

        // 2. Arbitrary `Nat.evil` outside sysroot fails closed.
        let bad_nat_proof = format!(
            "{proof_s}{}",
            r#"{"in":280,"str":{"pre":0,"str":"Nat"}}
{"in":281,"str":{"pre":280,"str":"evil"}}
{"def":{"all":[281],"hints":"abbrev","levelParams":[],"name":281,"safety":"safe","type":100,"value":100}}
"#
        );
        let err = run_compare(&init_s, &expected_s, &bad_nat_proof, false).unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("reserved kernel/sysroot root"), "{err}");
    }

    /// Replace the `Spec.specs` placeholder definition in the `expected_cone`
    /// fixture with `lines` (which must redefine name 18).
    fn with_expected_spec(expected_s: &str, lines: &str) -> String {
        expected_s.replace(
            r#"{"def":{"all":[18],"hints":"abbrev","levelParams":[],"name":18,"safety":"safe","type":10,"value":10}}"#,
            lines,
        )
    }

    #[test]
    fn rejects_open_exports_instead_of_skipping_missing_dependencies() {
        let (init_s, expected_s, proof_s) = synthetic_ndjson_fixture();

        // `Spec.specs` in the trusted export depends on `Spec.aux`, which the
        // trusted export omits; the proof export supplies its own `Spec.aux`.
        // The omission must fail closed rather than let `proof_full` define
        // the dependency.
        let open_expected = with_expected_spec(
            &expected_s,
            r#"{"in":30,"str":{"pre":17,"str":"aux"}}
{"ie":30,"const":{"name":30,"us":[]}}
{"def":{"all":[18],"hints":"abbrev","levelParams":[],"name":18,"safety":"safe","type":10,"value":30}}"#,
        );
        let proof_with_aux = proof_s.replace(
            r#"{"def":{"all":[108],"hints":"abbrev","levelParams":[],"name":108,"safety":"safe","type":100,"value":100}}"#,
            r#"{"in":130,"str":{"pre":107,"str":"aux"}}
{"ie":130,"const":{"name":130,"us":[]}}
{"def":{"all":[130],"hints":"abbrev","levelParams":[],"name":130,"safety":"safe","type":100,"value":100}}
{"def":{"all":[108],"hints":"abbrev","levelParams":[],"name":108,"safety":"safe","type":100,"value":130}}"#,
        );
        let err = run_compare(&init_s, &open_expected, &proof_with_aux, false).unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert!(
            err.message.contains("expected_cone is not closed")
                && err.message.contains("Spec.aux"),
            "{err}"
        );

        // An open proof export fails closed too.
        let open_proof = proof_s.replace(
            r#"{"thm":{"all":[112],"levelParams":[],"name":112,"type":108,"value":100}}"#,
            r#"{"in":131,"str":{"pre":111,"str":"missing"}}
{"ie":131,"const":{"name":131,"us":[]}}
{"thm":{"all":[112],"levelParams":[],"name":112,"type":108,"value":131}}"#,
        );
        let err = run_compare(&init_s, &expected_s, &open_proof, false).unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert!(err.message.contains("proof_full is not closed"), "{err}");

        // A definition's mutual-block `all` peer is recorded by name only, so
        // its absence is not an open export.
        let peer_expected = with_expected_spec(
            &expected_s,
            r#"{"in":31,"str":{"pre":17,"str":"peer"}}
{"def":{"all":[18,31],"hints":"abbrev","levelParams":[],"name":18,"safety":"safe","type":10,"value":10}}"#,
        );
        let peer_proof = proof_s.replace(
            r#"{"def":{"all":[108],"hints":"abbrev","levelParams":[],"name":108,"safety":"safe","type":100,"value":100}}"#,
            r#"{"in":132,"str":{"pre":107,"str":"peer"}}
{"def":{"all":[108,132],"hints":"abbrev","levelParams":[],"name":108,"safety":"safe","type":100,"value":100}}"#,
        );
        run_compare(&init_s, &peer_expected, &peer_proof, false).unwrap();
    }

    #[test]
    fn pins_sysroot_named_constants_to_the_clean_sysroot_export() {
        let (init_s, expected_s, proof_s) = synthetic_ndjson_fixture();
        let mut sysroot = default_sysroot_map();
        sysroot.insert("Nat.log2".to_owned(), "Init.Data.Nat.Log2".to_owned());
        let origins = default_origins();
        let req = default_req(false, &sysroot, &origins);
        let pins = format!(
            "{init_s}{}",
            r#"{"in":900,"str":{"pre":0,"str":"Nat"}}
{"in":901,"str":{"pre":900,"str":"log2"}}
{"def":{"all":[901],"hints":"abbrev","levelParams":[],"name":901,"safety":"safe","type":1,"value":0}}
"#
        );
        let log2_proof = |value: u64| {
            format!(
                r#"{proof_s}{{"in":300,"str":{{"pre":0,"str":"Nat"}}}}
{{"in":301,"str":{{"pre":300,"str":"log2"}}}}
{{"il":101,"succ":0}}
{{"ie":120,"sort":101}}
{{"def":{{"all":[301],"hints":"abbrev","levelParams":[],"name":301,"safety":"safe","type":120,"value":{value}}}}}
"#
            )
        };

        // 1. A sysroot-named constant identical to the clean re-export passes.
        let summary =
            run_compare_pinned(&init_s, &pins, &expected_s, &log2_proof(100), &req).unwrap();
        assert_eq!(summary.sysroot_pinned_declarations, 1);

        // 2. A proof module that redeclares the sysroot name with different
        // content (as a prelude-only module that never imports the defining
        // sysroot module could) fails closed.
        let err =
            run_compare_pinned(&init_s, &pins, &expected_s, &log2_proof(120), &req).unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert!(
            err.message.contains("Nat.log2") && err.message.contains("differs from clean sysroot"),
            "{err}"
        );

        // 3. A sysroot-named constant missing from the clean re-export fails
        // closed rather than being trusted by name.
        let err =
            run_compare_pinned(&init_s, &init_s, &expected_s, &log2_proof(100), &req).unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert!(err.message.contains("absent from the clean sysroot re-export"), "{err}");

        // 4. A private proof constant whose user name is kernel-accelerated
        // never counts as sysroot.
        let private_add = format!(
            "{proof_s}{}",
            r#"{"in":310,"str":{"pre":0,"str":"_private"}}
{"in":311,"str":{"pre":310,"str":"Proof"}}
{"in":312,"num":{"pre":311,"i":0}}
{"in":313,"str":{"pre":312,"str":"Nat"}}
{"in":314,"str":{"pre":313,"str":"add"}}
{"def":{"all":[314],"hints":"abbrev","levelParams":[],"name":314,"safety":"safe","type":100,"value":100}}
"#
        );
        let err = run_compare(&init_s, &expected_s, &private_add, false).unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert!(err.message.contains("kernel-accelerated name"), "{err}");
    }

    #[test]
    fn enforces_trusted_isolation_and_target_origins_on_both_exports() {
        let (init_s, expected_s, proof_s) = synthetic_ndjson_fixture();
        let sysroot = default_sysroot_map();
        let origins = default_origins();
        let req = default_req(false, &sysroot, &origins);

        // 1. Proof-origin `Trusted.*` constant fails closed.
        let evil = format!(
            "{proof_s}{}",
            r#"{"in":320,"str":{"pre":101,"str":"Evil"}}
{"def":{"all":[320],"hints":"abbrev","levelParams":[],"name":320,"safety":"safe","type":100,"value":100}}
"#
        );
        let err = run_compare_with(&init_s, &expected_s, &evil, &req).unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert!(
            err.message.contains("Trusted.MirSemantics.Evil")
                && err.message.contains("outside model modules"),
            "{err}"
        );

        // 2. A generated equation theorem of a model constant is admitted.
        let eq_helper = format!(
            "{proof_s}{}",
            r#"{"in":321,"str":{"pre":102,"str":"eq_1"}}
{"thm":{"all":[321],"levelParams":[],"name":321,"type":100,"value":100}}
"#
        );
        run_compare_with(&init_s, &expected_s, &eq_helper, &req).unwrap();

        // 3. A non-model target module declaring `Trusted.*` in the trusted
        // export fails closed.
        let spec_trusted_expected = format!(
            "{expected_s}{}",
            r#"{"in":40,"str":{"pre":11,"str":"Crate2"}}
{"def":{"all":[40],"hints":"abbrev","levelParams":[],"name":40,"safety":"safe","type":10,"value":10}}
"#
        );
        let mut spec_origins = default_origins();
        spec_origins.insert(
            "Trusted.MirSemantics.Crate2".to_owned(),
            origin("Spec", TargetOriginRole::Specification),
        );
        let spec_req = default_req(false, &sysroot, &spec_origins);
        let err = run_compare_with(&init_s, &spec_trusted_expected, &proof_s, &spec_req).unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert!(err.message.contains("outside model modules"), "{err}");

        // 4. A target-module constant in the proof export must come from the
        // trusted export.
        let captured_helper = format!(
            "{proof_s}{}",
            r#"{"in":330,"str":{"pre":105,"str":"helper"}}
{"def":{"all":[330],"hints":"abbrev","levelParams":[],"name":330,"safety":"safe","type":100,"value":100}}
"#
        );
        let mut helper_origins = default_origins();
        helper_origins
            .insert("Captured.helper".to_owned(), origin("Captured", TargetOriginRole::Capture));
        let helper_req = default_req(false, &sysroot, &helper_origins);
        let err = run_compare_with(&init_s, &expected_s, &captured_helper, &helper_req).unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert!(err.message.contains("absent from the trusted expected export"), "{err}");

        // 5. Every trusted-export constant needs an authenticated origin.
        let orphan_expected = format!(
            "{expected_s}{}",
            r#"{"in":41,"str":{"pre":0,"str":"Orphan"}}
{"in":42,"str":{"pre":41,"str":"x"}}
{"def":{"all":[42],"hints":"abbrev","levelParams":[],"name":42,"safety":"safe","type":10,"value":10}}
"#
        );
        let err = run_compare(&init_s, &orphan_expected, &proof_s, false).unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert!(err.message.contains("no authenticated sysroot or target-module origin"), "{err}");

        // 6. Canonical inputs must come from their designated roles and the
        // expected declaration from the `Expected` module.
        for (name, module, role) in [
            ("Captured.program", "Spec", TargetOriginRole::Specification),
            ("Spec.specs", "Captured", TargetOriginRole::Capture),
            ("Trusted.MirSemantics.Crate.mk", "Expected", TargetOriginRole::Expected),
            ("Expected.claim", "Other", TargetOriginRole::Expected),
        ] {
            let mut bad = default_origins();
            bad.insert(name.to_owned(), origin(module, role));
            let bad_req = default_req(false, &sysroot, &bad);
            let err = run_compare_with(&init_s, &expected_s, &proof_s, &bad_req).unwrap_err();
            assert_eq!(err.code, 1, "{name}: {err}");
            // A non-model `Trusted.*` origin is already refused by the
            // `Trusted` isolation check.
            assert!(
                err.message.contains("incorrect canonical input origin")
                    || (name.starts_with("Trusted.") && err.message.contains("outside model modules")),
                "{name}: {err}"
            );
        }

        // 7. The target theorem must be proof-origin: a target-module or
        // sysroot origin fails closed.
        let mut theorem_origins = default_origins();
        theorem_origins
            .insert("Proof.verify".to_owned(), origin("Expected", TargetOriginRole::Expected));
        let theorem_req = default_req(false, &sysroot, &theorem_origins);
        let err = run_compare_with(&init_s, &expected_s, &proof_s, &theorem_req).unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert!(err.message.contains("Proof.verify"), "{err}");
        let mut theorem_sysroot = default_sysroot_map();
        theorem_sysroot.insert("Proof.verify".to_owned(), "Init.Prelude".to_owned());
        let theorem_req = default_req(false, &theorem_sysroot, &origins);
        let pins = format!(
            "{init_s}{}",
            r#"{"in":910,"str":{"pre":0,"str":"Proof"}}
{"in":911,"str":{"pre":910,"str":"verify"}}
{"thm":{"all":[911],"levelParams":[],"name":911,"type":0,"value":0}}
"#
        );
        let err =
            run_compare_pinned(&init_s, &pins, &expected_s, &proof_s, &theorem_req).unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert!(err.message.contains("Proof.verify"), "{err}");
    }

    #[test]
    fn applies_specification_bans_to_every_module_indexed_spec_constant() {
        let (init_s, expected_s, proof_s) = synthetic_ndjson_fixture();
        let mut sysroot = default_sysroot_map();
        sysroot.insert("panicCore".to_owned(), "Init.Prelude".to_owned());

        // 1. A compiler-generated spec constant (e.g. an anonymous instance)
        // that the trusted export omits fails closed.
        let mut missing = default_origins();
        missing.insert(
            "instInhabitedFoo".to_owned(),
            origin("Spec", TargetOriginRole::Specification),
        );
        let req = default_req(false, &sysroot, &missing);
        let err = run_compare_with(&init_s, &expected_s, &proof_s, &req).unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert!(
            err.message.contains("instInhabitedFoo") && err.message.contains("absent"),
            "{err}"
        );

        // 2. A paired well-founded `_unsafe_rec` auxiliary is never exported
        // and is not required, but it may not appear in either export: there
        // it is a target-module constant absent from the trusted export (and a
        // `partial` declaration).
        let mut paired = default_origins();
        paired.insert(
            "Spec.specs._unsafe_rec".to_owned(),
            TargetConstOrigin {
                module: "Spec".to_owned(),
                role: TargetOriginRole::Specification,
                paired_unsafe_rec: true,
            },
        );
        let req = default_req(false, &sysroot, &paired);
        run_compare_with(&init_s, &expected_s, &proof_s, &req).unwrap();
        let proof_with_aux = format!(
            "{proof_s}{}",
            r#"{"in":340,"str":{"pre":108,"str":"_unsafe_rec"}}
{"def":{"all":[340],"hints":"opaque","levelParams":[],"name":340,"safety":"partial","type":100,"value":100}}
"#
        );
        let err = run_compare_with(&init_s, &expected_s, &proof_with_aux, &req).unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert!(err.message.contains("Spec.specs._unsafe_rec"), "{err}");

        // 3. A spec constant outside the `Spec` namespace (here a generated
        // instance in a custom namespace, unreferenced by `Spec.specs`) is
        // attributed by the module index and gets the direct bans.
        let instance_expected = format!(
            "{expected_s}{}",
            r#"{"in":50,"str":{"pre":0,"str":"panicCore"}}
{"ie":50,"const":{"name":50,"us":[]}}
{"def":{"all":[50],"hints":"abbrev","levelParams":[],"name":50,"safety":"safe","type":10,"value":10}}
{"in":51,"str":{"pre":0,"str":"Contract"}}
{"in":52,"str":{"pre":51,"str":"instFoo"}}
{"def":{"all":[52],"hints":"abbrev","levelParams":[],"name":52,"safety":"safe","type":10,"value":50}}
"#
        );
        let mut inst_origins = default_origins();
        inst_origins.insert(
            "Contract.instFoo".to_owned(),
            origin("Spec", TargetOriginRole::Specification),
        );
        let req = default_req(false, &sysroot, &inst_origins);
        let err =
            run_compare_pinned(&init_s, &instance_expected, &instance_expected, &proof_s, &req)
                .unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert!(
            err.message.contains("Contract.instFoo") && err.message.contains("cannot reference"),
            "{err}"
        );
    }

    #[test]
    fn renders_leanexport_name_literals_round_trippably() {
        let mut arena = CanonicalArena::new();
        let private = arena.intern_encoded_name("_private.Spec.#0.foo");
        assert_eq!(render_leanexport_name(&arena, private).as_deref(), Some("_private.Spec.0.foo"));
        let dotted = arena.intern_encoded_name("Foo.a\\.b");
        assert_eq!(render_leanexport_name(&arena, dotted).as_deref(), Some("Foo.«a.b»"));
        let digits = arena.intern_encoded_name("Foo.0");
        assert_eq!(render_leanexport_name(&arena, digits).as_deref(), Some("Foo.«0»"));
        let bang = arena.intern_dotted_name("List.head!");
        assert_eq!(render_leanexport_name(&arena, bang).as_deref(), Some("List.head!"));
        let unicode = arena.intern_dotted_name("Spec.α");
        assert_eq!(render_leanexport_name(&arena, unicode).as_deref(), Some("Spec.«α»"));
        let guillemet = arena.intern_dotted_name("Spec.a»b");
        assert_eq!(render_leanexport_name(&arena, guillemet), None);
        let leading_num = arena.intern_encoded_name("#3.x");
        assert_eq!(render_leanexport_name(&arena, leading_num), None);
    }

    #[test]
    fn plans_reexports_from_export_frontiers() {
        let (_init_s, expected_s, proof_s) = synthetic_ndjson_fixture();
        let mut arena = CanonicalArena::new();
        let expected_env =
            parse_ndjson_reader(BufReader::new(expected_s.as_bytes()), &mut arena, "expected")
                .unwrap();
        let proof_env =
            parse_ndjson_reader(BufReader::new(proof_s.as_bytes()), &mut arena, "proof").unwrap();

        // Treat `Captured.program` and `Spec.specs` as sysroot-named: both are
        // referenced only from non-sysroot `Expected.claim`, so both are roots.
        let sysroot = HashMap::from([
            ("Captured.program".to_owned(), "Init.A".to_owned()),
            ("Spec.specs".to_owned(), "Init.B".to_owned()),
        ]);
        let plan = plan_sysroot_pin_export(&arena, &[&expected_env, &proof_env], &sysroot).unwrap();
        assert_eq!(plan.modules, vec!["Init.A".to_owned(), "Init.B".to_owned()]);
        assert_eq!(plan.roots, vec!["Captured.program".to_owned(), "Spec.specs".to_owned()]);

        // `5a` roots: the expected declaration, every safe spec constant, and
        // the proof export's target-module frontier.
        let mut origins = default_origins();
        origins.insert(
            "Contract.extra".to_owned(),
            origin("Spec", TargetOriginRole::Specification),
        );
        let plan = plan_expected_export(
            &mut arena,
            &proof_env,
            &origins,
            &["Spec".to_owned(), "Expected".to_owned()],
            "Expected.claim",
        )
        .unwrap();
        assert_eq!(plan.modules, vec!["Expected".to_owned(), "Spec".to_owned()]);
        assert_eq!(
            plan.roots,
            vec![
                "Contract.extra".to_owned(),
                "Expected.claim".to_owned(),
                "Spec.specs".to_owned()
            ]
        );
    }

    #[test]
    fn admits_only_listed_canonical_roots_and_their_crate_constructors() {
        let (init_s, expected_s, proof_s) = synthetic_ndjson_fixture();
        let sysroot = default_sysroot_map();

        let model = || origin("Trusted.MirSemantics", TargetOriginRole::Model);

        // An unlisted root fails closed even when the Model module defines
        // it and `Expected.claim` applies it to `Crate.mk`.
        let bogus = |s: &str| s.replace(r#""str":"UnitTheorem"}"#, r#""str":"BogusTheorem"}"#);
        let mut origins_bogus = default_origins();
        origins_bogus.remove("Trusted.MirSemantics.UnitTheorem");
        origins_bogus.insert("Trusted.MirSemantics.BogusTheorem".to_owned(), model());
        let mut req = default_req(false, &sysroot, &origins_bogus);
        req.canonical_root = "Trusted.MirSemantics.BogusTheorem";
        let err = run_compare_with(&init_s, &bogus(&expected_s), &bogus(&proof_s), &req)
            .unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert!(err.message.contains("unexpected canonical root"), "{err}");

        // Profile v2 roots apply `CrateV2.mk`.
        let to_v2 = |s: &str| {
            s.replace(r#""str":"UnitTheorem"}"#, r#""str":"UnitTheoremV2"}"#)
                .replace(r#""str":"Crate"}"#, r#""str":"CrateV2"}"#)
        };
        let (expected_v2, proof_v2) = (to_v2(&expected_s), to_v2(&proof_s));
        let mut origins_v2 = default_origins();
        origins_v2.remove("Trusted.MirSemantics.UnitTheorem");
        origins_v2.remove("Trusted.MirSemantics.Crate.mk");
        origins_v2.insert("Trusted.MirSemantics.UnitTheoremV2".to_owned(), model());
        origins_v2.insert("Trusted.MirSemantics.CrateV2.mk".to_owned(), model());
        let mut req = default_req(false, &sysroot, &origins_v2);
        req.canonical_root = "Trusted.MirSemantics.UnitTheoremV2";
        run_compare_with(&init_s, &expected_v2, &proof_v2, &req).unwrap();

        // A v2 root applied to the v1 `Crate.mk` fails closed.
        let mut origins_mixed = default_origins();
        origins_mixed.insert("Trusted.MirSemantics.UnitTheoremV2".to_owned(), model());
        let mixed = |s: &str| s.replace(r#""str":"UnitTheorem"}"#, r#""str":"UnitTheoremV2"}"#);
        let mut req = default_req(false, &sysroot, &origins_mixed);
        req.canonical_root = "Trusted.MirSemantics.UnitTheoremV2";
        let err = run_compare_with(&init_s, &mixed(&expected_s), &mixed(&proof_s), &req)
            .unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert!(err.message.contains("Trusted.MirSemantics.CrateV2.mk"), "{err}");
    }

    #[test]
    fn enforces_target_role_edges_and_reached_compiler_overrides() {
        let (init_s, expected_s, proof_s) = synthetic_ndjson_fixture();

        // 1. A specification constant referencing captured program data is a
        // compiled `Specification -> Capture` edge, which `TargetRole::allows`
        // forbids.
        let spec_to_capture_expected = expected_s.replace(
            r#"{"def":{"all":[18],"hints":"abbrev","levelParams":[],"name":18,"safety":"safe","type":10,"value":10}}"#,
            r#"{"def":{"all":[18],"hints":"abbrev","levelParams":[],"name":18,"safety":"safe","type":10,"value":13}}"#,
        );
        let spec_to_capture_proof = proof_s.replace(
            r#"{"def":{"all":[108],"hints":"abbrev","levelParams":[],"name":108,"safety":"safe","type":100,"value":100}}"#,
            r#"{"def":{"all":[108],"hints":"abbrev","levelParams":[],"name":108,"safety":"safe","type":100,"value":103}}"#,
        );
        let err = run_compare(&init_s, &spec_to_capture_expected, &spec_to_capture_proof, false)
            .unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert!(
            err.message.contains("target authority violation")
                && err.message.contains("Spec.specs")
                && err.message.contains("Captured.program"),
            "{err}"
        );

        // 2. A sysroot constant may never reference a target constant.
        let mut sysroot = default_sysroot_map();
        sysroot.insert("Spec.specs".to_owned(), "Init.Prelude".to_owned());
        let mut origins = default_origins();
        origins.remove("Spec.specs");
        origins.insert("Spec.helper".to_owned(), origin("Spec", TargetOriginRole::Specification));
        let lib_to_target_expected = format!(
            "{}{}",
            expected_s.replace(
                r#"{"def":{"all":[18],"hints":"abbrev","levelParams":[],"name":18,"safety":"safe","type":10,"value":10}}"#,
                r#"{"in":60,"str":{"pre":17,"str":"helper"}}
{"ie":60,"const":{"name":60,"us":[]}}
{"def":{"all":[60],"hints":"abbrev","levelParams":[],"name":60,"safety":"safe","type":10,"value":10}}
{"def":{"all":[18],"hints":"abbrev","levelParams":[],"name":18,"safety":"safe","type":10,"value":60}}"#,
            ),
            ""
        );
        let lib_to_target_proof = proof_s.replace(
            r#"{"def":{"all":[108],"hints":"abbrev","levelParams":[],"name":108,"safety":"safe","type":100,"value":100}}"#,
            r#"{"in":150,"str":{"pre":107,"str":"helper"}}
{"ie":150,"const":{"name":150,"us":[]}}
{"def":{"all":[150],"hints":"abbrev","levelParams":[],"name":150,"safety":"safe","type":100,"value":100}}
{"def":{"all":[108],"hints":"abbrev","levelParams":[],"name":108,"safety":"safe","type":100,"value":150}}"#,
        );
        let req = default_req(false, &sysroot, &origins);
        let err = run_compare_pinned(
            &init_s,
            &lib_to_target_expected,
            &lib_to_target_expected,
            &lib_to_target_proof,
            &req,
        )
        .unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert!(
            err.message.contains("target authority violation")
                && err.message.contains("Spec.specs")
                && err.message.contains("Spec.helper"),
            "{err}"
        );

        // 3. A reached target declaration carrying a compiler override fails
        // closed; an unreached one does not matter.
        let sysroot = default_sysroot_map();
        let origins = default_origins();
        let overrides = BTreeSet::from(["Spec.specs".to_owned()]);
        let mut req = default_req(false, &sysroot, &origins);
        req.target_compiler_overrides = &overrides;
        let err = run_compare_with(&init_s, &expected_s, &proof_s, &req).unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert!(
            err.message.contains("compiler override") && err.message.contains("Spec.specs"),
            "{err}"
        );
        let unreached = BTreeSet::from(["Spec.unreached".to_owned()]);
        req.target_compiler_overrides = &unreached;
        run_compare_with(&init_s, &expected_s, &proof_s, &req).unwrap();
    }

    #[test]
    fn structural_dag_tamper_mutator_rejects_every_attack_vector() {
        let (init_s, expected_s, proof_s) = synthetic_ndjson_fixture();
        let sysroot = default_sysroot_map();
        let origins = default_origins();
        let req = default_req(false, &sysroot, &origins);

        // Baseline must pass cleanly before mutating.
        run_compare_with(&init_s, &expected_s, &proof_s, &req).unwrap();

        // 1. Deleted transitive dependency (`Trusted.MirSemantics.Crate.mk`
        // removed).
        let dep_line = concat!(
            r#"{"def":{"all":[104],"hints":"abbrev","levelParams":[],"name":104,"safety":"safe","type":100,"value":100}}"#,
            "\n",
        );
        let deleted_dep_proof = proof_s.replace(dep_line, "");
        assert_ne!(deleted_dep_proof, proof_s);
        let err = run_compare_with(&init_s, &expected_s, &deleted_dep_proof, &req).unwrap_err();
        assert!(
            err.message.contains("proof_full is not closed")
                && err.message.contains("Trusted.MirSemantics.Crate.mk"),
            "unexpected error for deleted dep: {err}"
        );

        // 2. Altered constant value in `Proof`'s `Expected.claim` vs
        // `Expected`.
        let altered_val_proof = proof_s.replace(
            r#"{"def":{"all":[110],"hints":"abbrev","levelParams":[],"name":110,"safety":"safe","type":100,"value":107}}"#,
            r#"{"def":{"all":[110],"hints":"abbrev","levelParams":[],"name":110,"safety":"safe","type":100,"value":100}}"#,
        );
        assert_ne!(altered_val_proof, proof_s);
        let err = run_compare_with(&init_s, &expected_s, &altered_val_proof, &req).unwrap_err();
        assert!(
            err.message.contains(
                "declaration `Expected.claim` differs between trusted expected export and proof export"
            ),
            "unexpected error for altered body: {err}"
        );

        // 3. Altered constant type in `Proof`'s `Spec.specs` (changing `type`
        // from `Sort 0` (`100`) to already-declared `UnitTheorem` (`101`) keeps
        // topological order intact so Step 3's DAG-identity check fires).
        let altered_type_proof = proof_s.replace(
            r#"{"def":{"all":[108],"hints":"abbrev","levelParams":[],"name":108,"safety":"safe","type":100,"value":100}}"#,
            r#"{"def":{"all":[108],"hints":"abbrev","levelParams":[],"name":108,"safety":"safe","type":101,"value":100}}"#,
        );
        assert_ne!(altered_type_proof, proof_s);
        let err = run_compare_with(&init_s, &expected_s, &altered_type_proof, &req).unwrap_err();
        assert!(
            err.message.contains(
                "declaration `Spec.specs` differs between trusted expected export and proof export"
            ),
            "unexpected error for altered type: {err}"
        );

        // 4. Altered universe level parameter list (`[100]` vs `[]`).
        let altered_univ_proof = proof_s.replace(
            r#"{"def":{"all":[110],"hints":"abbrev","levelParams":[],"name":110,"safety":"safe","type":100,"value":107}}"#,
            r#"{"def":{"all":[110],"hints":"abbrev","levelParams":[100],"name":110,"safety":"safe","type":100,"value":107}}"#,
        );
        assert_ne!(altered_univ_proof, proof_s);
        let err = run_compare_with(&init_s, &expected_s, &altered_univ_proof, &req).unwrap_err();
        assert!(
            err.message.contains(
                "declaration `Expected.claim` differs between trusted expected export and proof export"
            ),
            "unexpected error for altered levelParams: {err}"
        );

        // 5. Foreign axiom injected and referenced inside `Proof.verify`.
        let verify_line =
            r#"{"thm":{"all":[112],"levelParams":[],"name":112,"type":108,"value":100}}"#;
        let foreign_axiom_proof = proof_s.replace(
            verify_line,
            r#"{"in":150,"str":{"pre":0,"str":"evilAxiom"}}
{"ie":150,"const":{"name":150,"us":[]}}
{"axiom":{"isUnsafe":false,"levelParams":[],"name":150,"type":100}}
{"thm":{"all":[112],"levelParams":[],"name":112,"type":108,"value":150}}"#,
        );
        assert_ne!(foreign_axiom_proof, proof_s);
        let err = run_compare_with(&init_s, &expected_s, &foreign_axiom_proof, &req).unwrap_err();
        assert!(
            err.message.contains("unpermitted axiom") && err.message.contains("evilAxiom"),
            "unexpected error for foreign axiom: {err}"
        );

        // 6. Foreign opaque declaration injected into `Proof` cone.
        let foreign_opaque_proof = proof_s.replace(
            verify_line,
            r#"{"in":151,"str":{"pre":0,"str":"evilOpaque"}}
{"ie":151,"const":{"name":151,"us":[]}}
{"opaque":{"all":[151],"isUnsafe":false,"levelParams":[],"name":151,"type":100,"value":100}}
{"thm":{"all":[112],"levelParams":[],"name":112,"type":108,"value":151}}"#,
        );
        assert_ne!(foreign_opaque_proof, proof_s);
        let err = run_compare_with(&init_s, &expected_s, &foreign_opaque_proof, &req).unwrap_err();
        assert!(
            err.message.contains("opaque declaration") && err.message.contains("evilOpaque"),
            "unexpected error for foreign opaque: {err}"
        );

        // 7. Foreign quotient declaration injected outside pinned quot
        // primitives.
        let foreign_quot_proof = proof_s.replace(
            verify_line,
            r#"{"in":152,"str":{"pre":0,"str":"evilQuot"}}
{"ie":152,"const":{"name":152,"us":[]}}
{"quot":{"kind":"type","levelParams":[],"name":152,"type":100}}
{"thm":{"all":[112],"levelParams":[],"name":112,"type":108,"value":152}}"#,
        );
        assert_ne!(foreign_quot_proof, proof_s);
        let err = run_compare_with(&init_s, &expected_s, &foreign_quot_proof, &req).unwrap_err();
        assert!(
            err.message.contains("unexpected quotient declaration")
                && err.message.contains("evilQuot"),
            "unexpected error for foreign quot: {err}"
        );

        // 8. `Trusted.*` leakage outside `model_modules` (e.g. `Spec` origin).
        let mut bad_origins = origins.clone();
        bad_origins.insert(
            "Trusted.MirSemantics.UnitTheorem".to_owned(),
            origin("Spec", TargetOriginRole::Specification),
        );
        let bad_origin_req = default_req(false, &sysroot, &bad_origins);
        let err = run_compare_with(&init_s, &expected_s, &proof_s, &bad_origin_req).unwrap_err();
        assert!(
            err.message.contains("outside model modules")
                && err.message.contains("Trusted.MirSemantics.UnitTheorem"),
            "unexpected error for Trusted.* origin leak: {err}"
        );

        // 9. Swapped subject/specification declarations (`Captured.program` vs
        // `Spec.specs`).
        let mut swapped_req = default_req(false, &sysroot, &origins);
        swapped_req.subject_declaration = "Spec.specs";
        swapped_req.specification_declaration = "Captured.program";
        let err = run_compare_with(&init_s, &expected_s, &proof_s, &swapped_req).unwrap_err();
        assert!(
            err.message.contains("incorrect canonical input origin")
                && err.message.contains("Spec.specs"),
            "unexpected error for swapped declarations: {err}"
        );

        // 10. Export metadata toolchain version mismatch
        // (`4.99.0` vs `4.35.0`).
        let bad_meta_proof = proof_s.replacen(r#""version":"4.35.0""#, r#""version":"4.99.0""#, 1);
        assert_ne!(bad_meta_proof, proof_s);
        let err = run_compare_with(&init_s, &expected_s, &bad_meta_proof, &req).unwrap_err();
        assert!(
            err.message.contains("proof_full NDJSON metadata differs"),
            "unexpected error for metadata mismatch: {err}"
        );
    }
}
