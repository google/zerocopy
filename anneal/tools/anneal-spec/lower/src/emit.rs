// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Deterministic `Spec.lean`, `spec_span_map.json`, and `spec-closure.golden`
//! emission over `Trusted.Framework.MirEnvelopeSpec`.
//!
//! `Spec.lean` carries no Rust line or column information, so reformatting
//! the Rust source leaves its bytes (and every proof cache keyed on them)
//! unchanged. Source positions live only in the sideband span map.

use proc_macro2::Span;
use serde_json::{json, Value};

use crate::{
    ast::{PureFn, SpecFn, Ty},
    check::{lean_ident, LoweredFn, Uses, INT, VAL},
    closure::{
        render_spec_closure_golden, CapturedBodySummary, CapturedProgramSummary, ClosureDecl,
        ClosureEntry, Scope,
    },
    diag::SourceMap,
    Source,
};

const LICENSE_HEADER: &[&str] = &[
    "-- Copyright 2026 The Fuchsia Authors",
    "--",
    "-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0",
    "-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT",
    "-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.",
    "-- This file may not be copied, modified, or distributed except according to",
    "-- those terms.",
];

const DOWNSTREAM_GAP_TAGS: &[&str] = &[
    "unverifiedDownstream(rustc_mir_opt)",
    "unverifiedDownstream(llvm_codegen)",
    "unverifiedDownstream(linker)",
    "unverifiedDownstream(microarch_timing)",
];

/// The generated outputs of one specification unit.
pub struct Lowered {
    /// The Lean specification module.
    pub spec_lean: String,
    /// Pretty-printed `spec_span_map.json`, ending in a newline; empty for a
    /// span-free `Format::V2Module` lowering.
    pub span_map: String,
    /// Pretty-printed `spec-closure.golden`, ending in a newline.
    pub spec_closure: String,
    /// Where a `Format::V2Module` lowering's module goes, relative to the
    /// output directory (`Specs/<crate>/<claim>.lean`); `None` for
    /// `Format::V1`.
    pub module_path: Option<String>,
}

impl Lowered {
    /// The files to write, as paths relative to the output directory and
    /// their contents.
    pub fn outputs(&self) -> Vec<(&str, &str)> {
        match &self.module_path {
            None => vec![
                ("Spec.lean", &self.spec_lean),
                ("spec_span_map.json", &self.span_map),
                ("spec-closure.golden", &self.spec_closure),
            ],
            Some(path) => {
                vec![(path, &self.spec_lean), ("spec-closure.golden", &self.spec_closure)]
            }
        }
    }
}

struct Writer<'a> {
    text: String,
    line: usize,
    entries: Vec<Value>,
    decls: Vec<ClosureDecl>,
    sources: &'a [Source],
    namespace: &'a str,
    /// Whether to record Rust provenance in `entries`.
    spans: bool,
}

impl Writer<'_> {
    fn push(&mut self, s: &str) {
        self.text.push_str(s);
        self.text.push('\n');
        self.line += s.matches('\n').count() + 1;
    }

    /// Emits a generated runtime declaration without a Rust span.
    fn runtime_def(&mut self, name: &str, decl: &str) {
        self.push(decl);
        self.decls.push(ClosureDecl { name: name.to_string(), kind: "def" });
    }

    /// Emits `decl` (one or more lines), records it in `decls`, and records
    /// its Rust provenance in `span_map` when enabled.
    fn decl(&mut self, name: &str, decl: &str, file: usize, span: Span) {
        let start = self.line;
        self.push(decl);
        self.decls.push(ClosureDecl { name: name.to_string(), kind: "def" });
        if !self.spans {
            return;
        }
        let src = &self.sources[file];
        let s = SourceMap::new(&src.text).span(span);
        self.entries.push(json!({
            "lean_decl": format!("{}.{name}", self.namespace),
            "lean_line_start": start,
            "lean_line_end": self.line - 1,
            "rust": {
                "file": src.label,
                "start_byte": s.start_byte,
                "end_byte": s.end_byte,
                "lo_line": s.lo_line,
                "lo_col": s.lo_col,
                "hi_line": s.hi_line,
                "hi_col": s.hi_col,
            },
        }));
    }
}

/// The Lean type of a helper parameter or result. Later binder types and the
/// result type are in scope of earlier parameters, so these come from
/// `check`'s capture-checked names (see `check::INT`).
fn lean_ty(t: Ty) -> &'static str {
    match t {
        Ty::Bool => "Prop",
        Ty::Unit | Ty::Never => VAL,
        Ty::Int(_) | Ty::Math => INT,
    }
}

fn lean_string(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Text for a doc comment. Lean block comments nest, so both `/-` and `-/`
/// are defused; otherwise user-derived text could close the comment and
/// inject commands.
fn doc_text(s: &str) -> String {
    s.replace("/-", "/ -").replace("-/", "- /")
}

/// Renders `text` (already defused by `doc_text`) as a `/-- ... -/` doc
/// comment that wraps at 80 columns. Words are split only at spaces outside
/// backtick code spans, so a code span is never broken across lines. A word
/// wider than 80 columns gets a line of its own. The closing `-/` is attached
/// to the last word, so it never sits alone on a line.
fn doc_comment(text: &str) -> String {
    const WIDTH: usize = 80;
    let mut words = vec![String::from("/--")];
    let mut word = String::new();
    let mut in_code = false;
    for c in text.chars() {
        if c == '`' {
            in_code = !in_code;
        }
        if c == ' ' && !in_code {
            if !word.is_empty() {
                words.push(std::mem::take(&mut word));
            }
        } else {
            word.push(c);
        }
    }
    if !word.is_empty() {
        words.push(word);
    }
    // Keep the closing `-/` on the same line as the last word.
    let last = words.last_mut().expect("starts with `/--`");
    last.push_str(" -/");
    let mut out = String::new();
    let mut col = 0;
    for w in words {
        let n = w.chars().count();
        if col > 0 && col + 1 + n > WIDTH {
            out.push('\n');
            col = 0;
        } else if col > 0 {
            out.push(' ');
            col += 1;
        }
        out.push_str(&w);
        col += n;
    }
    out
}

fn mir_ty(t: Ty) -> String {
    match t {
        Ty::Bool => ".bool".into(),
        Ty::Unit => ".unit".into(),
        Ty::Never => ".never".into(),
        Ty::Int(t) => {
            let width = if t.pointer_sized {
                ".isize"
            } else {
                match t.bits {
                    8 => ".i8",
                    16 => ".i16",
                    32 => ".i32",
                    64 => ".i64",
                    128 => ".i128",
                    _ => unreachable!("unsupported integer bit width {}", t.bits),
                }
            };
            format!(".int {width} {}", t.signed)
        }
        Ty::Math => unreachable!("`math` is not a function signature type"),
    }
}

fn mir_signature_record(f: &SpecFn) -> String {
    let params: Vec<String> = f.params.iter().map(|p| mir_ty(p.ty)).collect();
    format!(
        "{{ isUnsafe := {}, abi := .rust, params := [{}], ret := {} }}",
        f.is_unsafe,
        params.join(", "),
        mir_ty(f.ret)
    )
}

fn captured_mir_signature_record(b: &CapturedBodySummary) -> String {
    format!(
        "{{ isUnsafe := {}, abi := .rust, params := [{}], ret := {} }}",
        b.is_unsafe,
        b.params_lean.join(", "),
        b.ret_lean
    )
}

fn signature(f: &SpecFn) -> String {
    let params: Vec<String> =
        f.params.iter().map(|p| format!("{}: {}", p.name, p.ty.describe())).collect();
    let unsafety = if f.is_unsafe { "unsafe " } else { "" };
    format!("{unsafety}fn {}({}) -> {}", f.path, params.join(", "), f.ret.describe())
}

#[allow(clippy::too_many_arguments)]
pub fn emit(
    sources: &[Source],
    helpers: &[(&PureFn, String)],
    fns: &[(&SpecFn, LoweredFn)],
    unannotated_safe_callees: &[CapturedBodySummary],
    capture: Option<&CapturedProgramSummary>,
    scope: Scope,
    runtime: &Uses,
    namespace: &str,
    lean_module: &str,
    module_path: Option<String>,
) -> Lowered {
    let module = module_path.is_some();
    let mut w = Writer {
        text: String::new(),
        line: 1,
        entries: Vec::new(),
        decls: Vec::new(),
        sources,
        namespace,
        spans: !module,
    };
    for line in LICENSE_HEADER {
        w.push(line);
    }
    w.push("");
    w.push("-- Generated by `anneal-spec-lower` from Rust `anneal::spec` items. Do not edit;");
    w.push("-- change the Rust specification and regenerate instead.");
    if module {
        w.push("module");
        w.push("prelude");
        w.push("public import Trusted.MirSemantics");
        w.push("public import Trusted.Framework.Bridge");
        w.push("");
        w.push("@[expose] public section");
    } else {
        w.push("prelude");
        w.push("import Trusted.MirSemantics");
        w.push("import Trusted.Framework.Bridge");
    }
    w.push("");
    w.push(&format!("namespace {namespace}"));
    w.push("");
    w.push("open Trusted.MirAst Trusted.MirSemantics Trusted.Framework");

    let any_max_steps = fns.iter().any(|(_, l)| l.max_steps.is_some());
    if runtime.val_int.get() {
        w.push("");
        w.runtime_def(
            "specInt",
            "/-- Mathematical value of an integer `Val` (`0` for any other value, which a\n\
             well-typed argument or return value never is). -/\n\
             noncomputable def specInt : Val → Int\n  \
             | .scalar _s__anneal => scalarAsInt _s__anneal\n  \
             | _ => 0",
        );
    }
    if runtime.val_nat.get() {
        w.push("");
        w.runtime_def(
            "specNat",
            "/-- Mathematical value of an unsigned integer `Val` as `Nat` (`0` for any\n\
             other or negative value, which a well-typed unsigned argument never is). -/\n\
             noncomputable def specNat : Val → Nat\n  \
             | .scalar _s__anneal => (scalarAsInt _s__anneal).toNat\n  \
             | _ => 0",
        );
    }
    if runtime.val_bool.get() {
        w.push("");
        w.runtime_def(
            "specBool",
            "/-- Payload of a `bool` `Val` (`false` for any other value, which a\n\
             well-typed argument or return value never is). -/\n\
             noncomputable def specBool : Val → Bool\n  \
             | .bool _b__anneal => _b__anneal\n  \
             | _ => false",
        );
    }
    if runtime.arg.get() {
        w.push("");
        w.runtime_def(
            "specArg",
            "/-- The `i`-th entry argument (`()` when absent, which `ValidEntryArgs` rules\n\
             out). -/\n\
             noncomputable def specArg (_q__anneal : Query) (_i__anneal : Nat) : Val :=\n  \
             match Trusted.MirSemantics.getElem? _q__anneal.args _i__anneal with\n  \
             | some _v__anneal => _v__anneal\n  \
             | none => .unit",
        );
    }
    let is_profile_v2 = capture.is_some_and(|c| c.mir_profile_version == 2);
    if any_max_steps {
        w.push("");
        if is_profile_v2 {
            w.runtime_def(
                "reachesDoneWithinV2",
                "/-- State `s` reaches `.done out` satisfying `post out` within at most `bound`\n\
                 Profile v2 MIR small steps (`StepV2`), without faulting. Bounds abstract MIR\n\
                 transitions, not physical wall-clock time or hardware cycles. -/\n\
                 noncomputable def reachesDoneWithinV2 (_p__anneal : Program)\n    \
                 (_post__anneal : TerminalOut → Prop) : Nat → State → Prop :=\n  \
                 @Nat.rec (fun _ => State → Prop)\n    \
                 (fun _ => False)\n    \
                 (fun _ _ih__anneal _s__anneal =>\n      \
                 (∃ _out__anneal : TerminalOut,\n        \
                 StepV2 _p__anneal _s__anneal (.done _out__anneal) ∧\n        \
                 _post__anneal _out__anneal) ∨\n      \
                 (∃ _sNext__anneal : State,\n        \
                 StepV2 _p__anneal _s__anneal (.step _sNext__anneal) ∧\n        \
                 _ih__anneal _sNext__anneal))",
            );
        } else {
            w.runtime_def(
                "reachesDoneWithin",
                "/-- State `s` reaches `.done out` satisfying `post out` within at most `bound`\n\
                 deterministic MIR small steps (`Step`), without faulting. Bounds abstract MIR\n\
                 transitions, not physical wall-clock time or hardware cycles. -/\n\
                 noncomputable def reachesDoneWithin (_p__anneal : Program)\n    \
                 (_post__anneal : TerminalOut → Prop) : Nat → State → Prop :=\n  \
                 @Nat.rec (fun _ => State → Prop)\n    \
                 (fun _ => False)\n    \
                 (fun _ _ih__anneal _s__anneal =>\n      \
                 (∃ _out__anneal : TerminalOut,\n        \
                 Step _p__anneal _s__anneal (.done _out__anneal) ∧\n        \
                 _post__anneal _out__anneal) ∨\n      \
                 (∃ _sNext__anneal : State,\n        \
                 Step _p__anneal _s__anneal (.step _sNext__anneal) ∧\n        \
                 _ih__anneal _sNext__anneal))",
            );
        }
        w.push("");
        w.runtime_def(
            "contractTerminalPost",
            "/-- Terminal-outcome predicate of `c : Trusted.Framework.FnContract` on entry\n\
             `q` (gating `.aborted` by `c.effects.noAbort = false`, `.unwound` by\n\
             `c.effects.noUnwind = false`, and checking `c.postReturn` on normal return). -/\n\
             noncomputable def contractTerminalPost\n    \
             (_c__anneal : Trusted.Framework.FnContract Query Val CallerMemory)\n    \
             (_q__anneal : Query) (_out__anneal : TerminalOut) : Prop :=\n  \
             match _out__anneal with\n  \
             | .returned _retOut__anneal =>\n    \
             _c__anneal.postReturn _q__anneal _retOut__anneal.ret _retOut__anneal.callerMem\n  \
             | .unwound _uwMem__anneal =>\n    \
             _c__anneal.effects.noUnwind = false ∧\n      \
             _c__anneal.postUnwind _q__anneal _uwMem__anneal\n  \
             | .aborted _abMem__anneal =>\n    \
             _c__anneal.effects.noAbort = false ∧\n      \
             _c__anneal.postAbort _q__anneal _abMem__anneal",
        );
        w.push("");
        if is_profile_v2 {
            w.runtime_def(
                "entrySatisfiesStepBoundV2",
                "/-- Bounded-step adequacy obligation for one `MirVerifiedEntry` under Profile\n\
                 v2: the body in `p` matching `identity` and `sig` initializes cleanly and\n\
                 reaches a contract-admissible terminal outcome within `bound q` Profile v2\n\
                 MIR small steps on every valid entry `q` in `c.effectiveBehaviorPre`. -/\n\
                 noncomputable def entrySatisfiesStepBoundV2 (_p__anneal : Program)\n    \
                 (_identity__anneal : String) (_sig__anneal : MirSignature)\n    \
                 (_c__anneal : Trusted.Framework.FnContract Query Val CallerMemory)\n    \
                 (_bound__anneal : Query → Nat) : Prop :=\n  \
                 ∃ (_defId__anneal : DefId) (_body__anneal : Body),\n    \
                 Trusted.MirSemantics.getElem? _p__anneal.bodies _defId__anneal =\n      \
                 some _body__anneal ∧\n    \
                 stringBeq _body__anneal.identity _identity__anneal = true ∧\n    \
                 bodyMatchesMirSignature _body__anneal _sig__anneal = true ∧\n    \
                 ∀ _q__anneal : Query,\n      \
                 ValidEntryArgsV2 _body__anneal _q__anneal →\n      \
                 _c__anneal.effectiveBehaviorPre _body__anneal.isUnsafe _q__anneal →\n      \
                 ∃ _s0__anneal : State,\n        \
                 initStateV2 (entryProgForBody _p__anneal _defId__anneal)\n          \
                 _q__anneal = .ok _s0__anneal ∧\n        \
                 reachesDoneWithinV2 (entryProgForBody _p__anneal _defId__anneal)\n          \
                 (contractTerminalPost _c__anneal _q__anneal)\n          \
                 (_bound__anneal _q__anneal) _s0__anneal",
            );
        } else {
            w.runtime_def(
                "entrySatisfiesStepBoundV1",
                "/-- Bounded-step adequacy obligation for one `MirVerifiedEntry` under Profile\n\
                 v1: the body in `p` matching `identity` and `sig` initializes cleanly and\n\
                 reaches a contract-admissible terminal outcome within `bound { args := args }`\n\
                 MIR small steps on every valid entry in `c.effectiveBehaviorPre`. -/\n\
                 noncomputable def entrySatisfiesStepBoundV1 (_p__anneal : Program)\n    \
                 (_identity__anneal : String) (_sig__anneal : MirSignature)\n    \
                 (_c__anneal : Trusted.Framework.FnContract Query Val CallerMemory)\n    \
                 (_bound__anneal : Query → Nat) : Prop :=\n  \
                 ∃ (_defId__anneal : DefId) (_body__anneal : Body),\n    \
                 Trusted.MirSemantics.getElem? _p__anneal.bodies _defId__anneal =\n      \
                 some _body__anneal ∧\n    \
                 stringBeq _body__anneal.identity _identity__anneal = true ∧\n    \
                 bodyMatchesMirSignature _body__anneal _sig__anneal = true ∧\n    \
                 ∀ _args__anneal : List Val,\n      \
                 ValidEntryArgs _body__anneal _args__anneal →\n      \
                 _c__anneal.effectiveBehaviorPre _body__anneal.isUnsafe\n        \
                 { args := _args__anneal } →\n      \
                 ∃ _s0__anneal : State,\n        \
                 initState (entryProgForBody _p__anneal _defId__anneal)\n          \
                 { args := _args__anneal } = .ok _s0__anneal ∧\n        \
                 reachesDoneWithin (entryProgForBody _p__anneal _defId__anneal)\n          \
                 (contractTerminalPost _c__anneal { args := _args__anneal })\n          \
                 (_bound__anneal { args := _args__anneal }) _s0__anneal",
            );
        }
    }
    for (h, body) in helpers {
        let params: Vec<String> = h
            .params
            .iter()
            .map(|p| format!("({} : {})", lean_ident(&p.name), lean_ty(p.ty)))
            .collect();
        let sep = if params.is_empty() { "" } else { " " };
        w.push("");
        let decl = format!(
            "{}\nnoncomputable def pure_{}{sep}{} : {} :=\n  {body}",
            doc_comment(&format!("`#[anneal::pure]` helper `{}`.", doc_text(&h.name))),
            h.name,
            params.join(" "),
            lean_ty(h.ret),
        );
        w.decl(&format!("pure_{}", h.name), &decl, h.file, h.span);
    }

    let mut closure_entries = Vec::new();
    let mut lean_entries = Vec::new();
    let mut gap_lean_prefix = Vec::new();
    let mut gap_tags = Vec::new();

    if scope == Scope::Unit {
        gap_lean_prefix.push(".selectedUnitScope".to_string());
        gap_tags.push("selectedUnitScope".to_string());
    }
    if let Some(cap) = capture {
        if cap.mir_profile_version == 2 {
            gap_lean_prefix.push(".unbridgedSemantics \"mir_profile_v2\"".to_string());
            gap_tags.push("unbridgedSemantics(mir_profile_v2)".to_string());
            gap_lean_prefix.push(".callerMemoryThreadIsolation \"mir_profile_v2\"".to_string());
            gap_tags.push("callerMemoryThreadIsolation(mir_profile_v2)".to_string());
            if cap.bodies.iter().any(|b| b.has_raw_ptr_local) {
                gap_lean_prefix.push(".callerRawPtrAliasing \"mir_profile_v2\"".to_string());
                gap_tags.push("callerRawPtrAliasing(mir_profile_v2)".to_string());
            }
        }
    }

    for (k, (f, l)) in fns.iter().enumerate() {
        let full_id = format!("rust-path-v1::{}", f.path);
        let sig_doc = signature(f);
        w.push("");
        let id = format!(
            "{}\ndef fn{k}_id : String :=\n  {}",
            doc_comment(&format!("`{}`", doc_text(&sig_doc))),
            lean_string(&full_id)
        );
        w.decl(&format!("fn{k}_id"), &id, f.file, f.sig_span);

        w.push("");
        let sig_decl = format!(
            "{}\ndef fn{k}_sig : MirSignature :=\n  {}",
            doc_comment(&format!("MIR signature of `{}`.", doc_text(&f.path))),
            mir_signature_record(f)
        );
        w.decl(&format!("fn{k}_sig"), &sig_decl, f.file, f.sig_span);

        let clause_span = |pick: &dyn Fn(&crate::ast::Clause) -> bool| {
            f.clauses
                .iter()
                .filter(|c| pick(&c.clause))
                .map(|c| c.span)
                .reduce(|a, b| a.join(b).unwrap_or(a))
                .unwrap_or(f.attr_span)
        };
        use crate::ast::Clause as C;
        if let Some(p) = &l.safety_pre {
            w.push("");
            let decl = format!(
                "{}\nnoncomputable def fn{k}_safety (_q__anneal : Query) : Prop :=\n  {p}",
                doc_comment(&format!("Caller safety obligation of `{}`.", doc_text(&f.path))),
            );
            let span = clause_span(&|c| matches!(c, C::Requires(_) | C::SafetyRequires(_)));
            w.decl(&format!("fn{k}_safety"), &decl, f.file, span);
        }
        if let Some(p) = &l.behavior_pre {
            w.push("");
            let decl = format!(
                "{}\nnoncomputable def fn{k}_pre (_q__anneal : Query) : Prop :=\n  {p}",
                doc_comment(&format!("Behavioral precondition of `{}`.", doc_text(&f.path))),
            );
            w.decl(
                &format!("fn{k}_pre"),
                &decl,
                f.file,
                clause_span(&|c| matches!(c, C::Requires(_))),
            );
        }
        if let Some(p) = &l.post {
            w.push("");
            let decl = format!(
                "{}\nnoncomputable def fn{k}_post (_q__anneal : Query) (_ret__anneal : Val)\n    \
                 (_mem__anneal : CallerMemory) : Prop :=\n  {p}",
                doc_comment(&format!("Normal-return postcondition of `{}`.", doc_text(&f.path))),
            );
            w.decl(
                &format!("fn{k}_post"),
                &decl,
                f.file,
                clause_span(&|c| matches!(c, C::Ensures { .. })),
            );
        }
        if let Some(ms) = &l.max_steps {
            w.push("");
            let decl = format!(
                "{}\nnoncomputable def fn{k}_max_steps (_q__anneal : Query) : Nat :=\n  {ms}",
                doc_comment(&format!(
                    "Deterministic MIR small-step bound of `{}` (abstract `Step` transitions, \
                     not physical wall-clock time).",
                    doc_text(&f.path)
                )),
            );
            w.decl(
                &format!("fn{k}_max_steps"),
                &decl,
                f.file,
                clause_span(&|c| matches!(c, C::MaxSteps(_))),
            );
        }
        let mut fields = Vec::new();
        if l.safety_pre.is_some() {
            fields.push(format!("  safetyPre := fn{k}_safety"));
        }
        if l.behavior_pre.is_some() {
            fields.push(format!("  behaviorPre := fn{k}_pre"));
        }
        if l.post.is_some() {
            fields.push(format!("  postReturn := fn{k}_post"));
        }
        fields.push(format!(
            "  effects := {{ terminates := {}, noUnwind := {}, noAbort := true }}",
            l.terminates, l.no_unwind
        ));
        w.push("");
        let decl = format!(
            "noncomputable def fn{k}_contract :\n    \
             Trusted.Framework.FnContract Query Val CallerMemory := {{\n{}\n}}",
            fields.join("\n")
        );
        w.decl(&format!("fn{k}_contract"), &decl, f.file, f.attr_span);

        let require_inhabited = f.vacuous_ok.is_none();
        if let Some(reason) = &f.vacuous_ok {
            let reason = reason.split_whitespace().collect::<Vec<_>>().join(" ");
            gap_lean_prefix.push(format!(".waivedInhabitation fn{k}_id"));
            gap_tags.push(format!("waivedInhabitation({full_id})"));
            lean_entries.push((
                Some(format!("    -- vacuous_ok: {reason}")),
                format!(
                    "    {{ identity := fn{k}_id, sig := fn{k}_sig, contract := fn{k}_contract, \
                     requireInhabited := false }}"
                ),
            ));
        } else {
            lean_entries.push((
                None,
                format!(
                    "    {{ identity := fn{k}_id, sig := fn{k}_sig, contract := fn{k}_contract }}"
                ),
            ));
        }

        closure_entries.push(ClosureEntry {
            identity: full_id,
            signature: sig_doc,
            is_unsafe: f.is_unsafe,
            safety_pre: l.safety_pre.clone(),
            behavior_pre: l.behavior_pre.clone(),
            post_return: l.post.clone(),
            max_steps: l.max_steps.clone(),
            terminates: l.terminates,
            no_unwind: l.no_unwind,
            no_abort: true,
            require_inhabited,
        });
    }

    for (m, callee) in unannotated_safe_callees.iter().enumerate() {
        let sig_str = captured_mir_signature_record(callee);
        let short_path = callee.identity.strip_prefix("rust-path-v1::").unwrap_or(&callee.identity);
        w.push("");
        w.runtime_def(
            &format!("callee{m}_id"),
            &format!(
                "{}\ndef callee{m}_id : String :=\n  {}",
                doc_comment(&format!(
                    "Unannotated safe callee `{}` (default UB-freedom entry).",
                    doc_text(short_path)
                )),
                lean_string(&callee.identity),
            ),
        );
        w.push("");
        w.runtime_def(
            &format!("callee{m}_sig"),
            &format!(
                "{}\ndef callee{m}_sig : MirSignature :=\n  {sig_str}",
                doc_comment(&format!("Captured MIR signature of `{}`.", doc_text(short_path))),
            ),
        );
        w.push("");
        w.runtime_def(
            &format!("callee{m}_contract"),
            &format!(
                "noncomputable def callee{m}_contract :\n    \
                 Trusted.Framework.FnContract Query Val CallerMemory := {{\n  \
                 effects := {{ terminates := false, noUnwind := false, noAbort := false }}\n}}"
            ),
        );
        lean_entries.push((
            None,
            format!(
                "    {{ identity := callee{m}_id, sig := callee{m}_sig, \
                 contract := callee{m}_contract }}"
            ),
        ));
        closure_entries.push(ClosureEntry {
            identity: callee.identity.clone(),
            signature: format!("fn {short_path}"),
            is_unsafe: false,
            safety_pre: None,
            behavior_pre: None,
            post_return: None,
            max_steps: None,
            terminates: false,
            no_unwind: false,
            no_abort: false,
            require_inhabited: true,
        });
    }

    for tag in DOWNSTREAM_GAP_TAGS {
        gap_tags.push((*tag).to_string());
    }

    let any_terminates = closure_entries.iter().any(|e| e.terminates);
    let (claim_shapes_lean, claim_shapes_tags): (&str, &[&str]) = if any_terminates {
        ("[.forallSafety, .termination]", &["forallSafety", "termination"])
    } else {
        ("[.forallSafety]", &["forallSafety"])
    };

    let gaps_lean = if gap_lean_prefix.is_empty() {
        "defaultMirDownstreamGaps".to_string()
    } else {
        format!("{} :: defaultMirDownstreamGaps", gap_lean_prefix.join(" :: "))
    };

    let mut formatted_entries = Vec::new();
    let total_entries = lean_entries.len();
    for (idx, (comment, item)) in lean_entries.into_iter().enumerate() {
        let sep = if idx + 1 == total_entries { "" } else { "," };
        if let Some(c) = comment {
            formatted_entries.push(c);
        }
        formatted_entries.push(format!("{item}{sep}"));
    }

    let mut spec_fields = vec![
        format!("  entries := [\n{}\n  ]", formatted_entries.join("\n")),
        format!("  claimShapes := {claim_shapes_lean}"),
        format!("  gaps := {gaps_lean}"),
        "  laws := []".to_string(),
    ];
    if any_max_steps {
        let step_helper =
            if is_profile_v2 { "entrySatisfiesStepBoundV2" } else { "entrySatisfiesStepBoundV1" };
        let mut step_items = Vec::new();
        for (k, (_, l)) in fns.iter().enumerate() {
            if l.max_steps.is_some() {
                step_items.push(format!(
                    "    {step_helper} _p__anneal fn{k}_id fn{k}_sig fn{k}_contract \
                     fn{k}_max_steps"
                ));
            }
        }
        spec_fields
            .push(format!("  stepBounds := fun _p__anneal => [\n{}\n  ]", step_items.join(",\n")));
    }

    w.push("");
    w.runtime_def(
        "specs",
        &format!("noncomputable def specs : MirEnvelopeSpec := {{\n{}\n}}", spec_fields.join("\n")),
    );
    w.push("");
    w.push(&format!("end {namespace}"));
    if module {
        w.push("");
        w.push("end");
    }

    let spec_closure = render_spec_closure_golden(
        lean_module,
        &w.text,
        &w.decls,
        &closure_entries,
        claim_shapes_tags,
        &gap_tags,
        any_max_steps,
    );

    if module {
        return Lowered { spec_lean: w.text, span_map: String::new(), spec_closure, module_path };
    }
    let map = json!({
        "schema_version": 1,
        "columns": "1-based Unicode scalar values",
        "entries": w.entries,
    });
    let mut span_map = serde_json::to_string_pretty(&map).expect("span map serializes");
    span_map.push('\n');
    Lowered { spec_lean: w.text, span_map, spec_closure, module_path }
}
