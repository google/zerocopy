// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Deterministic `Spec.lean` and `spec_span_map.json` emission.
//!
//! `Spec.lean` carries no Rust line or column information, so reformatting
//! the Rust source leaves its bytes (and every proof cache keyed on them)
//! unchanged. Source positions live only in the sideband span map.

use proc_macro2::Span;
use serde_json::{json, Value};

use crate::{
    ast::{PureFn, SpecFn, Ty},
    check::{lean_ident, LoweredFn, Uses, INT, VAL},
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

/// The generated outputs of one specification unit.
pub struct Lowered {
    pub spec_lean: String,
    /// Pretty-printed `spec_span_map.json`, ending in a newline.
    pub span_map: String,
}

struct Writer<'a> {
    text: String,
    line: usize,
    entries: Vec<Value>,
    sources: &'a [Source],
}

impl Writer<'_> {
    fn push(&mut self, s: &str) {
        self.text.push_str(s);
        self.text.push('\n');
        self.line += s.matches('\n').count() + 1;
    }

    /// Emits `decl` (one or more lines) and records its Rust provenance.
    fn decl(&mut self, name: &str, decl: &str, file: usize, span: Span) {
        let start = self.line;
        self.push(decl);
        let src = &self.sources[file];
        let s = SourceMap::new(&src.text).span(span);
        self.entries.push(json!({
            "lean_decl": format!("Spec.{name}"),
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

fn binder(used: bool, name: &str) -> String {
    if used {
        name.to_string()
    } else {
        format!("_{name}")
    }
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

fn contract_signature(f: &SpecFn) -> String {
    let params: Vec<String> = f.params.iter().map(|p| mir_ty(p.ty)).collect();
    format!(
        "some {{ isUnsafe := {}, params := [{}], ret := {} }}",
        f.is_unsafe,
        params.join(", "),
        mir_ty(f.ret),
    )
}

fn signature(f: &SpecFn) -> String {
    let params: Vec<String> =
        f.params.iter().map(|p| format!("{}: {}", p.name, p.ty.describe())).collect();
    let unsafety = if f.is_unsafe { "unsafe " } else { "" };
    format!("{unsafety}fn {}({}) -> {}", f.path, params.join(", "), f.ret.describe())
}

pub fn emit(
    sources: &[Source],
    helpers: &[(&PureFn, String)],
    fns: &[(&SpecFn, LoweredFn)],
    runtime: &Uses,
) -> Lowered {
    let mut w = Writer { text: String::new(), line: 1, entries: Vec::new(), sources };
    for line in LICENSE_HEADER {
        w.push(line);
    }
    w.push("");
    w.push("-- Generated by `anneal-spec-lower` from Rust `anneal::spec` items. Do not edit;");
    w.push("-- change the Rust specification and regenerate instead.");
    w.push("prelude");
    w.push("import Trusted.MirSemantics");
    w.push("");
    w.push("namespace Spec");
    w.push("");
    w.push("open Trusted.MirAst Trusted.MirSemantics");
    if runtime.val_int.get() {
        w.push("");
        w.push(
            "/-- Mathematical value of an integer `Val` (`0` for any other value, which a\n\
             well-typed argument or return value never is). -/\n\
             noncomputable def specInt : Val → Int\n  \
             | .scalar s => scalarAsInt s\n  \
             | _ => 0",
        );
    }
    if runtime.val_bool.get() {
        w.push("");
        w.push(
            "/-- Payload of a `bool` `Val` (`false` for any other value, which a\n\
             well-typed argument or return value never is). -/\n\
             noncomputable def specBool : Val → Bool\n  \
             | .bool b => b\n  \
             | _ => false",
        );
    }
    if runtime.arg.get() {
        w.push("");
        w.push(
            "/-- The `i`-th entry argument (`()` when absent, which `ValidEntryArgs` rules\n\
             out). -/\n\
             noncomputable def specArg (q : Query) (i : Nat) : Val :=\n  \
             match Trusted.MirSemantics.getElem? q.args i with\n  \
             | some v => v\n  \
             | none => .unit",
        );
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
    for (k, (f, l)) in fns.iter().enumerate() {
        w.push("");
        let id = format!(
            "{}\ndef fn{k}_id : String :=\n  {}",
            doc_comment(&format!("`{}`", doc_text(&signature(f)))),
            lean_string(&format!("rust-path-v1::{}", f.path))
        );
        w.decl(&format!("fn{k}_id"), &id, f.file, f.sig_span);
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
                "{}\nnoncomputable def fn{k}_safety ({} : Query) : Prop :=\n  {p}",
                doc_comment(&format!("Caller safety obligation of `{}`.", doc_text(&f.path))),
                binder(l.uses_safety_q, "q"),
            );
            let span = clause_span(&|c| matches!(c, C::Requires(_) | C::SafetyRequires(_)));
            w.decl(&format!("fn{k}_safety"), &decl, f.file, span);
        }
        if let Some(p) = &l.behavior_pre {
            w.push("");
            let decl = format!(
                "{}\nnoncomputable def fn{k}_pre ({} : Query) : Prop :=\n  {p}",
                doc_comment(&format!("Behavioral precondition of `{}`.", doc_text(&f.path))),
                binder(l.uses_pre_q, "q"),
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
                "{}\nnoncomputable def fn{k}_post ({} : Query) ({} : Out) : Prop :=\n  {p}",
                doc_comment(&format!("Normal-return postcondition of `{}`.", doc_text(&f.path))),
                binder(l.uses_post_q, "q"),
                binder(l.uses_post_out, "out"),
            );
            w.decl(
                &format!("fn{k}_post"),
                &decl,
                f.file,
                clause_span(&|c| matches!(c, C::Ensures { .. })),
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
            "  effects := {{ terminates := {}, noUnwind := {} }}",
            l.terminates, l.no_unwind
        ));
        w.push("");
        let decl = format!(
            "noncomputable def fn{k}_contract : FnContract := {{\n{}\n}}",
            fields.join("\n")
        );
        w.decl(&format!("fn{k}_contract"), &decl, f.file, f.attr_span);
    }
    w.push("");
    let mut entries = Vec::new();
    for (k, (f, _)) in fns.iter().enumerate() {
        let sep = if k + 1 == fns.len() { "" } else { "," };
        let sig = contract_signature(f);
        if let Some(reason) = &f.vacuous_ok {
            let reason = reason.split_whitespace().collect::<Vec<_>>().join(" ");
            entries.push(format!("  -- vacuous_ok: {reason}"));
            entries.push(format!(
                "  {{ identity := fn{k}_id, contract := fn{k}_contract, signature := {sig}, requireInhabited := false }}{sep}"
            ));
        } else {
            entries.push(format!(
                "  {{ identity := fn{k}_id, contract := fn{k}_contract, signature := {sig} }}{sep}"
            ));
        }
    }
    w.push(&format!(
        "noncomputable def specs : Specs := ContractSpecs [\n{}\n]",
        entries.join("\n")
    ));
    w.push("");
    w.push("end Spec");
    let map = json!({
        "schema_version": 1,
        "columns": "1-based Unicode scalar values",
        "entries": w.entries,
    });
    let mut span_map = serde_json::to_string_pretty(&map).expect("span map serializes");
    span_map.push('\n');
    Lowered { spec_lean: w.text, span_map }
}
