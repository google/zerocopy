// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Lean rendering of captured types, lists, identities, and the
//! `AutoScaffold` module itself.

use std::fmt::Write as _;

use serde_json::Value;

use super::{hypothesis_name, BodyInfo, Profile};

fn json_bool(value: &Value, name: &str) -> Result<bool, String> {
    value.get(name).and_then(Value::as_bool).ok_or_else(|| format!("type has no boolean `{name}`"))
}

fn int_width(value: &Value, name: &str) -> Result<&'static str, String> {
    match value.get(name).and_then(Value::as_str) {
        Some("i8") => Ok("i8"),
        Some("i16") => Ok("i16"),
        Some("i32") => Ok("i32"),
        Some("i64") => Ok("i64"),
        Some("i128") => Ok("i128"),
        Some("isize") => Ok("isize"),
        other => Err(format!("unknown integer width {other:?}")),
    }
}

fn mutability(value: &Value) -> Result<&'static str, String> {
    match value.get("mutability").and_then(Value::as_str) {
        Some("shared") => Ok("shared"),
        Some("mut") => Ok("mut"),
        other => Err(format!("unknown mutability {other:?}")),
    }
}

fn boxed(value: &Value, name: &str) -> Result<String, String> {
    lean_ty(value.get(name).ok_or_else(|| format!("type has no `{name}`"))?)
}

/// Captured type kinds without fields, each with the `MirTy` constructor the
/// capture's Lean emitter renders it as.
const NULLARY_TYS: &[(&str, &str)] = &[
    ("bool", "bool"),
    ("char", "char"),
    ("ordering", "ordering"),
    ("unit", "unit"),
    ("never", "never"),
    ("str", "str"),
];

/// Captured type kinds whose only field is one type, each with that field and
/// the `MirTy` constructor the capture's Lean emitter applies to it.
const WRAPPER_TYS: &[(&str, &str, &str)] = &[
    ("slice", "elem", "slice"),
    ("vec", "elem", "vec"),
    ("box", "pointee", "box"),
    ("range_to", "elem", "rangeTo"),
    ("range_from", "elem", "rangeFrom"),
    ("range", "elem", "range"),
    ("option", "elem", "option"),
];

fn lookup(table: &[(&str, &'static str)], kind: &str) -> Option<&'static str> {
    table.iter().find(|(k, _)| *k == kind).map(|(_, ctor)| *ctor)
}

/// Render a captured type as the `Trusted.MirAst.MirTy` term that the
/// capture's own Lean emitter produces for it.
pub(super) fn lean_ty(ty: &Value) -> Result<String, String> {
    let kind = ty.get("kind").and_then(Value::as_str).ok_or("type has no kind")?;
    if let Some(ctor) = lookup(NULLARY_TYS, kind) {
        return Ok(format!("MirTy.{ctor}"));
    }
    if let Some(&(_, field, ctor)) = WRAPPER_TYS.iter().find(|(k, _, _)| *k == kind) {
        return Ok(format!("(MirTy.{ctor} {})", boxed(ty, field)?));
    }
    Ok(match kind {
        "int" => {
            format!("(MirTy.int IntWidth.{} {})", int_width(ty, "width")?, json_bool(ty, "signed")?)
        }
        "overflow_pair" => format!(
            "(MirTy.tuple [(MirTy.int IntWidth.{} {}), MirTy.bool])",
            int_width(ty, "width")?,
            json_bool(ty, "signed")?
        ),
        "tuple" => {
            let fields = ty.get("fields").and_then(Value::as_array).ok_or("tuple has no fields")?;
            let fields = fields.iter().map(lean_ty).collect::<Result<Vec<_>, _>>()?;
            format!("(MirTy.tuple {})", lean_list(&fields))
        }
        "ref" => format!("(MirTy.ref Mutability.{} {})", mutability(ty)?, boxed(ty, "pointee")?),
        "raw_ptr" => {
            format!("(MirTy.rawPtr Mutability.{} {})", mutability(ty)?, boxed(ty, "pointee")?)
        }
        "array" => {
            let len = ty.get("len").and_then(Value::as_u64).ok_or("array has no len")?;
            format!("(MirTy.array {} {len})", boxed(ty, "elem")?)
        }
        "enum" => {
            let id = ty.get("id").and_then(Value::as_u64).ok_or("enum has no id")?;
            let tag = ty.get("tag_repr").ok_or("enum has no tag_repr")?;
            let tag = match tag.get("kind").and_then(Value::as_str) {
                Some("zero_sized") => "EnumTagRepr.zeroSized".to_owned(),
                Some("scalar") => format!(
                    "(EnumTagRepr.scalar IntWidth.{} {})",
                    int_width(tag, "width")?,
                    json_bool(tag, "signed")?
                ),
                other => return Err(format!("unknown enum tag_repr {other:?}")),
            };
            let discriminants =
                ty.get("discriminants").and_then(Value::as_array).ok_or("enum discriminants")?;
            let discriminants = discriminants
                .iter()
                .map(|d| {
                    d.as_str()
                        .filter(|s| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()))
                        .map(str::to_owned)
                        .ok_or_else(|| "enum discriminant is not a decimal string".to_owned())
                })
                .collect::<Result<Vec<_>, _>>()?;
            format!(
                "(MirTy.enum {{ id := {id}, discrWidth := IntWidth.{}, discrSigned := {}, \
                 tagRepr := {tag}, discriminants := {} }})",
                int_width(ty, "discr_width")?,
                json_bool(ty, "discr_signed")?,
                lean_list(&discriminants)
            )
        }
        other => return Err(format!("unknown type kind `{other}`")),
    })
}

/// The most elements in one Lean list literal, as in the capture's emitter.
pub(super) const MAX_LIST_CHUNK_LEN: usize = 16;

/// Render `items` as a Lean list the way the capture's emitter (`list` in
/// `rustc-capture/src/lean.rs`) does: a literal of at most
/// [`MAX_LIST_CHUNK_LEN`] elements, or a balanced tree of
/// `_root_.List.append` over such literals. A long flat literal expands into
/// nested `let`s that exceed Lean's `maxRecDepth`, while the tree keeps the
/// term's depth logarithmic and is definitionally equal to the flat list.
pub(super) fn lean_list(items: &[String]) -> String {
    fn join(chunks: &[&[String]]) -> String {
        match chunks {
            [] => "[]".to_owned(),
            [leaf] => format!("[{}]", leaf.join(", ")),
            _ => {
                let (left, right) = chunks.split_at(chunks.len() / 2);
                format!("(_root_.List.append {} {})", join(left), join(right))
            }
        }
    }
    let chunks: Vec<&[String]> = items.chunks(MAX_LIST_CHUNK_LEN).collect();
    join(&chunks)
}

/// Render `s` exactly as the capture's Lean emitter renders a body identity:
/// a balanced tree of `Trusted.MirAst.stringAppend` over `String.ofList`
/// leaves of at most 16 numeric `Char`s. A string literal would force Lean to
/// unfold it character by character when comparing it with the captured
/// identity, which exceeds `maxRecDepth` on long identities; matching the
/// captured term keeps `identity_eq` a cheap definitional unfolding.
pub(super) fn lean_identity(s: &str) -> String {
    fn join(chunks: &[&[char]]) -> String {
        match chunks {
            [] => "(_root_.String.ofList [])".to_owned(),
            [leaf] => {
                let chars: Vec<String> =
                    leaf.iter().map(|c| format!("(_root_.Char.ofNat {})", u32::from(*c))).collect();
                format!("(_root_.String.ofList [{}])", chars.join(", "))
            }
            _ => {
                let (left, right) = chunks.split_at(chunks.len() / 2);
                format!("(Trusted.MirAst.stringAppend {} {})", join(left), join(right))
            }
        }
    }
    let chars: Vec<char> = s.chars().collect();
    let chunks: Vec<&[char]> = chars.chunks(MAX_LIST_CHUNK_LEN).collect();
    join(&chunks)
}

/// Render `s` for a Lean doc comment, escaping the comment delimiters and
/// non-ASCII characters.
pub(super) fn doc_text(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '`' => out.push('\''),
            ' '..='~' => out.push(c),
            _ => {
                let _ = write!(out, "\\u{{{:x}}}", c as u32);
            }
        }
    }
    out.replace("-/", "- /").replace("/-", "/ -")
}

const HEADER: &str = "\
-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- Generated by anneal-scaffold from capture.json. Do not edit; regenerate
-- after the capture changes, and check with `anneal-scaffold --check`.

module
prelude
public import Captured
public import Trusted.MirSemantics

@[expose] public section

";

pub(super) fn render_module(module: &str, profile: Profile, infos: &[BodyInfo]) -> String {
    let mut out = String::from(HEADER);
    let _ = writeln!(out, "namespace {module}\n");
    out.push_str("open Trusted.MirAst Trusted.MirSemantics\n\n");
    for info in infos {
        render_body(&mut out, profile, info);
    }
    render_bodies_verified(&mut out, profile, infos);
    let _ = writeln!(out, "end {module}\n\nend");
    out
}

fn render_body(out: &mut String, profile: Profile, info: &BodyInfo) {
    let BodyInfo { index, identity, slug, is_unsafe, params, fuel } = info;
    let _ = writeln!(
        out,
        "/-! ### `{}` -/\n\nnamespace {slug}\n\n\
         /-- The `DefId` of this body in `Captured.program`. -/\n\
         abbrev defId : DefId := {index}\n\n\
         /-- This body. -/\n\
         abbrev body : Body := Captured.body_{index}\n\n\
         /-- This body's identity, `{}`, in the form the capture emits it. -/\n\
         abbrev identity : String :=\n  {}\n\n\
         theorem found :\n    Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body :=\n  rfl\n\n\
         theorem identity_eq : body.identity = identity := rfl\n\n\
         theorem isUnsafe_eq : body.isUnsafe = {is_unsafe} := rfl\n\n\
         theorem admitted : {} Captured.program body = true := rfl\n\n\
         theorem params :\n    (body.locals.drop 1).take body.argumentCount =\n      {} :=\n  rfl\n",
        doc_text(identity),
        doc_text(identity),
        lean_identity(identity),
        profile.admitted,
        lean_list(params),
    );
    if let Some(fuel) = fuel {
        let _ = writeln!(
            out,
            "/-- The number of statements and terminators in this acyclic body, which\n\
             bounds the steps of any single-frame run of it. -/\n\
             abbrev fuel : Nat := {fuel}\n"
        );
    }
    let _ = writeln!(out, "end {slug}\n");
}

/// A conjunction of one proposition per body, folded over the body list as
/// `Anneal.MirWp.BodiesVerified` does, so that one anonymous constructor in
/// body order discharges it and its size grows linearly with the body count.
/// It folds with `List.foldr` rather than recursing by pattern matching, which
/// would make Lean emit an `unsafe` `_unsafe_rec` helper.
const ALL_BODIES: &str = "\
/-- `P` holds for each body of `bs`, at its `DefId` counted from `idx`. -/
def AllBodies (P : DefId → Body → Prop) (idx : Nat) (bs : List Body) : Prop :=
  bs.foldr (fun body ih curIdx => P curIdx body ∧ ih (curIdx + 1)) (fun _ => True) idx

theorem allBodies_getElem {P : DefId → Body → Prop} :
    ∀ {idx : Nat} {bs : List Body}, AllBodies P idx bs →
      ∀ (k : Nat) (b : Body), Trusted.MirSemantics.getElem? bs k = some b → P (idx + k) b
  | _, [], _, _, _, hGet => by cases hGet
  | idx, _ :: _, hBs, 0, b, hGet => by
    injection hGet with hEq
    subst hEq
    rw [Nat.add_zero]
    exact hBs.1
  | idx, _ :: _, hBs, k + 1, b, hGet => by
    have hSub := allBodies_getElem hBs.2 k b hGet
    have hIdx : idx + 1 + k = idx + (k + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 k]
    rw [← hIdx]
    exact hSub

";

fn render_bodies_verified(out: &mut String, profile: Profile, infos: &[BodyInfo]) {
    let Profile { specs, body_verified, .. } = profile;
    out.push_str(ALL_BODIES);
    let _ = writeln!(
        out,
        "/-- The per-body obligation of `ProgramVerified`, from one hypothesis per\n\
         body named `h_<slug>`. Pass the hypotheses by name, in any order. -/\n\
         theorem bodiesVerified {{specs : {specs}}}"
    );
    for info in infos {
        let slug = &info.slug;
        let _ = writeln!(
            out,
            "    ({} :\n      {body_verified} Captured.program {slug}.defId {slug}.body\n        \
             (specs.safety {slug}.body.identity))",
            hypothesis_name(slug),
        );
    }
    let _ = writeln!(
        out,
        "    : ∀ (defId : DefId) (body : Body),\n      \
         Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body →\n      \
         {body_verified} Captured.program defId body (specs.safety body.identity) := by\n  \
         have hAll : AllBodies\n      \
         (fun defId body => {body_verified} Captured.program defId body\n        \
         (specs.safety body.identity))\n      \
         0 Captured.program.bodies := ⟨"
    );
    let mut by_index: Vec<&BodyInfo> = infos.iter().collect();
    by_index.sort_by_key(|info| info.index);
    for info in &by_index {
        let _ = writeln!(out, "    {},", hypothesis_name(&info.slug));
    }
    let _ = writeln!(
        out,
        "    True.intro⟩\n  \
         intro defId body hBody\n  \
         have h := allBodies_getElem hAll defId body hBody\n  \
         rw [Nat.zero_add] at h\n  \
         exact h\n"
    );
}
