// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Render an identity-keyed `AutoScaffold.lean` from a capture's
//! `capture.json`.
//!
//! A hand-written `Proof.lean` that names `Captured.body_3` or `DefId` `3`
//! breaks whenever the captured bodies are reordered, even though nothing it
//! proves has changed. The scaffold moves every index-dependent fact into a
//! generated module and names each body by its identity instead:
//!
//! - one namespace per body, `AutoScaffold.b_<slug>`, holding its `defId`,
//!   `body`, `identity`, the lookup lemma `found`, `identity_eq`,
//!   `isUnsafe_eq`, the static admission lemma `admitted`, the parameter types
//!   `params`, and, for an acyclic body, `fuel`, the number of its statements
//!   and terminators;
//! - `bodiesVerified`, which turns one identity-named hypothesis per body
//!   into the universal per-body obligation of `ProgramVerified` (or
//!   `ProgramVerifiedV2`), so proofs can pass hypotheses by name in any order.
//!
//! The scaffold is an ordinary proof module, so it adds no trust. Its facts
//! about the capture are proved by `rfl`, so a stale or wrong scaffold fails
//! to elaborate; `bodiesVerified` rests on the generic `allBodies_getElem`,
//! proved by case analysis on the body list. The output depends only on the
//! capture, and bodies appear sorted by slug, so reordering bodies changes
//! only the indices inside the scaffold.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Write as _,
};

use serde_json::Value;

/// The `capture.json` schema version this renderer understands.
pub const SCHEMA_VERSION: u64 = 5;

/// The prefix of every captured body identity.
const IDENTITY_PREFIX: &str = "rust-path-v1::";

/// An error that makes the capture unusable for scaffolding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error(pub String);

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for Error {}

fn err(message: impl Into<String>) -> Error {
    Error(message.into())
}

/// The Profile-dependent names used by the scaffold.
#[derive(Clone, Copy)]
struct Profile {
    admitted: &'static str,
    specs: &'static str,
    body_verified: &'static str,
}

const PROFILE_V1: Profile =
    Profile { admitted: "BodyStaticAdmitted", specs: "Specs", body_verified: "BodyVerified" };

const PROFILE_V2: Profile =
    Profile { admitted: "BodyStaticAdmittedV2", specs: "SpecsV2", body_verified: "BodyVerifiedV2" };

/// One captured body, as the scaffold needs it.
struct BodyInfo {
    index: usize,
    identity: String,
    slug: String,
    is_unsafe: bool,
    params: Vec<String>,
    fuel: Option<usize>,
}

/// The module roots that `cargo anneal verify` refuses for authored proof
/// modules (`reserved_proof_module` in `trusted/cargo-anneal/src/verify.rs`):
/// the installed model and theory, the captured subject and generated claim,
/// and the Lean toolchain and inspector.
const RESERVED_MODULE_ROOTS: &[&str] = &[
    "Captured",
    "Expected",
    "Trusted",
    "Anneal",
    "Init",
    "Std",
    "Lean",
    "Lake",
    "TrustedBoundary",
    "SpecPreflight",
];

/// Check that `module` is a dotted Lean module name whose components are
/// ASCII identifiers starting with an uppercase letter, and whose root is not
/// one that `cargo anneal verify` reserves.
pub fn validate_module_name(module: &str) -> Result<(), Error> {
    let ok = !module.is_empty()
        && module.split('.').all(|part| {
            let mut chars = part.chars();
            chars.next().is_some_and(|c| c.is_ascii_uppercase())
                && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
        });
    if !ok {
        return Err(err(format!(
            "invalid Lean module name `{module}`: use dot-separated ASCII \
             identifiers that start with an uppercase letter"
        )));
    }
    let root = module.split('.').next().unwrap_or(module);
    if RESERVED_MODULE_ROOTS.contains(&root) {
        return Err(err(format!(
            "reserved Lean module name `{module}`: `cargo anneal verify` refuses \
             proof modules under `{root}`"
        )));
    }
    Ok(())
}

/// The deepest nesting of JSON arrays and objects a capture may have. A
/// captured type nests one object per level, so deeply nested types (an
/// `Option` of an `Option` of ...) need more than `serde_json`'s default
/// limit of 128, but real captures stay far below this bound, which keeps the
/// recursive parsing, rendering, and dropping of a capture within
/// [`RENDER_STACK_BYTES`].
pub const MAX_JSON_DEPTH: usize = 4096;

/// The stack of the thread that [`render`] parses and renders a capture on:
/// ample for [`MAX_JSON_DEPTH`] levels of recursion even in a debug build. It
/// is reserved, not committed, so untouched pages cost nothing.
const RENDER_STACK_BYTES: usize = 256 << 20;

/// The deepest nesting of arrays and objects in the JSON text `text`,
/// counted without parsing it, so that a capture nested too deeply for
/// [`render`] is refused before any recursion. Brackets inside strings do
/// not count; malformed text is left for the parser to reject.
fn json_depth(text: &str) -> usize {
    let (mut depth, mut max) = (0usize, 0usize);
    let (mut in_string, mut escaped) = (false, false);
    for b in text.bytes() {
        if in_string {
            match b {
                _ if escaped => escaped = false,
                b'\\' => escaped = true,
                b'"' => in_string = false,
                _ => {}
            }
            continue;
        }
        match b {
            b'"' => in_string = true,
            b'[' | b'{' => {
                depth += 1;
                max = max.max(depth);
            }
            b']' | b'}' => depth = depth.saturating_sub(1),
            _ => {}
        }
    }
    max
}

/// Render the scaffold module `module` for the capture in `capture_json`.
pub fn render(capture_json: &str, module: &str) -> Result<String, Error> {
    validate_module_name(module)?;
    if json_depth(capture_json) > MAX_JSON_DEPTH {
        return Err(err(format!(
            "malformed capture: arrays and objects nest more than {MAX_JSON_DEPTH} deep"
        )));
    }
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(RENDER_STACK_BYTES)
            .spawn_scoped(scope, || render_capture(capture_json, module))
            .map_err(|e| err(format!("cannot start the rendering thread: {e}")))?
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

/// [`render`], on a thread whose stack holds [`MAX_JSON_DEPTH`] levels.
fn render_capture(capture_json: &str, module: &str) -> Result<String, Error> {
    let malformed = |e: serde_json::Error| err(format!("malformed capture: {e}"));
    let mut de = serde_json::Deserializer::from_str(capture_json);
    // `json_depth` has already bounded the nesting.
    de.disable_recursion_limit();
    let mut values = de.into_iter::<Value>();
    let capture = values.next().ok_or_else(|| err("malformed capture: no JSON value"))?;
    let capture = capture.map_err(malformed)?;
    if let Some(trailing) = values.next() {
        return Err(match trailing {
            Ok(_) => err("malformed capture: more than one JSON value"),
            Err(e) => malformed(e),
        });
    }
    let version = capture.get("schema_version").and_then(Value::as_u64);
    if version != Some(SCHEMA_VERSION) {
        return Err(err(format!(
            "unsupported capture schema_version {}: expected {SCHEMA_VERSION}",
            version.map_or_else(|| "(missing)".to_owned(), |v| v.to_string())
        )));
    }
    let program = field(&capture, "program", "capture")?;
    let profile = match field(program, "mir_profile_version", "program")?.as_u64() {
        Some(1) => PROFILE_V1,
        Some(2) => PROFILE_V2,
        other => return Err(err(format!("unsupported mir_profile_version {other:?}"))),
    };
    let bodies = field(program, "bodies", "program")?
        .as_array()
        .ok_or_else(|| err("program.bodies is not an array"))?;
    if bodies.is_empty() {
        return Err(err("program.bodies is empty"));
    }
    let mut infos = bodies
        .iter()
        .enumerate()
        .map(|(index, body)| body_info(index, body))
        .collect::<Result<Vec<_>, _>>()?;
    assign_slugs(&mut infos)?;
    infos.sort_by(|a, b| a.slug.cmp(&b.slug));
    Ok(render_module(module, profile, &infos))
}

fn field<'a>(value: &'a Value, name: &str, context: &str) -> Result<&'a Value, Error> {
    value.get(name).ok_or_else(|| err(format!("{context} has no `{name}` field")))
}

fn body_info(index: usize, body: &Value) -> Result<BodyInfo, Error> {
    let context = format!("program.bodies[{index}]");
    let identity = field(body, "identity", &context)?
        .as_str()
        .ok_or_else(|| err(format!("{context}.identity is not a string")))?
        .to_owned();
    let is_unsafe = field(body, "is_unsafe", &context)?
        .as_bool()
        .ok_or_else(|| err(format!("{context}.is_unsafe is not a boolean")))?;
    let arg_count = field(body, "arg_count", &context)?
        .as_u64()
        .and_then(|n| usize::try_from(n).ok())
        .ok_or_else(|| err(format!("{context}.arg_count is not a count")))?;
    let local_tys = field(body, "local_tys", &context)?
        .as_array()
        .ok_or_else(|| err(format!("{context}.local_tys is not an array")))?;
    if local_tys.len() <= arg_count {
        return Err(err(format!("{context} has fewer locals than arguments")));
    }
    let params = local_tys[1..=arg_count]
        .iter()
        .map(|ty| lean_ty(ty).map_err(|e| err(format!("{context}: {e}"))))
        .collect::<Result<Vec<_>, _>>()?;
    let blocks = field(body, "blocks", &context)?
        .as_array()
        .ok_or_else(|| err(format!("{context}.blocks is not an array")))?;
    let fuel = acyclic_fuel(blocks).map_err(|e| err(format!("{context}: {e}")))?;
    Ok(BodyInfo { index, identity, slug: String::new(), is_unsafe, params, fuel })
}

/// Derive a unique ASCII Lean identifier from each identity.
///
/// An identity whose base slug (see [`base_slug`]) no other identity shares
/// keeps it. Identities that share a base slug are numbered `<base>_<n>` in
/// identity order, taking the lowest numbers that are neither some identity's
/// base slug nor already assigned. Every slug is therefore unique, and the
/// result depends only on the set of identities, not on body order.
fn assign_slugs(infos: &mut [BodyInfo]) -> Result<(), Error> {
    let mut by_identity: Vec<usize> = (0..infos.len()).collect();
    by_identity.sort_by(|&a, &b| infos[a].identity.cmp(&infos[b].identity));
    for pair in by_identity.windows(2) {
        if infos[pair[0]].identity == infos[pair[1]].identity {
            return Err(err(format!("duplicate body identity `{}`", infos[pair[0]].identity)));
        }
    }
    let mut groups: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for &i in &by_identity {
        groups.entry(base_slug(&infos[i].identity)).or_default().push(i);
    }
    let mut taken: BTreeSet<String> = groups.keys().cloned().collect();
    for (base, members) in groups {
        if let [only] = members[..] {
            infos[only].slug = base;
            continue;
        }
        let mut n = 0usize;
        for i in members {
            let slug = loop {
                n += 1;
                let candidate = format!("{base}_{n}");
                if taken.insert(candidate.clone()) {
                    break candidate;
                }
            };
            infos[i].slug = slug;
        }
    }
    Ok(())
}

/// The base slug of an identity: drop the identity prefix, map every run of
/// other characters to `_`, and prefix `b_` so the result never collides with
/// a keyword.
fn base_slug(identity: &str) -> String {
    let path = identity.strip_prefix(IDENTITY_PREFIX).unwrap_or(identity);
    let mut slug = String::from("b");
    let mut pending_sep = true;
    for c in path.chars() {
        if c.is_ascii_alphanumeric() {
            if pending_sep {
                slug.push('_');
                pending_sep = false;
            }
            slug.push(c);
        } else {
            pending_sep = true;
        }
    }
    // An identity with no ASCII alphanumerics still needs a usable name.
    if slug.len() == 1 {
        slug.push_str("_body");
    }
    slug
}

/// The `bodiesVerified` hypothesis name for the body with slug `slug`.
fn hypothesis_name(slug: &str) -> String {
    format!("h_{}", slug.strip_prefix("b_").unwrap_or(slug))
}

/// How a terminator field names successor blocks, following its type in
/// `ir::Terminator`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Edge {
    /// `u32`: always a block.
    Block,
    /// `Option<u32>`: a block, or an explicit null for a call that diverges.
    OptionalBlock,
    /// `Vec<(u128, u32)>`: the second element of each pair is a block.
    SwitchTargets,
}

/// Each captured terminator kind with its successor-block fields.
const TERMINATOR_EDGES: &[(&str, &[(&str, Edge)])] = &[
    ("goto", &[("block", Edge::Block)]),
    ("switch_int", &[("otherwise", Edge::Block), ("targets", Edge::SwitchTargets)]),
    ("assert", &[("target", Edge::Block)]),
    ("core_call", &[("target", Edge::OptionalBlock)]),
    ("call", &[("target", Edge::OptionalBlock)]),
    ("sysroot_call", &[("target", Edge::OptionalBlock)]),
    ("call_ne", &[("target", Edge::OptionalBlock)]),
    ("drop", &[("target", Edge::Block)]),
    ("ret", &[]),
    ("unreachable", &[]),
    ("unsupported", &[]),
];

/// The successor blocks of a terminator.
fn successors(term: &Value) -> Result<Vec<u64>, String> {
    let kind = term.get("kind").and_then(Value::as_str).ok_or("terminator has no kind")?;
    let (_, fields) = TERMINATOR_EDGES
        .iter()
        .find(|(k, _)| *k == kind)
        .ok_or_else(|| format!("unknown terminator kind `{kind}`"))?;
    let mut out = Vec::new();
    for &(name, edge) in *fields {
        let value = term.get(name);
        let malformed = || format!("{kind} has a missing or malformed `{name}`");
        match edge {
            Edge::Block => out.push(value.and_then(Value::as_u64).ok_or_else(malformed)?),
            // The capture always emits the field, so only an explicit null
            // diverges; a missing field or any other non-block value is
            // malformed.
            Edge::OptionalBlock => match value.ok_or_else(malformed)? {
                Value::Null => {}
                v => out.push(v.as_u64().ok_or_else(malformed)?),
            },
            Edge::SwitchTargets => {
                for pair in value.and_then(Value::as_array).ok_or_else(malformed)? {
                    let block = pair.as_array().and_then(|p| p.get(1)).and_then(Value::as_u64);
                    out.push(block.ok_or_else(malformed)?);
                }
            }
        }
    }
    Ok(out)
}

/// The number of statements and terminators in `blocks` when their control
/// flow graph is acyclic, which bounds the length of any single-frame run.
/// `None` for a cyclic graph.
fn acyclic_fuel(blocks: &[Value]) -> Result<Option<usize>, String> {
    let mut edges = Vec::with_capacity(blocks.len());
    let mut total = 0usize;
    for (i, block) in blocks.iter().enumerate() {
        let statements = block
            .get("statements")
            .and_then(Value::as_array)
            .ok_or_else(|| format!("block {i} has no statements array"))?;
        total = statements
            .len()
            .checked_add(1)
            .and_then(|n| total.checked_add(n))
            .ok_or("statement count overflows")?;
        let term = block.get("terminator").ok_or_else(|| format!("block {i} has no terminator"))?;
        let succ = successors(term).map_err(|e| format!("block {i}: {e}"))?;
        let succ = succ
            .into_iter()
            .map(|s| {
                usize::try_from(s)
                    .ok()
                    .filter(|&s| s < blocks.len())
                    .ok_or_else(|| format!("block {i} targets missing block {s}"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        edges.push(succ);
    }
    // Iterative three-color depth-first search from every block.
    let mut color = vec![0u8; blocks.len()];
    for start in 0..blocks.len() {
        if color[start] != 0 {
            continue;
        }
        let mut stack = vec![(start, 0usize)];
        color[start] = 1;
        while let Some(&mut (node, ref mut next)) = stack.last_mut() {
            if let Some(&succ) = edges[node].get(*next) {
                *next += 1;
                match color[succ] {
                    0 => {
                        color[succ] = 1;
                        stack.push((succ, 0));
                    }
                    1 => return Ok(None),
                    _ => {}
                }
            } else {
                color[node] = 2;
                stack.pop();
            }
        }
    }
    Ok(Some(total))
}

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
fn lean_ty(ty: &Value) -> Result<String, String> {
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
        "struct" => {
            let layout = ty.get("layout").ok_or("struct has no layout")?;
            let nat = |key: &str| {
                layout
                    .get(key)
                    .and_then(Value::as_u64)
                    .ok_or_else(|| format!("struct layout has no {key}"))
            };
            let offsets = layout
                .get("field_offsets")
                .and_then(Value::as_array)
                .ok_or("struct layout has no field_offsets")?
                .iter()
                .map(|off| off.as_u64().map(|o| o.to_string()).ok_or("struct field offset"))
                .collect::<Result<Vec<_>, _>>()?;
            let fields =
                ty.get("fields").and_then(Value::as_array).ok_or("struct has no fields")?;
            let fields = fields.iter().map(lean_ty).collect::<Result<Vec<_>, _>>()?;
            format!(
                "(MirTy.struct_ (StructLayout.mk {} {} {} {}) {})",
                nat("id")?,
                nat("size")?,
                nat("align_log2")?,
                lean_list(&offsets),
                lean_list(&fields)
            )
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
const MAX_LIST_CHUNK_LEN: usize = 16;

/// Render `items` as a Lean list the way the capture's emitter (`list` in
/// `rustc-capture/src/lean.rs`) does: a literal of at most
/// [`MAX_LIST_CHUNK_LEN`] elements, or a balanced tree of
/// `_root_.List.append` over such literals. A long flat literal expands into
/// nested `let`s that exceed Lean's `maxRecDepth`, while the tree keeps the
/// term's depth logarithmic and is definitionally equal to the flat list.
fn lean_list(items: &[String]) -> String {
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
fn lean_identity(s: &str) -> String {
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
fn doc_text(s: &str) -> String {
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

fn render_module(module: &str, profile: Profile, infos: &[BodyInfo]) -> String {
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

#[cfg(test)]
mod tests {
    use super::*;

    fn body(identity: &str, args: &[Value], blocks: Value) -> Value {
        let mut local_tys = vec![serde_json::json!({ "kind": "unit" })];
        local_tys.extend(args.iter().cloned());
        serde_json::json!({
            "identity": identity,
            "arg_count": args.len(),
            "is_unsafe": false,
            "local_tys": local_tys,
            "blocks": blocks,
        })
    }

    fn capture(bodies: Vec<Value>) -> String {
        serde_json::json!({
            "schema_version": SCHEMA_VERSION,
            "program": { "mir_profile_version": 1, "bodies": bodies },
        })
        .to_string()
    }

    fn ret_block() -> Value {
        serde_json::json!([{ "statements": [], "terminator": { "kind": "ret" } }])
    }

    #[test]
    fn slugs_are_ascii_prefixed_and_numbered_by_identity() {
        assert_eq!(
            base_slug("rust-path-v1::<usize as PointerMetadata>::from_elem_count"),
            "b_usize_as_PointerMetadata_from_elem_count"
        );
        assert_eq!(base_slug("rust-path-v1::end"), "b_end");
        assert_eq!(base_slug("rust-path-v1::<>::_"), "b_body");
        assert_eq!(base_slug(""), "b_body");
        assert_eq!(hypothesis_name("b_body"), "h_body");
        let punctuation =
            render(&capture(vec![body("rust-path-v1::<>", &[], ret_block())]), "A").unwrap();
        assert!(punctuation.contains("namespace b_body"));
        assert!(punctuation.contains("(h_body :"));
    }

    fn slugs(identities: &[&str]) -> Vec<String> {
        let mut infos: Vec<BodyInfo> = identities
            .iter()
            .enumerate()
            .map(|(index, id)| BodyInfo {
                index,
                identity: format!("rust-path-v1::{id}"),
                slug: String::new(),
                is_unsafe: false,
                params: Vec::new(),
                fuel: None,
            })
            .collect();
        assign_slugs(&mut infos).unwrap();
        infos.into_iter().map(|i| i.slug).collect()
    }

    #[test]
    fn numbered_slugs_are_globally_unique_and_order_independent() {
        assert_eq!(slugs(&["a::b", "a_b", "c"]), ["b_a_b_1", "b_a_b_2", "b_c"]);
        // `a::b` and `a_b` share the base slug `b_a_b`, and their numbering
        // must skip `b_a_b_1`, the base slug of `a_b_1`.
        assert_eq!(slugs(&["a::b", "a_b", "a_b_1"]), ["b_a_b_2", "b_a_b_3", "b_a_b_1"]);
        // Numbering skips every base slug, and numbering a numbered-looking
        // base stays distinct.
        let ids = ["x::1", "x_1", "x", "x.", "x_2"];
        let forward = slugs(&ids);
        assert_eq!(forward, ["b_x_1_1", "b_x_1_2", "b_x_3", "b_x_4", "b_x_2"]);
        let unique: BTreeSet<_> = forward.iter().collect();
        assert_eq!(unique.len(), forward.len());
        // Reversing the bodies maps each identity to the same slug.
        let mut reversed_ids = ids;
        reversed_ids.reverse();
        let mut reversed = slugs(&reversed_ids);
        reversed.reverse();
        assert_eq!(reversed, forward);
    }

    #[test]
    fn reordering_bodies_changes_only_indices() {
        let int = serde_json::json!({ "kind": "int", "width": "isize", "signed": false });
        let a = body("rust-path-v1::a", std::slice::from_ref(&int), ret_block());
        let b = body("rust-path-v1::b", &[], ret_block());
        let forward = render(&capture(vec![a.clone(), b.clone()]), "AutoScaffold").unwrap();
        let reverse = render(&capture(vec![b, a]), "AutoScaffold").unwrap();
        assert_ne!(forward, reverse);
        let normalize = |s: &str| {
            s.replace("body_0", "body_X")
                .replace("body_1", "body_X")
                .replace("defId : DefId := 0", "defId : DefId := X")
                .replace("defId : DefId := 1", "defId : DefId := X")
                .lines()
                // The constructor lists hypotheses in body order.
                .filter(|l| !l.starts_with("    h_"))
                .collect::<Vec<_>>()
                .join("\n")
        };
        assert_eq!(normalize(&forward), normalize(&reverse));
        assert!(forward.contains("(h_a :\n      BodyVerified Captured.program b_a.defId b_a.body"));
        assert!(forward.contains("[(MirTy.int IntWidth.isize false)]"));
    }

    #[test]
    fn fuel_counts_acyclic_bodies_and_omits_loops() {
        let acyclic = serde_json::json!([
            { "statements": [{}, {}], "terminator": { "kind": "goto", "block": 1 } },
            { "statements": [{}], "terminator": { "kind": "ret" } },
        ]);
        assert_eq!(acyclic_fuel(acyclic.as_array().unwrap()), Ok(Some(5)));
        let cyclic = serde_json::json!([
            { "statements": [], "terminator": { "kind": "switch_int", "targets": [["0", 1]], "otherwise": 0 } },
            { "statements": [], "terminator": { "kind": "ret" } },
        ]);
        assert_eq!(acyclic_fuel(cyclic.as_array().unwrap()), Ok(None));
        let dangling =
            serde_json::json!([{ "statements": [], "terminator": { "kind": "goto", "block": 7 } }]);
        assert!(acyclic_fuel(dangling.as_array().unwrap()).is_err());
        // A call, sysroot call, or core call (`PanicAbort`) with a null
        // target diverges.
        for kind in ["call", "sysroot_call", "core_call"] {
            let diverging = serde_json::json!([
                { "statements": [], "terminator": { "kind": kind, "target": null } },
            ]);
            assert_eq!(acyclic_fuel(diverging.as_array().unwrap()), Ok(Some(1)), "{kind}");
        }
        let core_call = serde_json::json!([
            { "statements": [{}], "terminator": { "kind": "core_call", "target": 1 } },
            { "statements": [], "terminator": { "kind": "ret" } },
        ]);
        assert_eq!(acyclic_fuel(core_call.as_array().unwrap()), Ok(Some(3)));
        for missing in ["goto", "assert", "call", "sysroot_call", "core_call"] {
            let malformed =
                serde_json::json!([{ "statements": [], "terminator": { "kind": missing } }]);
            assert!(acyclic_fuel(malformed.as_array().unwrap()).is_err(), "{missing}");
        }
        for target in [serde_json::json!("bad"), serde_json::json!(-1)] {
            let malformed = serde_json::json!([
                { "statements": [], "terminator": { "kind": "sysroot_call", "target": target } },
            ]);
            assert!(acyclic_fuel(malformed.as_array().unwrap()).is_err(), "{target}");
        }
        let unknown = serde_json::json!([{ "statements": [], "terminator": { "kind": "yield" } }]);
        assert!(acyclic_fuel(unknown.as_array().unwrap()).is_err());
    }

    #[test]
    fn types_render_like_the_capture_emitter() {
        let ty = serde_json::json!({
            "kind": "ref",
            "mutability": "shared",
            "pointee": {
                "kind": "enum", "id": 9, "discr_width": "i32", "discr_signed": true,
                "tag_repr": { "kind": "scalar", "width": "i8", "signed": true },
                "discriminants": ["0", "1"],
            },
        });
        assert_eq!(
            lean_ty(&ty).unwrap(),
            "(MirTy.ref Mutability.shared (MirTy.enum { id := 9, discrWidth := IntWidth.i32, \
             discrSigned := true, tagRepr := (EnumTagRepr.scalar IntWidth.i8 true), \
             discriminants := [0, 1] }))"
        );
        assert!(lean_ty(&serde_json::json!({ "kind": "float" })).is_err());
        assert!(
            lean_ty(&serde_json::json!({ "kind": "int", "width": "i7", "signed": true })).is_err()
        );
        // `&str`, `Range<Option<u8>>`, `[RangeTo<usize>; 2]`, and a tuple of
        // `RangeFrom<i8>` and `&[char]`.
        let u8_ty = serde_json::json!({ "kind": "int", "width": "i8", "signed": false });
        let cases = [
            (
                serde_json::json!({ "kind": "ref", "mutability": "shared", "pointee": { "kind": "str" } }),
                "(MirTy.ref Mutability.shared MirTy.str)",
            ),
            (
                serde_json::json!({ "kind": "range", "elem": { "kind": "option", "elem": u8_ty } }),
                "(MirTy.range (MirTy.option (MirTy.int IntWidth.i8 false)))",
            ),
            (
                serde_json::json!({ "kind": "array", "len": 2, "elem": {
                    "kind": "range_to", "elem": { "kind": "int", "width": "isize", "signed": false },
                } }),
                "(MirTy.array (MirTy.rangeTo (MirTy.int IntWidth.isize false)) 2)",
            ),
            (
                serde_json::json!({ "kind": "tuple", "fields": [
                    { "kind": "range_from", "elem": { "kind": "int", "width": "i8", "signed": true } },
                    { "kind": "ref", "mutability": "mut", "pointee": {
                        "kind": "slice", "elem": { "kind": "char" },
                    } },
                ] }),
                "(MirTy.tuple [(MirTy.rangeFrom (MirTy.int IntWidth.i8 true)), \
                 (MirTy.ref Mutability.mut (MirTy.slice MirTy.char))])",
            ),
        ];
        let more = [
            (
                serde_json::json!({ "kind": "box", "pointee": { "kind": "slice", "elem": { "kind": "int", "width": "i8", "signed": false } } }),
                "(MirTy.box (MirTy.slice (MirTy.int IntWidth.i8 false)))",
            ),
            (
                serde_json::json!({ "kind": "vec", "elem": { "kind": "bool" } }),
                "(MirTy.vec MirTy.bool)",
            ),
        ];
        for (ty, expected) in cases.into_iter().chain(more) {
            assert_eq!(lean_ty(&ty).unwrap(), expected);
        }
        // `box` reads `pointee`, not `elem`.
        assert!(lean_ty(&serde_json::json!({ "kind": "box", "elem": { "kind": "bool" } })).is_err());
        assert!(lean_ty(&serde_json::json!({ "kind": "option" })).is_err());
    }

    /// The source of `rel`, relative to the Anneal workspace root.
    fn anneal_source(rel: &str) -> String {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
        std::fs::read_to_string(root.join(rel)).unwrap_or_else(|e| panic!("{rel}: {e}"))
    }

    /// The text from the first line starting with `start` through the next line
    /// that is exactly `}`.
    fn item<'a>(source: &'a str, start: &str) -> &'a str {
        let begin = source.find(start).unwrap_or_else(|| panic!("no `{start}`"));
        let len = source[begin..].find("\n}\n").unwrap_or_else(|| panic!("unclosed `{start}`"));
        &source[begin..begin + len]
    }

    fn snake_case(camel: &str) -> String {
        let mut out = String::new();
        for (i, c) in camel.chars().enumerate() {
            if c.is_ascii_uppercase() && i > 0 {
                out.push('_');
            }
            out.push(c.to_ascii_lowercase());
        }
        out
    }

    /// Every variant of the capture's `ir::Ty` renders, and with every `MirTy`
    /// constructor that the capture's Lean emitter uses for it.
    #[test]
    fn every_captured_type_kind_renders_like_the_capture_emitter() {
        let ir = anneal_source("trusted/rustc-capture/src/ir.rs");
        let lean = anneal_source("trusted/rustc-capture/src/lean.rs");
        let emitter = item(&lean, "fn ty_at(");
        let variants: Vec<&str> = item(&ir, "pub enum Ty {")
            .lines()
            .skip(1)
            .filter_map(|line| line.strip_prefix("    "))
            .filter(|line| line.starts_with(|c: char| c.is_ascii_uppercase()))
            .map(|line| line.split(|c: char| !c.is_ascii_alphanumeric()).next().unwrap())
            .collect();
        assert!(variants.len() >= 18 && variants.contains(&"Option"), "{variants:?}");
        let unit = serde_json::json!({ "kind": "unit" });
        for variant in variants {
            let kind = snake_case(variant);
            // One value carrying every field any type kind reads.
            let ty = serde_json::json!({
                "kind": kind, "width": "i8", "signed": true, "mutability": "shared",
                "pointee": unit, "elem": unit, "len": 1, "fields": [unit], "id": 0,
                "discr_width": "i8", "discr_signed": true,
                "tag_repr": { "kind": "zero_sized" }, "discriminants": ["0"],
                "layout": { "id": 0, "size": 0, "align_log2": 0, "field_offsets": [0] },
            });
            let rendered = lean_ty(&ty).unwrap_or_else(|e| panic!("{variant}: {e}"));
            let arm = emitter
                .match_indices(&format!("Ty::{variant}"))
                .map(|(at, _)| &emitter[at..])
                .find(|rest| !rest[4 + variant.len()..].starts_with(char::is_alphanumeric))
                .unwrap_or_else(|| panic!("lean.rs has no arm for `Ty::{variant}`"));
            let arm = &arm[..arm[4..].find("\n        Ty::").map_or(arm.len(), |end| end + 4)];
            let ctors: Vec<&str> = arm
                .split("Trusted.MirAst.MirTy.")
                .skip(1)
                .map(|rest| rest.split(|c: char| !c.is_ascii_alphanumeric()).next().unwrap())
                .collect();
            assert!(!ctors.is_empty(), "{variant}: no MirTy constructor in {arm}");
            for ctor in ctors {
                assert!(rendered.contains(&format!("MirTy.{ctor}")), "{variant}: {rendered}");
            }
        }
    }

    /// `TERMINATOR_EDGES` lists exactly the variants of the capture's
    /// `ir::Terminator`, and each successor field with the edge its type
    /// implies: `u32`, `Option<u32>`, or `Vec<(u128, u32)>`.
    #[test]
    fn terminator_edges_match_the_capture() {
        let ir = anneal_source("trusted/rustc-capture/src/ir.rs");
        let mut captured = BTreeMap::new();
        let mut variant = None;
        for line in item(&ir, "pub enum Terminator {").lines().skip(1) {
            if let Some(rest) = line.strip_prefix("    ") {
                if rest.starts_with(|c: char| c.is_ascii_uppercase()) {
                    let name: String =
                        rest.chars().take_while(char::is_ascii_alphanumeric).collect();
                    variant = Some(snake_case(&name));
                    captured.insert(snake_case(&name), Vec::new());
                    continue;
                }
            }
            let Some(field) = line.strip_prefix("        ") else { continue };
            let Some((name, ty)) = field.trim_end_matches(',').split_once(": ") else {
                continue;
            };
            let edge = match (name, ty) {
                ("block" | "target" | "otherwise", "u32") => Edge::Block,
                ("target", "Option<u32>") => Edge::OptionalBlock,
                ("targets", "Vec<(u128, u32)>") => Edge::SwitchTargets,
                ("block" | "target" | "otherwise" | "targets", _) => {
                    panic!("unexpected successor field type `{field}`")
                }
                _ => continue,
            };
            captured.get_mut(variant.as_ref().unwrap()).unwrap().push((name.to_owned(), edge));
        }
        let ours: BTreeMap<String, Vec<(String, Edge)>> = TERMINATOR_EDGES
            .iter()
            .map(|(k, fields)| {
                ((*k).to_owned(), fields.iter().map(|&(n, e)| (n.to_owned(), e)).collect())
            })
            .collect();
        let by_name = |m: BTreeMap<String, Vec<(String, Edge)>>| {
            m.into_iter()
                .map(|(k, mut v)| {
                    v.sort_by(|a, b| a.0.cmp(&b.0));
                    (k, v)
                })
                .collect::<BTreeMap<_, _>>()
        };
        assert_eq!(by_name(ours), by_name(captured));
    }

    #[test]
    fn reserved_module_roots_match_cargo_anneal() {
        let verify = anneal_source("trusted/cargo-anneal/src/verify.rs");
        let reserved: BTreeSet<&str> =
            item(&verify, "fn reserved_proof_module(").split('"').skip(1).step_by(2).collect();
        assert_eq!(reserved, RESERVED_MODULE_ROOTS.iter().copied().collect());
        let one = capture(vec![body("rust-path-v1::a", &[], ret_block())]);
        for root in RESERVED_MODULE_ROOTS {
            for module in [root.to_string(), format!("{root}.AutoScaffold")] {
                let e = render(&one, &module).unwrap_err();
                assert!(e.0.contains("reserved"), "{module}: {e}");
            }
        }
        for module in ["TrustedHelpers", "Proof.Trusted", "Spec.AutoScaffold"] {
            assert!(render(&one, module).is_ok(), "{module}");
        }
    }

    #[test]
    fn identities_render_like_the_capture_emitter() {
        assert_eq!(lean_identity(""), "(_root_.String.ofList [])");
        assert_eq!(
            lean_identity("a\u{3bb}"),
            "(_root_.String.ofList [(_root_.Char.ofNat 97), (_root_.Char.ofNat 955)])"
        );
        // 33 characters make leaves of 16, 16, and 1, joined as 16 + (16 + 1)
        // exactly as the capture joins them.
        let long: String = std::iter::repeat_n('x', 33).collect();
        let rendered = lean_identity(&long);
        assert!(rendered.starts_with("(Trusted.MirAst.stringAppend (_root_.String.ofList ["));
        assert_eq!(rendered.matches("Trusted.MirAst.stringAppend").count(), 2);
        assert_eq!(rendered.matches("_root_.String.ofList").count(), 3);
    }

    #[test]
    fn docs_stay_printable_ascii() {
        assert_eq!(doc_text("`x` -/ /-"), "'x' - / / -");
    }

    /// The elements of a list that `lean_list` renders, in order, after
    /// checking that every literal holds at most `MAX_LIST_CHUNK_LEN` of
    /// them and every join is balanced.
    fn list_items(rendered: &str) -> Vec<String> {
        fn walk(s: &str, out: &mut Vec<String>) -> usize {
            if let Some(rest) = s.strip_prefix("(_root_.List.append ") {
                let inner = &rest[..rest.len() - 1];
                // Split at the top-level space between the two operands.
                let (mut depth, mut at) = (0i32, None);
                for (i, c) in inner.char_indices() {
                    match c {
                        '(' | '[' => depth += 1,
                        ')' | ']' => depth -= 1,
                        ' ' if depth == 0 => {
                            at = Some(i);
                            break;
                        }
                        _ => {}
                    }
                }
                let at = at.expect("two operands");
                let (l, r) = (walk(&inner[..at], out), walk(&inner[at + 1..], out));
                assert!(l.abs_diff(r) <= 1, "unbalanced join in {s}");
                return l.max(r) + 1;
            }
            let body = s.strip_prefix('[').and_then(|s| s.strip_suffix(']')).expect(s);
            let items: Vec<&str> =
                if body.is_empty() { vec![] } else { body.split(", ").collect() };
            assert!(items.len() <= MAX_LIST_CHUNK_LEN, "literal too long: {s}");
            out.extend(items.into_iter().map(str::to_owned));
            0
        }
        let mut out = Vec::new();
        walk(rendered, &mut out);
        out
    }

    #[test]
    fn long_lists_render_as_balanced_appends_of_short_literals() {
        let names = |n: usize| (0..n).map(|i| format!("x{i}")).collect::<Vec<_>>();
        assert_eq!(lean_list(&[]), "[]");
        assert_eq!(lean_list(&names(16)), format!("[{}]", names(16).join(", ")));
        for n in [17, 40, 255, 1950] {
            let rendered = lean_list(&names(n));
            assert!(rendered.starts_with("(_root_.List.append "), "{n}");
            assert_eq!(list_items(&rendered), names(n), "{n}");
        }
        // A 40-field tuple, a 40-variant enum, and 40 parameters.
        let int = serde_json::json!({ "kind": "int", "width": "i8", "signed": false });
        let tuple = serde_json::json!({ "kind": "tuple", "fields": vec![int.clone(); 40] });
        let rendered = lean_ty(&tuple).unwrap();
        let fields = rendered.strip_prefix("(MirTy.tuple ").unwrap().strip_suffix(')').unwrap();
        assert_eq!(list_items(fields), vec!["(MirTy.int IntWidth.i8 false)".to_owned(); 40]);
        let discriminants: Vec<String> = (0..40).map(|i| i.to_string()).collect();
        let enum_ty = serde_json::json!({
            "kind": "enum", "id": 1, "discr_width": "i8", "discr_signed": false,
            "tag_repr": { "kind": "zero_sized" }, "discriminants": discriminants,
        });
        let rendered = lean_ty(&enum_ty).unwrap();
        let list = rendered.split("discriminants := ").nth(1).unwrap().strip_suffix(" })").unwrap();
        assert_eq!(list_items(list), discriminants);
        let scaffold = render(
            &capture(vec![body("rust-path-v1::wide", &vec![int; 40], ret_block())]),
            "AutoScaffold",
        )
        .unwrap();
        let params = scaffold.split("argumentCount =\n      ").nth(1).unwrap();
        let params = &params[..params.find(" :=\n").unwrap()];
        assert_eq!(list_items(params).len(), 40);
    }

    /// A capture whose one body takes an argument of `depth` nested
    /// `Option`s around `inner`, built as text so that no recursive `Value`
    /// is built or dropped on the test thread.
    fn nested_option_capture(depth: usize, inner: &str) -> String {
        let placeholder = serde_json::json!("NESTED");
        let text = capture(vec![body("rust-path-v1::deep", &[placeholder], ret_block())]);
        let nested = format!(
            "{}{inner}{}",
            "{\"kind\":\"option\",\"elem\":".repeat(depth),
            "}".repeat(depth)
        );
        text.replace("\"NESTED\"", &nested)
    }

    #[test]
    fn deeply_nested_types_render_within_the_depth_bound() {
        let unit = "{\"kind\":\"unit\"}";
        for depth in [200, MAX_JSON_DEPTH - 10] {
            let scaffold = render(&nested_option_capture(depth, unit), "AutoScaffold")
                .unwrap_or_else(|e| panic!("{depth}: {e}"));
            assert_eq!(scaffold.matches("(MirTy.option ").count(), depth);
        }
        // A malformed type deep inside is reported, not a crash.
        let bad = render(&nested_option_capture(200, "{\"kind\":\"float\"}"), "AutoScaffold");
        assert!(bad.unwrap_err().0.contains("unknown type kind `float`"));
        let missing = render(&nested_option_capture(200, "{}"), "AutoScaffold");
        assert!(missing.unwrap_err().0.contains("type has no kind"));
        // Beyond the bound, the capture is refused before it is parsed.
        let too_deep = render(&nested_option_capture(MAX_JSON_DEPTH, unit), "AutoScaffold");
        assert!(too_deep.unwrap_err().0.contains(&format!("nest more than {MAX_JSON_DEPTH} deep")));
        let unbalanced = format!("{}{}", "[".repeat(MAX_JSON_DEPTH + 1), "]".repeat(3));
        assert!(render(&unbalanced, "AutoScaffold").unwrap_err().0.contains("nest more than"));
        // Trailing values are malformed.
        let one = capture(vec![body("rust-path-v1::a", &[], ret_block())]);
        assert!(render(&format!("{one} {one}"), "AutoScaffold").is_err());
        assert!(render(&format!("{one} ]"), "AutoScaffold").is_err());
    }

    #[test]
    fn json_depth_ignores_brackets_in_strings() {
        assert_eq!(json_depth(""), 0);
        assert_eq!(json_depth("[[{}], {}]"), 3);
        assert_eq!(json_depth(r#"["[[[", "\"[[", "\\", [1]]"#), 2);
        assert_eq!(json_depth("]]]["), 1);
    }

    #[test]
    fn rejects_unusable_captures() {
        assert!(render("{", "AutoScaffold").is_err());
        assert!(render(&capture(vec![]), "AutoScaffold").is_err());
        let wrong_schema = serde_json::json!({ "schema_version": 4, "program": {} }).to_string();
        assert!(render(&wrong_schema, "AutoScaffold").unwrap_err().0.contains("schema_version"));
        let dup = capture(vec![
            body("rust-path-v1::a", &[], ret_block()),
            body("rust-path-v1::a", &[], ret_block()),
        ]);
        assert!(render(&dup, "AutoScaffold").unwrap_err().0.contains("duplicate"));
        let one = capture(vec![body("rust-path-v1::a", &[], ret_block())]);
        for bad in ["", "autoScaffold", "Auto.", "Auto-Scaffold", "Auto..S"] {
            assert!(render(&one, bad).is_err(), "{bad}");
        }
        assert!(render(&one, "Proof.AutoScaffold").is_ok());
    }
}
