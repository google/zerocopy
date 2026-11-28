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

mod fuel;
mod lean;
#[cfg(test)]
mod tests;

use std::collections::{BTreeMap, BTreeSet};

use serde_json::Value;

use crate::{
    fuel::acyclic_fuel,
    lean::{lean_ty, render_module},
};

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
