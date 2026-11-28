// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! SHA-256 and canonical `request_sha256` / `specification_manifest_sha256`
//! bindings matching `cargo-anneal verify`, plus `scope.instantiations`
//! path validation matching `anneal-rustc-capture`.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use anneal_spec_lower::{lower_with, Format, Options, Source};
use serde_json::{json, Map, Value};

/// Standard FIPS 180-4 SHA-256 digest rendered as 64 lowercase hex characters.
pub(crate) fn sha256_hex(data: &[u8]) -> String {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    let compress = |h: &mut [u32; 8], block: &[u8; 64]| {
        let mut w = [0u32; 64];
        for (i, word) in block.as_chunks::<4>().0.iter().enumerate() {
            w[i] = u32::from_be_bytes(*word);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = *h;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = hh.wrapping_add(s1).wrapping_add(ch).wrapping_add(K[i]).wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);
            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }
        for (dst, add) in h.iter_mut().zip([a, b, c, d, e, f, g, hh]) {
            *dst = dst.wrapping_add(add);
        }
    };

    let (blocks, rem) = data.as_chunks::<64>();
    for block in blocks {
        compress(&mut h, block);
    }
    let bit_len = (data.len() as u64) * 8;
    let mut tail = [0u8; 128];
    tail[..rem.len()].copy_from_slice(rem);
    tail[rem.len()] = 0x80;
    if rem.len() < 56 {
        tail[56..64].copy_from_slice(&bit_len.to_be_bytes());
        let mut b0 = [0u8; 64];
        b0.copy_from_slice(&tail[..64]);
        compress(&mut h, &b0);
    } else {
        tail[120..128].copy_from_slice(&bit_len.to_be_bytes());
        let (mut b0, mut b1) = ([0u8; 64], [0u8; 64]);
        b0.copy_from_slice(&tail[..64]);
        b1.copy_from_slice(&tail[64..128]);
        compress(&mut h, &b0);
        compress(&mut h, &b1);
    }
    let mut out = String::with_capacity(64);
    for word in h {
        use std::fmt::Write as _;
        let _ = write!(&mut out, "{word:08x}");
    }
    out
}

/// Parses an optional 64-character hex SHA-256 string field, normalized to
/// lowercase.
pub(crate) fn opt_sha256_field(
    obj: &Map<String, Value>,
    key: &str,
    ptr: &str,
) -> Result<Option<String>, String> {
    let Some(val) = obj.get(key) else {
        return Ok(None);
    };
    let Some(s) = val.as_str() else {
        return Err(format!("{ptr}/{key} must be a 64-character hex SHA-256 string"));
    };
    if s.len() != 64 || !s.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err(format!("{ptr}/{key} must be a 64-character hex SHA-256 string"));
    }
    Ok(Some(s.to_ascii_lowercase()))
}

/// Computes `specification_manifest_sha256` matching `cargo-anneal verify`:
/// `sha256(serde_json::to_vec_pretty(&[(module, sha256(lean_bytes)), ...]))`.
pub(crate) fn spec_manifest_sha256(entries: &[(&str, &str)]) -> String {
    let arr: Vec<Value> = entries.iter().map(|(m, h)| json!([m, h])).collect();
    let pretty = serde_json::to_vec_pretty(&arr).expect("JSON array serialization is infallible");
    sha256_hex(&pretty)
}

/// Computes `specification_manifest_sha256` for a single lowered Lean
/// specification module `module_name` with source text `lean_source`.
pub(crate) fn single_module_spec_manifest_sha256(module_name: &str, lean_source: &str) -> String {
    let lean_sha = sha256_hex(lean_source.as_bytes());
    spec_manifest_sha256(&[(module_name, &lean_sha)])
}

/// One target extracted from `anneal::spec` sources, carrying both its
/// `Format::V1` (`Spec`) manifest digests and its `claim` + shared `sources`
/// so [`SpecSource::digests_for_target`] can also compute the
/// `Format::V2Module` (`Specs.<crate>.<claim>`) manifest digest once
/// `crate_name` is unified.
#[derive(Clone)]
pub struct SpecSource {
    targets: Vec<String>,
    /// Per-target `(claim, precomputed V1 specification_manifest_sha256 set)`.
    bindings: BTreeMap<String, (String, BTreeSet<String>)>,
    sources: Option<Arc<[Source]>>,
}

impl std::fmt::Debug for SpecSource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SpecSource")
            .field("targets", &self.targets)
            .field("bindings", &self.bindings)
            .finish()
    }
}

impl PartialEq for SpecSource {
    fn eq(&self, other: &Self) -> bool {
        self.targets == other.targets && self.bindings == other.bindings
    }
}

impl Eq for SpecSource {}

impl SpecSource {
    /// Constructs an unbound target list (for synthetic tests without Rust
    /// source text). Because no lowered specification digest is bound, no
    /// receipt can discharge these targets unless constructed via
    /// [`crate::spec_inputs`].
    pub fn targets<I, S>(targets: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let targets: Vec<String> = targets.into_iter().map(Into::into).collect();
        SpecSource { targets, bindings: BTreeMap::new(), sources: None }
    }

    pub(crate) fn from_lowered(
        file_idx: usize,
        sources: &Arc<[Source]>,
        file_targets: Vec<(String, String)>,
        whole_v1_digest: Option<&str>,
    ) -> Self {
        let single_file_v1 = lower_with(&sources[file_idx..=file_idx], &Options::default())
            .ok()
            .map(|l| single_module_spec_manifest_sha256("Spec", &l.spec_lean));
        let mut targets = Vec::with_capacity(file_targets.len());
        let mut bindings = BTreeMap::new();
        for (target, claim) in file_targets {
            let mut digests = BTreeSet::new();
            if let Some(d) = whole_v1_digest {
                digests.insert(d.to_owned());
            }
            if let Some(d) = &single_file_v1 {
                digests.insert(d.clone());
            }
            if let Ok(l) =
                lower_with(sources, &Options { claim: Some(claim.clone()), ..Options::default() })
            {
                digests.insert(single_module_spec_manifest_sha256("Spec", &l.spec_lean));
            }
            if let Ok(l) = lower_with(
                sources,
                &Options { targets: vec![target.clone()], ..Options::default() },
            ) {
                digests.insert(single_module_spec_manifest_sha256("Spec", &l.spec_lean));
            }
            targets.push(target.clone());
            bindings.insert(target, (claim, digests));
        }
        SpecSource { targets, bindings, sources: Some(Arc::clone(sources)) }
    }

    /// The `rust-path-v1` paths (without scheme) specified in this file.
    pub fn target_paths(&self) -> &[String] {
        &self.targets
    }

    /// Allowed `specification_manifest_sha256` digests for `target` under
    /// `crate_name` (including `Format::V2Module` `Specs.<crate>.<claim>` when
    /// `crate_name` is known).
    pub(crate) fn digests_for_target(
        &self,
        target: &str,
        crate_name: Option<&str>,
        v2_cache: &mut BTreeMap<(usize, String, String), Option<String>>,
    ) -> BTreeSet<String> {
        let Some((claim, base_digests)) = self.bindings.get(target) else {
            return BTreeSet::new();
        };
        let mut out = base_digests.clone();
        if let (Some(sources), Some(slug)) = (&self.sources, crate_name) {
            let cache_key =
                (Arc::as_ptr(sources) as *const Source as usize, slug.to_owned(), claim.clone());
            let v2 = v2_cache.entry(cache_key).or_insert_with(|| {
                let opts = Options {
                    targets: Vec::new(),
                    claim: Some(claim.clone()),
                    format: Format::V2Module,
                    crate_slug: Some(slug.to_owned()),
                };
                lower_with(sources, &opts).ok().map(|lowered| {
                    let module = format!("Specs.{slug}.{claim}");
                    single_module_spec_manifest_sha256(&module, &lowered.spec_lean)
                })
            });
            if let Some(d) = v2 {
                out.insert(d.clone());
            }
        }
        out
    }
}

impl From<Vec<String>> for SpecSource {
    fn from(targets: Vec<String>) -> Self {
        SpecSource::targets(targets)
    }
}

/// Computes `request_sha256` matching `cargo-anneal verify` when `root`
/// carries a complete request (`compilation` + `scope` + `proof`). Minimal
/// request stubs omitting `proof` or required compilation paths return
/// `Ok(None)` so they still register `deferred` contracts without matching an
/// unrelated receipt.
pub(crate) fn canonical_request_sha256(
    root: &Map<String, Value>,
) -> Result<Option<String>, String> {
    let Some(comp_val) = root.get("compilation").and_then(Value::as_object) else {
        return Ok(None);
    };
    let Some(proof_val) = root.get("proof") else {
        return Ok(None);
    };
    let proof_obj = proof_val.as_object().ok_or("/proof must be an object")?;
    for req_key in ["source_root", "crate_root", "crate_name", "source_files"] {
        if !comp_val.contains_key(req_key) {
            return Ok(None);
        }
    }
    for k in root.keys() {
        if !matches!(k.as_str(), "schema_version" | "compilation" | "scope" | "proof") {
            return Err(format!("unknown field `{k}` in request"));
        }
    }
    for k in comp_val.keys() {
        if !matches!(
            k.as_str(),
            "source_root"
                | "crate_root"
                | "crate_name"
                | "crate_type"
                | "panic"
                | "overflow_checks"
                | "edition"
                | "target"
                | "cfg"
                | "env"
                | "source_files"
                | "stdlib_crate"
        ) {
            return Err(format!("unknown field `/compilation/{k}` in request"));
        }
    }
    let req_str = |obj: &Map<String, Value>, key: &str, ptr: &str| -> Result<String, String> {
        obj.get(key)
            .and_then(Value::as_str)
            .map(str::to_owned)
            .ok_or_else(|| format!("{ptr}/{key} must be a string"))
    };
    let opt_str =
        |obj: &Map<String, Value>, key: &str, default: &str, ptr: &str| -> Result<String, String> {
            match obj.get(key) {
                None => Ok(default.to_owned()),
                Some(v) => v
                    .as_str()
                    .map(str::to_owned)
                    .ok_or_else(|| format!("{ptr}/{key} must be a string")),
            }
        };

    let source_root = req_str(comp_val, "source_root", "/compilation")?;
    let crate_root = req_str(comp_val, "crate_root", "/compilation")?;
    let crate_name = req_str(comp_val, "crate_name", "/compilation")?;
    let crate_type = opt_str(comp_val, "crate_type", "lib", "/compilation")?;
    if !matches!(crate_type.as_str(), "lib" | "bin") {
        return Err(format!("unrecognized `/compilation/crate_type` `{crate_type}`"));
    }
    let panic = opt_str(comp_val, "panic", "unwind", "/compilation")?;
    if !matches!(panic.as_str(), "unwind" | "abort") {
        return Err(format!("unrecognized `/compilation/panic` `{panic}`"));
    }
    let overflow_checks = match comp_val.get("overflow_checks") {
        None => false,
        Some(v) => v.as_bool().ok_or("/compilation/overflow_checks must be a boolean")?,
    };
    let edition = opt_str(comp_val, "edition", "2024", "/compilation")?;
    let target = opt_str(comp_val, "target", "x86_64-unknown-linux-gnu", "/compilation")?;
    let cfg: BTreeSet<String> = match comp_val.get("cfg") {
        None => BTreeSet::new(),
        Some(v) => v
            .as_array()
            .and_then(|a| a.iter().map(|x| x.as_str().map(str::to_owned)).collect())
            .ok_or("/compilation/cfg must be an array of strings")?,
    };
    let env: BTreeMap<String, String> = match comp_val.get("env") {
        None => BTreeMap::new(),
        Some(v) => {
            let m = v.as_object().ok_or("/compilation/env must be an object")?;
            let mut out = BTreeMap::new();
            for (k, val) in m {
                let s = val.as_str().ok_or("/compilation/env values must be strings")?;
                out.insert(k.clone(), s.to_owned());
            }
            out
        }
    };
    let source_files: Vec<String> = comp_val
        .get("source_files")
        .and_then(Value::as_array)
        .and_then(|a| a.iter().map(|x| x.as_str().map(str::to_owned)).collect())
        .ok_or("/compilation/source_files must be an array of strings")?;
    let stdlib_crate: Option<String> = match comp_val.get("stdlib_crate") {
        None | Some(Value::Null) => None,
        Some(v) => Some(
            v.as_str().map(str::to_owned).ok_or("/compilation/stdlib_crate must be a string")?,
        ),
    };

    let scope_obj =
        root.get("scope").and_then(Value::as_object).ok_or("/scope must be an object")?;
    let scope_kind = req_str(scope_obj, "kind", "/scope")?;
    let mut scope_fields: Vec<(&str, Value)> = vec![("kind", json!(scope_kind))];
    match scope_kind.as_str() {
        "crate" => {
            for k in scope_obj.keys() {
                if k != "kind" {
                    return Err(format!("unknown field `/scope/{k}` on crate request"));
                }
            }
        }
        "selected_unit" => {
            for k in scope_obj.keys() {
                if !matches!(k.as_str(), "kind" | "roots" | "instantiations") {
                    return Err(format!("unknown field `/scope/{k}` in request"));
                }
            }
            let roots: BTreeSet<String> = scope_obj
                .get("roots")
                .and_then(Value::as_array)
                .and_then(|a| a.iter().map(|x| x.as_str().map(str::to_owned)).collect())
                .ok_or("/scope/roots must be an array of strings")?;
            scope_fields.push(("roots", json!(roots)));
            if let Some(insts_val) = scope_obj.get("instantiations") {
                let insts = insts_val.as_array().ok_or("/scope/instantiations must be an array")?;
                let mut sorted: BTreeSet<(String, Vec<String>)> = BTreeSet::new();
                for (i, item) in insts.iter().enumerate() {
                    let obj = item
                        .as_object()
                        .ok_or_else(|| format!("/scope/instantiations/{i} must be an object"))?;
                    for k in obj.keys() {
                        if !matches!(k.as_str(), "path" | "args") {
                            return Err(format!(
                                "unknown field `/scope/instantiations/{i}/{k}` in request"
                            ));
                        }
                    }
                    let p = req_str(obj, "path", &format!("/scope/instantiations/{i}"))?;
                    let a: Vec<String> = obj
                        .get("args")
                        .and_then(Value::as_array)
                        .and_then(|arr| arr.iter().map(|x| x.as_str().map(str::to_owned)).collect())
                        .ok_or_else(|| {
                            format!("/scope/instantiations/{i}/args must be an array of strings")
                        })?;
                    sorted.insert((p, a));
                }
                if !sorted.is_empty() {
                    let raw_insts: Vec<String> = sorted
                        .iter()
                        .map(|(p, a)| {
                            format_ordered_object(&[("path", json!(p)), ("args", json!(a))], 3)
                        })
                        .collect();
                    scope_fields.push((
                        "instantiations",
                        Value::String(format!("{RAW_SENTINEL}{}", format_raw_array(&raw_insts, 2))),
                    ));
                }
            }
        }
        other => return Err(format!("unrecognized request scope kind `{other}`")),
    }

    for k in proof_obj.keys() {
        if !matches!(
            k.as_str(),
            "source_root"
                | "specification"
                | "theorem"
                | "specification_module"
                | "theorem_module"
                | "sources"
        ) {
            return Err(format!("unknown field `/proof/{k}` in request"));
        }
    }
    let proof_source_root = req_str(proof_obj, "source_root", "/proof")?;
    let specification = opt_str(proof_obj, "specification", "Spec.specs", "/proof")?;
    let theorem = opt_str(proof_obj, "theorem", "Proof.verify", "/proof")?;
    let opt_nullable_str =
        |obj: &Map<String, Value>, key: &str, ptr: &str| -> Result<Value, String> {
            match obj.get(key) {
                None | Some(Value::Null) => Ok(Value::Null),
                Some(Value::String(s)) => Ok(Value::String(s.clone())),
                Some(_) => Err(format!("{ptr}/{key} must be a string or null")),
            }
        };
    let specification_module = opt_nullable_str(proof_obj, "specification_module", "/proof")?;
    let theorem_module = opt_nullable_str(proof_obj, "theorem_module", "/proof")?;
    let raw_sources = proof_obj
        .get("sources")
        .and_then(Value::as_array)
        .ok_or("/proof/sources must be an array")?;
    let mut rendered_sources = Vec::with_capacity(raw_sources.len());
    for (i, src) in raw_sources.iter().enumerate() {
        let ptr = format!("/proof/sources/{i}");
        let obj = src.as_object().ok_or_else(|| format!("{ptr} must be an object"))?;
        for k in obj.keys() {
            if !matches!(k.as_str(), "module" | "path" | "role") {
                return Err(format!("unknown field `{ptr}/{k}` in request"));
            }
        }
        let module = req_str(obj, "module", &ptr)?;
        let path = req_str(obj, "path", &ptr)?;
        let role = req_str(obj, "role", &ptr)?;
        if !matches!(role.as_str(), "specification" | "proof") {
            return Err(format!("unrecognized `{ptr}/role` `{role}`"));
        }
        rendered_sources.push(format_ordered_object(
            &[("module", json!(module)), ("path", json!(path)), ("role", json!(role))],
            3,
        ));
    }

    let mut comp_fields: Vec<(&str, Value)> = vec![
        ("source_root", json!(source_root)),
        ("crate_root", json!(crate_root)),
        ("crate_name", json!(crate_name)),
        ("crate_type", json!(crate_type)),
        ("panic", json!(panic)),
    ];
    if overflow_checks {
        comp_fields.push(("overflow_checks", json!(true)));
    }
    comp_fields.extend([
        ("edition", json!(edition)),
        ("target", json!(target)),
        ("cfg", json!(cfg)),
        ("env", json!(env)),
        ("source_files", json!(source_files)),
    ]);
    if let Some(stdlib) = stdlib_crate {
        comp_fields.push(("stdlib_crate", json!(stdlib)));
    }

    let proof_fields: Vec<(&str, Value)> = vec![
        ("source_root", json!(proof_source_root)),
        ("specification", json!(specification)),
        ("theorem", json!(theorem)),
        ("specification_module", specification_module),
        ("theorem_module", theorem_module),
        (
            "sources",
            Value::String(format!("{RAW_SENTINEL}{}", format_raw_array(&rendered_sources, 2))),
        ),
    ];

    let top_fields: Vec<(&str, Value)> = vec![
        ("schema_version", json!(1)),
        (
            "compilation",
            Value::String(format!("{RAW_SENTINEL}{}", format_ordered_object(&comp_fields, 1))),
        ),
        (
            "scope",
            Value::String(format!("{RAW_SENTINEL}{}", format_ordered_object(&scope_fields, 1))),
        ),
        (
            "proof",
            Value::String(format!("{RAW_SENTINEL}{}", format_ordered_object(&proof_fields, 1))),
        ),
    ];
    let pretty = format_ordered_object(&top_fields, 0);
    Ok(Some(sha256_hex(pretty.as_bytes())))
}

const RAW_SENTINEL: &str = "\0RAW_JSON\0";

fn format_raw_array(elements: &[String], depth: usize) -> String {
    if elements.is_empty() {
        return "[]".to_owned();
    }
    let elem_indent = "  ".repeat(depth + 1);
    let close_indent = "  ".repeat(depth);
    let body: Vec<String> = elements.iter().map(|e| format!("{elem_indent}{e}")).collect();
    format!("[\n{}\n{close_indent}]", body.join(",\n"))
}

fn format_ordered_object(fields: &[(&str, Value)], depth: usize) -> String {
    if fields.is_empty() {
        return "{}".to_owned();
    }
    let field_indent = "  ".repeat(depth + 1);
    let close_indent = "  ".repeat(depth);
    let mut lines = Vec::with_capacity(fields.len());
    for (k, v) in fields {
        let key_json = serde_json::to_string(k).expect("key JSON");
        let val_json = match v {
            Value::String(s) if s.starts_with(RAW_SENTINEL) => s[RAW_SENTINEL.len()..].to_owned(),
            other => indent_pretty_value(other, depth + 1),
        };
        lines.push(format!("{field_indent}{key_json}: {val_json}"));
    }
    format!("{{\n{}\n{close_indent}}}", lines.join(",\n"))
}

fn indent_pretty_value(val: &Value, depth: usize) -> String {
    let raw = serde_json::to_string_pretty(val).expect("value JSON");
    if !raw.contains('\n') {
        return raw;
    }
    let prefix = "  ".repeat(depth);
    let mut out = String::new();
    for (i, line) in raw.lines().enumerate() {
        if i > 0 {
            out.push('\n');
            out.push_str(&prefix);
        }
        out.push_str(line);
    }
    out
}

/// Validates and parses `/scope/instantiations` on a selected-unit receipt.
pub(crate) fn parse_receipt_instantiations(
    scope: &Map<String, Value>,
) -> Result<Vec<(String, Vec<String>)>, String> {
    let Some(val) = scope.get("instantiations") else {
        return Ok(Vec::new());
    };
    let arr = val.as_array().ok_or("/scope/instantiations must be an array")?;
    let mut out = Vec::with_capacity(arr.len());
    for (i, item) in arr.iter().enumerate() {
        let ptr = format!("/scope/instantiations/{i}");
        let obj = item.as_object().ok_or_else(|| format!("{ptr} must be an object"))?;
        for k in obj.keys() {
            if !matches!(k.as_str(), "path" | "args") {
                return Err(format!("unexpected field `{ptr}/{k}`"));
            }
        }
        let path = obj
            .get("path")
            .and_then(Value::as_str)
            .filter(|s| !s.is_empty())
            .ok_or_else(|| format!("{ptr}/path must be a non-empty string"))?;
        let args: Vec<String> = obj
            .get("args")
            .and_then(Value::as_array)
            .and_then(|a| a.iter().map(|x| x.as_str().map(str::to_owned)).collect())
            .ok_or_else(|| format!("{ptr}/args must be an array of strings"))?;
        out.push((path.to_owned(), args));
    }
    Ok(out)
}

/// Checks whether a `/selected` entry `(census_path, selected_path)` can be
/// produced by one of the validated `instantiations`
/// (`(inst_path, inst_args)`).
///
/// Matches `anneal-rustc-capture`'s `mono::instantiate_body`:
/// - Zero-argument entries (`inst_args.is_empty()`) name non-generic functions,
///   so `inst_path == census_path` and `selected_path == census_path`.
/// - Non-empty `inst_args` with `inst_path == census_path` instantiate a
///   generic free function, generic `impl` method, or default trait method in
///   place (`resolved_def == target_def`), so `selected_path` must differ from
///   `census_path`, carry concrete `<...>` arguments, and keep every module,
///   `impl` kind/trait, and callable segment aligned with `census_path`.
/// - Non-empty `inst_args` with `inst_path != census_path` only arise when
///   `Instance::try_resolve` dispatches a trait method `inst_path`
///   (`[mod::...::]Trait::method`, with no `<...>`) to a concrete or generic
///   trait `impl` method `census_path` (`<impl Trait for SelfTy>::method` or
///   `<SelfTy as Trait>::method`) for the same trait and method name.
pub(crate) fn matches_instantiation(
    census_path: &str,
    selected_path: &str,
    instantiations: &[(String, Vec<String>)],
) -> bool {
    instantiations
        .iter()
        .any(|(ip, args)| matches_single_instantiation(census_path, selected_path, ip, args))
}

#[derive(Debug, PartialEq, Eq)]
enum PathSegment {
    Ident { base: String, has_generics: bool },
    ImplTrait { trait_base: Vec<String> },
    ImplInherent,
    QualifiedAs { trait_base: Vec<String> },
}

fn matches_single_instantiation(
    census_path: &str,
    selected_path: &str,
    ip: &str,
    args: &[String],
) -> bool {
    let Some(cen_segs) = parse_callable_segments(census_path) else {
        return false;
    };
    let Some(sel_segs) = parse_callable_segments(selected_path) else {
        return false;
    };
    if args.is_empty() {
        return ip == census_path && selected_path == census_path;
    }
    if ip == census_path {
        return selected_path != census_path
            && selected_path.contains('<')
            && segments_match_same_def(&cen_segs, &sel_segs);
    }
    if ip.contains('<') {
        return false;
    }
    let Some(ip_segs) = parse_callable_segments(ip) else {
        return false;
    };
    if ip_segs.len() < 2 {
        return false;
    }
    let mut ip_idents = Vec::with_capacity(ip_segs.len());
    for seg in &ip_segs {
        match seg {
            PathSegment::Ident { base, has_generics: false } => ip_idents.push(base.clone()),
            _ => return false,
        }
    }
    let (ip_method, ip_trait) = ip_idents.split_last().expect("len >= 2");
    if cen_segs.len() < 2 || !segments_match_same_def(&cen_segs, &sel_segs) {
        return false;
    }
    let cen_method = match cen_segs.last() {
        Some(PathSegment::Ident { base, .. }) => base,
        _ => return false,
    };
    if cen_method != ip_method {
        return false;
    }
    let cen_impl_trait = match &cen_segs[cen_segs.len() - 2] {
        PathSegment::ImplTrait { trait_base } | PathSegment::QualifiedAs { trait_base } => {
            trait_base
        }
        _ => return false,
    };
    trait_bases_compatible(ip_trait, cen_impl_trait)
}

fn segments_match_same_def(cen: &[PathSegment], sel: &[PathSegment]) -> bool {
    if cen.len() != sel.len() || cen.is_empty() {
        return false;
    }
    if !matches!(cen.last(), Some(PathSegment::Ident { .. }))
        || !matches!(sel.last(), Some(PathSegment::Ident { .. }))
    {
        return false;
    }
    cen.iter().zip(sel).all(|(c, s)| match (c, s) {
        (PathSegment::Ident { base: cb, .. }, PathSegment::Ident { base: sb, .. }) => cb == sb,
        (PathSegment::ImplInherent, PathSegment::ImplInherent) => true,
        (PathSegment::ImplTrait { trait_base: ct }, PathSegment::ImplTrait { trait_base: st })
        | (
            PathSegment::QualifiedAs { trait_base: ct },
            PathSegment::QualifiedAs { trait_base: st },
        ) => trait_bases_compatible(ct, st),
        _ => false,
    })
}

fn trait_bases_compatible(a: &[String], b: &[String]) -> bool {
    !a.is_empty() && !b.is_empty() && (a.ends_with(b) || b.ends_with(a))
}

fn parse_callable_segments(path: &str) -> Option<Vec<PathSegment>> {
    let raw_segs = split_raw_segments(path)?;
    let mut out = Vec::with_capacity(raw_segs.len());
    for raw in raw_segs {
        out.push(parse_segment(raw)?);
    }
    if !matches!(out.last(), Some(PathSegment::Ident { .. })) {
        return None;
    }
    Some(out)
}

fn parse_segment(raw: &str) -> Option<PathSegment> {
    if raw.starts_with('<') {
        if !raw.ends_with('>') || skip_angle_group(raw, 0) != Some(raw.len()) {
            return None;
        }
        let inner = raw[1..raw.len() - 1].trim();
        if let Some(after_impl) =
            inner.strip_prefix("impl").filter(|rest| rest.starts_with(' ') || rest.starts_with('<'))
        {
            let rest = if after_impl.starts_with('<') {
                let end = skip_angle_group(after_impl, 0)?;
                &after_impl[end..]
            } else {
                after_impl
            }
            .trim();
            if rest.is_empty() {
                return None;
            }
            if let Some(for_idx) = find_top_level_keyword(rest, " for ") {
                let trait_str = rest[..for_idx].trim();
                let self_str = rest[for_idx + 5..].trim();
                if trait_str.is_empty() || self_str.is_empty() {
                    return None;
                }
                return Some(PathSegment::ImplTrait { trait_base: parse_trait_base(trait_str)? });
            }
            return Some(PathSegment::ImplInherent);
        }
        let as_idx = find_top_level_keyword(inner, " as ")?;
        let self_str = inner[..as_idx].trim();
        let trait_str = inner[as_idx + 4..].trim();
        if self_str.is_empty() || trait_str.is_empty() {
            return None;
        }
        return Some(PathSegment::QualifiedAs { trait_base: parse_trait_base(trait_str)? });
    }
    if let Some(lt_idx) = raw.find('<') {
        let prefix = &raw[..lt_idx];
        let base = prefix.strip_suffix("::").unwrap_or(prefix);
        if base.is_empty() || base.contains(':') || base.contains('>') {
            return None;
        }
        if skip_angle_group(raw, lt_idx) != Some(raw.len()) {
            return None;
        }
        Some(PathSegment::Ident { base: base.to_owned(), has_generics: true })
    } else {
        if raw.is_empty() || raw.contains(':') || raw.contains('>') {
            return None;
        }
        Some(PathSegment::Ident { base: raw.to_owned(), has_generics: false })
    }
}

fn parse_trait_base(trait_str: &str) -> Option<Vec<String>> {
    let s = trait_str.strip_prefix("::").unwrap_or(trait_str);
    let raw_segs = split_raw_segments(s)?;
    let mut idents = Vec::with_capacity(raw_segs.len());
    for raw in raw_segs {
        match parse_segment(raw)? {
            PathSegment::Ident { base, .. } => idents.push(base),
            _ => return None,
        }
    }
    if idents.is_empty() {
        None
    } else {
        Some(idents)
    }
}

fn split_raw_segments(s: &str) -> Option<Vec<&str>> {
    if s.is_empty() {
        return None;
    }
    let bytes = s.as_bytes();
    let mut segs = Vec::new();
    let mut seg_start = 0usize;
    let mut i = 0usize;
    while i < bytes.len() {
        if bytes[i] == b'<' {
            i = skip_angle_group(s, i)?;
        } else if i + 2 <= bytes.len() && &bytes[i..i + 2] == b"::" {
            let after = &s[i + 2..];
            let is_turbofish = after.starts_with('<')
                && !after.starts_with("<impl ")
                && !after.starts_with("<impl<")
                && i > seg_start
                && bytes[i - 1] != b'>';
            if is_turbofish {
                i = skip_angle_group(s, i + 2)?;
            } else {
                if i == seg_start {
                    return None;
                }
                segs.push(&s[seg_start..i]);
                i += 2;
                seg_start = i;
                if seg_start == bytes.len() {
                    return None;
                }
            }
        } else if bytes[i] == b'>' {
            return None;
        } else {
            let ch = s[i..].chars().next()?;
            i += ch.len_utf8();
        }
    }
    if seg_start == bytes.len() {
        return None;
    }
    segs.push(&s[seg_start..]);
    Some(segs)
}

fn find_top_level_keyword(s: &str, kw: &str) -> Option<usize> {
    let bytes = s.as_bytes();
    let kw_bytes = kw.as_bytes();
    let mut depth = 0usize;
    let mut i = 0usize;
    while i < bytes.len() {
        if bytes[i] == b'\'' {
            if let Some(next) = skip_char_literal(s, i) {
                i = next;
                continue;
            }
        }
        if depth > 0 && i + 2 <= bytes.len() && &bytes[i..i + 2] == b"->" {
            i += 2;
            continue;
        }
        match bytes[i] {
            b'<' => {
                depth += 1;
                i += 1;
            }
            b'>' => {
                depth = depth.checked_sub(1)?;
                i += 1;
            }
            _ => {
                if depth == 0
                    && i + kw_bytes.len() <= bytes.len()
                    && &bytes[i..i + kw_bytes.len()] == kw_bytes
                {
                    return Some(i);
                }
                let ch = s[i..].chars().next()?;
                i += ch.len_utf8();
            }
        }
    }
    None
}

fn skip_char_literal(s: &str, pos: usize) -> Option<usize> {
    let bytes = s.as_bytes();
    if bytes.get(pos) != Some(&b'\'') {
        return None;
    }
    if bytes.get(pos + 1) == Some(&b'\\') {
        let mut j = pos + 3;
        while j < bytes.len() && j <= pos + 12 {
            if bytes[j] == b'\'' {
                return Some(j + 1);
            }
            j += 1;
        }
        return None;
    }
    let rest = s.get(pos + 1..)?;
    let ch = rest.chars().next()?;
    if ch != '\'' && ch != '\\' && rest.as_bytes().get(ch.len_utf8()) == Some(&b'\'') {
        Some(pos + 1 + ch.len_utf8() + 1)
    } else {
        None
    }
}

fn skip_angle_group(s: &str, start_lt: usize) -> Option<usize> {
    let bytes = s.as_bytes();
    if bytes.get(start_lt) != Some(&b'<') {
        return None;
    }
    let mut depth = 0usize;
    let mut i = start_lt;
    while i < bytes.len() {
        if bytes[i] == b'\'' {
            if let Some(next) = skip_char_literal(s, i) {
                i = next;
                continue;
            }
        }
        if depth > 0 && i + 2 <= bytes.len() && &bytes[i..i + 2] == b"->" {
            i += 2;
            continue;
        }
        match bytes[i] {
            b'<' => {
                depth += 1;
                i += 1;
            }
            b'>' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(i + 1);
                }
                i += 1;
            }
            _ => {
                let ch = s[i..].chars().next()?;
                i += ch.len_utf8();
            }
        }
    }
    None
}
