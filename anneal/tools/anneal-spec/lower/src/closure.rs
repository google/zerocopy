// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Deterministic `spec-closure.golden` generation, standalone FIPS 180-4
//! SHA-256, and optional `capture.json` callee ingestion.

use std::collections::BTreeMap;

use serde_json::{json, Value};

/// Verification scope reflected in `MirEnvelopeSpec.gaps`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Scope {
    /// Selected-unit scope (`.selectedUnitScope` disclosed in `gaps`).
    #[default]
    Unit,
    /// Whole-crate scope (no `.selectedUnitScope` gap).
    Crate,
}

/// Summary of one body from `capture.json` used to synthesize UB-freedom
/// entries for unannotated safe callees and reject unannotated `unsafe`
/// callees.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapturedBodySummary {
    /// Full `rust-path-v1::...` identity string from `capture.json` (or
    /// normalized with `rust-path-v1::` when unprefixed).
    pub identity: String,
    pub is_unsafe: bool,
    pub params_lean: Vec<String>,
    pub ret_lean: String,
    pub has_raw_ptr_local: bool,
}

/// Summary of a `capture.json` artifact passed via `--capture-json`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapturedProgramSummary {
    pub scope: Scope,
    pub mir_profile_version: u32,
    pub bodies: Vec<CapturedBodySummary>,
}

/// One declaration recorded in `SpecClosureGolden.user_declarations`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClosureDecl {
    pub name: String,
    pub kind: &'static str,
}

/// Summary of one `MirVerifiedEntry` for `envelope_summary` and
/// `non_normative_context.expanded_contracts`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClosureEntry {
    pub identity: String,
    pub signature: String,
    pub is_unsafe: bool,
    pub safety_pre: Option<String>,
    pub behavior_pre: Option<String>,
    pub post_return: Option<String>,
    pub max_steps: Option<String>,
    pub terminates: bool,
    pub no_unwind: bool,
    pub no_abort: bool,
    pub require_inhabited: bool,
}

const SHA256_K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// Computes the lowercase 64-character hexadecimal FIPS 180-4 SHA-256 digest
/// of `data`.
pub fn sha256_hex(data: &[u8]) -> String {
    let mut state: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    let bit_len = (data.len() as u64).checked_mul(8).expect("input fits in u64 bits");
    let mut padded = Vec::with_capacity((data.len() + 9).div_ceil(64) * 64);
    padded.extend_from_slice(data);
    padded.push(0x80);
    while (padded.len() % 64) != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());

    for chunk in padded.as_chunks::<64>().0 {
        let mut w = [0u32; 64];
        for (i, &word) in chunk.as_chunks::<4>().0.iter().enumerate() {
            w[i] = u32::from_be_bytes(word);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = state;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 =
                h.wrapping_add(s1).wrapping_add(ch).wrapping_add(SHA256_K[i]).wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);

            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }
        for (st, delta) in state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
            *st = st.wrapping_add(delta);
        }
    }

    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(64);
    for word in state {
        for b in word.to_be_bytes() {
            out.push(HEX[(b >> 4) as usize] as char);
            out.push(HEX[(b & 0x0f) as usize] as char);
        }
    }
    out
}

/// Renders pretty-printed `spec-closure.golden` JSON matching `cargo-anneal`'s
/// `SpecClosureGolden` schema.
pub fn render_spec_closure_golden(
    lean_module: &str,
    spec_lean: &str,
    decls: &[ClosureDecl],
    entries: &[ClosureEntry],
    claim_shapes: &[&str],
    gaps: &[String],
    has_step_bounds: bool,
) -> String {
    let trailing_newline = spec_lean.ends_with('\n');
    let body = spec_lean.strip_suffix('\n').unwrap_or(spec_lean);
    let lines: Vec<String> = if body.is_empty() && !trailing_newline {
        Vec::new()
    } else {
        body.split('\n').map(String::from).collect()
    };
    let mut user_decls: Vec<(String, String, &'static str)> = decls
        .iter()
        .map(|d| (lean_module.to_string(), format!("{lean_module}.{}", d.name), d.kind))
        .collect();
    user_decls.sort_by(|a, b| (&a.0, &a.1).cmp(&(&b.0, &b.1)));
    let user_declarations: Vec<Value> = user_decls
        .into_iter()
        .map(|(m, n, k)| {
            json!({
                "module": m,
                "name": n,
                "kind": k,
            })
        })
        .collect();

    let entries_json: Vec<Value> = entries
        .iter()
        .map(|e| {
            json!({
                "identity": e.identity,
                "is_unsafe": e.is_unsafe,
                "terminates": e.terminates,
                "no_unwind": e.no_unwind,
                "no_abort": e.no_abort,
                "require_inhabited": e.require_inhabited,
            })
        })
        .collect();

    let expanded_contracts: Vec<Value> = entries
        .iter()
        .map(|e| {
            json!({
                "identity": e.identity,
                "signature": e.signature,
                "safety_pre": e.safety_pre,
                "behavior_pre": e.behavior_pre,
                "post_return": e.post_return,
                "max_steps": e.max_steps,
                "effects": {
                    "terminates": e.terminates,
                    "no_unwind": e.no_unwind,
                    "no_abort": e.no_abort,
                },
                "require_inhabited": e.require_inhabited,
            })
        })
        .collect();

    let doc = json!({
        "root_spec_module": {
            "module": lean_module,
            "sha256": sha256_hex(spec_lean.as_bytes()),
            "trailing_newline": trailing_newline,
            "lines": lines,
        },
        "imported_spec_modules": BTreeMap::<String, Value>::new(),
        "user_declarations": user_declarations,
        "envelope_summary": {
            "entries": entries_json,
            "stubs": Vec::<String>::new(),
            "refutations": Vec::<String>::new(),
            "claim_shapes": claim_shapes,
            "gaps": gaps,
            "law_heads": Vec::<Value>::new(),
            "has_step_bounds": has_step_bounds,
        },
        "non_normative_context": {
            "expanded_contracts": expanded_contracts,
        },
    });
    let mut rendered = serde_json::to_string_pretty(&doc).expect("spec-closure JSON serializes");
    rendered.push('\n');
    rendered
}

/// Parses `capture.json` (`{ "program": { ... } }` or `{ "bodies": ... }`)
/// into [`CapturedProgramSummary`].
pub fn parse_capture_json(text: &str) -> Result<CapturedProgramSummary, String> {
    let root: Value =
        serde_json::from_str(text).map_err(|e| format!("invalid capture JSON: {e}"))?;
    let prog = root.get("program").unwrap_or(&root);
    let scope = match prog.get("scope") {
        Some(Value::String(s)) if s == "crate" => Scope::Crate,
        Some(Value::String(s)) if s == "unit" || s == "selected_unit" => Scope::Unit,
        Some(Value::Object(map)) => match map.get("kind").and_then(Value::as_str) {
            Some("crate") => Scope::Crate,
            Some("unit" | "selected_unit") => Scope::Unit,
            other => return Err(format!("unsupported capture scope kind {other:?}")),
        },
        None => Scope::Unit,
        other => return Err(format!("unsupported capture scope {other:?}")),
    };
    let mir_profile_version = prog
        .get("mir_profile_version")
        .and_then(Value::as_u64)
        .unwrap_or(1)
        .try_into()
        .map_err(|_| "invalid mir_profile_version in capture JSON".to_string())?;
    let raw_bodies = prog
        .get("bodies")
        .and_then(Value::as_array)
        .ok_or_else(|| "capture JSON missing `bodies` array".to_string())?;
    let mut bodies = Vec::with_capacity(raw_bodies.len());
    for (idx, body) in raw_bodies.iter().enumerate() {
        let raw_id = body
            .get("identity")
            .and_then(Value::as_str)
            .filter(|s| !s.is_empty())
            .ok_or_else(|| format!("capture body #{idx} missing non-empty `identity`"))?;
        let identity = if raw_id.starts_with("rust-path-v1::") {
            raw_id.to_string()
        } else {
            format!("rust-path-v1::{raw_id}")
        };
        let is_unsafe = body
            .get("is_unsafe")
            .and_then(Value::as_bool)
            .ok_or_else(|| format!("capture body `{identity}` missing boolean `is_unsafe`"))?;
        let arg_count: usize = body
            .get("arg_count")
            .and_then(Value::as_u64)
            .ok_or_else(|| format!("capture body `{identity}` missing `arg_count`"))?
            .try_into()
            .map_err(|_| format!("capture body `{identity}` `arg_count` overflows usize"))?;
        let local_tys = body
            .get("local_tys")
            .and_then(Value::as_array)
            .ok_or_else(|| format!("capture body `{identity}` missing `local_tys` array"))?;
        if local_tys.len() < 1 + arg_count {
            return Err(format!(
                "capture body `{identity}` has {} local_tys for arg_count={arg_count}",
                local_tys.len()
            ));
        }
        let ret_lean = capture_ty_to_lean(&local_tys[0])
            .map_err(|e| format!("capture body `{identity}` return type: {e}"))?;
        let mut params_lean = Vec::with_capacity(arg_count);
        for (p_idx, ty_val) in local_tys[1..=arg_count].iter().enumerate() {
            params_lean.push(
                capture_ty_to_lean(ty_val)
                    .map_err(|e| format!("capture body `{identity}` param #{p_idx}: {e}"))?,
            );
        }
        let has_raw_ptr_local = local_tys.iter().any(ty_contains_raw_ptr);
        bodies.push(CapturedBodySummary {
            identity,
            is_unsafe,
            params_lean,
            ret_lean,
            has_raw_ptr_local,
        });
    }
    Ok(CapturedProgramSummary { scope, mir_profile_version, bodies })
}

fn parse_int_width(v: &Value) -> Result<&'static str, String> {
    match v.as_str() {
        Some("i8") => Ok(".i8"),
        Some("i16") => Ok(".i16"),
        Some("i32") => Ok(".i32"),
        Some("i64") => Ok(".i64"),
        Some("i128") => Ok(".i128"),
        Some("isize") => Ok(".isize"),
        other => Err(format!("unknown integer width {other:?}")),
    }
}

fn parse_mutability(v: &Value) -> Result<&'static str, String> {
    match v.as_str() {
        Some("shared" | "not" | "imm") => Ok(".shared"),
        Some("mut") => Ok(".mut"),
        other => Err(format!("unknown mutability {other:?}")),
    }
}

fn ty_contains_raw_ptr(v: &Value) -> bool {
    match v.get("kind").and_then(Value::as_str) {
        Some("raw_ptr") => true,
        Some("tuple") => v
            .get("fields")
            .and_then(Value::as_array)
            .is_some_and(|fs| fs.iter().any(ty_contains_raw_ptr)),
        Some("ref" | "box_ptr") => v.get("pointee").is_some_and(ty_contains_raw_ptr),
        Some("slice" | "array" | "range" | "range_from" | "range_to" | "option" | "vec") => {
            v.get("elem").is_some_and(ty_contains_raw_ptr)
        }
        _ => false,
    }
}

fn capture_ty_to_lean(v: &Value) -> Result<String, String> {
    let kind =
        v.get("kind").and_then(Value::as_str).ok_or_else(|| format!("missing `kind` in {v}"))?;
    match kind {
        "bool" => Ok(".bool".into()),
        "char" => Ok(".char".into()),
        "ordering" => Ok(".ordering".into()),
        "unit" => Ok(".unit".into()),
        "never" => Ok(".never".into()),
        "str" => Ok(".str".into()),
        "int" => {
            let w = parse_int_width(v.get("width").unwrap_or(&Value::Null))?;
            let signed = v
                .get("signed")
                .and_then(Value::as_bool)
                .ok_or_else(|| "int type missing `signed`".to_string())?;
            Ok(format!(".int {w} {signed}"))
        }
        "overflow_pair" => {
            let w = parse_int_width(v.get("width").unwrap_or(&Value::Null))?;
            let signed = v
                .get("signed")
                .and_then(Value::as_bool)
                .ok_or_else(|| "overflow_pair missing `signed`".to_string())?;
            Ok(format!(".tuple [.int {w} {signed}, .bool]"))
        }
        "tuple" => {
            let fields = v
                .get("fields")
                .and_then(Value::as_array)
                .ok_or_else(|| "tuple type missing `fields`".to_string())?;
            let mut rendered = Vec::with_capacity(fields.len());
            for f in fields {
                rendered.push(capture_ty_to_lean(f)?);
            }
            Ok(format!(".tuple [{}]", rendered.join(", ")))
        }
        "ref" => {
            let m = parse_mutability(v.get("mutability").unwrap_or(&Value::Null))?;
            let inner = v.get("pointee").ok_or_else(|| "ref type missing `pointee`".to_string())?;
            Ok(format!(".ref {m} ({})", capture_ty_to_lean(inner)?))
        }
        "raw_ptr" => {
            let m = parse_mutability(v.get("mutability").unwrap_or(&Value::Null))?;
            let inner =
                v.get("pointee").ok_or_else(|| "raw_ptr type missing `pointee`".to_string())?;
            Ok(format!(".rawPtr {m} ({})", capture_ty_to_lean(inner)?))
        }
        "slice" => {
            let elem = v.get("elem").ok_or_else(|| "slice type missing `elem`".to_string())?;
            Ok(format!(".slice ({})", capture_ty_to_lean(elem)?))
        }
        "array" => {
            let elem = v.get("elem").ok_or_else(|| "array type missing `elem`".to_string())?;
            let len = v
                .get("len")
                .and_then(Value::as_u64)
                .ok_or_else(|| "array type missing `len`".to_string())?;
            Ok(format!(".array ({}) {len}", capture_ty_to_lean(elem)?))
        }
        "range_to" => {
            let elem = v.get("elem").ok_or_else(|| "range_to missing `elem`".to_string())?;
            Ok(format!(".rangeTo ({})", capture_ty_to_lean(elem)?))
        }
        "range_from" => {
            let elem = v.get("elem").ok_or_else(|| "range_from missing `elem`".to_string())?;
            Ok(format!(".rangeFrom ({})", capture_ty_to_lean(elem)?))
        }
        "range" => {
            let elem = v.get("elem").ok_or_else(|| "range missing `elem`".to_string())?;
            Ok(format!(".range ({})", capture_ty_to_lean(elem)?))
        }
        "option" => {
            let elem = v.get("elem").ok_or_else(|| "option missing `elem`".to_string())?;
            Ok(format!(".option ({})", capture_ty_to_lean(elem)?))
        }
        other => Err(format!("unsupported captured MIR type kind `{other}`")),
    }
}

#[cfg(test)]
mod tests {
    use super::sha256_hex;

    #[test]
    fn sha256_matches_fips_180_4_vectors() {
        assert_eq!(
            sha256_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        assert_eq!(
            sha256_hex(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        );
    }
}
