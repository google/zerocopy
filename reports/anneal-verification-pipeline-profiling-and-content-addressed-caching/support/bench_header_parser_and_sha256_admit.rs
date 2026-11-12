// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Standalone Rust benchmark and prototype for Track 3:
//! - Experiment 3A(iv): Pure-Rust Lean 4 header parser (`parse_lean_header`)
//!   matching `Lean.Parser.Module.parseHeader` + `Lean.Elab.HeaderSyntax.imports`
//!   at `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`.
//! - Experiment 3B(i)-(iv): Lockfile SHA-256 admission profiling & optimization:
//!   (i)   Sequential `sha256_file` (`sha2` with SHA-NI) vs. pure software SHA-256,
//!         plus redundant `moduleIdentities` re-hashing in `target.rs`.
//!   (ii)  Lazy / transitive-closure subsets and companion-part selection.
//!   (iii) Preallocated buffer reuse and multi-threaded parallel hashing (2, 4, 8, 16 threads).
//!   (iv)  Stat-keyed `(dev, ino, size, mtime_nsec, ctime_nsec)` admission cache.

use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::io::Read;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::time::Instant;

const PARTS: [&str; 5] = ["olean", "olean.server", "olean.private", "ir.sig", "ir"];

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ImportEdge {
    pub module: String,
    pub import_all: bool,
    pub is_exported: bool,
    pub is_meta: bool,
}

// ---------------------------------------------------------------------------
// Experiment 3A(iv): Pure-Rust Lean 4 Header Parser
// Mirrors Lean.Parser.Basic.{whitespace, finishCommentBlock, identFnAux} and
// Lean.Parser.Module.parseHeader + Lean.Elab.HeaderSyntax.imports in
// leanprover/lean4 v4.34.1 (5045d0056413266e57c625dcd7c365b10e377c52).
// ---------------------------------------------------------------------------

struct HeaderLexer<'a> {
    src: &'a str,
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> HeaderLexer<'a> {
    fn new(src: &'a str) -> Self {
        Self {
            src,
            bytes: src.as_bytes(),
            pos: 0,
        }
    }

    fn at_end(&self) -> bool {
        self.pos >= self.bytes.len()
    }

    /// Mirrors `Lean.Parser.Basic.whitespace` and `finishCommentBlock`
    /// (`src/Lean/Parser/Basic.lean:537-588`).
    /// - Rejects `\t` and isolated `\r`.
    /// - Skips `--` line comments to `\n` or EOF.
    /// - Skips nested `/- ... -/` block comments, EXCEPT `/--` and `/-!`
    ///   doc/module-doc comments, which are tokens that terminate the header.
    fn skip_whitespace(&mut self) -> Result<(), String> {
        while self.pos < self.bytes.len() {
            let b = self.bytes[self.pos];
            if b == b'\t' {
                return Err("tabs are not allowed; please configure your editor to expand them".into());
            }
            if b == b'\r' {
                if self.pos + 1 < self.bytes.len() && self.bytes[self.pos + 1] == b'\n' {
                    self.pos += 2;
                    continue;
                }
                return Err("isolated carriage returns are not allowed".into());
            }
            if b == b' ' || b == b'\n' || b == 0x0c || b == 0x0b {
                self.pos += 1;
                continue;
            }
            // Check Unicode whitespace if non-ASCII
            if b >= 0x80 {
                let ch = self.src[self.pos..].chars().next().unwrap();
                if ch.is_whitespace() {
                    self.pos += ch.len_utf8();
                    continue;
                }
                break;
            }
            if b == b'-' && self.pos + 1 < self.bytes.len() && self.bytes[self.pos + 1] == b'-' {
                self.pos += 2;
                while self.pos < self.bytes.len() && self.bytes[self.pos] != b'\n' {
                    if self.bytes[self.pos] == b'\r'
                        && (self.pos + 1 >= self.bytes.len() || self.bytes[self.pos + 1] != b'\n')
                    {
                        return Err("isolated carriage returns are not allowed".into());
                    }
                    self.pos += 1;
                }
                continue;
            }
            if b == b'/' && self.pos + 1 < self.bytes.len() && self.bytes[self.pos + 1] == b'-' {
                // In Lean 4 (`Basic.lean:584`), `/--` and `/-!` are doc-comment tokens, not whitespace!
                if self.pos + 2 < self.bytes.len() {
                    let third = self.bytes[self.pos + 2];
                    if third == b'-' || third == b'!' {
                        break;
                    }
                }
                self.pos += 2;
                let mut nesting = 1usize;
                while nesting > 0 {
                    if self.pos >= self.bytes.len() {
                        return Err("unterminated comment".into());
                    }
                    if self.bytes[self.pos] == b'-'
                        && self.pos + 1 < self.bytes.len()
                        && self.bytes[self.pos + 1] == b'/'
                    {
                        nesting -= 1;
                        self.pos += 2;
                    } else if self.bytes[self.pos] == b'/'
                        && self.pos + 1 < self.bytes.len()
                        && self.bytes[self.pos + 1] == b'-'
                    {
                        nesting += 1;
                        self.pos += 2;
                    } else {
                        let ch = self.src[self.pos..].chars().next().unwrap();
                        self.pos += ch.len_utf8();
                    }
                }
                continue;
            }
            break;
        }
        Ok(())
    }

    fn is_id_first(ch: char) -> bool {
        ch.is_alphabetic() || ch == '_'
    }

    fn is_id_rest(ch: char) -> bool {
        ch.is_alphanumeric() || ch == '_' || ch == '\'' || ch == '?' || ch == '!'
    }

    /// Try to match an exact keyword token (`module`, `prelude`, `public`, `meta`, `import`, `all`)
    /// not followed by an identifier continuation character or `.` identifier continuation.
    fn try_keyword(&mut self, kw: &str) -> Result<bool, String> {
        let end = self.pos + kw.len();
        if end > self.bytes.len() || &self.src[self.pos..end] != kw {
            return Ok(false);
        }
        if end < self.bytes.len() {
            let next_ch = self.src[end..].chars().next().unwrap();
            if Self::is_id_rest(next_ch) || next_ch == '«' {
                return Ok(false);
            }
            if next_ch == '.' && end + 1 < self.bytes.len() {
                let after_dot = self.src[end + 1..].chars().next().unwrap();
                if Self::is_id_first(after_dot) || after_dot == '«' {
                    return Ok(false);
                }
            }
        }
        self.pos = end;
        self.skip_whitespace()?;
        Ok(true)
    }

    /// Parse a hierarchical Lean module identifier (`identWithPartialTrailingDot`).
    fn parse_module_ident(&mut self) -> Result<String, String> {
        let start_pos = self.pos;
        let mut components = Vec::new();
        loop {
            if self.at_end() {
                return Err("expected module identifier".into());
            }
            let ch = self.src[self.pos..].chars().next().unwrap();
            if ch == '«' {
                self.pos += ch.len_utf8();
                let part_start = self.pos;
                while !self.at_end() {
                    let c = self.src[self.pos..].chars().next().unwrap();
                    if c == '»' {
                        break;
                    }
                    self.pos += c.len_utf8();
                }
                if self.at_end() {
                    return Err("unterminated identifier escape".into());
                }
                components.push(&self.src[part_start..self.pos]);
                let close = self.src[self.pos..].chars().next().unwrap();
                self.pos += close.len_utf8();
            } else if Self::is_id_first(ch) {
                let part_start = self.pos;
                self.pos += ch.len_utf8();
                while !self.at_end() {
                    let c = self.src[self.pos..].chars().next().unwrap();
                    if Self::is_id_rest(c) {
                        self.pos += c.len_utf8();
                    } else {
                        break;
                    }
                }
                let part = &self.src[part_start..self.pos];
                if components.is_empty()
                    && matches!(
                        part,
                        "module" | "prelude" | "public" | "meta" | "import" | "all"
                    )
                    && (self.at_end() || self.bytes[self.pos] != b'.')
                {
                    self.pos = start_pos;
                    return Err(format!("unexpected keyword `{part}` where module identifier expected"));
                }
                components.push(part);
            } else {
                return Err("expected module identifier".into());
            }

            if !self.at_end() && self.bytes[self.pos] == b'.' {
                if self.pos + 1 < self.bytes.len() {
                    let after_dot = self.src[self.pos + 1..].chars().next().unwrap();
                    if Self::is_id_first(after_dot) || after_dot == '«' {
                        self.pos += 1;
                        continue;
                    }
                }
                return Err("trailing dot on import identifier".into());
            }
            break;
        }
        self.skip_whitespace()?;
        Ok(components.join("."))
    }
}

pub fn parse_lean_header(src: &str) -> Result<Vec<ImportEdge>, String> {
    let mut lex = HeaderLexer::new(src);
    lex.skip_whitespace()?;

    let has_module = lex.try_keyword("module")?;
    let has_prelude = lex.try_keyword("prelude")?;

    let mut imports = Vec::new();
    if !has_prelude {
        imports.push(ImportEdge {
            module: "Init".to_string(),
            import_all: false,
            is_exported: true,
            is_meta: false,
        });
        imports.push(ImportEdge {
            module: "Init".to_string(),
            import_all: false,
            is_exported: true,
            is_meta: true,
        });
    }

    loop {
        let saved = lex.pos;
        let is_public = lex.try_keyword("public")?;
        let is_meta = lex.try_keyword("meta")?;
        // In `Module/Syntax.lean:22-23`, `atomic (optional «public» >> optional «meta» >> "import ")`
        // backtracks if `"import"` does not follow `"public"` or `"meta"` (e.g., `public section`).
        if !lex.try_keyword("import")? {
            lex.pos = saved;
            break;
        }
        let import_all = lex.try_keyword("all")?;
        let module = lex.parse_module_ident()?;

        if !has_module {
            if is_public {
                return Err("cannot use `public import` without `module`".into());
            }
            if is_meta {
                return Err("cannot use `meta import` without `module`".into());
            }
            if import_all {
                return Err("cannot use `import all` without `module`".into());
            }
        } else if import_all && is_public {
            return Err("cannot use `all` with `public import`".into());
        }

        imports.push(ImportEdge {
            module,
            import_all,
            is_exported: is_public || !has_module,
            is_meta,
        });
    }

    Ok(imports)
}

// ---------------------------------------------------------------------------
// Experiment 3B(i): Pure Software SHA-256 (to compare against SHA-NI in `sha2`)
// ---------------------------------------------------------------------------

const K256: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

#[inline(never)]
fn sha256_software_block(state: &mut [u32; 8], block: &[u8; 64]) {
    let mut w = [0u32; 64];
    for i in 0..16 {
        w[i] = u32::from_be_bytes([
            block[i * 4],
            block[i * 4 + 1],
            block[i * 4 + 2],
            block[i * 4 + 3],
        ]);
    }
    for i in 16..64 {
        let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
        let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16]
            .wrapping_add(s0)
            .wrapping_add(w[i - 7])
            .wrapping_add(s1);
    }
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *state;
    for i in 0..64 {
        let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
        let ch = (e & f) ^ ((!e) & g);
        let temp1 = h
            .wrapping_add(s1)
            .wrapping_add(ch)
            .wrapping_add(K256[i])
            .wrapping_add(w[i]);
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
    state[0] = state[0].wrapping_add(a);
    state[1] = state[1].wrapping_add(b);
    state[2] = state[2].wrapping_add(c);
    state[3] = state[3].wrapping_add(d);
    state[4] = state[4].wrapping_add(e);
    state[5] = state[5].wrapping_add(f);
    state[6] = state[6].wrapping_add(g);
    state[7] = state[7].wrapping_add(h);
}

fn sha256_software(data: &[u8]) -> [u8; 32] {
    let mut state: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
        0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
    ];
    let mut chunks = data.chunks_exact(64);
    for chunk in &mut chunks {
        sha256_software_block(&mut state, chunk.try_into().unwrap());
    }
    let rem = chunks.remainder();
    let mut pad = [0u8; 128];
    pad[..rem.len()].copy_from_slice(rem);
    pad[rem.len()] = 0x80;
    let bit_len = (data.len() as u64) * 8;
    if rem.len() < 56 {
        pad[56..64].copy_from_slice(&bit_len.to_be_bytes());
        sha256_software_block(&mut state, pad[..64].try_into().unwrap());
    } else {
        pad[120..128].copy_from_slice(&bit_len.to_be_bytes());
        sha256_software_block(&mut state, pad[..64].try_into().unwrap());
        sha256_software_block(&mut state, pad[64..128].try_into().unwrap());
    }
    let mut out = [0u8; 32];
    for (i, word) in state.iter().enumerate() {
        out[i * 4..(i + 1) * 4].copy_from_slice(&word.to_be_bytes());
    }
    out
}

fn hex_encode(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        s.push(HEX[(b >> 4) as usize] as char);
        s.push(HEX[(b & 0x0f) as usize] as char);
    }
    s
}

#[derive(Clone)]
struct FileToHash {
    path: PathBuf,
    expected_hex: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct StatKey {
    dev: u64,
    ino: u64,
    size: u64,
    mtime_sec: i64,
    mtime_nsec: i64,
    ctime_sec: i64,
    ctime_nsec: i64,
}

impl StatKey {
    fn from_meta(m: &fs::Metadata) -> Self {
        Self {
            dev: m.dev(),
            ino: m.ino(),
            size: m.len(),
            mtime_sec: m.mtime(),
            mtime_nsec: m.mtime_nsec(),
            ctime_sec: m.ctime(),
            ctime_nsec: m.ctime_nsec(),
        }
    }
}

fn collect_lock_files(lock_path: &Path, prefix: &Path) -> Vec<FileToHash> {
    let text = fs::read_to_string(lock_path).unwrap();
    let v: Value = serde_json::from_str(&text).unwrap();
    let modules = v["modules"].as_object().unwrap();
    let mut out = Vec::new();
    for (mod_name, rec) in modules {
        let rel = mod_name.replace('.', "/");
        out.push(FileToHash {
            path: prefix.join("src/lean").join(format!("{rel}.lean")),
            expected_hex: rec["sourceSha256"].as_str().unwrap().to_ascii_lowercase(),
        });
        let parts = rec["parts"].as_object().unwrap();
        for p in PARTS {
            if let Some(sha) = parts.get(p).and_then(Value::as_str) {
                out.push(FileToHash {
                    path: prefix.join("lib/lean").join(format!("{rel}.{p}")),
                    expected_hex: sha.to_ascii_lowercase(),
                });
            }
        }
    }
    out
}

fn bench_fn<F: FnMut()>(runs: usize, mut f: F) -> Value {
    let mut samples_ms = Vec::with_capacity(runs);
    for _ in 0..runs {
        let t0 = Instant::now();
        f();
        samples_ms.push(t0.elapsed().as_secs_f64() * 1000.0);
    }
    samples_ms.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let median = samples_ms[runs / 2];
    let mean = samples_ms.iter().sum::<f64>() / (runs as f64);
    let min = samples_ms[0];
    json!({
        "runs": runs,
        "median_ms": (median * 1000.0).round() / 1000.0,
        "mean_ms": (mean * 1000.0).round() / 1000.0,
        "min_ms": (min * 1000.0).round() / 1000.0,
    })
}

fn main() {
    let track3 = Path::new("/tmp/ref_research_stack221_perf/track3");
    let mvp_src = Path::new("/tmp/ref_research_stack221_perf/mvp_src");
    let prefix = Path::new("/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1");

    // -----------------------------------------------------------------------
    // 1. Verify & Benchmark Experiment 3A(iv): Pure-Rust Header Parser
    // -----------------------------------------------------------------------
    let mut header_bench = serde_json::Map::new();
    for fixture in ["scalar", "spin", "starnix"] {
        let stage = track3.join("stages").join(fixture);
        let req_text = fs::read_to_string(stage.join("request-001-headers.json")).unwrap();
        let req_val: Value = serde_json::from_str(&req_text).unwrap();
        let exp_text = fs::read_to_string(stage.join("request-001-headers.result.json")).unwrap();
        let exp_val: Value = serde_json::from_str(&exp_text).unwrap();
        let exp_headers = exp_val["result"]["headers"].as_array().unwrap();

        let sources: Vec<(String, PathBuf)> = req_val["sources"]
            .as_array()
            .unwrap()
            .iter()
            .map(|pair| {
                let arr = pair.as_array().unwrap();
                (
                    arr[0].as_str().unwrap().to_string(),
                    PathBuf::from(arr[1].as_str().unwrap()),
                )
            })
            .collect();

        // Check exact agreement with Lean's Parser.parseHeader + Elab.HeaderSyntax.imports
        for ((mod_name, path), exp_h) in sources.iter().zip(exp_headers.iter()) {
            let text = fs::read_to_string(path).unwrap();
            let actual_imports = parse_lean_header(&text).expect("valid fixture header");
            let actual_json = json!({
                "module": mod_name,
                "imports": actual_imports,
            });
            assert_eq!(&actual_json, exp_h, "Header mismatch on {fixture}:{mod_name}");
        }

        // Benchmark 100 runs of reading + parsing all headers in the fixture
        let timing = bench_fn(100, || {
            for (_, path) in &sources {
                let text = fs::read_to_string(path).unwrap();
                let imps = parse_lean_header(&text).unwrap();
                std::hint::black_box(imps);
            }
        });
        header_bench.insert(
            fixture.to_string(),
            json!({
                "file_count": sources.len(),
                "exact_match_with_lean_parser": true,
                "timing": timing,
            }),
        );
    }

    // Edge-case unit tests for `parse_lean_header`
    assert_eq!(
        parse_lean_header("prelude\n-- import Evil\n/- nested /- import Evil2 -/ comment -/\nimport Init.Prelude\n/-! # Module doc\nimport NotAnImport -/\ndef x := 1\n").unwrap(),
        vec![ImportEdge {
            module: "Init.Prelude".into(),
            import_all: false,
            is_exported: true,
            is_meta: false,
        }]
    );
    assert_eq!(
        parse_lean_header("import Foo.«bar.baz».Qux\n").unwrap(),
        vec![
            ImportEdge { module: "Init".into(), import_all: false, is_exported: true, is_meta: false },
            ImportEdge { module: "Init".into(), import_all: false, is_exported: true, is_meta: true },
            ImportEdge { module: "Foo.bar.baz.Qux".into(), import_all: false, is_exported: true, is_meta: false },
        ]
    );
    assert!(parse_lean_header("prelude\n\timport Init.Prelude\n").is_err());
    assert!(parse_lean_header("prelude\n/- unterminated comment\nimport Init.Prelude\n").is_err());
    assert!(parse_lean_header("prelude\npublic import Init.Prelude\n").is_err());
    assert!(parse_lean_header("prelude\nimport all Init.Prelude\n").is_err());

    // -----------------------------------------------------------------------
    // 2. Experiment 3B: SHA-256 Lockfile Admission Benchmarks
    // -----------------------------------------------------------------------
    let f_files = collect_lock_files(&mvp_src.join("trusted/lean/foundation-lock.json"), prefix);
    let l_files = collect_lock_files(&mvp_src.join("trusted/audit/library-lock.json"), prefix);
    let mut all_files = f_files.clone();
    all_files.extend(l_files.iter().cloned());

    // Collect the 29 Init.* modules re-hashed in `target.rs` (`moduleIdentities`) on starnix
    let starnix_res_text = fs::read_to_string(
        "/tmp/anneal-mvp-starnix-installed-final/baseline-artifacts/result.json",
    )
    .unwrap();
    let starnix_res: Value = serde_json::from_str(&starnix_res_text).unwrap();
    let mod_ids = starnix_res["audit"]["moduleIdentities"].as_object().unwrap();
    let mut provenance_rehashed_files = Vec::new();
    for mod_name in mod_ids.keys() {
        if mod_name.starts_with("Init.") {
            let rel = mod_name.replace('.', "/");
            let src = prefix.join("src/lean").join(format!("{rel}.lean"));
            provenance_rehashed_files.push(src);
            for p in ["olean", "olean.server", "olean.private", "ir.sig", "ir"] {
                let art = prefix.join("lib/lean").join(format!("{rel}.{p}"));
                if art.exists() {
                    provenance_rehashed_files.push(art);
                }
            }
        }
    }
    let provenance_rehashed_bytes: u64 = provenance_rehashed_files
        .iter()
        .map(|p| fs::metadata(p).unwrap().len())
        .sum();

    // (i-a) Sequential `cargo_anneal::sha256_file` equivalent (with `sha2` SHA-NI)
    let seq_foundation = bench_fn(5, || {
        for f in &f_files {
            let meta = fs::symlink_metadata(&f.path).unwrap();
            assert!(meta.is_file() && !meta.file_type().is_symlink());
            let bytes = fs::read(&f.path).unwrap();
            let hex = hex_encode(&Sha256::digest(&bytes));
            assert_eq!(hex, f.expected_hex);
        }
    });

    let seq_library = bench_fn(5, || {
        for f in &l_files {
            let meta = fs::symlink_metadata(&f.path).unwrap();
            assert!(meta.is_file() && !meta.file_type().is_symlink());
            let bytes = fs::read(&f.path).unwrap();
            let hex = hex_encode(&Sha256::digest(&bytes));
            assert_eq!(hex, f.expected_hex);
        }
    });

    let seq_combined = bench_fn(5, || {
        for f in &all_files {
            let meta = fs::symlink_metadata(&f.path).unwrap();
            assert!(meta.is_file() && !meta.file_type().is_symlink());
            let bytes = fs::read(&f.path).unwrap();
            let hex = hex_encode(&Sha256::digest(&bytes));
            assert_eq!(hex, f.expected_hex);
        }
    });

    let seq_provenance_rehash = bench_fn(5, || {
        for p in &provenance_rehashed_files {
            let meta = fs::symlink_metadata(p).unwrap();
            assert!(meta.is_file() && !meta.file_type().is_symlink());
            let bytes = fs::read(p).unwrap();
            let hex = hex_encode(&Sha256::digest(&bytes));
            std::hint::black_box(hex);
        }
    });

    // (i-b) Pure software SHA-256 on combined 162.26 MB (1 run since software SHA-256 on 162MB is ~550ms)
    let seq_software_combined = bench_fn(3, || {
        for f in &all_files {
            let bytes = fs::read(&f.path).unwrap();
            let hex = hex_encode(&sha256_software(&bytes));
            assert_eq!(hex, f.expected_hex);
        }
    });

    // (ii) Only `.lean` + primary `.olean` (skipping `.olean.private`, `.olean.server`, `.ir`, `.ir.sig`)
    let olean_only_files: Vec<FileToHash> = all_files
        .iter()
        .filter(|f| {
            let s = f.path.to_string_lossy();
            s.ends_with(".lean") || s.ends_with(".olean")
        })
        .cloned()
        .collect();
    let olean_only_bytes: u64 = olean_only_files
        .iter()
        .map(|f| fs::metadata(&f.path).unwrap().len())
        .sum();
    let seq_olean_only = bench_fn(5, || {
        for f in &olean_only_files {
            let meta = fs::symlink_metadata(&f.path).unwrap();
            assert!(meta.is_file() && !meta.file_type().is_symlink());
            let bytes = fs::read(&f.path).unwrap();
            let hex = hex_encode(&Sha256::digest(&bytes));
            assert_eq!(hex, f.expected_hex);
        }
    });

    // (iii-a) Sequential with reusable preallocated buffer (eliminating 1,038 Vec mmap/munmap allocations)
    let seq_reusable_buf = bench_fn(5, || {
        let mut buf = Vec::with_capacity(16 * 1024 * 1024);
        for f in &all_files {
            let meta = fs::symlink_metadata(&f.path).unwrap();
            assert!(meta.is_file() && !meta.file_type().is_symlink());
            buf.clear();
            fs::File::open(&f.path).unwrap().read_to_end(&mut buf).unwrap();
            let hex = hex_encode(&Sha256::digest(&buf));
            assert_eq!(hex, f.expected_hex);
        }
    });

    // (iii-b) Multi-threaded parallel SHA-256 hashing across 2, 4, 8, 16 threads
    let mut parallel_results = serde_json::Map::new();
    for num_threads in [2usize, 4, 8, 16] {
        let t_res = bench_fn(5, || {
            let chunk_size = (all_files.len() + num_threads - 1) / num_threads;
            std::thread::scope(|s| {
                for chunk in all_files.chunks(chunk_size) {
                    s.spawn(move || {
                        let mut buf = Vec::with_capacity(16 * 1024 * 1024);
                        for f in chunk {
                            let meta = fs::symlink_metadata(&f.path).unwrap();
                            assert!(meta.is_file() && !meta.file_type().is_symlink());
                            buf.clear();
                            fs::File::open(&f.path).unwrap().read_to_end(&mut buf).unwrap();
                            let hex = hex_encode(&Sha256::digest(&buf));
                            assert_eq!(hex, f.expected_hex);
                        }
                    });
                }
            });
        });
        parallel_results.insert(format!("threads_{num_threads}"), t_res);
    }

    // (iv) Stat-keyed `(dev, ino, size, mtime_nsec, ctime_nsec)` admission cache
    let mut stat_cache: HashMap<PathBuf, (StatKey, String)> = HashMap::with_capacity(all_files.len());
    for f in &all_files {
        let meta = fs::symlink_metadata(&f.path).unwrap();
        stat_cache.insert(
            f.path.clone(),
            (StatKey::from_meta(&meta), f.expected_hex.clone()),
        );
    }
    let stat_cache_warm = bench_fn(20, || {
        for f in &all_files {
            let meta = fs::symlink_metadata(&f.path).unwrap();
            assert!(meta.is_file() && !meta.file_type().is_symlink());
            let key = StatKey::from_meta(&meta);
            let (cached_key, cached_sha) = stat_cache.get(&f.path).unwrap();
            assert_eq!(&key, cached_key);
            assert_eq!(cached_sha, &f.expected_hex);
        }
    });

    let out = json!({
        "exp3a_iv_rust_header_parser": header_bench,
        "exp3b_sha256_admission": {
            "counts": {
                "foundation_files": f_files.len(),
                "library_files": l_files.len(),
                "combined_files": all_files.len(),
                "olean_and_lean_only_files": olean_only_files.len(),
                "olean_and_lean_only_bytes": olean_only_bytes,
                "starnix_provenance_rehashed_files": provenance_rehashed_files.len(),
                "starnix_provenance_rehashed_bytes": provenance_rehashed_bytes,
            },
            "i_sequential_sha_ni_foundation": seq_foundation,
            "i_sequential_sha_ni_library": seq_library,
            "i_sequential_sha_ni_combined": seq_combined,
            "i_sequential_sha_ni_starnix_provenance_rehash": seq_provenance_rehash,
            "i_sequential_pure_software_combined": seq_software_combined,
            "ii_sequential_olean_and_lean_only": seq_olean_only,
            "iii_a_sequential_reusable_buffer": seq_reusable_buf,
            "iii_b_parallel_sha_ni": parallel_results,
            "iv_stat_keyed_cache_warm": stat_cache_warm,
        }
    });

    let out_path = track3.join("support/exp3a_iv_and_exp3b_results.json");
    fs::write(&out_path, serde_json::to_string_pretty(&out).unwrap()).unwrap();
    println!("{}", serde_json::to_string_pretty(&out).unwrap());
}
