// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Source scan proving that the pure `core` modules perform no OS I/O.

use super::*;

fn skip_comment_or_string(bytes: &[u8], i: usize) -> Option<usize> {
    let b = bytes[i];
    if b == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'/' {
        let mut j = i + 2;
        while j < bytes.len() && bytes[j] != b'\n' {
            j += 1;
        }
        return Some(j);
    }
    if b == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'*' {
        let mut j = i + 2;
        let mut depth = 1usize;
        while j < bytes.len() && depth > 0 {
            if bytes[j] == b'/' && j + 1 < bytes.len() && bytes[j + 1] == b'*' {
                depth += 1;
                j += 2;
            } else if bytes[j] == b'*' && j + 1 < bytes.len() && bytes[j + 1] == b'/' {
                depth -= 1;
                j += 2;
            } else {
                j += 1;
            }
        }
        return Some(j);
    }
    if (b == b'r' || (b == b'b' && i + 1 < bytes.len() && bytes[i + 1] == b'r'))
        && i + 1 < bytes.len()
    {
        let mut j = if b == b'b' { i + 2 } else { i + 1 };
        let mut hashes = 0usize;
        while j < bytes.len() && bytes[j] == b'#' {
            hashes += 1;
            j += 1;
        }
        if j < bytes.len() && bytes[j] == b'"' {
            j += 1;
            while j < bytes.len() {
                if bytes[j] == b'"'
                    && j + 1 + hashes <= bytes.len()
                    && bytes[j + 1..j + 1 + hashes].iter().all(|&c| c == b'#')
                {
                    j += 1 + hashes;
                    break;
                }
                j += 1;
            }
            return Some(j);
        }
    }
    if b == b'"' {
        let mut j = i + 1;
        while j < bytes.len() {
            if bytes[j] == b'\\' {
                j += 2;
            } else if bytes[j] == b'"' {
                j += 1;
                break;
            } else {
                j += 1;
            }
        }
        return Some(j);
    }
    if b == b'\'' {
        if i + 2 < bytes.len() && bytes[i + 1] == b'\\' {
            if let Some(end) = bytes[i + 2..].iter().position(|&c| c == b'\'') {
                return Some(i + 2 + end + 1);
            }
        } else if i + 2 < bytes.len() && bytes[i + 2] == b'\'' {
            return Some(i + 3);
        }
    }
    None
}

fn strip_cfg_test_blocks(source: &str) -> String {
    let bytes = source.as_bytes();
    let mut out = String::with_capacity(source.len());
    let mut i = 0usize;
    let mut chunk_start = 0usize;
    const NEEDLE: &[u8] = b"#[cfg(test)]";
    while i < bytes.len() {
        if let Some(next) = skip_comment_or_string(bytes, i) {
            i = next;
            continue;
        }
        if bytes[i..].starts_with(NEEDLE) {
            out.push_str(&source[chunk_start..i]);
            let mut j = i + NEEDLE.len();
            // Advance past the annotated item: stop at `;` if this is a
            // semicolon-terminated item (`#[cfg(test)] mod tests;`), or strip
            // the balanced `{ ... }` block outside comments and strings.
            let mut brace_depth = 0usize;
            while j < bytes.len() {
                if let Some(next) = skip_comment_or_string(bytes, j) {
                    j = next;
                    continue;
                }
                match bytes[j] {
                    b';' if brace_depth == 0 => {
                        j += 1;
                        break;
                    }
                    b'{' => {
                        brace_depth += 1;
                        j += 1;
                    }
                    b'}' if brace_depth > 0 => {
                        brace_depth -= 1;
                        j += 1;
                        if brace_depth == 0 {
                            break;
                        }
                    }
                    _ => j += 1,
                }
            }
            i = j;
            chunk_start = i;
            continue;
        }
        i += 1;
    }
    out.push_str(&source[chunk_start..]);
    out
}

fn collect_rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.is_dir() {
            collect_rs_files(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            out.push(path);
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum RustTok<'a> {
    Ident(&'a str),
    ColonColon,
    LBrace,
    RBrace,
    Comma,
    Semi,
    Other,
}

fn tokenize_rust(src: &str) -> Vec<RustTok<'_>> {
    let bytes = src.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        if b.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        // Line comment.
        if b == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'/' {
            i += 2;
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        // Block comment (supports nesting).
        if b == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'*' {
            i += 2;
            let mut depth = 1usize;
            while i < bytes.len() && depth > 0 {
                if bytes[i] == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'*' {
                    depth += 1;
                    i += 2;
                } else if bytes[i] == b'*' && i + 1 < bytes.len() && bytes[i + 1] == b'/' {
                    depth -= 1;
                    i += 2;
                } else {
                    i += 1;
                }
            }
            continue;
        }
        // Raw string literal: r#"..."# or br#"..."#.
        if (b == b'r' || (b == b'b' && i + 1 < bytes.len() && bytes[i + 1] == b'r'))
            && i + 1 < bytes.len()
        {
            let mut j = if b == b'b' { i + 2 } else { i + 1 };
            let mut hashes = 0usize;
            while j < bytes.len() && bytes[j] == b'#' {
                hashes += 1;
                j += 1;
            }
            if j < bytes.len() && bytes[j] == b'"' {
                j += 1;
                while j < bytes.len() {
                    if bytes[j] == b'"'
                        && j + 1 + hashes <= bytes.len()
                        && bytes[j + 1..j + 1 + hashes].iter().all(|&c| c == b'#')
                    {
                        j += 1 + hashes;
                        break;
                    }
                    j += 1;
                }
                i = j;
                out.push(RustTok::Other);
                continue;
            }
        }
        // Normal string literal.
        if b == b'"' {
            i += 1;
            while i < bytes.len() {
                if bytes[i] == b'\\' {
                    i += 2;
                } else if bytes[i] == b'"' {
                    i += 1;
                    break;
                } else {
                    i += 1;
                }
            }
            out.push(RustTok::Other);
            continue;
        }
        // Char literal (avoid confusing `'"'` with a string start).
        if b == b'\'' {
            if i + 2 < bytes.len() && bytes[i + 1] == b'\\' {
                if let Some(end) = bytes[i + 2..].iter().position(|&c| c == b'\'') {
                    i = i + 2 + end + 1;
                    out.push(RustTok::Other);
                    continue;
                }
            } else if i + 2 < bytes.len() && bytes[i + 2] == b'\'' {
                i += 3;
                out.push(RustTok::Other);
                continue;
            }
            i += 1;
            out.push(RustTok::Other);
            continue;
        }
        if b == b':' && i + 1 < bytes.len() && bytes[i + 1] == b':' {
            out.push(RustTok::ColonColon);
            i += 2;
            continue;
        }
        if b == b'{' {
            out.push(RustTok::LBrace);
            i += 1;
            continue;
        }
        if b == b'}' {
            out.push(RustTok::RBrace);
            i += 1;
            continue;
        }
        if b == b',' {
            out.push(RustTok::Comma);
            i += 1;
            continue;
        }
        if b == b';' {
            out.push(RustTok::Semi);
            i += 1;
            continue;
        }
        if b.is_ascii_alphabetic() || b == b'_' {
            let start = i;
            i += 1;
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
            out.push(RustTok::Ident(&src[start..i]));
            continue;
        }
        out.push(RustTok::Other);
        i += 1;
    }
    out
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum PathRootKind {
    Std,
    StdIo,
    CrateOrSuper,
}

fn check_path_after_colon_colon(
    toks: &[RustTok<'_>],
    idx: usize,
    kind: PathRootKind,
    forbidden_shell_mods: &[&str],
    file_label: &str,
) -> Result<(), String> {
    const FORBIDDEN_STD_MODS: &[&str] = &["fs", "process", "net", "env", "os", "time"];
    const FORBIDDEN_STD_IO: &[&str] = &["stdin", "stdout", "stderr", "Read", "Write"];

    match toks.get(idx) {
        Some(RustTok::Ident(name)) => {
            match kind {
                PathRootKind::CrateOrSuper => {
                    if *name == "super" && matches!(toks.get(idx + 1), Some(RustTok::ColonColon)) {
                        return check_path_after_colon_colon(
                            toks,
                            idx + 2,
                            PathRootKind::CrateOrSuper,
                            forbidden_shell_mods,
                            file_label,
                        );
                    }
                    if forbidden_shell_mods.contains(name) {
                        return Err(format!(
                            "forbidden shell module `{name}` reference in {file_label}"
                        ));
                    }
                }
                PathRootKind::Std => {
                    if FORBIDDEN_STD_MODS.contains(name) {
                        return Err(format!("forbidden `std::{name}` reference in {file_label}"));
                    }
                    if *name == "io" && matches!(toks.get(idx + 1), Some(RustTok::ColonColon)) {
                        return check_path_after_colon_colon(
                            toks,
                            idx + 2,
                            PathRootKind::StdIo,
                            forbidden_shell_mods,
                            file_label,
                        );
                    }
                }
                PathRootKind::StdIo => {
                    if FORBIDDEN_STD_IO.contains(name) {
                        return Err(format!(
                            "forbidden `std::io::{name}` reference in {file_label}"
                        ));
                    }
                }
            }
            Ok(())
        }
        Some(RustTok::LBrace) => {
            let mut depth = 1usize;
            let mut j = idx + 1;
            let mut at_item_start = true;
            while j < toks.len() && depth > 0 {
                if depth == 1 && at_item_start {
                    check_path_after_colon_colon(toks, j, kind, forbidden_shell_mods, file_label)?;
                    at_item_start = false;
                }
                match toks[j] {
                    RustTok::LBrace => depth += 1,
                    RustTok::RBrace => depth -= 1,
                    RustTok::Comma if depth == 1 => at_item_start = true,
                    _ => {}
                }
                j += 1;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

fn check_pure_core_source(
    prod: &str,
    file_label: &str,
    extra_shell_mods: &[&str],
) -> Result<(), String> {
    let forbidden_tokens = [
        "std::fs",
        "std::process",
        "std::net",
        "std::env",
        "std::os::",
        "std::time::",
        "std::io::stdin",
        "std::io::stdout",
        "std::io::stderr",
        "std::io::Read",
        "std::io::Write",
        "libc::",
        "exocrate::",
        "clap::",
        "tempfile::",
        "walkdir::",
        "unsafe ",
        "unsafe{",
    ];
    let mut forbidden_shell_mods: Vec<&str> = vec![
        "bundle",
        "cli",
        "diagnostics",
        "init",
        "inspect",
        "olean_cache",
        "sandbox",
        "setup",
        "stage",
        "sys_util",
        "target",
        "toolchain",
        "trusted_bundle",
        "verify",
    ];
    for m in extra_shell_mods {
        if !forbidden_shell_mods.contains(m) {
            forbidden_shell_mods.push(m);
        }
    }
    for tok in forbidden_tokens {
        if prod.contains(tok) {
            return Err(format!(
                "pure core module {file_label} must not reference forbidden token `{tok}`"
            ));
        }
    }
    let toks = tokenize_rust(prod);
    for i in 0..toks.len() {
        let root_kind = match (&toks[i], toks.get(i + 1)) {
            (RustTok::Ident("std"), Some(RustTok::ColonColon)) => Some(PathRootKind::Std),
            (RustTok::Ident("crate" | "super"), Some(RustTok::ColonColon)) => {
                Some(PathRootKind::CrateOrSuper)
            }
            _ => None,
        };
        if let Some(kind) = root_kind {
            check_path_after_colon_colon(&toks, i + 2, kind, &forbidden_shell_mods, file_label)?;
        }
    }
    Ok(())
}

#[test]
fn enforce_pure_core_has_no_os_io() {
    let src_dir = anneal_root().join("trusted/cargo-anneal/src");
    let core_dir = src_dir.join("core");
    let core_mod = fs::read_to_string(core_dir.join("mod.rs")).unwrap();
    assert!(core_mod.contains("#![forbid(unsafe_code)]"));
    let inspect_mod = fs::read_to_string(core_dir.join("inspect/mod.rs")).unwrap();
    assert!(inspect_mod.contains("#![forbid(unsafe_code)]"));

    // Dynamically collect every non-`core` module declared in `lib.rs` so new
    // shell modules cannot drift out of the guard.
    let lib_rs = fs::read_to_string(src_dir.join("lib.rs")).unwrap();
    let lib_toks = tokenize_rust(&lib_rs);
    let mut declared_shell_mods = Vec::new();
    for i in 0..lib_toks.len() {
        if let (RustTok::Ident("mod"), Some(RustTok::Ident(name)), Some(RustTok::Semi)) =
            (&lib_toks[i], lib_toks.get(i + 1), lib_toks.get(i + 2))
            && *name != "core"
        {
            declared_shell_mods.push(*name);
        }
    }
    assert!(
        declared_shell_mods.contains(&"cli") && declared_shell_mods.contains(&"trusted_bundle"),
        "expected declared shell modules from lib.rs, got {declared_shell_mods:?}"
    );

    let mut files = Vec::new();
    collect_rs_files(&core_dir, &mut files);
    assert!(!files.is_empty());

    for file in files {
        let raw = fs::read_to_string(&file).unwrap();
        let prod = strip_cfg_test_blocks(&raw);
        let label = file.display().to_string();
        if let Err(err) = check_pure_core_source(&prod, &label, &declared_shell_mods) {
            panic!("{err}");
        }
    }

    // Guard self-tests: confirm grouped, aliased, nested, inline, comment,
    // external-module, and `walkdir::` bypasses are rejected while clean
    // pure-core imports pass.
    for bypass in [
        "use crate::{inspect, core};",
        "use crate::{inspect as shell_inspect};",
        "use super::sys_util::SafeFs;",
        "fn f() { let _ = crate::sys_util::SafeFs::open(); }",
        "use super::{super::{sandbox::run}};",
        "use std::{fs as f};",
        "use std::{io::{self, Read}};",
        "use crate::cli::Args;",
        "use crate::diagnostics::hint_for_failure;",
        "use crate::init::run;",
        "use crate::trusted_bundle::BUNDLE;",
        "fn f() { let _ = walkdir::WalkDir::new(\".\"); }",
        "// Mentioning #[cfg(test)] in a comment must not hide code.\n\
         fn f() { let _ = crate::init::run(); }",
        "#[cfg(test)] mod tests;\n\
         fn f() { let _ = crate::init::run(); }",
    ] {
        let stripped = strip_cfg_test_blocks(bypass);
        assert!(
            check_pure_core_source(&stripped, "probe.rs", &declared_shell_mods).is_err(),
            "pure-core guard failed to reject `{bypass}`"
        );
    }
    assert!(
        check_pure_core_source(
            &strip_cfg_test_blocks(
                "use crate::core::inspect::schema::SuccessReceipt;\n\
                 use std::{collections::BTreeMap, fmt};\n\
                 #[cfg(test)]\n\
                 mod tests { use crate::init::run; }\n",
            ),
            "clean.rs",
            &declared_shell_mods,
        )
        .is_ok()
    );
}
