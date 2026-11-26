// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Fail-closed admission of benign `.cargo/config{,.toml}` and
//! `$CARGO_HOME/config{,.toml}` files for Cargo-based shortcuts.
//!
//! Cargo shortcuts (`verify --manifest-path`, `shard-plan --manifest-path`)
//! build their own `rustc` invocation instead of running Cargo, so any Cargo
//! configuration that would change compilation (flags, wrappers, targets,
//! environment, patches, profiles, ...) cannot be honored and must be refused.
//! Two fail-closed policies share one deliberately small TOML subset parser:
//!
//! - [`CargoConfigPolicy::InWorkspace`] (`source_root..=workspace_root`) admits
//!   only [`ALLOWED_TABLES`]: command aliases, terminal output, `cargo doc`
//!   browser settings, `cargo new` templates, and future-incompatibility
//!   reporting.
//! - [`CargoConfigPolicy::AmbientHost`] (ancestors strictly above
//!   `workspace_root` and `$CARGO_HOME/config{,.toml}`) additionally admits
//!   `net`, `registries`, `registry`, and `source` (`[source.crates-io]`,
//!   `[source.vendored-sources]`, ...) needed by offline or vendored developer
//!   and CI Cargo homes while still rejecting `[build]`, `[target]`,
//!   `[profile]`, `[unstable]`, `[env]`, `[patch]`, `[http]`, `[install]`, and
//!   all other tables.
//!
//! Both policies check files against the same restricted TOML grammar:
//!
//! - blank lines and `#` comments;
//! - single-line `[table]` or `[table.sub.key]` headers with bare-key
//!   segments, whose top-level table is allowed by the active policy;
//! - `key = value` entries (bare or dotted bare keys) inside such a table,
//!   whose value is a single-line basic or literal string, a boolean, a
//!   decimal integer, or an array of those (which may span lines).
//!
//! Anything else, including multi-line strings, inline tables, arrays of
//! tables, quoted keys, top-level keys, duplicate tables or keys, and any line
//! this parser does not fully understand, is rejected. Rejecting a valid but
//! unusual file only sends the user to an explicit `--request`; admitting a
//! file whose meaning this parser misread could silently drop configuration
//! the user expects to apply.

use std::{
    collections::BTreeSet,
    fs,
    io::{self, Read as _},
    path::Path,
};

/// Lists the top-level Cargo configuration tables that never affect how
/// `rustc` compiles the crate inside `source_root..=workspace_root`: command
/// aliases, terminal output, `cargo doc` browser settings, `cargo new`
/// templates, and future-incompatibility reporting.
pub const ALLOWED_TABLES: &[&str] =
    &["alias", "term", "doc", "cargo-new", "future-incompat-report"];

/// Lists the top-level Cargo configuration tables admitted in ambient host
/// configuration (ancestors strictly above `workspace_root` and `$CARGO_HOME`):
/// [`ALLOWED_TABLES`] plus `net`, `registries`, `registry`, and `source` for
/// offline or vendored host setups (dependency-free shortcut crates never
/// resolve external crates or sources during `rustc` capture).
pub const ALLOWED_AMBIENT_HOST_TABLES: &[&str] = &[
    "alias",
    "term",
    "doc",
    "cargo-new",
    "future-incompat-report",
    "net",
    "registries",
    "registry",
    "source",
];

/// Selects which non-compilation Cargo configuration tables are admitted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CargoConfigPolicy {
    /// Package and workspace directories (`source_root..=workspace_root`).
    InWorkspace,
    /// Ancestor directories strictly above `workspace_root` and `$CARGO_HOME`.
    AmbientHost,
}

impl CargoConfigPolicy {
    /// Return the top-level Cargo tables admitted under this policy.
    pub const fn allowed_tables(self) -> &'static [&'static str] {
        match self {
            Self::InWorkspace => ALLOWED_TABLES,
            Self::AmbientHost => ALLOWED_AMBIENT_HOST_TABLES,
        }
    }
}

/// Bounds the size of an admitted config file.
pub const MAX_CONFIG_BYTES: u64 = 64 * 1024;

/// Check the Cargo configuration file at `path` under `policy`.
///
/// Returns `Ok(())` only for a regular, non-symlink, UTF-8 file of at most
/// [`MAX_CONFIG_BYTES`] that lies entirely within `policy`'s admitted subset.
/// Otherwise returns a short reason suitable for a failure detail.
pub fn check_config_file(path: &Path, policy: CargoConfigPolicy) -> Result<(), String> {
    let meta = fs::symlink_metadata(path).map_err(|e| format!("cannot inspect: {e}"))?;
    if meta.file_type().is_symlink() {
        return Err("symlink".to_owned());
    }
    if !meta.is_file() {
        return Err("not a regular file".to_owned());
    }
    if meta.len() > MAX_CONFIG_BYTES {
        return Err(format!("larger than {MAX_CONFIG_BYTES} bytes"));
    }
    let bytes = read_bounded_no_follow(path).map_err(|e| format!("cannot read: {e}"))?;
    if bytes.len() as u64 > MAX_CONFIG_BYTES {
        return Err(format!("larger than {MAX_CONFIG_BYTES} bytes"));
    }
    let text = std::str::from_utf8(&bytes).map_err(|_| "not UTF-8".to_owned())?;
    check_config_text(text, policy)
}

/// Read at most `MAX_CONFIG_BYTES + 1` bytes, refusing to follow a symlink
/// planted after the metadata check and rejecting a non-regular open handle.
fn read_bounded_no_follow(path: &Path) -> io::Result<Vec<u8>> {
    let mut opts = fs::OpenOptions::new();
    opts.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        opts.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
    }
    let file = opts.open(path)?;
    if !file.metadata()?.is_file() {
        return Err(io::Error::other("not a regular file"));
    }
    let mut bytes = Vec::new();
    file.take(MAX_CONFIG_BYTES + 1).read_to_end(&mut bytes)?;
    Ok(bytes)
}

/// Check Cargo configuration `text` against the subset admitted by `policy`.
pub fn check_config_text(text: &str, policy: CargoConfigPolicy) -> Result<(), String> {
    let allowed_tables = policy.allowed_tables();
    if text.starts_with('\u{feff}') {
        return Err("byte-order mark".to_owned());
    }
    let mut lines = text.split('\n').enumerate().peekable();
    let mut section: Option<String> = None;
    let mut tables = BTreeSet::new();
    let mut keys = BTreeSet::new();
    while let Some((index, raw)) = lines.next() {
        let line_no = index + 1;
        let line = raw.strip_suffix('\r').unwrap_or(raw);
        let at = |reason: &str| format!("line {line_no}: {reason}");
        if line.chars().any(|c| c.is_control() && c != '\t') {
            return Err(at("control character"));
        }
        let trimmed = line.trim_matches([' ', '\t']);
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        if let Some(rest) = trimmed.strip_prefix('[') {
            if rest.starts_with('[') {
                return Err(at("array of tables"));
            }
            // Name a forbidden bare top-level table (such as `target` in
            // `[target.'cfg(..)']`) before judging the rest of the header.
            let first = rest.split(['.', ']']).next().unwrap_or("").trim_matches([' ', '\t']);
            if parse_key_path(first).is_some() && !allowed_tables.contains(&first) {
                return Err(format!("table [{first}]"));
            }
            let (header, after) = rest.split_once(']').ok_or_else(|| at("malformed header"))?;
            expect_line_end(after).map_err(|r| at(&r))?;
            let segments = parse_key_path(header).ok_or_else(|| at("malformed header"))?;
            if !allowed_tables.contains(&segments[0]) {
                return Err(format!("table [{}]", segments[0]));
            }
            let name = segments.join(".");
            if !tables.insert(name.clone()) {
                return Err(at(&format!("duplicate table [{name}]")));
            }
            section = Some(name);
            continue;
        }
        let (key, value) = trimmed.split_once('=').ok_or_else(|| at("unrecognized line"))?;
        let segments = parse_key_path(key).ok_or_else(|| at("unsupported key"))?;
        let Some(current) = &section else {
            return Err(format!("top-level key {}", segments.join(".")));
        };
        let full = format!("{current}.{}", segments.join("."));
        if !keys.insert(full.clone()) {
            return Err(at(&format!("duplicate key {full}")));
        }
        let value = value.trim_start_matches([' ', '\t']);
        if let Some(mut rest) = value.strip_prefix('[') {
            // Arrays may span lines; each continuation line holds more
            // elements, separators, comments, or the closing bracket.
            // Errors name the line being scanned, while an unterminated
            // array names the line that opened it.
            let mut expect_element = true;
            let mut cur_no = line_no;
            let at_cur = |cur_no: usize, reason: &str| format!("line {cur_no}: {reason}");
            loop {
                match scan_array(rest, &mut expect_element).map_err(|r| at_cur(cur_no, &r))? {
                    ArrayScan::Closed(after) => {
                        expect_line_end(after).map_err(|r| at_cur(cur_no, &r))?;
                        break;
                    }
                    ArrayScan::Open => {
                        let Some((next_index, next)) = lines.next() else {
                            return Err(at("unterminated array"));
                        };
                        cur_no = next_index + 1;
                        let next = next.strip_suffix('\r').unwrap_or(next);
                        if next.chars().any(|c| c.is_control() && c != '\t') {
                            return Err(at_cur(cur_no, "control character in array"));
                        }
                        rest = next;
                    }
                }
            }
        } else {
            let after = scan_scalar(value).map_err(|r| at(&r))?;
            expect_line_end(after).map_err(|r| at(&r))?;
        }
    }
    Ok(())
}

/// Parse a dotted path of bare keys (`a.b-c.d_e`), allowing spaces or tabs
/// around each segment, and return its segments.
fn parse_key_path(raw: &str) -> Option<Vec<&str>> {
    let segments: Vec<&str> = raw.split('.').map(|s| s.trim_matches([' ', '\t'])).collect();
    let bare = |s: &&str| {
        !s.is_empty() && s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-')
    };
    segments.iter().all(bare).then_some(segments)
}

/// Accept only trailing whitespace or a `#` comment.
fn expect_line_end(rest: &str) -> Result<(), String> {
    let rest = rest.trim_start_matches([' ', '\t']);
    if rest.is_empty() || rest.starts_with('#') {
        Ok(())
    } else {
        Err("unexpected trailing text".to_owned())
    }
}

/// Scan one scalar value at the start of `s` and return the remaining text.
fn scan_scalar(s: &str) -> Result<&str, String> {
    if s.starts_with("\"\"\"") || s.starts_with("'''") {
        return Err("multi-line string".to_owned());
    }
    if let Some(rest) = s.strip_prefix('"') {
        return scan_basic_string(rest);
    }
    if let Some(rest) = s.strip_prefix('\'') {
        let end = rest.find('\'').ok_or_else(|| "unterminated literal string".to_owned())?;
        return Ok(&rest[end + 1..]);
    }
    if s.starts_with('{') {
        return Err("inline table".to_owned());
    }
    let end = s.find([' ', '\t', ',', ']', '#']).unwrap_or(s.len());
    let (token, rest) = s.split_at(end);
    if matches!(token, "true" | "false") || is_decimal_integer(token) {
        Ok(rest)
    } else {
        Err("unsupported value".to_owned())
    }
}

/// Scan the remainder of a single-line basic string after its opening quote.
fn scan_basic_string(s: &str) -> Result<&str, String> {
    let mut chars = s.char_indices();
    while let Some((i, c)) = chars.next() {
        match c {
            '"' => return Ok(&s[i + 1..]),
            '\\' => {
                let digits = match chars.next() {
                    Some((_, 'b' | 't' | 'n' | 'f' | 'r' | 'e' | '"' | '\\')) => 0,
                    Some((_, 'x')) => 2,
                    Some((_, 'u')) => 4,
                    Some((_, 'U')) => 8,
                    _ => return Err("invalid string escape".to_owned()),
                };
                for _ in 0..digits {
                    match chars.next() {
                        Some((_, h)) if h.is_ascii_hexdigit() => {}
                        _ => return Err("invalid string escape".to_owned()),
                    }
                }
            }
            _ => {}
        }
    }
    Err("unterminated string".to_owned())
}

/// Return whether `token` is a TOML decimal integer (`0`, `-12`, `1_000`).
fn is_decimal_integer(token: &str) -> bool {
    let digits = token.strip_prefix(['+', '-']).unwrap_or(token);
    let bytes = digits.as_bytes();
    !bytes.is_empty()
        && bytes.iter().all(|b| b.is_ascii_digit() || *b == b'_')
        && bytes[0].is_ascii_digit()
        && bytes[bytes.len() - 1].is_ascii_digit()
        && !digits.contains("__")
        && (bytes[0] != b'0' || bytes.len() == 1)
}

enum ArrayScan<'a> {
    Closed(&'a str),
    Open,
}

/// Scan array content on one line, tracking whether an element or a
/// separator comes next across continuation lines.
fn scan_array<'a>(mut s: &'a str, expect_element: &mut bool) -> Result<ArrayScan<'a>, String> {
    loop {
        s = s.trim_start_matches([' ', '\t']);
        if s.is_empty() || s.starts_with('#') {
            return Ok(ArrayScan::Open);
        }
        if let Some(rest) = s.strip_prefix(']') {
            return Ok(ArrayScan::Closed(rest));
        }
        if *expect_element {
            if s.starts_with('[') {
                return Err("nested array".to_owned());
            }
            s = scan_scalar(s)?;
            *expect_element = false;
        } else if let Some(rest) = s.strip_prefix(',') {
            s = rest;
            *expect_element = true;
        } else {
            return Err("malformed array".to_owned());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(test)]
    fn check_benign_config_text(text: &str) -> Result<(), String> {
        check_config_text(text, CargoConfigPolicy::InWorkspace)
    }

    #[cfg(test)]
    fn check_benign_config_file(path: &Path) -> Result<(), String> {
        check_config_file(path, CargoConfigPolicy::InWorkspace)
    }

    #[test]
    fn admits_non_compilation_tables() {
        for text in [
            "",
            "\n# only a comment\n\n",
            "[alias]\nnightly_docs = \"doc --no-deps -Zunstable-options\"\n",
            "[alias]\nb = \"build\"\nxtask = [\"run\", \"--package\", 'xtask', \"--\"]\n",
            "[alias]\nmulti = [\n  \"run\", # comment\n  \"--release\",\n]\n",
            "[term]\nverbose = false\ncolor = 'auto'\nprogress.when = \"never\"\n",
            "[term.progress]\nwidth = 80\n",
            "[doc]\nbrowser = [\"firefox\", \"--new-tab\"] # trailing\n",
            "[cargo-new]\nvcs = \"none\"\n",
            "[future-incompat-report]\nfrequency = \"never\"\n",
            "\r\n[ alias ]\r\nt = \"test \\\"q\\\" \\u00e9\"\r\n",
            "[alias]\nempty = []\nn = -1_000\n",
        ] {
            assert_eq!(check_benign_config_text(text), Ok(()), "{text:?}");
        }
    }

    #[test]
    fn rejects_compilation_tables_and_ambiguous_syntax() {
        for (text, reason) in [
            ("[build]\nrustflags = [\"--cfg\", \"x\"]\n", "table [build]"),
            ("[target.'cfg(all())']\nrustflags = []\n", "table [target]"),
            ("[target.x86_64-unknown-linux-gnu]\nlinker = \"cc\"\n", "table [target]"),
            ("[env]\nFOO = \"1\"\n", "table [env]"),
            ("[profile.dev]\nopt-level = 3\n", "table [profile]"),
            ("[patch.crates-io]\nfoo = { path = \"x\" }\n", "table [patch]"),
            ("[source.crates-io]\nreplace-with = \"v\"\n", "table [source]"),
            ("[registries.x]\nindex = \"y\"\n", "table [registries]"),
            ("[registry]\ndefault = \"x\"\n", "table [registry]"),
            ("[unstable]\nbuild-std = [\"core\"]\n", "table [unstable]"),
            ("[net]\noffline = true\n", "table [net]"),
            ("[http]\nproxy = \"x\"\n", "table [http]"),
            ("[install]\nroot = \"x\"\n", "table [install]"),
            ("[resolver]\nincompatible-rust-versions = \"allow\"\n", "table [resolver]"),
            ("paths = [\"x\"]\n", "top-level key paths"),
            ("build.rustc-wrapper = \"evil\"\n", "top-level key build.rustc-wrapper"),
            ("include = \"other.toml\"\n[alias]\n", "top-level key include"),
            ("[\"build\"]\nrustflags = []\n", "malformed header"),
            ("[alias.\"x\"]\n", "malformed header"),
            ("[[alias]]\n", "array of tables"),
            ("[alias]\n\"b\" = \"build\"\n", "unsupported key"),
            ("[alias]\nb = \"\"\"\nbuild\"\"\"\n", "multi-line string"),
            ("[alias]\nb = '''build'''\n", "multi-line string"),
            ("[alias]\nb = { x = 1 }\n", "inline table"),
            ("[alias]\nb = [[\"x\"]]\n", "nested array"),
            ("[alias]\nb = [\"x\"\n", "unterminated array"),
            ("[alias]\nb = [\"x\" \"y\"]\n", "malformed array"),
            ("[alias]\nb = \"build\n", "unterminated string"),
            ("[alias]\nb = \"\\q\"\n", "invalid string escape"),
            ("[alias]\nb = build\n", "unsupported value"),
            ("[alias]\nb = 1.5\n", "unsupported value"),
            ("[alias]\nb = 0x10\n", "unsupported value"),
            ("[alias]\nb = \"x\" y\n", "unexpected trailing text"),
            ("[alias] x\n", "unexpected trailing text"),
            ("[alias\n", "malformed header"),
            ("[alias]\nb\n", "unrecognized line"),
            ("[alias]\nb = \"x\"\nb = \"y\"\n", "duplicate key alias.b"),
            ("[alias]\n[alias]\n", "duplicate table [alias]"),
            ("[alias]\nb = \"x\u{1b}\"\n", "control character"),
            ("\u{feff}[alias]\n", "byte-order mark"),
            ("[alias]\n[build]\n", "table [build]"),
        ] {
            let err = check_benign_config_text(text).expect_err(text);
            assert!(err.contains(reason), "{text:?}: {err}");
        }
    }

    #[test]
    fn array_errors_name_the_offending_line() {
        let err = |text: &str| check_benign_config_text(text).unwrap_err();
        assert_eq!(err("[alias]\nb = [\n  \"x\",\n  { y = 1 },\n]\n"), "line 4: inline table");
        assert_eq!(err("[alias]\nb = [\n  \"x\"\n  \"y\"\n]\n"), "line 4: malformed array");
        assert_eq!(err("[alias]\nb = [\n  \"x\u{7}\",\n]\n"), "line 3: control character in array");
        assert_eq!(err("[alias]\nb = [\n  \"x\",\n] y\n"), "line 4: unexpected trailing text");
        assert_eq!(err("[alias]\nb = [\n  \"x\",\n"), "line 2: unterminated array");
    }

    #[test]
    fn file_check_rejects_symlinks_special_and_oversized_files() {
        let dir = tempfile::tempdir().unwrap();
        let ok = dir.path().join("config.toml");
        fs::write(&ok, "[alias]\nb = \"build\"\n").unwrap();
        assert_eq!(check_benign_config_file(&ok), Ok(()));

        let big = dir.path().join("big.toml");
        let mut text = "[alias]\n".to_owned();
        while text.len() as u64 <= MAX_CONFIG_BYTES {
            text.push_str("# padding padding padding padding padding\n");
        }
        fs::write(&big, text).unwrap();
        assert!(check_benign_config_file(&big).unwrap_err().contains("larger than"));

        let bad_utf8 = dir.path().join("bad.toml");
        fs::write(&bad_utf8, b"[alias]\n# \xff\n").unwrap();
        assert_eq!(check_benign_config_file(&bad_utf8).unwrap_err(), "not UTF-8");

        let subdir = dir.path().join("sub");
        fs::create_dir(&subdir).unwrap();
        assert_eq!(check_benign_config_file(&subdir).unwrap_err(), "not a regular file");

        #[cfg(unix)]
        {
            let link = dir.path().join("link.toml");
            std::os::unix::fs::symlink(&ok, &link).unwrap();
            assert_eq!(check_benign_config_file(&link).unwrap_err(), "symlink");
            assert_eq!(
                check_config_file(&link, CargoConfigPolicy::AmbientHost).unwrap_err(),
                "symlink"
            );
        }
    }

    #[test]
    fn ambient_host_policy_admits_net_registries_and_source_while_rejecting_overrides() {
        for text in [
            "",
            "# offline/vendored developer Cargo home\n",
            "[net]\noffline = true\ngit-fetch-with-cli = true\nretry = 3\n",
            "[registries.corp]\nindex = \"sparse+https://corp.invalid/index/\"\n",
            "[registry]\ndefault = \"corp\"\nglobal-credential-providers = [\"cargo:token\"]\n",
            "[source.crates-io]\nreplace-with = \"vendored-sources\"\n\
             [source.vendored-sources]\ndirectory = '/opt/vendor'\n",
            "[alias]\nb = \"build\"\n[term]\ncolor = \"auto\"\n[net]\nretry = 1\n",
        ] {
            assert_eq!(check_config_text(text, CargoConfigPolicy::AmbientHost), Ok(()), "{text:?}");
        }

        // `InWorkspace` still rejects `[net]`, `[registries]`, `[registry]`,
        // and `[source]`.
        for (text, reason) in [
            ("[net]\noffline = true\n", "table [net]"),
            ("[registries.corp]\nindex = \"sparse+https://x/\"\n", "table [registries]"),
            ("[registry]\ndefault = \"x\"\n", "table [registry]"),
            ("[source.crates-io]\nreplace-with = \"v\"\n", "table [source]"),
        ] {
            assert_eq!(
                check_config_text(text, CargoConfigPolicy::InWorkspace).unwrap_err(),
                reason
            );
        }

        // `AmbientHost` still fails closed on compilation tables, `[http]`,
        // top-level keys, inline tables, multi-line strings, arrays of tables,
        // and malformed TOML (including non-ASCII UTF-8 boundaries).
        for (text, reason) in [
            ("[build]\nrustc = \"/tmp/rustc\"\n", "table [build]"),
            ("[build]\nrustc-wrapper = \"sccache\"\n", "table [build]"),
            ("[build]\njobs = 8\n", "table [build]"),
            ("[target.'cfg(all())']\nrustflags = []\n", "table [target]"),
            ("[target.x86_64-unknown-linux-gnu]\nlinker = \"clang\"\n", "table [target]"),
            ("[profile.dev]\noverflow-checks = true\n", "table [profile]"),
            ("[unstable]\nbuild-std = [\"core\"]\n", "table [unstable]"),
            ("[env]\nRUSTFLAGS = \"--cfg=x\"\n", "table [env]"),
            ("[patch.crates-io]\nfoo = { path = \"x\" }\n", "table [patch]"),
            ("[http]\nproxy = \"x\"\n", "table [http]"),
            ("[install]\nroot = \"x\"\n", "table [install]"),
            ("[resolver]\nincompatible-rust-versions = \"allow\"\n", "table [resolver]"),
            ("build.rustc-wrapper = \"wrap\"\n", "top-level key build.rustc-wrapper"),
            (
                "env.CARGO_ENCODED_RUSTFLAGS = \"--cfg=x\"\n",
                "top-level key env.CARGO_ENCODED_RUSTFLAGS",
            ),
            ("[[registries.extra.items]]\nname = \"a\"\n", "array of tables"),
            ("[source.vendored]\ndirectory = \"\"\"\n/opt/vendor\n\"\"\"\n", "multi-line string"),
            ("[net]\nextra = { retry = 1 }\n", "inline table"),
            ("[net]\nx = \"\\u000é\"\n", "invalid string escape"),
            ("[net]\nx = \"\\U0000000é\"\n", "invalid string escape"),
            ("[net]\nx = 123456789é00\n", "unsupported value"),
        ] {
            let err = check_config_text(text, CargoConfigPolicy::AmbientHost).expect_err(text);
            assert!(err.contains(reason), "{text:?}: {err}");
        }
    }
}
