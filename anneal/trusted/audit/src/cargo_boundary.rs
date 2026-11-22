// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Enforces repository Cargo workspace containment, `Cargo.lock` provenance,
//! and `trusted/root-manifest.sha256` verification ([`check_cargo_boundary`]).
//! A separate check, [`verify_bundled_resources`], verifies embedded
//! `bundled_resources.rs` canonical-source parity.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    ffi::{OsStr, OsString},
    fs, io,
    path::{Component, Path, PathBuf},
    process::Command,
};

use cargo_anneal::{
    Failure,
    bundle::{
        BundleError, render_bundled_resources, render_bundled_theory, validate_bundle_destination,
        validate_theory_bundle_destination,
    },
    is_clean_relative_path, is_sha256_hex, sha256_file,
};
use serde::Deserialize;
use walkdir::WalkDir;

use crate::miri_pin::verify_upstream_pin;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RootCargoManifest {
    workspace: RootCargoWorkspace,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RootCargoWorkspace {
    members: Vec<String>,
    #[serde(default)]
    exclude: Vec<String>,
    resolver: Option<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct MemberCargoManifest {
    package: MemberPackage,
    #[serde(default)]
    workspace: Option<toml::Value>,
    #[serde(default, rename = "cargo-features")]
    cargo_features: Option<toml::Value>,
    #[serde(default)]
    lib: Option<MemberTarget>,
    #[serde(default)]
    bin: Vec<MemberTarget>,
    #[serde(default)]
    example: Vec<MemberTarget>,
    #[serde(default)]
    test: Vec<MemberTarget>,
    #[serde(default)]
    bench: Vec<MemberTarget>,
    #[serde(default)]
    features: Option<toml::Value>,
    #[serde(default)]
    target: BTreeMap<String, TargetCfgSection>,
    #[serde(default)]
    dependencies: Option<toml::Value>,
    #[serde(default, rename = "dev-dependencies")]
    dev_dependencies: Option<toml::Value>,
    #[serde(default, rename = "dev_dependencies")]
    dev_dependencies_underscore: Option<toml::Value>,
    #[serde(default, rename = "build-dependencies")]
    build_dependencies: Option<toml::Value>,
    #[serde(default, rename = "build_dependencies")]
    build_dependencies_underscore: Option<toml::Value>,
}

/// Collect the five Cargo dependency table variants (`dependencies`,
/// `dev-dependencies`, `dev_dependencies`, `build-dependencies`,
/// `build_dependencies`) without `#[serde(flatten)]` so manifests and
/// `[target.<cfg>]` tables enforce `#[serde(deny_unknown_fields)]`.
fn dep_table_sections<'a>(
    dependencies: Option<&'a toml::Value>,
    dev_dependencies: Option<&'a toml::Value>,
    dev_dependencies_underscore: Option<&'a toml::Value>,
    build_dependencies: Option<&'a toml::Value>,
    build_dependencies_underscore: Option<&'a toml::Value>,
) -> [(&'static str, Option<&'a toml::Value>); 5] {
    [
        ("dependencies", dependencies),
        ("dev-dependencies", dev_dependencies),
        ("dev_dependencies", dev_dependencies_underscore),
        ("build-dependencies", build_dependencies),
        ("build_dependencies", build_dependencies_underscore),
    ]
}

impl MemberCargoManifest {
    /// Yield every `(section_label, target)` declared in `[lib]`, `[[bin]]`,
    /// `[[example]]`, `[[test]]`, and `[[bench]]`.
    fn all_targets(&self) -> impl Iterator<Item = (&'static str, &MemberTarget)> {
        self.lib
            .iter()
            .map(|t| ("lib", t))
            .chain(self.bin.iter().map(|t| ("bin", t)))
            .chain(self.example.iter().map(|t| ("example", t)))
            .chain(self.test.iter().map(|t| ("test", t)))
            .chain(self.bench.iter().map(|t| ("bench", t)))
    }

    /// Yield every `(section_label, raw_table_value)` across top-level
    /// dependency tables and `[target.<cfg>.*]` dependency tables.
    fn all_dep_tables(&self) -> Vec<(String, Option<&toml::Value>)> {
        let mut out: Vec<(String, Option<&toml::Value>)> = dep_table_sections(
            self.dependencies.as_ref(),
            self.dev_dependencies.as_ref(),
            self.dev_dependencies_underscore.as_ref(),
            self.build_dependencies.as_ref(),
            self.build_dependencies_underscore.as_ref(),
        )
        .into_iter()
        .map(|(s, v)| (s.to_string(), v))
        .collect();
        for (cfg_name, cfg_sec) in &self.target {
            for (sec, v) in cfg_sec.sections() {
                out.push((format!("target.{cfg_name}.{sec}"), v));
            }
        }
        out
    }

    /// Reject non-table `[features]` sections or non-string-list entries.
    fn validate_features(&self, member: &str) -> Result<(), Failure> {
        let Some(features_val) = &self.features else {
            return Ok(());
        };
        let Some(table) = features_val.as_table() else {
            return Err(Failure::policy(
                "cargo-boundary",
                format!("invalid [features] in {member}/Cargo.toml"),
            ));
        };
        for (feat, deps) in table {
            let Some(items) = deps.as_array() else {
                return Err(Failure::policy(
                    "cargo-boundary",
                    format!("invalid features.{feat} in {member}/Cargo.toml"),
                ));
            };
            if items.iter().any(|item| !item.is_str()) {
                return Err(Failure::policy(
                    "cargo-boundary",
                    format!("invalid features.{feat} entry in {member}/Cargo.toml"),
                ));
            }
        }
        Ok(())
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct MemberPackage {
    #[serde(default)]
    name: Option<String>,
    #[serde(default)]
    version: Option<toml::Value>,
    #[serde(default)]
    edition: Option<toml::Value>,
    #[serde(default)]
    publish: Option<toml::Value>,
    #[serde(default)]
    description: Option<toml::Value>,
    #[serde(default)]
    license: Option<toml::Value>,
    #[serde(default)]
    repository: Option<toml::Value>,
    #[serde(default)]
    readme: Option<toml::Value>,
    #[serde(default)]
    exclude: Option<toml::Value>,
    #[serde(default)]
    metadata: Option<toml::Value>,
    #[serde(default)]
    autolib: Option<toml::Value>,
    #[serde(default)]
    autobins: Option<toml::Value>,
    #[serde(default)]
    autoexamples: Option<toml::Value>,
    #[serde(default)]
    autotests: Option<toml::Value>,
    #[serde(default)]
    autobenches: Option<toml::Value>,
    #[serde(default)]
    build: Option<toml::Value>,
    #[serde(default)]
    metabuild: Option<toml::Value>,
    #[serde(default)]
    links: Option<toml::Value>,
    #[serde(default)]
    workspace: Option<toml::Value>,
}

impl MemberPackage {
    /// Reject missing or non-2024 `package.edition` settings so every trusted
    /// workspace member compiles under the same Rust 2024 lexical grammar
    /// (including `cr"..."` raw C-string literals) that `lex_rust_tokens`
    /// enforces.
    fn validate_edition(&self, member: &str) -> Result<(), Failure> {
        if self.edition.as_ref().and_then(toml::Value::as_str) != Some("2024") {
            return Err(Failure::policy(
                "cargo-boundary",
                format!("package.edition must be \"2024\" in {member}/Cargo.toml"),
            ));
        }
        Ok(())
    }

    /// Reject non-boolean Cargo target auto-discovery settings so malformed
    /// `[package]` fields fail closed.
    fn validate_auto_discovery_fields(&self, member: &str) -> Result<(), Failure> {
        for (field, value) in [
            ("autolib", self.autolib.as_ref()),
            ("autobins", self.autobins.as_ref()),
            ("autoexamples", self.autoexamples.as_ref()),
            ("autotests", self.autotests.as_ref()),
            ("autobenches", self.autobenches.as_ref()),
        ] {
            if let Some(val) = value
                && !val.is_bool()
            {
                return Err(Failure::policy(
                    "cargo-boundary",
                    format!("invalid package.{field} in {member}/Cargo.toml"),
                ));
            }
        }
        Ok(())
    }

    /// Reject table-valued workspace inheritance on `[package]` metadata.
    fn validate_no_workspace_inheritance(&self, member: &str) -> Result<(), Failure> {
        for (field, value) in [
            ("version", self.version.as_ref()),
            ("publish", self.publish.as_ref()),
            ("description", self.description.as_ref()),
            ("license", self.license.as_ref()),
            ("repository", self.repository.as_ref()),
            ("readme", self.readme.as_ref()),
            ("exclude", self.exclude.as_ref()),
        ] {
            if value.is_some_and(toml::Value::is_table) {
                return Err(Failure::policy(
                    "cargo-boundary",
                    format!(
                        "disallowed workspace inheritance on package.{field} in {member}/Cargo.toml"
                    ),
                ));
            }
        }
        if let Some(meta) = &self.metadata
            && !meta.is_table()
        {
            return Err(Failure::policy(
                "cargo-boundary",
                format!("invalid package.metadata in {member}/Cargo.toml"),
            ));
        }
        Ok(())
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct MemberTarget {
    #[serde(default)]
    name: Option<toml::Value>,
    #[serde(default)]
    path: Option<toml::Value>,
    #[serde(default)]
    test: Option<toml::Value>,
    #[serde(default)]
    doctest: Option<toml::Value>,
    #[serde(default)]
    bench: Option<toml::Value>,
    #[serde(default)]
    doc: Option<toml::Value>,
    #[serde(default)]
    harness: Option<toml::Value>,
    #[serde(default, rename = "required-features")]
    required_features: Option<toml::Value>,
    #[serde(default, rename = "required_features")]
    required_features_underscore: Option<toml::Value>,
    #[serde(default)]
    edition: Option<toml::Value>,
    #[serde(default, rename = "proc-macro")]
    proc_macro: Option<toml::Value>,
    #[serde(default, rename = "proc_macro")]
    proc_macro_underscore: Option<toml::Value>,
    #[serde(default, rename = "crate-type")]
    crate_type: Option<toml::Value>,
    #[serde(default, rename = "crate_type")]
    crate_type_underscore: Option<toml::Value>,
}

#[derive(Default, Deserialize)]
#[serde(deny_unknown_fields)]
struct TargetCfgSection {
    #[serde(default)]
    dependencies: Option<toml::Value>,
    #[serde(default, rename = "dev-dependencies")]
    dev_dependencies: Option<toml::Value>,
    #[serde(default, rename = "dev_dependencies")]
    dev_dependencies_underscore: Option<toml::Value>,
    #[serde(default, rename = "build-dependencies")]
    build_dependencies: Option<toml::Value>,
    #[serde(default, rename = "build_dependencies")]
    build_dependencies_underscore: Option<toml::Value>,
}

impl TargetCfgSection {
    /// Yield all `(section_label, raw_table_value)` entries present in this
    /// `[target.<cfg>]` dependency table group.
    fn sections(&self) -> [(&'static str, Option<&toml::Value>); 5] {
        dep_table_sections(
            self.dependencies.as_ref(),
            self.dev_dependencies.as_ref(),
            self.dev_dependencies_underscore.as_ref(),
            self.build_dependencies.as_ref(),
            self.build_dependencies_underscore.as_ref(),
        )
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CargoLockFile {
    version: Option<i64>,
    #[serde(default)]
    package: Vec<CargoLockPackage>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CargoLockPackage {
    name: String,
    #[allow(dead_code)]
    version: String,
    source: Option<String>,
    checksum: Option<String>,
    #[serde(default)]
    #[allow(dead_code)]
    dependencies: Vec<String>,
}

/// Return `true` if `ch` is a Unicode control (`Cc` other than `\n`, `\r`,
/// `\t`), line/paragraph separator (`Zl`/`Zp`), format character (`Cf`), or
/// `Default_Ignorable_Code_Point`.
pub(crate) fn is_bidi_or_invisible_control(ch: char) -> bool {
    matches!(
        ch,
        '\u{007F}'..='\u{009F}'
            | '\u{00AD}'
            | '\u{034F}'
            | '\u{0600}'..='\u{0605}'
            | '\u{061C}'
            | '\u{06DD}'
            | '\u{070F}'
            | '\u{0890}'..='\u{0891}'
            | '\u{08E2}'
            | '\u{115F}'..='\u{1160}'
            | '\u{17B4}'..='\u{17B5}'
            | '\u{180B}'..='\u{180F}'
            | '\u{200B}'..='\u{200F}'
            | '\u{2028}'..='\u{202E}'
            | '\u{2060}'..='\u{206F}'
            | '\u{3164}'
            | '\u{FE00}'..='\u{FE0F}'
            | '\u{FEFF}'
            | '\u{FFA0}'
            | '\u{FFF0}'..='\u{FFFB}'
            | '\u{110BD}'
            | '\u{110CD}'
            | '\u{13430}'..='\u{1343F}'
            | '\u{1BCA0}'..='\u{1BCA3}'
            | '\u{1D173}'..='\u{1D17A}'
            | '\u{E0000}'..='\u{E0FFF}'
    ) || (ch <= '\u{001F}' && !matches!(ch, '\n' | '\r' | '\t'))
}

/// Fail closed if raw text `src` begins with a UTF-8 BOM or contains any
/// disallowed Unicode control, separator, format, or default-ignorable code
/// point prior to comment, string, or manifest parsing.
fn reject_bidi_or_invisible_controls(src: &str, label: &str, phase: &str) -> Result<(), Failure> {
    if src.starts_with('\u{feff}') {
        return Err(Failure::policy(phase, format!("UTF-8 BOM forbidden in {label}")));
    }
    if let Some(ch) = src.chars().find(|&c| is_bidi_or_invisible_control(c)) {
        return Err(Failure::policy(
            phase,
            format!(
                "disallowed bidi or invisible control character (U+{:04X}) in {label}",
                ch as u32
            ),
        ));
    }
    Ok(())
}

/// Return `true` if `rel` is a non-empty slash-separated relative path whose
/// segments contain only printable non-whitespace ASCII bytes (`0x21..=0x7E`,
/// excluding `'\\'`, `':'`, `'~'`, `'.'`, `'..'`, and Windows trailing-dot
/// aliases such as `foo.`).
pub(crate) fn is_canonical_ascii_rel_path(rel: &str) -> bool {
    !rel.is_empty()
        && rel.split('/').all(|seg| {
            !seg.is_empty()
                && seg != "."
                && seg != ".."
                && !seg.ends_with('.')
                && seg
                    .bytes()
                    .all(|b| (0x21..=0x7E).contains(&b) && b != b'\\' && b != b':' && b != b'~')
        })
}

/// Return `true` if `name` (matched ASCII case-insensitively) names a
/// forbidden checked-in build or cache output (`target`, `.lake`, `.olean*`,
/// `.ilean`, `.ir`, or `.ir.sig`).
fn is_forbidden_build_artifact_entry(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    lower == "target"
        || lower == ".lake"
        || lower.ends_with(".olean")
        || lower.ends_with(".olean.server")
        || lower.ends_with(".olean.private")
        || lower.ends_with(".ilean")
        || lower.ends_with(".ir")
        || lower.ends_with(".ir.sig")
}

/// Return `true` if `name` (matched ASCII case-insensitively) names a
/// forbidden repository-root build or Nix `/result*` output (`.lake`,
/// `result*`, `.olean*`, `.ilean`, `.ir`, or `.ir.sig`, allowing the active
/// Cargo workspace `target/` directory at repository root).
fn is_forbidden_root_build_artifact_entry(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    lower.starts_with("result") || (lower != "target" && is_forbidden_build_artifact_entry(name))
}

/// Return `true` if `name` (matched ASCII case-insensitively) names a
/// forbidden Cargo, toolchain, VCS, or ambient override entry (`.cargo*`,
/// `rust-toolchain`, `rust-toolchain.*`, `.gitmodules`, `.envrc`,
/// `.gitattributes`, `AGENTS.override.md`, or `lean-toolchain`).
fn is_forbidden_override_entry_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    lower.starts_with(".cargo")
        || lower == "rust-toolchain"
        || lower.starts_with("rust-toolchain.")
        || lower == ".gitmodules"
        || lower == ".envrc"
        || lower == ".gitattributes"
        || lower == "agents.override.md"
        || lower == "lean-toolchain"
}

/// Reject forbidden Cargo, toolchain, VCS, and ambient override entries
/// directly inside `dir` (ASCII case-insensitively), and optionally reject
/// root-level build/Nix `/result*` outputs.
fn reject_forbidden_overrides_in_dir(
    dir: &Path,
    location: &str,
    reject_root_artifacts: bool,
) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    let entries = match fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(err) if err.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(err) => {
            return Err(Failure::operational(
                phase,
                format!("cannot read directory {location} ({}): {err}", dir.display()),
            ));
        }
    };
    for entry in entries {
        let entry = entry.map_err(|err| {
            Failure::operational(
                phase,
                format!("cannot inspect entry {location} ({}): {err}", dir.display()),
            )
        })?;
        let raw_name = entry.file_name();
        let name = raw_name.to_string_lossy();
        if is_forbidden_override_entry_name(&name) {
            return Err(Failure::policy(
                phase,
                format!("forbidden Cargo/toolchain override {location}: {name}"),
            ));
        }
        if reject_root_artifacts && is_forbidden_root_build_artifact_entry(&name) {
            return Err(Failure::policy(
                phase,
                format!("checked-in build/cache artifact forbidden {location}: {name}"),
            ));
        }
    }
    Ok(())
}

fn is_forbidden_nested_git_entry(name: &str) -> bool {
    name.eq_ignore_ascii_case(".git")
}

/// Recursively reject forbidden override entries (`is_forbidden_override_entry_name`,
/// permitting only `trusted/lean/lean-toolchain`) and nested `.git`
/// submodule/repository entries anywhere under `trusted_dir`.
fn reject_forbidden_overrides_in_trusted_tree(trusted_dir: &Path) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    for entry in WalkDir::new(trusted_dir).follow_links(false).sort_by_file_name() {
        let entry = entry.map_err(|err| {
            Failure::operational(
                phase,
                format!("cannot inspect trusted/ ({}): {err}", trusted_dir.display()),
            )
        })?;
        let path = entry.path();
        let Ok(rel) = path.strip_prefix(trusted_dir) else {
            continue;
        };
        if rel.as_os_str().is_empty() {
            continue;
        }
        let raw_name = entry.file_name();
        let name = raw_name.to_string_lossy();
        if is_forbidden_nested_git_entry(&name) {
            return Err(Failure::policy(
                phase,
                format!("forbidden nested .git/submodule entry in trusted/: {}", rel.display()),
            ));
        }
        if is_forbidden_override_entry_name(&name) && rel != Path::new("lean/lean-toolchain") {
            return Err(Failure::policy(
                phase,
                format!("forbidden Cargo/toolchain override in trusted/: {}", rel.display()),
            ));
        }
    }
    Ok(())
}

/// Reject `.cargo*`, `rust-toolchain*`, `.gitmodules`, `.envrc`,
/// `.gitattributes`, `AGENTS.override.md`, and `lean-toolchain` overrides at
/// the repository root and anywhere inside `trusted/` (including
/// case-insensitive directory entries; `trusted/lean/lean-toolchain` sits one
/// level deeper and remains permitted), plus nested `.git` entries inside
/// `trusted/`.
pub(crate) fn reject_cargo_toolchain_overrides(checkout: &Path) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    for forbidden in [
        ".cargo",
        ".cargo/config",
        ".cargo/config.toml",
        "rust-toolchain",
        "rust-toolchain.toml",
        ".gitmodules",
        ".envrc",
        ".gitattributes",
        "AGENTS.override.md",
        "lean-toolchain",
    ] {
        if fs::symlink_metadata(checkout.join(forbidden)).is_ok() {
            return Err(Failure::new(
                1,
                phase,
                format!("forbidden Cargo/toolchain override at repository root: {forbidden}"),
            ));
        }
    }
    reject_forbidden_overrides_in_dir(checkout, "at repository root", true)?;
    let trusted_dir = checkout.join("trusted");
    if fs::symlink_metadata(&trusted_dir)
        .map(|m| !m.file_type().is_symlink() && m.file_type().is_dir())
        .unwrap_or(false)
    {
        reject_forbidden_overrides_in_dir(&trusted_dir, "in trusted/", false)?;
        if fs::symlink_metadata(checkout.join("Cargo.toml")).is_err() {
            reject_forbidden_overrides_in_trusted_tree(&trusted_dir)?;
        }
    }
    Ok(())
}

fn verify_pinned_root_manifest_text(
    target_path: &Path,
    rel_path: &str,
    phase: &str,
) -> Result<(), Failure> {
    let raw = fs::read(target_path).map_err(|e| {
        Failure::operational(phase, format!("cannot read root-manifest entry {rel_path}: {e}"))
    })?;
    let must_be_utf8 = matches!(rel_path, "Cargo.toml" | "Cargo.lock" | "flake.nix" | "flake.lock")
        || matches!(
            Path::new(rel_path).extension().and_then(|e| e.to_str()),
            Some(
                "nix"
                    | "toml"
                    | "lock"
                    | "json"
                    | "sha256"
                    | "rs"
                    | "lean"
                    | "md"
                    | "sh"
                    | "py"
                    | "yml"
                    | "yaml"
                    | "txt"
            )
        );
    if must_be_utf8 {
        let text = std::str::from_utf8(&raw).map_err(|e| {
            Failure::policy(
                phase,
                format!("non-UTF-8 root-manifest entry forbidden ({rel_path}): {e}"),
            )
        })?;
        reject_bidi_or_invisible_controls(text, &format!("root-manifest entry {rel_path}"), phase)?;
    } else if !raw.contains(&0)
        && let Ok(text) = std::str::from_utf8(&raw)
    {
        reject_bidi_or_invisible_controls(text, &format!("root-manifest entry {rel_path}"), phase)?;
    }
    Ok(())
}

/// Reject Git submodules (`160000` gitlink index entries) within `checkout`
/// when `checkout` resides inside a Git working tree (without walking above
/// system temporary roots such as `/tmp`).
fn reject_git_submodules(
    checkout: &Path,
    checkout_canon: &Path,
    phase: &str,
) -> Result<(), Failure> {
    let tmp_canon = fs::canonicalize(std::env::temp_dir()).ok();
    let mut has_git = false;
    let mut cur = Some(checkout_canon);
    while let Some(dir) = cur {
        if tmp_canon.as_deref() == Some(dir) || dir.parent().is_none() {
            break;
        }
        if fs::symlink_metadata(dir.join(".git")).is_ok() {
            has_git = true;
            break;
        }
        cur = dir.parent();
    }
    if !has_git {
        return Ok(());
    }
    let mut cmd = Command::new("git");
    cmd.args(["-c", "core.fsmonitor=false", "ls-files", "--stage", "-z", "--", "."])
        .current_dir(checkout)
        .env_clear()
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_CONFIG_GLOBAL", "/dev/null");
    if let Some(path) = std::env::var_os("PATH") {
        cmd.env("PATH", path);
    }
    let output = cmd.output().map_err(|err| {
        Failure::operational(phase, format!("cannot inspect git index for submodules: {err}"))
    })?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(Failure::policy(
            phase,
            format!("git submodule index inspection failed: {}", stderr.trim()),
        ));
    }
    for record in output.stdout.split(|&b| b == 0).filter(|r| !r.is_empty()) {
        if let Some(rest) = record.strip_prefix(b"160000 ") {
            let path_bytes = rest.splitn(2, |&b| b == b'\t').nth(1).unwrap_or(rest);
            return Err(Failure::policy(
                phase,
                format!(
                    "gitlink/submodule forbidden in workspace: {}",
                    String::from_utf8_lossy(path_bytes)
                ),
            ));
        }
    }
    Ok(())
}

/// Reject case-folded directory entry aliases (`requested != on_disk` with
/// matching ASCII/Unicode lowercase) in `dir` so case-sensitive Linux audits
/// never skip files that case-insensitive Windows/macOS filesystems resolve.
fn verify_exact_case_entry(
    dir: &Path,
    seg: &OsStr,
    label: &str,
    phase: &str,
) -> Result<(), Failure> {
    let Ok(meta) = fs::symlink_metadata(dir) else {
        return Ok(());
    };
    if meta.file_type().is_symlink() || !meta.file_type().is_dir() {
        return Ok(());
    }
    let Some(seg_str) = seg.to_str() else {
        return Ok(());
    };
    let seg_lower = seg_str.to_lowercase();
    let entries = fs::read_dir(dir).map_err(|err| {
        Failure::operational(phase, format!("cannot read directory {}: {err}", dir.display()))
    })?;
    let mut found_exact = false;
    let mut folded_match: Option<String> = None;
    for entry in entries {
        let entry = entry.map_err(|err| {
            Failure::operational(phase, format!("cannot inspect entry in {}: {err}", dir.display()))
        })?;
        let raw = entry.file_name();
        if raw == seg {
            found_exact = true;
            continue;
        }
        let name = raw.to_string_lossy();
        if (name.eq_ignore_ascii_case(seg_str) || name.to_lowercase() == seg_lower)
            && folded_match.is_none()
        {
            folded_match = Some(name.into_owned());
        }
    }
    if !found_exact && let Some(name) = folded_match {
        return Err(Failure::policy(
            phase,
            format!(
                "case-folded path alias forbidden for {label}: requested '{seg_str}', found '{name}' in {}",
                dir.display()
            ),
        ));
    }
    Ok(())
}

/// Reject case-folded directory entry aliases along each existing component
/// prefix (and the first missing component) of `rel` under `base_dir`.
fn verify_exact_case_path_prefix(
    base_dir: &Path,
    rel: &Path,
    label: &str,
    phase: &str,
) -> Result<(), Failure> {
    let mut cur = base_dir.to_path_buf();
    for component in rel.components() {
        let Component::Normal(seg) = component else {
            break;
        };
        verify_exact_case_entry(&cur, seg, label, phase)?;
        cur.push(seg);
        match fs::symlink_metadata(&cur) {
            Ok(meta) if !meta.file_type().is_symlink() && meta.file_type().is_dir() => {}
            _ => break,
        }
    }
    Ok(())
}

/// Verify `trusted/root-manifest.sha256` (when present): every non-comment line
/// must name a unique clean relative path whose on-disk SHA-256 matches,
/// textual pinned manifests must pass UTF-8 and bidi/invisible-control scans,
/// and the four root build files (`Cargo.toml`, `Cargo.lock`, `flake.nix`,
/// `flake.lock`) must be covered.
fn verify_root_manifest_sha256(checkout: &Path) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    let manifest_path = checkout.join("trusted/root-manifest.sha256");
    if fs::symlink_metadata(&manifest_path).is_err() {
        return Ok(());
    }
    validate_single_link_regular(&manifest_path, "root TCB manifest", phase)?;
    let manifest_text = fs::read_to_string(&manifest_path)
        .map_err(|e| Failure::new(1, phase, format!("cannot read root-manifest.sha256: {e}")))?;
    let mut seen_paths = BTreeSet::new();
    for line in
        manifest_text.lines().map(str::trim).filter(|l| !l.is_empty() && !l.starts_with('#'))
    {
        let Some((expected_hex, rel_path)) = line.split_once("  ") else {
            return Err(Failure::new(
                1,
                phase,
                format!("malformed line in root-manifest.sha256: {line}"),
            ));
        };
        if !is_sha256_hex(expected_hex)
            || !is_clean_relative_path(rel_path)
            || !seen_paths.insert(rel_path.to_string())
        {
            return Err(Failure::new(
                1,
                phase,
                format!("invalid or duplicate entry in root-manifest.sha256: {line}"),
            ));
        }
        let target_path = checkout.join(rel_path);
        validate_single_link_regular(
            &target_path,
            &format!("root-manifest entry {rel_path}"),
            phase,
        )?;
        let actual_hex =
            sha256_file(&target_path, phase).map_err(|e| Failure::new(1, phase, e.message))?;
        if !actual_hex.eq_ignore_ascii_case(expected_hex) {
            return Err(Failure::new(
                1,
                phase,
                format!(
                    "root TCB manifest digest mismatch for {rel_path}: expected {expected_hex}, got {actual_hex}"
                ),
            ));
        }
        verify_pinned_root_manifest_text(&target_path, rel_path, phase)?;
    }
    for required_rel in ["Cargo.toml", "Cargo.lock", "flake.nix", "flake.lock"] {
        if !seen_paths.contains(required_rel) {
            return Err(Failure::new(
                1,
                phase,
                format!("root-manifest.sha256 missing required entry: {required_rel}"),
            ));
        }
    }
    Ok(())
}

fn map_bundle_error(err: BundleError) -> Failure {
    match err {
        BundleError::Policy(msg) => Failure::policy("bundle-manifest", msg),
        BundleError::Io(io_err) => {
            Failure::operational("bundle-manifest", format!("bundle I/O error: {io_err}"))
        }
    }
}

/// Verify that `trusted/cargo-anneal/src/bundled_resources.rs`,
/// `trusted/cargo-anneal/src/bundled_theory.json`, `theory/bundle-manifest.json`,
/// and every canonical source in [`cargo_anneal::bundle::TRUSTED_BUNDLE_SOURCES`],
/// [`cargo_anneal::bundle::THEORY_BUNDLE_MANIFEST`], and
/// [`cargo_anneal::bundle::PROVENANCE_SOURCES`] are regular files under
/// regular directories and match [`render_bundled_resources`] and
/// [`render_bundled_theory`] byte-for-byte.
pub fn verify_bundled_resources(checkout: &Path) -> Result<(), Failure> {
    let phase = "bundle-manifest";
    let (destination, permissions) =
        validate_bundle_destination(checkout).map_err(map_bundle_error)?;
    if permissions.is_none() {
        return Err(Failure::policy(
            phase,
            format!("missing bundled_resources.rs: {}", destination.display()),
        ));
    }
    let expected = render_bundled_resources(checkout).map_err(map_bundle_error)?;
    let actual = fs::read(&destination).map_err(|e| {
        Failure::operational(phase, format!("cannot read {}: {e}", destination.display()))
    })?;
    if actual != expected.as_bytes() {
        return Err(Failure::policy(
            phase,
            format!(
                "{} differs from canonical bundled sources; run regenerate_bundle",
                destination.display()
            ),
        ));
    }

    let (theory_destination, theory_permissions) =
        validate_theory_bundle_destination(checkout).map_err(map_bundle_error)?;
    if theory_permissions.is_none() {
        return Err(Failure::policy(
            phase,
            format!("missing bundled_theory.json: {}", theory_destination.display()),
        ));
    }
    let expected_theory = render_bundled_theory(checkout).map_err(map_bundle_error)?;
    let actual_theory = fs::read(&theory_destination).map_err(|e| {
        Failure::operational(phase, format!("cannot read {}: {e}", theory_destination.display()))
    })?;
    if actual_theory != expected_theory.as_bytes() {
        return Err(Failure::policy(
            phase,
            format!(
                "{} differs from canonical bundled theory sources; run regenerate_bundle",
                theory_destination.display()
            ),
        ));
    }
    Ok(())
}

/// Reject Cargo glob metacharacters in workspace `members` / `exclude` entries
/// so workspace membership is always explicit and literal.
fn has_cargo_glob_meta(rel: &str) -> bool {
    rel.bytes().any(|b| matches!(b, b'*' | b'?' | b'[' | b']'))
}

/// Validate every component of clean relative path `rel` under `root` via
/// `symlink_metadata`, requiring each component to be an existing regular
/// (non-symlink) directory whose canonical path stays strictly under
/// `root_canon`.
fn validate_real_dir(
    root: &Path,
    root_canon: &Path,
    rel: &Path,
    label: &str,
    phase: &str,
) -> Result<(PathBuf, PathBuf), Failure> {
    let mut cur = root.to_path_buf();
    let mut has_component = false;
    for component in rel.components() {
        let Component::Normal(segment) = component else {
            return Err(Failure::policy(
                phase,
                format!("invalid relative path for {label}: {}", rel.display()),
            ));
        };
        has_component = true;
        verify_exact_case_entry(&cur, segment, label, phase)?;
        cur.push(segment);
        let meta = fs::symlink_metadata(&cur).map_err(|err| {
            if err.kind() == io::ErrorKind::NotFound {
                Failure::policy(phase, format!("{label} does not exist: {}", cur.display()))
            } else {
                Failure::operational(
                    phase,
                    format!("cannot inspect {label} {}: {err}", cur.display()),
                )
            }
        })?;
        if meta.file_type().is_symlink() || !meta.file_type().is_dir() {
            return Err(Failure::policy(
                phase,
                format!("{label} must be a regular directory: {}", cur.display()),
            ));
        }
    }
    if !has_component {
        return Err(Failure::policy(phase, format!("empty relative path for {label}")));
    }
    let canon = fs::canonicalize(&cur).map_err(|err| {
        Failure::operational(phase, format!("cannot canonicalize {label} {}: {err}", cur.display()))
    })?;
    if !canon.starts_with(root_canon) || canon == root_canon {
        return Err(Failure::policy(
            phase,
            format!("{label} escapes containment root: {}", cur.display()),
        ));
    }
    Ok((cur, canon))
}

/// Validate every existing component of clean relative directory path `rel`
/// under `root` via `symlink_metadata`, rejecting symlinks, non-directories,
/// or canonical escapes while permitting absent `workspace.exclude` targets.
/// Returns `Some((dir, canon))` when `rel` exists on disk.
fn validate_existing_real_dir(
    root: &Path,
    root_canon: &Path,
    rel: &Path,
    label: &str,
    phase: &str,
) -> Result<Option<(PathBuf, PathBuf)>, Failure> {
    let mut cur = root.to_path_buf();
    let mut has_component = false;
    for component in rel.components() {
        let Component::Normal(segment) = component else {
            return Err(Failure::policy(
                phase,
                format!("invalid relative path for {label}: {}", rel.display()),
            ));
        };
        has_component = true;
        verify_exact_case_entry(&cur, segment, label, phase)?;
        cur.push(segment);
        match fs::symlink_metadata(&cur) {
            Ok(meta) if !meta.file_type().is_symlink() && meta.file_type().is_dir() => {}
            Ok(_) => {
                return Err(Failure::policy(
                    phase,
                    format!("{label} must be a regular directory: {}", cur.display()),
                ));
            }
            Err(err) if err.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(err) => {
                return Err(Failure::operational(
                    phase,
                    format!("cannot inspect {label} {}: {err}", cur.display()),
                ));
            }
        }
    }
    if !has_component {
        return Err(Failure::policy(phase, format!("empty relative path for {label}")));
    }
    let canon = fs::canonicalize(&cur).map_err(|err| {
        Failure::operational(phase, format!("cannot canonicalize {label} {}: {err}", cur.display()))
    })?;
    if !canon.starts_with(root_canon) || canon == root_canon {
        return Err(Failure::policy(
            phase,
            format!("{label} escapes containment root: {}", cur.display()),
        ));
    }
    Ok(Some((cur, canon)))
}

/// Require `meta` to describe a non-symlink regular file with a single hard
/// link (`nlink == 1` on Unix; fails closed on non-Unix hosts) so an external
/// hard link outside `trusted/` cannot share an inode with an audited
/// workspace or manifest file.
fn check_single_link_regular_meta(
    path: &Path,
    meta: &fs::Metadata,
    label: &str,
    phase: &str,
) -> Result<(), Failure> {
    if meta.file_type().is_symlink() || !meta.file_type().is_file() {
        return Err(Failure::policy(
            phase,
            format!("{label} must be a regular file: {}", path.display()),
        ));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        if meta.nlink() > 1 {
            return Err(Failure::policy(
                phase,
                format!(
                    "{label} must not be hard-linked (multiple hard links, nlink={}): {}",
                    meta.nlink(),
                    path.display()
                ),
            ));
        }
    }
    #[cfg(not(unix))]
    {
        return Err(Failure::policy(
            phase,
            format!(
                "cannot verify single hard-link invariant for {label} on this platform: {}",
                path.display()
            ),
        ));
    }
    Ok(())
}

/// Validate that `path` exists as a non-symlink regular file with a single
/// hard link (`nlink == 1` on Unix; fails closed on non-Unix hosts).
fn validate_single_link_regular(path: &Path, label: &str, phase: &str) -> Result<(), Failure> {
    let meta = fs::symlink_metadata(path).map_err(|err| {
        if err.kind() == io::ErrorKind::NotFound {
            Failure::policy(phase, format!("{label} does not exist: {}", path.display()))
        } else {
            Failure::operational(phase, format!("cannot inspect {label} {}: {err}", path.display()))
        }
    })?;
    check_single_link_regular_meta(path, &meta, label, phase)
}

/// Validate that every parent directory of clean relative file path `rel`
/// under `root` is an existing real (non-symlink) directory and that the leaf
/// itself is an existing single-link (non-symlink, non-hard-linked) regular
/// file strictly inside `root_canon`.
fn validate_real_file(
    root: &Path,
    root_canon: &Path,
    rel: &Path,
    label: &str,
    phase: &str,
) -> Result<(PathBuf, PathBuf), Failure> {
    if let Some(parent) = rel.parent()
        && !parent.as_os_str().is_empty()
    {
        validate_real_dir(root, root_canon, parent, label, phase)?;
    }
    if let Some(leaf) = rel.file_name() {
        let parent_dir = rel
            .parent()
            .filter(|p| !p.as_os_str().is_empty())
            .map(|p| root.join(p))
            .unwrap_or_else(|| root.to_path_buf());
        verify_exact_case_entry(&parent_dir, leaf, label, phase)?;
    }
    let full = root.join(rel);
    validate_single_link_regular(&full, label, phase)?;
    let canon = fs::canonicalize(&full).map_err(|err| {
        Failure::operational(
            phase,
            format!("cannot canonicalize {label} {}: {err}", full.display()),
        )
    })?;
    if !canon.starts_with(root_canon) {
        return Err(Failure::policy(
            phase,
            format!("{label} escapes containment root: {}", full.display()),
        ));
    }
    Ok((full, canon))
}

/// Verify that a workspace member target table does not override `edition` or
/// enable procedural macros and, when it declares an explicit `path`, that
/// every directory component and the target file itself are real (non-symlink)
/// entries contained inside `member_canon`.
fn validate_member_target(
    member: &str,
    member_dir: &Path,
    member_canon: &Path,
    section: &str,
    target: &MemberTarget,
) -> Result<Option<PathBuf>, Failure> {
    let phase = "cargo-boundary";
    if target.edition.is_some() {
        return Err(Failure::policy(
            phase,
            format!(
                "disallowed target-level edition override in {member}/Cargo.toml ({section}.edition)"
            ),
        ));
    }
    for (field, value) in [
        ("test", target.test.as_ref()),
        ("bench", target.bench.as_ref()),
        ("doc", target.doc.as_ref()),
        ("harness", target.harness.as_ref()),
    ] {
        if let Some(val) = value
            && !val.is_bool()
        {
            return Err(Failure::policy(
                phase,
                format!("invalid {section}.{field} in {member}/Cargo.toml"),
            ));
        }
    }
    for (field, value) in [
        ("required-features", target.required_features.as_ref()),
        ("required_features", target.required_features_underscore.as_ref()),
    ] {
        if let Some(val) = value {
            let Some(items) = val.as_array() else {
                return Err(Failure::policy(
                    phase,
                    format!("invalid {section}.{field} in {member}/Cargo.toml"),
                ));
            };
            if items.iter().any(|item| !item.is_str()) {
                return Err(Failure::policy(
                    phase,
                    format!("invalid {section}.{field} entry in {member}/Cargo.toml"),
                ));
            }
        }
    }
    for (field, value) in [
        ("proc-macro", target.proc_macro.as_ref()),
        ("proc_macro", target.proc_macro_underscore.as_ref()),
    ] {
        if let Some(val) = value {
            match val.as_bool() {
                Some(false) => {}
                Some(true) => {
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "disallowed proc-macro target in {member}/Cargo.toml ({section}.{field})"
                        ),
                    ));
                }
                None => {
                    return Err(Failure::policy(
                        phase,
                        format!("invalid {section}.{field} in {member}/Cargo.toml"),
                    ));
                }
            }
        }
    }
    for (field, value) in [
        ("crate-type", target.crate_type.as_ref()),
        ("crate_type", target.crate_type_underscore.as_ref()),
    ] {
        if let Some(val) = value {
            let Some(items) = val.as_array() else {
                return Err(Failure::policy(
                    phase,
                    format!("invalid {section}.{field} in {member}/Cargo.toml"),
                ));
            };
            for item in items {
                let Some(crate_type) = item.as_str() else {
                    return Err(Failure::policy(
                        phase,
                        format!("invalid {section}.{field} entry in {member}/Cargo.toml"),
                    ));
                };
                if crate_type == "proc-macro" {
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "disallowed proc-macro crate-type in {member}/Cargo.toml ({section}.{field})"
                        ),
                    ));
                }
            }
        }
    }

    let Some(path_val) = &target.path else {
        return Ok(None);
    };
    let Some(p) = path_val.as_str() else {
        return Err(Failure::new(
            1,
            phase,
            format!("invalid {section}.path in {member}/Cargo.toml"),
        ));
    };
    if p.contains('\0') || p.ends_with('/') || has_non_portable_path_syntax(p) {
        return Err(Failure::new(
            1,
            phase,
            format!("{member} target {section}.path escapes member directory: {p}"),
        ));
    }
    let mut clean_rel = PathBuf::new();
    for component in Path::new(p).components() {
        match component {
            Component::Normal(seg) => clean_rel.push(seg),
            Component::CurDir => {}
            Component::Prefix(_) | Component::RootDir | Component::ParentDir => {
                return Err(Failure::new(
                    1,
                    phase,
                    format!("{member} target {section}.path escapes member directory: {p}"),
                ));
            }
        }
    }
    if clean_rel.as_os_str().is_empty() {
        return Err(Failure::new(
            1,
            phase,
            format!("invalid {section}.path in {member}/Cargo.toml"),
        ));
    }
    let (target_path, _) = validate_real_file(
        member_dir,
        member_canon,
        &clean_rel,
        &format!("{member} target {section}.path"),
        phase,
    )?;
    Ok(Some(target_path))
}

/// Returns `true` when `rel_str` carries an extension for source, manifest,
/// documentation, script, or configuration text that must always parse as
/// valid UTF-8 free of disallowed Unicode control/format characters.
fn is_mandatory_utf8_member_path(rel_str: &str) -> bool {
    let ext = rel_str.rsplit_once('.').map(|(_, e)| e.to_ascii_lowercase());
    matches!(
        ext.as_deref(),
        Some(
            "rs" | "inc"
                | "toml"
                | "lock"
                | "md"
                | "txt"
                | "json"
                | "lean"
                | "yml"
                | "yaml"
                | "sh"
                | "py"
        )
    )
}

/// Validate a workspace `members` or `exclude` directory path under `trusted/`
/// against bidi/control, canonical printable-ASCII, override-name, and
/// global case-collision invariants across all registered ancestor prefixes
/// and workspace roots.
fn register_workspace_dir_path(
    path_str: &str,
    label: &str,
    workspace_roots: &mut BTreeMap<String, String>,
    global_lower_paths: &mut BTreeMap<String, String>,
    phase: &str,
) -> Result<(), Failure> {
    if path_str.chars().any(is_bidi_or_invisible_control) {
        return Err(Failure::policy(
            phase,
            format!("disallowed bidi or invisible control character in {label}: {path_str}"),
        ));
    }
    if !is_canonical_ascii_rel_path(path_str)
        || !path_str.starts_with("trusted/")
        || has_cargo_glob_meta(path_str)
    {
        return Err(Failure::new(
            1,
            phase,
            format!("{label} outside trusted/, non-ASCII, or uses glob: {path_str}"),
        ));
    }
    if path_str.split('/').any(is_forbidden_override_entry_name) {
        return Err(Failure::policy(
            phase,
            format!("forbidden Cargo/toolchain override in {label}: {path_str}"),
        ));
    }
    let lower = path_str.to_ascii_lowercase();
    if let Some(prev) = workspace_roots.insert(lower, path_str.to_string()) {
        let kind = if prev == path_str { "duplicate" } else { "case-colliding" };
        return Err(Failure::policy(
            phase,
            format!("{kind} workspace paths for {label}: {prev} vs {path_str}"),
        ));
    }
    let mut prefix = String::new();
    for seg in path_str.split('/') {
        if !prefix.is_empty() {
            prefix.push('/');
        }
        prefix.push_str(seg);
        let p_lower = prefix.to_ascii_lowercase();
        if let Some(prev) = global_lower_paths.get(&p_lower) {
            if prev != &prefix {
                return Err(Failure::policy(
                    phase,
                    format!("case-colliding workspace paths: {prev} vs {prefix}"),
                ));
            }
        } else {
            global_lower_paths.insert(p_lower, prefix.clone());
        }
    }
    Ok(())
}

/// Walk the entire workspace member directory without following symlinks,
/// Enforce whole-tree filesystem hygiene across a `trusted/` directory root
/// (every `workspace.members` crate tree—including `src/`, `examples/`,
/// `tests/`, `benches/`, and non-compiled data or test fixtures—as well as
/// existing `workspace.exclude` directories): every entry must have a
/// canonical printable-ASCII case-collision-free relative path, be a real
/// directory or a single-link regular file (`nlink == 1` on Unix) free of
/// canonical escapes outside `root_canon`, mandatory UTF-8 source/config/doc
/// extensions and other NUL-free valid UTF-8 text files must be free of
/// disallowed Unicode control/format characters (while binary resources remain
/// permitted), and no nested Cargo/toolchain/ambient override entries
/// (`.cargo*`, `rust-toolchain*`, `.gitmodules`, `.envrc`, `.gitattributes`,
/// `AGENTS.override.md`, or `lean-toolchain` outside
/// `trusted/lean/lean-toolchain`) may appear anywhere in the tree.
fn verify_trusted_subtree_hygiene(
    tree_kind: &str,
    root_rel: &str,
    root_dir: &Path,
    root_canon: &Path,
    global_lower_paths: &mut BTreeMap<String, String>,
) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    let mut seen_lower_paths: BTreeMap<String, String> = BTreeMap::new();
    for entry in WalkDir::new(root_dir).follow_links(false).sort_by_file_name() {
        let entry = entry.map_err(|err| {
            Failure::policy(phase, format!("cannot walk {tree_kind} {root_rel}: {err}"))
        })?;
        let path = entry.path();
        let rel = path.strip_prefix(root_dir).unwrap_or(path);
        let ft = entry.file_type();
        if ft.is_symlink() {
            return Err(Failure::policy(
                phase,
                format!("symlink forbidden in {tree_kind} {root_rel}: {}", rel.display()),
            ));
        }
        let mut rel_str = String::new();
        if !rel.as_os_str().is_empty() {
            if rel.to_string_lossy().chars().any(is_bidi_or_invisible_control) {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "disallowed bidi or invisible control character in {tree_kind} {root_rel} path: {}",
                        rel.display()
                    ),
                ));
            }
            let mut segments = Vec::new();
            for comp in rel.components() {
                match comp {
                    Component::Normal(os_seg) => {
                        let Some(seg) = os_seg.to_str() else {
                            return Err(Failure::policy(
                                phase,
                                format!(
                                    "non-UTF-8 path forbidden in {tree_kind} {root_rel}: {}",
                                    rel.display()
                                ),
                            ));
                        };
                        segments.push(seg);
                    }
                    _ => {
                        return Err(Failure::policy(
                            phase,
                            format!(
                                "non-canonical path component forbidden in {tree_kind} {root_rel}: {}",
                                rel.display()
                            ),
                        ));
                    }
                }
            }
            rel_str = segments.join("/");
            if !is_canonical_ascii_rel_path(&rel_str) {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "non-ASCII or non-canonical relative path forbidden in {tree_kind} {root_rel}: {rel_str}"
                    ),
                ));
            }
            if let Some(prev) =
                seen_lower_paths.insert(rel_str.to_ascii_lowercase(), rel_str.clone())
            {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "case-colliding paths forbidden in {tree_kind} {root_rel}: {prev} vs {rel_str}"
                    ),
                ));
            }
            let full_rel = format!("{root_rel}/{rel_str}");
            let full_lower = full_rel.to_ascii_lowercase();
            if let Some(prev) = global_lower_paths.get(&full_lower) {
                if prev != &full_rel {
                    return Err(Failure::policy(
                        phase,
                        format!("case-colliding workspace paths: {prev} vs {full_rel}"),
                    ));
                }
            } else {
                global_lower_paths.insert(full_lower, full_rel.clone());
            }
            let entry_name = entry.file_name();
            let entry_name_str = entry_name.to_string_lossy();
            if is_forbidden_nested_git_entry(&entry_name_str) {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "forbidden nested .git/submodule entry in {tree_kind} {root_rel}: {}",
                        rel.display()
                    ),
                ));
            }
            if is_forbidden_build_artifact_entry(&entry_name_str) {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "checked-in build/cache artifact forbidden in {tree_kind} {root_rel}: {}",
                        rel.display()
                    ),
                ));
            }
            if is_forbidden_override_entry_name(&entry_name_str)
                && full_rel != "trusted/lean/lean-toolchain"
            {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "forbidden Cargo/toolchain override in {tree_kind} {root_rel}: {}",
                        rel.display()
                    ),
                ));
            }
        }
        if ft.is_dir() {
            let canon = fs::canonicalize(path).map_err(|err| {
                Failure::operational(
                    phase,
                    format!("cannot canonicalize {tree_kind} directory {}: {err}", path.display()),
                )
            })?;
            if !canon.starts_with(root_canon) {
                return Err(Failure::policy(
                    phase,
                    format!("{tree_kind} directory escapes {root_rel}: {}", rel.display()),
                ));
            }
            continue;
        }
        if !ft.is_file() {
            return Err(Failure::policy(
                phase,
                format!("non-regular entry forbidden in {tree_kind} {root_rel}: {}", rel.display()),
            ));
        }
        let meta = entry.metadata().map_err(|err| {
            Failure::operational(
                phase,
                format!("cannot inspect {tree_kind} file {}: {err}", path.display()),
            )
        })?;
        check_single_link_regular_meta(
            path,
            &meta,
            &format!("{tree_kind} {root_rel} file {}", rel.display()),
            phase,
        )?;
        let canon = fs::canonicalize(path).map_err(|err| {
            Failure::operational(
                phase,
                format!("cannot canonicalize {tree_kind} file {}: {err}", path.display()),
            )
        })?;
        if !canon.starts_with(root_canon) {
            return Err(Failure::policy(
                phase,
                format!("{tree_kind} file escapes {root_rel}: {}", rel.display()),
            ));
        }
        let raw = fs::read(path).map_err(|err| {
            Failure::operational(
                phase,
                format!("cannot read {tree_kind} file {}: {err}", path.display()),
            )
        })?;
        if is_mandatory_utf8_member_path(&rel_str) {
            let text = std::str::from_utf8(&raw).map_err(|err| {
                Failure::policy(
                    phase,
                    format!(
                        "non-UTF-8 file forbidden in {tree_kind} {root_rel} ({}): {err}",
                        rel.display()
                    ),
                )
            })?;
            reject_bidi_or_invisible_controls(
                text,
                &format!("{tree_kind} {root_rel} file {rel_str}"),
                phase,
            )?;
        } else if !raw.contains(&0)
            && let Ok(text) = std::str::from_utf8(&raw)
        {
            reject_bidi_or_invisible_controls(
                text,
                &format!("{tree_kind} {root_rel} file {rel_str}"),
                phase,
            )?;
        }
    }
    Ok(())
}

/// Reject forbidden override entries in any uncached intermediate directory
/// between `trusted/` and `rel_root` (for example `trusted/sub/` for
/// `trusted/sub/pkg`) that Cargo or rustup could inherit.
fn reject_forbidden_overrides_along_ancestors(
    checkout: &Path,
    rel_root: &str,
    checked_ancestor_dirs: &mut BTreeSet<PathBuf>,
) -> Result<(), Failure> {
    let mut ancestor = checkout.to_path_buf();
    let components: Vec<_> = Path::new(rel_root).components().collect();
    for comp in &components[..components.len().saturating_sub(1)] {
        ancestor.push(comp);
        if checked_ancestor_dirs.insert(ancestor.clone()) {
            let rel_display = ancestor.strip_prefix(checkout).unwrap_or(&ancestor).display();
            reject_forbidden_overrides_in_dir(&ancestor, &format!("in {rel_display}/"), false)?;
        }
    }
    Ok(())
}

/// How `rustc` (Rust 2024) computes the base directory for out-of-line
/// `mod <ident>;` declarations inside a compiled source file.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum ModuleDirMode {
    /// Crate root (`src/lib.rs`, `src/main.rs`, `src/bin/*.rs`, `tests/*.rs`,
    /// `tests/*/main.rs`, explicit target `path`, etc.), `mod.rs`,
    /// `#[path = "..."]`-loaded file, or `include!`-loaded file: out-of-line
    /// `mod <ident>;` searches `source_file.parent()` plus any enclosing
    /// inline `mod` blocks.
    ParentDir,
    /// Non-root out-of-line module `<stem>.rs` loaded via `mod <stem>;`:
    /// out-of-line `mod <ident>;` searches `source_file.parent()/<stem>` plus
    /// any enclosing inline `mod` blocks.
    StemSubdir,
}

/// Return `true` if `name` is a single non-empty normal path segment for a
/// Cargo target name (`[[bin]]`, `[[example]]`, `[[test]]`, `[[bench]]`).
fn is_single_normal_segment(name: &str) -> bool {
    if name.is_empty() || name.contains('/') || name.contains('\\') || name == "." || name == ".." {
        return false;
    }
    let mut comps = Path::new(name).components();
    matches!(comps.next(), Some(Component::Normal(_))) && comps.next().is_none()
}

/// Seed the compiled Cargo host-source closure for `member` from every
/// validated explicit target `path`, `[lib]` (explicit `src/lib.rs` or
/// `autolib`-discovered `src/lib.rs` when `[lib]` is omitted), every explicit
/// pathless multi-target (`[[bin]]`, `[[example]]`, `[[test]]`, `[[bench]]`,
/// even when `auto<kind> = false`), and auto-discovered targets whose
/// `auto<kind>` setting is not `false` (skipping names overridden by explicit
/// targets).
///
/// Unreferenced files outside these Cargo target roots (such as non-compiled
/// test fixture data under `src/fixtures/` or `tests/fixtures/`, or disabled
/// targets when `autolib`/`auto<kind> = false`) remain covered by
/// [`verify_trusted_subtree_hygiene`] without being lexed as compiled host Rust;
/// every compiled module (including `src/*.rs` submodules and
/// `tests/support/mod.rs`) is reached through out-of-line `mod`, `#[path]`,
/// and `include!` traversal from these target roots.
fn collect_cargo_target_roots(
    member: &str,
    member_dir: &Path,
    member_canon: &Path,
    pkg_name: &str,
    manifest: &MemberCargoManifest,
    explicit_targets: Vec<PathBuf>,
) -> Result<Vec<(PathBuf, ModuleDirMode)>, Failure> {
    let phase = "cargo-boundary";
    let mut roots: Vec<(PathBuf, ModuleDirMode)> =
        explicit_targets.into_iter().map(|p| (p, ModuleDirMode::ParentDir)).collect();

    if let Some(lib) = &manifest.lib {
        if lib.path.is_none() {
            verify_exact_case_path_prefix(
                member_dir,
                Path::new("src/lib.rs"),
                &format!("{member} target lib.path"),
                phase,
            )?;
            if fs::symlink_metadata(member_dir.join("src/lib.rs"))
                .err()
                .is_none_or(|e| e.kind() != io::ErrorKind::NotFound)
            {
                let (path, _) = validate_real_file(
                    member_dir,
                    member_canon,
                    Path::new("src/lib.rs"),
                    &format!("{member} target lib.path"),
                    phase,
                )?;
                roots.push((path, ModuleDirMode::ParentDir));
            }
        }
    } else if manifest.package.autolib.as_ref().and_then(toml::Value::as_bool) != Some(false) {
        verify_exact_case_path_prefix(
            member_dir,
            Path::new("src/lib.rs"),
            &format!("{member} implicit src/lib.rs"),
            phase,
        )?;
        if fs::symlink_metadata(member_dir.join("src/lib.rs"))
            .err()
            .is_none_or(|e| e.kind() != io::ErrorKind::NotFound)
        {
            let (path, _) = validate_real_file(
                member_dir,
                member_canon,
                Path::new("src/lib.rs"),
                &format!("{member} implicit src/lib.rs"),
                phase,
            )?;
            roots.push((path, ModuleDirMode::ParentDir));
        }
    }

    for (section, dir_name, targets, auto_flag) in [
        ("bin", "src/bin", &manifest.bin, &manifest.package.autobins),
        ("example", "examples", &manifest.example, &manifest.package.autoexamples),
        ("test", "tests", &manifest.test, &manifest.package.autotests),
        ("bench", "benches", &manifest.bench, &manifest.package.autobenches),
    ] {
        let mut explicit_names = BTreeSet::new();
        for target in targets {
            let Some(name) = target.name.as_ref().and_then(toml::Value::as_str) else {
                return Err(Failure::policy(
                    phase,
                    format!("missing or invalid {section}.name in {member}/Cargo.toml"),
                ));
            };
            if !is_single_normal_segment(name) {
                return Err(Failure::policy(
                    phase,
                    format!("invalid {section}.name '{name}' in {member}/Cargo.toml"),
                ));
            }
            explicit_names.insert(name.to_string());
            if target.path.is_some() {
                continue;
            }
            let mut candidates = Vec::new();
            if section == "bin" && name == pkg_name {
                candidates.push("src/main.rs".to_string());
            }
            candidates.push(format!("{dir_name}/{name}.rs"));
            candidates.push(format!("{dir_name}/{name}/main.rs"));
            for rel in &candidates {
                verify_exact_case_path_prefix(
                    member_dir,
                    Path::new(rel),
                    &format!("{member} [[{section}]] '{name}'"),
                    phase,
                )?;
            }
            let existing: Vec<&str> = candidates
                .iter()
                .map(String::as_str)
                .filter(|rel| {
                    fs::symlink_metadata(member_dir.join(rel))
                        .err()
                        .is_none_or(|e| e.kind() != io::ErrorKind::NotFound)
                })
                .collect();
            let rel = match existing.as_slice() {
                [only] => *only,
                // Absent pathless target leaves (matching
                // `validate_relative_path_from_dir`) cannot execute Rust code
                // and are left for downstream phases such as
                // `verify_bundled_resources` to diagnose in their own phase,
                // while broken symlinks or multiple candidates fail here.
                [] => continue,
                _ => {
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "ambiguous source files for pathless [[{section}]] '{name}' in {member}/Cargo.toml"
                        ),
                    ));
                }
            };
            let (path, _) = validate_real_file(
                member_dir,
                member_canon,
                Path::new(rel),
                &format!("{member} [[{section}]] '{name}'"),
                phase,
            )?;
            roots.push((path, ModuleDirMode::ParentDir));
        }

        if auto_flag.as_ref().and_then(toml::Value::as_bool) == Some(false) {
            continue;
        }
        if section == "bin" && !explicit_names.contains(pkg_name) {
            verify_exact_case_path_prefix(
                member_dir,
                Path::new("src/main.rs"),
                &format!("{member} implicit src/main.rs"),
                phase,
            )?;
            if fs::symlink_metadata(member_dir.join("src/main.rs")).is_ok() {
                let (path, _) = validate_real_file(
                    member_dir,
                    member_canon,
                    Path::new("src/main.rs"),
                    &format!("{member} implicit src/main.rs"),
                    phase,
                )?;
                roots.push((path, ModuleDirMode::ParentDir));
            }
        }

        verify_exact_case_path_prefix(
            member_dir,
            Path::new(dir_name),
            &format!("{member}/{dir_name}"),
            phase,
        )?;
        let dir = member_dir.join(dir_name);
        if !fs::symlink_metadata(&dir).map(|m| m.file_type().is_dir()).unwrap_or(false) {
            continue;
        }
        let mut entries: Vec<PathBuf> = fs::read_dir(&dir)
            .map_err(|err| {
                Failure::operational(phase, format!("cannot read {member}/{dir_name}: {err}"))
            })?
            .map(|res| {
                res.map(|e| e.path()).map_err(|err| {
                    Failure::operational(
                        phase,
                        format!("cannot read entry in {member}/{dir_name}: {err}"),
                    )
                })
            })
            .collect::<Result<_, _>>()?;
        entries.sort();
        for path in entries {
            let meta = fs::symlink_metadata(&path).map_err(|err| {
                Failure::operational(phase, format!("cannot inspect {}: {err}", path.display()))
            })?;
            if meta.file_type().is_file()
                && path.extension().and_then(|ext| ext.to_str()) == Some("rs")
            {
                if let Some(stem) = path.file_stem().and_then(|s| s.to_str())
                    && !explicit_names.contains(stem)
                {
                    roots.push((path, ModuleDirMode::ParentDir));
                }
            } else if meta.file_type().is_dir() {
                verify_exact_case_entry(
                    &path,
                    OsStr::new("main.rs"),
                    &format!("{member}/{dir_name}"),
                    phase,
                )?;
                let main_rs = path.join("main.rs");
                if fs::symlink_metadata(&main_rs).map(|m| m.file_type().is_file()).unwrap_or(false)
                    && let Some(stem) = path.file_name().and_then(|s| s.to_str())
                    && !explicit_names.contains(stem)
                {
                    roots.push((main_rs, ModuleDirMode::ParentDir));
                }
            }
        }
    }
    Ok(roots)
}

/// Unstable `#![feature(...)]` gates admitted only in `trusted/rustc-capture`.
///
/// Other trusted workspace members build on stable Rust and admit no
/// `#![feature(...)]` gates. Restricting `rustc_private` to
/// `trusted/rustc-capture` prevents other workspace members from importing
/// toolchain-pinned sysroot crates via `extern crate`, while blocking nightly
/// lexer or macro extensions (such as `frontmatter`, `decl_macro`,
/// `concat_idents`, or `macro_metavar_expr_concat`) across the entire
/// workspace.
const RUSTC_CAPTURE_ALLOWED_FEATURES: &[&str] = &["normalize_lexically", "rustc_private"];

/// Return the closed allowlist of `#![feature(...)]` gates permitted for
/// workspace `member`.
fn allowed_unstable_features(member: &str) -> &'static [&'static str] {
    if member == "trusted/rustc-capture" { RUSTC_CAPTURE_ALLOWED_FEATURES } else { &[] }
}

/// Identifiers for Rust inline-assembly macros forbidden as macro invocations,
/// `use` imports/aliases, and attribute tokens across trusted workspace members.
fn is_disallowed_inline_asm_ident(name: &str) -> bool {
    matches!(name, "global_asm" | "asm" | "naked_asm")
}

/// Identifiers for Rust compile-time file-reading attributes and inline
/// assembly macros (such as `#[debugger_visualizer(gdb_script_file = ...)]`
/// and `global_asm!(".incbin ...")`) forbidden in attributes and `use` items
/// across trusted workspace members.
fn is_disallowed_file_reading_ident(name: &str) -> bool {
    name == "debugger_visualizer" || is_disallowed_inline_asm_ident(name)
}

#[derive(Debug, PartialEq, Eq)]
enum RustToken {
    /// Identifier with any leading `r#` raw-identifier prefix stripped from
    /// `name`, preserving `is_raw` so security denylists match `ident_name()`
    /// (`r#path`, `r#include_str`) while static `cfg` optimization only trusts
    /// `non_raw_ident()` (`true`, `false`, `all`, `any`, `not`, `cfg`,
    /// `cfg_attr`).
    Ident {
        name: String,
        is_raw: bool,
    },
    /// Decoded UTF-8 string literal (`"..."` or `r#*"..."#*`).
    StringLit(String),
    /// Non-string literal (byte/C-string, char/byte literal, number, lifetime).
    OtherLit,
    Pound,
    Bang,
    Eq,
    Comma,
    Semi,
    Colon,
    Dot,
    Amp,
    Dollar,
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    OtherPunct,
}

impl RustToken {
    fn ident_name(&self) -> Option<&str> {
        match self {
            Self::Ident { name, .. } => Some(name.as_str()),
            _ => None,
        }
    }

    fn non_raw_ident(&self) -> Option<&str> {
        match self {
            Self::Ident { name, is_raw: false } => Some(name.as_str()),
            _ => None,
        }
    }
}

fn is_rust_ident_start(ch: char) -> bool {
    ch == '_' || ch.is_ascii_alphabetic()
}

fn is_rust_ident_continue(ch: char) -> bool {
    ch == '_' || ch.is_ascii_alphanumeric()
}

/// If `rest` begins with a raw string opener (`"` or `#+"`), return
/// `(content, total_bytes_consumed)` including the closing `"#*`.
fn lex_raw_string_after_prefix(
    rest: &str,
    display_path: &str,
    phase: &str,
) -> Result<Option<(String, usize)>, Failure> {
    let bytes = rest.as_bytes();
    let hashes = bytes.iter().take_while(|&&b| b == b'#').count();
    if bytes.get(hashes) != Some(&b'"') {
        return Ok(None);
    }
    let content_start = hashes + 1;
    let mut pos = content_start;
    while pos < bytes.len() {
        if bytes[pos] == b'"'
            && pos + 1 + hashes <= bytes.len()
            && bytes[pos + 1..pos + 1 + hashes].iter().all(|&b| b == b'#')
        {
            let content = rest[content_start..pos].to_string();
            return Ok(Some((content, pos + 1 + hashes)));
        }
        pos += 1;
    }
    Err(Failure::policy(
        phase,
        format!("unterminated raw string literal in Rust source {display_path}"),
    ))
}

/// Decode a normal Rust UTF-8 string literal starting at the opening `"` of
/// `rest`, returning `(decoded, total_bytes_consumed)`.
fn lex_utf8_string(
    rest: &str,
    display_path: &str,
    phase: &str,
) -> Result<(String, usize), Failure> {
    let bytes = rest.as_bytes();
    debug_assert_eq!(bytes.first(), Some(&b'"'));
    let mut out = String::new();
    let mut pos = 1;
    while pos < bytes.len() {
        let ch = rest[pos..].chars().next().unwrap();
        pos += ch.len_utf8();
        match ch {
            '"' => return Ok((out, pos)),
            '\\' => {
                if pos >= bytes.len() {
                    return Err(Failure::policy(
                        phase,
                        format!("unterminated string escape in Rust source {display_path}"),
                    ));
                }
                let esc = rest[pos..].chars().next().unwrap();
                pos += esc.len_utf8();
                match esc {
                    '\\' => out.push('\\'),
                    '"' => out.push('"'),
                    '\'' => out.push('\''),
                    'n' => out.push('\n'),
                    'r' => out.push('\r'),
                    't' => out.push('\t'),
                    '0' => out.push('\0'),
                    '\n' => {
                        while let Some(&b) = bytes.get(pos) {
                            if matches!(b, b' ' | b'\t' | b'\n' | b'\r') {
                                pos += 1;
                            } else {
                                break;
                            }
                        }
                    }
                    '\r' if bytes.get(pos) == Some(&b'\n') => {
                        pos += 1;
                        while let Some(&b) = bytes.get(pos) {
                            if matches!(b, b' ' | b'\t' | b'\n' | b'\r') {
                                pos += 1;
                            } else {
                                break;
                            }
                        }
                    }
                    'x' => {
                        let Some(hex_bytes) = bytes.get(pos..pos + 2) else {
                            return Err(Failure::policy(
                                phase,
                                format!("truncated \\x escape in Rust source {display_path}"),
                            ));
                        };
                        if !hex_bytes.iter().all(u8::is_ascii_hexdigit) {
                            return Err(Failure::policy(
                                phase,
                                format!("invalid \\x escape in Rust source {display_path}"),
                            ));
                        }
                        let hex = std::str::from_utf8(hex_bytes).expect("ASCII hex digits");
                        let val = u8::from_str_radix(hex, 16).expect("validated hex digits");
                        if val > 0x7f {
                            return Err(Failure::policy(
                                phase,
                                format!("non-ASCII \\x escape in Rust string {display_path}"),
                            ));
                        }
                        out.push(char::from(val));
                        pos += 2;
                    }
                    'u' => {
                        if bytes.get(pos) != Some(&b'{') {
                            return Err(Failure::policy(
                                phase,
                                format!("malformed \\u escape in Rust source {display_path}"),
                            ));
                        }
                        pos += 1;
                        let start = pos;
                        while pos < bytes.len() && bytes[pos] != b'}' {
                            pos += 1;
                        }
                        if pos >= bytes.len() {
                            return Err(Failure::policy(
                                phase,
                                format!("unterminated \\u escape in Rust source {display_path}"),
                            ));
                        }
                        let raw_hex = &rest[start..pos];
                        pos += 1;
                        let cleaned: String = raw_hex.chars().filter(|&c| c != '_').collect();
                        if raw_hex.starts_with('_') || cleaned.is_empty() || cleaned.len() > 6 {
                            return Err(Failure::policy(
                                phase,
                                format!("invalid \\u escape in Rust source {display_path}"),
                            ));
                        }
                        let code = u32::from_str_radix(&cleaned, 16).map_err(|_| {
                            Failure::policy(
                                phase,
                                format!("invalid \\u hex digits in Rust source {display_path}"),
                            )
                        })?;
                        let decoded = char::from_u32(code).ok_or_else(|| {
                            Failure::policy(
                                phase,
                                format!("invalid Unicode scalar in Rust source {display_path}"),
                            )
                        })?;
                        out.push(decoded);
                    }
                    _ => {
                        return Err(Failure::policy(
                            phase,
                            format!(
                                "unsupported string escape \\{esc} in Rust source {display_path}"
                            ),
                        ));
                    }
                }
            }
            other => out.push(other),
        }
    }
    Err(Failure::policy(
        phase,
        format!("unterminated string literal in Rust source {display_path}"),
    ))
}

/// Consume a quoted byte-string (`b"..."`) or C-string (`c"..."`) starting at
/// the opening `"` of `rest`, returning total bytes consumed.
fn lex_opaque_quoted_string(rest: &str, display_path: &str, phase: &str) -> Result<usize, Failure> {
    let bytes = rest.as_bytes();
    debug_assert_eq!(bytes.first(), Some(&b'"'));
    let mut pos = 1;
    while pos < bytes.len() {
        match bytes[pos] {
            b'"' => return Ok(pos + 1),
            b'\\' => {
                pos += 1;
                if pos >= bytes.len() {
                    return Err(Failure::policy(
                        phase,
                        format!("unterminated byte/C string escape in Rust source {display_path}"),
                    ));
                }
                let ch = rest[pos..].chars().next().unwrap();
                pos += ch.len_utf8();
            }
            _ => {
                let ch = rest[pos..].chars().next().unwrap();
                pos += ch.len_utf8();
            }
        }
    }
    Err(Failure::policy(
        phase,
        format!("unterminated byte/C string literal in Rust source {display_path}"),
    ))
}

/// Consume a char or byte literal starting at the opening `'` of `rest`,
/// returning total bytes consumed.
fn lex_single_quoted_literal(
    rest: &str,
    display_path: &str,
    phase: &str,
) -> Result<usize, Failure> {
    let bytes = rest.as_bytes();
    debug_assert_eq!(bytes.first(), Some(&b'\''));
    let mut pos = 1;
    if pos >= bytes.len() {
        return Err(Failure::policy(
            phase,
            format!("unterminated char/byte literal in Rust source {display_path}"),
        ));
    }
    if bytes[pos] == b'\\' {
        pos += 1;
        if pos >= bytes.len() {
            return Err(Failure::policy(
                phase,
                format!("unterminated char/byte escape in Rust source {display_path}"),
            ));
        }
        let esc = rest[pos..].chars().next().unwrap();
        pos += esc.len_utf8();
        match esc {
            '\\' | '\'' | '"' | 'n' | 'r' | 't' | '0' => {}
            'x' => {
                if pos + 2 > bytes.len() || !bytes[pos..pos + 2].iter().all(u8::is_ascii_hexdigit) {
                    return Err(Failure::policy(
                        phase,
                        format!("invalid \\x char/byte escape in Rust source {display_path}"),
                    ));
                }
                pos += 2;
            }
            'u' => {
                if bytes.get(pos) != Some(&b'{') {
                    return Err(Failure::policy(
                        phase,
                        format!("malformed \\u char escape in Rust source {display_path}"),
                    ));
                }
                pos += 1;
                while pos < bytes.len() && bytes[pos] != b'}' {
                    pos += 1;
                }
                if pos >= bytes.len() {
                    return Err(Failure::policy(
                        phase,
                        format!("unterminated \\u char escape in Rust source {display_path}"),
                    ));
                }
                pos += 1;
            }
            _ => {
                return Err(Failure::policy(
                    phase,
                    format!("unsupported char/byte escape \\{esc} in Rust source {display_path}"),
                ));
            }
        }
        if bytes.get(pos) == Some(&b'\'') {
            return Ok(pos + 1);
        }
        return Err(Failure::policy(
            phase,
            format!("unterminated escaped char/byte literal in Rust source {display_path}"),
        ));
    }
    let ch = rest[pos..].chars().next().unwrap();
    pos += ch.len_utf8();
    if bytes.get(pos) == Some(&b'\'') {
        return Ok(pos + 1);
    }
    Err(Failure::policy(
        phase,
        format!("unterminated char/byte literal in Rust source {display_path}"),
    ))
}

/// Lex a Rust source file into tokens while stripping line and nested block
/// comments, decoding string literals, and distinguishing char/byte literals
/// from lifetimes so string/comment contents cannot mask or forge `#[path]` or
/// `include*!` directives.
fn lex_rust_tokens(src: &str, display_path: &str, phase: &str) -> Result<Vec<RustToken>, Failure> {
    reject_bidi_or_invisible_controls(src, &format!("Rust source {display_path}"), phase)?;
    let trimmed_start = src.trim_start_matches([' ', '\t', '\r', '\n']);
    if trimmed_start.starts_with("#!") && !trimmed_start.starts_with("#![") {
        return Err(Failure::policy(
            phase,
            format!("shebang '#!' forbidden in Rust source {display_path}"),
        ));
    }
    if trimmed_start.starts_with("---") {
        return Err(Failure::policy(
            phase,
            format!("frontmatter '---' forbidden in Rust source {display_path}"),
        ));
    }
    let bytes = src.as_bytes();
    let mut pos = 0;
    let mut tokens = Vec::new();
    while pos < bytes.len() {
        let rest = &src[pos..];
        let b = bytes[pos];
        if b.is_ascii_whitespace() {
            pos += 1;
            continue;
        }
        // Line comment (`//...`).
        if b == b'/' && bytes.get(pos + 1) == Some(&b'/') {
            pos += 2;
            while pos < bytes.len() && bytes[pos] != b'\n' {
                pos += 1;
            }
            continue;
        }
        // Nested block comment (`/* ... */`).
        if b == b'/' && bytes.get(pos + 1) == Some(&b'*') {
            pos += 2;
            let mut depth = 1usize;
            while pos < bytes.len() && depth > 0 {
                if bytes[pos] == b'/' && bytes.get(pos + 1) == Some(&b'*') {
                    depth += 1;
                    pos += 2;
                } else if bytes[pos] == b'*' && bytes.get(pos + 1) == Some(&b'/') {
                    depth -= 1;
                    pos += 2;
                } else {
                    let ch = src[pos..].chars().next().unwrap();
                    pos += ch.len_utf8();
                }
            }
            if depth != 0 {
                return Err(Failure::policy(
                    phase,
                    format!("unterminated block comment in Rust source {display_path}"),
                ));
            }
            continue;
        }
        // Raw byte string (`br#*"..."#*`) or raw C-string (`cr#*"..."#*`).
        if matches!(b, b'b' | b'c')
            && bytes.get(pos + 1) == Some(&b'r')
            && let Some((_, consumed)) =
                lex_raw_string_after_prefix(&src[pos + 2..], display_path, phase)?
        {
            pos += 2 + consumed;
            tokens.push(RustToken::OtherLit);
            continue;
        }
        // Quoted byte string (`b"..."`) or C-string (`c"..."`).
        if matches!(b, b'b' | b'c') && bytes.get(pos + 1) == Some(&b'"') {
            let consumed = lex_opaque_quoted_string(&src[pos + 1..], display_path, phase)?;
            pos += 1 + consumed;
            tokens.push(RustToken::OtherLit);
            continue;
        }
        // Byte literal (`b'...'`).
        if b == b'b' && bytes.get(pos + 1) == Some(&b'\'') {
            let consumed = lex_single_quoted_literal(&src[pos + 1..], display_path, phase)?;
            pos += 1 + consumed;
            tokens.push(RustToken::OtherLit);
            continue;
        }
        // Raw UTF-8 string (`r#*"..."#*`) or raw identifier (`r#ident`).
        if b == b'r' {
            if let Some((content, consumed)) =
                lex_raw_string_after_prefix(&src[pos + 1..], display_path, phase)?
            {
                pos += 1 + consumed;
                tokens.push(RustToken::StringLit(content));
                continue;
            }
            if bytes.get(pos + 1) == Some(&b'#')
                && let Some(first) = src[pos + 2..].chars().next()
                && is_rust_ident_start(first)
            {
                pos += 2;
                let start = pos;
                while let Some(ch) = src[pos..].chars().next() {
                    if is_rust_ident_continue(ch) {
                        pos += ch.len_utf8();
                    } else {
                        break;
                    }
                }
                tokens.push(RustToken::Ident { name: src[start..pos].to_string(), is_raw: true });
                continue;
            }
        }
        // Normal UTF-8 string literal (`"..."`).
        if b == b'"' {
            let (content, consumed) = lex_utf8_string(rest, display_path, phase)?;
            pos += consumed;
            tokens.push(RustToken::StringLit(content));
            continue;
        }
        // Char literal (`'a'`, `'\''`) vs. lifetime / loop label (`'a`,
        // `'r#fn`).
        if b == b'\'' {
            let after_quote = &src[pos + 1..];
            let is_char_lit = if after_quote.starts_with('\\') {
                true
            } else if let Some(ch) = after_quote.chars().next() {
                !matches!(ch, '\'' | '\n' | '\r' | '\t')
                    && after_quote[ch.len_utf8()..].starts_with('\'')
            } else {
                false
            };
            if is_char_lit {
                let consumed = lex_single_quoted_literal(rest, display_path, phase)?;
                pos += consumed;
            } else {
                pos += 1;
                if src[pos..].starts_with("r#") {
                    pos += 2;
                }
                while let Some(ch) = src[pos..].chars().next() {
                    if is_rust_ident_continue(ch) {
                        pos += ch.len_utf8();
                    } else {
                        break;
                    }
                }
            }
            tokens.push(RustToken::OtherLit);
            continue;
        }
        // Numeric literal (consume trailing suffix so `0x10` does not lex as an
        // identifier).
        if b.is_ascii_digit() {
            while pos < bytes.len() && (bytes[pos].is_ascii_alphanumeric() || bytes[pos] == b'_') {
                pos += 1;
            }
            tokens.push(RustToken::OtherLit);
            continue;
        }
        let ch = rest.chars().next().unwrap();
        // Comments, string literals, and char literals have already been
        // consumed above. Fail closed on any remaining non-ASCII character
        // (identifiers, combining marks, lifetimes, or Unicode whitespace) so
        // trusted Rust source cannot rely on Unicode XID/NFC normalization to
        // split `mod` identifiers or smuggle confusable tokens.
        if !ch.is_ascii() {
            return Err(Failure::policy(
                phase,
                format!(
                    "non-ASCII token or identifier forbidden in trusted Rust source {display_path}"
                ),
            ));
        }
        if is_rust_ident_start(ch) {
            let start = pos;
            pos += ch.len_utf8();
            while let Some(next_ch) = src[pos..].chars().next() {
                if is_rust_ident_continue(next_ch) {
                    pos += next_ch.len_utf8();
                } else {
                    break;
                }
            }
            tokens.push(RustToken::Ident { name: src[start..pos].to_string(), is_raw: false });
            continue;
        }
        pos += ch.len_utf8();
        let tok = match ch {
            '#' => RustToken::Pound,
            '!' => RustToken::Bang,
            '=' => RustToken::Eq,
            ',' => RustToken::Comma,
            ';' => RustToken::Semi,
            ':' => RustToken::Colon,
            '.' => RustToken::Dot,
            '&' => RustToken::Amp,
            '$' => RustToken::Dollar,
            '(' => RustToken::LParen,
            ')' => RustToken::RParen,
            '[' => RustToken::LBracket,
            ']' => RustToken::RBracket,
            '{' => RustToken::LBrace,
            '}' => RustToken::RBrace,
            _ => RustToken::OtherPunct,
        };
        tokens.push(tok);
    }
    Ok(tokens)
}

fn find_matching_delim(
    tokens: &[RustToken],
    open_idx: usize,
    open_tok: &RustToken,
    close_tok: &RustToken,
    display_path: &str,
    phase: &str,
) -> Result<usize, Failure> {
    let mut depth = 0usize;
    for (idx, tok) in tokens.iter().enumerate().skip(open_idx) {
        if tok == open_tok {
            depth += 1;
        } else if tok == close_tok {
            depth -= 1;
            if depth == 0 {
                return Ok(idx);
            }
        }
    }
    Err(Failure::policy(phase, format!("unbalanced delimiter in Rust source {display_path}")))
}

/// Bundles the validated workspace-member root and current Rust source path
/// during compiled host-source closure scanning.
struct MemberSourceContext<'a> {
    member: &'a str,
    member_dir: &'a Path,
    member_canon: &'a Path,
    source_file: &'a Path,
    dir_mode: ModuleDirMode,
    display_path: &'a str,
}

impl MemberSourceContext<'_> {
    fn source_parent_dir(&self) -> Result<&Path, Failure> {
        self.source_file.parent().ok_or_else(|| {
            Failure::operational(
                "cargo-boundary",
                format!("source file has no parent directory: {}", self.source_file.display()),
            )
        })
    }

    fn module_base_dir(&self) -> Result<PathBuf, Failure> {
        let parent = self.source_parent_dir()?;
        match self.dir_mode {
            ModuleDirMode::ParentDir => Ok(parent.to_path_buf()),
            ModuleDirMode::StemSubdir => {
                let stem = self.source_file.file_stem().ok_or_else(|| {
                    Failure::operational(
                        "cargo-boundary",
                        format!("source file has no file stem: {}", self.source_file.display()),
                    )
                })?;
                Ok(parent.join(stem))
            }
        }
    }
}

/// Return true when `rel_str` begins with `/`, contains `:` (Windows drive
/// prefixes `C:...` or NTFS alternate data streams `::$DATA`), contains `~`
/// (Windows 8.3 short-name aliases such as `PAYLOA~1.RS`), contains a Windows
/// backslash separator (`\`), or contains a component with a trailing `.` or
/// `' '` (which Windows strips to alias sibling files/directories).
fn has_non_portable_path_syntax(rel_str: &str) -> bool {
    rel_str.starts_with('/')
        || rel_str.contains('\\')
        || rel_str.contains(':')
        || rel_str.contains('~')
        || rel_str.split('/').any(|seg| {
            !matches!(seg, "" | "." | "..") && (seg.ends_with('.') || seg.ends_with(' '))
        })
}

/// Reject empty, NUL, trailing-slash, leading-slash, backslash (`\`), Windows
/// drive-prefix (`C:...`), or Windows trailing-dot/space-aliased component
/// relative path strings before calling `Path::new` so Windows-style aliases
/// and separators fail closed even when auditing on Unix.
fn validate_portable_relative_path_syntax(
    rel_str: &str,
    label: &str,
    display_path: &str,
    phase: &str,
) -> Result<(), Failure> {
    if rel_str.is_empty()
        || rel_str.contains('\0')
        || rel_str.ends_with('/')
        || rel_str.ends_with('\\')
    {
        return Err(Failure::policy(
            phase,
            format!("{label} in {display_path} has empty, trailing-slash, or NUL path"),
        ));
    }
    if has_non_portable_path_syntax(rel_str) {
        return Err(Failure::policy(
            phase,
            format!(
                "{label} in {display_path} escapes member directory or uses non-portable Windows path syntax: {rel_str}"
            ),
        ));
    }
    Ok(())
}

/// Validate a file path relative to `base_dir` (`expect_dir = false`),
/// returning `Ok(None)` when the leaf file does not exist inside
/// `ctx.member_dir`.
fn validate_relative_path_from_dir(
    ctx: &MemberSourceContext<'_>,
    base_dir: &Path,
    rel_str: &str,
    label: &str,
) -> Result<Option<PathBuf>, Failure> {
    validate_relative_path_from_dir_impl(ctx, base_dir, rel_str, label, false)
}

/// Validate an inline `#[path = "..."] mod name { ... }` directory relative to
/// `base_dir`, rejecting symlinks, non-directories, Windows alias components,
/// and member escapes while returning the validated directory path (even when
/// absent on disk so nested relative `#[path]` / `mod` checks keep the full
/// directory stack).
fn validate_relative_dir_from_dir(
    ctx: &MemberSourceContext<'_>,
    base_dir: &Path,
    rel_str: &str,
    label: &str,
) -> Result<PathBuf, Failure> {
    validate_relative_path_from_dir_impl(ctx, base_dir, rel_str, label, true)
        .map(|resolved| resolved.expect("expect_dir = true always returns resolved path"))
}

/// Resolve a relative path string `rel_str` against `base_dir` (which must lie
/// inside `ctx.member_dir`), requiring the path to stay strictly inside
/// `ctx.member_dir` at every step without traversing symlinks, hard links, or
/// non-directory ancestors.
///
/// When `expect_dir` is `false`, missing leaf files inside `ctx.member_dir` are
/// accepted (returning `Ok(None)`) so downstream checks such as
/// `verify_bundled_resources` report missing generated files in their own phase;
/// when `expect_dir` is `true`, every existing directory component (including the
/// leaf) must be a non-symlink directory inside `ctx.member_canon` and the
/// resolved in-member `PathBuf` is returned even if the leaf directory is
/// absent.
fn validate_relative_path_from_dir_impl(
    ctx: &MemberSourceContext<'_>,
    base_dir: &Path,
    rel_str: &str,
    label: &str,
    expect_dir: bool,
) -> Result<Option<PathBuf>, Failure> {
    let phase = "cargo-boundary";
    let display_path = ctx.display_path;
    validate_portable_relative_path_syntax(rel_str, label, display_path, phase)?;
    let rel_path = Path::new(rel_str);

    let base_dir_rel = base_dir.strip_prefix(ctx.member_dir).map_err(|_| {
        Failure::policy(
            phase,
            format!(
                "source directory escapes workspace member {}: {}",
                ctx.member,
                base_dir.display()
            ),
        )
    })?;
    verify_exact_case_path_prefix(
        ctx.member_dir,
        base_dir_rel,
        &format!("{label} in {display_path}"),
        phase,
    )?;

    let mut stack: Vec<OsString> = base_dir_rel
        .components()
        .map(|c| match c {
            Component::Normal(seg) => Ok(seg.to_os_string()),
            _ => Err(Failure::policy(
                phase,
                format!("unexpected source directory component in {}", ctx.member),
            )),
        })
        .collect::<Result<_, _>>()?;

    let components: Vec<Component<'_>> = rel_path.components().collect();
    if components.is_empty() {
        return Err(Failure::policy(phase, format!("{label} in {display_path} has empty path")));
    }

    let mut saw_missing_dir = false;
    for (idx, component) in components.iter().enumerate() {
        let is_last = idx + 1 == components.len();
        match component {
            Component::Prefix(_) | Component::RootDir => {
                return Err(Failure::policy(
                    phase,
                    format!("{label} in {display_path} escapes member directory: {rel_str}"),
                ));
            }
            Component::CurDir => continue,
            Component::ParentDir => {
                if saw_missing_dir || stack.pop().is_none() {
                    return Err(Failure::policy(
                        phase,
                        format!("{label} in {display_path} escapes member directory: {rel_str}"),
                    ));
                }
                let cur = stack.iter().fold(ctx.member_dir.to_path_buf(), |mut acc, seg| {
                    acc.push(seg);
                    acc
                });
                match fs::symlink_metadata(&cur) {
                    Ok(meta) if !meta.file_type().is_symlink() && meta.file_type().is_dir() => {}
                    Ok(_) => {
                        return Err(Failure::policy(
                            phase,
                            format!(
                                "{label} in {display_path} traverses non-directory or symlink: {rel_str}"
                            ),
                        ));
                    }
                    Err(err) if err.kind() == io::ErrorKind::NotFound => {}
                    Err(err) => {
                        return Err(Failure::operational(
                            phase,
                            format!("cannot inspect {}: {err}", cur.display()),
                        ));
                    }
                }
            }
            Component::Normal(seg) => {
                let parent_dir = stack.iter().fold(ctx.member_dir.to_path_buf(), |mut acc, s| {
                    acc.push(s);
                    acc
                });
                verify_exact_case_entry(
                    &parent_dir,
                    seg,
                    &format!("{label} in {display_path}"),
                    phase,
                )?;
                stack.push((*seg).to_os_string());
                let cur = stack.iter().fold(ctx.member_dir.to_path_buf(), |mut acc, s| {
                    acc.push(s);
                    acc
                });
                if expect_dir || !is_last {
                    match fs::symlink_metadata(&cur) {
                        Ok(meta) if !meta.file_type().is_symlink() && meta.file_type().is_dir() => {
                        }
                        Ok(_) => {
                            return Err(Failure::policy(
                                phase,
                                format!(
                                    "{label} in {display_path} traverses symlink or non-directory: {rel_str}"
                                ),
                            ));
                        }
                        Err(err) if err.kind() == io::ErrorKind::NotFound => {
                            saw_missing_dir = true;
                        }
                        Err(err) => {
                            return Err(Failure::operational(
                                phase,
                                format!("cannot inspect {}: {err}", cur.display()),
                            ));
                        }
                    }
                }
            }
        }
    }

    if stack.is_empty() && !expect_dir {
        return Err(Failure::policy(
            phase,
            format!(
                "{label} in {display_path} must name a regular file inside the member: {rel_str}"
            ),
        ));
    }
    let resolved = stack.iter().fold(ctx.member_dir.to_path_buf(), |mut acc, seg| {
        acc.push(seg);
        acc
    });
    if expect_dir {
        if let Ok(meta) = fs::symlink_metadata(&resolved)
            && !meta.file_type().is_symlink()
            && meta.file_type().is_dir()
        {
            let canon = fs::canonicalize(&resolved).map_err(|err| {
                Failure::operational(
                    phase,
                    format!("cannot canonicalize {}: {err}", resolved.display()),
                )
            })?;
            if !canon.starts_with(ctx.member_canon) {
                return Err(Failure::policy(
                    phase,
                    format!("{label} in {display_path} escapes member directory: {rel_str}"),
                ));
            }
        }
        return Ok(Some(resolved));
    }
    match fs::symlink_metadata(&resolved) {
        Ok(meta) => {
            check_single_link_regular_meta(
                &resolved,
                &meta,
                &format!("{label} in {display_path}"),
                phase,
            )?;
            let canon = fs::canonicalize(&resolved).map_err(|err| {
                Failure::operational(
                    phase,
                    format!("cannot canonicalize {}: {err}", resolved.display()),
                )
            })?;
            if !canon.starts_with(ctx.member_canon) {
                return Err(Failure::policy(
                    phase,
                    format!("{label} in {display_path} escapes member directory: {rel_str}"),
                ));
            }
            Ok(Some(resolved))
        }
        Err(err) if err.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(err) => Err(Failure::operational(
            phase,
            format!("cannot inspect {}: {err}", resolved.display()),
        )),
    }
}

/// Resolve a relative path string from `include*!` or `exocrate::config!`
/// against `ctx.source_file.parent()`.
fn validate_source_relative_path(
    ctx: &MemberSourceContext<'_>,
    rel_str: &str,
    label: &str,
) -> Result<Option<PathBuf>, Failure> {
    let source_dir = ctx.source_parent_dir()?;
    validate_relative_path_from_dir(ctx, source_dir, rel_str, label)
}

/// Validate a single `include!`, `include_str!`, or `include_bytes!` token
/// starting at `idx`, returning the index immediately after its closing
/// delimiter.
fn validate_include_token(
    ctx: &MemberSourceContext<'_>,
    tokens: &[RustToken],
    idx: usize,
    macro_name: &str,
    worklist: &mut VecDeque<(PathBuf, ModuleDirMode)>,
) -> Result<usize, Failure> {
    let phase = "cargo-boundary";
    let display_path = ctx.display_path;
    let Some(RustToken::Bang) = tokens.get(idx + 1) else {
        return Err(Failure::policy(
            phase,
            format!("disallowed non-invocation reference to {macro_name} in {display_path}"),
        ));
    };
    let (open_tok, close_tok) = match tokens.get(idx + 2) {
        Some(RustToken::LParen) => (&RustToken::LParen, &RustToken::RParen),
        Some(RustToken::LBracket) => (&RustToken::LBracket, &RustToken::RBracket),
        Some(RustToken::LBrace) => (&RustToken::LBrace, &RustToken::RBrace),
        _ => {
            return Err(Failure::policy(
                phase,
                format!("malformed {macro_name}! invocation in {display_path}"),
            ));
        }
    };
    let close = find_matching_delim(tokens, idx + 2, open_tok, close_tok, display_path, phase)?;
    let args = &tokens[idx + 3..close];
    let rel_target = match args {
        [RustToken::StringLit(s)] | [RustToken::StringLit(s), RustToken::Comma] => s.as_str(),
        _ => {
            return Err(Failure::policy(
                phase,
                format!("{macro_name}! in {display_path} must take a single string literal path"),
            ));
        }
    };
    let is_source_include = macro_name == "include";
    let resolved = validate_source_relative_path(ctx, rel_target, &format!("Rust {macro_name}!"))?;
    if is_source_include && let Some(path) = resolved {
        worklist.push_back((path, ModuleDirMode::ParentDir));
    }
    Ok(close + 1)
}

/// Confirm that the tokens immediately following a `#[path = "..."]` attribute
/// (after any sibling outer attributes and optional `pub` visibility) declare a
/// `mod <ident>;` or inline `mod <ident> { ... }` item, returning the token
/// index of its `mod` keyword when matched.
fn follows_mod_decl(
    tokens: &[RustToken],
    start: usize,
    display_path: &str,
    phase: &str,
) -> Result<Option<usize>, Failure> {
    let mut j = start;
    while tokens.get(j) == Some(&RustToken::Pound)
        && tokens.get(j + 1) == Some(&RustToken::LBracket)
    {
        let end = find_matching_delim(
            tokens,
            j + 1,
            &RustToken::LBracket,
            &RustToken::RBracket,
            display_path,
            phase,
        )?;
        j = end + 1;
    }
    if tokens.get(j).and_then(RustToken::ident_name) == Some("pub") {
        j += 1;
        if tokens.get(j) == Some(&RustToken::LParen) {
            let end = find_matching_delim(
                tokens,
                j,
                &RustToken::LParen,
                &RustToken::RParen,
                display_path,
                phase,
            )?;
            j = end + 1;
        }
    }
    if matches!(
        tokens.get(j),
        Some(RustToken::Ident {
            name,
            is_raw: false,
        }) if name == "mod"
    ) && tokens.get(j + 1).and_then(RustToken::ident_name).is_some()
        && matches!(tokens.get(j + 2), Some(RustToken::Semi | RustToken::LBrace))
    {
        Ok(Some(j))
    } else {
        Ok(None)
    }
}

#[derive(Clone, Debug)]
enum InlineModDir {
    Name(String),
    PathOverride(Vec<PathBuf>),
}

/// Resolve the active directory candidates for modules declared at the current
/// inline module scope. When `for_path_attr` is `true` at file top level,
/// `#[path = "..."]` starts from `ctx.source_parent_dir()` even for `ParentDir`
/// module stems; nested scopes start from the nearest enclosing
/// [`InlineModDir::PathOverride`] (or the owning top-level base) and append any
/// subsequent plain inline module names.
fn resolve_current_mod_dirs(
    ctx: &MemberSourceContext<'_>,
    inline_mod_stack: &[InlineModDir],
    ownership: StemOwnership,
    for_path_attr: bool,
) -> Result<Vec<PathBuf>, Failure> {
    let last_override =
        inline_mod_stack.iter().rposition(|frame| matches!(frame, InlineModDir::PathOverride(_)));
    let (mut dirs, tail): (Vec<PathBuf>, &[InlineModDir]) = match last_override {
        Some(idx) => {
            let InlineModDir::PathOverride(override_dirs) = &inline_mod_stack[idx] else {
                unreachable!("checked PathOverride above");
            };
            (override_dirs.clone(), &inline_mod_stack[idx + 1..])
        }
        None if inline_mod_stack.is_empty() => {
            let root_dir = if for_path_attr {
                ctx.source_parent_dir()?.to_path_buf()
            } else {
                ctx.module_base_dir()?
            };
            (vec![root_dir], inline_mod_stack)
        }
        None => {
            let base_dirs = match ownership {
                StemOwnership::OwnedRelative | StemOwnership::ConsumedIntoBase => {
                    vec![ctx.module_base_dir()?]
                }
                StemOwnership::DisownedByBlock => vec![ctx.source_parent_dir()?.to_path_buf()],
                StemOwnership::AmbiguousInMacro => {
                    let parent = ctx.source_parent_dir()?.to_path_buf();
                    let base = ctx.module_base_dir()?;
                    if parent == base { vec![parent] } else { vec![parent, base] }
                }
            };
            (base_dirs, inline_mod_stack)
        }
    };
    for frame in tail {
        let InlineModDir::Name(seg) = frame else {
            unreachable!("split at last PathOverride above");
        };
        for dir in &mut dirs {
            dir.push(seg);
        }
    }
    Ok(dirs)
}

/// Resolve an out-of-line `mod <mod_name>;` declaration without `#[path]`
/// against the active module directory candidates for the current inline module
/// scope, validating and enqueuing any existing `<name>.rs` or `<name>/mod.rs`
/// file.
fn enqueue_out_of_line_module(
    ctx: &MemberSourceContext<'_>,
    inline_mod_stack: &[InlineModDir],
    ownership: StemOwnership,
    mod_name: &str,
    worklist: &mut VecDeque<(PathBuf, ModuleDirMode)>,
) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    for search_dir in resolve_current_mod_dirs(ctx, inline_mod_stack, ownership, false)? {
        let search_rel = search_dir.strip_prefix(ctx.member_dir).map_err(|_| {
            Failure::policy(
                phase,
                format!(
                    "module search directory escapes workspace member {}: {}",
                    ctx.member,
                    search_dir.display()
                ),
            )
        })?;

        let file_name = format!("{mod_name}.rs");
        let mod_label = format!("Rust module '{mod_name}' declared in {}", ctx.display_path);
        verify_exact_case_path_prefix(ctx.member_dir, search_rel, &mod_label, phase)?;
        verify_exact_case_entry(&search_dir, OsStr::new(&file_name), &mod_label, phase)?;
        let file_rel = search_rel.join(&file_name);
        let file_path = ctx.member_dir.join(&file_rel);
        if fs::symlink_metadata(&file_path).is_ok() {
            let (validated, _) =
                validate_real_file(ctx.member_dir, ctx.member_canon, &file_rel, &mod_label, phase)?;
            worklist.push_back((validated, ModuleDirMode::StemSubdir));
        }

        verify_exact_case_entry(&search_dir, OsStr::new(mod_name), &mod_label, phase)?;
        verify_exact_case_entry(
            &search_dir.join(mod_name),
            OsStr::new("mod.rs"),
            &mod_label,
            phase,
        )?;
        let mod_rs_rel = search_rel.join(mod_name).join("mod.rs");
        let mod_rs_path = ctx.member_dir.join(&mod_rs_rel);
        if fs::symlink_metadata(&mod_rs_path).is_ok() {
            let (validated, _) = validate_real_file(
                ctx.member_dir,
                ctx.member_canon,
                &mod_rs_rel,
                &mod_label,
                phase,
            )?;
            worklist.push_back((validated, ModuleDirMode::ParentDir));
        }
    }
    Ok(())
}

/// How `rustc` (Rust 2024) `DirOwnership` of a `ModuleDirMode::StemSubdir`
/// file (`foo.rs`) behaves across inline `mod` items, non-module `{ ... }`
/// blocks, and macro invocations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum StemOwnership {
    /// File top level (outside any `{ ... }` block or macro invocation):
    /// entering an inline `mod` transitions to `ConsumedIntoBase`, a real
    /// `{ ... }` block transitions to `DisownedByBlock`, and a macro
    /// invocation enters `AmbiguousInMacro`.
    OwnedRelative,
    /// Inside a top-level inline `mod <name> { ... }`: `rustc` consumed the
    /// file stem into `module_base_dir()`, even across nested blocks or macros.
    ConsumedIntoBase,
    /// Inside a non-module `{ ... }` block (`fn`, `const`, etc.) entered
    /// while `OwnedRelative`: `rustc` dropped the stem (`UnownedViaBlock`) even
    /// across inline `mod`s or macros inside that block.
    DisownedByBlock,
    /// Inside a macro-invocation token tree entered while `OwnedRelative`: the
    /// macro may expand items at module level (e.g. `cfg_if!`) or wrap them in
    /// a block, so `#[path]` inside inline `mod`s scans both
    /// `source_parent_dir()` and `module_base_dir()`.
    AmbiguousInMacro,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RustDelim {
    Brace,
    Paren,
    Bracket,
}

impl RustDelim {
    fn from_open(tok: &RustToken) -> Option<Self> {
        match tok {
            RustToken::LBrace => Some(Self::Brace),
            RustToken::LParen => Some(Self::Paren),
            RustToken::LBracket => Some(Self::Bracket),
            _ => None,
        }
    }

    fn from_close(tok: &RustToken) -> Option<Self> {
        match tok {
            RustToken::RBrace => Some(Self::Brace),
            RustToken::RParen => Some(Self::Paren),
            RustToken::RBracket => Some(Self::Bracket),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct DelimFrame {
    open: RustDelim,
    inline_mod: bool,
    in_macro: bool,
    prev_ownership: StemOwnership,
}

/// Mutable state threaded through a single token-slice scan.
struct PendingPathSpec {
    base_dirs: Vec<PathBuf>,
    rel_target: String,
}

fn resolve_pending_path_specs(
    ctx: &MemberSourceContext<'_>,
    specs: Vec<PendingPathSpec>,
    worklist: &mut VecDeque<(PathBuf, ModuleDirMode)>,
) -> Result<(), Failure> {
    for spec in specs {
        for base_dir in spec.base_dirs {
            if let Some(resolved) =
                validate_relative_path_from_dir(ctx, &base_dir, &spec.rel_target, "Rust #[path]")?
            {
                worklist.push_back((resolved, ModuleDirMode::ParentDir));
            }
        }
    }
    Ok(())
}

fn resolve_pending_inline_path_dirs(
    ctx: &MemberSourceContext<'_>,
    specs: Vec<PendingPathSpec>,
) -> Result<Vec<PathBuf>, Failure> {
    let mut dirs = Vec::new();
    for spec in specs {
        for base_dir in spec.base_dirs {
            let dir =
                validate_relative_dir_from_dir(ctx, &base_dir, &spec.rel_target, "Rust #[path]")?;
            if !dirs.contains(&dir) {
                dirs.push(dir);
            }
        }
    }
    Ok(dirs)
}

struct SliceScanState<'a> {
    worklist: &'a mut VecDeque<(PathBuf, ModuleDirMode)>,
    inline_mod_stack: &'a mut Vec<InlineModDir>,
    delim_stack: Vec<DelimFrame>,
    ownership: StemOwnership,
    in_macro_base: bool,
    path_annotated_mods: BTreeSet<usize>,
    pending_path_targets: BTreeMap<usize, Vec<PendingPathSpec>>,
    pending_item_cfg_disabled: bool,
}

impl SliceScanState<'_> {
    fn in_macro(&self) -> bool {
        self.in_macro_base || self.delim_stack.iter().any(|frame| frame.in_macro)
    }
}

fn macro_invocation_open_idx(tokens: &[RustToken], idx: usize) -> Option<(usize, RustDelim)> {
    if tokens.get(idx).and_then(RustToken::ident_name).is_none()
        || tokens.get(idx + 1) != Some(&RustToken::Bang)
    {
        return None;
    }
    if let Some(delim) = tokens.get(idx + 2).and_then(RustDelim::from_open) {
        return Some((idx + 2, delim));
    }
    if tokens.get(idx + 2).and_then(RustToken::ident_name).is_some()
        && let Some(delim) = tokens.get(idx + 3).and_then(RustDelim::from_open)
    {
        return Some((idx + 3, delim));
    }
    None
}

/// Validate a comma-separated `#![feature(...)]` argument list against
/// [`allowed_unstable_features`] for `ctx.member`, rejecting empty lists,
/// non-identifier tokens, and any unstable feature outside the member's closed
/// allowlist.
fn validate_feature_allowlist(
    ctx: &MemberSourceContext<'_>,
    items: &[RustToken],
    phase: &str,
) -> Result<(), Failure> {
    let display_path = ctx.display_path;
    let allowed = allowed_unstable_features(ctx.member);
    if items.is_empty() {
        return Err(Failure::policy(
            phase,
            format!("empty feature(...) attribute in {display_path}"),
        ));
    }
    let mut i = 0;
    while i < items.len() {
        let Some(feat) = items[i].ident_name() else {
            return Err(Failure::policy(
                phase,
                format!("malformed feature(...) attribute in {display_path}"),
            ));
        };
        if !allowed.contains(&feat) {
            return Err(Failure::policy(
                phase,
                format!(
                    "disallowed unstable feature({feat}) in {display_path} (member {})",
                    ctx.member
                ),
            ));
        }
        i += 1;
        if i < items.len() {
            if items[i] != RustToken::Comma {
                return Err(Failure::policy(
                    phase,
                    format!("malformed feature(...) attribute in {display_path}"),
                ));
            }
            i += 1;
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum StaticCfg {
    AlwaysTrue,
    AlwaysFalse,
    Unknown,
}

fn delim_spans_full_slice(tokens: &[RustToken], open: &RustToken, close: &RustToken) -> bool {
    if tokens.first() != Some(open) || tokens.last() != Some(close) {
        return false;
    }
    let mut depth = 0usize;
    for (i, tok) in tokens.iter().enumerate() {
        if tok == open {
            depth += 1;
        } else if tok == close {
            depth -= 1;
            if depth == 0 {
                return i + 1 == tokens.len();
            }
        }
    }
    false
}

/// Split `tokens` at top-level commas (outside balanced `()`, `[]`, and `{}`
/// groups), returning `None` if delimiters are unbalanced or any non-trailing
/// item is empty.
fn split_top_level_comma_items(
    tokens: &[RustToken],
    allow_trailing_comma: bool,
) -> Option<Vec<&[RustToken]>> {
    if tokens.is_empty() {
        return Some(Vec::new());
    }
    let mut items = Vec::new();
    let mut stack: Vec<RustDelim> = Vec::new();
    let mut start = 0usize;
    for (i, tok) in tokens.iter().enumerate() {
        if let Some(open) = RustDelim::from_open(tok) {
            stack.push(open);
        } else if let Some(close) = RustDelim::from_close(tok) {
            if stack.pop() != Some(close) {
                return None;
            }
        } else if *tok == RustToken::Comma && stack.is_empty() {
            if i == start {
                return None;
            }
            items.push(&tokens[start..i]);
            start = i + 1;
        }
    }
    if !stack.is_empty() {
        return None;
    }
    if start < tokens.len() {
        items.push(&tokens[start..]);
    } else if !allow_trailing_comma {
        return None;
    }
    Some(items)
}

/// Conservatively evaluate a `#[cfg(...)]` or `#[cfg_attr(...)]` predicate in
/// Kleene three-valued logic over non-raw `true`, `false`, `all(...)`,
/// `any(...)`, and `not(...)`, failing closed to [`StaticCfg::Unknown`] on any
/// raw identifier (`r#true`, `r#false`, ...), platform/feature option, or
/// malformed predicate.
fn eval_static_cfg_predicate(tokens: &[RustToken]) -> StaticCfg {
    match tokens {
        [tok] if tok.non_raw_ident() == Some("true") => StaticCfg::AlwaysTrue,
        [tok] if tok.non_raw_ident() == Some("false") => StaticCfg::AlwaysFalse,
        [head, RustToken::LParen, .., RustToken::RParen]
            if matches!(head.non_raw_ident(), Some("all" | "any" | "not")) =>
        {
            if !delim_spans_full_slice(&tokens[1..], &RustToken::LParen, &RustToken::RParen) {
                return StaticCfg::Unknown;
            }
            let name = head.non_raw_ident().expect("checked above");
            let inner = &tokens[2..tokens.len() - 1];
            match name {
                "all" => {
                    let Some(items) = split_top_level_comma_items(inner, true) else {
                        return StaticCfg::Unknown;
                    };
                    let mut all_true = true;
                    for item in items {
                        match eval_static_cfg_predicate(item) {
                            StaticCfg::AlwaysFalse => return StaticCfg::AlwaysFalse,
                            StaticCfg::Unknown => all_true = false,
                            StaticCfg::AlwaysTrue => {}
                        }
                    }
                    if all_true { StaticCfg::AlwaysTrue } else { StaticCfg::Unknown }
                }
                "any" => {
                    let Some(items) = split_top_level_comma_items(inner, true) else {
                        return StaticCfg::Unknown;
                    };
                    let mut all_false = true;
                    for item in items {
                        match eval_static_cfg_predicate(item) {
                            StaticCfg::AlwaysTrue => return StaticCfg::AlwaysTrue,
                            StaticCfg::Unknown => all_false = false,
                            StaticCfg::AlwaysFalse => {}
                        }
                    }
                    if all_false { StaticCfg::AlwaysFalse } else { StaticCfg::Unknown }
                }
                "not" => {
                    let Some(items) = split_top_level_comma_items(inner, false) else {
                        return StaticCfg::Unknown;
                    };
                    let [pred] = items.as_slice() else {
                        return StaticCfg::Unknown;
                    };
                    match eval_static_cfg_predicate(pred) {
                        StaticCfg::AlwaysTrue => StaticCfg::AlwaysFalse,
                        StaticCfg::AlwaysFalse => StaticCfg::AlwaysTrue,
                        StaticCfg::Unknown => StaticCfg::Unknown,
                    }
                }
                _ => unreachable!(),
            }
        }
        _ => StaticCfg::Unknown,
    }
}

/// Extract the leading attribute path (`[::] ident (:: ident)*`, recording each
/// segment's `is_raw` bit) and the trailing token slice after that path.
fn split_attribute_head(attr: &[RustToken]) -> (Vec<(&str, bool)>, &[RustToken]) {
    let mut pos = 0;
    if attr.get(pos) == Some(&RustToken::Colon) && attr.get(pos + 1) == Some(&RustToken::Colon) {
        pos += 2;
    }
    let Some(RustToken::Ident { name: first, is_raw: first_raw }) = attr.get(pos) else {
        return (Vec::new(), attr);
    };
    let mut segments = vec![(first.as_str(), *first_raw)];
    pos += 1;
    while attr.get(pos) == Some(&RustToken::Colon)
        && attr.get(pos + 1) == Some(&RustToken::Colon)
        && let Some(RustToken::Ident { name: next, is_raw: next_raw }) = attr.get(pos + 2)
    {
        segments.push((next.as_str(), *next_raw));
        pos += 3;
    }
    (segments, &attr[pos..])
}

/// Scan an attribute token slice for forbidden constructs (`$`, `#`,
/// `crate_type`, `macro_export`, file-reading attributes/macros, `feature(...)`
/// outside allowlist, `include*!`), without treating `path` identifiers inside
/// arguments or cfg predicates as `#[path]` attributes.
fn validate_attr_tokens_non_path(
    ctx: &MemberSourceContext<'_>,
    attr: &[RustToken],
    state: &mut SliceScanState<'_>,
) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    let display_path = ctx.display_path;
    let mut idx = 0;
    while idx < attr.len() {
        match &attr[idx] {
            RustToken::Dollar => {
                return Err(Failure::policy(
                    phase,
                    format!("metavariable '$' forbidden inside attribute in {display_path}"),
                ));
            }
            RustToken::Pound => {
                return Err(Failure::policy(
                    phase,
                    format!("nested '#' forbidden inside attribute in {display_path}"),
                ));
            }
            RustToken::Ident { name, .. } if name == "crate_type" => {
                return Err(Failure::policy(
                    phase,
                    format!("disallowed crate_type attribute in {display_path}"),
                ));
            }
            RustToken::Ident { name, .. } if name == "macro_export" => {
                return Err(Failure::policy(
                    phase,
                    format!("disallowed macro_export attribute in {display_path}"),
                ));
            }
            RustToken::Ident { name, .. } if is_disallowed_file_reading_ident(name) => {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "disallowed compile-time file-reading construct '{name}' in {display_path}"
                    ),
                ));
            }
            RustToken::Ident { name, .. } if matches!(name.as_str(), "macro_rules" | "macro") => {
                return Err(Failure::policy(
                    phase,
                    format!("disallowed macro keyword '{name}' inside attribute in {display_path}"),
                ));
            }
            RustToken::Ident { name, .. }
                if matches!(name.as_str(), "toml_const" | "macro_util") =>
            {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "disallowed exocrate internal macro reference '{name}' in {display_path}"
                    ),
                ));
            }
            RustToken::Ident { name, .. }
                if matches!(name.as_str(), "config" | "parse_remote_archive")
                    && attr.get(idx + 1) == Some(&RustToken::Bang) =>
            {
                return Err(Failure::policy(
                    phase,
                    format!("disallowed {name}! macro inside attribute in {display_path}"),
                ));
            }
            RustToken::Ident { name, .. }
                if name == "feature" && attr.get(idx + 1) == Some(&RustToken::LParen) =>
            {
                let end = find_matching_delim(
                    attr,
                    idx + 1,
                    &RustToken::LParen,
                    &RustToken::RParen,
                    display_path,
                    phase,
                )?;
                validate_feature_allowlist(ctx, &attr[idx + 2..end], phase)?;
            }
            RustToken::Ident { name, .. }
                if matches!(name.as_str(), "include" | "include_str" | "include_bytes") =>
            {
                idx = validate_include_token(ctx, attr, idx, name, state.worklist)?;
                continue;
            }
            _ => {}
        }
        idx += 1;
    }
    Ok(())
}

#[derive(Clone, Copy)]
struct AttrContext {
    is_inner: bool,
    close_bracket: usize,
    in_cfg_attr: bool,
    can_disable_item: bool,
}

/// Enforce the literal outer `#[path = "..."] mod <name>;` contract,
/// queuing resolved paths in `state.pending_path_targets` keyed by
/// `mod_kw_idx` so a sibling `#[cfg(AlwaysFalse)]` drops them at `mod`.
fn handle_path_attribute(
    ctx: &MemberSourceContext<'_>,
    tokens: &[RustToken],
    attr_ctx: AttrContext,
    attr: &[RustToken],
    state: &mut SliceScanState<'_>,
) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    let display_path = ctx.display_path;
    if attr_ctx.is_inner {
        return Err(Failure::policy(
            phase,
            format!("inner #![path] attribute forbidden in {display_path}"),
        ));
    }
    if attr_ctx.in_cfg_attr {
        return Err(Failure::policy(
            phase,
            format!("unsupported or non-literal path attribute in {display_path}"),
        ));
    }
    let rel_target = match attr {
        [tok, RustToken::Eq, RustToken::StringLit(s)] if tok.ident_name() == Some("path") => {
            s.as_str()
        }
        _ => {
            return Err(Failure::policy(
                phase,
                format!("unsupported or non-literal path attribute in {display_path}"),
            ));
        }
    };
    let Some(mod_kw_idx) =
        follows_mod_decl(tokens, attr_ctx.close_bracket + 1, display_path, phase)?
    else {
        return Err(Failure::policy(
            phase,
            format!(
                "#[path] attribute is permitted only on 'mod <name>' declarations in {display_path}"
            ),
        ));
    };
    state.path_annotated_mods.insert(mod_kw_idx);
    let resolved_base_dirs =
        resolve_current_mod_dirs(ctx, state.inline_mod_stack, state.ownership, true)?;
    state.pending_path_targets.entry(mod_kw_idx).or_default().push(PendingPathSpec {
        base_dirs: resolved_base_dirs,
        rel_target: rel_target.to_string(),
    });
    Ok(())
}

/// Dispatch an attribute body structurally by its head path (`path`, `cfg`,
/// `cfg_attr`, or general attribute) while validating nested `cfg_attr` inner
/// attributes recursively.
fn inspect_attribute_body(
    ctx: &MemberSourceContext<'_>,
    tokens: &[RustToken],
    attr_ctx: AttrContext,
    attr: &[RustToken],
    state: &mut SliceScanState<'_>,
) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    let display_path = ctx.display_path;
    let (head, rest) = split_attribute_head(attr);

    if head.last().map(|(name, _)| *name) == Some("path") {
        validate_attr_tokens_non_path(ctx, attr, state)?;
        return handle_path_attribute(ctx, tokens, attr_ctx, attr, state);
    }

    if head.as_slice() == [("cfg", false)] {
        validate_attr_tokens_non_path(ctx, attr, state)?;
        if !attr_ctx.is_inner
            && attr_ctx.can_disable_item
            && delim_spans_full_slice(rest, &RustToken::LParen, &RustToken::RParen)
        {
            let pred = &rest[1..rest.len() - 1];
            if eval_static_cfg_predicate(pred) == StaticCfg::AlwaysFalse {
                state.pending_item_cfg_disabled = true;
            }
        }
        return Ok(());
    }

    if let [(head_name, head_is_raw)] = head.as_slice()
        && *head_name == "cfg_attr"
    {
        if !delim_spans_full_slice(rest, &RustToken::LParen, &RustToken::RParen) {
            return Err(Failure::policy(
                phase,
                format!("malformed cfg_attr attribute in {display_path}"),
            ));
        }
        let inner = &rest[1..rest.len() - 1];
        let Some(items) = split_top_level_comma_items(inner, true) else {
            return Err(Failure::policy(
                phase,
                format!("malformed cfg_attr attribute in {display_path}"),
            ));
        };
        let Some((&pred, nested_attrs)) = items.split_first() else {
            return Err(Failure::policy(
                phase,
                format!("malformed cfg_attr attribute in {display_path}"),
            ));
        };
        validate_attr_tokens_non_path(ctx, pred, state)?;
        let cfg_val =
            if *head_is_raw { StaticCfg::Unknown } else { eval_static_cfg_predicate(pred) };
        if cfg_val == StaticCfg::AlwaysFalse && !state.in_macro() {
            // `rustc` unconditionally strips the inner attributes outside macro
            // invocations; preserve balanced-syntax and `$`/`#` checks without
            // validating stripped attributes.
            for sub_attr in nested_attrs {
                for tok in *sub_attr {
                    match tok {
                        RustToken::Dollar => {
                            return Err(Failure::policy(
                                phase,
                                format!(
                                    "metavariable '$' forbidden inside attribute in {display_path}"
                                ),
                            ));
                        }
                        RustToken::Pound => {
                            return Err(Failure::policy(
                                phase,
                                format!("nested '#' forbidden inside attribute in {display_path}"),
                            ));
                        }
                        _ => {}
                    }
                }
            }
            return Ok(());
        }
        let child_ctx = AttrContext {
            in_cfg_attr: true,
            can_disable_item: attr_ctx.can_disable_item && cfg_val == StaticCfg::AlwaysTrue,
            ..attr_ctx
        };
        for sub_attr in nested_attrs {
            inspect_attribute_body(ctx, tokens, child_ctx, sub_attr, state)?;
        }
        return Ok(());
    }

    validate_attr_tokens_non_path(ctx, attr, state)
}

/// Inspect the token body of an outer (`#[...]`) or inner (`#![...]`)
/// attribute, rejecting macro-composed attributes, `crate_type`,
/// `macro_export`, first-party macro definitions, compile-time file-reading
/// constructs (`debugger_visualizer`, `*asm`), unallowlisted
/// `#![feature(...)]` gates, and any `path` attribute other than a validated
/// literal outer `#[path = "..."] mod <name>;`.
fn validate_rust_attribute(
    ctx: &MemberSourceContext<'_>,
    tokens: &[RustToken],
    is_inner: bool,
    open_bracket: usize,
    close_bracket: usize,
    state: &mut SliceScanState<'_>,
) -> Result<(), Failure> {
    let attr = &tokens[open_bracket + 1..close_bracket];
    let can_disable_item = !is_inner && !state.in_macro();
    inspect_attribute_body(
        ctx,
        tokens,
        AttrContext { is_inner, close_bracket, in_cfg_attr: false, can_disable_item },
        attr,
        state,
    )
}

/// Find the closing delimiter matching `tokens[open_idx]` (`(`, `[`, or `{`)
/// while enforcing balanced `{}`, `()`, and `[]` delimiters inside skipped
/// disabled inline `mod` blocks or disabled item macro invocations.
fn find_balanced_delim_end(
    tokens: &[RustToken],
    open_idx: usize,
    display_path: &str,
    phase: &str,
) -> Result<usize, Failure> {
    if tokens.get(open_idx).and_then(RustDelim::from_open).is_none() {
        return Err(Failure::policy(
            phase,
            format!("expected opening delimiter in {display_path}"),
        ));
    }
    let mut stack: Vec<RustDelim> = Vec::new();
    for (idx, tok) in tokens.iter().enumerate().skip(open_idx) {
        if let Some(open) = RustDelim::from_open(tok) {
            stack.push(open);
        } else if let Some(close) = RustDelim::from_close(tok) {
            let Some(expected) = stack.pop() else {
                return Err(Failure::policy(
                    phase,
                    format!("unbalanced closing delimiter in {display_path}"),
                ));
            };
            if expected != close {
                return Err(Failure::policy(
                    phase,
                    format!("mismatched closing delimiter in {display_path}"),
                ));
            }
            if stack.is_empty() {
                return Ok(idx);
            }
        }
    }
    Err(Failure::policy(phase, format!("unclosed delimiter in {display_path}")))
}

/// Match an item-level macro invocation `[::] ident (:: ident)* ! delim`
/// (with balanced nested delimiters and optional trailing `;`) when
/// `state.pending_item_cfg_disabled` is active, returning the index after the
/// skipped invocation while never matching `macro_rules!` or `macro`.
fn disabled_item_macro_invocation_end(
    tokens: &[RustToken],
    idx: usize,
    display_path: &str,
    phase: &str,
) -> Result<Option<usize>, Failure> {
    let mut pos = idx;
    if tokens.get(pos) == Some(&RustToken::Colon) && tokens.get(pos + 1) == Some(&RustToken::Colon)
    {
        pos += 2;
    }
    let Some(first_name) = tokens.get(pos).and_then(RustToken::ident_name) else {
        return Ok(None);
    };
    if matches!(first_name, "macro_rules" | "macro") {
        return Ok(None);
    }
    pos += 1;
    while tokens.get(pos) == Some(&RustToken::Colon)
        && tokens.get(pos + 1) == Some(&RustToken::Colon)
    {
        let Some(seg_name) = tokens.get(pos + 2).and_then(RustToken::ident_name) else {
            return Ok(None);
        };
        if matches!(seg_name, "macro_rules" | "macro") {
            return Ok(None);
        }
        pos += 3;
    }
    if tokens.get(pos) != Some(&RustToken::Bang) {
        return Ok(None);
    }
    let open_idx = pos + 1;
    if tokens.get(open_idx).and_then(RustDelim::from_open).is_none() {
        return Ok(None);
    }
    let close_idx = find_balanced_delim_end(tokens, open_idx, display_path, phase)?;
    let next_idx = if tokens.get(close_idx + 1) == Some(&RustToken::Semi) {
        close_idx + 2
    } else {
        close_idx + 1
    };
    Ok(Some(next_idx))
}

/// Validate `exocrate::config! { ... }` starting at `exocrate` (`idx`),
/// verifying every literal path in `versioned_files: &[...]` resolves to an
/// existing regular file inside `ctx.member_canon` relative to
/// `ctx.source_file.parent()` (matching `exocrate::config!`'s `include_bytes!`
/// expansion) and scanning the remainder of the macro body.
fn validate_exocrate_config(
    ctx: &MemberSourceContext<'_>,
    tokens: &[RustToken],
    idx: usize,
    state: &mut SliceScanState<'_>,
) -> Result<usize, Failure> {
    let phase = "cargo-boundary";
    let display_path = ctx.display_path;
    if tokens.get(idx + 4) != Some(&RustToken::Bang) {
        return Err(Failure::policy(
            phase,
            format!("disallowed non-invocation reference to exocrate::config in {display_path}"),
        ));
    }
    let (open_tok, close_tok) = match tokens.get(idx + 5) {
        Some(RustToken::LBrace) => (&RustToken::LBrace, &RustToken::RBrace),
        Some(RustToken::LParen) => (&RustToken::LParen, &RustToken::RParen),
        Some(RustToken::LBracket) => (&RustToken::LBracket, &RustToken::RBracket),
        _ => {
            return Err(Failure::policy(
                phase,
                format!("malformed exocrate::config! invocation in {display_path}"),
            ));
        }
    };
    let close = find_matching_delim(tokens, idx + 5, open_tok, close_tok, display_path, phase)?;
    let body = &tokens[idx + 6..close];

    let vf_positions: Vec<usize> = body
        .iter()
        .enumerate()
        .filter_map(|(pos, tok)| match tok {
            RustToken::Ident { name, .. } if name == "versioned_files" => Some(pos),
            _ => None,
        })
        .collect();
    if vf_positions.len() != 1 {
        return Err(Failure::policy(
            phase,
            format!(
                "exocrate::config! in {display_path} must declare exactly one versioned_files field"
            ),
        ));
    }
    let vf = vf_positions[0];
    if body.get(vf + 1) != Some(&RustToken::Colon)
        || body.get(vf + 2) != Some(&RustToken::Amp)
        || body.get(vf + 3) != Some(&RustToken::LBracket)
    {
        return Err(Failure::policy(
            phase,
            format!(
                "exocrate::config! versioned_files in {display_path} must be a literal slice &[...]"
            ),
        ));
    }
    let arr_end = find_matching_delim(
        body,
        vf + 3,
        &RustToken::LBracket,
        &RustToken::RBracket,
        display_path,
        phase,
    )?;
    let entries = &body[vf + 4..arr_end];
    let mut i = 0;
    while i < entries.len() {
        let RustToken::StringLit(rel) = &entries[i] else {
            return Err(Failure::policy(
                phase,
                format!(
                    "exocrate::config! versioned_files in {display_path} must contain only string literals"
                ),
            ));
        };
        let resolved =
            validate_source_relative_path(ctx, rel, "Rust exocrate::config! versioned_files")?;
        if resolved.is_none() {
            return Err(Failure::policy(
                phase,
                format!(
                    "Rust exocrate::config! versioned_files in {display_path} does not exist: {rel}"
                ),
            ));
        }
        i += 1;
        if i < entries.len() {
            if entries[i] != RustToken::Comma {
                return Err(Failure::policy(
                    phase,
                    format!("malformed exocrate::config! versioned_files list in {display_path}"),
                ));
            }
            i += 1;
        }
    }

    let inner_ownership = match state.ownership {
        StemOwnership::OwnedRelative => StemOwnership::AmbiguousInMacro,
        other => other,
    };
    validate_token_slice_with_ownership(
        ctx,
        body,
        state.worklist,
        state.inline_mod_stack,
        inner_ownership,
        true,
    )?;
    Ok(close + 1)
}

/// Validate `exocrate::parse_remote_archive! { [vis] const NAME: RemoteArchive
/// = "<rel>"; }` starting at `exocrate` (`idx`), verifying the manifest path
/// resolves relative to `ctx.member_dir` (`CARGO_MANIFEST_DIR`) to an existing
/// regular non-symlink file inside `ctx.member_canon`.
fn validate_exocrate_parse_remote_archive(
    ctx: &MemberSourceContext<'_>,
    tokens: &[RustToken],
    idx: usize,
) -> Result<usize, Failure> {
    let phase = "cargo-boundary";
    let display_path = ctx.display_path;
    if tokens.get(idx + 4) != Some(&RustToken::Bang) {
        return Err(Failure::policy(
            phase,
            format!(
                "disallowed non-invocation reference to exocrate::parse_remote_archive in {display_path}"
            ),
        ));
    }
    let (open_tok, close_tok) = match tokens.get(idx + 5) {
        Some(RustToken::LBrace) => (&RustToken::LBrace, &RustToken::RBrace),
        Some(RustToken::LParen) => (&RustToken::LParen, &RustToken::RParen),
        Some(RustToken::LBracket) => (&RustToken::LBracket, &RustToken::RBracket),
        _ => {
            return Err(Failure::policy(
                phase,
                format!("malformed exocrate::parse_remote_archive! invocation in {display_path}"),
            ));
        }
    };
    let close = find_matching_delim(tokens, idx + 5, open_tok, close_tok, display_path, phase)?;
    let body = &tokens[idx + 6..close];
    let mut pos = 0;
    if body.get(pos).and_then(RustToken::ident_name) == Some("pub") {
        pos += 1;
        if body.get(pos) == Some(&RustToken::LParen) {
            let vis_end = find_matching_delim(
                body,
                pos,
                &RustToken::LParen,
                &RustToken::RParen,
                display_path,
                phase,
            )?;
            pos = vis_end + 1;
        }
    }
    let rel_str = match &body[pos..] {
        [
            RustToken::Ident { name: kw_const, .. },
            RustToken::Ident { .. },
            RustToken::Colon,
            RustToken::Ident { name: ty_name, .. },
            RustToken::Eq,
            RustToken::StringLit(rel),
            RustToken::Semi,
        ] if kw_const == "const" && ty_name == "RemoteArchive" => rel.as_str(),
        _ => {
            return Err(Failure::policy(
                phase,
                format!("unsupported exocrate::parse_remote_archive! form in {display_path}"),
            ));
        }
    };
    validate_portable_relative_path_syntax(
        rel_str,
        "Rust exocrate::parse_remote_archive!",
        display_path,
        phase,
    )?;
    let mut clean_rel = PathBuf::new();
    for component in Path::new(rel_str).components() {
        match component {
            Component::Normal(seg) => clean_rel.push(seg),
            Component::CurDir => {}
            Component::Prefix(_) | Component::RootDir | Component::ParentDir => {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "Rust exocrate::parse_remote_archive! in {display_path} escapes member directory: {rel_str}"
                    ),
                ));
            }
        }
    }
    if clean_rel.as_os_str().is_empty() {
        return Err(Failure::policy(
            phase,
            format!("Rust exocrate::parse_remote_archive! in {display_path} has empty path"),
        ));
    }
    validate_real_file(
        ctx.member_dir,
        ctx.member_canon,
        &clean_rel,
        &format!("Rust exocrate::parse_remote_archive! in {display_path}"),
        phase,
    )?;
    Ok(close + 1)
}

/// Inspect a `use ...;` item starting at `idx`, rejecting imports of
/// `exocrate`, `include*`, `toml_const`, or `macro_util` so path-reading
/// macros cannot be aliased or glob-imported out of sight.
fn validate_use_item(
    tokens: &[RustToken],
    idx: usize,
    display_path: &str,
    phase: &str,
) -> Result<usize, Failure> {
    let mut brace_depth = 0usize;
    let mut j = idx + 1;
    while j < tokens.len() {
        match &tokens[j] {
            RustToken::LBrace => brace_depth += 1,
            RustToken::RBrace => {
                if brace_depth == 0 {
                    return Err(Failure::policy(
                        phase,
                        format!("unbalanced '}}' in use item in {display_path}"),
                    ));
                }
                brace_depth -= 1;
            }
            RustToken::Pound => {
                return Err(Failure::policy(
                    phase,
                    format!("unexpected '#' inside use item in {display_path}"),
                ));
            }
            RustToken::Semi if brace_depth == 0 => return Ok(j + 1),
            RustToken::Ident { name, .. } if is_disallowed_file_reading_ident(name) => {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "disallowed import of compile-time file-reading construct '{name}' in {display_path}"
                    ),
                ));
            }
            RustToken::Ident { name, .. }
                if matches!(
                    name.as_str(),
                    "exocrate"
                        | "parse_remote_archive"
                        | "include"
                        | "include_str"
                        | "include_bytes"
                        | "toml_const"
                        | "macro_util"
                ) =>
            {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "disallowed import of path-reading macro or crate '{name}' in {display_path}"
                    ),
                ));
            }
            _ => {}
        }
        j += 1;
    }
    Err(Failure::policy(phase, format!("unterminated use item in {display_path}")))
}

/// Validate a token slice from a compiled trusted workspace member source file,
/// following inline and out-of-line `mod` declarations, `#[path]`, and
/// `include!` into `worklist` while validating `include_str!`,
/// `include_bytes!`, and `exocrate` data paths in place.
fn validate_token_slice(
    ctx: &MemberSourceContext<'_>,
    tokens: &[RustToken],
    worklist: &mut VecDeque<(PathBuf, ModuleDirMode)>,
    inline_mod_stack: &mut Vec<InlineModDir>,
) -> Result<(), Failure> {
    validate_token_slice_with_ownership(
        ctx,
        tokens,
        worklist,
        inline_mod_stack,
        StemOwnership::OwnedRelative,
        false,
    )
}

/// Inner implementation of [`validate_token_slice`] carrying the enclosing
/// [`StemOwnership`] and macro-body state across recursive `exocrate::config!`
/// scans.
fn validate_token_slice_with_ownership(
    ctx: &MemberSourceContext<'_>,
    tokens: &[RustToken],
    worklist: &mut VecDeque<(PathBuf, ModuleDirMode)>,
    inline_mod_stack: &mut Vec<InlineModDir>,
    initial_ownership: StemOwnership,
    initial_in_macro: bool,
) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    let display_path = ctx.display_path;
    let initial_inline_depth = inline_mod_stack.len();
    let mut state = SliceScanState {
        worklist,
        inline_mod_stack,
        delim_stack: Vec::new(),
        ownership: initial_ownership,
        in_macro_base: initial_in_macro,
        path_annotated_mods: BTreeSet::new(),
        pending_path_targets: BTreeMap::new(),
        pending_item_cfg_disabled: false,
    };
    let mut idx = 0;
    while idx < tokens.len() {
        if tokens[idx] == RustToken::Pound {
            let (is_inner, open) = if tokens.get(idx + 1) == Some(&RustToken::Bang)
                && tokens.get(idx + 2) == Some(&RustToken::LBracket)
            {
                (true, idx + 2)
            } else if tokens.get(idx + 1) == Some(&RustToken::LBracket) {
                (false, idx + 1)
            } else {
                return Err(Failure::policy(
                    phase,
                    format!("standalone '#' token forbidden in Rust source {display_path}"),
                ));
            };
            let close = find_matching_delim(
                tokens,
                open,
                &RustToken::LBracket,
                &RustToken::RBracket,
                display_path,
                phase,
            )?;
            if is_inner {
                state.pending_item_cfg_disabled = false;
            }
            validate_rust_attribute(ctx, tokens, is_inner, open, close, &mut state)?;
            idx = close + 1;
            continue;
        }
        if state.pending_item_cfg_disabled && tokens[idx].ident_name() == Some("pub") {
            let mut next_idx = idx + 1;
            if tokens.get(next_idx) == Some(&RustToken::LParen) {
                let close = find_matching_delim(
                    tokens,
                    next_idx,
                    &RustToken::LParen,
                    &RustToken::RParen,
                    display_path,
                    phase,
                )?;
                validate_attr_tokens_non_path(ctx, &tokens[next_idx + 1..close], &mut state)?;
                next_idx = close + 1;
            }
            if tokens.get(next_idx).and_then(RustToken::ident_name) != Some("mod") {
                state.pending_item_cfg_disabled = false;
            }
            idx = next_idx;
            continue;
        }
        if matches!(
            &tokens[idx],
            RustToken::Ident {
                name,
                is_raw: false,
            } if name == "mod"
        ) && let Some(mod_name) = tokens.get(idx + 1).and_then(RustToken::ident_name)
            && matches!(tokens.get(idx + 2), Some(RustToken::LBrace | RustToken::Semi))
        {
            let cfg_disabled = state.pending_item_cfg_disabled;
            state.pending_item_cfg_disabled = false;
            if cfg_disabled {
                state.pending_path_targets.remove(&idx);
                if tokens.get(idx + 2) == Some(&RustToken::LBrace) {
                    let block_end = find_balanced_delim_end(tokens, idx + 2, display_path, phase)?;
                    idx = block_end + 1;
                } else {
                    idx += 3;
                }
                continue;
            }
            if tokens.get(idx + 2) == Some(&RustToken::LBrace) {
                let inline_dir = if let Some(specs) = state.pending_path_targets.remove(&idx) {
                    InlineModDir::PathOverride(resolve_pending_inline_path_dirs(ctx, specs)?)
                } else {
                    InlineModDir::Name(mod_name.to_string())
                };
                state.delim_stack.push(DelimFrame {
                    open: RustDelim::Brace,
                    inline_mod: true,
                    in_macro: false,
                    prev_ownership: state.ownership,
                });
                if state.ownership == StemOwnership::OwnedRelative {
                    state.ownership = StemOwnership::ConsumedIntoBase;
                }
                state.inline_mod_stack.push(inline_dir);
            } else if let Some(specs) = state.pending_path_targets.remove(&idx) {
                resolve_pending_path_specs(ctx, specs, state.worklist)?;
            } else if !state.path_annotated_mods.contains(&idx) {
                enqueue_out_of_line_module(
                    ctx,
                    state.inline_mod_stack,
                    state.ownership,
                    mod_name,
                    state.worklist,
                )?;
            }
            idx += 3;
            continue;
        }
        if state.pending_item_cfg_disabled
            && let Some(next_idx) =
                disabled_item_macro_invocation_end(tokens, idx, display_path, phase)?
        {
            state.pending_item_cfg_disabled = false;
            idx = next_idx;
            continue;
        }
        state.pending_item_cfg_disabled = false;
        match &tokens[idx] {
            RustToken::LBrace => {
                state.delim_stack.push(DelimFrame {
                    open: RustDelim::Brace,
                    inline_mod: false,
                    in_macro: false,
                    prev_ownership: state.ownership,
                });
                if state.ownership == StemOwnership::OwnedRelative {
                    state.ownership = StemOwnership::DisownedByBlock;
                }
                idx += 1;
            }
            RustToken::LParen | RustToken::LBracket => {
                let open = RustDelim::from_open(&tokens[idx]).expect("checked above");
                state.delim_stack.push(DelimFrame {
                    open,
                    inline_mod: false,
                    in_macro: false,
                    prev_ownership: state.ownership,
                });
                idx += 1;
            }
            tok @ (RustToken::RBrace | RustToken::RParen | RustToken::RBracket) => {
                let expected = RustDelim::from_close(tok).expect("checked above");
                let Some(frame) = state.delim_stack.pop() else {
                    return Err(Failure::policy(
                        phase,
                        format!("unbalanced closing delimiter in {display_path}"),
                    ));
                };
                if frame.open != expected {
                    return Err(Failure::policy(
                        phase,
                        format!("mismatched closing delimiter in {display_path}"),
                    ));
                }
                if frame.inline_mod {
                    state.inline_mod_stack.pop();
                }
                state.ownership = frame.prev_ownership;
                idx += 1;
            }
            RustToken::Pound => unreachable!("handled above"),
            RustToken::Ident { name, is_raw: false }
                if name == "macro_rules"
                    && tokens.get(idx + 1) == Some(&RustToken::Bang)
                    && matches!(tokens.get(idx + 2), Some(RustToken::Ident { .. }))
                    && matches!(
                        tokens.get(idx + 3),
                        Some(RustToken::LBrace | RustToken::LParen | RustToken::LBracket)
                    ) =>
            {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "macro_rules! definitions are forbidden in trusted workspace members ({display_path})"
                    ),
                ));
            }
            RustToken::Ident { name, is_raw: false } if name == "macro" => {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "declarative macro definitions are forbidden in trusted workspace members ({display_path})"
                    ),
                ));
            }
            RustToken::Ident { name, .. }
                if is_disallowed_inline_asm_ident(name)
                    && tokens.get(idx + 1) == Some(&RustToken::Bang) =>
            {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "disallowed compile-time file-reading construct '{name}' in {display_path}"
                    ),
                ));
            }
            RustToken::Ident { name, .. }
                if matches!(name.as_str(), "toml_const" | "macro_util")
                    && (tokens.get(idx + 1) == Some(&RustToken::Bang)
                        || tokens.get(idx + 1) == Some(&RustToken::Colon)
                        || idx.checked_sub(1).and_then(|p| tokens.get(p))
                            == Some(&RustToken::Colon)) =>
            {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "disallowed exocrate internal macro reference '{name}' in {display_path}"
                    ),
                ));
            }
            RustToken::Ident { name, is_raw: false }
                if name == "use"
                    && !matches!(
                        idx.checked_sub(1).and_then(|prev| tokens.get(prev)),
                        Some(RustToken::Dot | RustToken::Colon)
                    )
                    && matches!(
                        tokens.get(idx + 1),
                        Some(RustToken::Ident { .. } | RustToken::Colon | RustToken::LBrace)
                    ) =>
            {
                idx = validate_use_item(tokens, idx, display_path, phase)?;
            }
            RustToken::Ident { name, .. }
                if name == "extern"
                    && tokens.get(idx + 1).and_then(RustToken::ident_name) == Some("crate")
                    && tokens.get(idx + 2).and_then(RustToken::ident_name).is_some()
                    && tokens.get(idx + 3).and_then(RustToken::ident_name) == Some("as") =>
            {
                return Err(Failure::policy(
                    phase,
                    format!("disallowed extern crate alias in {display_path}"),
                ));
            }
            RustToken::Ident { name, .. }
                if name == "exocrate"
                    && tokens.get(idx + 1) == Some(&RustToken::Colon)
                    && tokens.get(idx + 2) == Some(&RustToken::Colon) =>
            {
                match tokens.get(idx + 3).and_then(RustToken::ident_name) {
                    Some("config") => {
                        idx = validate_exocrate_config(ctx, tokens, idx, &mut state)?;
                    }
                    Some("parse_remote_archive") => {
                        idx = validate_exocrate_parse_remote_archive(ctx, tokens, idx)?;
                    }
                    _ => idx += 3,
                }
            }
            RustToken::Ident { name, .. }
                if matches!(name.as_str(), "config" | "parse_remote_archive")
                    && tokens.get(idx + 1) == Some(&RustToken::Bang) =>
            {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "unqualified or aliased {name}! macro invocation forbidden in {display_path}"
                    ),
                ));
            }
            RustToken::Ident { name, .. }
                if matches!(name.as_str(), "include" | "include_str" | "include_bytes") =>
            {
                idx = validate_include_token(ctx, tokens, idx, name, state.worklist)?;
            }
            _ => {
                if let Some((open_idx, open)) = macro_invocation_open_idx(tokens, idx) {
                    state.delim_stack.push(DelimFrame {
                        open,
                        inline_mod: false,
                        in_macro: true,
                        prev_ownership: state.ownership,
                    });
                    if state.ownership == StemOwnership::OwnedRelative {
                        state.ownership = StemOwnership::AmbiguousInMacro;
                    }
                    idx = open_idx + 1;
                } else {
                    idx += 1;
                }
            }
        }
    }
    if !state.delim_stack.is_empty() {
        return Err(Failure::policy(phase, format!("unclosed delimiter in {display_path}")));
    }
    for (_, specs) in state.pending_path_targets {
        resolve_pending_path_specs(ctx, specs, state.worklist)?;
    }
    state.inline_mod_stack.truncate(initial_inline_depth);
    Ok(())
}

/// Scan every compiled Rust source file reachable from `initial_sources`
/// (Cargo target roots plus any module reached via out-of-line `mod`,
/// `#[path]`, or `include!`) to enforce lexical containment of first-party
/// `#[path]`, `include*!`, `exocrate::config!`, and
/// `exocrate::parse_remote_archive!` inputs while rejecting first-party macro
/// definitions, unallowlisted `#![feature(...)]` gates, `crate_type`, and
/// macro-composed attributes.
fn validate_member_rust_sources(
    member: &str,
    member_dir: &Path,
    member_canon: &Path,
    initial_sources: Vec<(PathBuf, ModuleDirMode)>,
) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    let mut visited: BTreeSet<(PathBuf, ModuleDirMode)> = BTreeSet::new();
    let mut worklist: VecDeque<(PathBuf, ModuleDirMode)> = initial_sources.into();

    while let Some((source_file, dir_mode)) = worklist.pop_front() {
        let canon = fs::canonicalize(&source_file).map_err(|err| {
            Failure::operational(
                phase,
                format!("cannot canonicalize {}: {err}", source_file.display()),
            )
        })?;
        if !canon.starts_with(member_canon) {
            return Err(Failure::policy(
                phase,
                format!("Rust source escapes workspace member {member}: {}", source_file.display()),
            ));
        }
        if !visited.insert((canon, dir_mode)) {
            continue;
        }
        let rel = source_file.strip_prefix(member_dir).unwrap_or(&source_file);
        let display_path = format!("{member}/{}", rel.display());
        let src = fs::read_to_string(&source_file).map_err(|err| {
            Failure::policy(
                phase,
                format!("cannot read Rust source as UTF-8 ({display_path}): {err}"),
            )
        })?;
        let tokens = lex_rust_tokens(&src, &display_path, phase)?;
        let ctx = MemberSourceContext {
            member,
            member_dir,
            member_canon,
            source_file: &source_file,
            dir_mode,
            display_path: &display_path,
        };
        let mut inline_mod_stack = Vec::new();
        validate_token_slice(&ctx, &tokens, &mut worklist, &mut inline_mod_stack)?;
    }
    Ok(())
}

/// Reject absolute paths or symlink components along a member's relative
/// `path = "..."` dependency before canonicalization.
fn reject_dep_path_symlinks(checkout: &Path, member: &str, dep_path: &str) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    if dep_path.is_empty() || dep_path.contains('\0') || has_non_portable_path_syntax(dep_path) {
        return Err(Failure::policy(
            phase,
            format!("{member} path dependency escapes checkout: {dep_path}"),
        ));
    }
    let mut stack: Vec<OsString> = Path::new(member)
        .components()
        .map(|c| match c {
            Component::Normal(seg) => Ok(seg.to_os_string()),
            _ => {
                Err(Failure::policy(phase, format!("workspace member outside trusted/: {member}")))
            }
        })
        .collect::<Result<_, _>>()?;

    for component in Path::new(dep_path).components() {
        match component {
            Component::Prefix(_) | Component::RootDir => {
                return Err(Failure::policy(
                    phase,
                    format!("{member} path dependency escapes checkout: {dep_path}"),
                ));
            }
            Component::CurDir => continue,
            Component::ParentDir => {
                if stack.pop().is_none() {
                    return Err(Failure::policy(
                        phase,
                        format!("{member} path dependency escapes checkout: {dep_path}"),
                    ));
                }
            }
            Component::Normal(seg) => {
                stack.push(seg.to_os_string());
                let cur = stack.iter().fold(checkout.to_path_buf(), |mut acc, s| {
                    acc.push(s);
                    acc
                });
                if let Ok(meta) = fs::symlink_metadata(&cur)
                    && meta.file_type().is_symlink()
                {
                    return Err(Failure::policy(
                        phase,
                        format!("{member} path dependency traverses symlink: {dep_path}"),
                    ));
                }
            }
        }
    }
    Ok(())
}

/// Validate a single dependency table (`[dependencies]`, `[dev-dependencies]`,
/// `[build-dependencies]`, or `[target.<cfg>.*]`) inside a workspace member's
/// `Cargo.toml`.
fn validate_dep_table(
    checkout: &Path,
    checkout_canon: &Path,
    member: &str,
    member_parent: &Path,
    member_set: &BTreeSet<String>,
    section: &str,
    table_val: Option<&toml::Value>,
) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    let Some(table_val) = table_val else {
        return Ok(());
    };
    let table = table_val.as_table().ok_or_else(|| {
        Failure::new(1, phase, format!("invalid {section} in {member}/Cargo.toml"))
    })?;
    for (dep_name, spec) in table {
        if !spec.is_str() && !spec.is_table() {
            return Err(Failure::policy(
                phase,
                format!("invalid dependency specification for {dep_name} in {member}/Cargo.toml"),
            ));
        }
        let Some(spec_obj) = spec.as_table() else {
            continue;
        };
        if spec_obj.contains_key("git")
            || spec_obj.contains_key("registry")
            || spec_obj.contains_key("registry-index")
        {
            return Err(Failure::new(
                1,
                phase,
                format!(
                    "disallowed git or custom-registry dependency {dep_name} in {member}/Cargo.toml"
                ),
            ));
        }
        if spec_obj.contains_key("package") {
            return Err(Failure::policy(
                phase,
                format!(
                    "disallowed renamed dependency (package = ...) {dep_name} in {member}/Cargo.toml"
                ),
            ));
        }
        if spec_obj.contains_key("workspace") {
            return Err(Failure::policy(
                phase,
                format!(
                    "disallowed workspace dependency inheritance (workspace = ...) for {dep_name} in {member}/Cargo.toml"
                ),
            ));
        }
        for key in spec_obj.keys() {
            if !matches!(
                key.as_str(),
                "version"
                    | "path"
                    | "features"
                    | "default-features"
                    | "default_features"
                    | "optional"
            ) {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "disallowed dependency key '{key}' for {dep_name} in {member}/Cargo.toml"
                    ),
                ));
            }
        }
        let Some(path_val) = spec_obj.get("path") else {
            continue;
        };
        let Some(dep_path) = path_val.as_str() else {
            return Err(Failure::new(
                1,
                phase,
                format!("non-string path dependency {dep_name} in {member}/Cargo.toml"),
            ));
        };
        reject_dep_path_symlinks(checkout, member, dep_path)?;
        let resolved = fs::canonicalize(member_parent.join(dep_path)).map_err(|_| {
            Failure::new(
                1,
                phase,
                format!("{member} path dependency target does not exist: {dep_path}"),
            )
        })?;
        let rel = resolved.strip_prefix(checkout_canon).map_err(|_| {
            Failure::new(1, phase, format!("{member} path dependency escapes checkout: {dep_path}"))
        })?;
        let rel_str = rel.to_string_lossy().replace('\\', "/");
        if !rel_str.starts_with("trusted/") {
            return Err(Failure::new(
                1,
                phase,
                format!("{member} path dependency points outside trusted/: {rel_str}"),
            ));
        }
        if !member_set.contains(&rel_str) {
            return Err(Failure::new(
                1,
                phase,
                format!("{member} path dependency points to non-member crate: {rel_str}"),
            ));
        }
        validate_single_link_regular(
            &resolved.join("Cargo.toml"),
            &format!("{member} path dependency Cargo.toml"),
            phase,
        )?;
    }
    Ok(())
}

/// Validate `Cargo.lock` (when present): version 4, every external dependency
/// sourced from `crates.io-index` with a 64-hex SHA-256 checksum, and every
/// source-less package belonging to `member_pkg_names`.
fn verify_cargo_lock(checkout: &Path, member_pkg_names: &BTreeSet<String>) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    verify_exact_case_entry(checkout, OsStr::new("Cargo.lock"), "Cargo.lock", phase)?;
    let lock_path = checkout.join("Cargo.lock");
    if fs::symlink_metadata(&lock_path).is_err() {
        return Ok(());
    }
    validate_single_link_regular(&lock_path, "Cargo.lock", phase)?;
    let lock_text = fs::read_to_string(&lock_path)
        .map_err(|e| Failure::new(1, phase, format!("cannot read Cargo.lock: {e}")))?;
    reject_bidi_or_invisible_controls(&lock_text, "Cargo.lock", phase)?;
    let lock_file: CargoLockFile = toml::from_str(&lock_text)
        .map_err(|e| Failure::new(1, phase, format!("malformed Cargo.lock: {e}")))?;
    if lock_file.version != Some(4) {
        return Err(Failure::new(1, phase, "Cargo.lock must have version = 4"));
    }
    for pkg in &lock_file.package {
        let pkg_name = pkg.name.as_str();
        match pkg.source.as_deref() {
            Some("registry+https://github.com/rust-lang/crates.io-index") => {
                if !pkg.checksum.as_deref().is_some_and(is_sha256_hex) {
                    return Err(Failure::new(
                        1,
                        phase,
                        format!("missing or invalid checksum in Cargo.lock for {pkg_name}"),
                    ));
                }
            }
            Some(other_src) => {
                return Err(Failure::new(
                    1,
                    phase,
                    format!(
                        "untrusted dependency source in Cargo.lock for {pkg_name}: {other_src}"
                    ),
                ));
            }
            None => {
                if pkg.checksum.is_some() || !member_pkg_names.contains(pkg_name) {
                    return Err(Failure::new(
                        1,
                        phase,
                        format!("untrusted local package without source in Cargo.lock: {pkg_name}"),
                    ));
                }
            }
        }
    }
    Ok(())
}

/// Verify Cargo workspace DAG containment, root Cargo/toolchain hygiene,
/// `Cargo.lock` dependency provenance, member and target filesystem
/// containment, lexical Rust source-closure containment (`#[path]`,
/// `include!`, `include_str!`, `include_bytes!`, `exocrate::config!`, and
/// `exocrate::parse_remote_archive!`), and `trusted/root-manifest.sha256`
/// (when present): all workspace members must reside under real directories
/// inside `trusted/`, and no workspace crate may depend on a path outside
/// `workspace.members`.
///
/// Entries in `workspace.exclude` are validated as non-glob real directories
/// under `trusted/` (when present), checked by
/// [`verify_trusted_subtree_hygiene`] (with intermediate ancestors checked for
/// real-directory containment and forbidden override entries) rather than parsed
/// as workspace members, and excluded from member `path`-dependency and
/// `Cargo.lock` allowlists.
/// Whole-tree filesystem hygiene (`verify_trusted_subtree_hygiene`) rejects
/// symlinks, hard-linked files (`nlink > 1`), special files, canonical
/// escapes, bidi/invisible control characters in texts or relative member
/// paths, and nested Cargo/toolchain/ambient override entries (`.cargo*`,
/// `rust-toolchain*`, `.gitmodules`, `.envrc`, `.gitattributes`,
/// `AGENTS.override.md`, `lean-toolchain`) across every file and directory in
/// each member (and ancestor directories up to the checkout root), including
/// uncompiled test fixture data, while compiled host-source closure scanning
/// (`collect_cargo_target_roots` + `validate_member_rust_sources`) starts from
/// every declared or auto-discovered Cargo target root (honoring
/// `autolib`/`auto<kind>` switches and resolving pathless explicit targets),
/// enforces ASCII-only tokens and identifiers outside comments and string/char
/// literals, and follows out-of-line `mod`, `#[path]`, and `include!`
/// declarations. Both Cargo manifests and dependency tables use closed-world
/// schemas (`#[serde(deny_unknown_fields)]`, rejecting `cargo-features`,
/// `package.metabuild`, `package.links`, `[workspace.dependencies]`, and
/// `workspace = true` inheritance); every workspace member must declare
/// `package.edition = "2024"` with no target-level `edition` overrides, set
/// `[lib] doctest = false` when it has a library target, and omit Cargo
/// `package = "..."` dependency renames and `extern crate ... as` aliases.
/// First-party macro definitions (`macro_rules!`, `macro`), proc-macro targets,
/// compile-time file-reading constructs (`debugger_visualizer` attributes and
/// imports, `global_asm`, `asm`, `naked_asm`), and unstable `#![feature(...)]`
/// gates outside [`allowed_unstable_features`] (`normalize_lexically` and
/// `rustc_private` in `trusted/rustc-capture` only)
/// are forbidden; external `Cargo.lock`- or pinned-toolchain dependencies and
/// their procedural macros outside the validated `exocrate` invocations remain
/// governed by `Cargo.lock` / toolchain provenance and human dependency
/// review.
///
/// Lean bundle parity belongs to [`verify_bundled_resources`], which
/// [`check_checkout_cargo_hygiene`] runs separately.
pub fn check_cargo_boundary(checkout: &Path) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    reject_cargo_toolchain_overrides(checkout)?;
    let root_toml_path = checkout.join("Cargo.toml");
    validate_single_link_regular(&root_toml_path, "root Cargo.toml", phase)?;
    let checkout_canon = fs::canonicalize(checkout)
        .map_err(|e| Failure::new(2, phase, format!("cannot canonicalize checkout: {e}")))?;
    let (trusted_dir, trusted_canon) = validate_real_dir(
        checkout,
        &checkout_canon,
        Path::new("trusted"),
        "trusted directory",
        phase,
    )?;
    reject_git_submodules(checkout, &checkout_canon, phase)?;
    let (capture_dir, capture_canon) = validate_real_dir(
        checkout,
        &checkout_canon,
        Path::new("trusted/rustc-capture"),
        "workspace member trusted/rustc-capture",
        phase,
    )?;
    if !capture_canon.starts_with(&trusted_canon) || capture_canon == trusted_canon {
        return Err(Failure::policy(
            phase,
            "workspace member trusted/rustc-capture escapes trusted/",
        ));
    }
    validate_single_link_regular(
        &capture_dir.join("Cargo.toml"),
        "trusted/rustc-capture/Cargo.toml",
        phase,
    )?;
    verify_root_manifest_sha256(checkout)?;

    let root_text = fs::read_to_string(&root_toml_path)
        .map_err(|e| Failure::new(1, phase, format!("malformed Cargo manifest: {e}")))?;
    reject_bidi_or_invisible_controls(&root_text, "root Cargo.toml", phase)?;
    let root_manifest: RootCargoManifest = toml::from_str(&root_text).map_err(|e| {
        Failure::new(1, phase, format!("root Cargo.toml may contain only [workspace]: {e}"))
    })?;
    if root_manifest.workspace.resolver.as_deref() != Some("2") {
        return Err(Failure::new(1, phase, "root [workspace] resolver must be \"2\""));
    }

    let members_set: BTreeSet<String> = root_manifest.workspace.members.iter().cloned().collect();
    if !members_set.contains("trusted/rustc-capture") {
        return Err(Failure::new(1, phase, "trusted/rustc-capture missing from workspace.members"));
    }

    let mut workspace_roots = BTreeMap::new();
    let mut global_lower_paths = BTreeMap::new();
    let mut checked_ancestor_dirs = BTreeSet::new();
    checked_ancestor_dirs.insert(checkout.to_path_buf());
    checked_ancestor_dirs.insert(checkout.join("trusted"));

    for excluded in &root_manifest.workspace.exclude {
        if !is_clean_relative_path(excluded)
            || !excluded.starts_with("trusted/")
            || excluded.ends_with('/')
            || has_cargo_glob_meta(excluded)
        {
            return Err(Failure::new(
                1,
                phase,
                format!("workspace.exclude outside trusted/ or uses glob: {excluded}"),
            ));
        }
        register_workspace_dir_path(
            excluded,
            &format!("workspace.exclude {excluded}"),
            &mut workspace_roots,
            &mut global_lower_paths,
            phase,
        )?;
        if members_set.contains(excluded) {
            return Err(Failure::new(
                1,
                phase,
                format!("workspace.exclude overlaps workspace.members: {excluded}"),
            ));
        }
        let excluded_rel = Path::new(excluded).strip_prefix("trusted").map_err(|_| {
            Failure::new(1, phase, format!("workspace.exclude outside trusted/: {excluded}"))
        })?;
        reject_forbidden_overrides_along_ancestors(checkout, excluded, &mut checked_ancestor_dirs)?;
        if let Some((excluded_dir, excluded_canon)) = validate_existing_real_dir(
            &checkout.join("trusted"),
            &trusted_canon,
            excluded_rel,
            &format!("workspace.exclude {excluded}"),
            phase,
        )? {
            verify_trusted_subtree_hygiene(
                "workspace.exclude",
                excluded,
                &excluded_dir,
                &excluded_canon,
                &mut global_lower_paths,
            )?;
        }
    }

    for member in &root_manifest.workspace.members {
        if !is_clean_relative_path(member)
            || !member.starts_with("trusted/")
            || member.ends_with('/')
            || has_cargo_glob_meta(member)
        {
            return Err(Failure::new(
                1,
                phase,
                format!("workspace member outside trusted/: {member}"),
            ));
        }
        register_workspace_dir_path(
            member,
            &format!("workspace member {member}"),
            &mut workspace_roots,
            &mut global_lower_paths,
            phase,
        )?;
    }

    let mut member_pkg_names = BTreeSet::new();
    for member in &root_manifest.workspace.members {
        let (member_dir, member_canon) = validate_real_dir(
            checkout,
            &checkout_canon,
            Path::new(member),
            &format!("workspace member {member}"),
            phase,
        )?;
        if !member_canon.starts_with(&trusted_canon) || member_canon == trusted_canon {
            return Err(Failure::policy(
                phase,
                format!("workspace member escapes trusted/: {member}"),
            ));
        }
        reject_forbidden_overrides_along_ancestors(checkout, member, &mut checked_ancestor_dirs)?;
        let member_toml_path = member_dir.join("Cargo.toml");
        validate_single_link_regular(&member_toml_path, &format!("{member}/Cargo.toml"), phase)?;
        let member_text = fs::read_to_string(&member_toml_path).map_err(|e| {
            Failure::new(1, phase, format!("malformed member Cargo.toml in {member}: {e}"))
        })?;
        reject_bidi_or_invisible_controls(&member_text, &format!("{member}/Cargo.toml"), phase)?;
        let manifest: MemberCargoManifest = toml::from_str(&member_text).map_err(|e| {
            Failure::new(1, phase, format!("malformed member Cargo.toml in {member}: {e}"))
        })?;
        let pkg_name =
            manifest.package.name.as_deref().filter(|s| !s.is_empty()).ok_or_else(|| {
                Failure::new(1, phase, format!("missing package.name in {member}"))
            })?;
        member_pkg_names.insert(pkg_name.to_string());

        if manifest.cargo_features.is_some() {
            return Err(Failure::policy(
                phase,
                format!("disallowed cargo-features in {member}/Cargo.toml"),
            ));
        }
        if manifest.package.metabuild.is_some() {
            return Err(Failure::policy(
                phase,
                format!("disallowed package.metabuild in {member}/Cargo.toml"),
            ));
        }
        if manifest.package.links.is_some() {
            return Err(Failure::policy(
                phase,
                format!("disallowed package.links in {member}/Cargo.toml"),
            ));
        }
        if manifest.package.build.is_some()
            || manifest.package.workspace.is_some()
            || manifest.workspace.is_some()
        {
            return Err(Failure::new(
                1,
                phase,
                format!("disallowed package.build or package.workspace in {member}/Cargo.toml"),
            ));
        }
        manifest.package.validate_edition(member)?;
        manifest.package.validate_no_workspace_inheritance(member)?;
        manifest.package.validate_auto_discovery_fields(member)?;
        manifest.validate_features(member)?;
        let autolib_disabled =
            manifest.package.autolib.as_ref().and_then(toml::Value::as_bool) == Some(false);
        if !autolib_disabled {
            verify_exact_case_path_prefix(
                &member_dir,
                Path::new("src/lib.rs"),
                &format!("{member}/src/lib.rs"),
                phase,
            )?;
        }
        let has_lib_target = manifest.lib.is_some()
            || (!autolib_disabled && fs::symlink_metadata(member_dir.join("src/lib.rs")).is_ok());
        if has_lib_target {
            let doctest_disabled = manifest
                .lib
                .as_ref()
                .and_then(|lib| lib.doctest.as_ref())
                .and_then(toml::Value::as_bool)
                == Some(false);
            if !doctest_disabled {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "library workspace member {member}/Cargo.toml must set [lib] doctest = false"
                    ),
                ));
            }
        }
        verify_exact_case_path_prefix(
            &member_dir,
            Path::new("build.rs"),
            &format!("{member}/build.rs"),
            phase,
        )?;
        if fs::symlink_metadata(member_dir.join("build.rs")).is_ok() {
            return Err(Failure::new(
                1,
                phase,
                format!("disallowed build script {member}/build.rs"),
            ));
        }

        let mut explicit_targets = Vec::new();
        for (section, target) in manifest.all_targets() {
            if let Some(target_path) =
                validate_member_target(member, &member_dir, &member_canon, section, target)?
            {
                explicit_targets.push(target_path);
            }
        }
        verify_trusted_subtree_hygiene(
            "workspace member",
            member,
            &member_dir,
            &member_canon,
            &mut global_lower_paths,
        )?;
        let initial_sources = collect_cargo_target_roots(
            member,
            &member_dir,
            &member_canon,
            pkg_name,
            &manifest,
            explicit_targets,
        )?;
        validate_member_rust_sources(member, &member_dir, &member_canon, initial_sources)?;

        for (section, tbl) in manifest.all_dep_tables() {
            validate_dep_table(
                checkout,
                &checkout_canon,
                member,
                &member_dir,
                &members_set,
                &section,
                tbl,
            )?;
        }
    }

    verify_trusted_subtree_hygiene(
        "trusted tree",
        "trusted",
        &trusted_dir,
        &trusted_canon,
        &mut global_lower_paths,
    )?;
    verify_cargo_lock(checkout, &member_pkg_names)?;
    Ok(())
}

/// Reject `.cargo*` and `rust-toolchain*` overrides at `checkout`, and run
/// [`check_cargo_boundary`], [`verify_upstream_pin`], and (when
/// `require_mir_wp` is enabled) [`verify_bundled_resources`] whenever any
/// Cargo, root-manifest, or vendored Miri TCB path is present.
///
/// Bundle parity follows `require_mir_wp` because the bundle embeds
/// `Trusted.MirAst`, `Trusted.MirSemantics`, and `Anneal.MirWp`: only
/// synthetic unit-test fixtures disable it, and they omit those sources.
/// `anneal-audit` always runs with `require_mir_wp` enabled, so deleting
/// `bundled_resources.rs` (with or without its generator) fails closed.
pub(crate) fn check_checkout_cargo_hygiene(
    checkout: &Path,
    require_mir_wp: bool,
) -> Result<(), Failure> {
    reject_cargo_toolchain_overrides(checkout)?;
    if [
        "Cargo.toml",
        "Cargo.lock",
        "trusted/root-manifest.sha256",
        "trusted/rustc-capture",
        "vendor",
    ]
    .iter()
    .any(|rel| fs::symlink_metadata(checkout.join(rel)).is_ok())
    {
        check_cargo_boundary(checkout)?;
        verify_upstream_pin(&checkout.join("vendor/lean-miri"))?;
        if require_mir_wp {
            verify_bundled_resources(checkout)?;
        }
    }
    Ok(())
}
