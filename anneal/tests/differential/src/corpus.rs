// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Differential litmus corpus manifest parser and fail-closed path validator.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Component, Path, PathBuf},
};

use serde::{Deserialize, Serialize};

use crate::verdict::{Expectation, ExpectedMiriOutcome, IntKind, MirValue, OrderingKind};

/// Default location of the Stage-1 Profile v1 corpus manifest relative to the
/// `anneal/` workspace root.
pub const DEFAULT_CORPUS_MANIFEST_REL: &str = "tests/corpora/differential/profile_v1/manifest.toml";

/// Parsed differential corpus manifest paired with its canonical directory.
#[derive(Clone, Debug)]
pub struct LoadedCorpus {
    pub manifest_path: PathBuf,
    pub root_dir: PathBuf,
    pub mir_dialect: String,
    pub cases: Vec<LitmusCase>,
}

/// Validated litmus test case ready for multi-leg execution.
#[derive(Clone, Debug)]
pub struct LitmusCase {
    pub id: String,
    pub source_rel: PathBuf,
    pub source_abs: PathBuf,
    pub function: String,
    pub category: String,
    pub expected: Expectation,
    pub miri_ub_contains: Option<String>,
    pub expected_miri: Option<ExpectedMiriOutcome>,
    pub args: Vec<MirValue>,
    pub expected_return: Option<MirValue>,
    pub fuel: usize,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawManifest {
    schema_version: u32,
    mir_dialect: String,
    #[serde(default)]
    case: Vec<RawCase>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawCase {
    id: String,
    source: String,
    function: String,
    category: String,
    expected: Expectation,
    miri_ub_contains: Option<String>,
    expected_miri: Option<ExpectedMiriOutcome>,
    #[serde(default)]
    args: Vec<RawValueSpec>,
    expected_return: Option<RawValueSpec>,
    #[serde(default = "default_fuel")]
    fuel: usize,
}

const fn default_fuel() -> usize {
    500
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct RawValueSpec {
    kind: String,
    value: Option<String>,
    int_kind: Option<String>,
    int_value: Option<String>,
    overflow: Option<bool>,
    enum_type: Option<String>,
    variant: Option<String>,
    variant_index: Option<usize>,
}

impl RawValueSpec {
    fn reject_unused(&self, kind: &str, allowed: &[&str]) -> Result<(), String> {
        for (name, present) in [
            ("value", self.value.is_some()),
            ("int_kind", self.int_kind.is_some()),
            ("int_value", self.int_value.is_some()),
            ("overflow", self.overflow.is_some()),
            ("enum_type", self.enum_type.is_some()),
            ("variant", self.variant.is_some()),
            ("variant_index", self.variant_index.is_some()),
        ] {
            if present && !allowed.contains(&name) {
                return Err(format!("field `{name}` is not valid for value kind {kind:?}"));
            }
        }
        Ok(())
    }

    fn into_mir_value(self) -> Result<MirValue, String> {
        let kind = self.kind.trim();
        match kind {
            "bool" => {
                self.reject_unused(kind, &["value"])?;
                let raw =
                    self.value.ok_or_else(|| "bool value missing `value` field".to_owned())?;
                match raw.trim() {
                    "true" => Ok(MirValue::Bool { value: true }),
                    "false" => Ok(MirValue::Bool { value: false }),
                    other => Err(format!("invalid bool value {other:?}")),
                }
            }
            "char" => {
                self.reject_unused(kind, &["value"])?;
                let raw =
                    self.value.ok_or_else(|| "char value missing `value` field".to_owned())?;
                let c = parse_char_spec(&raw)?;
                Ok(MirValue::Char { scalar: c as u32 })
            }
            "ordering" => {
                self.reject_unused(kind, &["value"])?;
                let raw =
                    self.value.ok_or_else(|| "ordering value missing `value` field".to_owned())?;
                Ok(MirValue::Ordering { value: OrderingKind::parse(&raw)? })
            }
            "unit" => {
                self.reject_unused(kind, &[])?;
                Ok(MirValue::Unit)
            }
            "overflow_pair" => {
                self.reject_unused(kind, &["int_kind", "int_value", "overflow"])?;
                let kind_raw =
                    self.int_kind.ok_or_else(|| "overflow_pair missing `int_kind`".to_owned())?;
                let val_raw =
                    self.int_value.ok_or_else(|| "overflow_pair missing `int_value`".to_owned())?;
                let overflow =
                    self.overflow.ok_or_else(|| "overflow_pair missing `overflow`".to_owned())?;
                let int_kind = IntKind::parse_rust_name(&kind_raw)?;
                let bits = int_kind.parse_decimal_bits(&val_raw)?;
                Ok(MirValue::OverflowPair { int_kind, bits, overflow })
            }
            "enum" => {
                self.reject_unused(kind, &["enum_type", "variant", "variant_index"])?;
                let enum_type =
                    self.enum_type.ok_or_else(|| "enum missing `enum_type`".to_owned())?;
                let variant = self.variant.ok_or_else(|| "enum missing `variant`".to_owned())?;
                let variant_index =
                    self.variant_index.ok_or_else(|| "enum missing `variant_index`".to_owned())?;
                if enum_type.trim().is_empty() {
                    return Err("enum `enum_type` must not be empty".to_owned());
                }
                if variant.trim().is_empty() {
                    return Err("enum `variant` must not be empty".to_owned());
                }
                validate_ident(&enum_type, "enum_type")?;
                validate_ident(&variant, "variant")?;
                Ok(MirValue::Enum { enum_type, variant, variant_index })
            }
            int_name => {
                self.reject_unused(int_name, &["value"])?;
                let int_kind = IntKind::parse_rust_name(int_name)?;
                let raw =
                    self.value.ok_or_else(|| format!("{int_name} value missing `value` field"))?;
                let bits = int_kind.parse_decimal_bits(&raw)?;
                Ok(MirValue::Int { int_kind, bits })
            }
        }
    }
}

pub fn parse_char_spec(raw: &str) -> Result<char, String> {
    if let Some(hex) = raw.strip_prefix("U+").or_else(|| raw.strip_prefix("0x")) {
        let code = u32::from_str_radix(hex.trim(), 16)
            .map_err(|e| format!("invalid Unicode scalar {raw:?}: {e}"))?;
        return char::from_u32(code)
            .ok_or_else(|| format!("codepoint {raw:?} is not a Unicode scalar value"));
    }
    let mut chars = raw.chars();
    match (chars.next(), chars.next()) {
        (Some(c), None) => Ok(c),
        _ => Err(format!("expected single char or U+XXXX, got {raw:?}")),
    }
}

fn validate_ident(raw: &str, field: &str) -> Result<(), String> {
    let ok = !raw.is_empty() && raw.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
    if !ok {
        return Err(format!("invalid identifier {raw:?} in `{field}`"));
    }
    Ok(())
}

fn record_enum_bijection(
    by_name: &mut BTreeMap<String, BTreeMap<String, usize>>,
    by_index: &mut BTreeMap<String, BTreeMap<usize, String>>,
    val: &MirValue,
) -> Result<(), String> {
    let MirValue::Enum { enum_type, variant, variant_index } = val else {
        return Ok(());
    };
    let name_map = by_name.entry(enum_type.clone()).or_default();
    if let Some(&prev_idx) = name_map.get(variant) {
        if prev_idx != *variant_index {
            return Err(format!(
                "inconsistent enum discriminant for {enum_type}::{variant}: variant_index {variant_index} conflicts with earlier {prev_idx}"
            ));
        }
    } else {
        name_map.insert(variant.clone(), *variant_index);
    }

    let idx_map = by_index.entry(enum_type.clone()).or_default();
    if let Some(prev_variant) = idx_map.get(variant_index) {
        if prev_variant != variant {
            return Err(format!(
                "duplicate enum variant_index {variant_index} for {enum_type}: variant {variant:?} conflicts with earlier {prev_variant:?}"
            ));
        }
    } else {
        idx_map.insert(*variant_index, variant.clone());
    }
    Ok(())
}

fn validate_slug(label: &str, raw: &str) -> Result<(), String> {
    let ok = !raw.is_empty() && raw.bytes().all(|b| matches!(b, b'a'..=b'z' | b'0'..=b'9' | b'_'));
    if !ok {
        return Err(format!("{label} {raw:?} must match `[a-z0-9_]+`"));
    }
    Ok(())
}

fn validate_category(raw: &str) -> Result<(), String> {
    validate_slug("corpus category", raw)
}

fn validate_case_id(raw: &str) -> Result<(), String> {
    validate_slug("corpus case id", raw)
}

/// Load and validate a differential corpus manifest from disk.
pub fn load_manifest(manifest_path: &Path) -> Result<LoadedCorpus, String> {
    let manifest_canon = fs::canonicalize(manifest_path)
        .map_err(|e| format!("cannot resolve manifest {}: {e}", manifest_path.display()))?;
    if fs::symlink_metadata(manifest_path)
        .map_err(|e| format!("stat manifest {}: {e}", manifest_path.display()))?
        .file_type()
        .is_symlink()
    {
        return Err(format!("manifest path must not be a symlink: {}", manifest_path.display()));
    }
    let root_dir = manifest_canon
        .parent()
        .ok_or_else(|| format!("manifest has no parent directory: {}", manifest_canon.display()))?
        .to_path_buf();
    let content = fs::read_to_string(&manifest_canon)
        .map_err(|e| format!("read manifest {}: {e}", manifest_canon.display()))?;
    parse_manifest_str(&content, &manifest_canon, &root_dir)
}

/// Parse manifest TOML against a known `root_dir`, confining every fixture path
/// strictly inside `root_dir` with zero symlinks or parent escapes.
pub fn parse_manifest_str(
    toml_text: &str,
    manifest_path: &Path,
    root_dir: &Path,
) -> Result<LoadedCorpus, String> {
    let raw: RawManifest = toml::from_str(toml_text)
        .map_err(|e| format!("parse TOML manifest {}: {e}", manifest_path.display()))?;
    if raw.schema_version != 1 {
        return Err(format!(
            "unsupported manifest schema_version {} (expected 1)",
            raw.schema_version
        ));
    }
    if raw.mir_dialect != "profile_v1" {
        return Err(format!(
            "unsupported mir_dialect {:?} (expected \"profile_v1\")",
            raw.mir_dialect
        ));
    }
    if raw.case.is_empty() {
        return Err("corpus manifest must declare at least one [[case]]".to_owned());
    }

    let root_canon = fs::canonicalize(root_dir)
        .map_err(|e| format!("canonicalize corpus root {}: {e}", root_dir.display()))?;
    let mut seen_ids = BTreeSet::new();
    let mut enum_variant_to_idx: BTreeMap<String, BTreeMap<String, usize>> = BTreeMap::new();
    let mut enum_idx_to_variant: BTreeMap<String, BTreeMap<usize, String>> = BTreeMap::new();
    let mut cases = Vec::with_capacity(raw.case.len());

    for item in raw.case {
        validate_case_id(&item.id)?;
        if !seen_ids.insert(item.id.clone()) {
            return Err(format!("duplicate corpus case id {:?}", item.id));
        }
        if item.fuel == 0 {
            return Err(format!("case {:?}: fuel must be > 0", item.id));
        }
        validate_ident(&item.function, "function")
            .map_err(|e| format!("case {:?}: {e}", item.id))?;
        validate_category(&item.category).map_err(|e| format!("case {:?}: {e}", item.id))?;
        let (source_rel, source_abs) = confine_relative_source(&root_canon, &item.source)
            .map_err(|e| format!("case {:?}: {e}", item.id))?;

        let args = item
            .args
            .into_iter()
            .map(RawValueSpec::into_mir_value)
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| format!("case {:?} args: {e}", item.id))?;

        let expected_return = item
            .expected_return
            .map(RawValueSpec::into_mir_value)
            .transpose()
            .map_err(|e| format!("case {:?} expected_return: {e}", item.id))?;

        for val in args.iter().chain(expected_return.iter()) {
            record_enum_bijection(&mut enum_variant_to_idx, &mut enum_idx_to_variant, val)
                .map_err(|e| format!("case {:?}: {e}", item.id))?;
        }

        let miri_ub_contains = match item.miri_ub_contains {
            Some(s) => {
                if s.trim().is_empty() || s.contains('\0') {
                    return Err(format!(
                        "case {:?}: miri_ub_contains must be non-empty without NUL",
                        item.id
                    ));
                }
                Some(s)
            }
            None => None,
        };

        match item.expected {
            Expectation::Pass => {
                let Some(exp) = &expected_return else {
                    return Err(format!(
                        "case {:?}: expected = \"pass\" requires `expected_return`",
                        item.id
                    ));
                };
                if matches!(exp, MirValue::Enum { .. }) {
                    return Err(format!(
                        "case {:?}: enum `expected_return` is not supported in Stage 1",
                        item.id
                    ));
                }
                if miri_ub_contains.is_some() {
                    return Err(format!(
                        "case {:?}: non-UB case must not set `miri_ub_contains`",
                        item.id
                    ));
                }
                if item.expected_miri.is_some() {
                    return Err(format!(
                        "case {:?}: `expected_miri` is only supported on `unsupported_control` cases",
                        item.id
                    ));
                }
            }
            Expectation::Ub => {
                if expected_return.is_some() {
                    return Err(format!(
                        "case {:?}: expected = \"ub\" forbids `expected_return`",
                        item.id
                    ));
                }
                if miri_ub_contains.is_none() {
                    return Err(format!(
                        "case {:?}: expected = \"ub\" requires `miri_ub_contains`",
                        item.id
                    ));
                }
                if item.expected_miri.is_some() {
                    return Err(format!(
                        "case {:?}: `expected_miri` is only supported on `unsupported_control` cases",
                        item.id
                    ));
                }
            }
            Expectation::UnsupportedControl => {
                if expected_return.is_some() {
                    return Err(format!(
                        "case {:?}: {:?} forbids `expected_return`",
                        item.id, item.expected
                    ));
                }
                if miri_ub_contains.is_some() {
                    return Err(format!(
                        "case {:?}: {:?} forbids `miri_ub_contains`",
                        item.id, item.expected
                    ));
                }
                if item.expected_miri.is_none() {
                    return Err(format!(
                        "case {:?}: unsupported_control requires expected_miri",
                        item.id
                    ));
                }
            }
        }

        cases.push(LitmusCase {
            id: item.id,
            source_rel,
            source_abs,
            function: item.function,
            category: item.category,
            expected: item.expected,
            miri_ub_contains,
            expected_miri: item.expected_miri,
            args,
            expected_return,
            fuel: item.fuel,
        });
    }

    Ok(LoadedCorpus {
        manifest_path: manifest_path.to_path_buf(),
        root_dir: root_canon,
        mir_dialect: raw.mir_dialect,
        cases,
    })
}

fn confine_relative_source(root_canon: &Path, raw: &str) -> Result<(PathBuf, PathBuf), String> {
    let rel = Path::new(raw);
    if raw.is_empty() || rel.is_absolute() {
        return Err(format!("source must be non-empty relative path, got {raw:?}"));
    }
    let mut cur = root_canon.to_path_buf();
    for comp in rel.components() {
        match comp {
            Component::Normal(seg) => {
                cur.push(seg);
                let meta = fs::symlink_metadata(&cur)
                    .map_err(|e| format!("source component {}: {e}", cur.display()))?;
                if meta.file_type().is_symlink() {
                    return Err(format!(
                        "symlink forbidden in corpus source path: {}",
                        cur.display()
                    ));
                }
            }
            Component::ParentDir
            | Component::CurDir
            | Component::RootDir
            | Component::Prefix(_) => {
                return Err(format!("disallowed path component in corpus source {raw:?}"));
            }
        }
    }
    let abs = fs::canonicalize(&cur)
        .map_err(|e| format!("canonicalize source {}: {e}", cur.display()))?;
    if !abs.starts_with(root_canon) || !abs.is_file() {
        return Err(format!(
            "corpus source {} escapes root or is not a regular file",
            abs.display()
        ));
    }
    Ok((rel.to_path_buf(), abs))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_duplicate_ids_and_path_escapes() {
        let dir = tempfile::tempdir().unwrap();
        let src_dir = dir.path().join("src");
        fs::create_dir_all(&src_dir).unwrap();
        fs::write(src_dir.join("a.rs"), "pub fn f() -> u32 { 1 }\n").unwrap();
        let manifest_path = dir.path().join("manifest.toml");

        let dup = r#"
schema_version = 1
mir_dialect = "profile_v1"
[[case]]
id = "dup"
source = "src/a.rs"
function = "f"
category = "arith"
expected = "pass"
args = []
expected_return = { kind = "u32", value = "1" }
[[case]]
id = "dup"
source = "src/a.rs"
function = "f"
category = "arith"
expected = "pass"
args = []
expected_return = { kind = "u32", value = "1" }
"#;
        let err = parse_manifest_str(dup, &manifest_path, dir.path()).unwrap_err();
        assert!(err.contains("duplicate corpus case id"), "{err}");

        let escape = r#"
schema_version = 1
mir_dialect = "profile_v1"
[[case]]
id = "esc"
source = "../outside.rs"
function = "f"
category = "arith"
expected = "pass"
args = []
expected_return = { kind = "u32", value = "1" }
"#;
        let err = parse_manifest_str(escape, &manifest_path, dir.path()).unwrap_err();
        assert!(err.contains("disallowed path component"), "{err}");
    }

    #[test]
    fn rejects_invalid_ids_unknown_fields_missing_ub_cause_and_enum_return() {
        let dir = tempfile::tempdir().unwrap();
        let src_dir = dir.path().join("src");
        fs::create_dir_all(&src_dir).unwrap();
        fs::write(src_dir.join("a.rs"), "pub fn f() -> u32 { 1 }\n").unwrap();
        let manifest_path = dir.path().join("manifest.toml");

        for bad_id in ["bad:id", "bad id", "bad\tid"] {
            let toml_txt = format!(
                "schema_version = 1\nmir_dialect = \"profile_v1\"\n[[case]]\nid = {:?}\nsource = \"src/a.rs\"\nfunction = \"f\"\ncategory = \"arith\"\nexpected = \"pass\"\nargs = []\nexpected_return = {{ kind = \"u32\", value = \"1\" }}\n",
                bad_id
            );
            let err = parse_manifest_str(&toml_txt, &manifest_path, dir.path()).unwrap_err();
            assert!(err.contains("[a-z0-9_]+"), "{err}");
        }

        let unknown_field = r#"
schema_version = 1
mir_dialect = "profile_v1"
[[case]]
id = "p"
source = "src/a.rs"
function = "f"
category = "arith"
expected = "pass"
allow_conservative_unsupported = true
args = []
expected_return = { kind = "u32", value = "1" }
"#;
        let err = parse_manifest_str(unknown_field, &manifest_path, dir.path()).unwrap_err();
        assert!(err.contains("unknown field"), "{err}");

        let bad_rustc_flags = r#"
schema_version = 1
mir_dialect = "profile_v1"
[[case]]
id = "p2"
source = "src/a.rs"
function = "f"
category = "arith"
expected = "pass"
rustc_flags = ["-Zmiri-disable-validation"]
args = []
expected_return = { kind = "u32", value = "1" }
"#;
        assert!(parse_manifest_str(bad_rustc_flags, &manifest_path, dir.path()).is_err());

        let missing_ub_cause = r#"
schema_version = 1
mir_dialect = "profile_v1"
[[case]]
id = "u"
source = "src/a.rs"
function = "f"
category = "ub"
expected = "ub"
args = []
"#;
        let err = parse_manifest_str(missing_ub_cause, &manifest_path, dir.path()).unwrap_err();
        assert!(err.contains("miri_ub_contains"), "{err}");

        let enum_ret = r#"
schema_version = 1
mir_dialect = "profile_v1"
[[case]]
id = "e"
source = "src/a.rs"
function = "f"
category = "enums"
expected = "pass"
args = []
expected_return = { kind = "enum", enum_type = "E", variant = "A", variant_index = 0 }
"#;
        let err = parse_manifest_str(enum_ret, &manifest_path, dir.path()).unwrap_err();
        assert!(err.contains("enum `expected_return` is not supported"), "{err}");

        let empty_enum_type = r#"
schema_version = 1
mir_dialect = "profile_v1"
[[case]]
id = "e_empty"
source = "src/a.rs"
function = "f"
category = "enums"
expected = "pass"
args = [{ kind = "enum", enum_type = "", variant = "A", variant_index = 0 }]
expected_return = { kind = "u32", value = "1" }
"#;
        assert!(parse_manifest_str(empty_enum_type, &manifest_path, dir.path()).is_err());

        let conflicting_index = r#"
schema_version = 1
mir_dialect = "profile_v1"
[[case]]
id = "e1"
source = "src/a.rs"
function = "f"
category = "enums"
expected = "pass"
args = [{ kind = "enum", enum_type = "MyEnum", variant = "A", variant_index = 0 }]
expected_return = { kind = "u32", value = "1" }
[[case]]
id = "e2"
source = "src/a.rs"
function = "f"
category = "enums"
expected = "pass"
args = [{ kind = "enum", enum_type = "MyEnum", variant = "A", variant_index = 1 }]
expected_return = { kind = "u32", value = "1" }
"#;
        let err = parse_manifest_str(conflicting_index, &manifest_path, dir.path()).unwrap_err();
        assert!(err.contains("inconsistent enum discriminant"), "{err}");

        let duplicate_index = r#"
schema_version = 1
mir_dialect = "profile_v1"
[[case]]
id = "e1"
source = "src/a.rs"
function = "f"
category = "enums"
expected = "pass"
args = [{ kind = "enum", enum_type = "MyEnum", variant = "A", variant_index = 0 }]
expected_return = { kind = "u32", value = "1" }
[[case]]
id = "e2"
source = "src/a.rs"
function = "f"
category = "enums"
expected = "pass"
args = [{ kind = "enum", enum_type = "MyEnum", variant = "B", variant_index = 0 }]
expected_return = { kind = "u32", value = "1" }
"#;
        let err = parse_manifest_str(duplicate_index, &manifest_path, dir.path()).unwrap_err();
        assert!(err.contains("duplicate enum variant_index"), "{err}");

        for bad_id in
            ["", "BadId", "bad-id", "bad_\u{00e9}", "bad/id", "bad\\id", "bad\"id", "bad'id"]
        {
            let toml_txt = format!(
                "schema_version = 1\nmir_dialect = \"profile_v1\"\n[[case]]\nid = {:?}\nsource = \"src/a.rs\"\nfunction = \"f\"\ncategory = \"arith\"\nexpected = \"pass\"\nargs = []\nexpected_return = {{ kind = \"u32\", value = \"1\" }}\n",
                bad_id
            );
            let err = parse_manifest_str(&toml_txt, &manifest_path, dir.path()).unwrap_err();
            assert!(err.contains("[a-z0-9_]+"), "{bad_id}: {err}");
        }

        let unpinned_unsup = r#"
schema_version = 1
mir_dialect = "profile_v1"
[[case]]
id = "unsup_no_pin"
source = "src/a.rs"
function = "f"
category = "unsupported_control"
expected = "unsupported_control"
args = []
"#;
        let err = parse_manifest_str(unpinned_unsup, &manifest_path, dir.path()).unwrap_err();
        assert!(err.contains("unsupported_control requires expected_miri"), "{err}");

        for bad_cat in ["", "Arith", "bad-cat", "bad cat"] {
            let toml_txt = format!(
                "schema_version = 1\nmir_dialect = \"profile_v1\"\n[[case]]\nid = \"c\"\nsource = \"src/a.rs\"\nfunction = \"f\"\ncategory = {:?}\nexpected = \"pass\"\nargs = []\nexpected_return = {{ kind = \"u32\", value = \"1\" }}\n",
                bad_cat
            );
            let err = parse_manifest_str(&toml_txt, &manifest_path, dir.path()).unwrap_err();
            assert!(err.contains("[a-z0-9_]+"), "{err}");
        }

        let extra_val_field = r#"
schema_version = 1
mir_dialect = "profile_v1"
[[case]]
id = "bad_val"
source = "src/a.rs"
function = "f"
category = "arith"
expected = "pass"
args = [{ kind = "u32", value = "1", overflow = true }]
expected_return = { kind = "u32", value = "1" }
"#;
        let err = parse_manifest_str(extra_val_field, &manifest_path, dir.path()).unwrap_err();
        assert!(err.contains("is not valid for value kind"), "{err}");

        let unit_extra_val = r#"
schema_version = 1
mir_dialect = "profile_v1"
[[case]]
id = "bad_unit"
source = "src/a.rs"
function = "f"
category = "arith"
expected = "pass"
args = []
expected_return = { kind = "unit", value = "()" }
"#;
        let err = parse_manifest_str(unit_extra_val, &manifest_path, dir.path()).unwrap_err();
        assert!(err.contains("is not valid for value kind"), "{err}");
    }
}
