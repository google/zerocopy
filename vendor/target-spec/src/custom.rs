// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Parse custom platforms.

use std::borrow::Cow;

use cfg_expr::targets::{
    Abi, Arch, Env, Families, Family, HasAtomic, HasAtomics, Os, TargetInfo, Triple, Vendor,
};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Deserialize, Serialize, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[serde(rename_all = "kebab-case")]
pub(crate) struct TargetDefinition {
    // TODO: it would be nice to use target-spec-json for this, but that has a
    // few limitations as of v0.1:
    //
    // * target-pointer-width is a string before roughly nightly-2025-10-12 (it
    //   was changed to an integer after that).
    // * Os and Env deserialized to enums, but we would really like them to be strings.
    //
    // ---
    arch: String,
    #[serde(rename = "target-pointer-width", with = "target_pointer_width")]
    pointer_width: u8,

    // These parameters are not used by target-spec but are mandatory in Target, so we require them
    // here. https://doc.rust-lang.org/nightly/nightly-rustc/rustc_target/spec/struct.Target.html
    #[allow(dead_code)]
    llvm_target: String,
    #[allow(dead_code)]
    data_layout: String,

    // These are optional parameters used by target-spec.
    #[serde(default)]
    os: Option<String>,
    #[serde(default)]
    abi: Option<String>,
    #[serde(default)]
    env: Option<String>,
    #[serde(default)]
    vendor: Option<String>,
    #[serde(default)]
    target_family: Vec<String>,
    #[serde(default)]
    target_endian: Endian,
    #[serde(default)]
    min_atomic_width: Option<u16>,
    #[serde(default)]
    max_atomic_width: Option<u16>,
    #[serde(default)]
    panic_strategy: Option<String>,
}

impl TargetDefinition {
    pub(crate) fn into_target_info(self, triple: Cow<'static, str>) -> TargetInfo {
        // Per https://doc.rust-lang.org/nightly/nightly-rustc/src/rustc_target/spec/mod.rs.html,
        // the default value for min_atomic_width is 8.
        let min_atomic_width = self.min_atomic_width.unwrap_or(8);
        // The default max atomic width is the pointer width.
        let max_atomic_width = self.max_atomic_width.unwrap_or(self.pointer_width as u16);

        let mut has_atomics = Vec::new();
        // atomic_width should always be a power of two, but rather than checking that we just
        // start counting up from 8.
        let mut atomic_width = 8;
        while atomic_width <= max_atomic_width {
            if atomic_width < min_atomic_width {
                atomic_width *= 2;
                continue;
            }
            has_atomics.push(HasAtomic::IntegerSize(atomic_width));
            if atomic_width == self.pointer_width as u16 {
                has_atomics.push(HasAtomic::Pointer);
            }
            atomic_width *= 2;
        }

        let panic_strategy = match self.panic_strategy {
            None => cfg_expr::targets::Panic::unwind,
            Some(s) => cfg_expr::targets::Panic::new(s),
        };

        TargetInfo {
            triple: Triple::new(triple),
            os: self.os.map(Os::new),
            abi: self.abi.map(Abi::new),
            arch: Arch::new(self.arch),
            env: self.env.map(Env::new),
            vendor: self.vendor.map(Vendor::new),
            families: Families::new(self.target_family.into_iter().map(Family::new)),
            pointer_width: self.pointer_width,
            endian: self.target_endian.to_cfg_expr(),
            has_atomics: HasAtomics::new(has_atomics),
            panic: panic_strategy,
        }
    }
}

mod target_pointer_width {
    use serde::{Deserializer, Serializer};

    pub(super) fn deserialize<'de, D>(deserializer: D) -> Result<u8, D::Error>
    where
        D: Deserializer<'de>,
    {
        use std::fmt;

        struct PointerWidthVisitor;

        impl<'de> serde::de::Visitor<'de> for PointerWidthVisitor {
            type Value = u8;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a string or integer representing pointer width")
            }

            fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                value
                    .try_into()
                    .map_err(|_| E::custom(format!("pointer width {value} out of range for u8")))
            }

            fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                value
                    .parse::<u8>()
                    .map_err(|error| E::custom(format!("error parsing as integer: {error}")))
            }
        }

        deserializer.deserialize_any(PointerWidthVisitor)
    }

    pub(super) fn serialize<S>(value: &u8, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        // Should change this in the future to serialize as an integer?
        serializer.serialize_str(&value.to_string())
    }
}

#[derive(
    Copy, Clone, Debug, Deserialize, Serialize, Default, Eq, Hash, Ord, PartialEq, PartialOrd,
)]
#[serde(rename_all = "kebab-case")]
enum Endian {
    #[default]
    Little,
    Big,
}

impl Endian {
    fn to_cfg_expr(self) -> cfg_expr::targets::Endian {
        match self {
            Self::Little => cfg_expr::targets::Endian::little,
            Self::Big => cfg_expr::targets::Endian::big,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{collections::BTreeMap, process::Command};

    #[derive(Deserialize)]
    #[serde(transparent)]
    struct AllTargets(BTreeMap<String, TargetDefinition>);

    #[test]
    fn test_all_builtin_specs_recognized() {
        let rustc_bin: String = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_owned());
        let output = Command::new(rustc_bin)
            // Used for -Zunstable-options. This is test-only code so it doesn't matter.
            .env("RUSTC_BOOTSTRAP", "1")
            .args(["-Z", "unstable-options", "--print", "all-target-specs-json"])
            .output()
            .expect("rustc command succeeded");
        assert!(output.status.success(), "rustc command succeeded");

        let all_targets: AllTargets = serde_json::from_slice(&output.stdout)
            .expect("deserializing all-target-specs-json succeeded");
        for (triple, target_def) in all_targets.0 {
            eprintln!("*** testing {triple}");
            // Just make sure this doesn't panic. (If this becomes fallible in the future, then this
            // shouldn't return an error either.)
            target_def.clone().into_target_info(triple.clone().into());
            let json =
                serde_json::to_string(&target_def).expect("target def serialized successfully");
            eprintln!("* minified json: {json}");
            let target_def_2 = serde_json::from_str(&json).expect("target def 2 deserialized");
            assert_eq!(target_def, target_def_2, "matches");

            // Do some spot checks for things like big-endian targets.
            if triple.starts_with("powerpc-") || triple.starts_with("powerpc64-") {
                assert_eq!(
                    target_def.target_endian,
                    Endian::Big,
                    "powerpc is big-endian"
                );
            }
            if triple.contains("-linux") {
                assert!(
                    target_def.target_family.contains(&"unix".to_owned()),
                    "linux target_family should contain unix (was {:#?})",
                    target_def.target_family,
                );
            }
        }
    }
}
