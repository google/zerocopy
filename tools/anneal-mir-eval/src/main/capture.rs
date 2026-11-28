// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Capture loading, body selection, and evaluation configuration.

use std::fs;

use anneal_mir_eval::{CaptureInput, EvalConfig, Program, TargetEndian};

use super::ProfileOverride;

pub(super) struct LoadedCapture {
    pub(super) program: Program,
    pub(super) manifest_endian: Option<TargetEndian>,
    pub(super) from_manifest: bool,
}

pub(super) fn load_capture(path: &str) -> Result<LoadedCapture, String> {
    let raw = fs::read_to_string(path).map_err(|err| format!("failed to read '{path}': {err}"))?;
    let input = CaptureInput::from_json_str(&raw)?;
    let (manifest_endian, from_manifest) = match input.manifest() {
        Some(m) => {
            let endian =
                TargetEndian::from_manifest_str(&m.configuration.endian).ok_or_else(|| {
                    format!(
                        "unsupported manifest configuration.endian '{}'",
                        m.configuration.endian
                    )
                })?;
            (Some(endian), true)
        }
        None => (None, false),
    };
    Ok(LoadedCapture { program: input.into_program(), manifest_endian, from_manifest })
}

pub(super) fn resolve_body_id(
    program: &Program,
    from_manifest: bool,
    selector: Option<&str>,
) -> Result<usize, String> {
    match selector {
        None => {
            if from_manifest && program.bodies.len() != 1 {
                return Err(format!(
                    "capture manifest contains {} bodies; pass --body <idx|identity>",
                    program.bodies.len()
                ));
            }
            let idx = program.entry_def_id as usize;
            if idx < program.bodies.len() {
                Ok(idx)
            } else {
                Err(format!("default entry_def_id {idx} out of bounds"))
            }
        }
        Some(sel) => {
            if let Ok(idx) = sel.parse::<usize>() {
                if idx < program.bodies.len() {
                    return Ok(idx);
                }
                return Err(format!(
                    "body index {idx} out of bounds (len={})",
                    program.bodies.len()
                ));
            }
            if let Some(exact) = program.bodies.iter().position(|b| b.identity == sel) {
                return Ok(exact);
            }
            let suffix_matches: Vec<usize> = program
                .bodies
                .iter()
                .enumerate()
                .filter_map(|(i, b)| {
                    (b.identity.strip_prefix("rust-path-v1::") == Some(sel)).then_some(i)
                })
                .collect();
            match suffix_matches.as_slice() {
                [only] => Ok(*only),
                [] => Err(format!("no body matching '{sel}'")),
                _ => Err(format!("ambiguous body selector '{sel}'")),
            }
        }
    }
}

pub(super) fn build_config(
    program: &Program,
    endian_override: Option<TargetEndian>,
    manifest_endian: Option<TargetEndian>,
    profile_override: ProfileOverride,
) -> Result<EvalConfig, anneal_mir_eval::FaultDetail> {
    let mut cfg = match profile_override {
        ProfileOverride::Auto => {
            let effective_v2_endian = endian_override.or(manifest_endian);
            EvalConfig::for_program(program, effective_v2_endian)?
        }
        ProfileOverride::StrictV1 => EvalConfig::profile_v1(),
        ProfileOverride::ProfileV2 => {
            let endian = endian_override.or(manifest_endian).unwrap_or(TargetEndian::Little);
            if endian != TargetEndian::Little {
                return Err(anneal_mir_eval::FaultDetail::unsupported(
                    "Profile v2 only supports little-endian targets \
                     (Trusted.MirSemantics.profileV2TargetEndian)",
                ));
            }
            EvalConfig::profile_v2(TargetEndian::Little)
        }
    };
    if let Some(endian) = endian_override {
        if cfg.enable_profile_v2() && endian != TargetEndian::Little {
            return Err(anneal_mir_eval::FaultDetail::unsupported(
                "Profile v2 only supports little-endian targets \
                 (Trusted.MirSemantics.profileV2TargetEndian)",
            ));
        }
        cfg.endian = endian;
    }
    Ok(cfg)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn manifest_endian_and_body_selection_contracts() {
        let v1_prog = Program {
            scope: anneal_mir_eval::Scope::Crate,
            bodies: Vec::new(),
            entry_def_id: 0,
            pointer_width_bits: 64,
            overflow_checks: false,
            panic: anneal_mir_eval::PanicStrategy::Unwind,
            has_local_panic_handler: true,
            mir_profile_version: 1,
        };
        let v2_prog = Program { mir_profile_version: 2, ..v1_prog.clone() };

        // Profile v2 fails closed on big-endian manifests or overrides.
        assert!(
            build_config(&v2_prog, None, Some(TargetEndian::Big), ProfileOverride::Auto).is_err()
        );
        assert!(
            build_config(
                &v2_prog,
                Some(TargetEndian::Big),
                Some(TargetEndian::Little),
                ProfileOverride::ProfileV2,
            )
            .is_err()
        );

        let cfg_little =
            build_config(&v2_prog, None, Some(TargetEndian::Little), ProfileOverride::Auto)
                .unwrap();
        assert_eq!(cfg_little.endian, TargetEndian::Little);
        assert!(cfg_little.enable_profile_v2());

        let cfg_override = build_config(
            &v2_prog,
            Some(TargetEndian::Little),
            Some(TargetEndian::Big),
            ProfileOverride::ProfileV2,
        )
        .unwrap();
        assert_eq!(cfg_override.endian, TargetEndian::Little);

        let cfg_v1 =
            build_config(&v1_prog, None, Some(TargetEndian::Little), ProfileOverride::Auto)
                .unwrap();
        assert_eq!(cfg_v1.endian, TargetEndian::Big);
        assert!(cfg_v1.is_strict_profile_v1());

        struct TempDir(std::path::PathBuf);
        impl Drop for TempDir {
            fn drop(&mut self) {
                let _ = fs::remove_dir_all(&self.0);
            }
        }
        let dir = {
            let mut attempt = 0u64;
            loop {
                let candidate = std::env::temp_dir()
                    .join(format!("anneal-mir-eval-main-unit-{}-{attempt}", std::process::id()));
                match fs::create_dir(&candidate) {
                    Ok(()) => break TempDir(candidate),
                    Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => attempt += 1,
                    Err(e) => panic!("create temp dir {candidate:?}: {e}"),
                }
            }
        };
        let manifest_path = dir.0.join("manifest.json");
        let body_json = |id: &str| {
            format!(
                r#"{{
                    "arg_count": 0,
                    "is_unsafe": false,
                    "identity": "{id}",
                    "local_tys": [{{ "kind": "unit" }}],
                    "blocks": [{{ "statements": [], "terminator": {{ "kind": "ret" }} }}]
                }}"#
            )
        };
        let manifest_json = |endian: &str, two_bodies: bool| {
            let bodies = if two_bodies {
                format!("{}, {}", body_json("demo::one"), body_json("demo::two"))
            } else {
                body_json("demo::one")
            };
            format!(
                r#"{{
                    "schema_version": 5,
                    "compiler": {{
                        "commit": "deadbeef",
                        "version": "1.100.0",
                        "sysroot": "/sysroot",
                        "rustc_sha256": "{h}",
                        "driver": {{
                            "linkage": "dynamic_dso",
                            "driver_sha256": "{h}",
                            "dso_digests": {{}}
                        }}
                    }},
                    "configuration": {{
                        "crate_root": "src/lib.rs",
                        "crate_name": "demo",
                        "crate_type": "lib",
                        "panic": "unwind",
                        "edition": "2024",
                        "target": "x86_64-unknown-linux-gnu",
                        "cfg": [],
                        "env": {{}},
                        "opt_level": 0,
                        "debug_assertions": false,
                        "overflow_checks": true,
                        "mir_preserve_ub": true,
                        "pointer_bits": 64,
                        "endian": "{endian}",
                        "declared_source_files": ["src/lib.rs"]
                    }},
                    "source_files": [],
                    "census": [],
                    "selected": [],
                    "unsupported": [],
                    "program": {{
                        "scope": {{ "kind": "crate" }},
                        "overflow_checks": true,
                        "mir_profile_version": 1,
                        "bodies": [{bodies}]
                    }}
                }}"#,
                h = "a".repeat(64)
            )
        };

        fs::write(&manifest_path, manifest_json("big", true)).unwrap();
        let loaded = load_capture(manifest_path.to_str().unwrap()).unwrap();
        assert_eq!(loaded.manifest_endian, Some(TargetEndian::Big));
        assert!(loaded.from_manifest);
        assert!(loaded.program.overflow_checks);
        assert!(resolve_body_id(&loaded.program, loaded.from_manifest, None).is_err());
        assert_eq!(
            resolve_body_id(&loaded.program, loaded.from_manifest, Some("demo::two")).unwrap(),
            1
        );

        fs::write(&manifest_path, manifest_json("pdp", false)).unwrap();
        assert!(load_capture(manifest_path.to_str().unwrap()).is_err());
    }
}
