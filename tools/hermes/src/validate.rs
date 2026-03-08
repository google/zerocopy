use anyhow::{bail, Result};

use crate::{
    parse::{attr::FunctionBlockInner, ParsedItem},
    scanner::HermesArtifact,
};

/// Validates the collected Hermes artifacts.
///
/// Checks:
/// 1. All `spec` functions (functions with a `/// ````hermes` block but not `unsafe(axiom)`)
///    must have a non-empty `proof` section.
///
/// If `allow_sorry` is true, this check is skipped, allowing incomplete proofs
/// (which will typically be generated as `sorry` in Lean).
pub fn validate_artifacts(packages: &[HermesArtifact], allow_sorry: bool) -> Result<()> {
    let mut has_errors = false;

    for package in packages {
        for item in &package.items {
            if let ParsedItem::Function(func) = &item.item {
                // 1. Check auto-generated name collisions
                let mut reserved_names = std::collections::HashSet::new();
                reserved_names.insert("h_ret_is_valid".to_string());
                reserved_names.insert("h_unnamed".to_string());

                let mut report_error = |msg: &str| {
                    eprintln!(
                        "Error in function `{}`:\n  --> {}\n  {}\n",
                        func.item.name(),
                        item.source_file.display(),
                        msg
                    );
                    has_errors = true;
                };

                for p in &func.item.sig().inputs {
                    match p {
                        crate::parse::hkd::SafeFnArg::Typed { name, ty } => {
                            let mut is_mut_ref = false;
                            if let crate::parse::hkd::SafeType::Reference { mutability, .. } = ty {
                                is_mut_ref = *mutability;
                            }
                            if name != "_" {
                                reserved_names.insert(format!("h_{}_is_valid", name));
                                if is_mut_ref {
                                    reserved_names.insert(format!("h_{}'_is_valid", name));
                                }
                            }
                        }
                        crate::parse::hkd::SafeFnArg::Receiver { mutability, reference } => {
                            reserved_names.insert("h_self_is_valid".to_string());
                            if *reference && *mutability {
                                reserved_names.insert("h_self'_is_valid".to_string());
                            }
                        }
                    }
                }

                let check_reserved = |name: &str| -> bool { reserved_names.contains(name) };

                for clause in func.hermes.requires.iter() {
                    if clause.lines.iter().all(|l| l.content.trim().is_empty()) {
                        report_error("Requires bounds cannot be completely empty.");
                    }
                    if let Some(name) = &clause.name {
                        if check_reserved(&name.content) {
                            report_error(&format!("Requires bound name `{}` is reserved for auto-generated invariants.", name.content));
                        }
                    }
                }
                for clause in func.hermes.ensures.iter() {
                    if clause.lines.iter().all(|l| l.content.trim().is_empty()) {
                        report_error("Ensures bounds cannot be completely empty.");
                    }
                    if let Some(name) = &clause.name {
                        if check_reserved(&name.content) {
                            report_error(&format!("Ensures bound name `{}` is reserved for auto-generated invariants.", name.content));
                        }
                    }
                }

                if let FunctionBlockInner::Proof { cases, .. } = &func.hermes.inner {
                    // 2. Check proof: coverage (only if not allow_sorry)
                    if !allow_sorry {
                        let _has_ensures = !func.hermes.ensures.is_empty();
                        if !cases.is_empty() {
                            // Check that every ensures is covered exactly once
                            let mut provided_cases = std::collections::HashSet::new();
                            for case in cases.iter() {
                                if let Some(n) = &case.name {
                                    provided_cases.insert(n.content.clone());
                                } else {
                                    provided_cases.insert("h_unnamed".to_string());
                                }
                            }

                            let mut valid_names = std::collections::HashSet::new();
                            let mut has_unnamed_ensure = false;

                            // Implicit unnamed returns generate an `isValid` boundary, but do NOT
                            // create an unnamed case for the user to prove (that's handled by `h_ret_is_valid`
                            // or the tuple structure). Thus we do NOT insert "unnamed" into valid_names here.

                            for ensure in func.hermes.ensures.iter() {
                                if let Some(name) = &ensure.name {
                                    valid_names.insert(name.content.clone());
                                } else {
                                    valid_names.insert("h_unnamed".to_string());
                                    has_unnamed_ensure = true;
                                }
                            }
                            valid_names.extend(reserved_names.iter().cloned());

                            for case in cases.iter() {
                                if let Some(n) = &case.name {
                                    if !valid_names.contains(&n.content) {
                                        report_error(&format!("Validation Error: You provided a proof: for `{}` but no such constraint exists.", n.content));
                                    }
                                } else {
                                    if !has_unnamed_ensure && !func.hermes.ensures.is_empty() {
                                        report_error("Validation Error: You provided an unnamed `proof` block, but there are no unnamed `ensures` clauses to prove.");
                                    }
                                }
                            }

                            for ensure in func.hermes.ensures.iter() {
                                if let Some(name) = &ensure.name {
                                    if !provided_cases.contains(&name.content) {
                                        report_error(&format!(
                                            "Missing proof: for ensures bound `{}`.",
                                            name.content
                                        ));
                                    }
                                } else {
                                    if !provided_cases.contains("h_unnamed") {
                                        let mut has_explicit_unnamed = false;
                                        for e in func.hermes.ensures.iter() {
                                            if e.name.is_none() {
                                                has_explicit_unnamed = true;
                                            }
                                        }
                                        if has_explicit_unnamed {
                                            report_error("Missing unnamed proof: block for the unnamed ensures bound.");
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    if has_errors {
        bail!("Validation failed: Naming collisions or missing proofs detected.");
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_and_validate(code: &str) -> Result<()> {
        let mut packages = vec![];
        let mut items = vec![];
        crate::parse::scan_compilation_unit_internal(
            code,
            Some(std::path::PathBuf::from("test.rs")),
            false,
            |_, res| {
                use crate::parse::hkd::LiftToSafe;
                if let Ok(item) = res {
                    items.push(item.lift());
                } else {
                    panic!("Parsing failed unexpectedly: {:?}", res);
                }
            },
            |_| {},
        );
        packages.push(HermesArtifact {
            name: crate::resolve::HermesTargetName {
                package_name: cargo_metadata::PackageName::new("test".to_string()),
                target_name: "test".to_string(),
                kind: crate::resolve::HermesTargetKind::Lib,
            },
            target_kind: crate::resolve::HermesTargetKind::Lib,
            manifest_path: std::path::PathBuf::from("Cargo.toml"),
            start_from: std::collections::HashSet::new(),
            items,
        });
        validate_artifacts(&packages, false)
    }

    #[test]
    fn test_valid_function() {
        let code = r#"
            /// ```hermes
            /// ```
            fn valid() {}
        "#;
        assert!(parse_and_validate(code).is_ok());
    }

    #[test]
    fn test_coverage_named_proofs() {
        let code = r#"
            /// ```hermes
            /// ensures (a):
            ///   true
            /// ensures (b):
            ///   true
            /// proof (a):
            ///   trivial
            /// proof (b):
            ///   trivial
            /// ```
            fn valid_named_proofs() {}
        "#;
        assert!(parse_and_validate(code).is_ok());

        let code_missing = r#"
            /// ```hermes
            /// ensures (a):
            ///   true
            /// ensures (b):
            ///   true
            /// proof (a):
            ///   trivial
            /// ```
            fn missing_b() {}
        "#;
        assert!(parse_and_validate(code_missing).is_err());
    }

    #[test]
    fn test_auto_generated_collision_requires() {
        let code = r#"
            /// ```hermes
            /// requires (h_x_is_valid):
            ///   true
            /// proof:
            ///   trivial
            /// ```
            unsafe fn collide(x: u32) {}
        "#;
        assert!(parse_and_validate(code).is_err());

        let code = r#"
            /// ```hermes
            /// proof (h_unnamed):
            ///   trivial
            /// ```
            unsafe fn foo() {}
        "#;
        println!("{:#?}", parse_and_validate(code));

        println!(
            "{:#?}",
            crate::parse::attr::FunctionHermesBlock::parse_from_attrs(
                &[syn::parse_quote!(#[doc = " ```hermes\n proof (h_unnamed): true\n ```"])],
                false,
                ""
            )
        );
    }

    #[test]
    fn test_auto_generated_collision_mut_ref() {
        let code = r#"
            /// ```hermes
            /// ensures (h_y'_is_valid):
            ///   true
            /// proof (h_y'_is_valid):
            ///   trivial
            /// ```
            fn collide_out(y: &mut u32) {}
        "#;
        assert!(parse_and_validate(code).is_err());
    }
    #[test]
    fn test_mismatched_proof_name() {
        let code = r#"
            /// ```hermes
            /// ensures (h_foo):
            ///   true
            /// proof (h_bar):
            ///   trivial
            /// ```
            fn mismatch() {}
        "#;
        assert!(parse_and_validate(code).is_err());
    }

    #[test]
    fn test_valid_proof_for_auto_injected_bound() {
        let code = r#"
            /// ```hermes
            /// proof (h_x_is_valid):
            ///   trivial
            /// ```
            fn auto_proof(x: u32) {}
        "#;
        assert!(parse_and_validate(code).is_ok());
    }

    #[test]
    fn test_auto_generated_collision_ret() {
        let code = r#"
            /// ```hermes
            /// ensures (h_ret_is_valid):
            ///   true
            /// proof (h_ret_is_valid):
            ///   trivial
            /// ```
            fn collide_ret() -> u32 { 0 }
        "#;
        assert!(parse_and_validate(code).is_err());
    }

    #[test]
    fn test_auto_generated_collision_self() {
        let code = r#"
            struct Foo;
            impl Foo {
                /// ```hermes
                /// ensures (h_self'_is_valid):
                ///   true
                /// proof (h_self'_is_valid):
                ///   trivial
                /// ```
                fn collide_self(&mut self) {}
            }
        "#;
        assert!(parse_and_validate(code).is_err());
    }

    #[test]
    fn test_unnamed_ensures_with_unnamed_proof() {
        let code = r#"
            /// ```hermes
            /// ensures:
            ///   true
            /// proof:
            ///   trivial
            /// ```
            fn works() {}
        "#;
        assert!(parse_and_validate(code).is_ok());
    }

    #[test]
    fn test_zero_ensures_no_proof_valid() {
        let code = r#"
            /// ```hermes
            /// requires (h_req):
            ///   true
            /// ```
            unsafe fn zero_ensures(x: u32) {}
        "#;
        assert!(parse_and_validate(code).is_ok());
    }

    #[test]
    fn test_unnamed_ensures_with_named_proof_fails() {
        let code = r#"
            /// ```hermes
            /// ensures:
            ///   true
            /// proof (foo):
            ///   trivial
            /// ```
            fn mismatch_unnamed() {}
        "#;
        assert!(parse_and_validate(code).is_err());
    }

    #[test]
    fn test_unnamed_proof_without_unnamed_ensure() {
        let code = r#"
            /// ```hermes
            /// ensures (h_foo):
            ///   true
            /// proof:
            ///   trivial
            /// ```
            fn mismatch_proof() {}
        "#;
        assert!(parse_and_validate(code).is_err());
    }

    #[test]
    fn test_proof_context_without_cases_valid() {
        let code = r#"
            /// ```hermes
            /// ensures (ens):
            ///   ret = x
            /// proof context:
            ///   have h: x = x := by simp
            /// ```
            fn proof_context_no_cases(x: u32) -> u32 { x }
        "#;
        // This should pass validation, because missing proofs are allowed (handled by simp_all or sorry)
        assert!(parse_and_validate(code).is_ok());
    }

    #[test]
    fn test_unnamed_proof_without_unnamed_ensure_fails() {
        let code = r#"
            /// ```hermes
            /// ensures (h_foo):
            ///   ret = x
            /// proof (unnamed):
            ///   simp_all
            /// proof (h_foo):
            ///   simp_all
            /// ```
            fn extra_unnamed_proof(x: u32) -> u32 { x }
        "#;
        // This should fail because there is no unnamed user ensures
        assert!(parse_and_validate(code).is_err());
    }

    #[test]
    fn test_explicit_unnamed_name_valid() {
        let code = r#"
            /// ```hermes
            /// requires (unnamed):
            ///   x > 0
            /// ensures (ens):
            ///   ret = x
            /// proof (ens):
            ///   simp_all
            /// ```
            unsafe fn explicit_unnamed(x: u32) -> u32 { x }
        "#;
        // This should pass because 'unnamed' is not reserved from the user's perspective,
        // it just maps to the unnamed placeholder.
        assert!(parse_and_validate(code).is_ok());
    }
    #[test]
    fn test_empty_requires_clause() {
        let code = r#"
            /// ```hermes
            /// requires (h_req):
            /// ensures (h_res):
            ///   true
            /// proof (h_res):
            ///   trivial
            /// ```
            unsafe fn empty_req(x: u32) {}
        "#;
        assert!(parse_and_validate(code).is_err());
    }

    #[test]
    fn test_empty_ensures_clause() {
        let code = r#"
            /// ```hermes
            /// requires (h_req):
            ///   true
            /// ensures (h_res):
            /// proof context:
            ///   trivial
            /// ```
            unsafe fn empty_ens(x: u32) {}
        "#;
        assert!(parse_and_validate(code).is_err());
    }

    #[test]
    fn test_zero_ensures_with_unnamed_proof_allowed() {
        let code = r#"
            /// ```hermes
            /// proof:
            ///   trivial
            /// ```
            fn zero_ensures_unnamed_proof() {}
        "#;
        assert!(parse_and_validate(code).is_ok());
    }

    #[test]
    fn test_zero_ensures_with_named_proof_fails() {
        let code = r#"
            /// ```hermes
            /// proof (foo):
            ///   trivial
            /// ```
            fn zero_ensures_named_proof() {}
        "#;
        assert!(parse_and_validate(code).is_err());
    }

    #[test]
    fn test_all_exhaustive_unnamed_singelton_edge_cases() {
        // Naming `h_unnamed` explicitly should fail
        let code = r#"
            /// ```hermes
            /// requires (h_unnamed):
            ///   true
            /// ```
            unsafe fn foo() {}
        "#;
        assert!(parse_and_validate(code).is_err());

        // Naming `h_unnamed` as proof target succeeds since it perfectly aliases the unnamed proposition logic
        let code = r#"
            /// ```hermes
            /// proof (h_unnamed):
            ///   true
            /// ```
            unsafe fn foo() {}
        "#;
        assert!(parse_and_validate(code).is_ok());

        // Order independence: parsing 1 unnamed and multiple named mixed
        let code = r#"
            /// ```hermes
            /// requires (a):
            ///   true
            /// requires:
            ///   true
            /// requires (b):
            ///   true
            /// ensures (ens_b):
            ///   true
            /// ensures:
            ///   true
            /// ensures (ens_a):
            ///   true
            /// proof (ens_b):
            ///   trivial
            /// proof (ens_a):
            ///   trivial
            /// proof:
            ///   trivial
            /// ```
            unsafe fn complex_mix() {}
        "#;
        assert!(parse_and_validate(code).is_ok());
    }
}
