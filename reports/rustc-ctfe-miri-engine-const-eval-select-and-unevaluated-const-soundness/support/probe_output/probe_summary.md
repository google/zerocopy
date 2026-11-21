# Live `rustc` & Miri CTFE / `const_eval_select` / GVN Probe Summary

- **Compiler:** `rustc 1.98.0-nightly (14210df0e 2026-05-31)`
- **Checks passed:** `21 / 21`
- **Miri available:** `True`

| # | Check | Result |
|---:|:---|:---:|
| 1 | `s1::compile_and_run_o0_o3_parity` | PASS |
| 2 | `s1::postcleanup_preserves_const_eval_select_both_arms` | PASS |
| 3 | `s1::mir_for_ctfe_remaps_to_const_arm_with_ctfe_limit` | PASS |
| 4 | `s1::runtime_optimized_remaps_to_rt_arm_even_at_o0` | PASS |
| 5 | `s1::implicit_promotion_emits_two_promoted_bodies_and_skips_fallible_dead_div` | PASS |
| 6 | `s1::polymorphic_unevaluated_const_persists_while_inline_const_folds_at_o3` | PASS |
| 7 | `s2::guaranteed_eq_static_vs_const_memory_in_ctfe` | PASS |
| 8 | `s2::is_val_statically_known_flips_0_to_1_between_o0_and_o3_after_inlining` | PASS |
| 9 | `s2::mir_gvn_folds_scalar_unevaluated_const_but_preserves_ptr_expose_provenance` | PASS |
| 10 | `s2::llvm_ir_emits_llvm_is_constant_at_o0_and_folds_away_at_o3` | PASS |
| 11 | `s3::frozen_static_is_llvm_constant_while_unsafecell_static_is_mutable_global` | PASS |
| 12 | `s3::const_unsafecell_not_promoted_and_fresh_per_use_plus_zst_cell_ref` | PASS |
| 13 | `s4::unsound_const_eval_select_diverges_between_ctfe_and_runtime_without_error` | PASS |
| 14 | `s4::non_invariant_ivsk_violates_o0_vs_o3_refinement` | PASS |
| 15 | `s5::const_check_and_ctfe_reject_ptr_to_int_cast_and_ptr_byte_load` | PASS |
| 16 | `s5::const_check_rejects_raw_pointer_relational_comparison` | PASS |
| 17 | `s5::ctfe_validation_rejects_inner_unsafecell_behind_const_ref` | PASS |
| 18 | `s5::uninstantiated_failing_assoc_const_succeeds_until_monomorphized_even_in_dead_branch` | PASS |
| 19 | `s6::miri_permissive_executes_ptr_roundtrip_ces_divergence_and_nondet_ivsk_across_seeds` | PASS |
| 20 | `s6::miri_strict_provenance_rejects_int_to_ptr_and_catches_rodata_unsafecell_write_ub` | PASS |
| 21 | `census::sysroot_const_eval_select_32_sites_and_ivsk_sites_classified` | PASS |
