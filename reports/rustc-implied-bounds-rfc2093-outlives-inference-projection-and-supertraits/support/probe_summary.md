# Probe Summary: Implied Bounds, RFC 2093, Projection Normalization, and Supertraits

- Compiler: `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`commit-hash: 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`)
- Total checks: `39/39` passed

| Group | Case ID | Compile RC | Result | Key Diagnostic / Stdout |
| :--- | :--- | :---: | :---: | :--- |
| `a_implied_bounds_and_rfc2093_boundaries` | `fn_implied_ref_ok` | `0` | `PASS` | `IMPLIED_FN_OK=1` |
| `a_implied_bounds_and_rfc2093_boundaries` | `fn_implied_return_ok` | `0` | `PASS` | `IMPLIED_RET_OK=1` |
| `a_implied_bounds_and_rfc2093_boundaries` | `struct_ref_rfc2093_ok` | `0` | `PASS` | `RFC2093_STRUCT_OK=1` |
| `a_implied_bounds_and_rfc2093_boundaries` | `struct_mutual_rec_fixpoint_ok` | `0` | `PASS` | `MUTUAL_FIXPOINT_OK=1` |
| `a_implied_bounds_and_rfc2093_boundaries` | `struct_union_enum_rfc2093_ok` | `0` | `PASS` | `UNION_ENUM_OK=1` |
| `a_implied_bounds_and_rfc2093_boundaries` | `struct_ref_impl_inherits_rfc2093_ok` | `0` | `PASS` | `IMPL_INHERIT_OK=1` |
| `a_implied_bounds_and_rfc2093_boundaries` | `struct_static_ref_no_outlives_e0310` | `1` | `PASS` | `error[E0310]: the parameter type `T` may not live long enough` |
| `a_implied_bounds_and_rfc2093_boundaries` | `fn_implied_static_ref_ok` | `0` | `PASS` | `FN_STATIC_OK=1` |
| `a_implied_bounds_and_rfc2093_boundaries` | `impl_for_static_ref_ok` | `0` | `PASS` | `IMPL_STATIC_OK=7` |
| `a_implied_bounds_and_rfc2093_boundaries` | `struct_static_ref_explicit_ok` | `0` | `PASS` | `STATIC_EXPLICIT_OK=1` |
| `a_implied_bounds_and_rfc2093_boundaries` | `struct_nested_static_ref_e0310` | `1` | `PASS` | `error[E0310]: the parameter type `U` may not live long enough` |
| `a_implied_bounds_and_rfc2093_boundaries` | `struct_for_binder_late_bound_ok` | `0` | `PASS` | `LATE_BOUND_OK=1` |
| `a_implied_bounds_and_rfc2093_boundaries` | `struct_proj_allows_assoc_outlives_ok` | `0` | `PASS` | `PROJ_ASSOC_OUTLIVES_OK=1` |
| `a_implied_bounds_and_rfc2093_boundaries` | `struct_proj_rejects_param_outlives_e0309` | `1` | `PASS` | `error[E0309]: the parameter type `T` may not live long enough` |
| `a_implied_bounds_and_rfc2093_boundaries` | `struct_proj_unnormalized_impl_e0309` | `1` | `PASS` | `error[E0309]: the parameter type `T` may not live long enough` |
| `a_implied_bounds_and_rfc2093_boundaries` | `type_alias_unchecked_ok` | `0` | `PASS` | `LAZY_ALIAS_OK=11` |
| `a_implied_bounds_and_rfc2093_boundaries` | `type_alias_unchecked_static_ok` | `0` | `PASS` | `STATIC_ALIAS_UNCHECKED=42` |
| `a_implied_bounds_and_rfc2093_boundaries` | `type_alias_lazy_checked_static_e0310` | `1` | `PASS` | `error[E0310]: the parameter type `T` may not live long enough` |
| `a_implied_bounds_and_rfc2093_boundaries` | `type_alias_lazy_checked_early_ok` | `0` | `PASS` | `CHECKED_ALIAS_OK=12` |
| `a_implied_bounds_and_rfc2093_boundaries` | `trait_impl_for_ref_requires_wf_ok` | `0` | `PASS` | `IMPL_FOR_REF_OK=1` |
| `a_implied_bounds_and_rfc2093_boundaries` | `trait_method_caller_missing_implied_e0309` | `1` | `PASS` | `error[E0309]: the parameter type `T` may not live long enough` |
| `a_implied_bounds_and_rfc2093_boundaries` | `assoc_type_ref_missing_outlives_e0309` | `1` | `PASS` | `error[E0309]: the parameter type `T` may not live long enough` |
| `a_implied_bounds_and_rfc2093_boundaries` | `rfc2093_runs_after_default_object_bound` | `1` | `PASS` | `error: lifetime may not live long enough` |
| `a_implied_bounds_and_rfc2093_boundaries` | `explicit_outlives_changes_default_object_bound_ok` | `0` | `PASS` | `OBJ_DEFAULT_OK=1` |
| `a_implied_bounds_and_rfc2093_boundaries` | `rustc_dump_inferred_outlives_oracle` | `1` | `PASS` | `error: rustc_dump_inferred_outlives` |
| `b_supertrait_elaboration_and_projection_norm` | `supertrait_elaboration_and_norm_ok` | `0` | `PASS` | `SUPERTRAIT_NORM=42` |
| `b_supertrait_elaboration_and_projection_norm` | `trait_param_bound_not_implied_by_filter_e0309` | `1` | `PASS` | `error[E0309]: the parameter type `T` may not live long enough` |
| `b_supertrait_elaboration_and_projection_norm` | `trait_self_outlives_elaborates_ok` | `0` | `PASS` | `SELF_ELAB_OK=1` |
| `b_supertrait_elaboration_and_projection_norm` | `trait_assoc_outlives_elaborates_ok` | `0` | `PASS` | `ASSOC_ELAB_OK=1` |
| `b_supertrait_elaboration_and_projection_norm` | `trait_alias_all_filter_elaborates_ok` | `0` | `PASS` | `TRAIT_ALIAS_ELAB_OK=1` |
| `b_supertrait_elaboration_and_projection_norm` | `diamond_consistent_supertrait_proj_ok` | `0` | `PASS` | `DIAMOND_NORM=99` |
| `b_supertrait_elaboration_and_projection_norm` | `diamond_conflicting_supertrait_proj_e0284` | `1` | `PASS` | `error[E0284]: type annotations needed: cannot satisfy `<Self as Base>::Item == u32`` |
| `b_supertrait_elaboration_and_projection_norm` | `normalized_sig_implies_inner_outlives_ok` | `0` | `PASS` | `NORM_IMPLIED_OK=1` |
| `b_supertrait_elaboration_and_projection_norm` | `struct_where_not_implied_in_impl_e0277` | `1` | `PASS` | `error[E0277]: can't compare `T` with `T`` |
| `c_next_solver_differential` | `next_solver_fn_implied_ref_ok` | `0` | `PASS` | `NEXT_FN_OK=1` |
| `c_next_solver_differential` | `next_solver_static_ref_e0310` | `1` | `PASS` | `error[E0310]: the parameter type `T` may not live long enough` |
| `c_next_solver_differential` | `next_solver_trait_param_bound_e0309` | `1` | `PASS` | `error[E0309]: the parameter type `T` may not live long enough` |
| `c_next_solver_differential` | `next_solver_supertrait_norm_ok` | `0` | `PASS` | `NEXT_SUPERTRAIT_NORM=42` |
| `c_next_solver_differential` | `next_solver_struct_where_not_implied_e0277` | `1` | `PASS` | `error[E0277]: can't compare `T` with `T`` |
