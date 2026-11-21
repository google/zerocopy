# Monomorphization, Vtable Layout, and Trait Upcasting Probe Summary

- **Compiler:** `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`commit-hash: 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `LLVM version: 22.1.6`, `host: x86_64-unknown-linux-gnu`)
- **Checks passed:** `38 / 38`

| Check | Passed |
| :--- | :--- |
| `cgu::intra_crate_duplicate_private_vtables` | `True` |
| `cgu::o0_localcopy_internalized_and_cross_cgu_external` | `True` |
| `cgu::zero_linkonce_odr_emissions` | `True` |
| `cli::print_mono_items_requires_bool` | `True` |
| `limits::enforce_type_length_limit_flag_triggers_type_length_error` | `True` |
| `limits::poly_recursion_hits_recursion_limit` | `True` |
| `limits::type_length_limit_not_enforced_by_default` | `True` |
| `llvm_ir::copy_diamond_vtable_null_drop_and_trait_vptr` | `True` |
| `llvm_ir::drop_diamond_vtable_nonnull_drop_and_trait_vptr` | `True` |
| `llvm_ir::dyn_drop_glue_null_checks_slot_0` | `True` |
| `llvm_ir::empty_marker_has_no_trait_vptr` | `True` |
| `llvm_ir::upcast_d_to_b_loads_offset_48_invariant_nonnull` | `True` |
| `llvm_ir::vacant_slot_is_undef` | `True` |
| `llvm_ir::zero_cost_upcast_b_to_base` | `True` |
| `llvm_ir::zero_cost_upcast_d_to_a` | `True` |
| `llvm_ir::zero_cost_upcast_d_to_base` | `True` |
| `llvm_ir::zero_cost_upcast_empty_to_sec` | `True` |
| `llvm_ir::zero_cost_upcast_erase_principal` | `True` |
| `llvm_ir::zero_cost_upcast_single_base` | `True` |
| `llvm_ir::zero_cost_upcast_single_mid` | `True` |
| `mir::post_cleanup_dumps_captured` | `True` |
| `sep::cross_crate_duplicate_private_vtables` | `True` |
| `sep::share_generics_no_reinstantiates_default_but_still_reuses_inline_never` | `True` |
| `sep::share_generics_yes_reuses_upstream_poly_default_u64` | `True` |
| `shims::all_instance_kinds_collected_in_lazy` | `True` |
| `shims::compile_lazy_eager_ir` | `True` |
| `shims::eager_adds_dead_fn_unused_drop_and_default_trait_method` | `True` |
| `shims::link_dead_code_disables_internalization` | `True` |
| `shims::runtime_values_and_track_caller_lines` | `True` |
| `vtable::auto_trait_erase_prefix_reuse` | `True` |
| `vtable::compile_bin` | `True` |
| `vtable::compile_llvm_ir` | `True` |
| `vtable::diamond_prefix_vs_secondary_vptr` | `True` |
| `vtable::drop_dispatch_through_upcasted_boxes` | `True` |
| `vtable::empty_marker_prefix_reuse` | `True` |
| `vtable::native_exit_zero` | `True` |
| `vtable::single_chain_prefix_reuse` | `True` |
| `vtable::vacant_always_dispatch` | `True` |
