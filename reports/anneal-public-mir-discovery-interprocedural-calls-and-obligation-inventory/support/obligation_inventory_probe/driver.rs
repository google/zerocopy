// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Standalone `rustc_driver` probe for exhaustive crate obligation inventory in
//! `rustc 1.99.1 (58cf8f9c35b355199727627d07ae34a4e2846d67)`.
//!
//! Demonstrates that 100% of soundness-bearing crate obligations across
//! (a) `unsafe impl` blocks and impl polarities,
//! (b) ADTs, field visibilities, `#[non_exhaustive]`, and `#[unsafe]` fields,
//! (c) trait default methods and safe trait impls on public types,
//! (d) `Drop::drop` impls, compiler drop glue, and shims, and
//! (e) `static`, `const`, and `Body::required_consts` / `mentioned_items`
//! can be discovered directly from `TyCtxt` queries with zero text parsing.

#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::Safety;
use rustc_hir::def::DefKind;
use rustc_interface::interface::Compiler;
use rustc_middle::ty::{self, GenericArgs, Ty, TyCtxt};

struct ObligationInventoryProbe;

impl Callbacks for ObligationInventoryProbe {
    fn after_analysis(&mut self, _compiler: &Compiler, tcx: TyCtxt<'_>) -> Compilation {
        let eff_vis = tcx.effective_visibilities(());
        let crate_items = tcx.hir_crate_items(());

        println!("=== (A) TRAIT IMPLS, UNSAFE IMPLS, AND POLARITIES ===");
        for local_def_id in crate_items.definitions() {
            let def_id = local_def_id.to_def_id();
            if tcx.def_kind(def_id) != (DefKind::Impl { of_trait: true }) {
                continue;
            }
            let header = tcx.impl_trait_header(def_id);
            let trait_ref = header.trait_ref.skip_binder();
            let trait_def_id = trait_ref.def_id;
            let trait_def = tcx.trait_def(trait_def_id);
            let clauses = tcx.clauses_of(def_id).clauses;
            println!(
                "impl {:?} | trait={:?} (trait_safety={:?}) | impl_safety={:?} | polarity={:?} | self_ty={:?} | clauses={}",
                tcx.def_path_str(def_id),
                tcx.def_path_str(trait_def_id),
                trait_def.safety,
                header.safety,
                header.polarity,
                trait_ref.self_ty(),
                clauses.len(),
            );
        }

        println!("\n=== (B) ADTS, FIELD VISIBILITIES, NON_EXHAUSTIVE, AND #[unsafe] FIELDS ===");
        for local_def_id in crate_items.definitions() {
            let def_id = local_def_id.to_def_id();
            let kind = tcx.def_kind(def_id);
            if !matches!(kind, DefKind::Struct | DefKind::Enum | DefKind::Union) {
                continue;
            }
            let adt_def = tcx.adt_def(def_id);
            let adt_syntactic_pub = tcx.visibility(def_id).is_public();
            let adt_eff_reachable = eff_vis.is_reachable(local_def_id);
            let adt_eff_exported = eff_vis.is_exported(local_def_id);
            let is_non_exhaustive = adt_def.is_variant_list_non_exhaustive()
                || adt_def.variants().iter().any(|v| v.is_field_list_non_exhaustive());

            let mut all_fields_syntactic_pub_safe =
                adt_def.is_struct() && !is_non_exhaustive && adt_syntactic_pub;
            let mut all_fields_eff_reachable_safe =
                adt_def.is_struct() && !is_non_exhaustive && adt_eff_reachable;

            println!(
                "ADT {:?} | kind={:?} | repr_c={} | syn_pub={} | eff_reach={} | eff_exp={} | non_exhaustive={}",
                tcx.def_path_str(def_id),
                adt_def.adt_kind(),
                adt_def.repr().c(),
                adt_syntactic_pub,
                adt_eff_reachable,
                adt_eff_exported,
                is_non_exhaustive,
            );

            for variant in adt_def.variants() {
                for field in &variant.fields {
                    let f_local = field.did.expect_local();
                    let f_syn_pub = field.vis.is_public();
                    let f_eff_reach = eff_vis.is_reachable(f_local);
                    let f_eff_exp = eff_vis.is_exported(f_local);
                    let f_safe = field.safety == Safety::Safe;

                    if !(f_syn_pub && f_safe) {
                        all_fields_syntactic_pub_safe = false;
                    }
                    if !(f_eff_reach && f_safe) {
                        all_fields_eff_reachable_safe = false;
                    }

                    let lean_field_access = if field.safety == Safety::Unsafe {
                        "FieldAccess.unsafeField"
                    } else if f_eff_reach {
                        "FieldAccess.pubSafe"
                    } else {
                        "FieldAccess.priv"
                    };

                    println!(
                        "  field {}::{} | vis={:?} (syn_pub={}, eff_reach={}, eff_exp={}) | safety={:?} -> {}",
                        variant.name,
                        field.name,
                        field.vis,
                        f_syn_pub,
                        f_eff_reach,
                        f_eff_exp,
                        field.safety,
                        lean_field_access,
                    );
                }
            }
            println!(
                "  => allFieldsPubSafe (syntactic)={} | allFieldsPubSafe (effective_reachable)={}",
                all_fields_syntactic_pub_safe, all_fields_eff_reachable_safe,
            );
        }

        println!("\n=== (C) TRAIT DEFAULT METHODS AND SAFE TRAIT IMPLS ON PUBLIC TYPES ===");
        for local_def_id in crate_items.definitions() {
            let impl_def_id = local_def_id.to_def_id();
            if tcx.def_kind(impl_def_id) != (DefKind::Impl { of_trait: true }) {
                continue;
            }
            let header = tcx.impl_trait_header(impl_def_id);
            if header.polarity != ty::ImplPolarity::Positive {
                continue;
            }
            let trait_ref = header.trait_ref.skip_binder();
            let impl_map = tcx.impl_item_implementor_ids(impl_def_id);
            let typing_env = ty::TypingEnv::non_body_analysis(tcx, impl_def_id);

            println!(
                "Trait impl {:?} for {:?}",
                tcx.def_path_str(trait_ref.def_id),
                trait_ref.self_ty(),
            );

            for assoc_item in tcx.associated_items(trait_ref.def_id).in_definition_order() {
                if !assoc_item.is_fn() {
                    continue;
                }
                let overridden_did = impl_map.get(&assoc_item.def_id).copied();
                let resolved_instance =
                    ty::Instance::try_resolve(tcx, typing_env, assoc_item.def_id, trait_ref.args);

                let (resolved_str, mir_phase_str, bb_count) = match resolved_instance {
                    Ok(Some(inst)) => {
                        let body = tcx.instance_mir(inst.def);
                        (
                            format!("{:?}", inst),
                            format!("{:?}", body.phase),
                            body.basic_blocks.len(),
                        )
                    }
                    Ok(None) => ("<polymorphic/unresolved>".to_string(), "N/A".to_string(), 0),
                    Err(e) => (format!("<error: {:?}>", e), "N/A".to_string(), 0),
                };

                println!(
                    "  method {} | trait_item={:?} | local_override={:?} | resolved_instance={} | phase={} | bbs={}",
                    assoc_item.name(),
                    tcx.def_path_str(assoc_item.def_id),
                    overridden_did.map(|d| tcx.def_path_str(d)),
                    resolved_str,
                    mir_phase_str,
                    bb_count,
                );
            }
        }

        println!("\n=== (D) DROP::DROP IMPLS, DROP GLUE, AND COMPILER SHIMS ===");
        for local_def_id in crate_items.definitions() {
            let def_id = local_def_id.to_def_id();
            if !matches!(tcx.def_kind(def_id), DefKind::Struct | DefKind::Enum | DefKind::Union) {
                continue;
            }
            let adt_def = tcx.adt_def(def_id);
            let dtor = adt_def.destructor(tcx);
            let is_polymorphic = tcx.generics_of(def_id).requires_monomorphization(tcx);
            let drop_summary = if !is_polymorphic {
                let adt_ty =
                    Ty::new_adt(tcx, adt_def, GenericArgs::identity_for_item(tcx, def_id));
                let drop_inst = ty::Instance::resolve_drop_glue(tcx, adt_ty);
                let drop_mir = tcx.instance_mir(drop_inst.def);
                format!(
                    "{:?} (phase={:?}, bbs={})",
                    drop_inst.def,
                    drop_mir.phase,
                    drop_mir.basic_blocks.len(),
                )
            } else {
                "<polymorphic ADT: resolve_drop_glue per monomorphization>".to_string()
            };

            println!(
                "ADT {:?} | explicit_dtor={:?} | drop_glue_instance={}",
                tcx.def_path_str(def_id),
                dtor.map(|d| tcx.def_path_str(d.did)),
                drop_summary,
            );
        }

        // Also demonstrate Reify shim and ClosureOnce shim resolution on local items.
        for local_def_id in tcx.mir_keys(()) {
            let def_id = local_def_id.to_def_id();
            let kind = tcx.def_kind(def_id);
            if kind == DefKind::Fn && tcx.def_path_str(def_id) == "top_safe_fn" {
                let reify_def = ty::InstanceKind::Shim(ty::ShimKind::Reify(def_id, None));
                let reify_mir = tcx.instance_mir(reify_def);
                println!(
                    "Shim {:?} | phase={:?} | bbs={}",
                    reify_def,
                    reify_mir.phase,
                    reify_mir.basic_blocks.len(),
                );
            } else if kind == DefKind::Closure {
                let body = tcx.optimized_mir(def_id);
                let ty::TyKind::Closure(_, closure_args) =
                    *tcx.type_of(def_id).skip_binder().kind()
                else {
                    unreachable!()
                };
                let once_shim = ty::Instance::fn_once_adapter_instance(tcx, def_id, closure_args);
                let once_mir = tcx.instance_mir(once_shim.def);
                println!(
                    "Closure {:?} | phase={:?} | bbs={} | fn_once_shim={:?} (phase={:?}, bbs={})",
                    tcx.def_path_str(def_id),
                    body.phase,
                    body.basic_blocks.len(),
                    once_shim.def,
                    once_mir.phase,
                    once_mir.basic_blocks.len(),
                );
            }
        }

        println!(
            "\n=== (E) MIR_KEYS, FN_SIG SAFETY/VISIBILITY, POST_CLEANUP VS MIR_FOR_CTFE VS OPTIMIZED_MIR, REQUIRED_CONSTS, MENTIONED_ITEMS ==="
        );
        for local_def_id in tcx.mir_keys(()) {
            let def_id = local_def_id.to_def_id();
            let kind = tcx.def_kind(def_id);
            let is_trivial = tcx.is_trivial_const(*local_def_id);
            if is_trivial {
                let triv_val = tcx.trivial_const(*local_def_id);
                println!(
                    "mir_key {:?} | kind={:?} | query=trivial_const | val={:?}",
                    tcx.def_path_str(def_id),
                    kind,
                    triv_val,
                );
                continue;
            }

            let use_ctfe = matches!(
                kind,
                DefKind::Const { .. }
                    | DefKind::AssocConst { .. }
                    | DefKind::Static { .. }
                    | DefKind::AnonConst
            );

            // For non-const, non-ctor items, inspect `mir_drops_elaborated_and_const_checked`
            // BEFORE `optimized_mir` steals it, confirming `Runtime(PostCleanup)` availability.
            let post_cleanup_phase = if !use_ctfe && !tcx.is_constructor(def_id) {
                let steal_ref = tcx.mir_drops_elaborated_and_const_checked(*local_def_id);
                if !steal_ref.is_stolen() {
                    let b = steal_ref.borrow();
                    format!("{:?} (bbs={})", b.phase, b.basic_blocks.len())
                } else {
                    "<already stolen>".to_string()
                }
            } else {
                "N/A".to_string()
            };

            let (query_used, body) = if use_ctfe {
                ("mir_for_ctfe", tcx.mir_for_ctfe(def_id))
            } else {
                ("optimized_mir", tcx.optimized_mir(def_id))
            };

            let fn_safety_vis = if matches!(kind, DefKind::Fn | DefKind::AssocFn) {
                let sig = tcx.fn_sig(def_id).skip_binder();
                let reach = eff_vis.is_reachable(*local_def_id);
                let lean_fn_kind = match (reach, sig.safety()) {
                    (true, Safety::Safe) => "FnKind.pubSafe",
                    (true, Safety::Unsafe) => "FnKind.pubUnsafe",
                    (false, _) => "FnKind.priv",
                };
                format!("sig_safety={:?}, eff_reach={} -> {}", sig.safety(), reach, lean_fn_kind)
            } else {
                "N/A".to_string()
            };

            let req_consts: Option<Vec<String>> = body
                .required_consts
                .as_ref()
                .map(|cs| cs.iter().map(|c| format!("{:?}", c.const_)).collect());
            let mentioned: Option<Vec<String>> = body
                .mentioned_items
                .as_ref()
                .map(|ms| ms.iter().map(|m| format!("{:?}", m.node)).collect());

            println!(
                "mir_key {:?} | kind={:?} | {} | post_cleanup={} | query={} | phase={:?} | bbs={} | required_consts={:?} | mentioned_items={:?}",
                tcx.def_path_str(def_id),
                kind,
                fn_safety_vis,
                post_cleanup_phase,
                query_used,
                body.phase,
                body.basic_blocks.len(),
                req_consts,
                mentioned,
            );
        }

        Compilation::Stop
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    rustc_driver::run_compiler(&args, &mut ObligationInventoryProbe);
}
