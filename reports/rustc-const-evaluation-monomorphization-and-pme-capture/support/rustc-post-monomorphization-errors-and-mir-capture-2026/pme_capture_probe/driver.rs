// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_interface::interface::Compiler;
use rustc_middle::middle::privacy::Level;
use rustc_middle::mir::{Body, Const, MentionedItem};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::def_id::LocalDefId;

/// WS4 5-rule predicate identifying whether `def_id` is an external entry point
/// callable from outside the crate without going through an internal call site.
pub fn is_external_entry_fn(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    let eff_vis = tcx.effective_visibilities(());

    // Rule 1: Direct, re-exported, or signature-reachable public items.
    if eff_vis.is_reachable(def_id) {
        return true;
    }

    // Rule 2: Executable entry point (`fn main` or `#[start]`).
    if tcx.entry_fn(()).and_then(|(id, _)| id.as_local()) == Some(def_id) {
        return true;
    }

    // Rule 3: FFI / custom symbol export (`#[no_mangle]`, `#[export_name]`, EII).
    let kind = tcx.def_kind(def_id);
    if kind.has_codegen_attrs() {
        let attrs = tcx.codegen_fn_attrs(def_id);
        if attrs.contains_extern_indicator()
            || !attrs.foreign_item_symbol_aliases.is_empty()
        {
            return true;
        }
    }

    // Rule 4: Associated functions in `impl Trait for Type` where `Trait` is
    // foreign or publicly reachable.
    if kind == DefKind::AssocFn {
        let parent_id = tcx.local_parent(def_id);
        if matches!(tcx.def_kind(parent_id), DefKind::Impl { of_trait: true }) {
            let trait_def_id = tcx.impl_trait_id(parent_id.to_def_id());
            let trait_is_public = !trait_def_id.is_local()
                || eff_vis.is_reachable(trait_def_id.expect_local());
            if trait_is_public {
                return true;
            }
        }
    }

    // Rule 5: Closures (or synthetic coroutine bodies) that escape a reachable
    // enclosing item via `impl Trait`.
    if tcx.is_closure_like(def_id.to_def_id()) {
        let root_owner = tcx.typeck_root_def_id_local(def_id);
        if root_owner != def_id
            && is_external_entry_fn(tcx, root_owner)
            && eff_vis.is_public_at_level(def_id, Level::ReachableThroughImplTrait)
        {
            return true;
        }
    }

    false
}

fn format_mir_blocks(body: &Body<'_>) -> String {
    let mut out = String::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        out.push_str(&format!("    {:?}: {{\n", bb));
        for stmt in &data.statements {
            out.push_str(&format!("      {:?};\n", stmt.kind));
        }
        if let Some(ref term) = data.terminator {
            out.push_str(&format!("      {:?};\n", term.kind));
        }
        out.push_str("    }\n");
    }
    out
}

struct PmeCaptureCallbacks;

impl Callbacks for PmeCaptureCallbacks {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        let mir_keys = tcx.mir_keys(());
        println!("=== PME CAPTURE PROBE: mir_keys count = {} ===\n", mir_keys.len());

        // First list all mir_keys with their DefKind
        println!("--- 1. All LocalDefIds in tcx.mir_keys(()) ---");
        for &local_id in mir_keys.iter() {
            let def_id = local_id.to_def_id();
            let kind = tcx.def_kind(def_id);
            let const_ctx = tcx.hir_body_const_context(local_id);
            println!(
                "  - {:<62} | kind={:<12?} | const_ctx={:?}",
                tcx.def_path_str(def_id),
                kind,
                const_ctx
            );
        }
        println!();

        // Now iterate over callable runtime functions in mir_keys
        println!("--- 2. Per-Function Extraction (Runtime(PostCleanup) vs Optimized) ---");
        for &local_id in mir_keys.iter() {
            let def_id = local_id.to_def_id();
            let kind = tcx.def_kind(def_id);
            if !matches!(kind, DefKind::Fn | DefKind::AssocFn) {
                continue;
            }
            if tcx.hir_body_const_context(local_id).is_some() {
                continue;
            }

            let path = tcx.def_path_str(def_id);
            let is_public = is_external_entry_fn(tcx, local_id);
            let sig = tcx.fn_sig(def_id).skip_binder();
            let is_safe = sig.safety().is_safe();

            // 1. Borrow Runtime(PostCleanup) MIR BEFORE calling tcx.optimized_mir(def_id)
            //    because optimized_mir steals mir_drops_elaborated_and_const_checked!
            let (post_cleanup_phase, post_cleanup_bb_count, post_cleanup_blocks_str, req_consts) = {
                let post_cleanup_body =
                    tcx.mir_drops_elaborated_and_const_checked(local_id).borrow();
                let req = post_cleanup_body.required_consts().to_vec();
                (
                    post_cleanup_body.phase,
                    post_cleanup_body.basic_blocks.len(),
                    format_mir_blocks(&post_cleanup_body),
                    req,
                )
            };

            // 2. Now query tcx.optimized_mir(def_id) to compare blocks and read mentioned_items()
            let opt_body = tcx.optimized_mir(def_id);
            let opt_phase = opt_body.phase;
            let opt_bb_count = opt_body.basic_blocks.len();
            let opt_blocks_str = format_mir_blocks(opt_body);
            let mentioned = opt_body.mentioned_items().to_vec();

            println!("========================================================================");
            println!(
                "FUNCTION: {} (DefKind::{:?})",
                path, kind
            );
            println!(
                "  is_external_entry_fn (isPublic) : {}",
                is_public
            );
            println!(
                "  isSafe                          : {}",
                is_safe
            );
            println!(
                "  PostCleanup phase               : {:?} ({} basic blocks)",
                post_cleanup_phase, post_cleanup_bb_count
            );
            println!(
                "  Optimized phase                 : {:?} ({} basic blocks)",
                opt_phase, opt_bb_count
            );

            // 3. Extract required_consts() and their mir_for_ctfe(const_def_id) bodies
            let typing_env = ty::TypingEnv::post_analysis(tcx, def_id);
            println!("  required_consts ({}):", req_consts.len());
            for (idx, const_op) in req_consts.iter().enumerate() {
                match const_op.const_ {
                    Const::Unevaluated(uv, ty) => {
                        let const_kind = tcx.def_kind(uv.def);
                        println!(
                            "    [{}] Const::Unevaluated raw_def={} ({:?}) raw_args={:?} ty={:?}",
                            idx,
                            tcx.def_path_str(uv.def),
                            const_kind,
                            uv.args,
                            ty
                        );
                        // Resolve trait associated constants (like StaticAssert::ASSERT)
                        // via ty::Instance::try_resolve, matching tcx.const_eval_resolve.
                        let (resolved_def, resolved_args) =
                            match ty::Instance::try_resolve(tcx, typing_env, uv.def, uv.args) {
                                Ok(Some(inst)) => (inst.def_id(), inst.args),
                                _ => (uv.def, uv.args),
                            };
                        if resolved_def != uv.def {
                            println!(
                                "        -> Instance::try_resolve => def={} args={:?}",
                                tcx.def_path_str(resolved_def),
                                resolved_args
                            );
                        }
                        if resolved_def.as_local().is_some_and(|l| mir_keys.contains(&l)) {
                            let ctfe_body = tcx.mir_for_ctfe(resolved_def);
                            println!(
                                "        mir_for_ctfe({}) phase={:?} bb_count={} req_consts={}:",
                                tcx.def_path_str(resolved_def),
                                ctfe_body.phase,
                                ctfe_body.basic_blocks.len(),
                                ctfe_body.required_consts().len()
                            );
                            print!("{}", format_mir_blocks(ctfe_body));
                        } else {
                            println!(
                                "        (resolved_def {} has no local body in mir_keys)",
                                tcx.def_path_str(resolved_def)
                            );
                        }
                    }
                    other => {
                        println!("    [{}] {:?}", idx, other);
                    }
                }
            }

            // 4. Extract mentioned_items() and resolve their DefId / generic args
            println!("  mentioned_items ({}):", mentioned.len());
            for (idx, spanned_item) in mentioned.iter().enumerate() {
                match spanned_item.node {
                    MentionedItem::Fn(fn_ty) => {
                        if let ty::FnDef(callee_def_id, callee_args) = *fn_ty.kind() {
                            println!(
                                "    [{}] MentionedItem::Fn def={} args={:?}",
                                idx,
                                tcx.def_path_str(callee_def_id),
                                callee_args
                            );
                        } else {
                            println!("    [{}] MentionedItem::Fn({:?})", idx, fn_ty);
                        }
                    }
                    MentionedItem::Drop(drop_ty) => {
                        println!("    [{}] MentionedItem::Drop({:?})", idx, drop_ty);
                    }
                    MentionedItem::UnsizeCast { source_ty, target_ty } => {
                        println!(
                            "    [{}] MentionedItem::UnsizeCast {{ source_ty: {:?}, target_ty: {:?} }}",
                            idx, source_ty, target_ty
                        );
                    }
                    MentionedItem::Closure(closure_ty) => {
                        println!("    [{}] MentionedItem::Closure({:?})", idx, closure_ty);
                    }
                }
            }

            println!("  Runtime(PostCleanup) basic_blocks:");
            print!("{}", post_cleanup_blocks_str);
            println!("  Runtime(Optimized) basic_blocks:");
            print!("{}", opt_blocks_str);
            println!();
        }

        Compilation::Stop
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut callbacks = PmeCaptureCallbacks;
    rustc_driver::run_compiler(&args, &mut callbacks);
}
