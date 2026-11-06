// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! In-process `rustc_driver` probe for Round 2 Question R2-4:
//! 1. Concrete monomorphization collection (`tcx.collect_and_partition_mono_items(())`)
//!    and generic body instantiation (`EarlyBinder::instantiate` vs
//!    `Instance::instantiate_mir_and_normalize_erasing_regions`).
//! 2. Polymorphic analysis (`TypingEnv::post_analysis(tcx, def_id)`) vs concrete
//!    monomorphized analysis (`TypingEnv::fully_monomorphized()`).
//! 3. DefId / intrinsic call interception at `-Z mir-opt-level=0` for all 12
//!    `zerocopy` operations (`cat6_*`) and `core` pointer/slice/numeric wrappers,
//!    including `#[track_caller]` ABI reconciliation (`requires_caller_location`).

#![feature(rustc_private)]
#![feature(box_patterns)]

extern crate rustc_abi;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_interface::interface::Compiler;
use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
use rustc_middle::mir::{
    Body, NonDivergingIntrinsic, Rvalue, StatementKind, TerminatorKind,
};
use rustc_middle::mono::MonoItem;
use rustc_middle::ty::{
    self, EarlyBinder, GenericArgsRef, Instance, Ty, TyCtxt, TypingEnv,
};

struct MonomorphProbeCallbacks;

#[allow(dead_code)]
#[derive(Debug)]
enum CalleeClassification {
    CoreZerocopyWrapper {
        category: &'static str,
        semantic_lowering: String,
        type_args_summary: String,
        track_caller: bool,
    },
    CoreHelperWrapper {
        category: &'static str,
        semantic_lowering: String,
        type_args_summary: String,
        track_caller: bool,
    },
    DirectIntrinsic {
        name: String,
        semantic_lowering: String,
        type_args_summary: String,
    },
    UserOrUninterceptedCall {
        resolved_instance: String,
        is_local: bool,
        track_caller: bool,
        fn_abi_summary: String,
    },
}

fn format_ty_layout<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
) -> String {
    match tcx.layout_of(typing_env.as_query_input(ty)) {
        Ok(layout) => format!(
            "`{}` (size={}B, align={}B, repr={:?})",
            ty,
            layout.size.bytes(),
            layout.align.abi.bytes(),
            layout.backend_repr
        ),
        Err(err) => format!("`{}` (LayoutError={:?})", ty, err),
    }
}

fn summarize_type_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    args: GenericArgsRef<'tcx>,
) -> String {
    let tys: Vec<String> = args
        .types()
        .enumerate()
        .map(|(idx, ty)| format!("T{}={}", idx, format_ty_layout(tcx, typing_env, ty)))
        .collect();
    if tys.is_empty() {
        "none".to_string()
    } else {
        tys.join(", ")
    }
}

fn classify_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    def_id: DefId,
    args: GenericArgsRef<'tcx>,
) -> CalleeClassification {
    let def_path = tcx.def_path_str(def_id);
    let track_caller = tcx
        .codegen_fn_attrs(def_id)
        .flags
        .contains(CodegenFnAttrFlags::TRACK_CALLER);
    let type_args_summary = summarize_type_args(tcx, typing_env, args);

    if let Some(intrinsic) = tcx.intrinsic(def_id) {
        let name = intrinsic.name.as_str().to_string();
        let lowering = match name.as_str() {
            "size_of" => {
                let t = args.type_at(0);
                let sz = tcx
                    .layout_of(typing_env.as_query_input(t))
                    .map(|l| l.size.bytes().to_string())
                    .unwrap_or_else(|e| format!("{:?}", e));
                format!("ConstEval usize = {}B", sz)
            }
            "align_of" => {
                let t = args.type_at(0);
                let al = tcx
                    .layout_of(typing_env.as_query_input(t))
                    .map(|l| l.align.abi.bytes().to_string())
                    .unwrap_or_else(|e| format!("{:?}", e));
                format!("ConstEval usize = {}B", al)
            }
            "copy" => "MemMove(dst, src, count * size_of::<T>()) [not lowered by LowerIntrinsics]".to_string(),
            "write_bytes" => "MemSet(dst, val, count * size_of::<T>()) [not lowered by LowerIntrinsics]".to_string(),
            "caller_location" => "Implicit caller Location<'static> pointer".to_string(),
            _ => format!("Intrinsic `{}`", name),
        };
        return CalleeClassification::DirectIntrinsic {
            name,
            semantic_lowering: lowering,
            type_args_summary,
        };
    }

    match def_path.as_str() {
        "core::mem::size_of" => {
            let t = args.type_at(0);
            let sz = tcx
                .layout_of(typing_env.as_query_input(t))
                .map(|l| format!("const {}_usize", l.size.bytes()))
                .unwrap_or_else(|e| format!("symbolic size_of::<{}> ({:?})", t, e));
            return CalleeClassification::CoreZerocopyWrapper {
                category: "cat6:size_of",
                semantic_lowering: format!("dest = {}", sz),
                type_args_summary,
                track_caller,
            };
        }
        "core::mem::align_of" => {
            let t = args.type_at(0);
            let al = tcx
                .layout_of(typing_env.as_query_input(t))
                .map(|l| format!("const {}_usize", l.align.abi.bytes()))
                .unwrap_or_else(|e| format!("symbolic align_of::<{}> ({:?})", t, e));
            return CalleeClassification::CoreZerocopyWrapper {
                category: "cat6:align_of",
                semantic_lowering: format!("dest = {}", al),
                type_args_summary,
                track_caller,
            };
        }
        "core::mem::transmute_copy" | "transmute_copy" => {
            let src = args.type_at(0);
            let dst = args.type_at(1);
            return CalleeClassification::CoreZerocopyWrapper {
                category: "cat6:transmute_copy",
                semantic_lowering: format!(
                    "dest = ReadBytes::<{}>(src_ref as *const {}) [assert size_of::<{}>() >= size_of::<{}>()]",
                    dst, dst, src, dst
                ),
                type_args_summary,
                track_caller,
            };
        }
        "core::ptr::read" | "read" => {
            let t = args.type_at(0);
            return CalleeClassification::CoreZerocopyWrapper {
                category: "cat6:ptr::read",
                semantic_lowering: format!("dest = AlignedLoad::<{}>(arg0)", t),
                type_args_summary,
                track_caller,
            };
        }
        "core::ptr::write" | "write" => {
            let t = args.type_at(0);
            return CalleeClassification::CoreZerocopyWrapper {
                category: "cat6:ptr::write",
                semantic_lowering: format!("AlignedStore::<{}>(arg0, arg1)", t),
                type_args_summary,
                track_caller,
            };
        }
        "core::ptr::copy" | "copy" => {
            let t = args.type_at(0);
            return CalleeClassification::CoreZerocopyWrapper {
                category: "cat6:ptr::copy",
                semantic_lowering: format!(
                    "MemMove::<{}>(dst=arg1, src=arg0, count=arg2)",
                    t
                ),
                type_args_summary,
                track_caller,
            };
        }
        "core::ptr::copy_nonoverlapping" | "copy_nonoverlapping" => {
            let t = args.type_at(0);
            return CalleeClassification::CoreZerocopyWrapper {
                category: "cat6:ptr::copy_nonoverlapping",
                semantic_lowering: format!(
                    "MemCpyDisjoint::<{}>(dst=arg1, src=arg0, count=arg2)",
                    t
                ),
                type_args_summary,
                track_caller,
            };
        }
        "core::ptr::write_bytes" | "write_bytes" => {
            let t = args.type_at(0);
            return CalleeClassification::CoreZerocopyWrapper {
                category: "cat6:ptr::write_bytes",
                semantic_lowering: format!(
                    "MemSet::<{}>(dst=arg0, byte=arg1, count=arg2)",
                    t
                ),
                type_args_summary,
                track_caller,
            };
        }
        "core::hint::unreachable_unchecked" | "unreachable_unchecked" => {
            return CalleeClassification::CoreZerocopyWrapper {
                category: "cat6:hint::unreachable_unchecked",
                semantic_lowering: "AssertFalse / Unreachable obligation".to_string(),
                type_args_summary,
                track_caller,
            };
        }
        "core::mem::MaybeUninit::<T>::uninit" => {
            return CalleeClassification::CoreZerocopyWrapper {
                category: "cat6:MaybeUninit::uninit",
                semantic_lowering: "dest = UninitValue::<T>()".to_string(),
                type_args_summary,
                track_caller,
            };
        }
        "core::mem::MaybeUninit::<T>::write" => {
            return CalleeClassification::CoreZerocopyWrapper {
                category: "cat6:MaybeUninit::write",
                semantic_lowering: "*self_mut = InitValue::<T>(val); dest = &mut (*self_mut).value".to_string(),
                type_args_summary,
                track_caller,
            };
        }
        "core::mem::MaybeUninit::<T>::assume_init" => {
            return CalleeClassification::CoreZerocopyWrapper {
                category: "cat6:MaybeUninit::assume_init",
                semantic_lowering: "dest = AssertInitialized::<T>(self_val)".to_string(),
                type_args_summary,
                track_caller,
            };
        }
        "core::cell::UnsafeCell::<T>::get" => {
            return CalleeClassification::CoreZerocopyWrapper {
                category: "cat6:UnsafeCell::get",
                semantic_lowering: "dest = arg0 as *const UnsafeCell<T> as *mut T (offset 0)".to_string(),
                type_args_summary,
                track_caller,
            };
        }
        "core::ptr::const_ptr::<impl *const T>::addr" => {
            return CalleeClassification::CoreHelperWrapper {
                category: "cat3:ptr::addr",
                semantic_lowering: "dest = PtrToAddr(arg0)".to_string(),
                type_args_summary,
                track_caller,
            };
        }
        "core::ptr::const_ptr::<impl *const T>::expose_provenance" => {
            return CalleeClassification::CoreHelperWrapper {
                category: "cat3:ptr::expose_provenance",
                semantic_lowering: "dest = PointerExposeProvenance(arg0)".to_string(),
                type_args_summary,
                track_caller,
            };
        }
        "core::ptr::with_exposed_provenance" => {
            return CalleeClassification::CoreHelperWrapper {
                category: "cat3:ptr::with_exposed_provenance",
                semantic_lowering: "dest = PointerWithExposedProvenance::<T>(arg0)".to_string(),
                type_args_summary,
                track_caller,
            };
        }
        "core::ptr::without_provenance" => {
            return CalleeClassification::CoreHelperWrapper {
                category: "cat3:ptr::without_provenance",
                semantic_lowering: "dest = PtrWithoutProvenance::<*const T>(arg0)".to_string(),
                type_args_summary,
                track_caller,
            };
        }
        "core::ptr::without_provenance_mut" | "without_provenance_mut" => {
            return CalleeClassification::CoreHelperWrapper {
                category: "cat3:ptr::without_provenance_mut",
                semantic_lowering: "dest = PtrWithoutProvenance::<*mut T>(arg0)".to_string(),
                type_args_summary,
                track_caller,
            };
        }
        "core::slice::<impl [T]>::len" | "slice::<impl [T]>::len" => {
            return CalleeClassification::CoreHelperWrapper {
                category: "cat3:slice::len",
                semantic_lowering: "dest = PtrMetadata(arg0)".to_string(),
                type_args_summary,
                track_caller,
            };
        }
        "core::num::NonZero::<T>::get" => {
            return CalleeClassification::CoreHelperWrapper {
                category: "cat4:NonZero::get",
                semantic_lowering: "dest = Transmute::<NonZero<T>, T>(arg0)".to_string(),
                type_args_summary,
                track_caller,
            };
        }
        "core::num::<impl usize>::wrapping_add"
        | "core::num::<impl u64>::wrapping_add" => {
            return CalleeClassification::CoreHelperWrapper {
                category: "cat4/5:wrapping_add",
                semantic_lowering: "dest = Add(arg0, arg1)".to_string(),
                type_args_summary,
                track_caller,
            };
        }
        "core::num::<impl u64>::wrapping_mul" => {
            return CalleeClassification::CoreHelperWrapper {
                category: "cat5:wrapping_mul",
                semantic_lowering: "dest = Mul(arg0, arg1)".to_string(),
                type_args_summary,
                track_caller,
            };
        }
        _ => {}
    }

    match Instance::try_resolve(tcx, typing_env, def_id, args) {
        Ok(Some(instance)) => {
            let req_loc = instance.def.requires_caller_location(tcx);
            let abi_summary = match tcx
                .fn_abi_of_instance(typing_env.as_query_input((instance, ty::List::empty())))
            {
                Ok(fn_abi) => {
                    let arg_modes: Vec<String> = fn_abi
                        .args
                        .iter()
                        .enumerate()
                        .map(|(i, a)| format!("arg[{}]:`{}`({:?})", i, a.layout.ty, a.mode))
                        .collect();
                    format!(
                        "ret:`{}`({:?}), args=[{}]",
                        fn_abi.ret.layout.ty,
                        fn_abi.ret.mode,
                        arg_modes.join(", ")
                    )
                }
                Err(e) => format!("FnAbiError({:?})", e),
            };
            CalleeClassification::UserOrUninterceptedCall {
                resolved_instance: tcx.def_path_str_with_args(instance.def_id(), instance.args),
                is_local: instance.def_id().is_local(),
                track_caller: req_loc,
                fn_abi_summary: abi_summary,
            }
        }
        Ok(None) => CalleeClassification::UserOrUninterceptedCall {
            resolved_instance: format!(
                "<unresolved symbolic trait projection `{}`>",
                tcx.def_path_str_with_args(def_id, args)
            ),
            is_local: def_id.is_local(),
            track_caller,
            fn_abi_summary: "Symbolic/Polymorphic (requires monomorphization or trait law)".to_string(),
        },
        Err(e) => CalleeClassification::UserOrUninterceptedCall {
            resolved_instance: format!("ResolveError({:?})", e),
            is_local: def_id.is_local(),
            track_caller,
            fn_abi_summary: "Error".to_string(),
        },
    }
}

fn dump_substituted_instance_mir<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>) {
    let typing_env = TypingEnv::fully_monomorphized();
    let raw_body = tcx.instance_mir(instance.def);

    // Method A: EarlyBinder::bind(raw_body.clone()).instantiate(tcx, instance.args).skip_norm_wip()
    let binder_instantiated: Body<'tcx> = EarlyBinder::bind(raw_body.clone())
        .instantiate(tcx, instance.args)
        .skip_norm_wip();

    // Method B: instance.instantiate_mir_and_normalize_erasing_regions(...)
    let normalized_body: Body<'tcx> = instance.instantiate_mir_and_normalize_erasing_regions(
        tcx,
        typing_env,
        EarlyBinder::bind(raw_body.clone()),
    );

    println!(
        "=== SUBSTITUTED MIR FOR INSTANCE `{}` (DefId={:?}, args={:?}) ===",
        tcx.def_path_str_with_args(instance.def_id(), instance.args),
        instance.def_id(),
        instance.args
    );
    println!(
        "  EarlyBinder::instantiate vs instantiate_mir_and_normalize_erasing_regions local_decls match: {}",
        binder_instantiated
            .local_decls
            .iter()
            .zip(normalized_body.local_decls.iter())
            .all(|(a, b)| a.ty == b.ty)
    );

    if let Ok(fn_abi) =
        tcx.fn_abi_of_instance(typing_env.as_query_input((instance, ty::List::empty())))
    {
        println!(
            "  Concrete FnAbi: conv={:?}, ret=`{}` (size={}B, align={}B, mode={:?}), arg_count={}",
            fn_abi.conv,
            fn_abi.ret.layout.ty,
            fn_abi.ret.layout.size.bytes(),
            fn_abi.ret.layout.align.abi.bytes(),
            fn_abi.ret.mode,
            fn_abi.args.len()
        );
        for (i, arg) in fn_abi.args.iter().enumerate() {
            println!(
                "    FnAbi::arg[{}]: ty=`{}`, size={}B, align={}B, mode={:?}",
                i,
                arg.layout.ty,
                arg.layout.size.bytes(),
                arg.layout.align.abi.bytes(),
                arg.mode
            );
        }
    }

    for (local, decl) in normalized_body.local_decls.iter_enumerated() {
        println!(
            "  local {:?}: {}",
            local,
            format_ty_layout(tcx, typing_env, decl.ty)
        );
    }

    for (bb, bb_data) in normalized_body.basic_blocks.iter_enumerated() {
        println!("  {:?}:", bb);
        for stmt in &bb_data.statements {
            println!("    stmt: {:?}", stmt.kind);
        }
        if let Some(term) = &bb_data.terminator {
            println!("    term: {:?}", term.kind);
            if let TerminatorKind::Call { func, .. } = &term.kind {
                let func_ty = func.ty(&normalized_body, tcx);
                if let ty::FnDef(callee_def_id, callee_args) = *func_ty.kind() {
                    let class = classify_call(tcx, typing_env, callee_def_id, callee_args);
                    println!("      -> Resolved Call in Substituted Body: {:?}", class);
                }
            }
        }
    }
    println!();
}

impl Callbacks for MonomorphProbeCallbacks {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        println!("========================================================================");
        println!("PART 1: MONOMORPHIZATION COLLECTION (`collect_and_partition_mono_items`)");
        println!("========================================================================");

        let partitions = tcx.collect_and_partition_mono_items(());
        let mut local_fn_instances: Vec<Instance<'tcx>> = Vec::new();
        let mut upstream_fn_instances: Vec<Instance<'tcx>> = Vec::new();

        for cgu in partitions.codegen_units {
            for (mono_item, _data) in cgu.items() {
                if let MonoItem::Fn(instance) = *mono_item {
                    if instance.def_id().is_local() {
                        local_fn_instances.push(instance);
                    } else {
                        upstream_fn_instances.push(instance);
                    }
                }
            }
        }

        local_fn_instances.sort_by_key(|inst| tcx.def_path_str_with_args(inst.def_id(), inst.args));
        local_fn_instances.dedup();
        upstream_fn_instances
            .sort_by_key(|inst| tcx.def_path_str_with_args(inst.def_id(), inst.args));
        upstream_fn_instances.dedup();

        println!(
            "Total CGUs: {}, Local MonoItem::Fn count: {}, Upstream (`core`) MonoItem::Fn count: {}",
            partitions.codegen_units.len(),
            local_fn_instances.len(),
            upstream_fn_instances.len()
        );
        println!("\n--- Local Monomorphized Instances ({}) ---", local_fn_instances.len());
        for inst in &local_fn_instances {
            let is_generic_inst = !inst.args.is_empty();
            println!(
                "  [local{}] `{}` (DefKind={:?}, track_caller={})",
                if is_generic_inst { " GENERIC" } else { "" },
                tcx.def_path_str_with_args(inst.def_id(), inst.args),
                tcx.def_kind(inst.def_id()),
                inst.def.requires_caller_location(tcx)
            );
        }

        println!(
            "\n--- Upstream (`core`) Monomorphized Instances Pulled into CGUs at mir-opt-level=0 ({}) ---",
            upstream_fn_instances.len()
        );
        for inst in &upstream_fn_instances {
            println!(
                "  [upstream] `{}` (track_caller={})",
                tcx.def_path_str_with_args(inst.def_id(), inst.args),
                inst.def.requires_caller_location(tcx)
            );
        }
        println!();

        // Dump substituted MIR for the generic & trait instances in probe_6cat.rs
        for inst in &local_fn_instances {
            let path = tcx.def_path_str_with_args(inst.def_id(), inst.args);
            if path.contains("cat5_generic_id")
                || path.contains("cat5_trait_generic")
                || path.contains("compute")
            {
                dump_substituted_instance_mir(tcx, *inst);
            }
        }

        println!("========================================================================");
        println!("PART 2: POLYMORPHIC (`TypingEnv::post_analysis`) vs MONOMORPHIC ANALYSIS");
        println!("========================================================================");

        for item_id in tcx.hir_crate_items(()).free_items() {
            let def_id = item_id.owner_id.to_def_id();
            let name = tcx.def_path_str(def_id);
            if name != "cat5_generic_id" && name != "cat5_trait_generic" {
                continue;
            }
            let poly_env = TypingEnv::post_analysis(tcx, def_id);
            let fn_ty = tcx.type_of(def_id).instantiate_identity();
            let body = tcx.optimized_mir(def_id);

            println!("=== POLYMORPHIC BODY `{}` ===", name);
            println!("  tcx.type_of(def_id).instantiate_identity(): `{:?}`", fn_ty);
            println!("  param_env caller_bounds: {:?}", poly_env.param_env.caller_bounds());
            println!("  required_consts count: {}", body.required_consts().len());

            for (local, _decl) in body.local_decls.iter_enumerated() {
                let place = rustc_middle::mir::Place::from(local);
                let place_ty = place.ty(&body.local_decls, tcx).ty;
                let ptr_ty = Ty::new_imm_ptr(tcx, place_ty);
                println!(
                    "  local {:?}: Place::ty=`{:?}` (kind={:?})",
                    local,
                    place_ty,
                    place_ty.kind()
                );
                println!(
                    "    layout_of(val_ty) in post_analysis: {}",
                    format_ty_layout(tcx, poly_env, place_ty)
                );
                println!(
                    "    layout_of(*const val_ty) in post_analysis: {}",
                    format_ty_layout(tcx, poly_env, ptr_ty)
                );
            }

            for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
                if let Some(term) = &bb_data.terminator {
                    if let TerminatorKind::Call { func, .. } = &term.kind {
                        let func_ty = func.ty(body, tcx);
                        if let ty::FnDef(callee_def_id, callee_args) = *func_ty.kind() {
                            let class = classify_call(tcx, poly_env, callee_def_id, callee_args);
                            println!("  [Polymorphic Call @ {:?}] {:?}", bb, class);
                        }
                    }
                }
            }
            println!();
        }

        // Also compare polymorphic `core::mem::transmute_copy<Src, Dst>` vs monomorphized
        // `core::mem::transmute_copy::<u64, [u32; 2]>` to demonstrate `Src`/`Dst` symbolic
        // type parameters and `body.required_consts()` evaluation!
        for inst in &upstream_fn_instances {
            let path = tcx.def_path_str(inst.def_id());
            if path == "core::mem::transmute_copy" {
                let def_id = inst.def_id();
                let poly_env = TypingEnv::post_analysis(tcx, def_id);
                let poly_body = tcx.instance_mir(ty::InstanceKind::Item(def_id));
                println!(
                    "=== POLYMORPHIC `Src`/`Dst` BODY `{}` vs MONOMORPHIZED `{}` ===",
                    path,
                    tcx.def_path_str_with_args(def_id, inst.args)
                );
                println!(
                    "  generics: {:?}",
                    tcx.generics_of(def_id)
                        .own_params
                        .iter()
                        .map(|p| (p.index, p.name))
                        .collect::<Vec<_>>()
                );
                println!("  param_env caller_bounds: {:?}", poly_env.param_env.caller_bounds());
                for (local, _decl) in poly_body.local_decls.iter_enumerated().take(5) {
                    let place = rustc_middle::mir::Place::from(local);
                    let place_ty = place.ty(&poly_body.local_decls, tcx).ty;
                    println!(
                        "  [Poly] local {:?}: Place::ty=`{:?}` -> layout={}",
                        local,
                        place_ty,
                        format_ty_layout(tcx, poly_env, place_ty)
                    );
                }
                let mono_env = TypingEnv::fully_monomorphized();
                for rc in poly_body.required_consts() {
                    let poly_eval = rc.const_.eval(tcx, poly_env, rc.span);
                    let mono_const = inst.instantiate_mir_and_normalize_erasing_regions(
                        tcx,
                        mono_env,
                        EarlyBinder::bind(rc.const_),
                    );
                    let mono_eval = mono_const.eval(tcx, mono_env, rc.span);
                    println!(
                        "  [required_const] poly_const={:?}\n    -> eval in post_analysis (symbolic Src, Dst): {:?}\n    -> eval in fully_monomorphized (Src=u64, Dst=[u32; 2]): {:?}",
                        rc.const_, poly_eval, mono_eval
                    );
                }
                println!();
            }
        }

        println!("========================================================================");
        println!("PART 3: DEF_ID / INTRINSIC CALL INTERCEPTION ACROSS `probe_6cat.rs`");
        println!("========================================================================");

        let mono_env = TypingEnv::fully_monomorphized();
        for item_id in tcx.hir_crate_items(()).free_items() {
            let def_id = item_id.owner_id.to_def_id();
            if tcx.def_kind(def_id) != DefKind::Fn {
                continue;
            }
            let name = tcx.def_path_str(def_id);
            if !name.starts_with("cat3_") && !name.starts_with("cat5_") && !name.starts_with("cat6_")
            {
                continue;
            }
            let is_poly = tcx.generics_of(def_id).count() > 0;
            let env = if is_poly {
                TypingEnv::post_analysis(tcx, def_id)
            } else {
                mono_env
            };
            let body = tcx.optimized_mir(def_id);
            println!("=== FUNCTION `{}` (phase={:?}) ===", name, body.phase);

            for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
                for stmt in &bb_data.statements {
                    match &stmt.kind {
                        StatementKind::Assign(box (place, rvalue)) => match rvalue {
                            Rvalue::Cast(cast_kind, op, dst_ty) => {
                                let src_ty = op.ty(&body.local_decls, tcx);
                                println!(
                                    "  [{:?} Stmt Cast {:?}] `{:?}` = {:?} : {} -> {}",
                                    bb,
                                    cast_kind,
                                    place,
                                    op,
                                    format_ty_layout(tcx, env, src_ty),
                                    format_ty_layout(tcx, env, *dst_ty)
                                );
                            }
                            Rvalue::UnaryOp(rustc_middle::mir::UnOp::PtrMetadata, op) => {
                                println!(
                                    "  [{:?} Stmt PtrMetadata] `{:?}` = PtrMetadata({:?})",
                                    bb, place, op
                                );
                            }
                            Rvalue::Use(rustc_middle::mir::Operand::RuntimeChecks(chk), _) => {
                                println!(
                                    "  [{:?} Stmt RuntimeChecks] `{:?}` = RuntimeChecks({:?}) (sess.ub_checks()={})",
                                    bb,
                                    place,
                                    chk,
                                    tcx.sess.ub_checks()
                                );
                            }
                            _ => {}
                        },
                        StatementKind::Intrinsic(box NonDivergingIntrinsic::CopyNonOverlapping(
                            cno,
                        )) => {
                            let src_ptr_ty = cno.src.ty(&body.local_decls, tcx);
                            println!(
                                "  [{:?} Stmt Intrinsic::CopyNonOverlapping] src={:?} ({}), dst={:?}, count={:?}",
                                bb,
                                cno.src,
                                format_ty_layout(tcx, env, src_ptr_ty),
                                cno.dst,
                                cno.count
                            );
                        }
                        _ => {}
                    }
                }
                if let Some(term) = &bb_data.terminator {
                    match &term.kind {
                        TerminatorKind::Call { func, args, destination, .. } => {
                            let func_ty = func.ty(body, tcx);
                            if let ty::FnDef(callee_def_id, callee_args) = *func_ty.kind() {
                                let class = classify_call(tcx, env, callee_def_id, callee_args);
                                println!(
                                    "  [{:?} Call] dest=`{:?}`, mir_args={}, callee=`{}`\n    -> {:?}",
                                    bb,
                                    destination,
                                    args.len(),
                                    tcx.def_path_str_with_args(callee_def_id, callee_args),
                                    class
                                );
                            }
                        }
                        TerminatorKind::Unreachable => {
                            println!("  [{:?} TerminatorKind::Unreachable]", bb);
                        }
                        _ => {}
                    }
                }
            }
            if !body.required_consts().is_empty() {
                for rc in body.required_consts() {
                    let val = rc.const_.eval(tcx, env, rc.span);
                    println!(
                        "  [required_const] {:?} -> eval={:?} (ty=`{}`)",
                        rc.const_,
                        val,
                        rc.const_.ty()
                    );
                }
            }
            println!();
        }

        Compilation::Stop
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut callbacks = MonomorphProbeCallbacks;
    let _ = rustc_driver::catch_fatal_errors(|| {
        rustc_driver::run_compiler(&args, &mut callbacks);
    });
}
