// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![feature(rustc_private)]

extern crate rustc_abi;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

use rustc_abi::{BackendRepr, FieldsShape, TagEncoding, Variants};
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_interface::interface::Compiler;
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{Body, Location, PlaceElem, TerminatorKind};
use rustc_middle::ty::{self, Instance, Ty, TyCtxt, TypingEnv};

struct ExtractorCallbacks;

fn dump_ty_layout<'tcx>(tcx: TyCtxt<'tcx>, label: &str, ty: Ty<'tcx>) {
    let typing_env = TypingEnv::fully_monomorphized();
    let layout = match tcx.layout_of(typing_env.as_query_input(ty)) {
        Ok(l) => l,
        Err(e) => {
            println!("=== TYPE LAYOUT: {} ({:?}) -> LayoutError: {:?} ===", label, ty, e);
            return;
        }
    };
    println!("=== TYPE LAYOUT: {} (`{}`) ===", label, ty);
    println!(
        "  size: {} bytes, abi_align: {} bytes, is_sized: {}, is_zst: {}",
        layout.size.bytes(),
        layout.align.abi.bytes(),
        layout.is_sized(),
        layout.is_zst()
    );
    println!("  backend_repr: {:?}", layout.backend_repr);

    if let ty::Adt(adt_def, args) = ty.kind() {
        let repr = adt_def.repr();
        println!(
            "  adt_kind: {:?}, repr: c={}, transparent={}, pack={:?}, align={:?}, int={:?}",
            adt_def.adt_kind(),
            repr.c(),
            repr.transparent(),
            repr.pack,
            repr.align,
            repr.int
        );
        for (v_idx, v_def) in adt_def.variants().iter_enumerated() {
            let discr = ty.discriminant_for_variant(tcx, v_idx);
            println!(
                "  decl_variant {:?} (`{}`): discr={:?}",
                v_idx,
                v_def.name,
                discr.map(|d| (d.val, d.ty))
            );
            for (f_idx, f_def) in v_def.fields.iter_enumerated() {
                let f_ty = f_def.ty(tcx, args);
                println!(
                    "    decl_field {:?} (`{}`): vis={:?}, ty=`{:?}`",
                    f_idx, f_def.name, f_def.vis, f_ty
                );
            }
        }
    }

    match &layout.fields {
        FieldsShape::Primitive => println!("  fields_shape: Primitive"),
        FieldsShape::Union(count) => println!("  fields_shape: Union({})", count),
        FieldsShape::Array { stride, count } => {
            println!(
                "  fields_shape: Array {{ stride: {} bytes, count: {} }}",
                stride.bytes(),
                count
            )
        }
        FieldsShape::Arbitrary { offsets, in_memory_order } => {
            println!("  fields_shape: Arbitrary (in_memory_order={:?}):", in_memory_order);
            for (f_idx, offset) in offsets.iter_enumerated() {
                println!("    FieldIdx({}) -> byte_offset: {}", f_idx.index(), offset.bytes());
            }
        }
    }

    match &layout.variants {
        Variants::Empty => println!("  variants: Empty"),
        Variants::Single { index } => println!("  variants: Single {{ index: {:?} }}", index),
        Variants::Multiple { tag, tag_encoding, tag_field, variants } => {
            println!(
                "  variants: Multiple {{ tag: {:?}, tag_encoding: {:?}, tag_field: {:?} }}",
                tag, tag_encoding, tag_field
            );
            match tag_encoding {
                TagEncoding::Direct => {
                    println!("    TagEncoding::Direct (stored at field {:?})", tag_field);
                }
                TagEncoding::Niche { untagged_variant, niche_variants, niche_start } => {
                    println!(
                        "    TagEncoding::Niche {{ untagged_variant: {:?}, niche_variants: {:?}, niche_start: {:#x} }}",
                        untagged_variant, niche_variants, niche_start
                    );
                }
            }
            for (v_idx, v_layout) in variants.iter_enumerated() {
                println!(
                    "    variant_layout {:?}: size={} bytes, backend_repr={:?}, field_offsets={:?}",
                    v_idx,
                    v_layout.size.bytes(),
                    v_layout.backend_repr,
                    v_layout.field_offsets
                );
            }
        }
    }
    println!();
}

struct DowncastAndCallVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Visitor<'tcx> for DowncastAndCallVisitor<'tcx> {
    fn visit_projection_elem(
        &mut self,
        local: rustc_middle::mir::PlaceRef<'tcx>,
        elem: PlaceElem<'tcx>,
        context: rustc_middle::mir::visit::PlaceContext,
        location: Location,
    ) {
        if let PlaceElem::Downcast(sym, variant_idx) = elem {
            println!(
                "    [Downcast @ {:?}] name={:?}, VariantIdx={:?} (pretty.rs omits VariantIdx when name is Some!)",
                location, sym, variant_idx
            );
        }
        self.super_projection_elem(local, elem, context, location);
    }

    fn visit_terminator(
        &mut self,
        terminator: &rustc_middle::mir::Terminator<'tcx>,
        location: Location,
    ) {
        if let TerminatorKind::Call { func, args, .. } = &terminator.kind {
            if let Some((def_id, generic_args)) = func.const_fn_def() {
                let sig = self.tcx.fn_sig(def_id).instantiate(self.tcx, generic_args);
                let requires_caller_loc = self.tcx.codegen_fn_attrs(def_id).flags.contains(
                    rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags::TRACK_CALLER,
                );
                println!(
                    "    [Call @ {:?}] callee=`{}` (DefKind={:?}, sig=`{:?}`, track_caller={}, mir_arg_count={})",
                    location,
                    self.tcx.def_path_str_with_args(def_id, generic_args),
                    self.tcx.def_kind(def_id),
                    sig.skip_binder(),
                    requires_caller_loc,
                    args.len()
                );
            }
        }
        self.super_terminator(terminator, location);
    }
}

impl Callbacks for ExtractorCallbacks {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        println!("==================================================================");
        println!("1. LOCAL ADT & COMPOSITE LAYOUT EXTRACTION");
        println!("==================================================================");

        for item_id in tcx.hir_crate_items(()).free_items() {
            let def_id = item_id.owner_id.to_def_id();
            match tcx.def_kind(def_id) {
                DefKind::Struct | DefKind::Enum | DefKind::Union => {
                    let generics = tcx.generics_of(def_id);
                    if generics.count() == 0 {
                        let ty = Ty::new_adt(tcx, tcx.adt_def(def_id), ty::List::empty());
                        dump_ty_layout(tcx, &tcx.def_path_str(def_id), ty);
                    }
                }
                _ => {}
            }
        }

        // Also dump key instantiated types from function signatures in probe_6cat.rs
        let extra_fn_names = [
            "cat1_make_tuple",
            "cat1_make_fixed_array",
            "cat1_make_option_usize",
            "cat1_make_option_nonzero",
            "cat1_make_result",
            "cat6_maybe_uninit",
            "cat6_unsafe_cell_get",
        ];
        for item_id in tcx.hir_crate_items(()).free_items() {
            let def_id = item_id.owner_id.to_def_id();
            if tcx.def_kind(def_id) == DefKind::Fn {
                let name = tcx.def_path_str(def_id);
                if extra_fn_names.contains(&name.as_str()) {
                    let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
                    dump_ty_layout(tcx, &format!("ret_of({})", name), sig.output());
                    for (i, input_ty) in sig.inputs().iter().enumerate() {
                        dump_ty_layout(tcx, &format!("arg{}_of({})", i, name), *input_ty);
                    }
                }
            }
        }

        println!("==================================================================");
        println!("2. FUNCTION SIGNATURES, FN_ABI, REQUIRED_CONSTS, & MIR METADATA");
        println!("==================================================================");

        let typing_env = TypingEnv::fully_monomorphized();
        for item_id in tcx.hir_crate_items(()).free_items() {
            let def_id = item_id.owner_id.to_def_id();
            if tcx.def_kind(def_id) != DefKind::Fn {
                continue;
            }
            let name = tcx.def_path_str(def_id);
            let vis = tcx.visibility(def_id);
            let generics = tcx.generics_of(def_id);
            let predicates = tcx.predicates_of(def_id);
            let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
            let attrs = tcx.codegen_fn_attrs(def_id);
            println!("=== FN `{}` ===", name);
            println!(
                "  vis: {:?}, safety: {:?}, abi: {:?}, inline: {:?}, flags: {:?}",
                vis,
                sig.safety(),
                sig.abi(),
                attrs.inline,
                attrs.flags
            );
            if generics.count() > 0 {
                println!("  generics_count: {}", generics.count());
                for (clause, _span) in predicates.predicates {
                    println!("    where_predicate: {:?}", clause);
                }
            } else {
                let instance = Instance::mono(tcx, def_id);
                if let Ok(fn_abi) =
                    tcx.fn_abi_of_instance(typing_env.as_query_input((instance, ty::List::empty())))
                {
                    println!(
                        "  FnAbi: conv={:?}, c_variadic={}, ret_mode={:?} (size={}B), arg_count={}",
                        fn_abi.conv,
                        fn_abi.c_variadic,
                        fn_abi.ret.mode,
                        fn_abi.ret.layout.size.bytes(),
                        fn_abi.args.len()
                    );
                    for (idx, arg_abi) in fn_abi.args.iter().enumerate() {
                        println!(
                            "    FnAbi::arg[{}]: ty=`{}`, size={}B, mode={:?}",
                            idx,
                            arg_abi.layout.ty,
                            arg_abi.layout.size.bytes(),
                            arg_abi.mode
                        );
                    }
                }
            }

            let body: &Body<'tcx> = tcx.optimized_mir(def_id);
            println!(
                "  MIR phase={:?}, basic_blocks={}, local_decls={}, required_consts={}, mentioned_items={}",
                body.phase,
                body.basic_blocks.len(),
                body.local_decls.len(),
                body.required_consts().len(),
                body.mentioned_items().len()
            );
            for rc in body.required_consts() {
                println!("    required_const: {:?} @ {:?}", rc.const_, rc.span);
            }
            for mi in body.mentioned_items() {
                println!("    mentioned_item: {:?}", mi.node);
            }
            let mut visitor = DowncastAndCallVisitor { tcx };
            visitor.visit_body(body);
            println!();
        }

        Compilation::Stop
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut callbacks = ExtractorCallbacks;
    let _ = rustc_driver::catch_fatal_errors(|| {
        rustc_driver::run_compiler(&args, &mut callbacks);
    });
}
