#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_public;
extern crate rustc_public_bridge;
extern crate rustc_session;
extern crate rustc_span;

use std::sync::OnceLock;

use rustc_driver::{Callbacks, Compilation, run_compiler};
use rustc_interface::interface;
use rustc_middle::mir;
use rustc_middle::ty::TyCtxt;
use rustc_middle::util::Providers;
use rustc_public::CrateDef;
use rustc_public::abi::{FieldsShape, VariantsShape};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Rvalue, StatementKind, TerminatorKind};
use rustc_public::rustc_internal;
use rustc_public::target::MachineInfo;
use rustc_public::ty::{AdtKind, ConstantKind, RigidTy, TyKind, VariantIdx};
use rustc_public_bridge::IndexedVal;
use rustc_span::def_id::LocalDefId;

type OrigQuery = fn(TyCtxt<'_>, LocalDefId) -> &'_ rustc_data_structures::steal::Steal<mir::Body<'_>>;
static ORIG_QUERY: OnceLock<OrigQuery> = OnceLock::new();

fn inspect_rustc_public(label: &str) {
    println!("=== [{}] Machine & Crate Inventory ===", label);
    let machine = MachineInfo::target();
    println!(
        "machine_info: endian={:?} pointer_width_bits={}",
        match machine.endian {
            rustc_public::target::Endian::Little => "Little",
            rustc_public::target::Endian::Big => "Big",
        },
        machine.pointer_width.bits()
    );
    let local = rustc_public::local_crate();
    let ext = rustc_public::external_crates();
    let items = rustc_public::all_local_items();
    println!(
        "local_crate: name={} id={:?} is_local={} fn_defs={} statics={} trait_decls={} trait_impls={} foreign_mods={} all_local_items={}",
        local.name,
        rustc_internal::crate_num(&local),
        local.is_local,
        local.fn_defs().len(),
        local.statics().len(),
        local.trait_decls().len(),
        local.trait_impls().len(),
        local.foreign_modules().len(),
        items.len(),
    );
    println!(
        "external_crates ({}): {:?}",
        ext.len(),
        ext.iter().map(|c| c.name.as_str()).collect::<Vec<_>>()
    );

    println!("=== [{}] Inspecting Functions, Bodies, and Instances ===", label);
    for item in &items {
        let name = item.name();
        let req_mono = item.requires_monomorphization();
        let kind = item.kind();
        let tool_attrs = item.all_tool_attrs();
        let body = item.body();
        let stmt_summary = body.as_ref().map(|b| {
            let total_stmts: usize = b.blocks.iter().map(|bb| bb.statements.len()).sum();
            let place_mentions: usize = b
                .blocks
                .iter()
                .flat_map(|bb| &bb.statements)
                .filter(|s| matches!(s.kind, StatementKind::PlaceMention(_)))
                .count();
            let storage_ops: usize = b
                .blocks
                .iter()
                .flat_map(|bb| &bb.statements)
                .filter(|s| matches!(s.kind, StatementKind::StorageLive(_) | StatementKind::StorageDead(_)))
                .count();
            let retag_yes: usize = b
                .blocks
                .iter()
                .flat_map(|bb| &bb.statements)
                .filter(|s| matches!(s.kind, StatementKind::Assign(_, Rvalue::Use(_, rustc_public::mir::WithRetag::Yes))))
                .count();
            let asserts: usize = b
                .blocks
                .iter()
                .filter(|bb| matches!(bb.terminator.kind, TerminatorKind::Assert { .. }))
                .count();
            let asms: usize = b
                .blocks
                .iter()
                .filter(|bb| matches!(bb.terminator.kind, TerminatorKind::InlineAsm { .. }))
                .count();
            let aborts: usize = b
                .blocks
                .iter()
                .filter(|bb| matches!(bb.terminator.kind, TerminatorKind::Abort))
                .count();
            (b.blocks.len(), total_stmts, place_mentions, storage_ops, retag_yes, asserts, asms, aborts, b.spread_arg())
        });
        println!(
            "item={} kind={:?} mono={} tool_attrs={} body={:?}",
            name, kind, req_mono, tool_attrs.len(), stmt_summary
        );

        if name.ends_with("inline_asm_fn") {
            if let Some(b) = &body {
                for bb in &b.blocks {
                    if let TerminatorKind::InlineAsm {
                        template,
                        operands,
                        options,
                        line_spans,
                        destination,
                        unwind,
                    } = &bb.terminator.kind
                    {
                        println!(
                            "  INLINE_ASM: template={:?} options={:?} line_spans={:?} dest={:?} unwind={:?} operands={:?}",
                            template, options, line_spans, destination, unwind, operands
                        );
                    }
                }
            }
        }

        if name.ends_with("const_eval_fn") || name.ends_with("union_uninit_const") {
            let inst_body = Instance::try_from(*item).ok().and_then(|i| i.body());
            for (pass_label, opt_body) in [("item.body()", body.as_ref()), ("instance.body()", inst_body.as_ref())] {
                if let Some(b) = opt_body {
                    for bb in &b.blocks {
                        for s in &bb.statements {
                            if let StatementKind::Assign(_, Rvalue::Use(rustc_public::mir::Operand::Constant(c), _)) = &s.kind {
                                println!("  CONST_OP [{}] ({}): kind={:?}", pass_label, name, c.const_.kind());
                                if let ConstantKind::Allocated(alloc) = c.const_.kind() {
                                    println!(
                                        "    alloc bytes_len={} has_none={} ptrs={:?}",
                                        alloc.bytes.len(),
                                        alloc.bytes.iter().any(|x| x.is_none()),
                                        alloc.provenance.ptrs
                                    );
                                    for &(_, prov) in &alloc.provenance.ptrs {
                                        let ga = rustc_public::mir::alloc::GlobalAlloc::from(prov.0);
                                        println!("    provenance -> {:?}", ga);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    println!("=== [{}] Inspecting Statics ===", label);
    for st in local.statics() {
        let init = st.eval_initializer();
        println!(
            "static={} init_ok={} init_ptrs={:?}",
            st.name(),
            init.is_ok(),
            init.as_ref().map(|a| &a.provenance.ptrs)
        );
    }

    println!("=== [{}] Inspecting Generic Instance Resolution & CTFE Swallow ===", label);
    if let Some(gen_fn) = local.fn_defs().into_iter().find(|f| f.name().ends_with("generic_id")) {
        let sig = gen_fn.fn_sig();
        let u32_ty = rustc_public::ty::Ty::unsigned_ty(rustc_public::ty::UintTy::U32);
        let args = rustc_public::ty::GenericArgs(vec![rustc_public::ty::GenericArgKind::Type(u32_ty)]);
        let inst = Instance::resolve(gen_fn, &args);
        println!(
            "generic_id sig_inputs={:?} resolved={:?} has_body={:?} body_blocks={:?}",
            sig.value.inputs(),
            inst.as_ref().map(|i| i.mangled_name()),
            inst.as_ref().map(|i| i.has_body()),
            inst.as_ref().ok().and_then(|i| i.body()).map(|b| b.blocks.len())
        );
    }
    if let Some(bomb_fn) = local.fn_defs().into_iter().find(|f| f.name().ends_with("generic_ctfe_bomb")) {
        let u8_ty = rustc_public::ty::Ty::unsigned_ty(rustc_public::ty::UintTy::U8);
        let args_u8 = rustc_public::ty::GenericArgs(vec![rustc_public::ty::GenericArgKind::Type(u8_ty)]);
        let inst = Instance::resolve(bomb_fn, &args_u8);
        let body_u8 = inst.as_ref().ok().and_then(|i| i.body());
        println!("generic_ctfe_bomb::<u8> resolved={} body_some={}", inst.is_ok(), body_u8.is_some());
        if let Some(b) = body_u8 {
            for bb in &b.blocks {
                for s in &bb.statements {
                    if let StatementKind::Assign(_, Rvalue::Use(rustc_public::mir::Operand::Constant(c), _)) = &s.kind {
                        println!("  BOMB const operand kind={:?}", c.const_.kind());
                    }
                }
            }
        }
    }

    println!("=== [{}] Inspecting Param/Item Layouts & ADTs ===", label);
    for item in &items {
        if item.name().ends_with("place_mention_test")
            || item.name().ends_with("niche_match")
            || item.name().ends_with("touch_all_adts")
            || item.name().ends_with("union_uninit_const")
            || item.name().ends_with("attr_fn")
            || item.name().ends_with("generic_id")
        {
            if let Some(b) = item.body() {
                for (lidx, decl) in b.local_decls() {
                    let lay = decl.ty.layout();
                    if let TyKind::RigidTy(RigidTy::Adt(adt, args)) = decl.ty.kind() {
                        let shape = lay.as_ref().map(|l| l.shape());
                        let repr = adt.repr();
                        let mut discrs = Vec::new();
                        if adt.kind() == AdtKind::Enum {
                            for i in 0..adt.num_variants() {
                                let vidx = VariantIdx::to_val(i);
                                discrs.push((i, adt.discriminant_for_variant(vidx).val));
                            }
                        }
                        println!(
                            "ADT {}: kind={:?} args_len={} repr={:?} discrs={:?} shape={:?}",
                            adt.name(),
                            adt.kind(),
                            args.0.len(),
                            repr,
                            discrs,
                            shape.map(|s| format!(
                                "size={} align={} fields={:?} variants={:?}",
                                s.size.bytes(),
                                s.abi_align,
                                s.fields,
                                match s.variants {
                                    VariantsShape::Empty => "Empty".into(),
                                    VariantsShape::Single { index } => format!("Single({})", index.to_index()),
                                    VariantsShape::Multiple { tag, tag_encoding, tag_field, variants } =>
                                        format!("Multiple(tag={:?}, enc={:?}, tag_field={}, vars={:?})", tag, tag_encoding, tag_field, variants),
                                }
                            ))
                        );
                        let _ = (FieldsShape::Primitive, lidx);
                    } else if matches!(decl.ty.kind(), TyKind::Param(_)) {
                        println!("Generic Param local {:?}: layout={:?}", lidx, lay);
                    }
                }
            }
        }
    }
}

struct HybridCallbacks;

impl Callbacks for HybridCallbacks {
    fn config(&mut self, config: &mut interface::Config) {
        config.override_queries = Some(|_, providers: &mut Providers| {
            let _ = ORIG_QUERY.set(providers.queries.mir_drops_elaborated_and_const_checked);
            providers.queries.mir_drops_elaborated_and_const_checked = |tcx, def| {
                let orig = ORIG_QUERY.get().unwrap();
                orig(tcx, def)
            };
        });
    }

    fn after_analysis<'tcx>(&mut self, _: &interface::Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        for def in tcx.iter_local_def_id() {
            let kind = tcx.def_kind(def);
            if matches!(kind, rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn)
                && tcx.is_mir_available(def.to_def_id())
            {
                let raw = tcx.mir_drops_elaborated_and_const_checked(def);
                let body = raw.borrow();
                let name = rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def.to_def_id()));
                let stmts: usize = body.basic_blocks.iter().map(|b| b.statements.len()).sum();
                let pm: usize = body.basic_blocks.iter().flat_map(|b| &b.statements).filter(|s| matches!(s.kind, mir::StatementKind::PlaceMention(_))).count();
                let cleanup_bbs = body.basic_blocks.iter().filter(|b| b.is_cleanup).count();
                let stable_post = rustc_internal::run(tcx, || rustc_internal::stable(&*body)).unwrap();
                let stable_pm: usize = stable_post.blocks.iter().flat_map(|b| &b.statements).filter(|s| matches!(s.kind, StatementKind::PlaceMention(_))).count();
                println!("raw_postcleanup {} bbs={} stmts={} raw_pm={} stable_pm={} cleanup_bbs={}", name, body.basic_blocks.len(), stmts, pm, stable_pm, cleanup_bbs);
            }
        }
        rustc_internal::run(tcx, || inspect_rustc_public("hybrid-after_analysis")).unwrap();
        Compilation::Stop
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mode = args.get(1).map(|s| s.as_str()).unwrap_or("run");
    let rustc_args = args[2..].to_vec();
    match mode {
        "run" => {
            let res = rustc_public::run!(&rustc_args, || -> std::ops::ControlFlow<(), ()> {
                inspect_rustc_public("rustc_public::run!");
                std::ops::ControlFlow::Break(())
            });
            println!("rustc_public::run! result: {:?}", res);
        }
        "hybrid" => {
            let mut cb = HybridCallbacks;
            run_compiler(&rustc_args, &mut cb);
        }
        other => panic!("unknown mode: {other}"),
    }
}
