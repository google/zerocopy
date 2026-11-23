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

use rustc_driver::{Callbacks, Compilation, compiler_entrypoint};
use rustc_interface::interface;
use rustc_middle::mir;
use rustc_middle::ty::TyCtxt;
use rustc_middle::util::Providers;
use rustc_public::CrateDef;
use rustc_public::mir::{Rvalue, StatementKind, TerminatorKind};
use rustc_public::rustc_internal;
use rustc_public::target::MachineInfo;
use rustc_public::ty::{AdtKind, ConstantKind, RigidTy, TyKind, VariantIdx};
use rustc_public_bridge::IndexedVal;
use rustc_span::def_id::LocalDefId;

type OrigQuery = fn(TyCtxt<'_>, LocalDefId) -> &'_ rustc_data_structures::steal::Steal<mir::Body<'_>>;
static ORIG_QUERY: OnceLock<OrigQuery> = OnceLock::new();

fn inspect_crate(label: &str, summarize_only: bool) {
    let machine = MachineInfo::target();
    let local = rustc_public::local_crate();
    let ext = rustc_public::external_crates();
    let items = rustc_public::all_local_items();
    let adts = local.adts();
    println!(
        "=== [{}] endian={:?} ptr_bits={} local={} fn_defs={} statics={} adts={} trait_decls={} trait_impls={} all_local_items={} ext_crates={} ===",
        label,
        match machine.endian {
            rustc_public::target::Endian::Little => "Little",
            rustc_public::target::Endian::Big => "Big",
        },
        machine.pointer_width.bits(),
        local.name,
        local.fn_defs().len(),
        local.statics().len(),
        adts.len(),
        local.trait_decls().len(),
        local.trait_impls().len(),
        items.len(),
        ext.len(),
    );

    let mut bodies_ok = 0usize;
    let mut bodies_none = 0usize;
    let mut opt_bbs = 0usize;
    let mut opt_stmts = 0usize;
    let mut adt_layouts_ok = 0usize;
    let mut adt_layouts_err = 0usize;
    let mut alias_tys_seen = 0usize;
    let mut pm_total = 0usize;
    let mut asm_total = 0usize;

    for item in &items {
        if let Some(b) = item.body() {
            bodies_ok += 1;
            opt_bbs += b.blocks.len();
            opt_stmts += b.blocks.iter().map(|bb| bb.statements.len()).sum::<usize>();
            for bb in &b.blocks {
                for s in &bb.statements {
                    if matches!(s.kind, StatementKind::PlaceMention(_)) {
                        pm_total += 1;
                    }
                    if !summarize_only && item.name().ends_with("union_uninit_const") {
                        if let StatementKind::Assign(_, Rvalue::Use(rustc_public::mir::Operand::Constant(c), _)) = &s.kind {
                            println!("  [item.body()] union_uninit_const const={:?}", c.const_.kind());
                        }
                    }
                }
                if let TerminatorKind::InlineAsm { .. } = &bb.terminator.kind {
                    asm_total += 1;
                }
            }
            for (_, decl) in b.local_decls() {
                if matches!(decl.ty.kind(), TyKind::Alias(..)) {
                    alias_tys_seen += 1;
                }
            }
        } else {
            bodies_none += 1;
        }
    }

    for adt in &adts {
        let _ = (adt.kind(), adt.repr());
        for v in adt.variants() {
            let _ = v.idx();
        }
        if adt.kind() == AdtKind::Enum {
            for i in 0..adt.num_variants() {
                let _ = adt.discriminant_for_variant(VariantIdx::to_val(i));
            }
        }
        match adt.ty().layout() {
            Ok(_) => adt_layouts_ok += 1,
            Err(_) => adt_layouts_err += 1,
        }
    }

    println!(
        "SUMMARY: bodies_ok={} bodies_none={} opt_bbs={} opt_stmts={} alias_tys_seen={} pm_total={} asm_total={} adt_layouts_ok={} adt_layouts_err={}",
        bodies_ok, bodies_none, opt_bbs, opt_stmts, alias_tys_seen, pm_total, asm_total, adt_layouts_ok, adt_layouts_err
    );
    let _ = ConstantKind::ZeroSized;
    let _ = RigidTy::Bool;
}

struct Probe1102 {
    summarize_only: bool,
}

impl Callbacks for Probe1102 {
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
        let mut postcleanup_ok = 0usize;
        let mut post_bbs = 0usize;
        let mut post_stmts = 0usize;
        let mut postcleanup_pm = 0usize;
        let mut postcleanup_cleanup_bbs = 0usize;
        let mut call_use_count = 0usize;
        for def in tcx.iter_local_def_id() {
            let kind = tcx.def_kind(def);
            if matches!(kind, rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn)
                && tcx.is_mir_available(def.to_def_id())
            {
                let raw = tcx.mir_drops_elaborated_and_const_checked(def);
                let body = raw.borrow();
                post_bbs += body.basic_blocks.len();
                post_stmts += body.basic_blocks.iter().map(|bb| bb.statements.len()).sum::<usize>();
                postcleanup_cleanup_bbs += body.basic_blocks.iter().filter(|b| b.is_cleanup).count();
                for bb in body.basic_blocks.iter() {
                    if let mir::TerminatorKind::Call { call_source: mir::CallSource::Use, .. } = &bb.terminator().kind {
                        call_use_count += 1;
                    }
                }
                let stable_post = rustc_internal::run(tcx, || rustc_internal::stable(&*body)).unwrap();
                postcleanup_ok += 1;
                postcleanup_pm += stable_post
                    .blocks
                    .iter()
                    .flat_map(|b| &b.statements)
                    .filter(|s| matches!(s.kind, StatementKind::PlaceMention(_)))
                    .count();
            }
        }
        println!(
            "POSTCLEANUP_STABLE_OK count={} post_bbs={} post_stmts={} pm={} cleanup_bbs={} call_use={}",
            postcleanup_ok, post_bbs, post_stmts, postcleanup_pm, postcleanup_cleanup_bbs, call_use_count
        );
        rustc_internal::run(tcx, || inspect_crate("1.102-nightly", self.summarize_only)).unwrap();
        Compilation::Stop
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let summarize_only = args.get(1).map(|s| s == "zerocopy").unwrap_or(false);
    let rustc_args = args[2..].to_vec();
    let mut cb = Probe1102 { summarize_only };
    compiler_entrypoint(&rustc_args, &mut cb);
}
