#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

use std::collections::BTreeMap;
use std::sync::{Mutex, OnceLock};

use rustc_data_structures::steal::Steal;
use rustc_driver::Compilation;
use rustc_hir::def::DefKind;
use rustc_index::IndexVec;
use rustc_interface::interface;
use rustc_middle::mir::{
    self, Body, Const, ConstOperand, Operand, Promoted, Rvalue, StatementKind, TerminatorKind,
    traversal,
};
use rustc_middle::ty::{self, TyCtxt};
use rustc_middle::util::Providers;
use rustc_session::Session;
use rustc_span::def_id::LocalDefId;

type MirBuiltProvider = for<'tcx> fn(TyCtxt<'tcx>, LocalDefId) -> &'tcx Steal<Body<'tcx>>;
type MirPromotedProvider = for<'tcx> fn(
    TyCtxt<'tcx>,
    LocalDefId,
) -> (
    &'tcx Steal<Body<'tcx>>,
    &'tcx Steal<IndexVec<Promoted, Body<'tcx>>>,
);
type MirDropsProvider = for<'tcx> fn(TyCtxt<'tcx>, LocalDefId) -> &'tcx Steal<Body<'tcx>>;

static ORIG_MIR_BUILT: OnceLock<MirBuiltProvider> = OnceLock::new();
static ORIG_MIR_PROMOTED: OnceLock<MirPromotedProvider> = OnceLock::new();
static ORIG_MIR_DROPS: OnceLock<MirDropsProvider> = OnceLock::new();

#[derive(Default)]
struct CapturedStages {
    mir_built: BTreeMap<String, String>,
    mir_promoted: BTreeMap<String, String>,
    mir_drops: BTreeMap<String, String>,
}

static STAGES: Mutex<Option<CapturedStages>> = Mutex::new(None);

fn format_const_op<'tcx>(tcx: TyCtxt<'tcx>, c: &ConstOperand<'tcx>) -> String {
    let kind_str = match c.const_ {
        Const::Ty(ty, ct) => format!("Const::Ty(ty={ty:?}, ct={ct:?}, kind={:?})", ct.kind()),
        Const::Unevaluated(uv, ty) => {
            let def_path = tcx.def_path_str(uv.def);
            let def_kind = tcx.def_kind(uv.def);
            format!(
                "Const::Unevaluated(def={def_path}, def_kind={def_kind:?}, args={:?}, promoted={:?}, ty={ty:?})",
                uv.args, uv.promoted
            )
        }
        Const::Val(val, ty) => format!("Const::Val(val={val:?}, ty={ty:?})"),
    };
    format!(
        "{kind_str} [is_required_const={}]",
        c.const_.is_required_const()
    )
}

fn format_operand<'tcx>(tcx: TyCtxt<'tcx>, op: &Operand<'tcx>) -> String {
    match op {
        Operand::Copy(p) => format!("Copy({p:?})"),
        Operand::Move(p) => format!("Move({p:?})"),
        Operand::Constant(c) => format!("Constant({})", format_const_op(tcx, c)),
        Operand::RuntimeChecks(r) => format!("RuntimeChecks({r:?})"),
    }
}

fn format_body<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId, stage: &str, body: &Body<'tcx>) -> String {
    let mut out = String::new();
    let path = tcx.def_path_str(def);
    let def_kind = tcx.def_kind(def);
    out.push_str(&format!(
        "=== ITEM `{path}` ({def_kind:?}) @ {stage} (phase={:?}) ===\n",
        body.phase
    ));
    match &body.required_consts {
        None => out.push_str("  required_consts: None\n"),
        Some(rcs) => {
            out.push_str(&format!("  required_consts: Some(len={})\n", rcs.len()));
            for (i, rc) in rcs.iter().enumerate() {
                out.push_str(&format!("    [{i}] {}\n", format_const_op(tcx, rc)));
            }
        }
    }
    let reachable: std::collections::BTreeSet<_> =
        traversal::preorder(body).map(|(bb, _)| bb).collect();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if data.is_cleanup {
            continue;
        }
        let is_reach = reachable.contains(&bb);
        out.push_str(&format!("  {bb:?} (reachable={is_reach}):\n"));
        for (si, stmt) in data.statements.iter().enumerate() {
            match &stmt.kind {
                StatementKind::Assign(b) => {
                    let (place, rv) = &**b;
                    let rv_str = match rv {
                        Rvalue::Use(op, retag) => {
                            format!("Use({}, retag={retag:?})", format_operand(tcx, op))
                        }
                        Rvalue::Repeat(op, cnt) => {
                            format!("Repeat({}, count={cnt:?})", format_operand(tcx, op))
                        }
                        Rvalue::BinaryOp(op, ops) => format!(
                            "BinaryOp({op:?}, {}, {})",
                            format_operand(tcx, &ops.0),
                            format_operand(tcx, &ops.1)
                        ),
                        Rvalue::UnaryOp(op, opnd) => {
                            format!("UnaryOp({op:?}, {})", format_operand(tcx, opnd))
                        }
                        other => format!("{other:?}"),
                    };
                    out.push_str(&format!("    stmt[{si}]: Assign({place:?} = {rv_str})\n"));
                }
                StatementKind::StorageLive(_) | StatementKind::StorageDead(_) => {}
                other => {
                    out.push_str(&format!("    stmt[{si}]: {other:?}\n"));
                }
            }
        }
        let term = data.terminator();
        let term_str = match &term.kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                let args_str: Vec<_> = args
                    .iter()
                    .map(|a| format_operand(tcx, &a.node))
                    .collect();
                format!(
                    "Call(func={}, args=[{}], dest={destination:?}, target={target:?})",
                    format_operand(tcx, func),
                    args_str.join(", ")
                )
            }
            other => format!("{other:?}"),
        };
        out.push_str(&format!("    terminator: {term_str}\n"));
    }
    out
}

fn hook_mir_built<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId) -> &'tcx Steal<Body<'tcx>> {
    let orig = ORIG_MIR_BUILT.get().unwrap();
    let steal = orig(tcx, def);
    let txt = format_body(tcx, def, "mir_built", &steal.borrow());
    STAGES
        .lock()
        .unwrap()
        .as_mut()
        .unwrap()
        .mir_built
        .insert(tcx.def_path_str(def), txt);
    steal
}

fn hook_mir_promoted<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
) -> (
    &'tcx Steal<Body<'tcx>>,
    &'tcx Steal<IndexVec<Promoted, Body<'tcx>>>,
) {
    let orig = ORIG_MIR_PROMOTED.get().unwrap();
    let (steal_body, steal_prom) = orig(tcx, def);
    let mut txt = format_body(tcx, def, "mir_promoted", &steal_body.borrow());
    let prom = steal_prom.borrow();
    if !prom.is_empty() {
        txt.push_str(&format!("  promoted fragments: {}\n", prom.len()));
        for (p_idx, p_body) in prom.iter_enumerated() {
            txt.push_str(&format!(
                "  --- promoted[{p_idx:?}] ---\n{}",
                format_body(tcx, def, "promoted_fragment", p_body)
            ));
        }
    }
    STAGES
        .lock()
        .unwrap()
        .as_mut()
        .unwrap()
        .mir_promoted
        .insert(tcx.def_path_str(def), txt);
    (steal_body, steal_prom)
}

fn hook_mir_drops<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId) -> &'tcx Steal<Body<'tcx>> {
    let orig = ORIG_MIR_DROPS.get().unwrap();
    let steal = orig(tcx, def);
    let txt = format_body(
        tcx,
        def,
        "mir_drops_elaborated_and_const_checked",
        &steal.borrow(),
    );
    STAGES
        .lock()
        .unwrap()
        .as_mut()
        .unwrap()
        .mir_drops
        .insert(tcx.def_path_str(def), txt);
    steal
}

fn override_queries(_sess: &Session, providers: &mut Providers) {
    let _ = ORIG_MIR_BUILT.set(providers.queries.mir_built);
    let _ = ORIG_MIR_PROMOTED.set(providers.queries.mir_promoted);
    let _ = ORIG_MIR_DROPS.set(providers.queries.mir_drops_elaborated_and_const_checked);
    providers.queries.mir_built = hook_mir_built;
    providers.queries.mir_promoted = hook_mir_promoted;
    providers.queries.mir_drops_elaborated_and_const_checked = hook_mir_drops;
}

struct ProbeCallbacks;

impl rustc_driver::Callbacks for ProbeCallbacks {
    fn config(&mut self, config: &mut interface::Config) {
        *STAGES.lock().unwrap() = Some(CapturedStages::default());
        config.override_queries = Some(override_queries);
    }

    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        let mut defs: Vec<LocalDefId> = tcx.hir_body_owners().collect();
        defs.sort_by_key(|d| tcx.def_path_str(*d));

        let mut ctfe_or_opt = BTreeMap::new();
        for def in &defs {
            let path = tcx.def_path_str(*def);
            if !tcx.is_trivial_const(*def) {
                let _ = tcx.mir_drops_elaborated_and_const_checked(*def);
            } else {
                let _ = tcx.mir_built(*def);
            }
            match tcx.def_kind(*def) {
                DefKind::Fn | DefKind::AssocFn => {
                    let opt_body = tcx.optimized_mir(def.to_def_id());
                    ctfe_or_opt.insert(
                        path,
                        format_body(tcx, *def, "optimized_mir", opt_body),
                    );
                }
                DefKind::Const { .. }
                | DefKind::AssocConst { .. }
                | DefKind::InlineConst
                | DefKind::AnonConst => {
                    if !tcx.is_trivial_const(*def) {
                        let ctfe_body = tcx.mir_for_ctfe(def.to_def_id());
                        ctfe_or_opt.insert(
                            path,
                            format_body(tcx, *def, "mir_for_ctfe", ctfe_body),
                        );
                    } else {
                        ctfe_or_opt.insert(
                            path,
                            format!(
                                "=== ITEM `{}` ({:?}) @ mir_for_ctfe ===\n  [trivial_const = true]\n",
                                tcx.def_path_str(*def),
                                tcx.def_kind(*def)
                            ),
                        );
                    }
                }
                _ => {}
            }
        }

        let stages = STAGES.lock().unwrap().take().unwrap();
        for def in &defs {
            let path = tcx.def_path_str(*def);
            println!("################################################################################");
            println!("### DEF: {path} ({:?})", tcx.def_kind(*def));
            println!("################################################################################");
            if let Some(s) = stages.mir_built.get(&path) {
                print!("{s}");
            }
            if let Some(s) = stages.mir_promoted.get(&path) {
                print!("{s}");
            }
            if let Some(s) = stages.mir_drops.get(&path) {
                print!("{s}");
            }
            if let Some(s) = ctfe_or_opt.get(&path) {
                print!("{s}");
            }
            println!();
        }

        Compilation::Stop
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut cb = ProbeCallbacks;
    rustc_driver::run_compiler(&args, &mut cb);
}
