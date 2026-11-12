// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![feature(rustc_private, box_patterns)]
#![allow(dead_code)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir_transform;
extern crate rustc_session;
extern crate rustc_span;

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fs::File;
use std::io::Write;
use std::sync::OnceLock;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::LocalDefId;
use rustc_interface::interface::{Compiler, Config};
use rustc_middle::mir::{
    Body, ClearCrossCrate, NonDivergingIntrinsic, Operand, Rvalue, StatementKind, TerminatorKind,
};
use rustc_middle::ty::{InstanceKind, TyCtxt};
use rustc_middle::util::Providers;
use rustc_session::Session;
use rustc_span::FileName;

type MirStealProvider =
    for<'tcx> fn(TyCtxt<'tcx>, LocalDefId) -> &'tcx rustc_data_structures::steal::Steal<Body<'tcx>>;

static DEFAULT_MIR_DROPS_ELABORATED: OnceLock<MirStealProvider> = OnceLock::new();

#[derive(Clone, Debug, PartialEq, Eq)]
struct BodySummary {
    phase: String,
    bb_count: usize,
    local_count: usize,
    cleared_local_info_count: usize,
    stmt_count: usize,
    storage_marker_count: usize,
    fake_read_count: usize,
    ascribe_user_type_count: usize,
    place_mention_count: usize,
    const_eval_counter_count: usize,
    assume_count: usize,
    runtime_checks_ops: Vec<String>,
    required_consts_len: Option<usize>,
    mentioned_items_len: Option<usize>,
    blocks: Vec<BlockSummary>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct BlockSummary {
    bb: usize,
    is_cleanup: bool,
    stmts: Vec<String>,
    terminator: String,
}

fn summarize_body<'tcx>(body: &Body<'tcx>) -> BodySummary {
    let mut stmt_count = 0;
    let mut storage_marker_count = 0;
    let mut fake_read_count = 0;
    let mut ascribe_user_type_count = 0;
    let mut place_mention_count = 0;
    let mut const_eval_counter_count = 0;
    let mut assume_count = 0;
    let mut runtime_checks_ops = Vec::new();
    let mut blocks = Vec::new();

    for (bb_idx, bb) in body.basic_blocks.iter_enumerated() {
        let mut stmts = Vec::new();
        for stmt in &bb.statements {
            stmt_count += 1;
            match &stmt.kind {
                StatementKind::StorageLive(_) | StatementKind::StorageDead(_) => {
                    storage_marker_count += 1;
                }
                StatementKind::FakeRead(_) => {
                    fake_read_count += 1;
                }
                StatementKind::AscribeUserType(_, _) => {
                    ascribe_user_type_count += 1;
                }
                StatementKind::PlaceMention(_) => {
                    place_mention_count += 1;
                }
                StatementKind::ConstEvalCounter => {
                    const_eval_counter_count += 1;
                }
                StatementKind::Intrinsic(box NonDivergingIntrinsic::Assume(_)) => {
                    assume_count += 1;
                }
                StatementKind::Assign(box (_, Rvalue::Use(Operand::RuntimeChecks(rc), _))) => {
                    runtime_checks_ops.push(format!("{rc:?}"));
                }
                _ => {}
            }
            stmts.push(summarize_stmt(&stmt.kind));
        }
        let terminator = summarize_terminator(&bb.terminator().kind);
        blocks.push(BlockSummary {
            bb: bb_idx.as_usize(),
            is_cleanup: bb.is_cleanup,
            stmts,
            terminator,
        });
    }

    let cleared_local_info_count = body
        .local_decls
        .iter()
        .filter(|d| matches!(d.local_info, ClearCrossCrate::Clear))
        .count();

    BodySummary {
        phase: format!("{:?}", body.phase),
        bb_count: body.basic_blocks.len(),
        local_count: body.local_decls.len(),
        cleared_local_info_count,
        stmt_count,
        storage_marker_count,
        fake_read_count,
        ascribe_user_type_count,
        place_mention_count,
        const_eval_counter_count,
        assume_count,
        runtime_checks_ops,
        required_consts_len: body.required_consts.as_ref().map(|v| v.len()),
        mentioned_items_len: body.mentioned_items.as_ref().map(|v| v.len()),
        blocks,
    }
}

fn summarize_stmt<'tcx>(kind: &StatementKind<'tcx>) -> String {
    match kind {
        StatementKind::Assign(box (place, rval)) => {
            format!("Assign({place:?}, {})", summarize_rvalue(rval))
        }
        StatementKind::StorageLive(l) => format!("StorageLive({l:?})"),
        StatementKind::StorageDead(l) => format!("StorageDead({l:?})"),
        StatementKind::FakeRead(box (cause, place)) => format!("FakeRead({cause:?}, {place:?})"),
        StatementKind::AscribeUserType(_, _) => "AscribeUserType(..)".to_string(),
        StatementKind::PlaceMention(place) => format!("PlaceMention({place:?})"),
        StatementKind::ConstEvalCounter => "ConstEvalCounter".to_string(),
        StatementKind::Intrinsic(box NonDivergingIntrinsic::Assume(op)) => {
            format!("Assume({op:?})")
        }
        StatementKind::Intrinsic(box NonDivergingIntrinsic::CopyNonOverlapping(_)) => {
            "CopyNonOverlapping(..)".to_string()
        }
        StatementKind::Nop => "Nop".to_string(),
        other => format!("{other:?}"),
    }
}

fn summarize_rvalue<'tcx>(rval: &Rvalue<'tcx>) -> String {
    match rval {
        Rvalue::Use(op, retag) => format!("Use({op:?}, retag={retag:?})"),
        Rvalue::BinaryOp(op, box (l, r)) => format!("BinaryOp({op:?}, {l:?}, {r:?})"),
        Rvalue::UnaryOp(op, arg) => format!("UnaryOp({op:?}, {arg:?})"),
        Rvalue::Cast(kind, op, ty) => format!("Cast({kind:?}, {op:?}, {ty:?})"),
        Rvalue::Ref(_, bk, place) => format!("Ref({bk:?}, {place:?})"),
        Rvalue::RawPtr(kind, place) => format!("RawPtr({kind:?}, {place:?})"),
        Rvalue::Aggregate(box kind, ops) => format!("Aggregate({kind:?}, len={})", ops.len()),
        Rvalue::Discriminant(place) => format!("Discriminant({place:?})"),
        other => format!("{other:?}"),
    }
}

fn summarize_terminator<'tcx>(kind: &TerminatorKind<'tcx>) -> String {
    match kind {
        TerminatorKind::Goto { target } => format!("Goto({target:?})"),
        TerminatorKind::SwitchInt { discr, targets } => {
            let branches: Vec<String> = targets
                .iter()
                .map(|(val, tgt)| format!("{val}: {tgt:?}"))
                .collect();
            format!(
                "SwitchInt({discr:?}, [{}], otherwise: {:?})",
                branches.join(", "),
                targets.otherwise()
            )
        }
        TerminatorKind::Return => "Return".to_string(),
        TerminatorKind::Unreachable => "Unreachable".to_string(),
        TerminatorKind::UnwindResume => "UnwindResume".to_string(),
        TerminatorKind::UnwindTerminate(r) => format!("UnwindTerminate({r:?})"),
        TerminatorKind::Drop { place, target, unwind, .. } => {
            format!("Drop({place:?}, target={target:?}, unwind={unwind:?})")
        }
        TerminatorKind::Call { func, args, destination, target, .. } => {
            format!(
                "Call(func={func:?}, argc={}, dest={destination:?}, target={target:?})",
                args.len()
            )
        }
        TerminatorKind::Assert { cond, expected, msg, target, .. } => {
            format!(
                "Assert(cond={cond:?}, expected={expected}, msg={msg:?}, optional_overflow={}, target={target:?})",
                msg.is_optional_overflow_check()
            )
        }
        other => format!("{other:?}"),
    }
}

thread_local! {
    static HOOK_CAPTURED: RefCell<BTreeMap<u32, BodySummary>> = const { RefCell::new(BTreeMap::new()) };
}

fn override_queries(_sess: &Session, providers: &mut Providers) {
    DEFAULT_MIR_DROPS_ELABORATED
        .get_or_init(|| providers.queries.mir_drops_elaborated_and_const_checked);
    providers.queries.mir_drops_elaborated_and_const_checked = hooked_mir_drops_elaborated;
}

fn hooked_mir_drops_elaborated<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
) -> &'tcx rustc_data_structures::steal::Steal<Body<'tcx>> {
    let default_provider = DEFAULT_MIR_DROPS_ELABORATED.get().unwrap();
    let steal = default_provider(tcx, def);
    let summary = summarize_body(&steal.borrow());
    HOOK_CAPTURED.with(|cell| {
        cell.borrow_mut().insert(def.local_def_index.as_u32(), summary);
    });
    steal
}

fn sysroot_path() -> String {
    if let Ok(s) = std::env::var("SYSROOT") {
        return s;
    }
    let out = std::process::Command::new("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .expect("rustc --print sysroot");
    String::from_utf8(out.stdout).unwrap().trim().to_string()
}

#[derive(Clone, Debug)]
struct StealStatusRecord {
    def_index: u32,
    def_path: String,
    def_kind: String,
    const_context: String,
    is_trivial_const: bool,
    is_constructor: bool,
    is_coroutine: bool,
    mir_built_is_stolen: bool,
    mir_promoted_0_is_stolen: Option<bool>,
    mir_promoted_1_is_stolen: Option<bool>,
    // Snapshot of .is_stolen() taken BEFORE after_analysis forces any queries on other items:
    mir_drops_is_stolen_at_entry: Option<bool>,
    // Snapshot of .is_stolen() after all items have had mir_drops_elaborated_and_const_checked forced:
    mir_drops_is_stolen_after_all_drops_elaborated: Option<bool>,
    promoted_mir_count_at_after_analysis: Option<usize>,
    hook_captured_postcleanup: Option<BodySummary>,
    direct_borrow_postcleanup_ok: bool,
    mir_for_ctfe_summary: Option<BodySummary>,
    mir_for_ctfe_matches_postcleanup_modulo_counter: Option<bool>,
    optimized_mir_summary: Option<BodySummary>,
    instance_mir_summary: Option<BodySummary>,
}

struct ProbeCallbacks {
    use_hook: bool,
    source_code: String,
    records: Vec<StealStatusRecord>,
}

impl Callbacks for ProbeCallbacks {
    fn config(&mut self, config: &mut Config) {
        let src = self.source_code.clone();
        config.input = rustc_session::config::Input::Str {
            name: FileName::Custom("probe_input.rs".to_string()),
            input: src,
        };
        if self.use_hook {
            HOOK_CAPTURED.with(|c| c.borrow_mut().clear());
            config.override_queries = Some(override_queries);
        }
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let mut keys: Vec<LocalDefId> = tcx.mir_keys(()).iter().copied().collect();
        keys.sort_by_key(|d| d.local_def_index.as_u32());

        // Pass 1: Force `mir_drops_elaborated_and_const_checked` ONLY if it has already been
        // computed during `analysis`, wait: calling `tcx.mir_drops_elaborated_and_const_checked(def)`
        // computes it if not yet computed!
        // Under `--emit=metadata`, `analysis` did NOT call `mir_drops_elaborated_and_const_checked`
        // on non-const functions (`S::method`, `regular_fn`, etc.).
        // Let's first record `.is_stolen()` for each item as we call `mir_drops_elaborated_and_const_checked`
        // on that item alone, and THEN record `.is_stolen()` after all items have had
        // `mir_drops_elaborated_and_const_checked` computed!
        let mut entry_steal_map = BTreeMap::new();
        for &def in &keys {
            let is_trivial = tcx.is_trivial_const(def);
            let is_ctor = tcx.is_constructor(def.to_def_id());
            if !is_trivial && !is_ctor {
                let stolen = tcx.mir_drops_elaborated_and_const_checked(def).is_stolen();
                entry_steal_map.insert(def.local_def_index.as_u32(), stolen);
            }
        }

        let mut post_all_drops_steal_map = BTreeMap::new();
        for &def in &keys {
            let is_trivial = tcx.is_trivial_const(def);
            let is_ctor = tcx.is_constructor(def.to_def_id());
            if !is_trivial && !is_ctor {
                let stolen = tcx.mir_drops_elaborated_and_const_checked(def).is_stolen();
                post_all_drops_steal_map.insert(def.local_def_index.as_u32(), stolen);
            }
        }

        for def in keys {
            let def_index = def.local_def_index.as_u32();
            let def_path = tcx.def_path_str(def);
            let dk = tcx.def_kind(def);
            let def_kind = format!("{dk:?}");
            let const_ctx = tcx.hir_body_const_context(def);
            let const_context = format!("{const_ctx:?}");
            let is_trivial = tcx.is_trivial_const(def);
            let is_ctor = tcx.is_constructor(def.to_def_id());
            let is_coro = tcx.is_coroutine(def.to_def_id());

            let mir_built_is_stolen = if !is_ctor {
                tcx.mir_built(def).is_stolen()
            } else {
                false
            };

            let (mir_promoted_0_is_stolen, mir_promoted_1_is_stolen) = if !is_trivial && !is_ctor {
                let (p0, p1) = tcx.mir_promoted(def);
                (Some(p0.is_stolen()), Some(p1.is_stolen()))
            } else {
                (None, None)
            };

            let mir_drops_is_stolen_at_entry = entry_steal_map.get(&def_index).copied();
            let mir_drops_is_stolen_after_all = post_all_drops_steal_map.get(&def_index).copied();

            let direct_borrow_postcleanup_ok = if !is_trivial && !is_ctor {
                let st = tcx.mir_drops_elaborated_and_const_checked(def);
                if !st.is_stolen() {
                    let _b = st.borrow();
                    true
                } else {
                    false
                }
            } else {
                false
            };

            let promoted_mir_count = if !is_trivial && !is_ctor {
                Some(tcx.promoted_mir(def).len())
            } else {
                None
            };

            let hook_captured = HOOK_CAPTURED.with(|c| c.borrow().get(&def_index).cloned());

            let mir_for_ctfe_summary = if !is_trivial && (const_ctx.is_some() || is_ctor) {
                Some(summarize_body(tcx.mir_for_ctfe(def)))
            } else {
                None
            };

            let mir_for_ctfe_matches_postcleanup_modulo_counter =
                match (&hook_captured, &mir_for_ctfe_summary) {
                    (Some(post), Some(ctfe)) => {
                        let mut ctfe_stripped = ctfe.clone();
                        ctfe_stripped.stmt_count -= ctfe_stripped.const_eval_counter_count;
                        ctfe_stripped.const_eval_counter_count = 0;
                        for b in &mut ctfe_stripped.blocks {
                            b.stmts.retain(|s| s != "ConstEvalCounter");
                        }
                        Some(*post == ctfe_stripped)
                    }
                    _ => None,
                };

            let optimized_mir_summary = if matches!(
                dk,
                DefKind::Fn | DefKind::AssocFn | DefKind::Closure | DefKind::Ctor(..)
            ) {
                Some(summarize_body(tcx.optimized_mir(def)))
            } else {
                None
            };

            let instance_mir_summary = if !is_trivial {
                Some(summarize_body(
                    tcx.instance_mir(InstanceKind::Item(def.to_def_id())),
                ))
            } else {
                None
            };

            self.records.push(StealStatusRecord {
                def_index,
                def_path,
                def_kind,
                const_context,
                is_trivial_const: is_trivial,
                is_constructor: is_ctor,
                is_coroutine: is_coro,
                mir_built_is_stolen,
                mir_promoted_0_is_stolen,
                mir_promoted_1_is_stolen,
                mir_drops_is_stolen_at_entry,
                mir_drops_is_stolen_after_all_drops_elaborated: mir_drops_is_stolen_after_all,
                promoted_mir_count_at_after_analysis: promoted_mir_count,
                hook_captured_postcleanup: hook_captured,
                direct_borrow_postcleanup_ok,
                mir_for_ctfe_summary,
                mir_for_ctfe_matches_postcleanup_modulo_counter,
                optimized_mir_summary,
                instance_mir_summary,
            });
        }

        Compilation::Stop
    }
}

fn run_probe_session(
    use_hook: bool,
    source_code: &str,
    extra_args: &[&str],
) -> Vec<StealStatusRecord> {
    let mut args = vec![
        "probe_driver".to_string(),
        "probe_input.rs".to_string(),
        "--crate-type=lib".to_string(),
        "--edition=2021".to_string(),
        "--sysroot".to_string(),
        sysroot_path(),
    ];
    for a in extra_args {
        args.push((*a).to_string());
    }
    let mut cb = ProbeCallbacks {
        use_hook,
        source_code: source_code.to_string(),
        records: Vec::new(),
    };
    rustc_driver::run_compiler(&args, &mut cb);
    cb.records
}

fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn opt_bool_json(v: Option<bool>) -> String {
    match v {
        Some(b) => b.to_string(),
        None => "null".to_string(),
    }
}

fn opt_usize_json(v: Option<usize>) -> String {
    match v {
        Some(n) => n.to_string(),
        None => "null".to_string(),
    }
}

fn summary_json(s: &Option<BodySummary>) -> String {
    let Some(b) = s else {
        return "null".to_string();
    };
    let blocks_json: Vec<String> = b
        .blocks
        .iter()
        .map(|blk| {
            let stmts: Vec<String> = blk.stmts.iter().map(|st| json_escape(st)).collect();
            format!(
                "{{\"bb\":{},\"is_cleanup\":{},\"stmts\":[{}],\"terminator\":{}}}",
                blk.bb,
                blk.is_cleanup,
                stmts.join(","),
                json_escape(&blk.terminator)
            )
        })
        .collect();
    let rc_json: Vec<String> = b.runtime_checks_ops.iter().map(|x| json_escape(x)).collect();
    format!(
        "{{\"phase\":{},\"bb_count\":{},\"local_count\":{},\"cleared_local_info_count\":{},\"stmt_count\":{},\"storage_marker_count\":{},\"fake_read_count\":{},\"ascribe_user_type_count\":{},\"place_mention_count\":{},\"const_eval_counter_count\":{},\"assume_count\":{},\"runtime_checks_ops\":[{}],\"required_consts_len\":{},\"mentioned_items_len\":{},\"blocks\":[{}]}}",
        json_escape(&b.phase),
        b.bb_count,
        b.local_count,
        b.cleared_local_info_count,
        b.stmt_count,
        b.storage_marker_count,
        b.fake_read_count,
        b.ascribe_user_type_count,
        b.place_mention_count,
        b.const_eval_counter_count,
        b.assume_count,
        rc_json.join(","),
        opt_usize_json(b.required_consts_len),
        opt_usize_json(b.mentioned_items_len),
        blocks_json.join(",")
    )
}

fn main() {
    let exp1_src = r#"
#![feature(core_intrinsics, rustc_attrs)]
#![allow(internal_features, dead_code)]

pub struct TupleS(pub u32);
pub struct S(pub u32);
pub struct Gen<T>(pub T);

impl S {
    pub const ASSOC_C_UNUSED: u32 = 3 + 4;
    pub const ASSOC_C_USED: u32 = 5 + 6;
    pub fn method(self) -> u32 {
        self.0 + Self::ASSOC_C_USED
    }
}

impl<T> Gen<T> {
    pub const GEN_C_UNUSED: usize = 10 + 20;
}

pub enum E {
    V0 = 1 + 2,
    V1 = 4,
}

pub const TRIVIAL_CONST: u32 = 42;
pub const NONTRIVIAL_CONST_UNUSED: u32 = 40 + 2;
pub static STATIC_ITEM: u32 = 10 + 5;

pub const fn const_fn_used(x: u32) -> u32 {
    x + 1
}

pub const fn const_fn_unused(x: u32) -> u32 {
    let mut acc = 0;
    let mut i = 0;
    while i < x {
        acc += i;
        i += 1;
    }
    acc
}

pub const CALLS_CONST_FN: u32 = const_fn_used(10);

pub fn regular_fn(a: u32, b: u32) -> [u8; const_fn_used(2) as usize] {
    let y = const { 7 + 8 };
    let _clos = |z: u32| z + y;
    let copy_a = a;
    let _unit: () = ();
    let _sum = copy_a + b;
    [0; 3]
}

pub fn with_promoted() -> &'static u32 {
    &(100 + 200)
}

pub unsafe fn raw_ptr_deref(p: *const u32, b: *const bool) -> (u32, bool) {
    (*p, *b)
}

pub async fn async_fn_example(x: u32) -> u32 {
    x + 1
}
"#;

    println!("=== EXP 1A & 1B: Steal<Body> Lifetimes (--emit=metadata vs --emit=link) ===");
    let records_meta = run_probe_session(
        true,
        exp1_src,
        &[
            "-Copt-level=0",
            "-Cdebug-assertions=off",
            "-Coverflow-checks=off",
            "--emit=metadata",
        ],
    );
    let records_link = run_probe_session(
        false,
        exp1_src,
        &[
            "-Copt-level=0",
            "-Cdebug-assertions=off",
            "-Coverflow-checks=off",
            "--emit=link",
        ],
    );
    for (rm, rl) in records_meta.iter().zip(records_link.iter()) {
        println!(
            "DefIdx {:2} | {:32} | kind={:20} | meta_entry={:5?} | meta_after_all={:5?} | link_entry={:5?} | ctfe_eq_post={:5?} | promoted_cnt={:?}",
            rm.def_index,
            rm.def_path,
            &rm.def_kind[..rm.def_kind.len().min(20)],
            rm.mir_drops_is_stolen_at_entry,
            rm.mir_drops_is_stolen_after_all_drops_elaborated,
            rl.mir_drops_is_stolen_at_entry,
            rm.mir_for_ctfe_matches_postcleanup_modulo_counter,
            rm.promoted_mir_count_at_after_analysis,
        );
        // After all items have had mir_drops_elaborated_and_const_checked run,
        // --emit=metadata and --emit=link have the EXACT same steal state!
        assert_eq!(
            rm.mir_drops_is_stolen_after_all_drops_elaborated,
            rl.mir_drops_is_stolen_after_all_drops_elaborated,
            "Post-all steal mismatch for {}",
            rm.def_path
        );
    }

    println!("\n=== EXP 2: Phase Comparison (Runtime(PostCleanup) vs mir_for_ctfe vs optimized_mir) ===");
    let records_opt0_ub_on = run_probe_session(
        true,
        exp1_src,
        &[
            "-Copt-level=0",
            "-Cdebug-assertions=on",
            "-Coverflow-checks=off",
            "--emit=metadata",
        ],
    );
    let records_miropt0_ub_off = run_probe_session(
        true,
        exp1_src,
        &[
            "-Copt-level=0",
            "-Zmir-opt-level=0",
            "-Cdebug-assertions=off",
            "-Coverflow-checks=off",
            "--emit=metadata",
        ],
    );
    let records_miropt0_ub_on = run_probe_session(
        true,
        exp1_src,
        &[
            "-Copt-level=0",
            "-Zmir-opt-level=0",
            "-Cdebug-assertions=on",
            "-Coverflow-checks=off",
            "--emit=metadata",
        ],
    );
    for (((r_def, r_ub_on), r_m0_ub0), r_m0_ub1) in records_meta
        .iter()
        .zip(records_opt0_ub_on.iter())
        .zip(records_miropt0_ub_off.iter())
        .zip(records_miropt0_ub_on.iter())
    {
        if let (Some(post), Some(opt_def), Some(opt_ub), Some(opt_m0), Some(opt_m0_ub1)) = (
            &r_def.hook_captured_postcleanup,
            &r_def.optimized_mir_summary,
            &r_ub_on.optimized_mir_summary,
            &r_m0_ub0.optimized_mir_summary,
            &r_m0_ub1.optimized_mir_summary,
        ) {
            println!(
                "Item {:28}:\n  PostCleanup        : phase={:22} bbs={:2} locals={:2} (cleared={:2}) stmts={:2} storage={:2} assume={:2} req_consts={:?} mentioned={:?}\n  Opt(O0,M=1,ub=off) : phase={:22} bbs={:2} locals={:2} (cleared={:2}) stmts={:2} storage={:2} assume={:2} req_consts={:?} mentioned={:?}\n  Opt(O0,M=1,ub=on)  : phase={:22} bbs={:2} locals={:2} (cleared={:2}) stmts={:2} storage={:2} assume={:2} req_consts={:?} mentioned={:?}\n  Opt(O0,M=0,ub=off) : phase={:22} bbs={:2} locals={:2} (cleared={:2}) stmts={:2} storage={:2} assume={:2} req_consts={:?} mentioned={:?}\n  Opt(O0,M=0,ub=on)  : phase={:22} bbs={:2} locals={:2} (cleared={:2}) stmts={:2} storage={:2} assume={:2} req_consts={:?} mentioned={:?}",
                r_def.def_path,
                post.phase, post.bb_count, post.local_count, post.cleared_local_info_count, post.stmt_count, post.storage_marker_count, post.assume_count, post.required_consts_len, post.mentioned_items_len,
                opt_def.phase, opt_def.bb_count, opt_def.local_count, opt_def.cleared_local_info_count, opt_def.stmt_count, opt_def.storage_marker_count, opt_def.assume_count, opt_def.required_consts_len, opt_def.mentioned_items_len,
                opt_ub.phase, opt_ub.bb_count, opt_ub.local_count, opt_ub.cleared_local_info_count, opt_ub.stmt_count, opt_ub.storage_marker_count, opt_ub.assume_count, opt_ub.required_consts_len, opt_ub.mentioned_items_len,
                opt_m0.phase, opt_m0.bb_count, opt_m0.local_count, opt_m0.cleared_local_info_count, opt_m0.stmt_count, opt_m0.storage_marker_count, opt_m0.assume_count, opt_m0.required_consts_len, opt_m0.mentioned_items_len,
                opt_m0_ub1.phase, opt_m0_ub1.bb_count, opt_m0_ub1.local_count, opt_m0_ub1.cleared_local_info_count, opt_m0_ub1.stmt_count, opt_m0_ub1.storage_marker_count, opt_m0_ub1.assume_count, opt_m0_ub1.required_consts_len, opt_m0_ub1.mentioned_items_len,
            );
        }
    }

    println!("\n=== EXP 3A: --release vs --debug Divergence Matrix at Runtime(PostCleanup) ===");
    let exp3_src = r#"
#![feature(core_intrinsics, rustc_attrs)]
#![allow(internal_features, dead_code)]

pub fn op_add(a: u32, b: u32) -> u32 { a + b }
pub fn op_sub(a: u32, b: u32) -> u32 { a - b }
pub fn op_mul(a: u32, b: u32) -> u32 { a * b }
pub fn op_add_assign(mut a: u32, b: u32) -> u32 { a += b; a }
pub fn op_shl_u32(a: u32, b: u32) -> u32 { a << b }
pub fn op_shr_i32_rhs(a: u32, b: i32) -> u32 { a >> b }
pub fn op_neg_signed(a: i32) -> i32 { -a }
pub fn op_not_signed(a: i32) -> i32 { !a }
pub fn op_div_unsigned(a: u32, b: u32) -> u32 { a / b }
pub fn op_rem_unsigned(a: u32, b: u32) -> u32 { a % b }
pub fn op_div_signed(a: i32, b: i32) -> i32 { a / b }
pub fn op_index(arr: &[u32; 4], i: usize) -> u32 { arr[i] }
pub fn op_wrapping_add(a: u32, b: u32) -> u32 { a.wrapping_add(b) }
pub fn op_checked_add(a: u32, b: u32) -> Option<u32> { a.checked_add(b) }
pub unsafe fn op_unchecked_add(a: u32, b: u32) -> u32 { core::intrinsics::unchecked_add(a, b) }
#[rustc_inherit_overflow_checks]
pub fn op_inherit_overflow(a: u32, b: u32) -> u32 { a + b }
pub const CONST_ADD: u32 = 10 + 20;
pub const fn const_fn_add(a: u32, b: u32) -> u32 { a + b }
pub fn intrinsic_runtime_checks() -> (bool, bool) {
    (core::intrinsics::ub_checks(), core::intrinsics::overflow_checks())
}
pub fn with_debug_assert_simple(x: u32) -> u32 {
    debug_assert!(x > 0);
    x
}
pub fn with_debug_assert_arith(x: u32, y: u32) -> u32 {
    debug_assert!(x + y > 0);
    x
}
pub fn with_cfg_macro(x: u32) -> u32 {
    if cfg!(debug_assertions) { x.wrapping_add(1) } else { x }
}
"#;

    let p_rel = run_probe_session(
        true,
        exp3_src,
        &["-Copt-level=0", "-Cdebug-assertions=off", "-Coverflow-checks=off", "--emit=metadata"],
    );
    let p_dbg_only = run_probe_session(
        true,
        exp3_src,
        &["-Copt-level=0", "-Cdebug-assertions=on", "-Coverflow-checks=off", "--emit=metadata"],
    );
    let p_ovf_only = run_probe_session(
        true,
        exp3_src,
        &["-Copt-level=0", "-Cdebug-assertions=off", "-Coverflow-checks=on", "--emit=metadata"],
    );
    let p_dbg = run_probe_session(
        true,
        exp3_src,
        &["-Copt-level=0", "-Cdebug-assertions=on", "-Coverflow-checks=on", "--emit=metadata"],
    );

    for (((r00, r10), r01), r11) in p_rel
        .iter()
        .zip(p_dbg_only.iter())
        .zip(p_ovf_only.iter())
        .zip(p_dbg.iter())
    {
        let (Some(b00), Some(b10), Some(b01), Some(b11)) = (
            r00.hook_captured_postcleanup.as_ref(),
            r10.hook_captured_postcleanup.as_ref(),
            r01.hook_captured_postcleanup.as_ref(),
            r11.hook_captured_postcleanup.as_ref(),
        ) else {
            continue;
        };
        let eq_dbg = b00 == b10;
        let eq_ovf = b00 == b01;
        let eq_full = b00 == b11;
        println!(
            "Item {:28} | eq(00,10_dbg_only)={:5} | eq(00,01_ovf_only)={:5} | eq(00,11_full_dbg)={:5} | bbs(00/10/01/11)={}/{}/{}/{}",
            r00.def_path,
            eq_dbg,
            eq_ovf,
            eq_full,
            b00.bb_count,
            b10.bb_count,
            b01.bb_count,
            b11.bb_count,
        );
    }

    // Print detailed blocks of with_debug_assert_simple under 00 (release) vs 10 (debug_assertions=on)
    let da_rel = p_rel.iter().find(|r| r.def_path == "with_debug_assert_simple").unwrap();
    let da_dbg = p_dbg_only.iter().find(|r| r.def_path == "with_debug_assert_simple").unwrap();
    println!("\n--- with_debug_assert_simple PostCleanup blocks (release: debug_assertions=off) ---");
    for blk in &da_rel.hook_captured_postcleanup.as_ref().unwrap().blocks {
        println!("  bb{} (cleanup={}): stmts={:?} term={}", blk.bb, blk.is_cleanup, blk.stmts, blk.terminator);
    }
    println!("--- with_debug_assert_simple PostCleanup blocks (debug: debug_assertions=on) ---");
    for blk in &da_dbg.hook_captured_postcleanup.as_ref().unwrap().blocks {
        println!("  bb{} (cleanup={}): stmts={:?} term={}", blk.bb, blk.is_cleanup, blk.stmts, blk.terminator);
    }

    println!("\n=== EXP 3B: LocalDefId (DefIndex) Shift under #[cfg(debug_assertions)] / #[cfg(overflow_checks)] ===");
    let exp3b_src = r#"
#![feature(cfg_overflow_checks, cfg_ub_checks)]
#![allow(dead_code)]

pub fn before_cfg(x: u32) -> u32 { x }

pub fn contains_cfg_closure(x: u32) -> u32 {
    #[cfg(debug_assertions)]
    let _check = |v: u32| v > 0;
    x
}

pub fn after_cfg_closure(x: u32) -> u32 { x + 1 }

#[cfg(overflow_checks)]
const EXTRA_CONST: u32 = 1;

pub fn after_cfg_item(x: u32) -> u32 { x }
"#;
    let shift_rel = run_probe_session(
        true,
        exp3b_src,
        &["-Copt-level=0", "-Cdebug-assertions=off", "-Coverflow-checks=off", "--emit=metadata"],
    );
    let shift_dbg = run_probe_session(
        true,
        exp3b_src,
        &["-Copt-level=0", "-Cdebug-assertions=on", "-Coverflow-checks=on", "--emit=metadata"],
    );
    println!("Release DefIndex table:");
    for r in &shift_rel {
        println!("  DefIdx {:2} -> {} ({})", r.def_index, r.def_path, r.def_kind);
    }
    println!("Debug DefIndex table:");
    for r in &shift_dbg {
        println!("  DefIdx {:2} -> {} ({})", r.def_index, r.def_path, r.def_kind);
    }

    // Write machine-readable JSON receipt
    let mut f = File::create("probe_results.json").expect("create probe_results.json");
    let exp1_json: Vec<String> = records_meta
        .iter()
        .zip(records_link.iter())
        .map(|(rm, rl)| {
            format!(
                "{{\"def_index\":{},\"def_path\":{},\"def_kind\":{},\"const_context\":{},\"is_trivial_const\":{},\"is_constructor\":{},\"is_coroutine\":{},\"mir_built_is_stolen\":{},\"mir_promoted_0_is_stolen\":{},\"mir_promoted_1_is_stolen\":{},\"meta_stolen_at_entry\":{},\"meta_stolen_after_all_drops\":{},\"link_stolen_at_entry\":{},\"direct_borrow_ok_at_entry_link\":{},\"promoted_mir_count\":{},\"ctfe_matches_postcleanup_modulo_counter\":{},\"postcleanup\":{},\"mir_for_ctfe\":{},\"optimized_mir_default_o0\":{}}}",
                rm.def_index,
                json_escape(&rm.def_path),
                json_escape(&rm.def_kind),
                json_escape(&rm.const_context),
                rm.is_trivial_const,
                rm.is_constructor,
                rm.is_coroutine,
                rm.mir_built_is_stolen,
                opt_bool_json(rm.mir_promoted_0_is_stolen),
                opt_bool_json(rm.mir_promoted_1_is_stolen),
                opt_bool_json(rm.mir_drops_is_stolen_at_entry),
                opt_bool_json(rm.mir_drops_is_stolen_after_all_drops_elaborated),
                opt_bool_json(rl.mir_drops_is_stolen_at_entry),
                rl.direct_borrow_postcleanup_ok,
                opt_usize_json(rm.promoted_mir_count_at_after_analysis),
                opt_bool_json(rm.mir_for_ctfe_matches_postcleanup_modulo_counter),
                summary_json(&rm.hook_captured_postcleanup),
                summary_json(&rm.mir_for_ctfe_summary),
                summary_json(&rm.optimized_mir_summary),
            )
        })
        .collect();

    let exp3_json: Vec<String> = p_rel
        .iter()
        .zip(p_dbg_only.iter())
        .zip(p_ovf_only.iter())
        .zip(p_dbg.iter())
        .filter_map(|(((r00, r10), r01), r11)| {
            let b00 = r00.hook_captured_postcleanup.as_ref()?;
            let b10 = r10.hook_captured_postcleanup.as_ref()?;
            let b01 = r01.hook_captured_postcleanup.as_ref()?;
            let b11 = r11.hook_captured_postcleanup.as_ref()?;
            Some(format!(
                "{{\"def_path\":{},\"def_kind\":{},\"eq_dbg_only\":{},\"eq_ovf_only\":{},\"eq_full_dbg\":{},\"rel_00\":{},\"dbg_10\":{},\"ovf_01\":{},\"dbg_11\":{}}}",
                json_escape(&r00.def_path),
                json_escape(&r00.def_kind),
                b00 == b10,
                b00 == b01,
                b00 == b11,
                summary_json(&r00.hook_captured_postcleanup),
                summary_json(&r10.hook_captured_postcleanup),
                summary_json(&r01.hook_captured_postcleanup),
                summary_json(&r11.hook_captured_postcleanup),
            ))
        })
        .collect();

    write!(
        f,
        "{{\n  \"toolchain\": \"nightly-2026-05-31 (f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1)\",\n  \"exp1_steal_and_phases\": [\n    {}\n  ],\n  \"exp3_profile_divergence\": [\n    {}\n  ]\n}}\n",
        exp1_json.join(",\n    "),
        exp3_json.join(",\n    ")
    )
    .expect("write json");
    println!("\nWrote probe_results.json successfully.");
}
