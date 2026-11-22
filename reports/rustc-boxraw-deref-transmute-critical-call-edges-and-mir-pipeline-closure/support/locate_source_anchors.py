#!/usr/bin/env python3
"""Locate the source lines cited by the report, at each examined commit.

    python3 locate_source_anchors.py --root <40-hex-commit>=<checkout-dir> [--root ...] --out anchors.json

For every anchor (a file plus a literal that occurs on one source line) the output records the
1-based line number(s) at each commit, or an empty list when the literal does not occur there.
An empty list is a finding in its own right (the construct does not exist at that commit); it
is never papered over.

Standard library only (Python 3.10+).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys

MT = "compiler/rustc_mir_transform/src/"
ANCHORS = [
    # --- pass manager
    (MT + "pass_manager.rs", "pub(crate) enum PassPolicy {", "definition of PassPolicy"),
    (MT + "pass_manager.rs", "They must not remove any UB, as they will", "Required: must not remove UB"),
    (MT + "pass_manager.rs", "fn is_required(&self) -> bool;", "older API: is_required"),
    (MT + "pass_manager.rs", "pub(super) fn should_run_pass<'tcx, P>(", "should_run_pass"),
    (MT + "pass_manager.rs", "|| new_phase == MirPhase::Runtime(RuntimePhase::Optimized);",
     "MIR is always validated on the change to Runtime(Optimized)"),
    # --- lib.rs pipeline
    (MT + "lib.rs", "fn mir_built(", "mir_built"),
    (MT + "lib.rs", "fn mir_promoted(", "mir_promoted"),
    (MT + "lib.rs", "if let Some((CtorKind::Fn, ctor_def_id)) = variant.ctor", "mir_keys adds fn-like constructors"),
    (MT + "lib.rs", "debug_assert!(!tcx.is_constructor(def.to_def_id()));", "mir_promoted never sees constructors"),
    (MT + "lib.rs", "return shim::build_adt_ctor(tcx, def.to_def_id());", "mir_for_ctfe of a constructor"),
    (MT + "lib.rs", "pub fn run_analysis_to_runtime_passes<'tcx>(", "run_analysis_to_runtime_passes"),
    (MT + "lib.rs", "fn run_analysis_cleanup_passes<'tcx>(", "run_analysis_cleanup_passes"),
    (MT + "lib.rs", "&deref_separator::Derefer,", "Derefer scheduled"),
    (MT + "lib.rs", "post_analysis_normalize::PostAnalysisNormalize", "PostAnalysisNormalize scheduled"),
    (MT + "lib.rs", "fn run_runtime_lowering_passes<'tcx>(", "run_runtime_lowering_passes"),
    (MT + "lib.rs", "&add_call_guards::CriticalCallEdges,", "CriticalCallEdges scheduled (all occurrences)"),
    (MT + "lib.rs", "&erase_deref_temps::EraseDerefTemps,", "EraseDerefTemps scheduled"),
    (MT + "lib.rs", "&elaborate_box_derefs::ElaborateBoxDerefs,", "ElaborateBoxDerefs scheduled"),
    (MT + "lib.rs", "fn run_runtime_cleanup_passes<'tcx>(", "run_runtime_cleanup_passes"),
    (MT + "lib.rs", "&simplify::SimplifyCfg::PreOptimizations,", "SimplifyCfg::PreOptimizations scheduled"),
    (MT + "lib.rs", "pub(crate) fn run_optimization_passes<'tcx>(", "run_optimization_passes"),
    (MT + "lib.rs", "&remove_unneeded_drops::RemoveUnneededDrops,", "RemoveUnneededDrops scheduled"),
    (MT + "lib.rs", "&multiple_return_terminators::MultipleReturnTerminators,",
     "MultipleReturnTerminators scheduled (all occurrences)"),
    (MT + "lib.rs", "fn optimized_mir(tcx: TyCtxt<'_>, did: LocalDefId) -> &Body<'_> {", "optimized_mir"),
    (MT + "lib.rs", "return tcx.mir_for_ctfe(did);", "optimized_mir of a constructor"),
    (MT + "lib.rs", "fn inner_optimized_mir(", "inner_optimized_mir"),
    # --- ElaborateBoxDerefs
    (MT + "elaborate_box_derefs.rs", "CastKind::BoxDerefTransmute", "cast kind used by the pass"),
    (MT + "elaborate_box_derefs.rs", "CastKind::Transmute,", "cast kind used by the pass (older)"),
    (MT + "elaborate_box_derefs.rs", "// Project to the first field (a `BoxRaw`), then transmute that.",
     "projection comment"),
    (MT + "elaborate_box_derefs.rs", "&& let Some(boxed_ty) = base_ty.boxed_ty()", "only Box-typed bases"),
    (MT + "elaborate_box_derefs.rs", "let ptr_local = self.patch.new_temp(ptr_ty, source_info.span);",
     "fresh temporary per elaborated deref"),
    (MT + "elaborate_box_derefs.rs", "PassPolicy::Required", "policy"),
    # --- Derefer / EraseDerefTemps
    (MT + "deref_separator.rs", "&& place.projection[1..].contains(&ProjectionElem::Deref)",
     "Derefer: non-leading derefs only"),
    (MT + "deref_separator.rs", "Rvalue::CopyForDeref(deref_place)", "Derefer emits CopyForDeref"),
    (MT + "erase_deref_temps.rs", "*rvalue = Rvalue::Use(Operand::Copy(place), WithRetag::No)",
     "EraseDerefTemps: CopyForDeref becomes a no-retag copy"),
    # --- AddCallGuards
    (MT + "add_call_guards.rs", "//! NOTE: Simplify CFG will happily undo most of the work this pass does.",
     "module doc"),
    (MT + "add_call_guards.rs", "let mut pred_count = IndexVec::from_elem(0u8, &body.basic_blocks);", "pred_count"),
    (MT + "add_call_guards.rs", "if pred_count[destination] > 1", "Call criterion"),
    (MT + "add_call_guards.rs", "&& (generates_invoke(unwind) || self == &AllCallEdges) =>", "Call criterion"),
    (MT + "add_call_guards.rs", "if has_outputs && (has_labels || generates_invoke(unwind)) {", "InlineAsm criterion"),
    (MT + "add_call_guards.rs", "if pred_count[*target] > 1 {", "InlineAsm per-target criterion"),
    (MT + "add_call_guards.rs", "fn generates_invoke(unwind: UnwindAction) -> bool {", "generates_invoke"),
    # --- RemoveUnneededDrops
    (MT + "remove_unneeded_drops.rs", "if ty.needs_drop(tcx, typing_env) {", "needs_drop test"),
    (MT + "remove_unneeded_drops.rs", "simplify_cfg(tcx, body);", "follow-up CFG simplification"),
    (MT + "remove_unneeded_drops.rs", "PassPolicy::optional(true)", "policy"),
    # --- MultipleReturnTerminators
    (MT + "multiple_return_terminators.rs",
     "if bb.statements.is_empty() && bb.terminator().kind == TerminatorKind::Return {", "simple return test"),
    (MT + "multiple_return_terminators.rs", "bb.terminator_mut().kind = TerminatorKind::Return;", "rewrite"),
    (MT + "multiple_return_terminators.rs", "simplify::remove_dead_blocks(body)", "follow-up"),
    (MT + "multiple_return_terminators.rs", "PassPolicy::optional(ctx.mir_opt_level() >= 4)", "policy"),
    (MT + "multiple_return_terminators.rs", "sess.mir_opt_level() >= 4", "policy (older API)"),
    # --- validator
    (MT + "validate.rs", "fn is_critical_call_edge(&self, target: Option<BasicBlock>, unwind: UnwindAction) -> bool {",
     "validator: critical call edge"),
    (MT + "validate.rs", "\"encountered critical edge in `Call` terminator {:?}\",", "validator failure message"),
    (MT + "validate.rs", "\"Cannot BoxDerefTransmute to non-pointer type {target_type}\"", "validator: cast target"),
    # --- shims
    (MT + "shim.rs", "pub(super) fn build_adt_ctor(tcx: TyCtxt<'_>, ctor_id: DefId) -> Body<'_> {", "build_adt_ctor"),
    (MT + "shim.rs", "// We don't pass any passes here, we just force a phase change to `Optimized`.",
     "constructor body: no passes"),
    (MT + "shim.rs", "crate::pass_manager::dump_mir_for_phase_change(tcx, &body);", "constructor body (older)"),
    (MT + "shim.rs", "&add_call_guards::CriticalCallEdges,", "CriticalCallEdges in shim pass lists"),
    # --- MIR syntax
    ("compiler/rustc_middle/src/mir/syntax.rs", "    BoxDerefTransmute,", "CastKind::BoxDerefTransmute"),
    ("compiler/rustc_middle/src/mir/syntax.rs",
     "    /// A special transmute used by elaborated `box` deref's to turn the inner pointer into a raw",
     "CastKind::BoxDerefTransmute doc"),
    ("compiler/rustc_middle/src/mir/syntax.rs", "    /// * [`ProjectionElem::Deref`] of `Box`",
     "RuntimePhase::PostCleanup forbids Deref of Box"),
    ("compiler/rustc_middle/src/mir/syntax.rs", "        /// written-to when execution continues with `targets`.",
     "InlineAsm outputs are written when continuing to targets"),
    # --- interpreter
    ("compiler/rustc_const_eval/src/interpret/cast.rs",
     "                if matches!(cast_kind, CastKind::BoxDerefTransmute) {", "interpreter: extra UB check"),
    ("compiler/rustc_const_eval/src/interpret/place.rs", "    pub fn deref_pointer(", "deref_pointer"),
    ("compiler/rustc_const_eval/src/interpret/place.rs", "            if ptr_ty.is_ref() || ptr_ty.is_box() {",
     "deref_pointer: checks for references and boxes only"),
    ("compiler/rustc_const_eval/src/interpret/place.rs", "            // Derefer should have removed all Box derefs.",
     "deref_pointer (older): Box derefs are a compiler bug here; no validity check"),
    ("compiler/rustc_const_eval/src/interpret/cast.rs", "                    self.deref_pointer(&ptr)?;",
     "interpreter: BoxDerefTransmute dereferences the input as a Box"),
    # --- codegen
    ("compiler/rustc_codegen_ssa/src/mir/block.rs", "            let invokeret = bx.invoke(", "invoke"),
    ("compiler/rustc_codegen_ssa/src/mir/block.rs", "                bx.switch_to_block(fx.llbb(target));",
     "the result store is emitted into the target block"),
    ("compiler/rustc_codegen_ssa/src/mir/block.rs",
     "                fx.store_return(bx, ret_dest, &fn_abi.ret, invokeret);", "store of the invoke result"),
    ("compiler/rustc_codegen_llvm/src/asm.rs",
     "        // Write results to outputs. We need to do this for all possible control flow.",
     "callbr outputs stored in every destination"),
    ("compiler/rustc_codegen_llvm/src/asm.rs",
     "        bx.callbr(fty, None, None, v, inputs, dest.unwrap(), labels, None, None)", "callbr"),
    # --- library
    ("library/alloc/src/boxed.rs", "struct BoxRaw<T: ?Sized> {", "BoxRaw"),
    ("library/alloc/src/boxed.rs", ">(BoxRaw<T>, A);", "Box field 0 is BoxRaw"),
    ("library/alloc/src/boxed.rs", ">(Unique<T>, A);", "Box field 0 is Unique (older)"),
    ("library/core/src/ptr/non_null.rs", "pattern_type!(*const T is !null),",
     "NonNull wraps a pattern type"),
    # --- misc
    ("compiler/rustc_middle/src/ty/util.rs", "    pub fn needs_drop(self, tcx: TyCtxt<'tcx>, typing_env: ty::TypingEnv<'tcx>) -> bool {",
     "needs_drop"),
    ("compiler/rustc_middle/src/ty/util.rs", "    pub fn is_constructor(self, def_id: DefId) -> bool {", "is_constructor"),
    ("compiler/rustc_session/src/config.rs", "    pub fn mir_opt_level(&self) -> usize {", "OptLevel::mir_opt_level"),
    ("src/tools/miri/src/lib.rs", "pub const MIRI_DEFAULT_ARGS: &[&str] = &[", "Miri default rustc args"),
    ("src/tools/miri/src/lib.rs", "    \"-Zmir-opt-level=0\",", "Miri: MIR opt level 0"),
    ("src/tools/miri/src/lib.rs", "    \"-Zmir-preserve-ub\",", "Miri: preserve UB"),
]


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("--root", action="append", required=True, metavar="COMMIT=DIR")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    roots = [r.split("=", 1) for r in args.root]
    doc = {"schema": "source-anchors/1", "commits": [c for c, _ in roots], "files": {}, "anchors": []}
    cache = {}
    for commit, d in roots:
        for path in sorted({a[0] for a in ANCHORS}):
            full = os.path.join(d, path)
            if os.path.exists(full):
                with open(full, encoding="utf-8") as f:
                    text = f.read().replace("\r", "")
                cache[(commit, path)] = text.split("\n")
                doc["files"].setdefault(path, {})[commit] = {
                    "sha256": hashlib.sha256(text.encode("utf-8")).hexdigest(),
                    "lines": text.count("\n") + (0 if text.endswith("\n") else 1)}
            else:
                doc["files"].setdefault(path, {})[commit] = None
    for path, literal, what in ANCHORS:
        entry = {"file": path, "literal": literal, "what": what, "lines": {}}
        for commit, _ in roots:
            lines = cache.get((commit, path))
            entry["lines"][commit] = (None if lines is None else
                                      [i + 1 for i, l in enumerate(lines) if literal in l])
        doc["anchors"].append(entry)
    text = json.dumps(doc, indent=1, sort_keys=True)
    if args.out:
        with open(args.out, "w", encoding="utf-8") as f:
            f.write(text + "\n")
    else:
        print(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
