import ToyInline.Results
import ToyInline.Instances

/-!
# Tightness witnesses for the inlining theorems

Each theorem below is a counterexample in canonical form for the four inlining theorems
`inline_behEquiv_retTemp_of_capsEq` (temp mode),
`inline_behEquiv_retDest_of_destUnobservedOnUnwind` (dest mode, configuration `cfg.withDest`),
`inline_behEquiv_retTemp_of_capsSubset_capLegal_abiInsensitive` and
`inline_behEquiv_retTemp_of_capsSubset_capLegal_abiAgree`: it lists every hypothesis of those
theorems (the temp-mode ones for `cfg`, the dest-mode ones for `cfg.withDest`), stating the
negation of the ones the instance violates, and then the failure of the conclusion
(`¬ BehEquiv`) for the temp-mode configuration, the dest-mode configuration, or both. For a
given theorem, the instance satisfies all of that theorem's hypotheses except the negated ones
it uses. All facts are decided by evaluation in the kernel. These are internal tightness
witnesses; the result cards for the capability-subset and link-rule questions use the focused
statements in `OtherCounterexamples.lean`.
-/

namespace Toy.Inline

/-- `IsCallSite` names the wrong function: the hypotheses are checked on `emptyF` while the program's function `0` is `freshF`, whose live local `1` is clobbered by slot `1`. -/
theorem cex_isCallSite :
    (¬ (IsCallSite freshP 0 0 emptyF freshCi freshG) ∧
    LocalsBounded emptyF ∧
    LocalsBounded freshG ∧
    BlocksBounded emptyF ∧
    ScopesWF emptyF ∧
    ScopesWF freshG ∧
    SlotsFresh freshCfg emptyF freshG ∧
    SlotsInjective freshCfg freshG ∧
    freshCfg.ret = .temp 2 ∧
    TempFresh 2 freshCfg emptyF freshG ∧
    freshCfg.redirectContinue = true ∧
    freshCfg.resumeMap = .unwind ∧
    freshCfg.link = .rustc ∧
    emptyF.caps = freshG.caps ∧
    CapsSubset freshG emptyF ∧
    CapLegal freshG ∧
    AbiInsensitive freshG ∧
    freshCi.abiSensitive = false ∧
    AbiAgree freshP emptyF freshG ∧
    SlotsFresh freshCfg.withDest emptyF freshG ∧
    SlotsInjective freshCfg.withDest freshG ∧
    freshCfg.withDest.ret = .dest ∧
    freshCfg.withDest.redirectContinue = true ∧
    freshCfg.withDest.resumeMap = .unwind ∧
    freshCfg.withDest.link = .rustc ∧
    CleanupClosed emptyF ∧
    DestNotReadInCleanup emptyF freshCi.dest) ∧
    ¬ BehEquiv freshP (inline freshP 0 0 freshCfg) ∧
    ¬ BehEquiv freshP (inline freshP 0 0 freshCfg.withDest) := by
  exact ⟨by decide, (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩)), (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩))⟩

/-- The caller declares one local but keeps local `1` live across the call; slot `1 = 1` is "fresh" relative to the declared count and clobbers it. -/
theorem cex_localsBoundedF :
    (IsCallSite locFP 0 0 locFF locFCi locFG ∧
    ¬ (LocalsBounded locFF) ∧
    LocalsBounded locFG ∧
    BlocksBounded locFF ∧
    ScopesWF locFF ∧
    ScopesWF locFG ∧
    SlotsFresh locFCfg locFF locFG ∧
    SlotsInjective locFCfg locFG ∧
    locFCfg.ret = .temp 2 ∧
    TempFresh 2 locFCfg locFF locFG ∧
    locFCfg.redirectContinue = true ∧
    locFCfg.resumeMap = .unwind ∧
    locFCfg.link = .rustc ∧
    locFF.caps = locFG.caps ∧
    CapsSubset locFG locFF ∧
    CapLegal locFG ∧
    AbiInsensitive locFG ∧
    locFCi.abiSensitive = false ∧
    AbiAgree locFP locFF locFG ∧
    SlotsFresh locFCfg.withDest locFF locFG ∧
    SlotsInjective locFCfg.withDest locFG ∧
    locFCfg.withDest.ret = .dest ∧
    locFCfg.withDest.redirectContinue = true ∧
    locFCfg.withDest.resumeMap = .unwind ∧
    locFCfg.withDest.link = .rustc ∧
    CleanupClosed locFF ∧
    DestNotReadInCleanup locFF locFCi.dest) ∧
    ¬ BehEquiv locFP (inline locFP 0 0 locFCfg) ∧
    ¬ BehEquiv locFP (inline locFP 0 0 locFCfg.withDest) := by
  exact ⟨by decide, (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩)), (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩))⟩

/-- The callee declares one local but reads its argument (local `1`), which the prologue therefore does not bind. -/
theorem cex_localsBoundedG :
    (IsCallSite locGP 0 0 locGF locGCi locGG ∧
    LocalsBounded locGF ∧
    ¬ (LocalsBounded locGG) ∧
    BlocksBounded locGF ∧
    ScopesWF locGF ∧
    ScopesWF locGG ∧
    SlotsFresh (InlineCfg.canonical 1) locGF locGG ∧
    SlotsInjective (InlineCfg.canonical 1) locGG ∧
    (InlineCfg.canonical 1).ret = .temp 1 ∧
    TempFresh 1 (InlineCfg.canonical 1) locGF locGG ∧
    (InlineCfg.canonical 1).redirectContinue = true ∧
    (InlineCfg.canonical 1).resumeMap = .unwind ∧
    (InlineCfg.canonical 1).link = .rustc ∧
    locGF.caps = locGG.caps ∧
    CapsSubset locGG locGF ∧
    CapLegal locGG ∧
    AbiInsensitive locGG ∧
    locGCi.abiSensitive = false ∧
    AbiAgree locGP locGF locGG ∧
    SlotsFresh (InlineCfg.canonical 1).withDest locGF locGG ∧
    SlotsInjective (InlineCfg.canonical 1).withDest locGG ∧
    (InlineCfg.canonical 1).withDest.ret = .dest ∧
    (InlineCfg.canonical 1).withDest.redirectContinue = true ∧
    (InlineCfg.canonical 1).withDest.resumeMap = .unwind ∧
    (InlineCfg.canonical 1).withDest.link = .rustc ∧
    CleanupClosed locGF ∧
    DestNotReadInCleanup locGF locGCi.dest) ∧
    ¬ BehEquiv locGP (inline locGP 0 0 (InlineCfg.canonical 1)) ∧
    ¬ BehEquiv locGP (inline locGP 0 0 (InlineCfg.canonical 1).withDest) := by
  exact ⟨by decide, (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩)), (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩))⟩

/-- The caller jumps to a missing block (undefined behaviour), which after inlining is a callee block (abort). -/
theorem cex_blocksBoundedF :
    (IsCallSite blkFP 0 0 blkFF blkFCi blkFG ∧
    LocalsBounded blkFF ∧
    LocalsBounded blkFG ∧
    ¬ (BlocksBounded blkFF) ∧
    ScopesWF blkFF ∧
    ScopesWF blkFG ∧
    SlotsFresh (InlineCfg.canonical 1) blkFF blkFG ∧
    SlotsInjective (InlineCfg.canonical 1) blkFG ∧
    (InlineCfg.canonical 1).ret = .temp 1 ∧
    TempFresh 1 (InlineCfg.canonical 1) blkFF blkFG ∧
    (InlineCfg.canonical 1).redirectContinue = true ∧
    (InlineCfg.canonical 1).resumeMap = .unwind ∧
    (InlineCfg.canonical 1).link = .rustc ∧
    blkFF.caps = blkFG.caps ∧
    CapsSubset blkFG blkFF ∧
    CapLegal blkFG ∧
    AbiInsensitive blkFG ∧
    blkFCi.abiSensitive = false ∧
    AbiAgree blkFP blkFF blkFG ∧
    SlotsFresh (InlineCfg.canonical 1).withDest blkFF blkFG ∧
    SlotsInjective (InlineCfg.canonical 1).withDest blkFG ∧
    (InlineCfg.canonical 1).withDest.ret = .dest ∧
    (InlineCfg.canonical 1).withDest.redirectContinue = true ∧
    (InlineCfg.canonical 1).withDest.resumeMap = .unwind ∧
    (InlineCfg.canonical 1).withDest.link = .rustc ∧
    CleanupClosed blkFF ∧
    DestNotReadInCleanup blkFF blkFCi.dest) ∧
    ¬ BehEquiv blkFP (inline blkFP 0 0 (InlineCfg.canonical 1)) ∧
    ¬ BehEquiv blkFP (inline blkFP 0 0 (InlineCfg.canonical 1).withDest) := by
  exact ⟨by decide, (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩)), (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩))⟩

/-- The caller's `loc` names a missing scope, which after inlining is the callee's outermost (inlined, tracked) scope. -/
theorem cex_scopesWFF :
    (IsCallSite scFP 0 0 scFF spanCi scFG ∧
    LocalsBounded scFF ∧
    LocalsBounded scFG ∧
    BlocksBounded scFF ∧
    ¬ (ScopesWF scFF) ∧
    ScopesWF scFG ∧
    SlotsFresh (InlineCfg.canonical 1) scFF scFG ∧
    SlotsInjective (InlineCfg.canonical 1) scFG ∧
    (InlineCfg.canonical 1).ret = .temp 1 ∧
    TempFresh 1 (InlineCfg.canonical 1) scFF scFG ∧
    (InlineCfg.canonical 1).redirectContinue = true ∧
    (InlineCfg.canonical 1).resumeMap = .unwind ∧
    (InlineCfg.canonical 1).link = .rustc ∧
    scFF.caps = scFG.caps ∧
    CapsSubset scFG scFF ∧
    CapLegal scFG ∧
    AbiInsensitive scFG ∧
    spanCi.abiSensitive = false ∧
    AbiAgree scFP scFF scFG ∧
    SlotsFresh (InlineCfg.canonical 1).withDest scFF scFG ∧
    SlotsInjective (InlineCfg.canonical 1).withDest scFG ∧
    (InlineCfg.canonical 1).withDest.ret = .dest ∧
    (InlineCfg.canonical 1).withDest.redirectContinue = true ∧
    (InlineCfg.canonical 1).withDest.resumeMap = .unwind ∧
    (InlineCfg.canonical 1).withDest.link = .rustc ∧
    CleanupClosed scFF ∧
    DestNotReadInCleanup scFF spanCi.dest) ∧
    ¬ BehEquiv scFP (inline scFP 0 0 (InlineCfg.canonical 1)) ∧
    ¬ BehEquiv scFP (inline scFP 0 0 (InlineCfg.canonical 1).withDest) := by
  exact ⟨by decide, (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩)), (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩))⟩

/-- A tracked callee's `loc` names a missing scope; in the callee's own frame the walk falls back to the implicit location, after inlining to the span. -/
theorem cex_scopesWFG :
    (IsCallSite scGP 0 0 scGF spanCi scGG ∧
    LocalsBounded scGF ∧
    LocalsBounded scGG ∧
    BlocksBounded scGF ∧
    ScopesWF scGF ∧
    ¬ (ScopesWF scGG) ∧
    SlotsFresh (InlineCfg.canonical 1) scGF scGG ∧
    SlotsInjective (InlineCfg.canonical 1) scGG ∧
    (InlineCfg.canonical 1).ret = .temp 1 ∧
    TempFresh 1 (InlineCfg.canonical 1) scGF scGG ∧
    (InlineCfg.canonical 1).redirectContinue = true ∧
    (InlineCfg.canonical 1).resumeMap = .unwind ∧
    (InlineCfg.canonical 1).link = .rustc ∧
    scGF.caps = scGG.caps ∧
    CapsSubset scGG scGF ∧
    CapLegal scGG ∧
    AbiInsensitive scGG ∧
    spanCi.abiSensitive = false ∧
    AbiAgree scGP scGF scGG ∧
    SlotsFresh (InlineCfg.canonical 1).withDest scGF scGG ∧
    SlotsInjective (InlineCfg.canonical 1).withDest scGG ∧
    (InlineCfg.canonical 1).withDest.ret = .dest ∧
    (InlineCfg.canonical 1).withDest.redirectContinue = true ∧
    (InlineCfg.canonical 1).withDest.resumeMap = .unwind ∧
    (InlineCfg.canonical 1).withDest.link = .rustc ∧
    CleanupClosed scGF ∧
    DestNotReadInCleanup scGF spanCi.dest) ∧
    ¬ BehEquiv scGP (inline scGP 0 0 (InlineCfg.canonical 1)) ∧
    ¬ BehEquiv scGP (inline scGP 0 0 (InlineCfg.canonical 1).withDest) := by
  exact ⟨by decide, (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩)), (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩))⟩

/-- Overlapping slot range: callee local `1` goes to caller local `1`, which is live across the call and is clobbered. -/
theorem cex_slotsFresh :
    (IsCallSite freshP 0 0 freshF freshCi freshG ∧
    LocalsBounded freshF ∧
    LocalsBounded freshG ∧
    BlocksBounded freshF ∧
    ScopesWF freshF ∧
    ScopesWF freshG ∧
    ¬ (SlotsFresh freshCfg freshF freshG) ∧
    SlotsInjective freshCfg freshG ∧
    freshCfg.ret = .temp 2 ∧
    TempFresh 2 freshCfg freshF freshG ∧
    freshCfg.redirectContinue = true ∧
    freshCfg.resumeMap = .unwind ∧
    freshCfg.link = .rustc ∧
    freshF.caps = freshG.caps ∧
    CapsSubset freshG freshF ∧
    CapLegal freshG ∧
    AbiInsensitive freshG ∧
    freshCi.abiSensitive = false ∧
    AbiAgree freshP freshF freshG ∧
    ¬ (SlotsFresh freshCfg.withDest freshF freshG) ∧
    SlotsInjective freshCfg.withDest freshG ∧
    freshCfg.withDest.ret = .dest ∧
    freshCfg.withDest.redirectContinue = true ∧
    freshCfg.withDest.resumeMap = .unwind ∧
    freshCfg.withDest.link = .rustc ∧
    CleanupClosed freshF ∧
    DestNotReadInCleanup freshF freshCi.dest) ∧
    ¬ BehEquiv freshP (inline freshP 0 0 freshCfg) ∧
    ¬ BehEquiv freshP (inline freshP 0 0 freshCfg.withDest) := by
  exact ⟨by decide, (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩)), (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩))⟩

/-- Both callee arguments go to the same host local. -/
theorem cex_slotsInjective :
    (IsCallSite injP 0 0 injF injCi injG ∧
    LocalsBounded injF ∧
    LocalsBounded injG ∧
    BlocksBounded injF ∧
    ScopesWF injF ∧
    ScopesWF injG ∧
    SlotsFresh injCfg injF injG ∧
    ¬ (SlotsInjective injCfg injG) ∧
    injCfg.ret = .temp 1 ∧
    TempFresh 1 injCfg injF injG ∧
    injCfg.redirectContinue = true ∧
    injCfg.resumeMap = .unwind ∧
    injCfg.link = .rustc ∧
    injF.caps = injG.caps ∧
    CapsSubset injG injF ∧
    CapLegal injG ∧
    AbiInsensitive injG ∧
    injCi.abiSensitive = false ∧
    AbiAgree injP injF injG ∧
    SlotsFresh injCfg.withDest injF injG ∧
    ¬ (SlotsInjective injCfg.withDest injG) ∧
    injCfg.withDest.ret = .dest ∧
    injCfg.withDest.redirectContinue = true ∧
    injCfg.withDest.resumeMap = .unwind ∧
    injCfg.withDest.link = .rustc ∧
    CleanupClosed injF ∧
    DestNotReadInCleanup injF injCi.dest) ∧
    ¬ BehEquiv injP (inline injP 0 0 injCfg) ∧
    ¬ BehEquiv injP (inline injP 0 0 injCfg.withDest) := by
  exact ⟨by decide, (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩)), (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩))⟩

/-- The return temporary is the argument's slot: the callee's early write to its return place clobbers the argument it then reads (temp mode only). -/
theorem cex_tempFresh :
    (IsCallSite tempP 0 0 tempF tempCi tempG ∧
    LocalsBounded tempF ∧
    LocalsBounded tempG ∧
    BlocksBounded tempF ∧
    ScopesWF tempF ∧
    ScopesWF tempG ∧
    SlotsFresh tempCfg tempF tempG ∧
    SlotsInjective tempCfg tempG ∧
    tempCfg.ret = .temp 2 ∧
    tempCfg.ret ≠ .dest ∧
    ¬ (TempFresh 2 tempCfg tempF tempG) ∧
    tempCfg.redirectContinue = true ∧
    tempCfg.resumeMap = .unwind ∧
    tempCfg.link = .rustc ∧
    tempF.caps = tempG.caps ∧
    CapsSubset tempG tempF ∧
    CapLegal tempG ∧
    AbiInsensitive tempG ∧
    tempCi.abiSensitive = false ∧
    AbiAgree tempP tempF tempG ∧
    SlotsFresh tempCfg.withDest tempF tempG ∧
    SlotsInjective tempCfg.withDest tempG ∧
    tempCfg.withDest.ret = .dest ∧
    ¬ (TempFresh 2 tempCfg.withDest tempF tempG) ∧
    tempCfg.withDest.redirectContinue = true ∧
    tempCfg.withDest.resumeMap = .unwind ∧
    tempCfg.withDest.link = .rustc ∧
    CleanupClosed tempF ∧
    DestNotReadInCleanup tempF tempCi.dest) ∧
    ¬ BehEquiv tempP (inline tempP 0 0 tempCfg) := by
  exact ⟨by decide, (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩))⟩

/-- The callee's inner call keeps its `continue` edge: a panic below it skips the caller's cleanup (the drop event `out 200` is missing). -/
theorem cex_redirectContinue :
    (IsCallSite contP 0 0 contF contCi contG ∧
    LocalsBounded contF ∧
    LocalsBounded contG ∧
    BlocksBounded contF ∧
    ScopesWF contF ∧
    ScopesWF contG ∧
    SlotsFresh contCfg contF contG ∧
    SlotsInjective contCfg contG ∧
    contCfg.ret = .temp 2 ∧
    TempFresh 2 contCfg contF contG ∧
    ¬ (contCfg.redirectContinue = true) ∧
    contCfg.resumeMap = .unwind ∧
    contCfg.link = .rustc ∧
    contF.caps = contG.caps ∧
    CapsSubset contG contF ∧
    CapLegal contG ∧
    AbiInsensitive contG ∧
    contCi.abiSensitive = false ∧
    AbiAgree contP contF contG ∧
    SlotsFresh contCfg.withDest contF contG ∧
    SlotsInjective contCfg.withDest contG ∧
    contCfg.withDest.ret = .dest ∧
    ¬ (contCfg.withDest.redirectContinue = true) ∧
    contCfg.withDest.resumeMap = .unwind ∧
    contCfg.withDest.link = .rustc ∧
    CleanupClosed contF ∧
    DestNotReadInCleanup contF contCi.dest) ∧
    ¬ BehEquiv contP (inline contP 0 0 contCfg) ∧
    ¬ BehEquiv contP (inline contP 0 0 contCfg.withDest) := by
  exact ⟨by decide, (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩)), (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩))⟩

/-- The callee's `resume` jumps to the normal continuation: after the callee's cleanup the caller returns normally instead of running its cleanup and unwinding. -/
theorem cex_resumeMap :
    (IsCallSite resP 0 0 contF contCi resG ∧
    LocalsBounded contF ∧
    LocalsBounded resG ∧
    BlocksBounded contF ∧
    ScopesWF contF ∧
    ScopesWF resG ∧
    SlotsFresh resCfg contF resG ∧
    SlotsInjective resCfg resG ∧
    resCfg.ret = .temp 2 ∧
    TempFresh 2 resCfg contF resG ∧
    resCfg.redirectContinue = true ∧
    ¬ (resCfg.resumeMap = .unwind) ∧
    resCfg.link = .rustc ∧
    contF.caps = resG.caps ∧
    CapsSubset resG contF ∧
    CapLegal resG ∧
    AbiInsensitive resG ∧
    contCi.abiSensitive = false ∧
    AbiAgree resP contF resG ∧
    SlotsFresh resCfg.withDest contF resG ∧
    SlotsInjective resCfg.withDest resG ∧
    resCfg.withDest.ret = .dest ∧
    resCfg.withDest.redirectContinue = true ∧
    ¬ (resCfg.withDest.resumeMap = .unwind) ∧
    resCfg.withDest.link = .rustc ∧
    CleanupClosed contF ∧
    DestNotReadInCleanup contF contCi.dest) ∧
    ¬ BehEquiv resP (inline resP 0 0 resCfg) ∧
    ¬ BehEquiv resP (inline resP 0 0 resCfg.withDest) := by
  exact ⟨by decide, (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩)), (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩))⟩

/-- Second-level inlining with the `ignoreParent` link rule, at a callsite in a nested (non-inlined) scope of an inlined tracked callee, inside an untracked host: the reported location is the inner callsite span `20` instead of the outer `10`. -/
theorem cex_linkRule :
    (IsCallSite linkP1 0 3 linkF1 linkCi1 linkK ∧
    LocalsBounded linkF1 ∧
    LocalsBounded linkK ∧
    BlocksBounded linkF1 ∧
    ScopesWF linkF1 ∧
    ScopesWF linkK ∧
    SlotsFresh linkCfg linkF1 linkK ∧
    SlotsInjective linkCfg linkK ∧
    linkCfg.ret = .temp 2 ∧
    TempFresh 2 linkCfg linkF1 linkK ∧
    linkCfg.redirectContinue = true ∧
    linkCfg.resumeMap = .unwind ∧
    ¬ (linkCfg.link = .rustc) ∧
    linkF1.caps = linkK.caps ∧
    CapsSubset linkK linkF1 ∧
    CapLegal linkK ∧
    AbiInsensitive linkK ∧
    linkCi1.abiSensitive = false ∧
    AbiAgree linkP1 linkF1 linkK ∧
    SlotsFresh linkCfg.withDest linkF1 linkK ∧
    SlotsInjective linkCfg.withDest linkK ∧
    linkCfg.withDest.ret = .dest ∧
    linkCfg.withDest.redirectContinue = true ∧
    linkCfg.withDest.resumeMap = .unwind ∧
    ¬ (linkCfg.withDest.link = .rustc) ∧
    CleanupClosed linkF1 ∧
    DestNotReadInCleanup linkF1 linkCi1.dest) ∧
    ¬ BehEquiv linkP1 (inline linkP1 0 3 linkCfg) ∧
    ¬ BehEquiv linkP1 (inline linkP1 0 3 linkCfg.withDest) := by
  exact ⟨by decide, (fun h => not_behEquivAtWith_of_halted_ne (n := 40) (m := 60) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩)), (fun h => not_behEquivAtWith_of_halted_ne (n := 40) (m := 60) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩))⟩

/-- Caller list `[1]` contains every capability of callee list `[]`; the callee's ABI-sensitive call to a capability-free function is correct in the callee and garbled in the host (`abi [1] ≠ abi []`). -/
theorem cex_capsAbi :
    (IsCallSite abiP 0 0 (capF [1]) plainCi abiG ∧
    LocalsBounded (capF [1]) ∧
    LocalsBounded abiG ∧
    BlocksBounded (capF [1]) ∧
    ScopesWF (capF [1]) ∧
    ScopesWF abiG ∧
    SlotsFresh (InlineCfg.canonical 1) (capF [1]) abiG ∧
    SlotsInjective (InlineCfg.canonical 1) abiG ∧
    (InlineCfg.canonical 1).ret = .temp 1 ∧
    TempFresh 1 (InlineCfg.canonical 1) (capF [1]) abiG ∧
    (InlineCfg.canonical 1).redirectContinue = true ∧
    (InlineCfg.canonical 1).resumeMap = .unwind ∧
    (InlineCfg.canonical 1).link = .rustc ∧
    ¬ ((capF [1]).caps = abiG.caps) ∧
    CapsSubset abiG (capF [1]) ∧
    CapLegal abiG ∧
    ¬ (AbiInsensitive abiG) ∧
    plainCi.abiSensitive = false ∧
    ¬ (AbiAgree abiP (capF [1]) abiG) ∧
    SlotsFresh (InlineCfg.canonical 1).withDest (capF [1]) abiG ∧
    SlotsInjective (InlineCfg.canonical 1).withDest abiG ∧
    (InlineCfg.canonical 1).withDest.ret = .dest ∧
    (InlineCfg.canonical 1).withDest.redirectContinue = true ∧
    (InlineCfg.canonical 1).withDest.resumeMap = .unwind ∧
    (InlineCfg.canonical 1).withDest.link = .rustc ∧
    CleanupClosed (capF [1]) ∧
    DestNotReadInCleanup (capF [1]) plainCi.dest) ∧
    ¬ BehEquiv abiP (inline abiP 0 0 (InlineCfg.canonical 1)) ∧
    ¬ BehEquiv abiP (inline abiP 0 0 (InlineCfg.canonical 1).withDest) := by
  exact ⟨by decide, (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩)), (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩))⟩

/-- The callee uses capability `3` without holding it (faults); the host holds it, so the inlined code does not fault. -/
theorem cex_capLegal :
    (IsCallSite legalP 0 0 (capF [3]) plainCi legalG ∧
    LocalsBounded (capF [3]) ∧
    LocalsBounded legalG ∧
    BlocksBounded (capF [3]) ∧
    ScopesWF (capF [3]) ∧
    ScopesWF legalG ∧
    SlotsFresh (InlineCfg.canonical 1) (capF [3]) legalG ∧
    SlotsInjective (InlineCfg.canonical 1) legalG ∧
    (InlineCfg.canonical 1).ret = .temp 1 ∧
    TempFresh 1 (InlineCfg.canonical 1) (capF [3]) legalG ∧
    (InlineCfg.canonical 1).redirectContinue = true ∧
    (InlineCfg.canonical 1).resumeMap = .unwind ∧
    (InlineCfg.canonical 1).link = .rustc ∧
    ¬ ((capF [3]).caps = legalG.caps) ∧
    CapsSubset legalG (capF [3]) ∧
    ¬ (CapLegal legalG) ∧
    AbiInsensitive legalG ∧
    plainCi.abiSensitive = false ∧
    AbiAgree legalP (capF [3]) legalG ∧
    SlotsFresh (InlineCfg.canonical 1).withDest (capF [3]) legalG ∧
    SlotsInjective (InlineCfg.canonical 1).withDest legalG ∧
    (InlineCfg.canonical 1).withDest.ret = .dest ∧
    (InlineCfg.canonical 1).withDest.redirectContinue = true ∧
    (InlineCfg.canonical 1).withDest.resumeMap = .unwind ∧
    (InlineCfg.canonical 1).withDest.link = .rustc ∧
    CleanupClosed (capF [3]) ∧
    DestNotReadInCleanup (capF [3]) plainCi.dest) ∧
    ¬ BehEquiv legalP (inline legalP 0 0 (InlineCfg.canonical 1)) ∧
    ¬ BehEquiv legalP (inline legalP 0 0 (InlineCfg.canonical 1).withDest) := by
  exact ⟨by decide, (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩)), (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩))⟩

/-- The inlined call itself is ABI-sensitive with `abi [1] ≠ abi []`: the original garbles the argument, the inlined prologue binds it correctly. -/
theorem cex_callAbiSensitive :
    (IsCallSite cabP 0 0 cabF cabCi cabG ∧
    LocalsBounded cabF ∧
    LocalsBounded cabG ∧
    BlocksBounded cabF ∧
    ScopesWF cabF ∧
    ScopesWF cabG ∧
    SlotsFresh (InlineCfg.canonical 1) cabF cabG ∧
    SlotsInjective (InlineCfg.canonical 1) cabG ∧
    (InlineCfg.canonical 1).ret = .temp 1 ∧
    TempFresh 1 (InlineCfg.canonical 1) cabF cabG ∧
    (InlineCfg.canonical 1).redirectContinue = true ∧
    (InlineCfg.canonical 1).resumeMap = .unwind ∧
    (InlineCfg.canonical 1).link = .rustc ∧
    ¬ (cabF.caps = cabG.caps) ∧
    CapsSubset cabG cabF ∧
    CapLegal cabG ∧
    AbiInsensitive cabG ∧
    ¬ (cabCi.abiSensitive = false) ∧
    ¬ (AbiAgree cabP cabF cabG) ∧
    SlotsFresh (InlineCfg.canonical 1).withDest cabF cabG ∧
    SlotsInjective (InlineCfg.canonical 1).withDest cabG ∧
    (InlineCfg.canonical 1).withDest.ret = .dest ∧
    (InlineCfg.canonical 1).withDest.redirectContinue = true ∧
    (InlineCfg.canonical 1).withDest.resumeMap = .unwind ∧
    (InlineCfg.canonical 1).withDest.link = .rustc ∧
    CleanupClosed cabF ∧
    DestNotReadInCleanup cabF cabCi.dest) ∧
    ¬ BehEquiv cabP (inline cabP 0 0 (InlineCfg.canonical 1)) ∧
    ¬ BehEquiv cabP (inline cabP 0 0 (InlineCfg.canonical 1).withDest) := by
  exact ⟨by decide, (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩)), (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩))⟩

/-- Destination mode: a cleanup block jumps to a normal block that reads the destination, which the callee wrote before panicking (destination mode only). -/
theorem cex_cleanupClosed :
    (IsCallSite clP 0 0 clF clCi dG ∧
    LocalsBounded clF ∧
    LocalsBounded dG ∧
    BlocksBounded clF ∧
    ScopesWF clF ∧
    ScopesWF dG ∧
    SlotsFresh (InlineCfg.canonical 2) clF dG ∧
    SlotsInjective (InlineCfg.canonical 2) dG ∧
    (InlineCfg.canonical 2).ret = .temp 2 ∧
    TempFresh 2 (InlineCfg.canonical 2) clF dG ∧
    (InlineCfg.canonical 2).redirectContinue = true ∧
    (InlineCfg.canonical 2).resumeMap = .unwind ∧
    (InlineCfg.canonical 2).link = .rustc ∧
    clF.caps = dG.caps ∧
    CapsSubset dG clF ∧
    CapLegal dG ∧
    AbiInsensitive dG ∧
    clCi.abiSensitive = false ∧
    AbiAgree clP clF dG ∧
    SlotsFresh (InlineCfg.canonical 2).withDest clF dG ∧
    SlotsInjective (InlineCfg.canonical 2).withDest dG ∧
    (InlineCfg.canonical 2).withDest.ret = .dest ∧
    (InlineCfg.canonical 2).withDest.redirectContinue = true ∧
    (InlineCfg.canonical 2).withDest.resumeMap = .unwind ∧
    (InlineCfg.canonical 2).withDest.link = .rustc ∧
    ¬ (CleanupClosed clF) ∧
    DestNotReadInCleanup clF clCi.dest) ∧
    ¬ BehEquiv clP (inline clP 0 0 (InlineCfg.canonical 2).withDest) := by
  exact ⟨by decide, (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩))⟩

/-- Destination mode: the caller's cleanup reads the destination, which the callee wrote before panicking (destination mode only). For the configuration `cfg.withDest` every temp-mode hypothesis other than `cfg.ret = .temp 2` also holds (including `TempFresh 2 cfg.withDest`), so this is also the witness for the `cfg.ret = .temp t` hypothesis of the temp-mode theorems. -/
theorem cex_destNotReadInCleanup :
    (IsCallSite dcP 0 0 dcF dcCi dG ∧
    LocalsBounded dcF ∧
    LocalsBounded dG ∧
    BlocksBounded dcF ∧
    ScopesWF dcF ∧
    ScopesWF dG ∧
    SlotsFresh (InlineCfg.canonical 2) dcF dG ∧
    SlotsInjective (InlineCfg.canonical 2) dG ∧
    (InlineCfg.canonical 2).ret = .temp 2 ∧
    TempFresh 2 (InlineCfg.canonical 2) dcF dG ∧
    (InlineCfg.canonical 2).redirectContinue = true ∧
    (InlineCfg.canonical 2).resumeMap = .unwind ∧
    (InlineCfg.canonical 2).link = .rustc ∧
    dcF.caps = dG.caps ∧
    CapsSubset dG dcF ∧
    CapLegal dG ∧
    AbiInsensitive dG ∧
    dcCi.abiSensitive = false ∧
    AbiAgree dcP dcF dG ∧
    SlotsFresh (InlineCfg.canonical 2).withDest dcF dG ∧
    SlotsInjective (InlineCfg.canonical 2).withDest dG ∧
    (InlineCfg.canonical 2).withDest.ret = .dest ∧
    (InlineCfg.canonical 2).withDest.ret ≠ .temp 2 ∧
    TempFresh 2 (InlineCfg.canonical 2).withDest dcF dG ∧
    (InlineCfg.canonical 2).withDest.redirectContinue = true ∧
    (InlineCfg.canonical 2).withDest.resumeMap = .unwind ∧
    (InlineCfg.canonical 2).withDest.link = .rustc ∧
    CleanupClosed dcF ∧
    ¬ (DestNotReadInCleanup dcF dcCi.dest)) ∧
    ¬ BehEquiv dcP (inline dcP 0 0 (InlineCfg.canonical 2).withDest) := by
  exact ⟨by decide, (fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide) (h ⟨0, [], 0⟩))⟩

end Toy.Inline
