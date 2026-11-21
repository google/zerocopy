import ToyInline.Examples

/-!
# Non-vacuity witnesses

For every main result, a concrete instance satisfying all of its hypotheses, fully proved.
-/

namespace Toy.Inline

theorem nonvacuity_frameRel_step :
    RenameInjectiveOn (· + 2) 2 ∧ RenameAvoids (· + 2) 2 [1] ∧
      StmtLocalsLt 2 (.assign 0 (.use (.var 1))) ∧
      FrameRel (· + 2) 2 [1] (cst 4) (cst 7) (upd (cst 7) 1 4) := by decide

/-- `progP` (caller with cleanup, callee that panics on `0`) with the canonical configuration
satisfies every hypothesis of `inline_behEquiv_retTemp_of_capsEq`. -/
theorem nonvacuity_inline_capsEq :
    IsCallSite progP 0 0 fP ciP gP ∧ LocalsBounded fP ∧ LocalsBounded gP ∧ BlocksBounded fP ∧
      ScopesWF fP ∧ ScopesWF gP ∧ SlotsFresh cfgP fP gP ∧ SlotsInjective cfgP gP ∧
      cfgP.ret = .temp 2 ∧ TempFresh 2 cfgP fP gP ∧ cfgP.redirectContinue = true ∧
      cfgP.resumeMap = .unwind ∧ cfgP.link = .rustc ∧ fP.caps = gP.caps := by decide

/-- A second-level site: inlining the copied call to `linkK` inside `linkF1` (a body that already
contains an inlined callee and a nested scope) satisfies every hypothesis of
`inline_behEquiv_retTemp_of_capsEq`. -/
theorem nonvacuity_inline_capsEq_secondLevel :
    IsCallSite linkP1 0 3 linkF1 linkCi1 linkK ∧ LocalsBounded linkF1 ∧ LocalsBounded linkK ∧
      BlocksBounded linkF1 ∧ ScopesWF linkF1 ∧ ScopesWF linkK ∧
      SlotsFresh (InlineCfg.canonical 2) linkF1 linkK ∧
      SlotsInjective (InlineCfg.canonical 2) linkK ∧
      (InlineCfg.canonical 2).ret = .temp 2 ∧ TempFresh 2 (InlineCfg.canonical 2) linkF1 linkK ∧
      (InlineCfg.canonical 2).redirectContinue = true ∧
      (InlineCfg.canonical 2).resumeMap = .unwind ∧ (InlineCfg.canonical 2).link = .rustc ∧
      linkF1.caps = linkK.caps := by decide

theorem nonvacuity_inline_retDest :
    IsCallSite progP 0 0 fP ciP gP ∧ LocalsBounded fP ∧ LocalsBounded gP ∧ BlocksBounded fP ∧
      ScopesWF fP ∧ ScopesWF gP ∧ SlotsFresh cfgPd fP gP ∧ SlotsInjective cfgPd gP ∧
      cfgPd.ret = .dest ∧ CleanupClosed fP ∧ DestNotReadInCleanup fP ciP.dest ∧
      cfgPd.redirectContinue = true ∧ cfgPd.resumeMap = .unwind ∧ cfgPd.link = .rustc ∧
      fP.caps = gP.caps := by decide

theorem nonvacuity_terminalHolds_iff : BehEquivAt progP (inline progP 0 0 cfgP) ⟨0, [0], 0⟩ :=
  behEquivAt_pos

theorem nonvacuity_safetyHolds_iff :
    BehEquivAt progP (inline progP 0 0 cfgP) ⟨0, [0], 0⟩ ∧ PrefixClosed NoPanic :=
  ⟨behEquivAt_pos, prefixClosed_noPanic⟩

/-- Host list `[1, 2]`, callee list `[2]` using capability `2`, no ABI-sensitive calls; note
`abiC [1, 2] ≠ abiC [2]`. -/
def nv5F : Fn := mkFn 1 [blk [] (mkCall 1 [] 0 (some 1) .continue), blk [] .ret] (caps := [1, 2])
def nv5G : Fn := mkFn 1 [blk [.needCap 2, .emit (.const 1)] .ret] (caps := [2])
def nv5P : Program := mkProg [nv5F, nv5G] (abi := abiC)

theorem nonvacuity_inline_capsSubset_abiInsensitive :
    IsCallSite nv5P 0 0 nv5F plainCi nv5G ∧ LocalsBounded nv5F ∧ LocalsBounded nv5G ∧
      BlocksBounded nv5F ∧ ScopesWF nv5F ∧ ScopesWF nv5G ∧
      SlotsFresh (InlineCfg.canonical 1) nv5F nv5G ∧
      SlotsInjective (InlineCfg.canonical 1) nv5G ∧ (InlineCfg.canonical 1).ret = .temp 1 ∧
      TempFresh 1 (InlineCfg.canonical 1) nv5F nv5G ∧
      (InlineCfg.canonical 1).redirectContinue = true ∧
      (InlineCfg.canonical 1).resumeMap = .unwind ∧ (InlineCfg.canonical 1).link = .rustc ∧
      CapsSubset nv5G nv5F ∧ CapLegal nv5G ∧ AbiInsensitive nv5G ∧
      plainCi.abiSensitive = false ∧ nv5F.caps ≠ nv5G.caps := by decide

/-- Host list `[0, 2]`, callee list `[2]` using capability `2` and making an ABI-sensitive call;
`abiC` agrees on both lists. -/
def nv6F : Fn := mkFn 1 [blk [] (mkCall 1 [] 0 (some 1) .continue), blk [] .ret] (caps := [0, 2])
def nv6G : Fn := mkFn 1 [blk [.needCap 2] (mkCall 2 [.const 5] 0 (some 1) .continue
  (abiSens := true)), blk [] .ret] (caps := [2])
def nv6K : Fn := mkFn 2 [blk [.emit (.var 1)] .ret] (caps := [2])
def nv6P : Program := mkProg [nv6F, nv6G, nv6K] (abi := abiC)

theorem nonvacuity_inline_capsSubset_abiAgree :
    IsCallSite nv6P 0 0 nv6F plainCi nv6G ∧ LocalsBounded nv6F ∧ LocalsBounded nv6G ∧
      BlocksBounded nv6F ∧ ScopesWF nv6F ∧ ScopesWF nv6G ∧
      SlotsFresh (InlineCfg.canonical 1) nv6F nv6G ∧
      SlotsInjective (InlineCfg.canonical 1) nv6G ∧ (InlineCfg.canonical 1).ret = .temp 1 ∧
      TempFresh 1 (InlineCfg.canonical 1) nv6F nv6G ∧
      (InlineCfg.canonical 1).redirectContinue = true ∧
      (InlineCfg.canonical 1).resumeMap = .unwind ∧ (InlineCfg.canonical 1).link = .rustc ∧
      CapsSubset nv6G nv6F ∧ CapLegal nv6G ∧ AbiAgree nv6P nv6F nv6G ∧
      ¬ AbiInsensitive nv6G ∧ nv6F.caps ≠ nv6G.caps := by decide

/-- `linkF1` (a host already containing an inlined tracked callee and a nested scope),
`linkK` and the `rustc` rule satisfy every hypothesis of `locValue_inline_calleeScope` (with
`s = 0`). -/
theorem nonvacuity_locValue_calleeScope :
    ScopeParentsBelow linkF1.scopes ∧ ScopeTreeWF linkK.scopes ∧ 0 < linkK.scopes.length ∧
      LinkRule.rustc = LinkRule.rustc := by decide

/-- `linkF1` and its scope `2` satisfy every hypothesis of `locValue_inline_callerScope`. -/
theorem nonvacuity_locValue_callerScope :
    ScopeParentsBelow linkF1.scopes ∧ 2 < linkF1.scopes.length := by decide

/-- `linkF`, its block `0`, and `linkG` satisfy every hypothesis of `scopesWF_inlineFn`. -/
theorem nonvacuity_scopesWF_inlineFn :
    nth? linkF.blocks 0 = some (blk [] (.call linkCi0)) ∧ ScopesWF linkF ∧
      ScopeParentsBelow linkG.scopes ∧ ScopeRefsBounded linkG := by
  decide

/-- `linkF`, its block `0` (ending in `linkCi0`), and `linkG` satisfy every hypothesis of
`localsBounded_inlineFn`. -/
theorem nonvacuity_localsBounded_inlineFn :
    nth? linkF.blocks 0 = some (blk [] (.call linkCi0)) ∧
      (blk [] (.call linkCi0)).term = .call linkCi0 ∧ LocalsBounded linkF ∧
      LocalsBounded linkG := by
  decide

/-- Three pairwise distinct programs with `BehEquiv pMissing pUnr` and `BehEquiv pUnr pGotoUnr`
satisfy both hypotheses of `behEquiv_trans`. -/
theorem nonvacuity_behEquiv_trans :
    pMissing.fns ≠ pUnr.fns ∧ pUnr.fns ≠ pGotoUnr.fns ∧ pMissing.fns ≠ pGotoUnr.fns ∧
      BehEquiv pMissing pUnr ∧ BehEquiv pUnr pGotoUnr :=
  ⟨by decide, by decide, by decide, behEquiv_pMissing_pUnr, behEquiv_pUnr_pGotoUnr⟩

end Toy.Inline
