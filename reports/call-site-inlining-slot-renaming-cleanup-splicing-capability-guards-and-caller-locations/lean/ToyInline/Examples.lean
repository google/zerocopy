import ToyInline.OtherCounterexamples

/-!
# Definition examples

For each core definition, at least one intended instance it admits and one it must reject,
all fully proved.
-/

namespace Toy.Inline

/-! ## Semantics -/

/-- The reference semantics unwinds LIFO: a panic in the callee runs the callee's cleanup
(`out 100`) before the caller's cleanup (`out 200`), then escapes. -/
theorem run_progP_lifo :
    run progP 40 (init progP ⟨0, [0], 0⟩) = ⟨[.out 100, .out 200], some .unwound⟩ := by decide

/-- Negative: the caller's cleanup does not run first. -/
theorem run_progP_not_fifo :
    (run progP 40 (init progP ⟨0, [0], 0⟩)).events ≠ [.out 200, .out 100] := by decide

/-- Normal run: the callee emits its argument and returns it plus one, which the caller emits. -/
theorem run_progP_normal :
    run progP 40 (init progP ⟨0, [7], 0⟩) = ⟨[.out 7, .out 8], some (.returned 0)⟩ := by decide

/-- ABI garbling: from host capability list `[1]`, an ABI-sensitive call to a capability-free
callee passes `5 + 1`. -/
theorem run_abi_garbles :
    run (mkProg [cabF, cabG] (abi := abiC)) 20 (init (mkProg [cabF, cabG] (abi := abiC)) e0) =
      ⟨[.out 6], some (.returned 0)⟩ := by decide

/-- Negative: with an ABI map that ignores capabilities, nothing is garbled. -/
theorem run_abi_not_garbled :
    (run (mkProg [cabF, cabG]) 20 (init (mkProg [cabF, cabG]) e0)).events ≠ [.out 6] := by decide

/-- `needCap` without the capability faults; with it, execution continues. -/
theorem run_needCap_fault : run legalP 20 (init legalP ⟨1, [], 0⟩) = ⟨[], some .capFault⟩ := by
  decide

theorem run_needCap_ok : run needP 20 (init needP ⟨1, [], 0⟩) = ⟨[.out 1], some (.returned 0)⟩ := by
  decide

/-! ## Caller locations -/

/-- Implicit-argument semantics: `k` (tracked) called by `g` (tracked) called by `f`
(untracked, call span `10`) reports `10`, the location of the call in the nearest untracked
frame. -/
theorem run_chain_tracked :
    run (chainP true) 30 (init (chainP true) e0) = ⟨[.loc 10], some (.returned 0)⟩ := by decide

/-- With an untracked wrapper `g`, `k` reports `g`'s call span `20`. -/
theorem run_chain_wrapper :
    run (chainP false) 30 (init (chainP false) e0) = ⟨[.loc 20], some (.returned 0)⟩ := by decide

/-- The scope walk on the twice-inlined body: from `k`'s inlined scope `2`, through `g`'s inlined
scope `1`, to the untracked host: `10`. -/
theorem locValue_chainQ :
    (nth? (chainQ true).fns 0).map (fun F => locValue (chainQ true).tracked F.scopes 2 30 none) =
      some 10 := by decide

/-- Negative: it is not the innermost callsite span. -/
theorem locValue_chainQ_ne :
    (nth? (chainQ true).fns 0).map (fun F => locValue (chainQ true).tracked F.scopes 2 30 none) ≠
      some 20 := by decide

/-- `linkScopes` with the `rustc` rule on the second level of `linkP1`: the new root of `k` points
to `g`'s inlined scope `1` through the callsite scope `2`'s own `inlinedParent`. -/
theorem linkScopes_rustc_example :
    linkScopes .rustc linkF1 linkCi1 linkK = [⟨some (2, 20), some 1⟩] := by decide

/-- Negative: the `ignoreParent` rule drops that link. -/
theorem linkScopes_ignoreParent_example :
    linkScopes .ignoreParent linkF1 linkCi1 linkK ≠ [⟨some (2, 20), some 1⟩] := by decide

/-! ## The inliner -/

/-- Inlining `gP` into `fP`: the callee's `resume` becomes a jump to the caller's cleanup block
`2`, its `ret` a jump to the return block `3`, and the call block ends in the prologue. -/
theorem inline_progP_shape :
    (nth? (inline progP 0 0 cfgP).fns 0).map (fun F => F.blocks.map Block.term) =
      some [.goto 4, .ret, .resume, .goto 1, .branch (.var 3) 5 6, .panic (.cleanup 7), .goto 3,
        .goto 2] ∧
    (nth? (inline progP 0 0 cfgP).fns 0).map (fun F => (nth? F.blocks 0).map Block.stmts) =
      some (some [.assign 3 (.use (.var 1)), .assign 2 (.use (.const 0))]) := by decide

/-- Negative: a block that does not end in a call is left alone. -/
theorem inline_nonCall_unchanged : (inline progP 0 1 cfgP).fns = progP.fns := by decide

/-! ## Observation order and behavioural equivalence -/

theorem prefix_pos : Obs.Prefix ⟨[.out 1], none⟩ ⟨[.out 1, .out 2], some .ub⟩ :=
  ⟨⟨[.out 2], rfl⟩, by simp⟩

/-- Negative: a halted observation is not a prefix of a different observation. -/
theorem prefix_neg : ¬ Obs.Prefix ⟨[.out 1], some .ub⟩ ⟨[.out 1, .out 2], some .ub⟩ := by
  intro h
  have := h.2 rfl
  simp at this

theorem behEquivAt_pos : BehEquivAt progP (inline progP 0 0 cfgP) ⟨0, [0], 0⟩ :=
  behEquivAtWith_of_halted_eq (n := 40) (m := 60) (by decide) (by decide)

theorem behEquivAt_neg : ¬ BehEquivAt contP (inline contP 0 0 contCfg) e0 :=
  not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide)

/-! ## Hypotheses on call sites and bodies -/

theorem isCallSite_pos : IsCallSite progP 0 0 fP ciP gP := by decide
theorem isCallSite_neg : ¬ IsCallSite progP 0 1 fP ciP gP := by decide

theorem localsBounded_pos : LocalsBounded fP := by decide
theorem localsBounded_neg : ¬ LocalsBounded locFF := by decide

theorem blocksBounded_pos : BlocksBounded fP := by decide
theorem blocksBounded_neg : ¬ BlocksBounded blkFF := by decide

theorem scopeParentsBelow_pos : ScopeParentsBelow linkF1.scopes := by decide
/-- Negative: an acyclic table whose link points to a larger index is rejected. -/
theorem scopeParentsBelow_neg :
    ¬ ScopeParentsBelow [⟨none, some 2⟩, ⟨none, none⟩, ⟨none, none⟩] := by decide

theorem scopeTreeWF_pos : ScopeTreeWF linkF1.scopes := by decide
theorem scopeTreeWF_neg : ¬ ScopeTreeWF cycScopes := by decide

theorem scopeRefsBounded_pos : ScopeRefsBounded linkF1 := by decide
theorem scopeRefsBounded_neg : ¬ ScopeRefsBounded scFF := by decide

theorem scopesWF_pos : ScopesWF linkG := by decide
theorem scopesWF_neg : ¬ ScopesWF scGG := by decide

theorem slotsFresh_pos : SlotsFresh cfgP fP gP := by decide
theorem slotsFresh_neg : ¬ SlotsFresh freshCfg freshF freshG := by decide

theorem slotsInjective_pos : SlotsInjective (InlineCfg.canonical 1) injG := by decide
theorem slotsInjective_neg : ¬ SlotsInjective injCfg injG := by decide

theorem tempFresh_pos : TempFresh 2 cfgP fP gP := by decide
theorem tempFresh_neg : ¬ TempFresh 2 tempCfg tempF tempG := by decide

theorem cleanupClosed_pos : CleanupClosed dcF := by decide
theorem cleanupClosed_neg : ¬ CleanupClosed clF := by decide

theorem destNotReadInCleanup_pos : DestNotReadInCleanup clF 1 := by decide
theorem destNotReadInCleanup_neg : ¬ DestNotReadInCleanup dcF 1 := by decide

theorem capsSubset_pos : CapsSubset abiG (capF [1]) := by decide
theorem capsSubset_neg : ¬ CapsSubset needG (capF []) := by decide

theorem capLegal_pos : CapLegal needG := by decide
theorem capLegal_neg : ¬ CapLegal legalG := by decide

theorem abiInsensitive_pos : AbiInsensitive gP := by decide
theorem abiInsensitive_neg : ¬ AbiInsensitive abiG := by decide

theorem abiAgree_pos : AbiAgree abiPc (capF [1]) abiG := by decide
theorem abiAgree_neg : ¬ AbiAgree abiP (capF [1]) abiG := by decide

/-! ## Store-level frame relation -/

theorem frameRel_pos : FrameRel (· + 2) 2 [1] (cst 4) (cst 7) (upd (cst 7) 1 4) := by decide
theorem frameRel_neg : ¬ FrameRel (· + 2) 2 [1] (cst 4) (cst 7) (cst 7) := by decide

theorem renameInjectiveOn_pos : RenameInjectiveOn (· + 2) 3 := by decide
theorem renameInjectiveOn_neg : ¬ RenameInjectiveOn (fun _ => 5) 2 := by decide

theorem renameAvoids_pos : RenameAvoids (· + 2) 2 [0, 1] := by decide
theorem renameAvoids_neg : ¬ RenameAvoids (· + 1) 2 [2] := by decide

theorem stmtLocalsLt_pos : StmtLocalsLt 2 (.assign 1 (.add (.var 0) (.const 3))) := by decide
theorem stmtLocalsLt_neg : ¬ StmtLocalsLt 2 (.emit (.var 2)) := by decide

/-! ## Observation properties -/

theorem noPanic_pos : NoPanic ⟨[], some (.returned 0)⟩ := by decide
theorem noPanic_neg : ¬ NoPanic ⟨[], some .unwound⟩ := by decide

theorem terminalHolds_pos : TerminalHolds NoPanic pRet e0 :=
  terminalHolds_of_halted (n := 5) (by decide) (by decide)
theorem terminalHolds_neg : ¬ TerminalHolds NoPanic pPan e0 :=
  not_terminalHolds_of_halted (n := 5) (by decide) (by decide)

theorem safetyHolds_pos : SafetyHolds NoPanic pRet e0 :=
  safetyHolds_noPanic_of_halted (N := 5) (o := .returned 0) (by decide) (by decide)
theorem safetyHolds_neg : ¬ SafetyHolds NoPanic pPan e0 := fun h => absurd (h 5) (by decide)

theorem prefixClosed_pos : PrefixClosed NoPanic := prefixClosed_noPanic
theorem prefixClosed_neg : ¬ PrefixClosed (fun o => o.outcome.isSome = true) :=
  cex_safety_prefixClosed.1.2

end Toy.Inline
