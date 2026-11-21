import ToyInline.Counterexamples

/-!
# Further counterexamples, impossibility statements and positive controls

Tightness witnesses for the frame lemma, the transfer theorems, the scope-walk theorems and
transitivity; the verification-condition non-claim; the insufficiency of the subset guard;
the naive caller-location policies; and the inlining-order instance.
-/

namespace Toy.Inline

/-! ## Frame relation (store level) -/

/-- Store with every local equal to `v`. -/
def cst (v : Nat) : Local → Nat := fun _ => v

/-- Non-injective renaming: callee locals `0` (return place) and `1` (argument) share host local
`5`; the callee's write to its return place clobbers the argument's image. All other hypotheses
hold; the conclusion fails. -/
theorem cex_frame_injective :
    (RenameAvoids (fun _ => 5) 2 [] ∧ StmtLocalsLt 2 (.assign 0 (.use (.const 7))) ∧
      FrameRel (fun _ => 5) 2 [] (cst 0) (cst 3) (cst 3) ∧ ¬ RenameInjectiveOn (fun _ => 5) 2) ∧
    ¬ (FrameRel (fun _ => 5) 2 [] (cst 0) (stmtStore (cst 3) (.assign 0 (.use (.const 7)))).1
          (stmtStore (cst 3) ((Stmt.assign 0 (.use (.const 7))).rename (fun _ => 5) 0)).1 ∧
        (stmtStore (cst 3) ((Stmt.assign 0 (.use (.const 7))).rename (fun _ => 5) 0)).2 =
          (stmtStore (cst 3) (.assign 0 (.use (.const 7)))).2) := by
  decide

/-- Overlapping range: callee local `1` goes to host local `2`, a caller local live across the
call; writing it clobbers the caller's value. All other hypotheses hold; the conclusion
fails. -/
theorem cex_frame_avoids :
    (RenameInjectiveOn (· + 1) 2 ∧ StmtLocalsLt 2 (.assign 1 (.use (.const 7))) ∧
      FrameRel (· + 1) 2 [2] (cst 4) (cst 4) (cst 4) ∧ ¬ RenameAvoids (· + 1) 2 [2]) ∧
    ¬ (FrameRel (· + 1) 2 [2] (cst 4) (stmtStore (cst 4) (.assign 1 (.use (.const 7)))).1
          (stmtStore (cst 4) ((Stmt.assign 1 (.use (.const 7))).rename (· + 1) 0)).1 ∧
        (stmtStore (cst 4) ((Stmt.assign 1 (.use (.const 7))).rename (· + 1) 0)).2 =
          (stmtStore (cst 4) (.assign 1 (.use (.const 7)))).2) := by
  decide

/-- The statement reads callee local `2`, outside the range `n = 2` the relation covers. -/
theorem cex_frame_stmtLocals :
    (RenameInjectiveOn (· + 10) 2 ∧ RenameAvoids (· + 10) 2 [] ∧
      FrameRel (· + 10) 2 [] (cst 0) (cst 1) (upd (cst 1) 12 9) ∧
      ¬ StmtLocalsLt 2 (.emit (.var 2))) ∧
    ¬ (FrameRel (· + 10) 2 [] (cst 0) (stmtStore (cst 1) (.emit (.var 2))).1
          (stmtStore (upd (cst 1) 12 9) ((Stmt.emit (.var 2)).rename (· + 10) 0)).1 ∧
        (stmtStore (upd (cst 1) 12 9) ((Stmt.emit (.var 2)).rename (· + 10) 0)).2 =
          (stmtStore (cst 1) (.emit (.var 2))).2) := by
  decide

/-- Without the relation before the step, nothing is preserved. -/
theorem cex_frame_rel :
    (RenameInjectiveOn (· + 10) 1 ∧ RenameAvoids (· + 10) 1 [] ∧ StmtLocalsLt 1 (.emit (.var 0)) ∧
      ¬ FrameRel (· + 10) 1 [] (cst 0) (cst 1) (cst 2)) ∧
    ¬ (FrameRel (· + 10) 1 [] (cst 0) (stmtStore (cst 1) (.emit (.var 0))).1
          (stmtStore (cst 2) ((Stmt.emit (.var 0)).rename (· + 10) 0)).1 ∧
        (stmtStore (cst 2) ((Stmt.emit (.var 0)).rename (· + 10) 0)).2 =
          (stmtStore (cst 1) (.emit (.var 0))).2) := by
  decide

/-! ## Transfer theorems -/

def pRet : Program := mkProg [mkFn 1 [blk [] .ret]]
def pPan : Program := mkProg [mkFn 1 [blk [] (.panic .continue)]]
def pMissing : Program := mkProg []
def pUnr : Program := mkProg [mkFn 1 [blk [] .unreachable]]
def e0 : Entry := ⟨0, [], 0⟩

theorem behEquiv_refl (p : Program) : BehEquiv p p := fun e => behEquivAtWith_refl .walk p e

theorem not_behEquivAt_pRet_pPan : ¬ BehEquivAt pRet pPan e0 :=
  not_behEquivAtWith_of_halted_ne (n := 5) (m := 5) (by decide) (by decide) (by decide)

theorem prefixClosed_noPanic : PrefixClosed NoPanic := by
  intro o o' h h' hc
  apply h'
  have hs : o.outcome.isSome := by rw [hc]; rfl
  rw [h.2 hs]
  exact hc

theorem safetyHolds_noPanic_of_halted {p : Program} {e : Entry} {N : Nat} {o : Outcome}
    (hN : (run p N (init p e)).outcome = some o) (ho : o ≠ .unwound) :
    SafetyHolds NoPanic p e := by
  intro n
  have hs : (run p N (init p e)).outcome.isSome := by rw [hN]; rfl
  have h := runWith_prefix_of_halted hs n
  cases hc : (run p n (init p e)).outcome with
  | none => intro h'; rw [hc] at h'; cases h'
  | some r =>
    have heq : run p N (init p e) = run p n (init p e) := h.2 (by rw [hc]; rfl)
    intro h'
    rw [← heq, hN] at h'
    exact ho (Option.some.inj h')

/-- Dropping behavioural equivalence: two programs with different outcomes disagree on the
terminal property `NoPanic`. -/
theorem cex_terminal_behEquiv :
    ¬ BehEquivAt pRet pPan e0 ∧ ¬ (TerminalHolds NoPanic pRet e0 ↔ TerminalHolds NoPanic pPan e0) :=
  ⟨not_behEquivAt_pRet_pPan, fun h =>
    not_terminalHolds_of_halted (n := 5) (by decide) (by decide)
      (h.1 (terminalHolds_of_halted (n := 5) (by decide) (by decide)))⟩

/-- Dropping behavioural equivalence (safety version; `NoPanic` is prefix-closed). -/
theorem cex_safety_behEquiv :
    (PrefixClosed NoPanic ∧ ¬ BehEquivAt pRet pPan e0) ∧
      ¬ (SafetyHolds NoPanic pRet e0 ↔ SafetyHolds NoPanic pPan e0) :=
  ⟨⟨prefixClosed_noPanic, not_behEquivAt_pRet_pPan⟩, fun h =>
    (fun hs => absurd (hs 5) (by decide))
      (h.1 (safetyHolds_noPanic_of_halted (N := 5) (o := .returned 0) (by decide) (by decide)))⟩

/-- "Has halted" is not prefix-closed and does not transfer: a program whose entry is missing
halts at once, an equivalent one first takes a silent step. -/
theorem cex_safety_prefixClosed :
    (BehEquivAt pMissing pUnr e0 ∧ ¬ PrefixClosed (fun o => o.outcome.isSome = true)) ∧
      ¬ (SafetyHolds (fun o => o.outcome.isSome = true) pMissing e0 ↔
          SafetyHolds (fun o => o.outcome.isSome = true) pUnr e0) := by
  refine ⟨⟨behEquivAtWith_of_halted_eq (n := 0) (m := 1) (by decide) (by decide), ?_⟩, ?_⟩
  · intro h
    have := h ⟨[], none⟩ ⟨[], some .ub⟩ ⟨List.nil_prefix, by simp⟩ rfl
    simp at this
  · intro h
    have hm : SafetyHolds (fun o => o.outcome.isSome = true) pMissing e0 := by
      intro n
      show (runWith .walk pMissing n (.halted .ub)).outcome.isSome = true
      rw [runWith_halted]; rfl
    exact absurd ((h.1 hm) 0) (by decide)

/-! ## What an inlined verification condition does not say -/

/-- Caller passing the constant `7` to the callee `gP` (which panics on `0`). -/
def vcF : Fn := mkFn 2 [blk [] (mkCall 1 [.const 7] 1 (some 1) .continue),
  blk [.emit (.var 1)] .ret]
def vcP : Program := mkProg [vcF, gP]
def vcQ : Program := inlineCanon vcP 0 0

/-- **A verification condition proved after inlining is not the callee's contract.** The
"no escaped panic" property holds for the inlined caller (and the original caller), because
the inlined code sees the call-site argument `7`; the callee itself, from its own entry with
argument `0`, runs its cleanup (event `out 100`) and ends in an escaped panic, in the original
and in the inlined program. -/
theorem inlined_vc_not_callee_contract :
    TerminalHolds NoPanic vcQ e0 ∧ TerminalHolds NoPanic vcP e0 ∧
      run vcP 30 (init vcP ⟨1, [0], 0⟩) = ⟨[.out 100], some .unwound⟩ ∧
      run vcQ 30 (init vcQ ⟨1, [0], 0⟩) = ⟨[.out 100], some .unwound⟩ ∧
      ¬ TerminalHolds NoPanic vcP ⟨1, [0], 0⟩ ∧ ¬ TerminalHolds NoPanic vcQ ⟨1, [0], 0⟩ :=
  ⟨terminalHolds_of_halted (n := 30) (by decide) (by decide),
   terminalHolds_of_halted (n := 30) (by decide) (by decide),
   by decide, by decide,
   not_terminalHolds_of_halted (n := 30) (by decide) (by decide),
   not_terminalHolds_of_halted (n := 30) (by decide) (by decide)⟩

/-! ## The subset guard is insufficient -/

/-- **Impossibility: "caller ⊇ callee" (with static capability legality and a non-ABI-sensitive
inlined call) does not make temp-mode inlining a behavioural equivalence.** The universal
statement is refuted by the instance exposed in `capsSubset_guard_insufficient_witness`. -/
theorem capsSubset_guard_insufficient :
    ¬ (∀ (p : Program) (f b : Nat) (F : Fn) (ci : CallInfo) (G : Fn) (cfg : InlineCfg)
        (t : Local),
        IsCallSite p f b F ci G → LocalsBounded F → LocalsBounded G → BlocksBounded F →
        ScopesWF F → ScopesWF G → SlotsFresh cfg F G → SlotsInjective cfg G →
        cfg.ret = .temp t → TempFresh t cfg F G → cfg.redirectContinue = true →
        cfg.resumeMap = .unwind → cfg.link = .rustc →
        CapsSubset G F → CapLegal G → ci.abiSensitive = false →
        BehEquiv p (inline p f b cfg)) := by
  intro h
  exact cex_capsAbi.2.1 (h abiP 0 0 (capF [1]) plainCi abiG (InlineCfg.canonical 1) 1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide))

/-- **The witness for `capsSubset_guard_insufficient`.** In `abiP` the host `capF [1]` holds
capability `1` and the callee `abiG` holds none; every hypothesis of the refuted universal holds
(temp mode, `t = 1`); `abiP.abi [1] ≠ abiP.abi []`; the callee's ABI-sensitive call passes `5`
correctly in the original program (event `out 5`) and garbles it to `6` after inlining, so the
inlined program is not behaviourally equivalent to the original. -/
theorem capsSubset_guard_insufficient_witness :
    (IsCallSite abiP 0 0 (capF [1]) plainCi abiG ∧ LocalsBounded (capF [1]) ∧
      LocalsBounded abiG ∧ BlocksBounded (capF [1]) ∧ ScopesWF (capF [1]) ∧ ScopesWF abiG ∧
      SlotsFresh (InlineCfg.canonical 1) (capF [1]) abiG ∧
      SlotsInjective (InlineCfg.canonical 1) abiG ∧
      (InlineCfg.canonical 1).ret = .temp 1 ∧ TempFresh 1 (InlineCfg.canonical 1) (capF [1]) abiG ∧
      (InlineCfg.canonical 1).redirectContinue = true ∧
      (InlineCfg.canonical 1).resumeMap = .unwind ∧ (InlineCfg.canonical 1).link = .rustc ∧
      CapsSubset abiG (capF [1]) ∧ CapLegal abiG ∧ plainCi.abiSensitive = false) ∧
    (capF [1]).caps = [1] ∧ abiG.caps = [] ∧ abiP.abi [1] ≠ abiP.abi [] ∧
    run abiP 30 (init abiP e0) = ⟨[.out 5], some (.returned 0)⟩ ∧
    run (inline abiP 0 0 (InlineCfg.canonical 1)) 40
        (init (inline abiP 0 0 (InlineCfg.canonical 1)) e0) = ⟨[.out 6], some (.returned 0)⟩ ∧
    ¬ BehEquiv abiP (inline abiP 0 0 (InlineCfg.canonical 1)) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
   fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide)
     (by decide) (h e0)⟩

/-- **Positive control.** The same program with an ABI map that ignores capabilities satisfies
every hypothesis of `inline_behEquiv_retTemp_of_capsSubset_capLegal_abiAgree`, and the inlined
program is behaviourally equivalent to the original from every entry. -/
theorem capsSubset_guard_positiveControl :
    (IsCallSite abiPc 0 0 (capF [1]) plainCi abiG ∧ LocalsBounded (capF [1]) ∧
      LocalsBounded abiG ∧ BlocksBounded (capF [1]) ∧ ScopesWF (capF [1]) ∧ ScopesWF abiG ∧
      SlotsFresh (InlineCfg.canonical 1) (capF [1]) abiG ∧
      SlotsInjective (InlineCfg.canonical 1) abiG ∧
      (InlineCfg.canonical 1).ret = .temp 1 ∧ TempFresh 1 (InlineCfg.canonical 1) (capF [1]) abiG ∧
      (InlineCfg.canonical 1).redirectContinue = true ∧
      (InlineCfg.canonical 1).resumeMap = .unwind ∧ (InlineCfg.canonical 1).link = .rustc ∧
      CapsSubset abiG (capF [1]) ∧ CapLegal abiG ∧ plainCi.abiSensitive = false ∧
      AbiAgree abiPc (capF [1]) abiG) ∧
    BehEquiv abiPc (inline abiPc 0 0 (InlineCfg.canonical 1)) := by
  refine ⟨by decide, ?_⟩
  intro ⟨fn, args, loc⟩
  cases fn with
  | zero =>
    exact behEquivAtWith_of_halted_eq (n := 20) (m := 25) (by rfl) (by rfl)
  | succ fn =>
    cases fn with
    | zero =>
      exact behEquivAtWith_of_halted_eq (n := 20) (m := 20) (by rfl) (by rfl)
    | succ fn =>
      cases fn with
      | zero =>
        exact behEquivAtWith_of_halted_eq (n := 10) (m := 10) (by rfl) (by rfl)
      | succ k =>
        have h1 : nth? abiPc.fns (k + 3) = none := rfl
        have h2 : nth? (inline abiPc 0 0 (InlineCfg.canonical 1)).fns (k + 3) = none := rfl
        exact behEquivAtWith_of_halted_eq (n := 1) (m := 1)
          (by simp [runWith, init, h1]) (by simp [runWith, init, h1, h2])

/-! ## Naive caller-location policies -/

/-- **"Innermost callsite span" is wrong for tracked chains.** Tracked `k` called (span `20`) by
tracked `g` called (span `10`) by untracked `f`. On the original program every policy reports
`10`; after inlining `g` into `f` and then the copied call to `k`, the scope walk still reports
`10` (and the inlined program is behaviourally equivalent from `f`'s entry), while the
innermost-span policy reports `20`. -/
theorem innermost_policy_wrong_for_tracked_chain :
    (∀ pol : LocPolicy, runWith pol (chainP true) 30 (init (chainP true) e0) =
        ⟨[.loc 10], some (.returned 0)⟩) ∧
      run (chainQ true) 40 (init (chainQ true) e0) = ⟨[.loc 10], some (.returned 0)⟩ ∧
      runWith .innermost (chainQ true) 40 (init (chainQ true) e0) =
        ⟨[.loc 20], some (.returned 0)⟩ ∧
      BehEquivAt (chainP true) (chainQ true) e0 ∧
      ¬ BehEquivAtWith .innermost (chainP true) (chainQ true) e0 :=
  ⟨fun pol => by cases pol <;> decide, by decide, by decide,
   behEquivAtWith_of_halted_eq (n := 30) (m := 40) (by decide) (by decide),
   not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide)⟩

/-- **"Outermost callsite span" is wrong for an untracked wrapper.** Tracked `k` called (span
`20`) by an untracked wrapper `g` called (span `10`) by `f`. On the original program every
policy reports `20`; after inlining both calls the scope walk still reports `20` (and the
inlined program is behaviourally equivalent from `f`'s entry), while the outermost-span policy
reports `10`. -/
theorem outermost_policy_wrong_for_untracked_wrapper :
    (∀ pol : LocPolicy, runWith pol (chainP false) 30 (init (chainP false) e0) =
        ⟨[.loc 20], some (.returned 0)⟩) ∧
      run (chainQ false) 40 (init (chainQ false) e0) = ⟨[.loc 20], some (.returned 0)⟩ ∧
      runWith .outermost (chainQ false) 40 (init (chainQ false) e0) =
        ⟨[.loc 10], some (.returned 0)⟩ ∧
      BehEquivAt (chainP false) (chainQ false) e0 ∧
      ¬ BehEquivAtWith .outermost (chainP false) (chainQ false) e0 :=
  ⟨fun pol => by cases pol <;> decide, by decide, by decide,
   behEquivAtWith_of_halted_eq (n := 30) (m := 40) (by decide) (by decide),
   not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide) (by decide)⟩

/-! ## Scope-walk theorems: tightness -/

def scopesFn (s : List Scope) : Fn := mkFn 1 [] (scopes := s)
/-- A scope table whose `inlinedParent` links form a cycle (`1 → 2 → 1`) through two tracked
inlined scopes with different callsite spans. -/
def cycScopes : List Scope := [⟨none, none⟩, ⟨some (2, 100), some 2⟩, ⟨some (2, 200), some 1⟩]
def trAll : FnId → Bool := fun _ => true
def ci50 : CallInfo := mkCallInfo 1 [] 0 none .continue (span := 50) (scope := 1)
def ci99 : CallInfo := mkCallInfo 1 [] 0 none .continue (span := 99)

theorem cex_walkCallee_F :
    (ScopeTreeWF (scopesFn [⟨none, none⟩, ⟨none, none⟩]).scopes ∧ 0 < 2 ∧
      LinkRule.rustc = LinkRule.rustc ∧ ¬ ScopeParentsBelow (scopesFn cycScopes).scopes) ∧
    locValue trAll ((scopesFn cycScopes).scopes ++
        linkScopes .rustc (scopesFn cycScopes) ci50 (scopesFn [⟨none, none⟩, ⟨none, none⟩]))
        ((scopesFn cycScopes).scopes.length + 0) 7 none ≠
      locValue trAll (scopesFn [⟨none, none⟩, ⟨none, none⟩]).scopes 0 7
        (if trAll ci50.callee then
          some (locValue trAll (scopesFn cycScopes).scopes ci50.scope ci50.span none)
        else none) := by
  decide

/-- The callee's outermost scope already carries `inlined` (of an untracked function `3`): the
clean-outermost-scope conjunct of `ScopeTreeWF` fails while its links-point-below conjunct
holds. -/
theorem cex_walkCallee_G :
    (ScopeParentsBelow (scopesFn rootScopes).scopes ∧ 0 < 1 ∧ LinkRule.rustc = LinkRule.rustc ∧
      ScopeParentsBelow (scopesFn [⟨some (3, 50), none⟩]).scopes ∧
      ¬ ScopeTreeWF (scopesFn [⟨some (3, 50), none⟩]).scopes) ∧
    locValue (fun g => g == 1) ((scopesFn rootScopes).scopes ++
        linkScopes .rustc (scopesFn rootScopes) ci99 (scopesFn [⟨some (3, 50), none⟩]))
        ((scopesFn rootScopes).scopes.length + 0) 7 none ≠
      locValue (fun g => g == 1) (scopesFn [⟨some (3, 50), none⟩]).scopes 0 7
        (if (fun g => g == 1) ci99.callee then
          some (locValue (fun g => g == 1) (scopesFn rootScopes).scopes ci99.scope ci99.span none)
        else none) := by
  decide

/-- The callee's table has a clean outermost scope but a 2-cycle (`1 → 2 → 1`) through two
tracked inlined scopes: the links-point-below conjunct of `ScopeTreeWF` fails for `G`. -/
theorem cex_walkCallee_Gparents :
    (ScopeParentsBelow (scopesFn rootScopes).scopes ∧
      nth? (scopesFn cycScopes).scopes 0 = some ⟨none, none⟩ ∧
      ¬ ScopeParentsBelow (scopesFn cycScopes).scopes ∧
      ¬ ScopeTreeWF (scopesFn cycScopes).scopes ∧
      1 < (scopesFn cycScopes).scopes.length ∧ LinkRule.rustc = LinkRule.rustc) ∧
    locValue trAll ((scopesFn rootScopes).scopes ++
        linkScopes .rustc (scopesFn rootScopes) ci99 (scopesFn cycScopes))
        ((scopesFn rootScopes).scopes.length + 1) 7 none ≠
      locValue trAll (scopesFn cycScopes).scopes 1 7
        (if trAll ci99.callee then
          some (locValue trAll (scopesFn rootScopes).scopes ci99.scope ci99.span none)
        else none) := by
  decide

/-- Scope index `1` is outside the callee's one-scope table. -/
theorem cex_walkCallee_s :
    (ScopeParentsBelow (scopesFn rootScopes).scopes ∧ ScopeTreeWF (scopesFn rootScopes).scopes ∧
      LinkRule.rustc = LinkRule.rustc ∧ ¬ (1 < (scopesFn rootScopes).scopes.length)) ∧
    locValue trAll ((scopesFn rootScopes).scopes ++
        linkScopes .rustc (scopesFn rootScopes) ci99 (scopesFn rootScopes))
        ((scopesFn rootScopes).scopes.length + 1) 7 none ≠
      locValue trAll (scopesFn rootScopes).scopes 1 7
        (if trAll ci99.callee then
          some (locValue trAll (scopesFn rootScopes).scopes ci99.scope ci99.span none)
        else none) := by
  decide

/-- The `ignoreParent` link rule at the second level of `linkP1`. -/
theorem cex_walkCallee_link :
    (ScopeParentsBelow linkF1.scopes ∧ ScopeTreeWF linkK.scopes ∧ 0 < linkK.scopes.length ∧
      LinkRule.ignoreParent ≠ LinkRule.rustc) ∧
    locValue linkP1.tracked (linkF1.scopes ++ linkScopes .ignoreParent linkF1 linkCi1 linkK)
        (linkF1.scopes.length + 0) 30 none ≠
      locValue linkP1.tracked linkK.scopes 0 30
        (if linkP1.tracked linkCi1.callee then
          some (locValue linkP1.tracked linkF1.scopes linkCi1.scope linkCi1.span none)
        else none) := by
  decide

/-- Host scope index `1` is the appended callee root, not a host scope. -/
theorem cex_walkCaller_s :
    (ScopeParentsBelow (scopesFn rootScopes).scopes ∧
      ¬ (1 < (scopesFn rootScopes).scopes.length)) ∧
    locValue trAll ((scopesFn rootScopes).scopes ++
        linkScopes .rustc (scopesFn rootScopes) ci99 (scopesFn rootScopes)) 1 7 none ≠
      locValue trAll (scopesFn rootScopes).scopes 1 7 none := by
  decide

/-- A cyclic host table: the walk's answer depends on its fuel, which grows with the table. -/
theorem cex_walkCaller_F :
    (¬ ScopeParentsBelow (scopesFn cycScopes).scopes ∧ 1 < (scopesFn cycScopes).scopes.length) ∧
    locValue trAll ((scopesFn cycScopes).scopes ++
        linkScopes .rustc (scopesFn cycScopes) ci50 (scopesFn rootScopes)) 1 7 none ≠
      locValue trAll (scopesFn cycScopes).scopes 1 7 none := by
  decide

/-- The block passed as `B` is not block `b` of `F`, and it names a missing scope. -/
theorem cex_scopesWF_B :
    (ScopesWF (mkFn 1 [blk [] (.goto 0)]) ∧ ScopeParentsBelow (mkFn 1 []).scopes ∧
      ScopeRefsBounded (mkFn 1 []) ∧
      nth? (mkFn 1 [blk [] (.goto 0)]).blocks 0 ≠ some (blk [.loc 0 9] (.goto 0))) ∧
    ¬ ScopesWF (inlineFn (mkFn 1 [blk [] (.goto 0)]) 0 (blk [.loc 0 9] (.goto 0)) ci99
        (mkFn 1 []) (InlineCfg.canonical 1)) := by
  decide

/-- The host's `loc` names a missing scope: the `ScopeRefsBounded` conjunct of `ScopesWF F` fails
while its `ScopeTreeWF` conjunct holds. -/
theorem cex_scopesWF_F :
    (nth? (mkFn 1 [blk [.loc 0 5] (.goto 0)]).blocks 0 = some (blk [.loc 0 5] (.goto 0)) ∧
      ScopeParentsBelow (mkFn 1 []).scopes ∧ ScopeRefsBounded (mkFn 1 []) ∧
      ScopeTreeWF (mkFn 1 [blk [.loc 0 5] (.goto 0)]).scopes ∧
      ¬ ScopesWF (mkFn 1 [blk [.loc 0 5] (.goto 0)])) ∧
    ¬ ScopesWF (inlineFn (mkFn 1 [blk [.loc 0 5] (.goto 0)]) 0 (blk [.loc 0 5] (.goto 0)) ci99
        (mkFn 1 []) (InlineCfg.canonical 1)) := by
  decide

/-- The callee's `loc` names a missing scope (`ScopeRefsBounded G` fails). -/
theorem cex_scopesWF_G :
    (nth? (mkFn 1 [blk [] (.goto 0)]).blocks 0 = some (blk [] (.goto 0)) ∧
      ScopesWF (mkFn 1 [blk [] (.goto 0)]) ∧
      ScopeParentsBelow (mkFn 1 [blk [.loc 0 5] .ret]).scopes ∧
      ¬ ScopeRefsBounded (mkFn 1 [blk [.loc 0 5] .ret])) ∧
    ¬ ScopesWF (inlineFn (mkFn 1 [blk [] (.goto 0)]) 0 (blk [] (.goto 0)) ci99
        (mkFn 1 [blk [.loc 0 5] .ret]) (InlineCfg.canonical 1)) := by
  decide

/-- The callee's scope `1` links to itself (`ScopeParentsBelow G.scopes` fails); after shifting,
the merged table has a link that does not point below. -/
theorem cex_scopesWF_Gparents :
    (nth? (mkFn 1 [blk [] (.goto 0)]).blocks 0 = some (blk [] (.goto 0)) ∧
      ScopesWF (mkFn 1 [blk [] (.goto 0)]) ∧
      ¬ ScopeParentsBelow (mkFn 1 [] (scopes := [⟨none, none⟩, ⟨none, some 1⟩])).scopes ∧
      ScopeRefsBounded (mkFn 1 [] (scopes := [⟨none, none⟩, ⟨none, some 1⟩]))) ∧
    ¬ ScopesWF (inlineFn (mkFn 1 [blk [] (.goto 0)]) 0 (blk [] (.goto 0)) ci99
        (mkFn 1 [] (scopes := [⟨none, none⟩, ⟨none, some 1⟩])) (InlineCfg.canonical 1)) := by
  decide

/-- Conjunct-level witness for `hF : ScopesWF F` of `scopesWF_inlineFn`: the host's outermost
scope is not clean (its other conjuncts hold); the merged table inherits it. -/
theorem cex_scopesWF_Froot :
    (nth? (mkFn 1 [blk [] (.goto 0)] (scopes := [⟨some (0, 1), none⟩])).blocks 0 =
        some (blk [] (.goto 0)) ∧
      ScopeParentsBelow (mkFn 1 [blk [] (.goto 0)] (scopes := [⟨some (0, 1), none⟩])).scopes ∧
      ScopeRefsBounded (mkFn 1 [blk [] (.goto 0)] (scopes := [⟨some (0, 1), none⟩])) ∧
      ¬ ScopesWF (mkFn 1 [blk [] (.goto 0)] (scopes := [⟨some (0, 1), none⟩])) ∧
      ScopeParentsBelow (mkFn 1 []).scopes ∧ ScopeRefsBounded (mkFn 1 [])) ∧
    ¬ ScopesWF (inlineFn (mkFn 1 [blk [] (.goto 0)] (scopes := [⟨some (0, 1), none⟩])) 0
        (blk [] (.goto 0)) ci99 (mkFn 1 []) (InlineCfg.canonical 1)) := by
  decide

/-- Conjunct-level witness for `hF : ScopesWF F` of `scopesWF_inlineFn`: the host's scope `1`
links to itself (its other conjuncts hold); the merged table inherits it. -/
theorem cex_scopesWF_Fparents :
    (nth? (mkFn 1 [blk [] (.goto 0)] (scopes := [⟨none, none⟩, ⟨none, some 1⟩])).blocks 0 =
        some (blk [] (.goto 0)) ∧
      ¬ ScopeParentsBelow
        (mkFn 1 [blk [] (.goto 0)] (scopes := [⟨none, none⟩, ⟨none, some 1⟩])).scopes ∧
      ScopeRefsBounded (mkFn 1 [blk [] (.goto 0)] (scopes := [⟨none, none⟩, ⟨none, some 1⟩])) ∧
      ScopeParentsBelow (mkFn 1 []).scopes ∧ ScopeRefsBounded (mkFn 1 [])) ∧
    ¬ ScopesWF (inlineFn (mkFn 1 [blk [] (.goto 0)] (scopes := [⟨none, none⟩, ⟨none, some 1⟩])) 0
        (blk [] (.goto 0)) ci99 (mkFn 1 []) (InlineCfg.canonical 1)) := by
  decide

/-! ## Transitivity: tightness -/

theorem cex_trans_left : BehEquiv pPan pPan ∧ ¬ BehEquiv pRet pPan :=
  ⟨behEquiv_refl _, fun h => not_behEquivAt_pRet_pPan (h e0)⟩

theorem cex_trans_right : BehEquiv pRet pRet ∧ ¬ BehEquiv pRet pPan :=
  ⟨behEquiv_refl _, fun h => not_behEquivAt_pRet_pPan (h e0)⟩

/-! ## Inlining order -/

def ordH : Fn := mkFn 1 [blk [] (mkCall 1 [] 0 (some 1) .continue), blk [] .ret]
def ordF : Fn := mkFn 2 [blk [] (mkCall 2 [] 1 (some 1) .continue), blk [.emit (.var 1)] .ret]
def ordG : Fn := mkFn 2 [blk [.assign 1 (.use (.const 4)), .assign 0 (.use (.var 1))] .ret]
def ordP : Program := mkProg [ordH, ordF, ordG]
/-- Inline `g` into `f`, then the new `f` into `h`. -/
def ordQ1 : Program := inlineCanon (inlineCanon ordP 1 0) 0 0
/-- Inline `f` into `h`, then `g` into the copy of `f`'s call (block `3` of the new `h`). -/
def ordQ2 : Program := inlineCanon (inlineCanon ordP 0 0) 0 3

def Fn.totalStmts (F : Fn) : Nat := (F.blocks.flatMap Block.stmts).length

/-- **The two inlining orders give different bodies for `h`.** With the canonical configuration
the first order has two more statements in `h` (the inner callee's slots are zero-initialised
both by `h`'s prologue and by the copied prologue); from the entry `h` both programs behave
like the original. -/
theorem inline_order_changes_body :
    (nth? ordQ1.fns 0).map Fn.totalStmts = some 11 ∧ (nth? ordQ2.fns 0).map Fn.totalStmts = some 9 ∧
      nth? ordQ1.fns 0 ≠ nth? ordQ2.fns 0 ∧
      BehEquivAt ordP ordQ1 e0 ∧ BehEquivAt ordP ordQ2 e0 :=
  ⟨by decide, by decide, by decide,
   behEquivAtWith_of_halted_eq (n := 30) (m := 40) (by decide) (by decide),
   behEquivAtWith_of_halted_eq (n := 30) (m := 40) (by decide) (by decide)⟩

/-- Inlining `g` into `f` and then the new `f` into `h` also replaces `f` (function `1`) in the
function table, while the other order leaves `f` unchanged. -/
theorem inline_order_other_fns :
    nth? ordQ1.fns 1 ≠ nth? ordP.fns 1 ∧ nth? ordQ2.fns 1 = nth? ordP.fns 1 := by
  decide

/-! ## Focused statements for the capability-subset and link-rule questions -/

/-- **The subset guard cannot be dropped: an inlined `needCap` faults in a host lacking the
capability.** In `needP` the callee `needG` holds and uses capability `3` and the host `capF []`
holds none. Every hypothesis of
`inline_behEquiv_retTemp_of_capsSubset_capLegal_abiInsensitive` and of
`inline_behEquiv_retTemp_of_capsSubset_capLegal_abiAgree` other than `CapsSubset G F` holds
(temp mode, `t = 1`), and `CapsSubset` fails. The original program emits `out 1` and returns;
the inlined program, in either return mode, executes `needCap 3` in the host and ends in
`capFault`; so neither inlined program is behaviourally equivalent to the original. -/
theorem capsSubset_needed_inlined_needCap_faults :
    (IsCallSite needP 0 0 (capF []) plainCi needG ∧ LocalsBounded (capF []) ∧
      LocalsBounded needG ∧ BlocksBounded (capF []) ∧ ScopesWF (capF []) ∧ ScopesWF needG ∧
      SlotsFresh (InlineCfg.canonical 1) (capF []) needG ∧
      SlotsInjective (InlineCfg.canonical 1) needG ∧
      (InlineCfg.canonical 1).ret = .temp 1 ∧ TempFresh 1 (InlineCfg.canonical 1) (capF []) needG ∧
      (InlineCfg.canonical 1).redirectContinue = true ∧
      (InlineCfg.canonical 1).resumeMap = .unwind ∧ (InlineCfg.canonical 1).link = .rustc ∧
      CapLegal needG ∧ AbiInsensitive needG ∧ plainCi.abiSensitive = false ∧
      AbiAgree needP (capF []) needG ∧ ¬ CapsSubset needG (capF [])) ∧
    run needP 30 (init needP e0) = ⟨[.out 1], some (.returned 0)⟩ ∧
    run (inline needP 0 0 (InlineCfg.canonical 1)) 40
        (init (inline needP 0 0 (InlineCfg.canonical 1)) e0) = ⟨[], some .capFault⟩ ∧
    run (inline needP 0 0 (InlineCfg.canonical 1).withDest) 40
        (init (inline needP 0 0 (InlineCfg.canonical 1).withDest) e0) = ⟨[], some .capFault⟩ ∧
    ¬ BehEquiv needP (inline needP 0 0 (InlineCfg.canonical 1)) ∧
    ¬ BehEquiv needP (inline needP 0 0 (InlineCfg.canonical 1).withDest) :=
  ⟨by decide, by decide, by decide, by decide,
   fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide)
     (by decide) (h e0),
   fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide)
     (by decide) (h e0)⟩

/-- **The `ignoreParent` link rule breaks two-level inlining.** In `linkP1` the host `linkF1`
already contains the inlined body of the tracked `linkG` (called from the untracked host with
span `10`); its block `3` holds the copied call `linkCi1` to the tracked `linkK`, issued from a
nested, non-inlined scope of the inlined callee with span `20`. With `linkCfg` (the canonical
configuration for `2` host locals except `link = .ignoreParent`), every hypothesis of
`inline_behEquiv_retTemp_of_capsEq` other than `hlink` holds (`t = 2`), and `CleanupClosed` and
`DestNotReadInCleanup` hold for the host. The original program reports location `10`; the
inlined program, in either return mode, reports `20`. -/
theorem linkRule_ignoreParent_changes_location :
    (IsCallSite linkP1 0 3 linkF1 linkCi1 linkK ∧ LocalsBounded linkF1 ∧ LocalsBounded linkK ∧
      BlocksBounded linkF1 ∧ ScopesWF linkF1 ∧ ScopesWF linkK ∧
      SlotsFresh linkCfg linkF1 linkK ∧ SlotsInjective linkCfg linkK ∧
      linkCfg.ret = .temp 2 ∧ TempFresh 2 linkCfg linkF1 linkK ∧
      linkCfg.redirectContinue = true ∧ linkCfg.resumeMap = .unwind ∧
      linkF1.caps = linkK.caps ∧ CleanupClosed linkF1 ∧ DestNotReadInCleanup linkF1 linkCi1.dest ∧
      linkCfg.link = .ignoreParent) ∧
    run linkP1 40 (init linkP1 e0) = ⟨[.loc 10], some (.returned 0)⟩ ∧
    run (inline linkP1 0 3 linkCfg) 60 (init (inline linkP1 0 3 linkCfg) e0) =
      ⟨[.loc 20], some (.returned 0)⟩ ∧
    run (inline linkP1 0 3 linkCfg.withDest) 60 (init (inline linkP1 0 3 linkCfg.withDest) e0) =
      ⟨[.loc 20], some (.returned 0)⟩ ∧
    ¬ BehEquiv linkP1 (inline linkP1 0 3 linkCfg) ∧
    ¬ BehEquiv linkP1 (inline linkP1 0 3 linkCfg.withDest) :=
  ⟨by decide, by decide, by decide, by decide,
   fun h => not_behEquivAtWith_of_halted_ne (n := 40) (m := 60) (by decide) (by decide)
     (by decide) (h e0),
   fun h => not_behEquivAtWith_of_halted_ne (n := 40) (m := 60) (by decide) (by decide)
     (by decide) (h e0)⟩

/-! ## Conjunct-level tightness of bundled hypotheses -/

/-- `cex_tempFresh` breaks the slot-disjointness conjunct of `TempFresh`; its other conjunct
(`F.nlocals ≤ t`) holds there. -/
theorem cex_tempFresh_breaks_slot_conjunct :
    tempF.nlocals ≤ 2 ∧ ¬ (∀ i, i < tempG.nlocals → 1 ≤ i → tempCfg.slot i ≠ 2) := by
  decide

/-- Caller with a local `1` live across the call, and a callee with no arguments that writes its
return place. -/
def tfF : Fn := mkFn 2 [blk [.assign 1 (.use (.const 5))]
  (mkCall 1 [] 0 (some 1) .continue), blk [.emit (.var 1)] .ret]
def tfCi : CallInfo := mkCallInfo 1 [] 0 (some 1) .continue
def tfG : Fn := mkFn 1 [blk [.assign 0 (.use (.const 9))] .ret]
def tfP : Program := mkProg [tfF, tfG]
/-- Canonical slots for `2` host locals, but the return temporary is the caller's live local `1`. -/
def tfCfg : InlineCfg := cfgWith 2 (ret := some (.temp 1))

/-- **`F.nlocals ≤ t` (the first conjunct of `TempFresh`) is tight on its own.** The return
temporary `1` is a live caller local; the callee's write to its return place clobbers it. Every
temp-mode hypothesis of the three temp-mode inlining theorems holds except the first conjunct
of `TempFresh` (its slot-disjointness conjunct holds), and the conclusion fails. -/
theorem cex_tempFresh_callerLocal :
    (IsCallSite tfP 0 0 tfF tfCi tfG ∧ LocalsBounded tfF ∧ LocalsBounded tfG ∧
      BlocksBounded tfF ∧ ScopesWF tfF ∧ ScopesWF tfG ∧
      SlotsFresh tfCfg tfF tfG ∧ SlotsInjective tfCfg tfG ∧ tfCfg.ret = .temp 1 ∧
      ¬ (tfF.nlocals ≤ 1) ∧ (∀ i, i < tfG.nlocals → 1 ≤ i → tfCfg.slot i ≠ 1) ∧
      ¬ TempFresh 1 tfCfg tfF tfG ∧
      tfCfg.redirectContinue = true ∧ tfCfg.resumeMap = .unwind ∧ tfCfg.link = .rustc ∧
      tfF.caps = tfG.caps ∧ CapsSubset tfG tfF ∧ CapLegal tfG ∧ AbiInsensitive tfG ∧
      tfCi.abiSensitive = false ∧ AbiAgree tfP tfF tfG) ∧
    ¬ BehEquiv tfP (inline tfP 0 0 tfCfg) :=
  ⟨by decide, fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide)
     (by decide) (by decide) (h e0)⟩

/-- `cex_scopesWFF` and `cex_scopesWFG` break the `ScopeRefsBounded` conjunct of `ScopesWF`;
the `ScopeTreeWF` conjunct holds in both. -/
theorem cex_scopesWF_breaks_refs_conjunct :
    ScopeTreeWF scFF.scopes ∧ ¬ ScopeRefsBounded scFF ∧
      ScopeTreeWF scGG.scopes ∧ ¬ ScopeRefsBounded scGG := by
  decide

/-- Host calling a tracked callee with span `77`. -/
def rtF : Fn := mkFn 1 [blk [] (mkCall 1 [] 0 (some 1) .continue (span := 77)), blk [] .ret]
/-- A tracked callee whose outermost scope is marked as an inlined scope of the untracked
(missing) function `3`; it reports a caller location from that scope. -/
def rtG : Fn := mkFn 1 [blk [.loc 7 0] .ret] (tc := true) (scopes := [⟨some (3, 50), none⟩])
def rtP : Program := mkProg [rtF, rtG]

/-- **The clean-outermost-scope conjunct of `ScopesWF G` is tight at the program level.** The
callee's outermost scope carries `inlined` (its other conjuncts hold): in the callee's frame the
walk stops there (`loc 7`); after inlining the link rule overwrites that scope with the inlined
tracked callee, and the walk reaches the call span (`loc 77`). -/
theorem cex_scopesWFG_root :
    (IsCallSite rtP 0 0 rtF spanCi rtG ∧
    LocalsBounded rtF ∧
    LocalsBounded rtG ∧
    BlocksBounded rtF ∧
    ScopesWF rtF ∧
    ¬ (ScopesWF rtG) ∧
    ScopeParentsBelow rtG.scopes ∧ ScopeRefsBounded rtG ∧
    SlotsFresh (InlineCfg.canonical 1) rtF rtG ∧
    SlotsInjective (InlineCfg.canonical 1) rtG ∧
    (InlineCfg.canonical 1).ret = .temp 1 ∧
    TempFresh 1 (InlineCfg.canonical 1) rtF rtG ∧
    (InlineCfg.canonical 1).redirectContinue = true ∧
    (InlineCfg.canonical 1).resumeMap = .unwind ∧
    (InlineCfg.canonical 1).link = .rustc ∧
    rtF.caps = rtG.caps ∧
    CapsSubset rtG rtF ∧
    CapLegal rtG ∧
    AbiInsensitive rtG ∧
    spanCi.abiSensitive = false ∧
    AbiAgree rtP rtF rtG ∧
    SlotsFresh (InlineCfg.canonical 1).withDest rtF rtG ∧
    SlotsInjective (InlineCfg.canonical 1).withDest rtG ∧
    (InlineCfg.canonical 1).withDest.ret = .dest ∧
    (InlineCfg.canonical 1).withDest.redirectContinue = true ∧
    (InlineCfg.canonical 1).withDest.resumeMap = .unwind ∧
    (InlineCfg.canonical 1).withDest.link = .rustc ∧
    CleanupClosed rtF ∧
    DestNotReadInCleanup rtF spanCi.dest) ∧
    run rtP 30 (init rtP e0) = ⟨[.loc 7], some (.returned 0)⟩ ∧
    run (inline rtP 0 0 (InlineCfg.canonical 1)) 40
      (init (inline rtP 0 0 (InlineCfg.canonical 1)) e0) = ⟨[.loc 77], some (.returned 0)⟩ ∧
    ¬ BehEquiv rtP (inline rtP 0 0 (InlineCfg.canonical 1)) ∧
    ¬ BehEquiv rtP (inline rtP 0 0 (InlineCfg.canonical 1).withDest) :=
  ⟨by decide, by decide, by decide,
   fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide)
     (by decide) (h e0),
   fun h => not_behEquivAtWith_of_halted_ne (n := 30) (m := 40) (by decide) (by decide)
     (by decide) (h e0)⟩

/-! ## What `inlineFn` preserves for iterated inlining -/

/-- A callee with no locals that panics. -/
def zeroG : Fn := mkFn 0 [blk [] (.panic .continue)]
def zeroF : Fn := mkFn 1 [blk [] (mkCall 1 [] 0 (some 1) .continue), blk [] .ret]
def zeroCi : CallInfo := mkCallInfo 1 [] 0 (some 1) .continue

/-- With a callee that declares no locals and the canonical temporary-mode configuration, the
new body declares the return temporary (`nlocals = 2`) and mentions no undeclared local. -/
theorem inlineFn_nlocals_covers_retTemp :
    LocalsBounded zeroF ∧ LocalsBounded zeroG ∧
      (inlineFn zeroF 0 (blk [] (.call zeroCi)) zeroCi zeroG (InlineCfg.canonical 1)).nlocals = 2 ∧
      LocalsBounded (inlineFn zeroF 0 (blk [] (.call zeroCi)) zeroCi zeroG
        (InlineCfg.canonical 1)) := by
  decide

/-! ### Tightness of `localsBounded_inlineFn` (canonical configuration for one host local) -/

/-- The host mentions an undeclared local (`var 3`), which the call block keeps. -/
theorem cex_localsBoundedInline_F :
    (nth? (mkFn 1 [blk [.emit (.var 3)] (.call zeroCi)]).blocks 0 =
        some (blk [.emit (.var 3)] (.call zeroCi)) ∧
      (blk [.emit (.var 3)] (.call zeroCi)).term = .call zeroCi ∧
      ¬ LocalsBounded (mkFn 1 [blk [.emit (.var 3)] (.call zeroCi)]) ∧
      LocalsBounded (mkFn 1 [blk [] .ret])) ∧
    ¬ LocalsBounded (inlineFn (mkFn 1 [blk [.emit (.var 3)] (.call zeroCi)]) 0
        (blk [.emit (.var 3)] (.call zeroCi)) zeroCi (mkFn 1 [blk [] .ret])
        (InlineCfg.canonical 1)) := by
  decide

/-- The callee mentions an undeclared local (`var 5`), renamed to host local `6`. -/
theorem cex_localsBoundedInline_G :
    (nth? (mkFn 1 [blk [] (.call zeroCi)]).blocks 0 = some (blk [] (.call zeroCi)) ∧
      (blk [] (.call zeroCi)).term = .call zeroCi ∧
      LocalsBounded (mkFn 1 [blk [] (.call zeroCi)]) ∧
      ¬ LocalsBounded (mkFn 1 [blk [.emit (.var 5)] .ret])) ∧
    ¬ LocalsBounded (inlineFn (mkFn 1 [blk [] (.call zeroCi)]) 0 (blk [] (.call zeroCi)) zeroCi
        (mkFn 1 [blk [.emit (.var 5)] .ret]) (InlineCfg.canonical 1)) := by
  decide

/-- Block `0` does not end in the given call, whose destination `7` the return block writes. -/
theorem cex_localsBoundedInline_term :
    (nth? (mkFn 1 [blk [] (.goto 0)]).blocks 0 = some (blk [] (.goto 0)) ∧
      (blk [] (.goto 0)).term ≠ .call (mkCallInfo 1 [] 7 (some 0) .continue) ∧
      LocalsBounded (mkFn 1 [blk [] (.goto 0)]) ∧ LocalsBounded (mkFn 1 [blk [] .ret])) ∧
    ¬ LocalsBounded (inlineFn (mkFn 1 [blk [] (.goto 0)]) 0 (blk [] (.goto 0))
        (mkCallInfo 1 [] 7 (some 0) .continue) (mkFn 1 [blk [] .ret]) (InlineCfg.canonical 1)) := by
  decide

/-- The block passed as `B` is not block `0` of the host, and it mentions `var 9`. -/
theorem cex_localsBoundedInline_B :
    (nth? (mkFn 1 [blk [] (.call zeroCi)]).blocks 0 ≠ some (blk [.emit (.var 9)] (.call zeroCi)) ∧
      (blk [.emit (.var 9)] (.call zeroCi)).term = .call zeroCi ∧
      LocalsBounded (mkFn 1 [blk [] (.call zeroCi)]) ∧ LocalsBounded (mkFn 1 [blk [] .ret])) ∧
    ¬ LocalsBounded (inlineFn (mkFn 1 [blk [] (.call zeroCi)]) 0
        (blk [.emit (.var 9)] (.call zeroCi)) zeroCi (mkFn 1 [blk [] .ret])
        (InlineCfg.canonical 1)) := by
  decide

/-- A callee that jumps to a missing block. -/
def oobG : Fn := mkFn 1 [blk [] (.goto 5)]

/-- `BlocksBounded` is not preserved when the callee jumps out of range (the inlining theorems do
not assume `BlocksBounded G`). -/
theorem cex_blocksBounded_inlineFn_oob :
    BlocksBounded zeroF ∧ ¬ BlocksBounded oobG ∧
      ¬ BlocksBounded (inlineFn zeroF 0 (blk [] (.call zeroCi)) zeroCi oobG
        (InlineCfg.canonical 1)) := by
  decide

/-! ## Non-reflexive behavioural equivalences -/

def pGotoUnr : Program := mkProg [mkFn 1 [blk [] (.goto 1), blk [] .unreachable]]

/-- A program whose entry function is missing and a program whose entry is `unreachable` are
behaviourally equivalent from every entry (both end in `ub` with no events). -/
theorem behEquiv_pMissing_pUnr : BehEquiv pMissing pUnr := by
  intro ⟨fn, args, loc⟩
  cases fn with
  | zero => exact behEquivAtWith_of_halted_eq (n := 0) (m := 1) (by rfl) (by rfl)
  | succ k => exact behEquivAtWith_of_halted_eq (n := 0) (m := 0) (by rfl) (by rfl)

/-- A silent `goto` does not change behaviour. -/
theorem behEquiv_pUnr_pGotoUnr : BehEquiv pUnr pGotoUnr := by
  intro ⟨fn, args, loc⟩
  cases fn with
  | zero => exact behEquivAtWith_of_halted_eq (n := 1) (m := 2) (by rfl) (by rfl)
  | succ k => exact behEquivAtWith_of_halted_eq (n := 0) (m := 0) (by rfl) (by rfl)

end Toy.Inline
