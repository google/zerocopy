import ToyCoalesce.CexUpgrade

/-!
# Counterexamples, positive controls and non-vacuity: coalescing, staging, transfer
-/

namespace Toy.Coalesce

/-- Refinement from a family of target traces matched by source runs. -/
theorem refines_of_param_trace {semT semS : Sem} {T S : Prog} (f : Nat → List Event)
    (g : Layout → Nat) (hT : ∀ A, outcome semT T A = .done (f (g A)) ∨ outcome semT T A = .badLayout)
    (hS : ∀ a, ∃ A, outcome semS S A = .done (f a)) : Refines semT T semS S := by
  intro o ⟨A, hA, hb⟩
  rcases hT A with h | h <;> rw [h] at hA
  · subst hA
    obtain ⟨A1, h1⟩ := hS (g A)
    exact Or.inr ⟨A1, h1, by simp⟩
  · exact absurd hA.symm hb

/-- The postcondition "no pointer comparison returned `true`" (it mentions comparison results). -/
def cmpAllFalse (t : List Event) : Prop := t.all (fun e => e != .cmp true) = true

instance : DecidablePred cmpAllFalse := fun t => by unfold cmpAllFalse; infer_instance

/-- If every non-excluded run of `S` completes with a trace satisfying `Q`, and `T` has a run that
completes with a trace violating `Q`, then `T` does not refine `S`. -/
theorem not_refines_of_pred {semT semS : Sem} {T S : Prog} (A' : Layout) (Q : List Event → Prop)
    (hS : ∀ A, (∃ t, outcome semS S A = .done t ∧ Q t) ∨ outcome semS S A = .badLayout)
    (t' : List Event) (hT : outcome semT T A' = .done t') (hQ : ¬ Q t') :
    ¬ Refines semT T semS S := by
  intro h
  rcases h (outcome semT T A') ⟨A', rfl, by rw [hT]; simp⟩ with ⟨A, hA, _⟩ | ⟨A, hA, hb⟩
  · rcases hS A with ⟨t, h1, _⟩ | h1 <;> rw [h1] at hA <;> cases hA
  · rcases hS A with ⟨t, h1, hq⟩ | h1 <;> rw [h1] at hA
    · rw [hT] at hA; cases hA; exact hQ hq
    · exact hb hA.symm

/-! ## Source and target runs -/

theorem p3_outcome (ms : MoveSem) (A : Layout) :
    outcome ⟨ms, .atomic⟩ p3 A = .done [.vals [.int 7], .cmp false, .vals [.int 9, .int 5]] ∨
      outcome ⟨ms, .atomic⟩ p3 A = .badLayout := by
  cases ms <;> simp only [p3] <;> run_eval

theorem pClobber_outcome (ms : MoveSem) (A : Layout) :
    outcome ⟨ms, .atomic⟩ pClobber A = .done [.vals [.int 7], .vals [.int 9, .int 5]] ∨
      outcome ⟨ms, .atomic⟩ pClobber A = .badLayout := by
  cases ms <;> simp only [pClobber] <;> run_eval

theorem pChain_outcome (ms : MoveSem) (A : Layout) :
    outcome ⟨ms, .atomic⟩ pChain A = .done [.vals [.int 4], .cmp false,
      .vals [.int 1, .int 2, .int 3], .vals [.int 5, .int 6], .vals [.addr (A 1)]] ∨
      outcome ⟨ms, .atomic⟩ pChain A = .badLayout := by
  cases ms <;> simp only [pChain] <;> run_eval

theorem pSib_outcome (ms : MoveSem) (A : Layout) :
    outcome ⟨ms, .atomic⟩ pSib A = .done [.vals [.int 1], .vals [.int 2], .cmp false,
      .vals [.int 3], .vals [.addr (A 2)]] ∨ outcome ⟨ms, .atomic⟩ pSib A = .badLayout := by
  cases ms <;> simp only [pSib] <;> run_eval

theorem pPrecise_outcome (ms : MoveSem) (A : Layout) :
    outcome ⟨ms, .atomic⟩ pPrecise A = .done [.vals [.int 1], .vals [.int 2], .cmp false] ∨
      outcome ⟨ms, .atomic⟩ pPrecise A = .badLayout := by
  cases ms <;> simp only [pPrecise] <;> run_eval

theorem pSwap_outcome (sem : Sem) (A : Layout) :
    outcome sem pSwap A = .done [.vals [.int 2, .int 1]] ∨ outcome sem pSwap A = .badLayout := by
  rcases sem with ⟨ms, am⟩
  cases ms <;> cases am <;> simp only [pSwap] <;> run_eval

/-- A program whose every run reaches `t` or is excluded has the same no-UB property for all
layouts. -/
theorem not_ub_of_outcome {sem : Sem} {P : Prog} {t : List Event}
    (h : ∀ A, outcome sem P A = .done t ∨ outcome sem P A = .badLayout) (A : Layout) :
    outcome sem P A ≠ .ub := by
  rcases h A with h1 | h1 <;> rw [h1] <;> simp

/-! ## Single merges -/

/-- Tightness of the lexical address condition in canonical form (`p3`, merge `x ↦ y.0`, under every `move` semantics):
the forest is well formed and `NoValueClobberStmt` holds; the lexical address condition fails (`x` and `y` are both address-taken and
allocated together); the source comparison `ptrInRange(&x, &y, 2)` is `false` on every
non-excluded layout while the coalesced one is `true` on `A0`; so the coalesced program does not
refine the source. -/
theorem cex_coalesce_single_addrTaken_lexOverlap (ms : MoveSem) :
    ForestWF p3 (single 0 1 0) ∧ NoValueClobberStmt ms (single 0 1 0) p3 ∧
    AddrTaken p3 0 ∧ AddrTaken p3 1 ∧ LexOverlap p3 0 1 ∧
    outcome ⟨ms, .atomic⟩ (coalesce (single 0 1 0) p3) A0 =
      .done [.vals [.int 7], .cmp true, .vals [.int 9, .int 5]] ∧
    ¬ Refines ⟨ms, .atomic⟩ (coalesce (single 0 1 0) p3) ⟨ms, .atomic⟩ p3 := by
  refine ⟨by decide, ?_, by decide, by decide, by decide, ?_, ?_⟩
  · intro A _ _; cases ms <;> simp only [p3] <;> log_eval
  · cases ms <;> decide
  · refine not_refines_of_witness A0 _ (p3_outcome ms) ?_ ?_ <;> cases ms <;> decide

/-- Positive control showing that the one-sided address condition "if `x` is address-taken,
then `x` and `y` are never allocated during a common tick" is not necessary: in `p3x` `x` is
address-taken, `y` is not, and `x` and `y` are allocated together, yet with `NoValueClobberStmt` the merge `x ↦ y.0` is a
refinement (under every `move` semantics). -/
theorem coalesce_single_refines_addrTaken_child_only (ms : MoveSem) :
    ForestWF p3x (single 0 1 0) ∧ NoValueClobberStmt ms (single 0 1 0) p3x ∧
    AddrTaken p3x 0 ∧ ¬ AddrTaken p3x 1 ∧ LexOverlap p3x 0 1 ∧
    Refines ⟨ms, .atomic⟩ (coalesce (single 0 1 0) p3x) ⟨ms, .atomic⟩ p3x := by
  refine ⟨by decide, ?_, by decide, by decide, by decide, ?_⟩
  · intro A _ _; cases ms <;> simp only [p3x] <;> log_eval
  · refine refines_of_param_trace
      (fun a => [.vals [.int 7], .vals [.addr a], .vals [.int 9, .int 5]]) (fun A => A 1) ?_ ?_
    · intro A; cases ms <;> simp only [p3x] <;> coalesce_simp <;> run_eval
    · intro a
      refine ⟨fun z => if z = 0 then a else a + 1, ?_⟩
      cases ms <;> simp only [p3x] <;> run_eval

/-- Tightness of `NoValueClobberStmt` in canonical form (`pClobber`, merge `x ↦ y.0`, no address observation, under
every `move` semantics): the forest is well formed, the lexical address condition holds vacuously, `NoValueClobberStmt` fails on `A0`, and the
coalesced program does not refine the source (it prints `9` for `x`). -/
theorem cex_coalesce_single_valueClobber (ms : MoveSem) :
    ForestWF pClobber (single 0 1 0) ∧
    (AddrTaken pClobber 0 → AddrTaken pClobber 1 → ¬ LexOverlap pClobber 0 1) ∧
    ClassAddrDisjoint pClobber (single 0 1 0) ∧
    ¬ NoValueClobberStmt ms (single 0 1 0) pClobber ∧
    ¬ Refines ⟨ms, .atomic⟩ (coalesce (single 0 1 0) pClobber) ⟨ms, .atomic⟩ pClobber := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · intro h
    have h0 := h A0 (by cases ms <;> decide) (by cases ms <;> decide)
    revert h0; cases ms <;> decide
  · refine not_refines_of_witness A0 _ (pClobber_outcome ms) ?_ ?_ <;> cases ms <;> decide

/-! ## Merge forests -/

/-- Merge edges checked independently against the original program do not compose (`pChain`,
forest `x ↦ y.1`, `y ↦ z.1`): each edge, as a single merge, satisfies `NoValueClobberStmt` and
the per-edge address condition, and the forest satisfies `NoValueClobberStmt` and the per-edge
check; but `x` and its final root `z` are both address-taken and allocated together, the
root-level check fails, and the coalesced program does not refine the source. -/
theorem cex_edgeAddrCheck_does_not_compose (ms : MoveSem) :
    ForestWF pChain μChain ∧ NoValueClobberStmt ms μChain pChain ∧
    NoValueClobberStmt ms (single 0 1 1) pChain ∧ NoValueClobberStmt ms (single 1 2 1) pChain ∧
    EdgeAddrCheck pChain μChain ∧ ¬ ClassAddrDisjoint pChain μChain ∧
    ¬ Refines ⟨ms, .atomic⟩ (coalesce μChain pChain) ⟨ms, .atomic⟩ pChain := by
  refine ⟨by decide, ?_, ?_, ?_, by decide, by decide, ?_⟩
  · intro A _ _; cases ms <;> simp only [pChain] <;> log_eval
  · intro A _ _; cases ms <;> simp only [pChain] <;> log_eval
  · intro A _ _; cases ms <;> simp only [pChain] <;> log_eval
  · refine not_refines_of_pred A0 cmpAllFalse ?_ [.vals [.int 4], .cmp true,
      .vals [.int 1, .int 2, .int 3], .vals [.int 5, .int 6], .vals [.addr 31]]
      (by cases ms <;> decide) (by decide)
    intro A
    rcases pChain_outcome ms A with h1 | h1
    · exact Or.inl ⟨_, h1, by simp [cmpAllFalse]⟩
    · exact Or.inr h1

/-- Checking each merged local against its root local, and each edge, is not enough
(`pSib`, sibling merges `x1 ↦ y.0`, `x2 ↦ y.0`): the per-edge and member-versus-root checks and `NoValueClobberStmt`
hold, but the two siblings are address-taken and allocated together, the root-level check
`ClassAddrDisjoint` fails, and the coalesced program does not refine the source. -/
theorem cex_rootAddrCheck_insufficient_siblings (ms : MoveSem) :
    ForestWF pSib μSib ∧ NoValueClobberStmt ms μSib pSib ∧ EdgeAddrCheck pSib μSib ∧
    RootAddrCheck pSib μSib ∧ ¬ ClassAddrDisjoint pSib μSib ∧
    ¬ Refines ⟨ms, .atomic⟩ (coalesce μSib pSib) ⟨ms, .atomic⟩ pSib := by
  refine ⟨by decide, ?_, by decide, by decide, by decide, ?_⟩
  · intro A _ _; cases ms <;> simp only [pSib] <;> log_eval
  · refine not_refines_of_pred A0 cmpAllFalse ?_ [.vals [.int 1], .vals [.int 2], .cmp true,
      .vals [.int 3], .vals [.addr 30]] (by cases ms <;> decide) (by decide)
    intro A
    rcases pSib_outcome ms A with h1 | h1
    · exact Or.inl ⟨_, h1, by simp [cmpAllFalse]⟩
    · exact Or.inr h1

/-- The union–find check on the concrete forests: it rejects `pChain`/`μChain` and `pSib`/`μSib`
and accepts `pChainOk`/`μChain`. -/
theorem ufCheck_examples :
    ufCheck pChain μChain = false ∧ ufCheck pSib μSib = false ∧ ufCheck pChainOk μChain = true :=
  by decide

/-- Non-vacuity for the forest theorem (`pChainOk`, forest `x ↦ y.1`, `y ↦ z.1`). -/
theorem nonvacuous_coalesce_refines_of_noValueClobber_of_classAddrDisjoint (ms : MoveSem) :
    ForestWF pChainOk μChain ∧ NoValueClobberStmt ms μChain pChainOk ∧
    ClassAddrDisjoint pChainOk μChain := by
  refine ⟨by decide, ?_, by decide⟩
  intro A _ _; cases ms <;> simp only [pChainOk] <;> log_eval

/-- Non-vacuity for the single-merge theorem (`p3x`, merge `x ↦ y.0`). -/
theorem nonvacuous_coalesce_single (ms : MoveSem) :
    ForestWF p3x (single 0 1 0) ∧ NoValueClobberStmt ms (single 0 1 0) p3x ∧
    (AddrTaken p3x 0 → AddrTaken p3x 1 → ¬ LexOverlap p3x 0 1) := by
  refine ⟨by decide, ?_, by decide⟩
  intro A _ _; cases ms <;> simp only [p3x] <;> log_eval

/-! ## Lifetime policies -/

/-- The precise-everywhere policy check passes on `pPrecise` for the merge `y ↦ x.0`, `NoValueClobberStmt` holds,
lexical intervals overlap, and the coalesced program does not refine the source. -/
theorem cex_policy_precise_for_addrTaken (ms : MoveSem) :
    ForestWF pPrecise (single 1 0 0) ∧ NoValueClobberStmt ms (single 1 0 0) pPrecise ∧
    PolicyCheck (fun _ => .precise) pPrecise (single 1 0 0) ∧ LexOverlap pPrecise 0 1 ∧
    ¬ Refines ⟨ms, .atomic⟩ (coalesce (single 1 0 0) pPrecise) ⟨ms, .atomic⟩ pPrecise := by
  refine ⟨by decide, ?_, by decide, by decide, ?_⟩
  · intro A _ _; cases ms <;> simp only [pPrecise] <;> log_eval
  · refine not_refines_of_witness A0 _ (pPrecise_outcome ms) ?_ ?_ <;> cases ms <;> decide

/-- Necessity: a policy that uses precise liveness for address-taken locals is not sound. -/
theorem not_policySound_of_precise_for_addrTaken (pol : Policy) (h : pol true = .precise) :
    ¬ PolicySound pol := by
  intro hs
  have hpc : PolicyCheck pol pPrecise (single 1 0 0) := by
    have h0 : decide (AddrTaken pPrecise 0) = true := by decide
    have h1 : decide (AddrTaken pPrecise 1) = true := by decide
    intro u hu v hv hne _ _
    have hu' : u = 0 ∨ u = 1 := by simp [Prog.nloc, pPrecise] at hu; omega
    have hv' : v = 0 ∨ v = 1 := by simp [Prog.nloc, pPrecise] at hv; omega
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
    · exact absurd rfl hne
    · rw [h0, h1, h]; decide
    · rw [h0, h1, h]; decide
    · exact absurd rfl hne
  exact (cex_policy_precise_for_addrTaken .deinit).2.2.2.2
    (hs .deinit pPrecise (single 1 0 0) (by decide) hpc)

/-- A uniform policy (over the two notions of `Notion`) is sound iff it uses lexical intervals
for address-taken locals. -/
theorem policySound_iff (pol : Policy) : PolicySound pol ↔ pol true = .lexical := by
  constructor
  · intro hs
    cases hpt : pol true with
    | lexical => rfl
    | precise => exact absurd hs (not_policySound_of_precise_for_addrTaken pol hpt)
  · exact policySound_of_lexical_for_addrTaken pol

/-- Positive control and non-vacuity: the mixed policy (lexical for address-taken locals,
precise otherwise) accepts the merge `y ↦ x.0` on `pPreciseOk`, which the lexical-everywhere
policy rejects, and that merge is a refinement. -/
theorem policy_mixed_accepts_pPreciseOk (ms : MoveSem) :
    ForestWF pPreciseOk (single 1 0 0) ∧
    PolicyCheck (fun b => if b then .lexical else .precise) pPreciseOk (single 1 0 0) ∧
    ¬ PolicyCheck (fun _ => .lexical) pPreciseOk (single 1 0 0) ∧
    Refines ⟨ms, .atomic⟩ (coalesce (single 1 0 0) pPreciseOk) ⟨ms, .atomic⟩ pPreciseOk := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  refine refines_of_single_trace [.vals [.int 1], .vals [.int 2]] A0 ?_ (by cases ms <;> decide)
  intro A; cases ms <;> simp only [pPreciseOk] <;> coalesce_simp <;> run_eval

/-! ## Overlap staging -/

/-- Coalescing creates an assignment that needs staging, and without staging the result is not a
refinement under in-order field writes (`pSwap`, merge `y' ↦ y.0`, under every `move` semantics):
the forest is well formed, `NoValueClobberStmt` and the root-level check hold, the source needs no staging, the
coalesced program contains `y := (y.1, y.0)`, it prints `(2, 2)` instead of `(2, 1)`; under atomic
assignment it is a refinement (positive control). -/
theorem cex_coalesce_without_staging_inOrder (ms : MoveSem) :
    ForestWF pSwap (single 1 0 0) ∧ NoValueClobberStmt ms (single 1 0 0) pSwap ∧
    ClassAddrDisjoint pSwap (single 1 0 0) ∧ NoStagingNeeded pSwap ∧
    ¬ NoStagingNeeded (coalesce (single 1 0 0) pSwap) ∧
    ¬ Refines ⟨ms, .inOrder⟩ (coalesce (single 1 0 0) pSwap) ⟨ms, .inOrder⟩ pSwap ∧
    Refines ⟨ms, .atomic⟩ (coalesce (single 1 0 0) pSwap) ⟨ms, .atomic⟩ pSwap := by
  refine ⟨by decide, ?_, by decide, by decide, by decide, ?_, ?_⟩
  · intro A _ _; cases ms <;> simp only [pSwap] <;> log_eval
  · refine not_refines_of_witness A0 _ (pSwap_outcome _) ?_ ?_ <;> cases ms <;> decide
  · refine refines_of_single_trace [.vals [.int 2, .int 1]] A0 ?_ (by cases ms <;> decide)
    intro A; cases ms <;> simp only [pSwap] <;> coalesce_simp <;> run_eval

/-- The staged pipeline on `pSwap`: the hypotheses of `stage_coalesce_refines_inOrder` hold and
the staged coalesced program refines the source under in-order field writes. -/
theorem stage_coalesce_pSwap (ms : MoveSem) :
    ForestWF pSwap (single 1 0 0) ∧ NoValueClobberStmt ms (single 1 0 0) pSwap ∧
    ClassAddrDisjoint pSwap (single 1 0 0) ∧ NoStagingNeeded pSwap ∧
    CalleesNoStaging (coalesce (single 1 0 0) pSwap) ∧ ParamsInRange pSwap ∧
    Refines ⟨ms, .inOrder⟩ (stage (coalesce (single 1 0 0) pSwap)) ⟨ms, .inOrder⟩ pSwap := by
  refine ⟨by decide, (cex_coalesce_without_staging_inOrder ms).2.1, by decide, by decide,
    by decide, by decide, ?_⟩
  refine refines_of_single_trace [.vals [.int 2, .int 1]] A0 ?_ (by cases ms <;> decide)
  intro A; cases ms <;> simp only [pSwap] <;> coalesce_simp <;> run_eval

/-- The staged program of the pipeline on `pSwap`. -/
def pSwapStaged : Prog := stage (coalesce (single 1 0 0) pSwap)

theorem pSwapStaged_outcome (ms : MoveSem) (A : Layout) :
    outcome ⟨ms, .inOrder⟩ pSwapStaged A = .done [.vals [.int 2, .int 1]] ∨
      outcome ⟨ms, .inOrder⟩ pSwapStaged A = .badLayout := by
  cases ms <;> simp only [pSwapStaged, pSwap] <;> coalesce_simp <;> run_eval

/-- The fixpoint pitfall: re-running the coalescer on the staged program merges the staging
temporary (local 2) back into `y` (merge `tmp ↦ y.0`): the forest is well formed, `NoValueClobberStmt` and the
root-level check hold on the staged program, the staged program needs no staging, the re-coalesced
program again contains `y := (y.1, y.0)` and does not refine the staged program under in-order
field writes. -/
theorem cex_recoalesce_staging_temp (ms : MoveSem) :
    ForestWF pSwapStaged (single 2 0 0) ∧ NoValueClobberStmt ms (single 2 0 0) pSwapStaged ∧
    ClassAddrDisjoint pSwapStaged (single 2 0 0) ∧ NoStagingNeeded pSwapStaged ∧
    ¬ NoStagingNeeded (coalesce (single 2 0 0) pSwapStaged) ∧
    ¬ Refines ⟨ms, .inOrder⟩ (coalesce (single 2 0 0) pSwapStaged) ⟨ms, .inOrder⟩ pSwapStaged := by
  refine ⟨by decide, ?_, by decide, by decide, by decide, ?_⟩
  · intro A _ _; cases ms <;> simp only [pSwapStaged, pSwap] <;> coalesce_simp <;> log_eval
  · refine not_refines_of_witness A0 _ (pSwapStaged_outcome ms) ?_ ?_ <;> cases ms <;> decide

/-! ## Verification-condition transfer -/

/-- Address-mentioning postconditions need the root-level check: on `p3` (merge `x ↦ y.0`),
`NoValueClobberStmt` holds, the root-level check fails, the source satisfies `cmpAllFalse` on every run, and the coalesced
program does not. -/
theorem cex_vc_forward_addrPost_needs_classAddrDisjoint :
    ForestWF p3 (single 0 1 0) ∧ NoValueClobberStmt .deinit (single 0 1 0) p3 ∧
    ¬ ClassAddrDisjoint p3 (single 0 1 0) ∧ ¬ AddrFree cmpAllFalse ∧ Valid semD p3 cmpAllFalse ∧
    ¬ Valid semD (coalesce (single 0 1 0) p3) cmpAllFalse := by
  refine ⟨by decide, (cex_coalesce_single_addrTaken_lexOverlap .deinit).2.1, by decide, ?_, ?_, ?_⟩
  · intro h
    have := (h [.cmp true] [.cmp false] rfl).2 (by decide)
    revert this; decide
  · intro o ⟨A, hA, hb⟩
    rcases p3_outcome .deinit A with h | h <;> rw [h] at hA
    · exact ⟨_, hA.symm, by decide⟩
    · exact absurd hA.symm hb
  · intro hv
    obtain ⟨t, ht, hp⟩ := hv _ ⟨A0, rfl, by decide⟩
    have : t = [.vals [.int 7], .cmp true, .vals [.int 9, .int 5]] := by
      have h2 : outcome semD (coalesce (single 0 1 0) p3) A0 =
        .done [.vals [.int 7], .cmp true, .vals [.int 9, .int 5]] := by decide
      rw [h2] at ht; cases ht; rfl
    subst this; revert hp; decide

/-- Under the precise-everywhere policy the same failure occurs (`pPrecise`, merge `y ↦ x.0`):
the forest is well formed, `NoValueClobberStmt` holds, the root-level check fails although the
precise-everywhere policy check passes, the source satisfies `cmpAllFalse` and the coalesced
program does not. -/
theorem cex_vc_forward_addrPost_precisePolicy :
    ForestWF pPrecise (single 1 0 0) ∧ NoValueClobberStmt .deinit (single 1 0 0) pPrecise ∧
    ¬ ClassAddrDisjoint pPrecise (single 1 0 0) ∧
    PolicyCheck (fun _ => .precise) pPrecise (single 1 0 0) ∧
    Valid semD pPrecise cmpAllFalse ∧ ¬ Valid semD (coalesce (single 1 0 0) pPrecise) cmpAllFalse := by
  refine ⟨by decide, (cex_policy_precise_for_addrTaken .deinit).2.1, by decide, by decide, ?_, ?_⟩
  · intro o ⟨A, hA, hb⟩
    rcases pPrecise_outcome .deinit A with h | h <;> rw [h] at hA
    · exact ⟨_, hA.symm, by decide⟩
    · exact absurd hA.symm hb
  · intro hv
    obtain ⟨t, ht, hp⟩ := hv _ ⟨A0, rfl, by decide⟩
    have h2 : outcome semD (coalesce (single 1 0 0) pPrecise) A0 =
      .done [.vals [.int 1], .vals [.int 2], .cmp true] := by decide
    rw [h2] at ht; cases ht; revert hp; decide

/-- An address-free postcondition: the erased trace equals a fixed list. -/
def erasedIs (t0 : List Event) (t : List Event) : Prop := t.map Event.erase = t0

instance (t0 : List Event) : DecidablePred (erasedIs t0) := fun t => by
  unfold erasedIs; infer_instance

theorem erasedIs_addrFree (t0 : List Event) : AddrFree (erasedIs t0) := by
  intro t t' h
  simp [erasedIs, h]

/-- Address-free transfer needs `NoValueClobberStmt`: on `pClobber` (merge `x ↦ y.0`, no address observation) the
source satisfies the address-free postcondition "the erased trace is `[7], [9, 5]`" and the
coalesced program does not. -/
theorem cex_vc_forward_addrFree_needs_noValueClobber :
    ForestWF pClobber (single 0 1 0) ∧ ¬ NoValueClobberStmt .deinit (single 0 1 0) pClobber ∧
    AddrFree (erasedIs [.vals [.int 7], .vals [.int 9, .int 5]]) ∧
    Valid semD pClobber (erasedIs [.vals [.int 7], .vals [.int 9, .int 5]]) ∧
    ¬ Valid semD (coalesce (single 0 1 0) pClobber) (erasedIs [.vals [.int 7], .vals [.int 9, .int 5]]) := by
  refine ⟨by decide, (cex_coalesce_single_valueClobber .deinit).2.2.2.1, erasedIs_addrFree _, ?_, ?_⟩
  · intro o ⟨A, hA, hb⟩
    rcases pClobber_outcome .deinit A with h | h <;> rw [h] at hA
    · exact ⟨_, hA.symm, by decide⟩
    · exact absurd hA.symm hb
  · intro hv
    obtain ⟨t, ht, hp⟩ := hv _ ⟨A0, rfl, by decide⟩
    have h2 : outcome semD (coalesce (single 0 1 0) pClobber) A0 =
      .done [.vals [.int 9], .vals [.int 9, .int 5]] := by decide
    rw [h2] at ht; cases ht; revert hp; decide

theorem pUBRemoved_outcome (A : Layout) :
    outcome semD pUBRemoved A = .ub ∨ outcome semD pUBRemoved A = .badLayout := by
  simp only [pUBRemoved]; run_eval

/-- Backward transfer needs the source to be free of undefined behaviour (`pUBRemoved`, merge
`x ↦ y.0`): `NoValueClobberStmt` holds (vacuously: every source run is undefined or excluded), the coalesced program
satisfies the address-free postcondition "the erased trace is `[5]`", the source does not. -/
theorem cex_vc_backward_needs_ubFree :
    ForestWF pUBRemoved (single 0 1 0) ∧ NoValueClobberStmt .deinit (single 0 1 0) pUBRemoved ∧
    AddrFree (erasedIs [.vals [.int 5]]) ∧ ¬ UBFree semD pUBRemoved ∧
    Valid semD (coalesce (single 0 1 0) pUBRemoved) (erasedIs [.vals [.int 5]]) ∧
    ¬ Valid semD pUBRemoved (erasedIs [.vals [.int 5]]) := by
  refine ⟨by decide, ?_, erasedIs_addrFree _, ?_, ?_, ?_⟩
  · intro A hub hbad
    rcases pUBRemoved_outcome A with h | h
    · exact absurd h hub
    · exact absurd h hbad
  · intro h; exact h ⟨A0, by decide, by decide⟩
  · refine fun o ⟨A, hA, hb⟩ => ?_
    have hT : outcome semD (coalesce (single 0 1 0) pUBRemoved) A = .done [.vals [.int 5]] ∨
        outcome semD (coalesce (single 0 1 0) pUBRemoved) A = .badLayout := by
      simp only [pUBRemoved]; coalesce_simp; run_eval
    rcases hT with h | h <;> rw [h] at hA
    · exact ⟨_, hA.symm, by decide⟩
    · exact absurd hA.symm hb
  · intro hv
    obtain ⟨t, ht, _⟩ := hv .ub ⟨A0, by decide, by decide⟩
    cases ht

/-- Positive control for address-free forward transfer without any address condition: on `p3`
(where the root-level check fails) the address-free postcondition "the erased trace is
`[7], [cmp], [9, 5]`" holds for the source and for the coalesced program. -/
theorem vc_forward_addrFree_p3 :
    ForestWF p3 (single 0 1 0) ∧ NoValueClobberStmt .deinit (single 0 1 0) p3 ∧
    ¬ ClassAddrDisjoint p3 (single 0 1 0) ∧
    Valid semD p3 (erasedIs [.vals [.int 7], .cmp false, .vals [.int 9, .int 5]]) ∧
    Valid semD (coalesce (single 0 1 0) p3) (erasedIs [.vals [.int 7], .cmp false, .vals [.int 9, .int 5]]) := by
  refine ⟨by decide, (cex_coalesce_single_addrTaken_lexOverlap .deinit).2.1, by decide, ?_, ?_⟩
  · intro o ⟨A, hA, hb⟩
    rcases p3_outcome .deinit A with h | h <;> rw [h] at hA
    · exact ⟨_, hA.symm, by decide⟩
    · exact absurd hA.symm hb
  · intro o ⟨A, hA, hb⟩
    have hT : outcome semD (coalesce (single 0 1 0) p3) A =
        .done [.vals [.int 7], .cmp true, .vals [.int 9, .int 5]] ∨
        outcome semD (coalesce (single 0 1 0) p3) A = .badLayout := by
      simp only [p3]; coalesce_simp; run_eval
    rcases hT with h | h <;> rw [h] at hA
    · exact ⟨_, hA.symm, by decide⟩
    · exact absurd hA.symm hb

/-- Part of the non-vacuity of backward address-free transfer: `p3x` with the merge `x ↦ y.0` has
`NoValueClobberStmt` and no undefined behaviour (the full witness is `nonvacuous_vc_p3x`). -/
theorem nonvacuous_vc_backward : ForestWF p3x (single 0 1 0) ∧
    NoValueClobberStmt .deinit (single 0 1 0) p3x ∧ UBFree semD p3x ∧
    AddrFree (erasedIs [.vals [.int 7], .vals [.addr 0], .vals [.int 9, .int 5]]) := by
  refine ⟨by decide, (nonvacuous_coalesce_single .deinit).2.1, ?_, erasedIs_addrFree _⟩
  intro ⟨A, hA, _⟩
  have : outcome semD p3x A = .done [.vals [.int 7], .vals [.addr (A 0)], .vals [.int 9, .int 5]] ∨
      outcome semD p3x A = .badLayout := by simp only [p3x]; run_eval
  rcases this with h | h <;> rw [h] at hA <;> cases hA

end Toy.Coalesce
