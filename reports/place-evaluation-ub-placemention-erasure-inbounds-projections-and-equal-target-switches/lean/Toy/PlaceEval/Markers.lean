import Toy.PlaceEval.MarkerEquiv

/-!
# Storage-marker erasure: statements and counterexamples
-/

namespace Toy.PlaceEval

/-! ## Behaviour sets of `pAddrCmp` and `pLive` under fresh addresses -/

/-- `pAddrCmp`, under every oracle: emits `1` if the two allocations of `x` got the same
address and `0` otherwise (or blocks); never UB. -/
theorem pAddrCmp_fresh_beh (ω : Nat → Nat) (b : Beh) (h : HasBehIn (.fresh ω) pAddrCmp b) :
    b = .term [1] ∨ b = .term [0] := by
  have hal : (2 * (ω 0 + 1) + 2) % 2 = 0 := by omega
  by_cases d1 : disjointRanges (ω 1 + 1) 1 (2 * (ω 0 + 1)) 4 = true
  · by_cases d2 : disjointRanges (ω 2 + 1) 1 (2 * (ω 0 + 1)) 4 = true
    · have d2' := d2
      simp only [disjointRanges] at d2'
      simp at d2'
      have h1 : ω 2 + 1 ≠ 2 * (ω 0 + 1) := by omega
      have h2 : ω 2 + 1 ≠ 2 * (ω 0 + 1) + 1 := by omega
      have h3 : 2 * (ω 0 + 1) + 2 + 1 ≠ 2 * (ω 0 + 1) := by omega
      have h4 : 2 * (ω 0 + 1) + 2 + 1 ≠ 2 * (ω 0 + 1) + 1 := by omega
      have h5 : 2 * (ω 0 + 1) + 2 ≠ 2 * (ω 0 + 1) + 1 := by omega
      have h6 : 2 * (ω 0 + 1) + 2 ≠ 2 * (ω 0 + 1) := by omega
      have h7 : ω 2 ≠ 2 * (ω 0 + 1) := by omega
      rw [hasBehIn_iff_toBeh (n := 12)
        (by simp_run [pAddrCmp, d1, d2, h1, h2, h3, h4, h5, h6, h7, hal])] at h
      simp_run [pAddrCmp, d1, d2, h1, h2, h3, h4, h5, h6, h7, hal] at h
      by_cases he : ω 1 = ω 2
      · simp [he] at h; exact Or.inl h.symm
      · simp [he] at h; exact Or.inr h.symm
    · rw [hasBehIn_iff_toBeh (n := 12) (by simp_run [pAddrCmp, d1, d2, hal])] at h
      simp_run [pAddrCmp, d1, d2, hal] at h
  · rw [hasBehIn_iff_toBeh (n := 12) (by simp_run [pAddrCmp, d1, hal])] at h
    simp_run [pAddrCmp, d1, hal] at h

/-- `pAddrCmp` with `x`'s markers erased, under every oracle: emits `1` (or blocks). -/
theorem pAddrCmp_erased_fresh_beh (ω : Nat → Nat) (b : Beh)
    (h : HasBehIn (.fresh ω) (eraseMarkers pAddrCmp 1) b) : b = .term [1] := by
  have hal : (2 * (ω 0 + 1) + 2) % 2 = 0 := by omega
  by_cases d1 : disjointRanges (ω 1 + 1) 1 (2 * (ω 0 + 1)) 4 = true
  · have h3 : 2 * (ω 0 + 1) + 2 + 1 ≠ 2 * (ω 0 + 1) := by omega
    have h4 : 2 * (ω 0 + 1) + 2 + 1 ≠ 2 * (ω 0 + 1) + 1 := by omega
    have h5 : 2 * (ω 0 + 1) + 2 ≠ 2 * (ω 0 + 1) + 1 := by omega
    have h6 : 2 * (ω 0 + 1) + 2 ≠ 2 * (ω 0 + 1) := by omega
    rw [hasBehIn_iff_toBeh (n := 12) (by simp_run [pAddrCmp, d1, h3, h4, h5, h6, hal])] at h
    simp_run [pAddrCmp, d1, h3, h4, h5, h6, hal] at h
    exact h.symm
  · rw [hasBehIn_iff_toBeh (n := 12) (by simp_run [pAddrCmp, d1, hal])] at h
    simp_run [pAddrCmp, d1, hal] at h

theorem pAddrCmp_fresh_term_zero : HasBeh .fresh pAddrCmp (.term [0]) :=
  ⟨fun k => [0, 10, 11].getD k 0, (hasBehIn_iff_toBeh (n := 12) (by decide) _).2 (by rfl)⟩

theorem pAddrCmp_fresh_term_one : HasBeh .fresh pAddrCmp (.term [1]) :=
  ⟨fun k => [0, 10, 10].getD k 0, (hasBehIn_iff_toBeh (n := 12) (by decide) _).2 (by rfl)⟩

/-- `pLive`, under every oracle: emits `5`. -/
theorem pLive_fresh_beh (ω : Nat → Nat) (b : Beh) (h : HasBehIn (.fresh ω) pLive b) :
    b = .term [5] := by
  rw [hasBehIn_iff_toBeh (n := 10) (by simp_run [pLive, u8])] at h
  simp_run [pLive, u8] at h
  exact h.symm

/-- `eraseMarkers pAddrCmp 1` never emits `0` under fresh addresses. -/
theorem hasBeh_ex_neg_erased_addrCmp : ¬ HasBeh .fresh (eraseMarkers pAddrCmp 1) (.term [0]) := by
  rintro ⟨ω, h⟩
  cases pAddrCmp_erased_fresh_beh ω _ h

/-! ## Pointer constants with provenance -/

theorem noProvConst_ex_pos : NoProvConst pStale := by decide
theorem noProvConst_ex_neg : ¬ NoProvConst pConstProvSlots := by decide

/-- **Refuted: marker erasure refines without a condition on pointer constants.** Under the
static slot assignment `SEx`, `pConstProvSlots` emits `5`, while its marker-erased version
reaches UB, so it is not a refinement. -/
theorem refuted_eraseMarkers_refinesPP :
    ¬ ∀ (S : Sem) (P : Prog) (x : Local), RefinesPP S P (eraseMarkers P x) := by
  intro h
  have := h SEx pConstProvSlots 0
  rw [refinesPP_iff_of_beh pConstProvSlots_beh pConstProvSlots_erased_beh] at this
  rcases this with h | ⟨t, h, _⟩ <;> cases h

/-- **Tightness of `NoProvConst` for marker-erasure refinement (static slots).** -/
theorem eraseMarkers_noProvConst_counterexample :
    ¬ RefinesPP SEx pConstProvSlots (eraseMarkers pConstProvSlots 0) := by
  rw [refinesPP_iff_of_beh pConstProvSlots_beh pConstProvSlots_erased_beh]
  rintro (h | ⟨t, h, _⟩) <;> cases h

/-- **Tightness of `NoProvConst` for marker-erasure refinement (fresh addresses).** Every
local of `pConstProvFresh` has alignment `1` and the program is UB-free under fresh
addresses, but its marker-erased version has a UB behaviour that improves no source
behaviour. -/
theorem eraseMarkers_fresh_noProvConst_counterexample :
    (∀ L ∈ pConstProvFresh.locals, 1 ≤ L.align) ∧ UBFree .fresh pConstProvFresh ∧
      ¬ RefinesPP .fresh pConstProvFresh (eraseMarkers pConstProvFresh 0) := by
  refine ⟨pConstProvFresh_alignPos, pConstProvFresh_ubFree, ?_⟩
  intro h
  obtain ⟨bs, ⟨ω, hbs⟩, himp⟩ := h (.wrong []) pConstProvFresh_erased_fresh_wrong
  rcases pConstProvFresh_fresh_beh ω bs hbs with rfl | rfl
  · rcases himp with h | ⟨t, h, _⟩ <;> cases h
  · rcases himp with h | ⟨t, h, _⟩ <;> cases h

/-! ## Erasing markers is a forward refinement -/

/-- **Marker erasure refines (no pointer constant with provenance).** If no operand of `P` is
a pointer constant carrying an allocation identifier (`NoProvConst P`), erasing every
`storageLive x` / `storageDead x` (so that, for `x < P.locals.length`, `x` is allocated at
entry for the whole run) gives a prefix-preserving refinement of `P`, under the fresh-address
semantics and under every static slot assignment, with no condition on `x`'s address or slot
(in particular, `x` may share a slot with another local). -/
theorem eraseMarkers_refinesPP_of_noProvConst (S : Sem) (P : Prog) (x : Local)
    (hnp : NoProvConst P) :
    RefinesPP S P (eraseMarkers P x) := by
  exact eraseMarkers_refinesPP_of_noProvConst_proof S P x hnp

/-- Non-vacuity of `eraseMarkers_refinesPP_of_noProvConst`: `pStale` has no pointer constant
with provenance. -/
theorem eraseMarkers_refinesPP_nonvacuous : NoProvConst pStale := noProvConst_ex_pos

/-- **Refuted: end-to-end refinement with a valid static slot assignment, without a condition
on pointer constants.** `sEx` is valid for `pConstProvFresh` (its slot execution emits `5`, a
fresh behaviour), but the slot execution of the marker-erased program reaches UB. -/
theorem refuted_eraseMarkers_slots_refinesAcross_fresh :
    ¬ ∀ (s : Local → Nat) (P : Prog) (x : Local),
      RefinesAcross .fresh P (.slots s) P → RefinesAcross .fresh P (.slots s) (eraseMarkers P x) := by
  intro h
  have := h sEx pConstProvFresh 0 pConstProvFresh_slots_valid
  obtain ⟨bs, ⟨ω, hbs⟩, himp⟩ := this (.wrong []) ((pConstProvFresh_erased_slots_beh _).2 rfl)
  rcases pConstProvFresh_fresh_beh ω bs hbs with rfl | rfl
  · rcases himp with h | ⟨t, h, _⟩ <;> cases h
  · rcases himp with h | ⟨t, h, _⟩ <;> cases h

/-- **End-to-end refinement with a static slot assignment.** If no operand of `P` is a
pointer constant carrying an allocation identifier, and the slot execution of `P` refines its
fresh-address execution (the slot assignment `s` is valid for `P`), then the slot execution of
the marker-erased program, with the same `s`, refines the fresh-address execution of `P`. -/
theorem eraseMarkers_slots_refinesAcross_fresh_of_noProvConst (s : Local → Nat) (P : Prog)
    (x : Local) (hnp : NoProvConst P) (hvalid : RefinesAcross .fresh P (.slots s) P) :
    RefinesAcross .fresh P (.slots s) (eraseMarkers P x) :=
  refinesAcross_trans hvalid (eraseMarkers_refinesPP_of_noProvConst (.slots s) P x hnp)

/-- Non-vacuity of `eraseMarkers_slots_refinesAcross_fresh_of_noProvConst`: `pLive` has no
pointer constant with provenance and `sEx` is valid for it. -/
theorem eraseMarkers_slots_nonvacuous :
    NoProvConst pLive ∧ RefinesAcross .fresh pLive (.slots sEx) pLive :=
  ⟨by decide, refinesAcross_of_src_beh pLive_fresh_term fun b hb => by
    rw [(pLive_slots_beh b).1 hb]; exact improvesPP_refl _⟩

/-- **Tightness of `NoProvConst` for the end-to-end refinement.** `sEx` is valid for
`pConstProvFresh`, but the end-to-end refinement fails for its marker-erased version. -/
theorem eraseMarkers_slots_noProvConst_counterexample :
    RefinesAcross .fresh pConstProvFresh (.slots sEx) pConstProvFresh ∧
      ¬ RefinesAcross .fresh pConstProvFresh (.slots sEx) (eraseMarkers pConstProvFresh 0) := by
  refine ⟨pConstProvFresh_slots_valid, fun h => ?_⟩
  obtain ⟨bs, ⟨ω, hbs⟩, himp⟩ := h (.wrong []) ((pConstProvFresh_erased_slots_beh _).2 rfl)
  rcases pConstProvFresh_fresh_beh ω bs hbs with rfl | rfl
  · rcases himp with h | ⟨t, h, _⟩ <;> cases h
  · rcases himp with h | ⟨t, h, _⟩ <;> cases h

/-- **A shared slot breaks the slot lowering of the erased program, not the end-to-end
refinement.** In `pShare`, locals `0` and `1` share address `4` under `sShare` and have
disjoint live ranges. Then: the slot execution of `pShare` refines its fresh execution; the
slot execution of the marker-erased program still refines the fresh execution of `pShare`;
but it does not refine the fresh execution of the marker-erased program itself (the write of
`7` to local `1` clobbers local `0`, which emits `7` instead of `5`). Every run of `pShare`
itself has UB; the theorem says nothing about programs without UB. -/
theorem eraseMarkers_sharedSlot_lowering_mismatch :
    sShare 0 = sShare 1 ∧
    RefinesAcross .fresh pShare (.slots sShare) pShare ∧
    RefinesAcross .fresh pShare (.slots sShare) (eraseMarkers pShare 0) ∧
    ¬ RefinesAcross .fresh (eraseMarkers pShare 0) (.slots sShare) (eraseMarkers pShare 0) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact refinesAcross_of_src_beh pShare_fresh_wrong fun b _ => improvesPP_wrong_nil b
  · exact refinesAcross_of_src_beh pShare_fresh_wrong fun b _ => improvesPP_wrong_nil b
  · intro h
    obtain ⟨bs, ⟨ω, hbs⟩, himp⟩ := h (.term [7]) ((pShare_erased_slots_beh _).2 rfl)
    rw [pShare_erased_fresh_beh ω bs hbs] at himp
    exact not_improvesPP_term_term (by decide) himp

/-! ## When erasure is an equivalence -/

/-- **Sufficient condition for equivalence (fresh addresses).** Under fresh addresses, if
every local of `P` has alignment at least `1`, no statement of `P` observes an address (no
`ptrEq`, no `addrOf`), and `P` is UB-free, then erasing the markers of `x` is a
prefix-preserving equivalence (traces and UB-freedom transfer in both directions). -/
theorem eraseMarkers_fresh_equivPP_of_alignPos_of_noAddrObs_of_ubFree (P : Prog) (x : Local)
    (hwf : ∀ L ∈ P.locals, 1 ≤ L.align) (hobs : NoAddrObs P) (hub : UBFree .fresh P) :
    EquivPP .fresh P (eraseMarkers P x) := by
  exact eraseMarkers_fresh_equivPP_proof P x hwf hobs hub

/-- Non-vacuity of `eraseMarkers_fresh_equivPP_of_alignPos_of_noAddrObs_of_ubFree`. -/
theorem noAddrObs_ubFree_pLive :
    (∀ L ∈ pLive.locals, 1 ≤ L.align) ∧ NoAddrObs pLive ∧ UBFree .fresh pLive := by
  refine ⟨by decide, ?_, ?_⟩
  · intro b hb s hs rv hrv
    simp [pLive] at hb
    subst hb
    simp at hs
    rcases hs with rfl | rfl | rfl | rfl <;> simp [Stmt.rvalue?] at hrv <;> subst hrv <;> rfl
  · rintro t ⟨ω, h⟩
    cases pLive_fresh_beh ω _ h

/-- Two one-byte locals of alignment `0` with disjoint live ranges:
`SL 0; SD 0; SL 1; emit 1`. Under fresh addresses every allocation of alignment `0` is at
address `0 * (ω k + 1) = 0`. -/
def pAlignZero : Prog :=
  ⟨[⟨1, 0⟩, ⟨1, 0⟩],
   [⟨[.storageLive 0, .storageDead 0, .storageLive 1, .emit (.use (.const (.int 1)))], .halt⟩]⟩

theorem pAlignZero_fresh_beh (ω : Nat → Nat) (b : Beh) (h : HasBehIn (.fresh ω) pAlignZero b) :
    b = .term [1] := by
  rw [hasBehIn_iff_toBeh (n := 10) (by simp_run [pAlignZero, disjointRanges])] at h
  simp_run [pAlignZero, disjointRanges] at h
  exact h.symm

theorem pAlignZero_erased_fresh_beh (ω : Nat → Nat) (b : Beh)
    (h : HasBehIn (.fresh ω) (eraseMarkers pAlignZero 0) b) : False := by
  rw [hasBehIn_iff_toBeh (n := 10) (by simp_run [pAlignZero, disjointRanges])] at h
  simp_run [pAlignZero, disjointRanges] at h

/-- **Alignment `0` with fresh addresses.** `pAlignZero` observes no address and is UB-free,
but its locals have alignment `0`; erasing the markers of local `0` pins it at address `0` for
the whole run, so the allocation of local `1` (also forced to address `0`) is always refused:
the marker-erased program has no behaviour at all, and erasure is not an equivalence. -/
theorem eraseMarkers_alignZero_not_equivPP :
    NoAddrObs pAlignZero ∧ UBFree .fresh pAlignZero ∧
      (∀ b, ¬ HasBeh .fresh (eraseMarkers pAlignZero 0) b) ∧
      ¬ RefinesPP .fresh (eraseMarkers pAlignZero 0) pAlignZero := by
  have hnone : ∀ b, ¬ HasBeh .fresh (eraseMarkers pAlignZero 0) b :=
    fun b ⟨ω, h⟩ => pAlignZero_erased_fresh_beh ω b h
  refine ⟨?_, ?_, hnone, ?_⟩
  · intro b hb s hs rv hrv
    simp [pAlignZero] at hb
    subst hb
    simp at hs
    rcases hs with rfl | rfl | rfl | rfl <;> simp [Stmt.rvalue?] at hrv <;> subst hrv <;> rfl
  · rintro t ⟨ω, h⟩
    cases pAlignZero_fresh_beh ω _ h
  · intro h
    obtain ⟨bs, hbs, _⟩ := h (.term [1])
      ⟨fun _ => 0, (hasBehIn_iff_toBeh (n := 10) (by decide) _).2 (by rfl)⟩
    exact hnone bs hbs

/-- **Tightness of `hwf` (all other hypotheses hold, the conclusion fails).** -/
theorem eraseMarkers_hwf_counterexample :
    NoAddrObs pAlignZero ∧ UBFree .fresh pAlignZero ∧
      ¬ EquivPP .fresh pAlignZero (eraseMarkers pAlignZero 0) :=
  ⟨eraseMarkers_alignZero_not_equivPP.1, eraseMarkers_alignZero_not_equivPP.2.1,
    fun h => eraseMarkers_alignZero_not_equivPP.2.2.2 h.2⟩

/-- **An observed address.** `pAddrCmp` is UB-free under fresh addresses and erasing `x`'s
markers refines it, but the source can emit `0` (the two live ranges of `x` get different
addresses) while the target always emits `1`: source behaviours strictly include target
behaviours, so erasure is not an equivalence. -/
theorem eraseMarkers_addrObserved_not_equivPP :
    (∀ L ∈ pAddrCmp.locals, 1 ≤ L.align) ∧
    UBFree .fresh pAddrCmp ∧ RefinesPP .fresh pAddrCmp (eraseMarkers pAddrCmp 1) ∧
    HasBeh .fresh pAddrCmp (.term [0]) ∧ ¬ HasBeh .fresh (eraseMarkers pAddrCmp 1) (.term [0]) ∧
    ¬ RefinesPP .fresh (eraseMarkers pAddrCmp 1) pAddrCmp := by
  refine ⟨by decide, ?_, ?_, pAddrCmp_fresh_term_zero, hasBeh_ex_neg_erased_addrCmp, ?_⟩
  · rintro t ⟨ω, h⟩
    rcases pAddrCmp_fresh_beh ω _ h with h | h <;> cases h
  · intro bt ⟨ω, h⟩
    rw [pAddrCmp_erased_fresh_beh ω bt h]
    exact ⟨_, pAddrCmp_fresh_term_one, improvesPP_refl _⟩
  · intro h
    obtain ⟨bs, ⟨ω, hbs⟩, himp⟩ := h _ pAddrCmp_fresh_term_zero
    rw [pAddrCmp_erased_fresh_beh ω bs hbs] at himp
    exact not_improvesPP_term_term (by decide) himp

/-- **Tightness of `hobs` (all other hypotheses hold, the conclusion fails).** -/
theorem eraseMarkers_hobs_counterexample :
    (∀ L ∈ pAddrCmp.locals, 1 ≤ L.align) ∧ UBFree .fresh pAddrCmp ∧
      ¬ EquivPP .fresh pAddrCmp (eraseMarkers pAddrCmp 1) :=
  ⟨eraseMarkers_addrObserved_not_equivPP.1, eraseMarkers_addrObserved_not_equivPP.2.1,
    fun h => eraseMarkers_addrObserved_not_equivPP.2.2.2.2.2 h.2⟩

/-- **A stale read.** `pStale` observes no address; erasing its markers refines it (the
source is UB, the target emits `5`), but is not an equivalence. -/
theorem eraseMarkers_staleRead_not_equivPP :
    (∀ L ∈ pStale.locals, 1 ≤ L.align) ∧
    NoAddrObs pStale ∧ RefinesPP .fresh pStale (eraseMarkers pStale 0) ∧
      ¬ RefinesPP .fresh (eraseMarkers pStale 0) pStale := by
  refine ⟨by decide, noAddrObs_ex_pos, ?_, ?_⟩
  · exact refinesAcross_of_src_beh pStale_fresh_wrong fun b _ => improvesPP_wrong_nil b
  · intro h
    obtain ⟨bs, ⟨ω, hbs⟩, himp⟩ := h _ pStale_fresh_wrong
    rw [pStale_erased_fresh_beh ω bs hbs] at himp
    rcases himp with h | ⟨t, h, _⟩ <;> cases h

/-- **Tightness of `hub` (all other hypotheses hold, the conclusion fails).** -/
theorem eraseMarkers_hub_counterexample :
    (∀ L ∈ pStale.locals, 1 ≤ L.align) ∧ NoAddrObs pStale ∧
      ¬ EquivPP .fresh pStale (eraseMarkers pStale 0) :=
  ⟨eraseMarkers_staleRead_not_equivPP.1, eraseMarkers_staleRead_not_equivPP.2.1,
    fun h => eraseMarkers_staleRead_not_equivPP.2.2.2 h.2⟩

/-- **`UBFree` and `NoAddrObs` are not necessary.** Erasing the markers of `pDeadUse` (which
uses `x` while it is unallocated, so it is not UB-free) is an equivalence, because the target
reaches `unreachable` with the same empty trace; erasing the markers of `pAddrSelf` (which
compares `&raw x` with itself) is an equivalence. -/
theorem eraseMarkers_fresh_equivPP_without_ubFree_or_noAddrObs :
    (EquivPP .fresh pDeadUse (eraseMarkers pDeadUse 0) ∧ ¬ UBFree .fresh pDeadUse) ∧
    (EquivPP .fresh pAddrSelf (eraseMarkers pAddrSelf 1) ∧ ¬ NoAddrObs pAddrSelf) := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro bt ⟨ω, h⟩
    rw [pDeadUse_erased_fresh_beh ω bt h]
    exact ⟨_, pDeadUse_fresh_wrong, improvesPP_refl _⟩
  · intro bt ⟨ω, h⟩
    rw [pDeadUse_fresh_beh ω bt h]
    exact ⟨_, pDeadUse_erased_fresh_wrong, improvesPP_refl _⟩
  · intro h
    exact h [] pDeadUse_fresh_wrong
  · intro bt ⟨ω, h⟩
    rw [pAddrSelf_erased_fresh_beh ω bt h]
    exact ⟨_, pAddrSelf_fresh_term, improvesPP_refl _⟩
  · intro bt ⟨ω, h⟩
    rw [pAddrSelf_fresh_beh ω bt h]
    exact ⟨_, pAddrSelf_erased_fresh_term, improvesPP_refl _⟩
  · intro h
    have := h (pAddrSelf.blk 0) (by decide)
      (.emit (.ptrEq (.copy ⟨0, []⟩ .ptr) (.copy ⟨0, []⟩ .ptr))) (by decide) _ rfl
    exact absurd this (by decide)

/-- One one-byte local of alignment `0` with a single live range: `SL 0; emit 1; SD 0`. -/
def pAlignZeroOne : Prog :=
  ⟨[⟨1, 0⟩], [⟨[.storageLive 0, .emit (.use (.const (.int 1))), .storageDead 0], .halt⟩]⟩

theorem pAlignZeroOne_fresh_beh (ω : Nat → Nat) (b : Beh)
    (h : HasBehIn (.fresh ω) pAlignZeroOne b) : b = .term [1] := by
  rw [hasBehIn_iff_toBeh (n := 10) (by simp_run [pAlignZeroOne, disjointRanges])] at h
  simp_run [pAlignZeroOne, disjointRanges] at h
  exact h.symm

theorem pAlignZeroOne_erased_fresh_beh (ω : Nat → Nat) (b : Beh)
    (h : HasBehIn (.fresh ω) (eraseMarkers pAlignZeroOne 0) b) : b = .term [1] := by
  rw [hasBehIn_iff_toBeh (n := 10) (by simp_run [pAlignZeroOne, disjointRanges])] at h
  simp_run [pAlignZeroOne, disjointRanges] at h
  exact h.symm

theorem pAlignZeroOne_fresh_term : HasBeh .fresh pAlignZeroOne (.term [1]) :=
  ⟨fun _ => 0, (hasBehIn_iff_toBeh (n := 10) (by decide) _).2 (by rfl)⟩

theorem pAlignZeroOne_erased_fresh_term : HasBeh .fresh (eraseMarkers pAlignZeroOne 0) (.term [1]) :=
  ⟨fun _ => 0, (hasBehIn_iff_toBeh (n := 10) (by decide) _).2 (by rfl)⟩

/-- **`hwf` is not necessary.** `pAlignZeroOne` observes no address and is UB-free under fresh
addresses, its only local has alignment `0`, and erasing its markers is an equivalence. -/
theorem eraseMarkers_fresh_equivPP_without_alignPos :
    NoAddrObs pAlignZeroOne ∧ UBFree .fresh pAlignZeroOne ∧
      ¬ (∀ L ∈ pAlignZeroOne.locals, 1 ≤ L.align) ∧
      EquivPP .fresh pAlignZeroOne (eraseMarkers pAlignZeroOne 0) := by
  refine ⟨?_, ?_, by decide, ?_, ?_⟩
  · intro b hb s hs rv hrv
    simp [pAlignZeroOne] at hb
    subst hb
    simp at hs
    rcases hs with rfl | rfl | rfl <;> simp [Stmt.rvalue?] at hrv <;> subst hrv <;> rfl
  · rintro t ⟨ω, h⟩
    cases pAlignZeroOne_fresh_beh ω _ h
  · intro bt ⟨ω, h⟩
    rw [pAlignZeroOne_erased_fresh_beh ω bt h]
    exact ⟨_, pAlignZeroOne_fresh_term, improvesPP_refl _⟩
  · intro bt ⟨ω, h⟩
    rw [pAlignZeroOne_fresh_beh ω bt h]
    exact ⟨_, pAlignZeroOne_erased_fresh_term, improvesPP_refl _⟩

/-- **UB checks after marker erasure miss stale reads.** Every exact UB checker for the
fresh semantics accepts the marker-erased `pStale`, although `pStale` is not UB-free. -/
theorem ubCheck_after_eraseMarkers_misses_stale_read :
    ∀ chk, ExactUBChecker .fresh chk →
      chk (eraseMarkers pStale 0) = true ∧ ¬ UBFree .fresh pStale := by
  intro chk hchk
  refine ⟨(hchk _).2 ?_, fun h => h [] pStale_fresh_wrong⟩
  rintro t ⟨ω, h⟩
  cases pStale_erased_fresh_beh ω _ h

end Toy.PlaceEval
