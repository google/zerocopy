import Toy.PlaceEval.Erasure

/-!
# Erasing storage markers: behaviour sets of the concrete programs

`eraseMarkers P x` removes every `storageLive x` / `storageDead x`, so (for
`x < P.locals.length`) `x` is allocated at entry for the whole run. Concrete instances use the fresh-address semantics (all oracles,
analysed symbolically) or a static slot assignment.
-/

namespace Toy.PlaceEval

/-! ## Behaviour sets under fresh addresses (every oracle) -/

/-- `pShare` with `x0`'s markers erased, under every oracle: `x0` is allocated at entry, the
later allocation of `x1` must avoid it, and `emit x0` emits `5` (or the run blocks). -/
theorem pShare_erased_fresh_beh (ω : Nat → Nat) (b : Beh)
    (h : HasBehIn (.fresh ω) (eraseMarkers pShare 0) b) : b = .term [5] := by
  by_cases hd : ω 1 + 1 ≤ ω 0 ∨ ω 0 + 1 ≤ ω 1
  · have hne : ω 1 ≠ ω 0 := by omega
    rw [hasBehIn_iff_toBeh (n := 10) (by simp_run [pShare, u8, disjointRanges, hd, hne])] at h
    simp_run [pShare, u8, disjointRanges, hd, hne] at h
    exact h.symm
  · rw [hasBehIn_iff_toBeh (n := 10) (by simp_run [pShare, u8, disjointRanges, hd])] at h
    simp_run [pShare, u8, disjointRanges, hd] at h

theorem pShare_fresh_wrong : HasBeh .fresh pShare (.wrong []) :=
  ⟨fun k => k, (hasBehIn_iff_toBeh (n := 12) (by decide) _).2 (by rfl)⟩

theorem pShare_erased_slots_beh (b : Beh) :
    HasBeh (.slots sShare) (eraseMarkers pShare 0) b ↔ b = .term [7] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b

theorem pShare_slots_beh (b : Beh) : HasBeh (.slots sShare) pShare b ↔ b = .wrong [] :=
  beh_slots_eq (n := 12) (by decide) (by rfl) b

/-- `pStale`, under every oracle: the read after the re-`storageLive` is UB. -/
theorem pStale_fresh_beh (ω : Nat → Nat) (b : Beh) (h : HasBehIn (.fresh ω) pStale b) :
    b = .wrong [] := by
  rw [hasBehIn_iff_toBeh (n := 10) (by simp_run [pStale, u8])] at h
  simp_run [pStale, u8] at h
  exact h.symm

/-- `pStale` with markers erased, under every oracle: emits `5`. -/
theorem pStale_erased_fresh_beh (ω : Nat → Nat) (b : Beh)
    (h : HasBehIn (.fresh ω) (eraseMarkers pStale 0) b) : b = .term [5] := by
  rw [hasBehIn_iff_toBeh (n := 10) (by simp_run [pStale, u8])] at h
  simp_run [pStale, u8] at h
  exact h.symm

theorem pStale_fresh_wrong : HasBeh .fresh pStale (.wrong []) :=
  ⟨fun k => k, (hasBehIn_iff_toBeh (n := 10) (by decide) _).2 (by rfl)⟩

theorem pStale_erased_fresh_term : HasBeh .fresh (eraseMarkers pStale 0) (.term [5]) :=
  ⟨fun k => k, (hasBehIn_iff_toBeh (n := 10) (by decide) _).2 (by rfl)⟩

/-- `pDeadUse`, under every oracle: the store to the unallocated `x` is UB. -/
theorem pDeadUse_fresh_beh (ω : Nat → Nat) (b : Beh) (h : HasBehIn (.fresh ω) pDeadUse b) :
    b = .wrong [] := by
  rw [hasBehIn_iff_toBeh (n := 10) (by simp_run [pDeadUse, u8])] at h
  simp_run [pDeadUse, u8] at h
  exact h.symm

/-- `pDeadUse` with markers erased, under every oracle: reaches `unreachable` (UB). -/
theorem pDeadUse_erased_fresh_beh (ω : Nat → Nat) (b : Beh)
    (h : HasBehIn (.fresh ω) (eraseMarkers pDeadUse 0) b) : b = .wrong [] := by
  rw [hasBehIn_iff_toBeh (n := 10) (by simp_run [pDeadUse, u8])] at h
  simp_run [pDeadUse, u8] at h
  exact h.symm

theorem pDeadUse_fresh_wrong : HasBeh .fresh pDeadUse (.wrong []) :=
  ⟨fun k => k, (hasBehIn_iff_toBeh (n := 10) (by decide) _).2 (by rfl)⟩

theorem pDeadUse_erased_fresh_wrong : HasBeh .fresh (eraseMarkers pDeadUse 0) (.wrong []) :=
  ⟨fun k => k, (hasBehIn_iff_toBeh (n := 10) (by decide) _).2 (by rfl)⟩

/-- `pAddrSelf`, under every oracle: emits `1` (or blocks). -/
theorem pAddrSelf_fresh_beh (ω : Nat → Nat) (b : Beh) (h : HasBehIn (.fresh ω) pAddrSelf b) :
    b = .term [1] := by
  by_cases hd : disjointRanges (ω 1 + 1) 1 (2 * (ω 0 + 1)) 2 = true
  · rw [hasBehIn_iff_toBeh (n := 10) (by simp_run [pAddrSelf, ptrL, hd])] at h
    simp_run [pAddrSelf, ptrL, hd] at h
    exact h.symm
  · rw [hasBehIn_iff_toBeh (n := 10) (by simp_run [pAddrSelf, ptrL, hd])] at h
    simp_run [pAddrSelf, ptrL, hd] at h

/-- `pAddrSelf` with markers erased, under every oracle: emits `1` (or blocks). -/
theorem pAddrSelf_erased_fresh_beh (ω : Nat → Nat) (b : Beh)
    (h : HasBehIn (.fresh ω) (eraseMarkers pAddrSelf 1) b) : b = .term [1] := by
  by_cases hd : disjointRanges (ω 1 + 1) 1 (2 * (ω 0 + 1)) 2 = true
  · rw [hasBehIn_iff_toBeh (n := 10) (by simp_run [pAddrSelf, ptrL, hd])] at h
    simp_run [pAddrSelf, ptrL, hd] at h
    exact h.symm
  · rw [hasBehIn_iff_toBeh (n := 10) (by simp_run [pAddrSelf, ptrL, hd])] at h
    simp_run [pAddrSelf, ptrL, hd] at h

theorem pAddrSelf_fresh_term : HasBeh .fresh pAddrSelf (.term [1]) :=
  ⟨fun k => 4 * k, (hasBehIn_iff_toBeh (n := 10) (by decide) _).2 (by rfl)⟩

theorem pAddrSelf_erased_fresh_term : HasBeh .fresh (eraseMarkers pAddrSelf 1) (.term [1]) :=
  ⟨fun k => 4 * k, (hasBehIn_iff_toBeh (n := 10) (by decide) _).2 (by rfl)⟩

/-- `pLive` under every oracle emits `5`. -/
theorem pLive_fresh_term : HasBeh .fresh pLive (.term [5]) :=
  ⟨fun k => k, (hasBehIn_iff_toBeh (n := 10) (by decide) _).2 (by rfl)⟩

theorem pLive_slots_beh (b : Beh) : HasBeh (.slots sEx) pLive b ↔ b = .term [5] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b

end Toy.PlaceEval
