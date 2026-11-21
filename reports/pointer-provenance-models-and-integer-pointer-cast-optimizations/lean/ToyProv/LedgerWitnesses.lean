import ToyProv.Forwarding
import ToyProv.Bytes

/-!
# Supporting lemmas for hypothesis ledgers (R4a, R4b, R5b)

These lemmas state no new result. They record

* tightness witnesses for the hypothesis `h` of the strict-model vacuity theorems
  `forwardAcrossCast_strict_src_ub` and `dseAcrossCast_strict_src_ub` (R4a, R4b);
* tightness witnesses for the hypotheses `hd` and `hs` of `memcpy_frame` (R5b), stated for
  `memcpy_frame`'s own conclusion; and
* the fact that the hypothesis `hr` of `memcpy_frame` is redundant: the frame conclusion follows
  from `hd` and `hs` alone (`memcpy_frame_of_hd_hs`).

Each witness has the shape "all other hypotheses hold and the conclusion fails".
-/

namespace Toy.Prov

/-- A two-instruction program: write the integer 1 into register 0 and output it. It contains no
cast, so it matches neither `ForwardAcrossCast` nor `DSEAcrossCast`. -/
def constObsProg : Prog := [.const 0 1, .obs 0]

/-- `constObsProg` is defined in the strict model and outputs `[1]`. -/
theorem constObsProg_beh_strict : beh .strict constObsProg = [.done [1]] := by decide

/-- **R4a, `h` needed in `forwardAcrossCast_strict_src_ub`.** The theorem has no hypothesis other
than `h`. Without `h`, `src` and `tgt` are arbitrary programs: for `src = tgt = constObsProg` the
strict behaviour is `[.done [1]]`, so the conclusion (both sides are `[.ub]`) fails. The pair does
not match `ForwardAcrossCast .strict`. -/
theorem forwardAcrossCast_strict_src_ub_h_needed :
    ¬ ForwardAcrossCast .strict constObsProg constObsProg ∧
      ¬ (beh .strict constObsProg = [.ub] ∧ beh .strict constObsProg = [.ub]) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hub := (forwardAcrossCast_strict_src_ub _ _ h).1
    rw [constObsProg_beh_strict] at hub
    exact absurd hub (by decide)
  · have hub := h.1
    rw [constObsProg_beh_strict] at hub
    exact absurd hub (by decide)

/-- **R4b, `h` needed in `dseAcrossCast_strict_src_ub`.** As for R4a: without `h`, the pair
`src = tgt = constObsProg` is defined in the strict model, so the conclusion fails. The pair does
not match `DSEAcrossCast .strict`. -/
theorem dseAcrossCast_strict_src_ub_h_needed :
    ¬ DSEAcrossCast .strict constObsProg constObsProg ∧
      ¬ (beh .strict constObsProg = [.ub] ∧ beh .strict constObsProg = [.ub]) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hub := (dseAcrossCast_strict_src_ub _ _ h).1
    rw [constObsProg_beh_strict] at hub
    exact absurd hub (by decide)
  · have hub := h.1
    rw [constObsProg_beh_strict] at hub
    exact absurd hub (by decide)

/-- **R5b, `hd` needed in `memcpy_frame`.** In `r5State` (exposed model), register 1 holds B
(`hr` with `y` = B) and `r5Succ` is the successor of `memcpy C B 2` (`hs`), but `x` is A (at 16)
while register 2 holds C (at 20). The byte that changes (C's first byte, at 20) lies outside
`[x.addr, x.addr + 2) = [16, 18)`, so the frame conclusion for `x` fails. -/
theorem memcpy_frame_hd_needed :
    r5State.regs 1 = some (.ptr ⟨some 1, 18⟩) ∧ some r5Succ ∈ step .exposed r5State (.memcpy 2 1 2) ∧
      r5State.regs 2 ≠ some (.ptr ⟨some 0, 16⟩) ∧
      ¬ (∀ z, z < (⟨some 0, 16⟩ : Ptr).addr ∨ (⟨some 0, 16⟩ : Ptr).addr + 2 ≤ z →
          r5Succ.mem z = r5State.mem z) := by
  refine ⟨by decide, r5Succ_mem .exposed, by decide, fun h => ?_⟩
  have := h 20 (by decide)
  revert this; decide

/-- `r5State` with B's two bytes written over A (at 16) instead of C: not the successor of
`memcpy C B 2`. -/
def r5WrongDst : St := { r5State with mem := writeBytes r5State.mem 16 (readBytes r5State.mem 18 2) }

/-- **R5b, `hs` needed in `memcpy_frame`.** In `r5State`, register 2 holds C (`hd` with `x` = C at
20) and register 1 holds B (`hr` with `y` = B), but `s' := r5WrongDst` is not a successor of the
`memcpy`: its byte at 16, outside `[20, 22)`, differs from `r5State`'s, so the frame conclusion
fails. -/
theorem memcpy_frame_hs_needed :
    r5State.regs 2 = some (.ptr ⟨some 2, 20⟩) ∧ r5State.regs 1 = some (.ptr ⟨some 1, 18⟩) ∧
      ¬ (∀ z, z < (⟨some 2, 20⟩ : Ptr).addr ∨ (⟨some 2, 20⟩ : Ptr).addr + 2 ≤ z →
          r5WrongDst.mem z = r5State.mem z) := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  have := h 16 (by decide)
  revert this; decide

/-- **R5b, `hr` is redundant in `memcpy_frame`.** The frame conclusion follows from `hd` and `hs`
alone: a defined `memcpy d r n` forces register `r` to hold some pointer, and the conclusion does
not mention the source pointer. -/
theorem memcpy_frame_of_hd_hs (m : Model) (s s' : St) (d r : Reg) (n : Nat) (x : Ptr)
    (hd : s.regs d = some (.ptr x)) (hs : some s' ∈ step m s (.memcpy d r n)) :
    ∀ z, z < x.addr ∨ x.addr + n ≤ z → s'.mem z = s.mem z := by
  cases hr : s.regs r with
  | none => simp [step, hd, hr] at hs
  | some v =>
    cases v with
    | int _ => simp [step, hd, hr] at hs
    | ptr y => exact memcpy_frame m s s' d r n x y hd hr hs

end Toy.Prov
