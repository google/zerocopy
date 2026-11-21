import ToyProv.Lemmas
import ToyProv.FlatInv
import ToyProv.Disjoint

/-!
# R1 — One-past-the-end equality and address-equality substitution
-/

namespace Toy.Prov

/-- Allocate A (2 bytes) and B (2 bytes), form `A + 2` (one past A's end), compare it with B's
start by `ptrEq`, and observe the result. -/
def onePastProg : Prog := [.alloc 0 2, .alloc 1 2, .offset 2 0 2, .ptrEq 3 2 1, .obs 3]

/-- Allocate A (`n₁` bytes) and B (`n₂` bytes), form `A + n₁` (one past A's end), compare it with
B's start by `ptrEq`, and observe the result. -/
def onePastProgN (n₁ n₂ : Nat) : Prog :=
  [.alloc 0 n₁, .alloc 1 n₂, .offset 2 0 (n₁ : Int), .ptrEq 3 2 1, .obs 3]

/-- **R1a.** In every model, for all allocation sizes `n₁, n₂ ≥ 1`, with the toy's bump allocator
(consecutive allocations are adjacent), the pointer one past the end of the first allocation A
compares equal by address to the pointer to the start of the next allocation B. -/
theorem onePast_ptrEq_adjacent_start (m : Model) (n₁ n₂ : Nat) (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) :
    beh m (onePastProgN n₁ n₂) = [.done [1]] := by
  cases m <;> simp [beh, runs, exec, step, onePastProgN, h₁, h₂, St.setReg, offsetAddr, init]

/-- **R1a, `h₁` needed.** A zero-size first allocation is UB. -/
theorem onePast_size₁_needed (m : Model) :
    (2 : Nat) ≠ 0 ∧ beh m (onePastProgN 0 2) ≠ [.done [1]] := by
  cases m <;> decide

/-- **R1a, `h₂` needed.** A zero-size second allocation is UB. -/
theorem onePast_size₂_needed (m : Model) :
    (2 : Nat) ≠ 0 ∧ beh m (onePastProgN 2 0) ≠ [.done [1]] := by
  cases m <;> decide

/-- **R1a non-vacuity / instance.** The two-byte instance `onePastProg` used by R1b. -/
theorem onePast_ptrEq_adjacent_start_all_models (m : Model) :
    (2 : Nat) ≠ 0 ∧ (2 : Nat) ≠ 0 ∧ beh m onePastProg = [.done [1]] := by
  cases m <;> decide

/-! ### R1b — `SubstAddrEq` is unsound in `strict` and `exposed`, sound on the same program in `flat` -/

/-- Code before the rewrite point: A, B, `p := A + 2`, observe `p == q` (it is `1`), `t := 7`. -/
def r1Pre : Prog := [.alloc 0 2, .alloc 1 2, .offset 2 0 2, .ptrEq 3 2 1, .obs 3, .const 4 7]
/-- Code after the rewrite point: read B back and observe it. -/
def r1Post : Prog := [.load 5 .int 1, .obs 5]
/-- Source: store through `q` (register 1, B's start). -/
def r1Src : Prog := r1Pre ++ .store 1 4 :: r1Post
/-- Target: the store's pointer operand `q` replaced by the address-equal `p` (register 2,
one past A's end). -/
def r1Tgt : Prog := r1Pre ++ (Instr.store 1 4).substUse 1 2 :: r1Post

theorem r1Tgt_eq : r1Tgt = r1Pre ++ .store 2 4 :: r1Post := by decide

/-- **R1b (strict).** Concrete counterexample: the rewrite is allowed by `SubstAddrEq` (the two
pointers are address-equal in every reachable state) but the target is not a refinement: the
source stores through B and observes `[1, 7]`; the target stores through the one-past-the-end
pointer of A, which is UB. -/
theorem substAddrEq_counterexample_strict :
    SubstAddrEq .strict r1Src r1Tgt ∧ ¬ Refines .strict r1Tgt r1Src ∧
      beh .strict r1Src = [.done [1, 7]] ∧ beh .strict r1Tgt = [.ub] :=
  ⟨⟨r1Pre, _, r1Post, 1, 2, rfl, rfl, by decide⟩, by decide, by decide, by decide⟩

/-- **R1b (exposed).** The same counterexample in the exposed model. -/
theorem substAddrEq_counterexample_exposed :
    SubstAddrEq .exposed r1Src r1Tgt ∧ ¬ Refines .exposed r1Tgt r1Src ∧
      beh .exposed r1Src = [.done [1, 7]] ∧ beh .exposed r1Tgt = [.ub] :=
  ⟨⟨r1Pre, _, r1Post, 1, 2, rfl, rfl, by decide⟩, by decide, by decide, by decide⟩

theorem substAddrEq_not_sound_strict : ¬ Sound .strict SubstAddrEq :=
  fun h => substAddrEq_counterexample_strict.2.1 (h _ _ substAddrEq_counterexample_strict.1)

theorem substAddrEq_not_sound_exposed : ¬ Sound .exposed SubstAddrEq :=
  fun h => substAddrEq_counterexample_exposed.2.1 (h _ _ substAddrEq_counterexample_exposed.1)

/-- **R1b positive control.** On the same program pair the rewrite is a refinement in the flat
model (and in fact behaviour-preserving). -/
theorem substAddrEq_example_refines_flat :
    SubstAddrEq .flat r1Src r1Tgt ∧ Refines .flat r1Tgt r1Src ∧ beh .flat r1Tgt = beh .flat r1Src ∧
      beh .flat r1Src = [.done [1, 7]] :=
  ⟨⟨r1Pre, _, r1Post, 1, 2, rfl, rfl, by decide⟩, by decide, by decide, by decide⟩

/-! ### R1c — address-equality substitution between in-bounds pointers -/

/-- **R1c.** In every model, substituting `p` for `q` in one instruction is a refinement when, in
every reachable state at that point, the two pointers have equal addresses and both are
in bounds of a live allocation (`inBoundsC`). In `strict`/`exposed` this holds because live
allocations are disjoint, so two in-bounds pointers with the same address have the same
provenance and are the same value (then R2c applies). -/
theorem substAddrEqInBounds_sound (m : Model) : Sound m SubstAddrEqInBounds := by
  cases m with
  | flat =>
    rintro src tgt ⟨pre, i, post, q, p, rfl, rfl, hc⟩
    apply substAddrEq_sound_flat
    refine ⟨pre, i, post, q, p, rfl, rfl, fun s hs => ?_⟩
    have h := hc s hs
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  | strict | exposed =>
    rintro src tgt ⟨pre, i, post, q, p, rfl, rfl, hc⟩
    apply refines_of_beh_eq
    apply beh_replace_of_step_eq
    intro s hs
    apply step_substUse
    have h := hc s hs
    simp only [Bool.and_eq_true, addrEqC, inBoundsC] at h
    rcases h with ⟨⟨had, hbp⟩, hbq⟩
    cases hp : s.regs p with
    | none => simp [hp] at had
    | some vp =>
      cases vp with
      | int _ => simp [hp] at had
      | ptr xp =>
        cases hq : s.regs q with
        | none => simp [hp, hq] at had
        | some vq =>
          cases vq with
          | int _ => simp [hp, hq] at had
          | ptr xq =>
            simp only [hp, hq, beq_iff_eq] at had hbp hbq
            simp only [canAccess, lookup_eq_getElem?] at hbp hbq
            cases hxp : xp.prov with
            | none => simp [hxp] at hbp
            | some idp =>
              cases hxq : xq.prov with
              | none => simp [hxq] at hbq
              | some idq =>
                simp only [hxp] at hbp
                simp only [hxq] at hbq
                cases hbp_blk : s.blocks[idp]? with
                | none => simp [hbp_blk] at hbp
                | some bp =>
                  cases hbq_blk : s.blocks[idq]? with
                  | none => simp [hbq_blk] at hbq
                  | some bq =>
                    simp only [hbp_blk, inBlock, Bool.and_eq_true, decide_eq_true_eq] at hbp
                    simp only [hbq_blk, inBlock, Bool.and_eq_true, decide_eq_true_eq] at hbq
                    rcases hbp with ⟨⟨_, hbp1⟩, hbp2⟩
                    rcases hbq with ⟨⟨_, hbq1⟩, hbq2⟩
                    have hid : idp = idq := disjoint_eq_of_in_range (after_disjointBlocks _ pre s hs)
                      hbp_blk hbq_blk ⟨hbp1, by dsimp only [Addr] at *; omega⟩
                      ⟨by rw [had]; exact hbq1, by dsimp only [Addr] at *; omega⟩
                    subst hid
                    cases xp; cases xq
                    simp only at had hxp hxq
                    subst had; subst hxp; subst hxq
                    rfl

/-- **R1c, `p` in bounds needed.** R1b's pair: `q` (B's start) is in bounds and address-equal to
`p` (one past A's end), which is not in bounds; the rewrite is not a refinement in `strict`. -/
theorem substAddrEqInBounds_p_needed :
    AllAfter .strict r1Pre (fun s => addrEqC 2 1 s && inBoundsC .strict 1 s) ∧
      ¬ AllAfter .strict r1Pre (inBoundsC .strict 2) ∧ ¬ Refines .strict r1Tgt r1Src := by
  decide

/-- Code before the rewrite point: A, B, `q := A + 2` (one past A's end), `p := B`. -/
def r1cPre : Prog := [.alloc 0 2, .alloc 1 2, .offset 2 0 2, .copy 3 1, .const 4 7]
/-- After the rewrite point: store 7 through `d` and read A. -/
def r1cPost : Prog := [.store 5 4, .load 6 .int 0, .obs 6]

/-- **R1c, `q` in bounds needed.** `q` (one past A's end) is not in bounds, `p` (B's start) is,
and they are address-equal. The source moves `q` back into A and stores there (outputs `[7]`);
the target moves `p` back, keeping B's provenance, and its store is UB. -/
theorem substAddrEqInBounds_q_needed :
    AllAfter .strict r1cPre (fun s => addrEqC 3 2 s && inBoundsC .strict 3 s) ∧
      ¬ AllAfter .strict r1cPre (inBoundsC .strict 2) ∧
      beh .strict (r1cPre ++ .offset 5 2 (-2) :: r1cPost) = [.done [7]] ∧
      beh .strict (r1cPre ++ (Instr.offset 5 2 (-2)).substUse 2 3 :: r1cPost) = [.ub] ∧
      ¬ Refines .strict (r1cPre ++ (Instr.offset 5 2 (-2)).substUse 2 3 :: r1cPost)
        (r1cPre ++ .offset 5 2 (-2) :: r1cPost) := by
  decide

/-- Code before the rewrite point: A, B, store 7 into B and 9 into A. -/
def r1cPreAddr : Prog := [.alloc 0 2, .alloc 1 2, .const 2 7, .const 3 9, .store 1 2, .store 0 3]

/-- **R1c, address equality needed.** Both pointers (A and B) are in bounds (`inBoundsC`), but their
addresses differ; substituting `p` (A) for `q` (B) in a load changes the output `[7]` to `[9]`. -/
theorem substAddrEqInBounds_addrEq_needed :
    AllAfter .strict r1cPreAddr (fun s => inBoundsC .strict 0 s && inBoundsC .strict 1 s) ∧
      ¬ AllAfter .strict r1cPreAddr (addrEqC 0 1) ∧
      beh .strict (r1cPreAddr ++ .load 4 .int 1 :: [.obs 4]) = [.done [7]] ∧
      beh .strict (r1cPreAddr ++ (Instr.load 4 .int 1).substUse 1 0 :: [.obs 4]) = [.done [9]] ∧
      ¬ Refines .strict (r1cPreAddr ++ (Instr.load 4 .int 1).substUse 1 0 :: [.obs 4])
        (r1cPreAddr ++ .load 4 .int 1 :: [.obs 4]) := by
  decide

/-- Code before the rewrite point: A; `q := A`; `p := (A + 1) - 1`. -/
def r1cPreNV : Prog := [.alloc 0 2, .copy 1 0, .offset 2 0 1, .offset 2 2 (-1), .const 3 7]

/-- **R1c non-vacuity.** In the strict and exposed models the side condition holds and the
rewrite (store through `p` instead of `q`) preserves the output `[7]`. -/
theorem substAddrEqInBounds_nonvacuous :
    SubstAddrEqInBounds .strict (r1cPreNV ++ .store 1 3 :: [.load 4 .int 0, .obs 4])
      (r1cPreNV ++ (Instr.store 1 3).substUse 1 2 :: [.load 4 .int 0, .obs 4]) ∧
      SubstAddrEqInBounds .exposed (r1cPreNV ++ .store 1 3 :: [.load 4 .int 0, .obs 4])
        (r1cPreNV ++ (Instr.store 1 3).substUse 1 2 :: [.load 4 .int 0, .obs 4]) ∧
      beh .strict (r1cPreNV ++ (Instr.store 1 3).substUse 1 2 :: [.load 4 .int 0, .obs 4]) = [.done [7]] :=
  ⟨⟨_, _, _, 1, 2, rfl, rfl, by decide⟩, ⟨_, _, _, 1, 2, rfl, rfl, by decide⟩, by decide⟩

end Toy.Prov
