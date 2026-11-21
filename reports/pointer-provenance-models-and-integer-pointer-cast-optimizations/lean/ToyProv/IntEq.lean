import ToyProv.Lemmas
import ToyProv.MonoSim
import ToyProv.Erasure

/-!
# R2 — Integer-equality folding

Three distinct rewrites are justified by `(int)p == (int)q`:

* substituting the *pointer* `p` for `q` (`SubstIntEq`) — unsound in `strict` and `exposed`
  even though both allocations are exposed (R2a);
* substituting one *integer* for an equal one (`SubstSameVal` on integer registers) — sound in
  every model, because integers carry no provenance (R2c);
* folding `d := int2ptr k` into `d := p` when `k == (int)p` (`Int2ptrToCopy`) — sound in
  `exposed` when no exposed live allocation other than `p`'s own can be picked for the address
  (R2b).
-/

namespace Toy.Prov

/-! ### R2a — pointer substitution justified by integer equality -/

/-- A, B, `p := A + 2`, cast both to integers, observe that the integers are equal, `t := 7`. -/
def r2Pre : Prog :=
  [.alloc 0 2, .alloc 1 2, .offset 2 0 2, .ptr2int 3 2, .ptr2int 4 1, .intEq 5 3 4, .obs 5, .const 6 7]
def r2Post : Prog := [.load 7 .int 1, .obs 7]
/-- Source: store through `q` (B's start). -/
def r2Src : Prog := r2Pre ++ .store 1 6 :: r2Post
/-- Target: `q` replaced by `p` (one past A's end), justified by `(int)p == (int)q`. -/
def r2Tgt : Prog := r2Pre ++ (Instr.store 1 6).substUse 1 2 :: r2Post

/-- **R2a (strict).** The rewrite satisfies `SubstIntEq` (equal addresses and both provenances
exposed in every reachable state; here the program has also cast both pointers and observed
`(int)p == (int)q`, although `SubstIntEq` itself does not require that), yet the target is UB
while the source outputs `[1, 7]`. -/
theorem substIntEq_counterexample_strict :
    SubstIntEq .strict r2Src r2Tgt ∧ ¬ Refines .strict r2Tgt r2Src ∧
      beh .strict r2Src = [.done [1, 7]] ∧ beh .strict r2Tgt = [.ub] :=
  ⟨⟨r2Pre, _, r2Post, 1, 2, rfl, rfl, by decide⟩, by decide, by decide, by decide⟩

/-- **R2a (exposed).** Exposure does not help: the target still stores through a pointer whose
provenance is A, at B's address. -/
theorem substIntEq_counterexample_exposed :
    SubstIntEq .exposed r2Src r2Tgt ∧ ¬ Refines .exposed r2Tgt r2Src ∧
      beh .exposed r2Src = [.done [1, 7]] ∧ beh .exposed r2Tgt = [.ub] :=
  ⟨⟨r2Pre, _, r2Post, 1, 2, rfl, rfl, by decide⟩, by decide, by decide, by decide⟩

theorem substIntEq_not_sound_strict : ¬ Sound .strict SubstIntEq :=
  fun h => substIntEq_counterexample_strict.2.1 (h _ _ substIntEq_counterexample_strict.1)

theorem substIntEq_not_sound_exposed : ¬ Sound .exposed SubstIntEq :=
  fun h => substIntEq_counterexample_exposed.2.1 (h _ _ substIntEq_counterexample_exposed.1)

/-- **R2a positive control.** In the flat model the same rewrite is a refinement. -/
theorem substIntEq_example_refines_flat :
    SubstIntEq .flat r2Src r2Tgt ∧ Refines .flat r2Tgt r2Src ∧
      beh .flat r2Src = [.done [1, 7]] ∧ beh .flat r2Tgt = [.done [1, 7]] :=
  ⟨⟨r2Pre, _, r2Post, 1, 2, rfl, rfl, by decide⟩, by decide, by decide, by decide⟩

/-! ### R2c — identical-value (in particular integer) substitution is sound in every model -/

/-- **R2c.** In every model, replacing reads of `q` by reads of `p` in one instruction preserves
behaviour (equality, not merely refinement) whenever, in every reachable state at that point, the
two registers hold the same value. (Sufficient, not necessary: the rewrite can also preserve
behaviour when `i` does not read `q` or its result is unused.) For integer registers this is integer GVN; for pointer registers it requires equal
provenance, which is what `SubstAddrEq` lacks. -/
theorem substSameVal_beh_eq (m : Model) (pre post : Prog) (i : Instr) (q p : Reg)
    (h : AllAfter m pre (sameValC p q)) :
    beh m (pre ++ i.substUse q p :: post) = beh m (pre ++ i :: post) := by
  apply beh_replace_of_step_eq
  intro s hs
  apply step_substUse
  have := h s hs
  simp only [sameValC] at this
  split at this <;> simp_all

theorem substSameVal_sound (m : Model) : Sound m SubstSameVal := by
  rintro src tgt ⟨pre, i, post, q, p, rfl, rfl, hc⟩
  exact refines_of_beh_eq (substSameVal_beh_eq m pre post i q p hc)

/-- **R2c non-vacuity, at the one-past-the-end boundary.** After `ip := (int)(A + 2)` and
`iq := (int)B`, replacing `iq` by `ip` as the operand of `int2ptr` is an instance of
`SubstSameVal` in the exposed model, and behaviour is unchanged (both output `[7]`). -/
def r2cPre : Prog := [.alloc 0 2, .alloc 1 2, .offset 2 0 2, .ptr2int 3 2, .ptr2int 4 1]
def r2cPost : Prog := [.const 6 7, .store 5 6, .load 7 .int 1, .obs 7]
theorem substSameVal_int_boundary_example :
    SubstSameVal .exposed (r2cPre ++ .int2ptr 5 4 :: r2cPost) (r2cPre ++ (Instr.int2ptr 5 4).substUse 4 3 :: r2cPost) ∧
      beh .exposed (r2cPre ++ (Instr.int2ptr 5 4).substUse 4 3 :: r2cPost) = [.done [7]] ∧
      beh .exposed (r2cPre ++ .int2ptr 5 4 :: r2cPost) = [.done [7]] :=
  ⟨⟨r2cPre, _, r2cPost, 4, 3, rfl, rfl, by decide⟩, by decide, by decide⟩

/-! ### R2b — when folding an integer back into a pointer is sound in `exposed` -/

/-- **R2b.** In the exposed model, replacing `d := int2ptr k` by `d := p` is a refinement if, in
every reachable state at that point, (`hk`) `k` holds the integer equal to `p`'s address, and
(`hc`) every allocation that `int2ptr` could pick for that address is `p`'s own provenance (so
either `p`'s allocation is the unique exposed live allocation whose closed range contains the
address, or there is no candidate at all). In the case with no candidate the source pointer has no
provenance and the target pointer has `p`'s; the statement relies on provenance monotonicity
(more provenance never introduces UB, `ToyProv.Monotone`). -/
theorem int2ptrToCopy_refines_exposed_of_intIsAddrOf_of_candSubProv
    (pre post : Prog) (d k p : Reg)
    (hk : AllAfter .exposed pre (intIsAddrOfC k p))
    (hc : AllAfter .exposed pre (candSubProvC p)) :
    Refines .exposed (pre ++ .copy d p :: post) (pre ++ .int2ptr d k :: post) := by
  let src := pre ++ .int2ptr d k :: post
  let tgt := pre ++ .copy d p :: post
  rw [Refines, beh_eq_of_after .exposed src, beh_eq_of_after .exposed tgt]
  cases hsrc : after .exposed src with
  | nil => left; simp
  | cons s_end s_rest =>
    right
    have hs_end : s_end ∈ execOk .exposed src init := by rw [← after_eq_execOk, hsrc]; simp
    rw [execOk_append, List.mem_flatMap] at hs_end
    rcases hs_end with ⟨s, hs, hs_step⟩
    rw [execOk_cons, List.mem_flatMap] at hs_step
    rcases hs_step with ⟨s₁, hs₁, hs_post⟩
    have hkp := hk s hs
    have hcp := hc s hs
    simp only [intIsAddrOfC] at hkp
    simp only [candSubProvC] at hcp
    cases hkreg : s.regs k with
    | none => simp [hkreg] at hkp
    | some vk =>
      cases vk with
      | ptr _ => simp [hkreg] at hkp
      | int a =>
        cases hpreg : s.regs p with
        | none => simp [hkreg, hpreg] at hkp
        | some vp =>
          cases vp with
          | int _ => simp [hkreg, hpreg] at hkp
          | ptr x =>
            simp only [hkreg, hpreg, beq_iff_eq] at hkp
            subst hkp
            simp only [hpreg, List.all_eq_true, decide_eq_true_eq] at hcp
            have hle₁ : StLE s₁ (s.setReg d (.ptr x)) := by
              rw [List.mem_filterMap] at hs₁
              rcases hs₁ with ⟨o, ho, ho_eq⟩
              cases o with
              | none => simp at ho_eq
              | some st =>
                simp only [id_eq, Option.some.injEq] at ho_eq; subst ho_eq
                simp only [step, hkreg, castToPtr] at ho
                cases hcand : candidates s x.addr with
                | nil =>
                  rw [hcand] at ho
                  simp at ho; subst ho
                  exact stLE_setReg (stLE_refl s) d ⟨rfl, Or.inl rfl⟩
                | cons c cs =>
                  rw [hcand] at ho
                  simp only [List.mem_map, Option.some.injEq] at ho
                  obtain ⟨id, hid, rfl⟩ := ho
                  have hid_mem : id ∈ candidates s x.addr := by rw [hcand]; exact hid
                  have hid_eq : some id = x.prov := hcp id hid_mem
                  exact stLE_setReg (stLE_refl s) d ⟨rfl, Or.inr hid_eq⟩
            obtain ⟨t_end, ht_post, hle_end⟩ :=
              execOk_mono (by decide) (by decide) (fun _ => rfl) hle₁ hs_post
            have ht_end_mem : t_end ∈ after .exposed tgt := by
              rw [after_eq_execOk, execOk_append, List.mem_flatMap]
              refine ⟨s, hs, ?_⟩
              rw [execOk_cons, List.mem_flatMap]
              refine ⟨s.setReg d (.ptr x), ?_, ht_post⟩
              simp [step, hpreg]
            have hcongr := exposed_beh_elements_equal tgt
            rw [beh_eq_of_after] at hcongr
            have ht_mem : Outcome.done s_end.out ∈
                (if (after .exposed tgt).isEmpty then [.ub]
                 else (after .exposed tgt).map (fun st => .done st.out)) := by
              cases hta : after .exposed tgt with
              | nil => rw [hta] at ht_end_mem; simp at ht_end_mem
              | cons t₀ trest =>
                simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.mem_map]
                exact ⟨t_end, by rwa [← hta], congrArg Outcome.done hle_end.2.2.1.symm⟩
            intro o ho
            have hoeq : o = Outcome.done s_end.out := hcongr o ho (.done s_end.out) ht_mem
            rw [hoeq]
            simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.mem_map]
            exact ⟨s_end, by simp, rfl⟩

/-- A exposed at 16; B exposed at 18. -/
def r2bPreK : Prog := [.alloc 0 2, .ptr2int 9 0, .alloc 1 2, .ptr2int 2 1]
def r2bPostK : Prog := [.const 4 7, .store 3 4, .load 5 .int 1, .obs 5]

/-- **R2b, `hk` needed.** `p` = A's start (its only candidate is A, so `hc` holds) but `k` is B's
address: the source picks B and outputs `[7]`, the target stores into A and then reads the
uninitialized B (UB). -/
theorem int2ptrToCopy_intIsAddrOf_needed :
    AllAfter .exposed r2bPreK (candSubProvC 0) ∧
      ¬ Refines .exposed (r2bPreK ++ .copy 3 0 :: r2bPostK) (r2bPreK ++ .int2ptr 3 2 :: r2bPostK) :=
  ⟨by decide, by decide⟩

/-- A and B adjacent; B exposed; `p := A + 2` and `k := (int)p` (which exposes A). -/
def r2bPreRT : Prog := [.alloc 0 2, .alloc 1 2, .ptr2int 9 1, .offset 2 0 2, .ptr2int 3 2]
def r2bPostRT : Prog := [.const 5 7, .store 4 5, .load 6 .int 1, .obs 6]

/-- **R2b, `hc` needed.** `k == (int)p` holds, and `p`'s own allocation A is live, exposed and
contains the address in its closed range, but B is a second candidate. The source's cast can
pick B and outputs `[7]`; the target keeps A's provenance and its store is UB. -/
theorem int2ptrToCopy_candSubProv_needed :
    AllAfter .exposed r2bPreRT (intIsAddrOfC 3 2) ∧ AllAfter .exposed r2bPreRT (provIsCandC 2) ∧
      ¬ Refines .exposed (r2bPreRT ++ .copy 4 2 :: r2bPostRT) (r2bPreRT ++ .int2ptr 4 3 :: r2bPostRT) :=
  ⟨by decide, by decide, by decide⟩

def r2bPreNV : Prog := [.alloc 0 2, .ptr2int 1 0]

/-- **R2b non-vacuity.** After `k := (int)A`, A is the only candidate for its address, and the
fold is behaviour-preserving on a continuation that stores through the result. -/
theorem int2ptrToCopy_refines_exposed_nonvacuous :
    AllAfter .exposed r2bPreNV (intIsAddrOfC 1 0) ∧ AllAfter .exposed r2bPreNV (candSubProvC 0) ∧
      Refines .exposed (r2bPreNV ++ .copy 2 0 :: [.const 3 5, .store 2 3, .load 4 .int 0, .obs 4])
        (r2bPreNV ++ .int2ptr 2 1 :: [.const 3 5, .store 2 3, .load 4 .int 0, .obs 4]) ∧
      beh .exposed (r2bPreNV ++ .int2ptr 2 1 :: [.const 3 5, .store 2 3, .load 4 .int 0, .obs 4]) =
        [.done [5]] :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- A (unexposed, at 16), B, C; `k := 16`; `q := int2ptr k` (no candidate, so no provenance) is
stored into B. -/
def r2bPreTorn : Prog := [.alloc 0 2, .alloc 1 2, .alloc 2 2, .const 3 16, .int2ptr 4 3, .store 1 4]
/-- Store `d` into C, copy B's first byte over C's first byte, load C at integer type. -/
def r2bPostTorn : Prog := [.store 2 5, .memcpy 2 1 1, .load 6 .int 2, .obs 6]

/-- **R2b, the case with no candidate.** A is not exposed, so `candidates` is empty and both side
conditions hold. The fold gives `d` A's provenance where the source's `int2ptr` gives none; C then
holds one fragment of a provenance-less pointer and one fragment of a pointer with provenance A,
both at address 16. Both programs output `[16]`. -/
theorem int2ptrToCopy_refines_exposed_no_candidate_example :
    AllAfter .exposed r2bPreTorn (intIsAddrOfC 3 0) ∧ AllAfter .exposed r2bPreTorn (candSubProvC 0) ∧
      AllAfter .exposed r2bPreTorn (fun s => (candidates s 16).isEmpty) ∧
      Refines .exposed (r2bPreTorn ++ .copy 5 0 :: r2bPostTorn) (r2bPreTorn ++ .int2ptr 5 3 :: r2bPostTorn) ∧
      beh .exposed (r2bPreTorn ++ .copy 5 0 :: r2bPostTorn) = [.done [16]] ∧
      beh .exposed (r2bPreTorn ++ .int2ptr 5 3 :: r2bPostTorn) = [.done [16]] :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

end Toy.Prov
