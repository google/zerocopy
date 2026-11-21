import ToyTbaa.Lemmas
import ToyTbaa.Examples

/-!
# Results: type-based alias analysis under effective-type and untyped memory

Every theorem in this file is fully proved.

Block notation used throughout: the *hoist* replacement turns `[store U q r, load s T p]`
into `[load s T p, store U q r]` (a load moved above an earlier store); the *sink*
replacement turns `[load s T p, store U q r]` into `[store U q r, load s T p]`; the
*store/store* replacement swaps two stores.
-/

namespace Toy.Tbaa
namespace Results

open Lemmas

/-- Four bytes of value `1`. -/
def ones4 : Val := [1, 1, 1, 1]

/-- Four bytes of value `2`. -/
def twos4 : Val := [2, 2, 2, 2]

/-! ## R1. TBAA soundness under (E): hoisting a load above an incompatible store -/

/-- **R1.** Under the effective-type semantics with the standard discipline: if neither `T`
nor `U` is the character type, `T` and `U` share no leaf scalar type, and the load's
destination register `s` differs from the store's source register `r`, then moving a `T`-load
from `p` above an earlier `U`-store to `q` is a refinement in every context, from every initial
state, and for every address pair `p, q`. -/
theorem hoist_load_above_store_sound_E_of_noCommonLeaf_of_ne_u8
    (T U : Ty) (p q : Nat) (s r : Reg)
    (hT : T ≠ .u8) (hU : U ≠ .u8) (hTU : NoCommonLeaf T U) (hsr : s ≠ r) :
    ReorderSound (stepE stdCfg) [.store U q r, .load s T p] [.load s T p, .store U q r] := by
  refine reorderSoundFrom_of_block (Inv := fun _ => True) (fun _ _ => trivial)
    (fun _ _ _ _ _ => trivial) ?_
  intro σ t _
  rcases block2_cases (stepE_store_noEmit _ U q r) (stepE_load_noEmit _ s T p) σ t with
    h | ⟨σ1, σ2, h1, h2, hrun⟩
  · exact Or.inl h
  · refine Or.inr ⟨σ2, hrun, ?_⟩
    obtain ⟨ds, hds, hv, hdok, rfl⟩ := stepE_store_next h1
    obtain ⟨cs, hcs, htok, rfl⟩ := stepE_load_next h2
    have hcs0 : readRange (updRange σ.mem q U.size (storeCell U (σ.regs r))) p T.size = some cs :=
      hcs
    have hdisj : RangesDisjoint p T.size q U.size := by
      refine Decidable.byContradiction fun hov => ?_
      obtain ⟨i, j, hi, hj, hij⟩ := exists_overlap (size_pos T) (size_pos U) hov
      have hcl : cs.length = T.size := readRange_length hcs0
      have hdl : ds.length = U.size := readRange_length hds
      have e1 := readRange_get hcs0 i (by omega)
      rw [hij, updRange_of_mem _ _ _ _ (by omega) (by omega), readRange_get hds j (by omega)] at e1
      simp only [Option.map, Option.some.injEq, Nat.add_sub_cancel_left] at e1
      have ht : stdCompat cs[i].eff.tag T.leaves[i] = true := tagsOk_get htok i (by omega) hi
      have hf := stored_tag_rejects hT hU hTU hi hj ds[j] (σ.regs r)
        (declOk_get hdok j (by omega) hj)
      rw [e1] at hf
      rw [hf] at ht
      cases ht
    have hcs' : readRange σ.mem p T.size = some cs := by
      rw [← readRange_updRange_disjoint σ.mem p T.size q U.size (storeCell U (σ.regs r)) hdisj]
      exact hcs0
    have hregs : updReg σ.regs s (cs.map Cell.val) r = σ.regs r := by
      simp [updReg, Ne.symm hsr]
    refine block2_ok (stepE_load_of hcs' htok) ?_
    have hv' : U.Valid ((({ σ with regs := updReg σ.regs s (cs.map Cell.val) } : St)).regs r) := by
      simpa [hregs] using hv
    rw [stepE_store_of (σ := { σ with regs := updReg σ.regs s (cs.map Cell.val) }) hds hv' hdok]
    simp [hregs]

/-- Non-vacuity of R1 (scalar instance): `T = f32, U = u32, p = 8, q = 0, s = 1, r = 0`
satisfies all hypotheses, and on it the source block is defined from a concrete state and the
target produces the same outcome. -/
theorem hoist_E_nonvacuous :
    Ty.f32 ≠ .u8 ∧ Ty.u32 ≠ .u8 ∧ NoCommonLeaf .f32 .u32 ∧ (1 : Reg) ≠ 0 ∧
    exec (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 8, .out 1] (freshAt 0 16 ones4) =
      .done [[0, 0, 0, 0]] ∧
    exec (stepE stdCfg) [.load 1 .f32 8, .store .u32 0 0, .out 1] (freshAt 0 16 ones4) =
      .done [[0, 0, 0, 0]] := by decide

/-- Non-vacuity of R1 (struct instance): a `pair` load hoisted above a `u16` store
(`T = pair, U = u16, p = 0, q = 8, s = 1, r = 0`) satisfies all hypotheses, and the source block
is defined from a concrete state with the target producing the same outcome. -/
theorem hoist_E_nonvacuous_struct :
    Ty.pair ≠ .u8 ∧ Ty.u16 ≠ .u8 ∧ NoCommonLeaf .pair .u16 ∧ (1 : Reg) ≠ 0 ∧
    exec (stepE stdCfg) [.store .u16 8 0, .load 1 .pair 0, .out 1] (freshAt 0 16 [1, 1]) =
      .done [[0, 0, 0, 0, 0, 0, 0, 0]] ∧
    exec (stepE stdCfg) [.load 1 .pair 0, .store .u16 8 0, .out 1] (freshAt 0 16 [1, 1]) =
      .done [[0, 0, 0, 0, 0, 0, 0, 0]] := by decide

/-- R1 tightness (`hT`), witness class: overlapping addresses `p = q = 0` on untyped allocated
storage. With a byte load (`T = u8`) all other hypotheses hold (`u32 ≠ u8`,
`NoCommonLeaf u8 u32`, `1 ≠ 0`) and the hoist is not sound. -/
theorem hoist_E_needs_load_ne_u8 :
    Ty.u32 ≠ .u8 ∧ NoCommonLeaf .u8 .u32 ∧ (1 : Reg) ≠ 0 ∧
    ¬ ReorderSound (stepE stdCfg) [.store .u32 0 0, .load 1 .u8 0] [.load 1 .u8 0, .store .u32 0 0] :=
  ⟨by decide, by decide, by decide,
   not_reorderSoundFrom_of [] [.out 1] (freshAt 0 16 ones4) trivial (by decide)⟩

/-- R1 tightness (`hU`), witness class: overlapping addresses `p = q = 0` on untyped allocated
storage with no effective type yet. With a byte store (`U = u8`) all other hypotheses hold and
the hoist is not sound: the later `u32` load is defined and sees the new byte. -/
theorem hoist_E_needs_store_ne_u8 :
    Ty.u32 ≠ .u8 ∧ NoCommonLeaf .u32 .u8 ∧ (1 : Reg) ≠ 0 ∧
    ¬ ReorderSound (stepE stdCfg) [.store .u8 0 0, .load 1 .u32 0] [.load 1 .u32 0, .store .u8 0 0] :=
  ⟨by decide, by decide, by decide,
   not_reorderSoundFrom_of [] [.out 1] (freshAt 0 16 [1]) trivial (by decide)⟩

/-- R1 tightness (`hU`), second witness class: overlapping addresses `p = q = 0` on a declared
`u32` object. All other hypotheses hold, the witness state `declSt .u32 4 [1]` is declared on
the load's range, and the hoist is not sound even from the states declared on that range (so
not sound from all states either). A byte store never changes a declared byte's type, so this
witness does not depend on how byte stores update the tags of allocated storage. -/
theorem hoist_E_needs_store_ne_u8_on_declared :
    Ty.u32 ≠ .u8 ∧ NoCommonLeaf .u32 .u8 ∧ (1 : Reg) ≠ 0 ∧
    DeclaredOn (declSt .u32 4 [1]) 0 Ty.u32.size ∧
    ¬ ReorderSoundFrom (fun σ => DeclaredOn σ 0 Ty.u32.size) (stepE stdCfg)
        [.store .u8 0 0, .load 1 .u32 0] [.load 1 .u32 0, .store .u8 0 0] ∧
    ¬ ReorderSound (stepE stdCfg) [.store .u8 0 0, .load 1 .u32 0] [.load 1 .u32 0, .store .u8 0 0] := by
  have hD : DeclaredOn (declSt .u32 4 [1]) 0 Ty.u32.size := by decide
  have hF : ¬ ReorderSoundFrom (fun σ => DeclaredOn σ 0 Ty.u32.size) (stepE stdCfg)
      [.store .u8 0 0, .load 1 .u32 0] [.load 1 .u32 0, .store .u8 0 0] :=
    not_reorderSoundFrom_of [] [.out 1] (declSt .u32 4 [1]) hD (by decide)
  exact ⟨by decide, by decide, by decide, hD, hF, fun h => hF (h.from _)⟩

/-- R1 tightness (`hTU`), witness class: overlapping addresses `p = q = 0` on untyped allocated
storage. `T = pair`, `U = u32` are distinct non-character types (so a "`T ≠ U`" criterion would
accept them), every other hypothesis holds, and the hoist is not sound: a `pair` load may read a
`u32` member just stored. -/
theorem hoist_E_needs_noCommonLeaf :
    Ty.pair ≠ .u32 ∧ Ty.pair ≠ .u8 ∧ Ty.u32 ≠ .u8 ∧ (1 : Reg) ≠ 0 ∧ ¬ NoCommonLeaf .pair .u32 ∧
    ¬ ReorderSound (stepE stdCfg) [.store .u32 0 0, .load 1 .pair 0] [.load 1 .pair 0, .store .u32 0 0] :=
  ⟨by decide, by decide, by decide, by decide, by decide,
   not_reorderSoundFrom_of [] [.out 1] (freshAt 0 16 ones4) trivial (by decide)⟩

/-- R1 tightness (`hsr`), witness class: disjoint addresses `p = 8, q = 0` on untyped allocated
storage. If the load overwrites the register the store reads (`s = r = 0`), all type hypotheses
hold and the hoist is not sound. -/
theorem hoist_E_needs_distinct_registers :
    Ty.f32 ≠ .u8 ∧ Ty.u32 ≠ .u8 ∧ NoCommonLeaf .f32 .u32 ∧
    ¬ ReorderSound (stepE stdCfg) [.store .u32 0 0, .load 0 .f32 8] [.load 0 .f32 8, .store .u32 0 0] :=
  ⟨by decide, by decide, by decide,
   not_reorderSoundFrom_of [] [.load 2 .u8 0, .out 2] (freshAt 0 16 ones4) trivial (by decide)⟩

/-! ## R1b, R1c. What R1 does not extend to under allocated storage -/

/-- **R1b (counterexample).** All hypotheses of R1 hold for `T = u32, U = f32, s = 1, r = 0`,
yet moving the load *below* the store (sink) is not sound under (E): on allocated storage the
`f32` store legitimately changes the bytes' effective type after the source's `u32` load. -/
theorem sink_load_below_store_not_sound_E :
    Ty.u32 ≠ .u8 ∧ Ty.f32 ≠ .u8 ∧ NoCommonLeaf .u32 .f32 ∧ (1 : Reg) ≠ 0 ∧
    ¬ ReorderSound (stepE stdCfg) [.load 1 .u32 0, .store .f32 0 0] [.store .f32 0 0, .load 1 .u32 0] :=
  ⟨by decide, by decide, by decide, by decide,
   not_reorderSoundFrom_of [] [.out 1] (freshAt 0 16 ones4) trivial (by decide)⟩

/-- **R1c (counterexample).** Swapping a `u32` store and an `f32` store to the same allocated
bytes is not sound under (E), although the types are non-character and share no leaf. -/
theorem store_store_reorder_not_sound_E :
    Ty.u32 ≠ .u8 ∧ Ty.f32 ≠ .u8 ∧ NoCommonLeaf .u32 .f32 ∧
    ¬ ReorderSound (stepE stdCfg) [.store .u32 0 0, .store .f32 0 1] [.store .f32 0 1, .store .u32 0 0] :=
  ⟨by decide, by decide, by decide,
   not_reorderSoundFrom_of [] [.load 2 .u8 0, .out 2] ((freshAt 0 16 []).withRegs (regs2 ones4 twos4))
     trivial (by decide)⟩

/-! ## R2. TBAA is unsound under (U) -/

/-- Witness state for R2: sixteen allocated zero bytes at `p..p+15` (untyped), every register
holding `U.size` bytes of value `1`. -/
def uWit (U : Ty) (p : Nat) : USt := erase (freshAt p 16 (List.replicate U.size 1))

theorem uWit_mem (U : Ty) (p a : Nat) (h1 : p ≤ a) (h2 : a < p + 16) :
    (uWit U p).mem a = some 0 := by
  simp [uWit, erase, freshAt, h1, h2]

theorem uWit_read (U T : Ty) (p : Nat) :
    readRange (uWit U p).mem p T.size = some (List.replicate T.size 0) :=
  readRange_const (fun i hi => uWit_mem U p (p + i) (by omega) (by have := size_le_eight T; omega))

/-- After a `U`-store of `U.size` bytes of value `1` to `p` in `uWit U p`, a `T`-read from `p`
succeeds and its first byte is `1`. -/
theorem uWit_read_after_store (U T : Ty) (p : Nat) :
    ∃ bs, readRange (updRange (uWit U p).mem p U.size
        (fun i _ => (List.replicate U.size 1).getD i 0)) p T.size = some bs ∧ bs[0]? = some 1 := by
  have hsome : (readRange (updRange (uWit U p).mem p U.size
      (fun i _ => (List.replicate U.size 1).getD i 0)) p T.size).isSome := by
    apply readRange_isSome
    intro i hi
    rw [updRange_isSome, uWit_mem U p (p + i) (by omega) (by have := size_le_eight T; omega)]
    rfl
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨bs, hbs, ?_⟩
  have hl : bs.length = T.size := readRange_length hbs
  have hpos := size_pos T
  have e := readRange_get hbs 0 (by omega)
  have hU := size_pos U
  rw [Nat.add_zero, updRange_of_mem _ _ _ _ (Nat.le_refl p) (by omega),
    uWit_mem U p p (Nat.le_refl p) (by omega)] at e
  simp only [Option.map, Nat.sub_self, Option.some.injEq] at e
  rw [List.getElem?_eq_getElem (by omega), ← e]
  simp [List.getD_eq_getElem?_getD, hU]

/-- **R2 (impossibility).** Under the untyped semantics, for all types `T` and `U` (with no
condition relating them) and every address `p`:
(1) from the witness state `uWit U p`, the target `[load 1 T p, store U p 0, out 1]` has the
behaviour "print `T.size` zero bytes", which the source `[store U p 0, load 1 T p, out 1]`
lacks; and (2) for all registers `s, r`, hoisting a `T`-load from `p` above a `U`-store to the
same address `p` is not a refinement. -/
theorem hoist_load_above_store_same_addr_unsound_U (T U : Ty) (p : Nat) :
    (Beh stepU [.load 1 T p, .store U p 0, .out 1] (uWit U p) (.done [List.replicate T.size 0]) ∧
     ¬ Beh stepU [.store U p 0, .load 1 T p, .out 1] (uWit U p) (.done [List.replicate T.size 0])) ∧
    ∀ s r : Reg, ¬ ReorderSound stepU [.store U p r, .load s T p] [.load s T p, .store U p r] := by
  obtain ⟨bs, hbs, hb0⟩ := uWit_read_after_store U T p
  have hz := uWit_read U T p
  have hzU := uWit_read U U p
  have hpos := size_pos T
  have hne : List.replicate T.size 0 ≠ bs := by
    intro h; rw [← h] at hb0; simp [hpos] at hb0
  have hvU : U.Valid (List.replicate U.size 1) := by simp [Ty.Valid]
  have hsome : (readRange (uWit U p).mem p U.size).isSome := by rw [hzU]; rfl
  -- memory after the store, and the register file of the witness state
  let M : UMem := updRange (uWit U p).mem p U.size (fun i _ => (List.replicate U.size 1).getD i 0)
  let R : Reg → Val := (uWit U p).regs
  have hR : ∀ x, R x = List.replicate U.size 1 := fun _ => rfl
  -- the source run, for any registers `s, r`
  have hsrc : ∀ s r : Reg,
      exec stepU [.store U p r, .load s T p, .out s] (uWit U p) = .done [bs] := by
    intro s r
    have h1 : stepU (.store U p r) (uWit U p) = .next ⟨M, R⟩ :=
      stepU_store_of (T := U) (p := p) (r := r) (u := uWit U p) hsome hvU
    have h2 : stepU (.load s T p) ⟨M, R⟩ = .next ⟨M, updReg R s bs⟩ := stepU_load_of hbs
    unfold exec
    rw [runFrom_cons_next h1, runFrom_cons_next h2, runFrom_cons_emit rfl]
    simp [runFrom, Final.outcome, updReg]
  -- the target run, for any registers `s, r`
  have htgt : ∀ s r : Reg,
      exec stepU [.load s T p, .store U p r, .out s] (uWit U p) = .done [List.replicate T.size 0] ∨
      exec stepU [.load s T p, .store U p r, .out s] (uWit U p) = .ub [] := by
    intro s r
    have h1 : stepU (.load s T p) (uWit U p) = .next ⟨(uWit U p).mem,
        updReg R s (List.replicate T.size 0)⟩ := stepU_load_of hz
    unfold exec
    rw [runFrom_cons_next h1]
    by_cases hv : U.Valid (updReg R s (List.replicate T.size 0) r)
    · have h2 := stepU_store_of (T := U) (p := p) (r := r)
        (u := ⟨(uWit U p).mem, updReg R s (List.replicate T.size 0)⟩) hsome hv
      rw [runFrom_cons_next h2, runFrom_cons_emit rfl]
      left; simp [runFrom, Final.outcome, updReg]
    · have h2 := stepU_store_invalid (T := U) (p := p) (r := r)
        (u := ⟨(uWit U p).mem, updReg R s (List.replicate T.size 0)⟩) hv
      rw [runFrom_cons_fault h2]
      right; rfl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show Allows _ _
    rcases htgt 1 0 with h | h
    · rw [h]; rfl
    · have h1 : stepU (.load 1 T p) (uWit U p) = .next ⟨(uWit U p).mem,
          updReg R 1 (List.replicate T.size 0)⟩ := stepU_load_of hz
      have hv : U.Valid (updReg R 1 (List.replicate T.size 0) 0) := by
        simpa [updReg, hR] using hvU
      have h2 := stepU_store_of (T := U) (p := p) (r := 0)
        (u := ⟨(uWit U p).mem, updReg R 1 (List.replicate T.size 0)⟩) hsome hv
      unfold exec at h
      rw [runFrom_cons_next h1, runFrom_cons_next h2, runFrom_cons_emit rfl] at h
      simp [runFrom, Final.outcome] at h
  · show ¬ Allows _ _
    rw [hsrc 1 0]
    simp only [Allows, Outcome.done.injEq, List.cons.injEq, and_true]
    exact hne
  · intro s r H
    apply not_reorderSoundFrom_of [] [.out s] (uWit U p) trivial ?_ H
    simp only [List.nil_append, List.cons_append]
    rw [hsrc s r]
    rcases htgt s r with h | h <;> rw [h]
    · simp only [Allows, Outcome.done.injEq, List.cons.injEq, and_true]; exact hne
    · simp [Allows]

/-- Consequence of R2: let `C` be a criterion on the pair of access types. If, whenever `C T U`
holds, hoisting a `T`-load above a `U`-store to the same address is a refinement under the
untyped semantics for every address `p` and every pair of distinct registers `s ≠ r` (the
register condition under which R1 and R6 license hoists), then `C` holds for no pair of types. -/
theorem no_type_criterion_licenses_same_addr_hoist_U (C : Ty → Ty → Prop)
    (hC : ∀ T U p s r, C T U → s ≠ r →
      ReorderSound stepU [.store U p r, .load s T p] [.load s T p, .store U p r]) :
    ∀ T U, ¬ C T U :=
  fun T U hTU =>
    (hoist_load_above_store_same_addr_unsound_U T U 0).2 1 0 (hC T U 0 1 0 hTU (by decide))

/-- Strengthening of `no_type_criterion_licenses_same_addr_hoist_U` with a weaker premise: let
`C` be a criterion on the pair of access types. If, whenever `C T U` holds, there is at least one
address `p` and one pair of registers `s, r` at which hoisting a `T`-load above a `U`-store to
the same address `p` is a refinement under the untyped semantics, then `C` holds for no pair of
types. -/
theorem no_type_criterion_licenses_same_addr_hoist_U_at_one_site (C : Ty → Ty → Prop)
    (hC : ∀ T U, C T U → ∃ p s r,
      ReorderSound stepU [.store U p r, .load s T p] [.load s T p, .store U p r]) :
    ∀ T U, ¬ C T U :=
  fun T U hTU =>
    let ⟨p, s, r, h⟩ := hC T U hTU
    (hoist_load_above_store_same_addr_unsound_U T U p).2 s r h

/-- Tightness of the premise `hC` of `no_type_criterion_licenses_same_addr_hoist_U`, witness
class: the criterion `C := fun _ _ => True` (accept every pair). The theorem has no other
hypothesis; for this criterion the conclusion `∀ T U, ¬ C T U` fails (and, as the theorem
requires, `hC` fails too). -/
theorem no_type_criterion_needs_premise :
    ¬ (∀ T U p s r, (fun _ _ : Ty => True) T U → s ≠ r →
        ReorderSound stepU [.store U p r, .load s T p] [.load s T p, .store U p r]) ∧
    ¬ (∀ T U : Ty, ¬ (fun _ _ : Ty => True) T U) :=
  ⟨fun h => (hoist_load_above_store_same_addr_unsound_U .f32 .u32 0).2 1 0
      (h .f32 .u32 0 1 0 trivial (by decide)),
   fun h => h .u32 .f32 trivial⟩

/-- Tightness of the premise `hC` of `no_type_criterion_licenses_same_addr_hoist_U_at_one_site`,
witness class: the criterion `C := fun _ _ => True`. The theorem has no other hypothesis; for
this criterion the conclusion fails (and, as the theorem requires, `hC` fails too). -/
theorem no_type_criterion_at_one_site_needs_premise :
    ¬ (∀ T U, (fun _ _ : Ty => True) T U → ∃ p s r,
        ReorderSound stepU [.store U p r, .load s T p] [.load s T p, .store U p r]) ∧
    ¬ (∀ T U : Ty, ¬ (fun _ _ : Ty => True) T U) :=
  ⟨fun h =>
     let ⟨p, s, r, hs⟩ := h .f32 .u32 trivial
     (hoist_load_above_store_same_addr_unsound_U .f32 .u32 p).2 s r hs,
   fun h => h .u32 .f32 trivial⟩

/-- Without the register condition `s ≠ r`, a premise of the shape of `hC` would refute every
criterion through register clobbering alone, at an address pair where R6 licenses the hoist for
distinct registers: at disjoint addresses (load from `8`, store to `0`) with `s = r = 0` the
hoist is not sound under the untyped semantics for any pair of types, because the load
overwrites the register the store reads. -/
theorem same_register_premise_refutes_disjoint_hoist_U (C : Ty → Ty → Prop)
    (hC : ∀ T U s r, C T U →
      ReorderSound stepU [.store U 0 r, .load s T 8] [.load s T 8, .store U 0 r]) :
    ∀ T U, ¬ C T U := by
  intro T U hTU
  have hunsound : ¬ ReorderSound stepU [.store U 0 0, .load 0 T 8] [.load 0 T 8, .store U 0 0] := by
    apply not_reorderSoundFrom_of [] [.load 2 .u8 0, .out 2] (uWit U 0) trivial
    cases T <;> cases U <;> decide
  exact hunsound (hC T U 0 0 hTU)

/-- Non-vacuity of the premises of `no_type_criterion_licenses_same_addr_hoist_U` and
`no_type_criterion_licenses_same_addr_hoist_U_at_one_site`: the empty criterion
`C := fun _ _ => False` satisfies both premises. By those theorems, every criterion satisfying
either premise holds for no pair of types. -/
theorem no_type_criterion_premises_satisfiable :
    (∀ T U p s r, (fun _ _ : Ty => False) T U → s ≠ r →
        ReorderSound stepU [.store U p r, .load s T p] [.load s T p, .store U p r]) ∧
    (∀ T U, (fun _ _ : Ty => False) T U → ∃ p s r,
        ReorderSound stepU [.store U p r, .load s T p] [.load s T p, .store U p r]) :=
  ⟨fun _ _ _ _ _ h => h.elim, fun _ _ h => h.elim⟩

/-- Non-vacuity / instance of R2 for the TBAA-relevant pair `T = f32, U = u32` at `p = 0`. -/
theorem hoist_unsound_U_instance :
    Beh stepU [.load 1 .f32 0, .store .u32 0 0, .out 1] (uWit .u32 0) (.done [[0, 0, 0, 0]]) ∧
    ¬ Beh stepU [.store .u32 0 0, .load 1 .f32 0, .out 1] (uWit .u32 0) (.done [[0, 0, 0, 0]]) := by
  decide

/-- Positive control for R2: the same programs from the same bytes (now as allocated storage
with no effective type) under the effective-type semantics: the hoist *is* a refinement there,
because the source's `f32` load of freshly `u32`-typed bytes is undefined. And under (U) the
hoist is a refinement when the load reads a disjoint range. -/
theorem hoist_U_witness_refines_under_E_or_disjoint :
    Refines (Beh (stepE stdCfg) [.load 1 .f32 0, .store .u32 0 0, .out 1] (freshAt 0 16 ones4))
            (Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .out 1] (freshAt 0 16 ones4)) ∧
    Refines (Beh stepU [.load 1 .f32 8, .store .u32 0 0, .out 1] (uWit .u32 0))
            (Beh stepU [.store .u32 0 0, .load 1 .f32 8, .out 1] (uWit .u32 0)) :=
  ⟨(refines_beh_iff _ _ _ _).2 (by decide), (refines_beh_iff _ _ _ _).2 (by decide)⟩

/-! ## R3a. `memcpy` then typed load: exact condition -/

/-- **R3a (characterization).** Under (E) with the standard discipline, for every state, type,
source `p`, destination `q` (overlap allowed) and register `s`: `memcpy q p T.size` followed by
a `T`-load from `q` and `out s` terminates normally, printing exactly the bytes that were at
`p`, if and only if `MemcpyLoadOk σ T p q` holds (both ranges allocated; at each byte offset,
the destination's declared leaf if that destination byte is declared, and otherwise the source
byte's tag, is compatible with `T`'s leaf). -/
theorem memcpy_then_typed_load_defined_E_iff (σ : St) (T : Ty) (p q : Nat) (s : Reg) :
    exec (stepE stdCfg) [.memcpy q p T.size, .load s T q, .out s] σ = .done [valsAt σ p T.size] ↔
      MemcpyLoadOk σ T p q := by
  unfold exec MemcpyLoadOk
  dsimp [runFrom, stepE, stdCfg]
  cases hsrc : readRange σ.mem p T.size with
  | none => simp [Final.outcome]
  | some cs =>
    cases hdst : readRange σ.mem q T.size with
    | none => simp [Final.outcome]
    | some ds =>
      dsimp only
      have hcb : (!true || CopyBytesOk stdCompat cs ds) = true := by
        simp [copyBytesOk_stdCompat]
      rw [hcb]; simp only [ite_true]
      have hcs_len : cs.length = T.size := readRange_length hsrc
      have hds_len : ds.length = T.size := readRange_length hdst
      have hrr_after := readRange_updRange_copyFrom σ.mem q 0 T.size cs ds
        (by simpa using hdst) (by simpa using hcs_len)
      simp only [Nat.add_zero, Nat.zero_add, List.drop_zero] at hrr_after
      rw [hrr_after]
      have hvals : (List.zipWith copyCell cs ds).map Cell.val = cs.map Cell.val :=
        zipWith_copyCell_val cs ds (by omega)
      have hv : T.Valid ((List.zipWith copyCell cs ds).map Cell.val) := by
        unfold Ty.Valid; rw [hvals, List.length_map]; exact hcs_len
      simp only [hv, ite_true]
      have htok_eq : TagsOk stdCompat (List.zipWith copyCell cs ds) T =
          ((cs.zip ds).zip T.leaves).all memcpyLoadCheck :=
        tagsOk_zipWith_copyCell cs ds T.leaves hcs_len hds_len
      rw [htok_eq]
      cases hcond : ((cs.zip ds).zip T.leaves).all memcpyLoadCheck
      · constructor
        · intro h; cases h
        · intro ⟨_, _, h1, h2, h3⟩; cases h1; cases h2; rw [hcond] at h3; cases h3
      · constructor
        · intro _; exact ⟨cs, ds, rfl, rfl, hcond⟩
        · intro _; simp [updReg, Final.outcome, valsAt, hsrc, hvals]

/-- The familiar sufficient condition, as a corollary of R3a: if a `T`-load from `p` would pass
the allocation and effective-type checks and every byte of `[q, q + T.size)` is allocated and
(if declared) accepts `T`, then `memcpy q p T.size` followed by a `T`-load from `q` is defined
and returns the bytes that were at `p`. -/
theorem memcpy_then_typed_load_defined_E_of_readable_of_receives (σ : St) (T : Ty) (p q : Nat)
    (s : Reg) (hsrc : ReadableAt stdCompat σ T p) (hdst : ReceivesAt σ T q) :
    exec (stepE stdCfg) [.memcpy q p T.size, .load s T q, .out s] σ = .done [valsAt σ p T.size] := by
  rw [memcpy_then_typed_load_defined_E_iff]
  obtain ⟨cs, hcs, htok⟩ := hsrc
  obtain ⟨ds, hds, hdok⟩ := hdst
  refine ⟨cs, ds, hcs, hds, ?_⟩
  have hcl : cs.length = T.size := readRange_length hcs
  have hdl : ds.length = T.size := readRange_length hds
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hx
  have hn1 : n < cs.length := by simp [List.length_zip] at hn; omega
  have hn2 : n < ds.length := by simp [List.length_zip] at hn; omega
  have hn3 : n < T.leaves.length := by simp [List.length_zip] at hn; omega
  simp only [List.getElem_zip, memcpyLoadCheck]
  have h1 := tagsOk_get htok n hn1 hn3
  have h2 := declOk_get hdok n hn2 hn3
  cases he : ds[n].eff with
  | decl d => rw [he] at h2; exact h2
  | alloc _ => exact h1

/-- Non-vacuity of R3a, both sides: the condition holds (and the run is defined) for copying
the `u32` object of `objSt .u32` into untyped storage at `8`, and for `memcpy` punning of an
`f32` object into a declared `u32` object; it fails (and the run is undefined) for copying an
`f32` object into allocated storage and loading the copy at `u32`. -/
theorem memcpy_then_load_nonvacuous :
    MemcpyLoadOk (objSt .u32) .u32 0 8 ∧
    exec (stepE stdCfg) [.memcpy 8 0 4, .load 1 .u32 8, .out 1] (objSt .u32) = .done [[0, 0, 0, 0]] ∧
    MemcpyLoadOk Examples.punIntoDeclSt .u32 0 8 ∧
    exec (stepE stdCfg) [.memcpy 8 0 4, .load 1 .u32 8, .out 1] Examples.punIntoDeclSt =
      .done [[1, 1, 1, 1]] ∧
    ¬ MemcpyLoadOk (objSt .f32) .u32 0 8 ∧
    exec (stepE stdCfg) [.memcpy 8 0 4, .load 1 .u32 8, .out 1] (objSt .f32) = .ub [] := by
  decide

/-- Non-vacuity of the corollary: the `u32` object of `objSt .u32` is readable at `u32` and the
untyped storage at `8` receives a `u32`. -/
theorem memcpy_corollary_nonvacuous :
    ReadableAt stdCompat (objSt .u32) .u32 0 ∧ ReceivesAt (objSt .u32) .u32 8 := by decide

/-- The sufficient condition of the corollary does not cover `memcpy` punning into a declared
object: there the source is not readable at the destination's type, yet the run is defined. -/
theorem readable_source_not_necessary :
    ¬ ReadableAt stdCompat Examples.punIntoDeclSt .u32 0 ∧ ReceivesAt Examples.punIntoDeclSt .u32 8 ∧
    exec (stepE stdCfg) [.memcpy 8 0 4, .load 1 .u32 8, .out 1] Examples.punIntoDeclSt =
      .done [valsAt Examples.punIntoDeclSt 0 4] := by
  decide

/-- Corollary tightness (`hsrc`), witness class: an `f32` object copied into allocated storage.
The destination hypothesis holds and the conclusion fails (the run is undefined: the copy
carries the `f32` type). -/
theorem memcpy_then_load_needs_readable_source :
    ¬ ReadableAt stdCompat (objSt .f32) .u32 0 ∧ ReceivesAt (objSt .f32) .u32 8 ∧
    exec (stepE stdCfg) [.memcpy 8 0 4, .load 1 .u32 8, .out 1] (objSt .f32) ≠
      .done [valsAt (objSt .f32) 0 4] := by
  decide

/-- State for the `hdst` counterexample: a `u32` object at `0..3`, a declared `f32` object at
`8..11`. -/
def copyIntoDeclF32 : St :=
  ⟨fun a => if a < 4 then some ⟨0, .alloc (some .u32)⟩
            else if 8 ≤ a ∧ a < 12 then some ⟨0, .decl .f32⟩ else none,
   fun _ => ones4⟩

/-- Corollary tightness (`hdst`), witness class: a `u32` object copied into a declared `f32`
object. The source hypothesis holds and the conclusion fails (the run is undefined). -/
theorem memcpy_then_load_needs_receiving_destination :
    ReadableAt stdCompat copyIntoDeclF32 .u32 0 ∧ ¬ ReceivesAt copyIntoDeclF32 .u32 8 ∧
    exec (stepE stdCfg) [.memcpy 8 0 4, .load 1 .u32 8, .out 1] copyIntoDeclF32 ≠
      .done [valsAt copyIntoDeclF32 0 4] := by
  decide

/-- State for the overlapping-copy examples: allocated storage tagged `f32` with value `7` at
`0..1`, a declared `u32` object with value `9` at `2..5`. -/
def partialOverlapPunSt : St :=
  ⟨fun a => if a < 2 then some ⟨7, .alloc (some .f32)⟩
            else if a < 6 then some ⟨9, .decl .u32⟩ else none,
   fun _ => []⟩

/-- The toy's `memcpy` reads all source bytes before writing (the semantics of C's `memmove`),
so copies between overlapping ranges are defined in the toy: copying `[0, 4)` to `[2, 6)` and
loading the destination at `u32` prints the original source bytes `[7, 7, 9, 9]` under both
semantics (a forward byte-by-byte copy would print `[7, 7, 7, 7]`), `MemcpyLoadOk` holds there,
and a self-copy (`p = q = 0`) is defined as well. -/
theorem memcpy_overlap_defined_examples :
    MemcpyLoadOk partialOverlapPunSt .u32 0 2 ∧
    exec (stepE stdCfg) [.memcpy 2 0 Ty.u32.size, .load 1 .u32 2, .out 1] partialOverlapPunSt =
      .done [[7, 7, 9, 9]] ∧
    exec stepU [.memcpy 2 0 Ty.u32.size, .load 1 .u32 2, .out 1] (erase partialOverlapPunSt) =
      .done [[7, 7, 9, 9]] ∧
    valsAt partialOverlapPunSt 0 4 = [7, 7, 9, 9] ∧
    MemcpyLoadOk (objSt .u16) .u16 0 0 ∧
    exec (stepE stdCfg) [.memcpy 0 0 Ty.u16.size, .load 0 .u16 0, .out 0] (objSt .u16) =
      .done [[0, 0]] := by
  decide

/-! ## R3b. Byte-access copy defined forces the byte-load hoist to be unsound -/

/-- **R3b (impossibility).** For every compatibility discipline `c`, with `memcpy` performing
its byte accesses under `c`, and every type `T`: if byte-wise copying the `T`-object of
`objSt T` (to the untyped storage at `8`) is defined, then, from the initial state `objSt T`
with suffix `out 1`, moving a byte (`u8`) load of address `0` above a `T`-store to address `0`
is not a refinement. (For `T = u8` this is a same-type reordering; the cross-type reading is
`T ≠ u8`.) -/
theorem byte_copy_defined_forces_byte_hoist_unsound (c : Compat) (T : Ty)
    (hcopy : exec (stepE ⟨c, true⟩) [.memcpy 8 0 T.size] (objSt T) = .done []) :
    ¬ Refines (Beh (stepE ⟨c, true⟩) [.load 1 .u8 0, .store T 0 0, .out 1] (objSt T))
              (Beh (stepE ⟨c, true⟩) [.store T 0 0, .load 1 .u8 0, .out 1] (objSt T)) := by
  rw [refines_beh_iff]
  cases hc_u8 : c (some .u8) .u8 <;>
    cases hc_u32 : c (some .u32) .u8 <;>
    cases hc_f32 : c (some .f32) .u8 <;>
    cases hc_u16 : c (some .u16) .u8 <;>
    cases T <;>
    simp [exec, runFrom, stepE, objSt, readRange, updRange, CopyBytesOk, TagsOk, DeclOk,
          storeCell, Ty.size, Ty.leaves, Ty.leafAt, Ty.Valid, Eff.tag,
          Allows, Final.outcome, updReg, hc_u8, hc_u32, hc_f32, hc_u16] at hcopy ⊢

/-- Non-vacuity of R3b (cross-type instances): with the standard (exempting) discipline the
copies of the `u32` and `pair` objects are defined. -/
theorem byte_copy_defined_nonvacuous :
    exec (stepE stdCfg) [.memcpy 8 0 Ty.u32.size] (objSt .u32) = .done [] ∧
    exec (stepE stdCfg) [.memcpy 8 0 Ty.pair.size] (objSt .pair) = .done [] := by decide

/-- Positive control for R3b: if `memcpy` bypassed the effective-type checks (a copy
primitive not made of byte accesses), the strict discipline would have *both* a defined copy
and a sound hoist at the same witnesses. So R3b depends on `memcpy` being a byte-access copy. -/
theorem byte_hoist_refines_with_unchecked_memcpy :
    exec (stepE ⟨strictCompat, false⟩) [.memcpy 8 0 Ty.u32.size] (objSt .u32) = .done [] ∧
    Refines (Beh (stepE ⟨strictCompat, false⟩) [.load 1 .u8 0, .store .u32 0 0, .out 1] (objSt .u32))
            (Beh (stepE ⟨strictCompat, false⟩) [.store .u32 0 0, .load 1 .u8 0, .out 1] (objSt .u32)) :=
  ⟨by decide, (refines_beh_iff _ _ _ _).2 (by decide)⟩

/-- The other horn of R3b is reachable: under `strictCompat` (byte accesses checked) the copy is
undefined and the byte hoist is a refinement at the witnesses. -/
theorem strict_copy_ub_and_byte_hoist_refines :
    exec (stepE ⟨strictCompat, true⟩) [.memcpy 8 0 Ty.u32.size] (objSt .u32) = .ub [] ∧
    Refines (Beh (stepE ⟨strictCompat, true⟩) [.load 1 .u8 0, .store .u32 0 0, .out 1] (objSt .u32))
            (Beh (stepE ⟨strictCompat, true⟩) [.store .u32 0 0, .load 1 .u8 0, .out 1] (objSt .u32)) :=
  ⟨by decide, (refines_beh_iff _ _ _ _).2 (by decide)⟩

/-- Under `strictCompat` the opposite reordering (a `u32` load hoisted above a `u8` store to the
same allocated bytes) is still not a refinement: byte stores keep the tags of allocated storage
under every discipline, so the strict discipline does not make byte stores non-aliasing with
typed loads. -/
theorem strict_typed_load_above_byte_store_not_refines :
    ¬ Refines (Beh (stepE ⟨strictCompat, true⟩) [.load 1 .u32 0, .store .u8 0 0, .out 1]
                ((objSt .u32).withRegs (regs2 [1] ones4)))
              (Beh (stepE ⟨strictCompat, true⟩) [.store .u8 0 0, .load 1 .u32 0, .out 1]
                ((objSt .u32).withRegs (regs2 [1] ones4))) :=
  fun h => absurd ((refines_allows_iff _ _).1 h) (by decide)

/-- For `T = u8` under the strict discipline the copy is defined and the refuted reordering is
a same-type `u8`/`u8` one; storing a `u8` into fresh allocated storage does not produce the
`u8` tag that `objSt u8` carries. -/
theorem byte_copy_u8_case_is_same_type :
    exec (stepE ⟨strictCompat, true⟩) [.memcpy 8 0 Ty.u8.size] (objSt .u8) = .done [] ∧
    (match stepE stdCfg (.store .u8 0 0) (freshAt 0 16 [0]) with
     | .next σ' => decide (σ'.mem 0 = (objSt .u8).mem 0)
     | _ => false) = false := by
  decide

/-- A discipline that exempts byte reads of `u32` bytes but not of `f32` bytes (used only to
show that the two horns of R3b are not exclusive). -/
def mixedCompat : Compat
  | some .f32, .u8 => false
  | t, s => stdCompat t s

/-- Boundary for R3b: the horns are not exclusive. Under `mixedCompat`, copying the `pair`
object is undefined *and* moving a byte load above a `pair` store is not a refinement. So
"copy undefined" does not imply "byte hoist sound" for types with several leaf types. -/
theorem byte_dichotomy_not_exclusive_for_pair :
    exec (stepE ⟨mixedCompat, true⟩) [.memcpy 8 0 Ty.pair.size] (objSt .pair) = .ub [] ∧
    ¬ Refines (Beh (stepE ⟨mixedCompat, true⟩) [.load 1 .u8 0, .store .pair 0 0, .out 1] (objSt .pair))
              (Beh (stepE ⟨mixedCompat, true⟩) [.store .pair 0 0, .load 1 .u8 0, .out 1] (objSt .pair)) :=
  ⟨by decide, fun h => absurd ((refines_allows_iff _ _).1 h) (by decide)⟩

/-! ## R4. The agreement boundary between (E) and (U) -/

/-- **R4a.** For every configuration, program and initial state: if the effective-type
execution does not stop at a `type` fault (`¬ TypeFaults`), its behaviours equal those of the
untyped execution from the erased state. -/
theorem behE_eq_behU_of_not_typeFaults (cfg : ECfg) (P : List Instr) (σ : St)
    (h : ¬ TypeFaults cfg P σ) :
    Beh (stepE cfg) P σ = Beh stepU P (erase σ) :=
  beh_eq_of_exec_eq (runFrom_sim_eq cfg P σ [] (by simpa [TypeFaults] using h))

/-- Non-vacuity of R4a: a program that reads a `u32` object bytewise does not type-fault (byte
reads are exempt), and its two behaviour sets coincide. -/
theorem behE_eq_behU_nonvacuous :
    ¬ TypeFaults stdCfg [.store .u32 0 0, .load 1 .u8 0, .out 1] (freshAt 0 16 ones4) ∧
    Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .u8 0, .out 1] (freshAt 0 16 ones4) =
      Beh stepU [.store .u32 0 0, .load 1 .u8 0, .out 1] (erase (freshAt 0 16 ones4)) :=
  ⟨by decide, beh_eq_of_exec_eq (by decide)⟩

/-- R4a tightness (`h`), witness class: a three-instruction program on untyped allocated
storage. The program type-faults and its behaviour sets under (E) and (U) differ. -/
theorem agreement_needs_no_type_fault :
    TypeFaults stdCfg [.store .u32 0 0, .load 1 .f32 0, .out 1] (freshAt 0 16 ones4) ∧
    Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .out 1] (freshAt 0 16 ones4) ≠
      Beh stepU [.store .u32 0 0, .load 1 .f32 0, .out 1] (erase (freshAt 0 16 ones4)) := by
  refine ⟨by decide, fun h => ?_⟩
  have h1 : Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .out 1] (freshAt 0 16 ones4)
      (.done [[7]]) := by decide
  have h2 : ¬ Beh stepU [.store .u32 0 0, .load 1 .f32 0, .out 1] (erase (freshAt 0 16 ones4))
      (.done [[7]]) := by decide
  exact h2 (h ▸ h1)

/-- A program without any load can make (E) and (U) disagree: an `f32` store into a declared
`u32` object. So the agreement boundary must count stores into declared objects, not only
loads (this is why `TypeFaults` counts every rejected access). -/
theorem declared_store_mismatch_diverges_without_loads :
    [Instr.store .f32 0 0].all (fun i => !i.isLoad) = true ∧
    TypeFaults stdCfg [.store .f32 0 0] (declSt .u32 4 ones4) ∧
    Beh (stepE stdCfg) [.store .f32 0 0] (declSt .u32 4 ones4) ≠
      Beh stepU [.store .f32 0 0] (erase (declSt .u32 4 ones4)) := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  have h1 : Beh (stepE stdCfg) [.store .f32 0 0] (declSt .u32 4 ones4) (.done [[7]]) := by decide
  have h2 : ¬ Beh stepU [.store .f32 0 0] (erase (declSt .u32 4 ones4)) (.done [[7]]) := by decide
  exact h2 (h ▸ h1)

/-- **R4b.** For every configuration, program and initial state, every behaviour of the
untyped execution from the erased state is a behaviour of the effective-type execution. -/
theorem behU_erase_refines_behE (cfg : ECfg) (P : List Instr) (σ : St) :
    Refines (Beh stepU P (erase σ)) (Beh (stepE cfg) P σ) :=
  (refines_allows_iff _ _).2 (runFrom_sim_allows cfg P σ [])

/-- Instance of R4b where the inclusion is strict (a type-faulting program). -/
theorem behU_refines_behE_strict_instance :
    Refines (Beh stepU [.store .u32 0 0, .load 1 .f32 0, .out 1] (erase (freshAt 0 16 ones4)))
            (Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .out 1] (freshAt 0 16 ones4)) ∧
    ¬ Refines (Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .out 1] (freshAt 0 16 ones4))
              (Beh stepU [.store .u32 0 0, .load 1 .f32 0, .out 1] (erase (freshAt 0 16 ones4))) :=
  ⟨(refines_allows_iff _ _).2 (by decide), fun h => absurd ((refines_allows_iff _ _).1 h) (by decide)⟩

/-- **R4c (characterization).** For every configuration, program and initial state whose
untyped execution terminates normally: the behaviours under (E) and (U) coincide iff the (E)
execution does not stop at a `type` fault. -/
theorem behE_eq_behU_iff_not_typeFaults_of_uDefined (cfg : ECfg) (P : List Instr) (σ : St)
    (hU : UDefined P (erase σ)) :
    Beh (stepE cfg) P σ = Beh stepU P (erase σ) ↔ ¬ TypeFaults cfg P σ := by
  refine ⟨fun heq hTF => ?_, behE_eq_behU_of_not_typeFaults cfg P σ⟩
  obtain ⟨t', ht'⟩ := runFrom_typeFaults_ub cfg P σ [] hTF
  obtain ⟨tU, htU⟩ := hU
  have h1 : Beh (stepE cfg) P σ (.ub t') := by
    show Allows (exec (stepE cfg) P σ) _
    unfold exec; rw [ht']; exact Allows.refl _
  rw [heq] at h1
  have h2 : Allows (exec stepU P (erase σ)) (.ub t') := h1
  rw [htU] at h2
  cases h2

/-- Non-vacuity of R4c: a type-faulting program has a defined untyped execution (and its
behaviour sets differ); the byte-reading program has a defined untyped execution and does not
type-fault. -/
theorem behE_eq_behU_iff_nonvacuous :
    UDefined [.store .u32 0 0, .load 1 .f32 0, .out 1] (erase (freshAt 0 16 ones4)) ∧
    TypeFaults stdCfg [.store .u32 0 0, .load 1 .f32 0, .out 1] (freshAt 0 16 ones4) ∧
    UDefined [.store .u32 0 0, .load 1 .u8 0, .out 1] (erase (freshAt 0 16 ones4)) ∧
    ¬ TypeFaults stdCfg [.store .u32 0 0, .load 1 .u8 0, .out 1] (freshAt 0 16 ones4) := by decide

/-- R4c tightness (`hU`), witness class: a program whose untyped run later reads unallocated
memory, with no `out` between the type fault and that base fault. The untyped run is not
defined, and the equivalence fails: the program type-faults (its `f32` load reads `u32`
bytes), yet its behaviours under (E) and (U) coincide. -/
theorem typeFault_masked_by_later_base_fault :
    ¬ UDefined [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (erase (freshAt 0 16 ones4)) ∧
    TypeFaults stdCfg [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (freshAt 0 16 ones4) ∧
    Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (freshAt 0 16 ones4) =
      Beh stepU [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (erase (freshAt 0 16 ones4)) ∧
    ¬ (Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (freshAt 0 16 ones4) =
        Beh stepU [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (erase (freshAt 0 16 ones4)) ↔
       ¬ TypeFaults stdCfg [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (freshAt 0 16 ones4)) := by
  have heq : Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (freshAt 0 16 ones4) =
      Beh stepU [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (erase (freshAt 0 16 ones4)) :=
    beh_eq_of_exec_eq (by decide)
  have htf : TypeFaults stdCfg [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100]
      (freshAt 0 16 ones4) := by decide
  exact ⟨by decide, htf, heq, fun hiff => hiff.1 heq htf⟩

/-- Without untyped definedness a type fault is not always masked: here an `out` lies between
the type fault and the later base fault of the untyped run, and the behaviour sets differ. -/
theorem typeFault_unmasked_despite_later_base_fault :
    ¬ UDefined [.store .u32 0 0, .load 1 .f32 0, .out 1, .load 2 .u8 100] (erase (freshAt 0 16 ones4)) ∧
    TypeFaults stdCfg [.store .u32 0 0, .load 1 .f32 0, .out 1, .load 2 .u8 100] (freshAt 0 16 ones4) ∧
    Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .out 1, .load 2 .u8 100] (freshAt 0 16 ones4) ≠
      Beh stepU [.store .u32 0 0, .load 1 .f32 0, .out 1, .load 2 .u8 100] (erase (freshAt 0 16 ones4)) := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  have h1 : Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .out 1, .load 2 .u8 100]
      (freshAt 0 16 ones4) (.done []) := by decide
  have h2 : ¬ Beh stepU [.store .u32 0 0, .load 1 .f32 0, .out 1, .load 2 .u8 100]
      (erase (freshAt 0 16 ones4)) (.done []) := by decide
  exact h2 (h ▸ h1)

/-! ### When the converse of R4b fails -/

/-- **Converse of R4b, exact condition.** For every configuration, program and initial state,
the converse inclusion of R4b (every behaviour of the effective-type execution is a behaviour of
the untyped execution from the erased state) fails if and only if the effective-type execution
stops at a `type` fault and, in addition, the untyped execution either terminates normally or
has a strictly longer output trace than the effective-type execution. -/
theorem behE_not_refines_behU_iff (cfg : ECfg) (P : List Instr) (σ : St) :
    ¬ Refines (Beh (stepE cfg) P σ) (Beh stepU P (erase σ)) ↔
      TypeFaults cfg P σ ∧
        (UDefined P (erase σ) ∨
         (exec (stepE cfg) P σ).trace.length < (exec stepU P (erase σ)).trace.length) := by
  unfold Beh; rw [refines_allows_iff]
  by_cases htf : TypeFaults cfg P σ
  · obtain ⟨tE, htE⟩ := runFrom_typeFaults_ub cfg P σ [] htf
    have hexE : exec (stepE cfg) P σ = .ub tE := htE
    have hsim : Allows (exec (stepE cfg) P σ) (exec stepU P (erase σ)) :=
      runFrom_sim_allows cfg P σ []
    rw [hexE] at hsim ⊢
    cases hexU : exec stepU P (erase σ) with
    | done tU =>
      have hu : UDefined P (erase σ) := ⟨tU, hexU⟩
      simp [Allows, Outcome.trace, htf, hu]
    | ub tU =>
      rw [hexU] at hsim
      have hnu : ¬ UDefined P (erase σ) := by
        rintro ⟨_, h⟩; rw [hexU] at h; cases h
      simp only [Allows, Outcome.trace] at hsim ⊢
      have hlen_le : tE.length ≤ tU.length := List.IsPrefix.length_le hsim
      constructor
      · intro hnot_pref
        refine ⟨htf, Or.inr ?_⟩
        refine Nat.lt_of_le_of_ne hlen_le ?_
        intro heq
        exact hnot_pref (by rw [List.IsPrefix.eq_of_length hsim heq]; exact List.prefix_refl _)
      · rintro ⟨_, hu | hlt⟩
        · exact absurd hu hnu
        · intro hpref
          have := List.IsPrefix.length_le hpref
          omega
  · have heq : exec (stepE cfg) P σ = exec stepU P (erase σ) :=
      runFrom_sim_eq cfg P σ [] (by simpa [TypeFaults] using htf)
    rw [heq]
    simp [Allows.refl, htf]

/-- **Converse of R4b when the untyped run is defined.** For every configuration, program and
initial state whose untyped execution from the erased state terminates normally (`UDefined`):
the converse inclusion of R4b fails if and only if the effective-type execution stops at a
`type` fault. -/
theorem behE_not_refines_behU_iff_typeFaults_of_uDefined (cfg : ECfg) (P : List Instr) (σ : St)
    (hU : UDefined P (erase σ)) :
    ¬ Refines (Beh (stepE cfg) P σ) (Beh stepU P (erase σ)) ↔ TypeFaults cfg P σ := by
  rw [behE_not_refines_behU_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, Or.inl hU⟩⟩

/-- **Agreement of (E) and (U), exact condition without `UDefined`.** For every configuration,
program and initial state, the behaviours under (E) and (U) coincide if and only if it is not
the case that the effective-type execution stops at a `type` fault while the untyped execution
either terminates normally or has a strictly longer output trace. -/
theorem behE_eq_behU_iff (cfg : ECfg) (P : List Instr) (σ : St) :
    Beh (stepE cfg) P σ = Beh stepU P (erase σ) ↔
      ¬ (TypeFaults cfg P σ ∧
        (UDefined P (erase σ) ∨
         (exec (stepE cfg) P σ).trace.length < (exec stepU P (erase σ)).trace.length)) := by
  rw [← behE_not_refines_behU_iff, Classical.not_not]
  constructor
  · intro h o ho; rw [← h]; exact ho
  · intro href
    funext o
    exact propext ⟨href o, behU_erase_refines_behE cfg P σ o⟩

/-- Non-vacuity of `behE_not_refines_behU_iff_typeFaults_of_uDefined`: on untyped allocated
storage, `[store u32 0 0, load 1 f32 0, out 1]` has a defined untyped run, type-faults, and
the converse inclusion fails; `[store u32 0 0, load 1 u8 0, out 1]` has a defined untyped run,
does not type-fault, and the converse inclusion holds. -/
theorem behE_not_refines_behU_of_uDefined_nonvacuous :
    UDefined [.store .u32 0 0, .load 1 .f32 0, .out 1] (erase (freshAt 0 16 ones4)) ∧
    TypeFaults stdCfg [.store .u32 0 0, .load 1 .f32 0, .out 1] (freshAt 0 16 ones4) ∧
    ¬ Refines (Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .out 1] (freshAt 0 16 ones4))
        (Beh stepU [.store .u32 0 0, .load 1 .f32 0, .out 1] (erase (freshAt 0 16 ones4))) ∧
    UDefined [.store .u32 0 0, .load 1 .u8 0, .out 1] (erase (freshAt 0 16 ones4)) ∧
    ¬ TypeFaults stdCfg [.store .u32 0 0, .load 1 .u8 0, .out 1] (freshAt 0 16 ones4) ∧
    Refines (Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .u8 0, .out 1] (freshAt 0 16 ones4))
        (Beh stepU [.store .u32 0 0, .load 1 .u8 0, .out 1] (erase (freshAt 0 16 ones4))) := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, ?_⟩
  · unfold Beh; rw [refines_allows_iff]; decide
  · unfold Beh; rw [refines_allows_iff]; decide

/-- The condition `UDefined` cannot be dropped from a biconditional of the form "the converse
inclusion fails iff the program type-faults and its untyped run is defined": on
`[store u32 0 0, load 1 f32 0, out 1, load 2 u8 100]` from untyped allocated storage the
untyped run is not defined (it reads unallocated address `100` after printing), the program
type-faults, and the converse inclusion still fails, because the untyped run prints before
faulting while the effective-type run stops at the type fault with an empty trace. -/
theorem behE_not_refines_behU_without_uDefined :
    ¬ UDefined [.store .u32 0 0, .load 1 .f32 0, .out 1, .load 2 .u8 100] (erase (freshAt 0 16 ones4)) ∧
    TypeFaults stdCfg [.store .u32 0 0, .load 1 .f32 0, .out 1, .load 2 .u8 100] (freshAt 0 16 ones4) ∧
    ¬ Refines (Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .out 1, .load 2 .u8 100]
                (freshAt 0 16 ones4))
        (Beh stepU [.store .u32 0 0, .load 1 .f32 0, .out 1, .load 2 .u8 100]
                (erase (freshAt 0 16 ones4))) ∧
    ¬ (∀ (cfg : ECfg) (Q : List Instr) (s : St),
        ¬ Refines (Beh (stepE cfg) Q s) (Beh stepU Q (erase s)) ↔
          (TypeFaults cfg Q s ∧ UDefined Q (erase s))) := by
  have hnot_ref : ¬ Refines
      (Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .out 1, .load 2 .u8 100] (freshAt 0 16 ones4))
      (Beh stepU [.store .u32 0 0, .load 1 .f32 0, .out 1, .load 2 .u8 100] (erase (freshAt 0 16 ones4))) := by
    unfold Beh; rw [refines_allows_iff]; decide
  have hnu : ¬ UDefined [.store .u32 0 0, .load 1 .f32 0, .out 1, .load 2 .u8 100]
      (erase (freshAt 0 16 ones4)) := by decide
  exact ⟨hnu, by decide, hnot_ref, fun hall => hnu ((hall stdCfg _ _).mp hnot_ref).2⟩

/-- A type-faulting program whose untyped run is not defined and for which the converse
inclusion of R4b holds: `[store u32 0 0, load 1 f32 0, load 2 u8 100]` (no `out` between the type
fault and the later base fault of the untyped run). -/
theorem behE_refines_behU_masked_instance :
    ¬ UDefined [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (erase (freshAt 0 16 ones4)) ∧
    TypeFaults stdCfg [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (freshAt 0 16 ones4) ∧
    Refines (Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (freshAt 0 16 ones4))
        (Beh stepU [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (erase (freshAt 0 16 ones4))) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold Beh; rw [refines_allows_iff]; decide

/-! ## R5. Declared storage licenses the sink and the store/store swap -/

/-- **R5a.** Under (E) with the standard discipline: if neither `T` nor `U` is the character
type and the two types share no leaf, then swapping a `T`-store to `p` and a `U`-store to `q` is
a refinement in every context and from every initial state in which every allocated byte of
`[p, p + T.size)` belongs to a declared object. -/
theorem store_store_reorder_sound_E_of_declared_of_noCommonLeaf_of_ne_u8 (T U : Ty) (p q : Nat)
    (a b : Reg) (hT : T ≠ .u8) (hU : U ≠ .u8) (hTU : NoCommonLeaf T U) :
    ReorderSoundFrom (fun σ => DeclaredOn σ p T.size) (stepE stdCfg)
      [.store T p a, .store U q b] [.store U q b, .store T p a] := by
  refine reorderSoundFrom_of_block (Inv := fun σ => DeclaredOn σ p T.size) (fun _ h => h)
    declaredOn_step ?_
  intro σ t hD
  rcases block2_cases (stepE_store_noEmit _ T p a) (stepE_store_noEmit _ U q b) σ t with
    h | ⟨σ1, σ2, h1, h2, hrun⟩
  · exact Or.inl h
  · refine Or.inr ⟨σ2, hrun, ?_⟩
    obtain ⟨ds1, hds1, hv1, hdok1, rfl⟩ := stepE_store_next h1
    obtain ⟨ds2, hds2, hv2, hdok2, rfl⟩ := stepE_store_next h2
    have hds20 : readRange (updRange σ.mem p T.size (storeCell T (σ.regs a))) q U.size = some ds2 :=
      hds2
    have hdisj : RangesDisjoint p T.size q U.size := by
      refine Decidable.byContradiction fun hov => ?_
      obtain ⟨i, j, hi, hj, hij⟩ := exists_overlap (size_pos T) (size_pos U) hov
      have l1 : ds1.length = T.size := readRange_length hds1
      have l2 : ds2.length = U.size := readRange_length hds20
      have e1 := readRange_get hds1 i (by omega)
      have e2 := readRange_get hds20 j (by omega)
      rw [← hij, updRange_of_mem _ _ _ _ (by omega) (by omega), e1] at e2
      simp only [Option.map, Option.some.injEq, Nat.add_sub_cancel_left] at e2
      obtain ⟨d, hd⟩ := isDecl_of_declaredOn hD hi e1
      have c1 : (match ds1[i].eff with
          | .decl d => stdCompat (some d) T.leaves[i]
          | .alloc _ => true) = true := declOk_get hdok1 i (by omega) hi
      rw [hd] at c1
      have c2 : (match ds2[j].eff with
          | .decl d => stdCompat (some d) U.leaves[j]
          | .alloc _ => true) = true := declOk_get hdok2 j (by omega) hj
      rw [← e2] at c2
      have hse : (storeCell T (σ.regs a) i ds1[i]).eff = .decl d := by simp only [storeCell, hd]
      rw [hse] at c2
      exact decl_two_checks (leaf_ne_u8_of_ne_u8 hT (List.getElem_mem hi))
        (leaf_ne_u8_of_ne_u8 hU (List.getElem_mem hj)) (noCommonLeaf_get hTU hi hj) c1 c2
    have hdisj' : RangesDisjoint q U.size p T.size := by unfold RangesDisjoint at *; omega
    have hds2' : readRange σ.mem q U.size = some ds2 := by
      rw [← readRange_updRange_disjoint σ.mem q U.size p T.size (storeCell T (σ.regs a)) hdisj']
      exact hds20
    have hds1' : readRange (updRange σ.mem q U.size (storeCell U (σ.regs b))) p T.size = some ds1 := by
      rw [readRange_updRange_disjoint _ _ _ _ _ _ hdisj]; exact hds1
    refine block2_ok (stepE_store_of hds2' hv2 hdok2) ?_
    rw [stepE_store_of (σ := { σ with mem := updRange σ.mem q U.size (storeCell U (σ.regs b)) })
      hds1' hv1 hdok1]
    simp only [updRange_comm σ.mem p T.size q U.size (storeCell T (σ.regs a))
      (storeCell U (σ.regs b)) hdisj]

/-- Non-vacuity of R5a (scalar instance): `T = u32` at `0`, `U = f32` at `4` in a declared
`pair` object; the hypotheses hold and the source block is defined there. -/
theorem store_store_declared_nonvacuous :
    Ty.u32 ≠ .u8 ∧ Ty.f32 ≠ .u8 ∧ NoCommonLeaf .u32 .f32 ∧
    DeclaredOn ((declPairSt []).withRegs (regs2 ones4 twos4)) 0 4 ∧
    exec (stepE stdCfg) [.store .u32 0 0, .store .f32 4 1, .load 2 .pair 0, .out 2]
      ((declPairSt []).withRegs (regs2 ones4 twos4)) = .done [ones4 ++ twos4] := by decide

/-- A declared `pair` object at `0..7` followed by untyped allocated storage at `8..15`. -/
def declPairThenFresh (rs : Reg → Val) : St :=
  ⟨fun a => if a < 4 then some ⟨0, .decl .u32⟩ else if a < 8 then some ⟨0, .decl .f32⟩
            else if a < 16 then some ⟨0, .alloc none⟩ else none, rs⟩

/-- Non-vacuity of R5a (struct instance): `T = pair` at `0` (declared), `U = u16` at `8`; the
hypotheses hold and the source block is defined there. -/
theorem store_store_declared_nonvacuous_struct :
    Ty.pair ≠ .u8 ∧ Ty.u16 ≠ .u8 ∧ NoCommonLeaf .pair .u16 ∧
    DeclaredOn (declPairThenFresh (regs2 (List.replicate 8 1) [2, 2])) 0 8 ∧
    exec (stepE stdCfg) [.store .pair 0 0, .store .u16 8 1, .load 2 .u8 0, .out 2]
      (declPairThenFresh (regs2 (List.replicate 8 1) [2, 2])) = .done [[1]] := by decide

/-- R5a tightness (`DeclaredOn`), witness class: overlapping addresses `p = q = 0` on untyped
allocated storage, where `DeclaredOn` fails. Type hypotheses hold and the swap is not sound
from all states (this restates R1c with the failing precondition exposed). -/
theorem store_store_needs_declared_storage :
    Ty.u32 ≠ .u8 ∧ Ty.f32 ≠ .u8 ∧ NoCommonLeaf .u32 .f32 ∧
    ¬ DeclaredOn ((freshAt 0 16 []).withRegs (regs2 ones4 twos4)) 0 4 ∧
    ¬ ReorderSound (stepE stdCfg) [.store .u32 0 0, .store .f32 0 1] [.store .f32 0 1, .store .u32 0 0] :=
  ⟨by decide, by decide, by decide, by decide, store_store_reorder_not_sound_E.2.2.2⟩

/-- R5a tightness (`hT`), witness class: overlapping addresses `p = q = 0` in a declared `f32`
object. A byte store and an `f32` store; all other hypotheses hold and the swap is not sound. -/
theorem store_store_declared_needs_first_ne_u8 :
    Ty.f32 ≠ .u8 ∧ NoCommonLeaf .u8 .f32 ∧ DeclaredOn ((declSt .f32 4 []).withRegs (regs2 [1] twos4)) 0 1 ∧
    ¬ ReorderSoundFrom (fun σ => DeclaredOn σ 0 Ty.u8.size) (stepE stdCfg)
        [.store .u8 0 0, .store .f32 0 1] [.store .f32 0 1, .store .u8 0 0] :=
  ⟨by decide, by decide, by decide,
   not_reorderSoundFrom_of [] [.load 2 .u8 0, .out 2] ((declSt .f32 4 []).withRegs (regs2 [1] twos4))
     (by decide) (by decide)⟩

/-- R5a tightness (`hU`), witness class: overlapping addresses `p = q = 0` in a declared `f32`
object. An `f32` store then a byte store. -/
theorem store_store_declared_needs_second_ne_u8 :
    Ty.f32 ≠ .u8 ∧ NoCommonLeaf .f32 .u8 ∧
    ¬ ReorderSoundFrom (fun σ => DeclaredOn σ 0 Ty.f32.size) (stepE stdCfg)
        [.store .f32 0 0, .store .u8 0 1] [.store .u8 0 1, .store .f32 0 0] :=
  ⟨by decide, by decide,
   not_reorderSoundFrom_of [] [.load 2 .u8 0, .out 2] ((declSt .f32 4 []).withRegs (regs2 twos4 [1]))
     (by decide) (by decide)⟩

/-- R5a tightness (`hTU`), witness class: overlapping addresses `p = q = 0` in a declared `pair`
object. A `pair` store and a `u32` store; `pair ≠ u32`, neither is `u8`, the storage is
declared, and the swap is not sound. -/
theorem store_store_declared_needs_noCommonLeaf :
    Ty.pair ≠ .u32 ∧ Ty.pair ≠ .u8 ∧ Ty.u32 ≠ .u8 ∧ ¬ NoCommonLeaf .pair .u32 ∧
    ¬ ReorderSoundFrom (fun σ => DeclaredOn σ 0 Ty.pair.size) (stepE stdCfg)
        [.store .pair 0 0, .store .u32 0 1] [.store .u32 0 1, .store .pair 0 0] :=
  ⟨by decide, by decide, by decide, by decide,
   not_reorderSoundFrom_of [] [.load 2 .u8 0, .out 2]
     ((declPairSt []).withRegs (regs2 (List.replicate 8 1) twos4)) (by decide) (by decide)⟩

/-- Companion of R5a: under the same type hypotheses, declaring the *second* store's range
`[q, q + U.size)` instead of the first also makes the swap a refinement in every context. -/
theorem store_store_reorder_sound_E_of_second_declared (T U : Ty) (p q : Nat)
    (a b : Reg) (hT : T ≠ .u8) (hU : U ≠ .u8) (hTU : NoCommonLeaf T U) :
    ReorderSoundFrom (fun σ => DeclaredOn σ q U.size) (stepE stdCfg)
      [.store T p a, .store U q b] [.store U q b, .store T p a] := by
  refine reorderSoundFrom_of_block (Inv := fun σ => DeclaredOn σ q U.size) (fun _ h => h)
    declaredOn_step ?_
  intro σ t hD
  rcases block2_cases (stepE_store_noEmit _ T p a) (stepE_store_noEmit _ U q b) σ t with
    h | ⟨σ1, σ2, h1, h2, hrun⟩
  · exact Or.inl h
  · refine Or.inr ⟨σ2, hrun, ?_⟩
    obtain ⟨ds1, hds1, hv1, hdok1, rfl⟩ := stepE_store_next h1
    obtain ⟨ds2, hds2, hv2, hdok2, rfl⟩ := stepE_store_next h2
    have hds20 : readRange (updRange σ.mem p T.size (storeCell T (σ.regs a))) q U.size = some ds2 := hds2
    have hdisj : RangesDisjoint p T.size q U.size := by
      refine Decidable.byContradiction fun hov => ?_
      obtain ⟨i, j, hi, hj, hij⟩ := exists_overlap (size_pos T) (size_pos U) hov
      have l1 : ds1.length = T.size := readRange_length hds1
      have l2 : ds2.length = U.size := readRange_length hds20
      have e1 := readRange_get hds1 i (by omega)
      have e2 := readRange_get hds20 j (by omega)
      have e1_at_q : σ.mem (q + j) = some ds1[i] := by rwa [← hij]
      obtain ⟨d, hd⟩ := isDecl_of_declaredOn hD hj e1_at_q
      rw [← hij, updRange_of_mem _ _ _ _ (by omega) (by omega), e1] at e2
      simp only [Option.map, Option.some.injEq, Nat.add_sub_cancel_left] at e2
      have c1 : (match ds1[i].eff with
          | .decl d => stdCompat (some d) T.leaves[i]
          | .alloc _ => true) = true := declOk_get hdok1 i (by omega) hi
      rw [hd] at c1
      have c2 : (match ds2[j].eff with
          | .decl d => stdCompat (some d) U.leaves[j]
          | .alloc _ => true) = true := declOk_get hdok2 j (by omega) hj
      rw [← e2] at c2
      have hse : (storeCell T (σ.regs a) i ds1[i]).eff = .decl d := by simp only [storeCell, hd]
      rw [hse] at c2
      exact decl_two_checks (leaf_ne_u8_of_ne_u8 hT (List.getElem_mem hi))
        (leaf_ne_u8_of_ne_u8 hU (List.getElem_mem hj)) (noCommonLeaf_get hTU hi hj) c1 c2
    have hdisj' : RangesDisjoint q U.size p T.size := by unfold RangesDisjoint at *; omega
    have hds2' : readRange σ.mem q U.size = some ds2 := by
      rwa [readRange_updRange_disjoint σ.mem q U.size p T.size (storeCell T (σ.regs a)) hdisj'] at hds20
    have hds1' : readRange (updRange σ.mem q U.size (storeCell U (σ.regs b))) p T.size = some ds1 := by
      rw [readRange_updRange_disjoint _ _ _ _ _ _ hdisj]; exact hds1
    refine block2_ok (stepE_store_of hds2' hv2 hdok2) ?_
    rw [stepE_store_of (σ := { σ with mem := updRange σ.mem q U.size (storeCell U (σ.regs b)) })
      hds1' hv1 hdok1]
    simp only [updRange_comm σ.mem p T.size q U.size (storeCell T (σ.regs a))
      (storeCell U (σ.regs b)) hdisj]

/-- Companion of R5a: for every pair of types (no type hypothesis) and disjoint byte ranges,
swapping a `T`-store to `p` and a `U`-store to `q` is a refinement in every context and from
every initial state, including states in which `DeclaredOn` fails. -/
theorem store_store_reorder_sound_E_of_disjoint_ranges (T U : Ty) (p q : Nat) (a b : Reg)
    (hdisj : RangesDisjoint p T.size q U.size) :
    ReorderSound (stepE stdCfg) [.store T p a, .store U q b] [.store U q b, .store T p a] := by
  refine reorderSoundFrom_of_block (Inv := fun _ => True) (fun _ _ => trivial)
    (fun _ _ _ _ _ => trivial) ?_
  intro σ t _
  rcases block2_cases (stepE_store_noEmit _ T p a) (stepE_store_noEmit _ U q b) σ t with
    h | ⟨σ1, σ2, h1, h2, hrun⟩
  · exact Or.inl h
  · refine Or.inr ⟨σ2, hrun, ?_⟩
    obtain ⟨ds1, hds1, hv1, hdok1, rfl⟩ := stepE_store_next h1
    obtain ⟨ds2, hds2, hv2, hdok2, rfl⟩ := stepE_store_next h2
    have hdisj' : RangesDisjoint q U.size p T.size := by unfold RangesDisjoint at *; omega
    have hds2' : readRange σ.mem q U.size = some ds2 := by
      rwa [readRange_updRange_disjoint σ.mem q U.size p T.size (storeCell T (σ.regs a)) hdisj'] at hds2
    have hds1' : readRange (updRange σ.mem q U.size (storeCell U (σ.regs b))) p T.size = some ds1 := by
      rw [readRange_updRange_disjoint _ _ _ _ _ _ hdisj]; exact hds1
    refine block2_ok (stepE_store_of hds2' hv2 hdok2) ?_
    rw [stepE_store_of (σ := { σ with mem := updRange σ.mem q U.size (storeCell U (σ.regs b)) })
      hds1' hv1 hdok1]
    simp only [updRange_comm σ.mem p T.size q U.size (storeCell T (σ.regs a))
      (storeCell U (σ.regs b)) hdisj]

/-- Non-vacuity of the two companions of R5a: the second store's range `[4, 8)` of a declared
`pair` object is declared and the source block is defined there (first store `u32` to `0`); and
for disjoint ranges on untyped allocated storage, where `DeclaredOn` fails, the source block is
defined. -/
theorem store_store_companions_nonvacuous :
    DeclaredOn ((declPairSt []).withRegs (regs2 ones4 twos4)) 4 Ty.f32.size ∧
    exec (stepE stdCfg) [.store .u32 0 0, .store .f32 4 1, .load 2 .pair 0, .out 2]
      ((declPairSt []).withRegs (regs2 ones4 twos4)) = .done [ones4 ++ twos4] ∧
    RangesDisjoint 0 Ty.u32.size 4 Ty.f32.size ∧
    ¬ DeclaredOn ((freshAt 0 16 []).withRegs (regs2 ones4 twos4)) 0 4 ∧
    exec (stepE stdCfg) [.store .u32 0 0, .store .f32 4 1, .load 2 .pair 0, .out 2]
      ((freshAt 0 16 []).withRegs (regs2 ones4 twos4)) = .done [ones4 ++ twos4] := by decide

/-- **R5b.** Under (E) with the standard discipline: if neither `T` nor `U` is the character
type, the types share no leaf, and the load's destination register `s` differs from the store's
source register `r`, then moving a `T`-load from `p` below a later `U`-store to `q` (sink) is a
refinement in every context and from every initial state in which every allocated byte of
`[p, p + T.size)` belongs to a declared object. -/
theorem sink_load_below_store_sound_E_of_declared_of_noCommonLeaf_of_ne_u8 (T U : Ty) (p q : Nat)
    (s r : Reg) (hT : T ≠ .u8) (hU : U ≠ .u8) (hTU : NoCommonLeaf T U) (hsr : s ≠ r) :
    ReorderSoundFrom (fun σ => DeclaredOn σ p T.size) (stepE stdCfg)
      [.load s T p, .store U q r] [.store U q r, .load s T p] := by
  refine reorderSoundFrom_of_block (Inv := fun σ => DeclaredOn σ p T.size) (fun _ h => h)
    declaredOn_step ?_
  intro σ t hD
  rcases block2_cases (stepE_load_noEmit _ s T p) (stepE_store_noEmit _ U q r) σ t with
    h | ⟨σ1, σ2, h1, h2, hrun⟩
  · exact Or.inl h
  · refine Or.inr ⟨σ2, hrun, ?_⟩
    obtain ⟨cs, hcs, htok, rfl⟩ := stepE_load_next h1
    obtain ⟨ds, hds, hv, hdok, rfl⟩ := stepE_store_next h2
    have hds0 : readRange σ.mem q U.size = some ds := hds
    have hregs : updReg σ.regs s (cs.map Cell.val) r = σ.regs r := by
      simp [updReg, Ne.symm hsr]
    have hv0 : U.Valid (σ.regs r) := by
      have h' : U.Valid (updReg σ.regs s (cs.map Cell.val) r) := hv
      rwa [hregs] at h'
    have hdisj : RangesDisjoint p T.size q U.size := by
      refine Decidable.byContradiction fun hov => ?_
      obtain ⟨i, j, hi, hj, hij⟩ := exists_overlap (size_pos T) (size_pos U) hov
      have l1 : cs.length = T.size := readRange_length hcs
      have l2 : ds.length = U.size := readRange_length hds0
      have e1 := readRange_get hcs i (by omega)
      have e2 := readRange_get hds0 j (by omega)
      rw [← hij, e1] at e2
      simp only [Option.some.injEq] at e2
      obtain ⟨d, hd⟩ := isDecl_of_declaredOn hD hi e1
      have c1 : stdCompat cs[i].eff.tag T.leaves[i] = true := tagsOk_get htok i (by omega) hi
      rw [hd] at c1
      have c2 : (match ds[j].eff with
          | .decl d => stdCompat (some d) U.leaves[j]
          | .alloc _ => true) = true := declOk_get hdok j (by omega) hj
      rw [← e2, hd] at c2
      exact decl_two_checks (leaf_ne_u8_of_ne_u8 hT (List.getElem_mem hi))
        (leaf_ne_u8_of_ne_u8 hU (List.getElem_mem hj)) (noCommonLeaf_get hTU hi hj) c1 c2
    have hcs' : readRange (updRange σ.mem q U.size (storeCell U (σ.regs r))) p T.size = some cs := by
      rw [readRange_updRange_disjoint _ _ _ _ _ _ hdisj]; exact hcs
    refine block2_ok (stepE_store_of hds0 hv0 hdok) ?_
    rw [stepE_load_of (σ := { σ with mem := updRange σ.mem q U.size (storeCell U (σ.regs r)) })
      hcs' htok]
    simp [hregs]

/-- Non-vacuity of R5b (scalar instance): `T = f32` at `4`, `U = u32` at `0` in a declared
`pair` object. -/
theorem sink_declared_nonvacuous :
    Ty.f32 ≠ .u8 ∧ Ty.u32 ≠ .u8 ∧ NoCommonLeaf .f32 .u32 ∧ (1 : Reg) ≠ 0 ∧
    DeclaredOn (declPairSt ones4) 4 4 ∧
    exec (stepE stdCfg) [.load 1 .f32 4, .store .u32 0 0, .out 1] (declPairSt ones4) =
      .done [[0, 0, 0, 0]] := by decide

/-- Non-vacuity of R5b (struct instance): `T = pair` at `0` (declared), `U = u16` at `8`. -/
theorem sink_declared_nonvacuous_struct :
    Ty.pair ≠ .u8 ∧ Ty.u16 ≠ .u8 ∧ NoCommonLeaf .pair .u16 ∧ (1 : Reg) ≠ 0 ∧
    DeclaredOn (declPairThenFresh (fun _ => [2, 2])) 0 8 ∧
    exec (stepE stdCfg) [.load 1 .pair 0, .store .u16 8 0, .out 1]
      (declPairThenFresh (fun _ => [2, 2])) = .done [[0, 0, 0, 0, 0, 0, 0, 0]] := by decide

/-- R5b tightness (`DeclaredOn`), witness class: overlapping addresses `p = q = 0` on untyped
allocated storage, where `DeclaredOn` fails. Type and register hypotheses hold and the sink is
not sound from all states (this restates R1b with the failing precondition exposed). -/
theorem sink_needs_declared_storage :
    Ty.u32 ≠ .u8 ∧ Ty.f32 ≠ .u8 ∧ NoCommonLeaf .u32 .f32 ∧ (1 : Reg) ≠ 0 ∧
    ¬ DeclaredOn (freshAt 0 16 ones4) 0 4 ∧
    ¬ ReorderSound (stepE stdCfg) [.load 1 .u32 0, .store .f32 0 0] [.store .f32 0 0, .load 1 .u32 0] :=
  ⟨by decide, by decide, by decide, by decide, by decide, sink_load_below_store_not_sound_E.2.2.2.2⟩

/-- R5b tightness (`hT`), witness class: overlapping addresses `p = q = 0` in a declared `f32`
object. A byte load sunk below an `f32` store. -/
theorem sink_declared_needs_load_ne_u8 :
    Ty.f32 ≠ .u8 ∧ NoCommonLeaf .u8 .f32 ∧ (1 : Reg) ≠ 0 ∧
    ¬ ReorderSoundFrom (fun σ => DeclaredOn σ 0 Ty.u8.size) (stepE stdCfg)
        [.load 1 .u8 0, .store .f32 0 0] [.store .f32 0 0, .load 1 .u8 0] :=
  ⟨by decide, by decide, by decide,
   not_reorderSoundFrom_of [] [.out 1] (declSt .f32 4 twos4) (by decide) (by decide)⟩

/-- R5b tightness (`hU`), witness class: overlapping addresses `p = q = 0` in a declared `f32`
object. An `f32` load sunk below a byte store. -/
theorem sink_declared_needs_store_ne_u8 :
    Ty.f32 ≠ .u8 ∧ NoCommonLeaf .f32 .u8 ∧ (1 : Reg) ≠ 0 ∧
    ¬ ReorderSoundFrom (fun σ => DeclaredOn σ 0 Ty.f32.size) (stepE stdCfg)
        [.load 1 .f32 0, .store .u8 0 0] [.store .u8 0 0, .load 1 .f32 0] :=
  ⟨by decide, by decide, by decide,
   not_reorderSoundFrom_of [] [.out 1] (declSt .f32 4 [2]) (by decide) (by decide)⟩

/-- R5b tightness (`hTU`), witness class: overlapping addresses `p = q = 0` in a declared `pair`
object. A `pair` load sunk below a `u32` store. -/
theorem sink_declared_needs_noCommonLeaf :
    Ty.pair ≠ .u32 ∧ Ty.pair ≠ .u8 ∧ Ty.u32 ≠ .u8 ∧ (1 : Reg) ≠ 0 ∧ ¬ NoCommonLeaf .pair .u32 ∧
    ¬ ReorderSoundFrom (fun σ => DeclaredOn σ 0 Ty.pair.size) (stepE stdCfg)
        [.load 1 .pair 0, .store .u32 0 0] [.store .u32 0 0, .load 1 .pair 0] :=
  ⟨by decide, by decide, by decide, by decide, by decide,
   not_reorderSoundFrom_of [] [.out 1] (declPairSt twos4) (by decide) (by decide)⟩

/-- R5b tightness (`hsr`), witness class: disjoint addresses `p = 4, q = 0` in a declared `pair`
object. The load overwrites the store's source register (`s = r = 0`); the storage is declared,
and the sink is not sound. -/
theorem sink_declared_needs_distinct_registers :
    Ty.f32 ≠ .u8 ∧ Ty.u32 ≠ .u8 ∧ NoCommonLeaf .f32 .u32 ∧
    ¬ ReorderSoundFrom (fun σ => DeclaredOn σ 4 Ty.f32.size) (stepE stdCfg)
        [.load 0 .f32 4, .store .u32 0 0] [.store .u32 0 0, .load 0 .f32 4] :=
  ⟨by decide, by decide, by decide,
   not_reorderSoundFrom_of [] [.load 2 .u8 0, .out 2] (declPairSt ones4) (by decide) (by decide)⟩

/-- Companion of R5b: under the same type and register hypotheses, declaring the store's range
`[q, q + U.size)` instead of the load's range also makes the sink a refinement in every
context. -/
theorem sink_load_below_store_sound_E_of_store_range_declared (T U : Ty) (p q : Nat)
    (s r : Reg) (hT : T ≠ .u8) (hU : U ≠ .u8) (hTU : NoCommonLeaf T U) (hsr : s ≠ r) :
    ReorderSoundFrom (fun σ => DeclaredOn σ q U.size) (stepE stdCfg)
      [.load s T p, .store U q r] [.store U q r, .load s T p] := by
  refine reorderSoundFrom_of_block (Inv := fun σ => DeclaredOn σ q U.size) (fun _ h => h)
    declaredOn_step ?_
  intro σ t hD
  rcases block2_cases (stepE_load_noEmit _ s T p) (stepE_store_noEmit _ U q r) σ t with
    h | ⟨σ1, σ2, h1, h2, hrun⟩
  · exact Or.inl h
  · refine Or.inr ⟨σ2, hrun, ?_⟩
    obtain ⟨cs, hcs, htok, rfl⟩ := stepE_load_next h1
    obtain ⟨ds, hds, hv, hdok, rfl⟩ := stepE_store_next h2
    have hds0 : readRange σ.mem q U.size = some ds := hds
    have hregs : updReg σ.regs s (cs.map Cell.val) r = σ.regs r := by
      simp [updReg, Ne.symm hsr]
    have hv0 : U.Valid (σ.regs r) := by
      have h' : U.Valid (updReg σ.regs s (cs.map Cell.val) r) := hv
      rwa [hregs] at h'
    have hdisj : RangesDisjoint p T.size q U.size := by
      refine Decidable.byContradiction fun hov => ?_
      obtain ⟨i, j, hi, hj, hij⟩ := exists_overlap (size_pos T) (size_pos U) hov
      have l1 : cs.length = T.size := readRange_length hcs
      have l2 : ds.length = U.size := readRange_length hds0
      have e1 := readRange_get hcs i (by omega)
      have e2 := readRange_get hds0 j (by omega)
      rw [← hij, e1] at e2
      simp only [Option.some.injEq] at e2
      have e1_at_q : σ.mem (q + j) = some cs[i] := by rw [← hij]; exact e1
      obtain ⟨d, hd⟩ := isDecl_of_declaredOn hD hj e1_at_q
      have c1 : stdCompat cs[i].eff.tag T.leaves[i] = true := tagsOk_get htok i (by omega) hi
      rw [hd] at c1
      have c2 : (match ds[j].eff with
          | .decl d => stdCompat (some d) U.leaves[j]
          | .alloc _ => true) = true := declOk_get hdok j (by omega) hj
      rw [← e2, hd] at c2
      exact decl_two_checks (leaf_ne_u8_of_ne_u8 hT (List.getElem_mem hi))
        (leaf_ne_u8_of_ne_u8 hU (List.getElem_mem hj)) (noCommonLeaf_get hTU hi hj) c1 c2
    have hcs' : readRange (updRange σ.mem q U.size (storeCell U (σ.regs r))) p T.size = some cs := by
      rw [readRange_updRange_disjoint _ _ _ _ _ _ hdisj]; exact hcs
    refine block2_ok (stepE_store_of hds0 hv0 hdok) ?_
    rw [stepE_load_of (σ := { σ with mem := updRange σ.mem q U.size (storeCell U (σ.regs r)) })
      hcs' htok]
    simp [hregs]

/-- Companion of R5b: for every pair of types (no type hypothesis), disjoint byte ranges and
distinct registers `s ≠ r`, sinking a `T`-load from `p` below a `U`-store to `q` is a refinement
in every context and from every initial state, including states in which `DeclaredOn` fails. -/
theorem sink_load_below_store_sound_E_of_disjoint_ranges (T U : Ty) (p q : Nat) (s r : Reg)
    (hdisj : RangesDisjoint p T.size q U.size) (hsr : s ≠ r) :
    ReorderSound (stepE stdCfg) [.load s T p, .store U q r] [.store U q r, .load s T p] := by
  refine reorderSoundFrom_of_block (Inv := fun _ => True) (fun _ _ => trivial)
    (fun _ _ _ _ _ => trivial) ?_
  intro σ t _
  rcases block2_cases (stepE_load_noEmit _ s T p) (stepE_store_noEmit _ U q r) σ t with
    h | ⟨σ1, σ2, h1, h2, hrun⟩
  · exact Or.inl h
  · refine Or.inr ⟨σ2, hrun, ?_⟩
    obtain ⟨cs, hcs, htok, rfl⟩ := stepE_load_next h1
    obtain ⟨ds, hds, hv, hdok, rfl⟩ := stepE_store_next h2
    have hds0 : readRange σ.mem q U.size = some ds := hds
    have hregs : updReg σ.regs s (cs.map Cell.val) r = σ.regs r := by simp [updReg, Ne.symm hsr]
    have hv0 : U.Valid (σ.regs r) := by
      have h' : U.Valid (updReg σ.regs s (cs.map Cell.val) r) := hv
      rwa [hregs] at h'
    have hcs' : readRange (updRange σ.mem q U.size (storeCell U (σ.regs r))) p T.size = some cs := by
      rw [readRange_updRange_disjoint _ _ _ _ _ _ hdisj]; exact hcs
    refine block2_ok (stepE_store_of hds0 hv0 hdok) ?_
    rw [stepE_load_of (σ := { σ with mem := updRange σ.mem q U.size (storeCell U (σ.regs r)) })
      hcs' htok]
    simp [hregs]

/-- Non-vacuity of the two companions of R5b: the store's range `[0, 4)` of a declared `pair`
object is declared and the source block (an `f32` load from `4`, a `u32` store to `0`) is
defined there; and for disjoint ranges on untyped allocated storage, where `DeclaredOn` fails,
the same source block is defined. -/
theorem sink_companions_nonvacuous :
    DeclaredOn (declPairSt ones4) 0 Ty.u32.size ∧
    exec (stepE stdCfg) [.load 1 .f32 4, .store .u32 0 0, .out 1] (declPairSt ones4) =
      .done [[0, 0, 0, 0]] ∧
    RangesDisjoint 4 Ty.f32.size 0 Ty.u32.size ∧ (1 : Reg) ≠ 0 ∧
    ¬ DeclaredOn (freshAt 0 16 ones4) 4 4 ∧
    exec (stepE stdCfg) [.load 1 .f32 4, .store .u32 0 0, .out 1] (freshAt 0 16 ones4) =
      .done [[0, 0, 0, 0]] := by decide

/-! ## R5c. The store/store swap scheme: declared versus allocated storage -/

/-- **R5c.** For the address-parametric scheme "swap a `u32` store to `p` and an `f32` store to
`q`" under (E) with the standard discipline: (1) for all `p, q`, the swap is a refinement from
every initial state in which every allocated byte of `[p, p + 4)` belongs to a declared object;
(2) it is not the case that, for all `p, q`, the swap is a refinement from every initial state in
which every allocated byte of `[p, p + 4)` is allocated storage (it fails at `p = q = 0`). -/
theorem store_swap_scheme_sound_on_declared_not_on_allocated :
    (∀ p q, ReorderSoundFrom (fun σ => DeclaredOn σ p 4) (stepE stdCfg)
        [.store .u32 p 0, .store .f32 q 1] [.store .f32 q 1, .store .u32 p 0]) ∧
    ¬ (∀ p q, ReorderSoundFrom (fun σ => AllocatedOn σ p 4) (stepE stdCfg)
        [.store .u32 p 0, .store .f32 q 1] [.store .f32 q 1, .store .u32 p 0]) :=
  ⟨fun p q => store_store_reorder_sound_E_of_declared_of_noCommonLeaf_of_ne_u8 .u32 .f32 p q 0 1
      (by decide) (by decide) (by decide),
   fun h => not_reorderSoundFrom_of [] [.load 2 .u8 0, .out 2]
      ((freshAt 0 16 []).withRegs (regs2 ones4 twos4)) (by decide) (by decide) (h 0 0)⟩

/-- Non-vacuity of R5c: at `p = 0, q = 4` a declared `pair` object satisfies the declared
precondition and the scheme's source block is defined; at `p = q = 0` untyped allocated
storage satisfies the allocated precondition. -/
theorem store_swap_scheme_nonvacuous :
    DeclaredOn ((declPairSt []).withRegs (regs2 ones4 twos4)) 0 4 ∧
    exec (stepE stdCfg) [.store .u32 0 0, .store .f32 4 1, .load 2 .pair 0, .out 2]
      ((declPairSt []).withRegs (regs2 ones4 twos4)) = .done [ones4 ++ twos4] ∧
    AllocatedOn ((freshAt 0 16 []).withRegs (regs2 ones4 twos4)) 0 4 := by decide

/-- A block that, after making `[0, 4)` defined to access (`memcpy 0 0 4` faults unless the range
is allocated) and putting a valid `f32` value in register `0`, prints register `1` and then
stores an `f32` to `0`. -/
def allocHoistSrc : List Instr := [.memcpy 0 0 4, .set 0 ones4, .out 1, .store .f32 0 0]

/-- The same block with the store moved above the `out`. -/
def allocHoistTgt : List Instr := [.memcpy 0 0 4, .set 0 ones4, .store .f32 0 0, .out 1]

theorem allocHoist_runs_eq (σ : St) (t : List Val) (hA : AllocatedOn σ 0 4) :
    runFrom (stepE stdCfg) allocHoistTgt σ t = runFrom (stepE stdCfg) allocHoistSrc σ t := by
  cases hm : readRange σ.mem 0 4 with
  | none =>
    have h1 : stepE stdCfg (.memcpy 0 0 4) σ = .fault .base := by simp [stepE, hm]
    simp only [allocHoistSrc, allocHoistTgt]
    rw [runFrom_cons_fault h1, runFrom_cons_fault h1]
  | some cs =>
    let σ1 : St := { σ with mem := updRange σ.mem 0 4 (copyFrom cs) }
    have h1 : stepE stdCfg (.memcpy 0 0 4) σ = .next σ1 := by
      simp [stepE, stdCfg, hm, copyBytesOk_stdCompat, σ1]
    have hA1 : AllocatedOn σ1 0 4 := allocatedOn_step _ _ _ hA (Or.inl h1)
    let σ2 : St := { σ1 with regs := updReg σ1.regs 0 ones4 }
    have h2 : stepE stdCfg (.set 0 ones4) σ1 = .next σ2 := rfl
    have hsome : (readRange σ2.mem 0 Ty.f32.size).isSome := by
      apply readRange_isSome
      intro i hi
      show (updRange σ.mem 0 4 (copyFrom cs) (0 + i)).isSome
      rw [updRange_isSome, readRange_get hm i (by have := readRange_length hm; simp [Ty.size, Ty.leaves] at hi; omega)]
      rfl
    obtain ⟨ds, hds⟩ := Option.isSome_iff_exists.mp hsome
    have hdok : DeclOk stdCompat ds .f32 = true := by
      unfold DeclOk
      rw [List.all_eq_true]
      intro x hx
      obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hx
      have hl : ds.length = 4 := readRange_length hds
      have hn1 : n < ds.length := by simp [List.length_zip] at hn; omega
      have e := readRange_get hds n hn1
      have hal := hA1 n (by omega)
      have e' : σ1.mem (0 + n) = some ds[n] := e
      rw [e'] at hal
      simp only [List.getElem_zip]
      simp only [Option.all] at hal
      cases he : ds[n].eff with
      | alloc _ => rfl
      | decl d => rw [he] at hal; cases hal
    have hv : Ty.f32.Valid (σ2.regs 0) := by simp [σ2, updReg, ones4, Ty.Valid, Ty.size, Ty.leaves]
    have h3 := stepE_store_of (cfg := stdCfg) hds hv hdok
    simp only [allocHoistSrc, allocHoistTgt]
    rw [runFrom_cons_next h1, runFrom_cons_next h1, runFrom_cons_next h2, runFrom_cons_next h2,
      runFrom_cons_next h3, runFrom_cons_emit rfl, runFrom_cons_emit rfl, runFrom_cons_next h3]

/-- Over arbitrary block replacements the two preconditions are incomparable even for a pure
reordering: moving an `f32` store above an `out` (after a guard that makes `[0, 4)` accessible)
is sound from every state whose bytes `[0, 4)` are allocated storage, with a defined source run,
but not sound from states whose bytes `[0, 4)` are declared. -/
theorem declared_and_allocated_preconditions_incomparable :
    AllocatedOn (freshAt 0 16 ones4) 0 4 ∧
    exec (stepE stdCfg) allocHoistSrc (freshAt 0 16 ones4) = .done [ones4] ∧
    ReorderSoundFrom (fun σ => AllocatedOn σ 0 4) (stepE stdCfg) allocHoistSrc allocHoistTgt ∧
    DeclaredOn (declSt .u32 4 ones4) 0 4 ∧
    ¬ ReorderSoundFrom (fun σ => DeclaredOn σ 0 4) (stepE stdCfg) allocHoistSrc allocHoistTgt :=
  ⟨by decide, by decide,
   reorderSoundFrom_of_eq (Inv := fun σ => AllocatedOn σ 0 4) (fun _ h => h) allocatedOn_step
     (fun σ t hA => allocHoist_runs_eq σ t hA),
   by decide,
   not_reorderSoundFrom_of [] [] (declSt .u32 4 ones4) (by decide) (by decide)⟩

/-! ## R6. The sound alternative under (U): disjointness, not types -/

/-- **R6.** Under the untyped semantics: if the address ranges `[p, p + T.size)` and
`[q, q + U.size)` are disjoint and the load's destination register `s` differs from the store's
source register `r`, then moving a `T`-load from `p` above a `U`-store to `q` is a refinement in
every context and from every initial state. No type hypothesis is involved. -/
theorem hoist_load_above_store_sound_U_of_disjoint_ranges (T U : Ty) (p q : Nat) (s r : Reg)
    (hdisj : RangesDisjoint p T.size q U.size) (hsr : s ≠ r) :
    ReorderSound stepU [.store U q r, .load s T p] [.load s T p, .store U q r] := by
  refine reorderSoundFrom_of_block (Inv := fun _ => True) (fun _ _ => trivial)
    (fun _ _ _ _ _ => trivial) ?_
  intro u t _
  rcases block2_cases (stepU_store_noEmit U q r) (stepU_load_noEmit s T p) u t with
    h | ⟨u1, u2, h1, h2, hrun⟩
  · exact Or.inl h
  · refine Or.inr ⟨u2, hrun, ?_⟩
    obtain ⟨hsome, hv, rfl⟩ := stepU_store_next h1
    obtain ⟨bs, hbs, rfl⟩ := stepU_load_next h2
    have hbs0 : readRange (updRange u.mem q U.size (fun i _ => (u.regs r).getD i 0)) p T.size =
        some bs := hbs
    have hbs' : readRange u.mem p T.size = some bs := by
      rwa [readRange_updRange_disjoint _ _ _ _ _ _ hdisj] at hbs0
    have hregs : updReg u.regs s bs r = u.regs r := by simp [updReg, Ne.symm hsr]
    refine block2_ok (stepU_load_of hbs') ?_
    have hv' : U.Valid ((({ u with regs := updReg u.regs s bs } : USt)).regs r) := by
      simpa [hregs] using hv
    rw [stepU_store_of (u := { u with regs := updReg u.regs s bs }) hsome hv']
    simp [hregs]

/-- A fully proved small instance of R6 (also its non-vacuity witness): `T = f32` at `8`,
`U = u32` at `0`; the hypotheses hold and, in the context `[] / [out 1]` from `uWit u32 0`, the
target's behaviours are among the source's. -/
theorem hoist_U_disjoint_instance :
    RangesDisjoint 8 Ty.f32.size 0 Ty.u32.size ∧ (1 : Reg) ≠ 0 ∧
    Refines (Beh stepU ([] ++ [.load 1 .f32 8, .store .u32 0 0] ++ [.out 1]) (uWit .u32 0))
            (Beh stepU ([] ++ [.store .u32 0 0, .load 1 .f32 8] ++ [.out 1]) (uWit .u32 0)) :=
  ⟨by decide, by decide, (refines_beh_iff _ _ _ _).2 (by decide)⟩

/-- R6 tightness (`hdisj`), witness class: overlapping addresses `p = q = 0` on untyped memory,
distinct registers, and the hoist is not sound under (U), even for the types `f32`/`u32` that
share no leaf. -/
theorem hoist_U_needs_disjoint_ranges :
    ¬ RangesDisjoint 0 Ty.f32.size 0 Ty.u32.size ∧ (1 : Reg) ≠ 0 ∧ NoCommonLeaf .f32 .u32 ∧
    ¬ ReorderSound stepU [.store .u32 0 0, .load 1 .f32 0] [.load 1 .f32 0, .store .u32 0 0] :=
  ⟨by decide, by decide, by decide,
   not_reorderSoundFrom_of [] [.out 1] (uWit .u32 0) trivial (by decide)⟩

/-- R6 tightness (`hsr`), witness class: disjoint addresses `p = 8, q = 0` on untyped memory.
The load overwrites the store's source register (`s = r = 0`) and the hoist is not sound. -/
theorem hoist_U_needs_distinct_registers :
    RangesDisjoint 8 Ty.f32.size 0 Ty.u32.size ∧
    ¬ ReorderSound stepU [.store .u32 0 0, .load 0 .f32 8] [.load 0 .f32 8, .store .u32 0 0] :=
  ⟨by decide,
   not_reorderSoundFrom_of [] [.load 2 .u8 0, .out 2] (uWit .u32 0) trivial (by decide)⟩

end Results
end Toy.Tbaa
