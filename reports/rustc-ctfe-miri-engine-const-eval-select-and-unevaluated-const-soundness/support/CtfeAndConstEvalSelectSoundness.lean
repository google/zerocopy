/-
  CtfeAndConstEvalSelectSoundness.lean
  Standalone Lean v4.34.1 mechanization (Init-only; 0 `sorry`, 0 `Classical.choice`,
  0 `omega`, 0 `bv_decide`, 0 `native_decide`, 0 `partial def`, 0 `._unsafe_rec`).

  Establishes relational ground truth for:
  1. Dual-mode MIR evaluation: `ctfeEval` (`CompileTimeMachine` symbolic `AllocId × Offset`
     provenance, deterministic fuel, forbidden ptr-to-int exposure, 3-valued `guaranteedPtrEq`,
     and final `InternValidFreeze` validation) vs. `rtEval` (concrete `ConcreteLayout`
     base addresses, pointer alignment inspection, and non-deterministic `is_val_statically_known`
     oracle `Nat → Bool`).
  2. Soundness of 3-valued `ctfeGuaranteedPtrEq` across all valid concrete layouts, plus
     proof that `GlobalAlloc::Memory` (`constMemory`) must remain `none` (`2`) under
     LLVM constant deduplication.
  3. Direct and contextual (`run_utf8_validation`-style helper-invariant) relational soundness
     for `const_eval_select`, plus Oracle-Bit Invariance for `is_val_statically_known`.
  4. Master CTFE-to-Runtime Refinement & `Const::Unevaluated` Substitution Soundness theorem.
  5. Three concrete sharpness counterexamples (`CE1`, `CE2`, `CE3`) proving every hypothesis
     is necessary.
-/

namespace CtfeAndConstEvalSelectSoundness

/-! ## 1. Symbolic Provenance, Cell Mutability, and Heap Model -/

abbrev AllocId := Nat

/-- Mirrors `rustc` allocation provenance classes:
    - `staticItem`: `GlobalAlloc::Static` (unique guaranteed runtime identity while live),
    - `constMemory`: `GlobalAlloc::Memory` (subject to LLVM/CGU deduplication or duplication),
    - `stackLocal`: transient per-frame stack allocation. -/
inductive AllocKind where
  | staticItem
  | constMemory
  | stackLocal
  deriving DecidableEq

/-- Mirrors `rustc_ast::Mutability::{Not, Mut}` on interned allocations. -/
inductive Mutability where
  | immut
  | mutWritable
  deriving DecidableEq

/-- Tracks whether a memory slot lies outside or inside an `UnsafeCell` (`!Freeze`). -/
inductive CellKind where
  | frozen
  | unsafeCell
  deriving DecidableEq

/-- Runtime and CTFE values. Pointers carry `(aid, off)`; `ctfeEval` forbids inspecting
    concrete integer addresses, whereas `rtEval` resolves `(aid, off)` via `ConcreteLayout`. -/
inductive Val where
  | scalar (n : Nat)
  | ptr (aid : AllocId) (off : Nat)
  | zst
  | uninit
  deriving DecidableEq

structure Slot where
  val : Val
  cell : CellKind
  deriving DecidableEq

structure Allocation where
  kind : AllocKind
  mutbl : Mutability
  align : Nat
  slots : List Slot
  deriving DecidableEq

def Allocation.size (a : Allocation) : Nat :=
  a.slots.length

def readSlotAt (slots : List Slot) (idx : Nat) : Option Slot :=
  (slots.foldr
    (fun s rec k =>
      match k with
      | 0 => some s
      | k' + 1 => rec k')
    (fun _ => none)) idx

def writeSlotAt (slots : List Slot) (idx : Nat) (v : Val) : Option (List Slot) :=
  match readSlotAt slots idx with
  | none => none
  | some s => some (slots.set idx { s with val := v })

theorem writeSlotAt_length (slots : List Slot) (off : Nat) (v : Val) (slots' : List Slot)
    (h : writeSlotAt slots off v = some slots') :
    slots'.length = slots.length := by
  unfold writeSlotAt at h
  cases hr : readSlotAt slots off with
  | none =>
      rw [hr] at h
      cases h
  | some s =>
      rw [hr] at h
      injection h with hEq
      rw [← hEq]
      exact List.length_set

abbrev Heap := List (AllocId × Allocation)

def Heap.lookup (H : Heap) (aid : AllocId) : Option Allocation :=
  H.foldr (fun pair rec => if pair.1 = aid then some pair.2 else rec) none

def Heap.update (H : Heap) (aid : AllocId) (a : Allocation) : Heap :=
  (aid, a) :: H

def Heap.maxId (H : Heap) : Nat :=
  H.foldr (fun pair rec => Nat.max pair.1 rec) 0

def Heap.freshId (H : Heap) : AllocId :=
  Heap.maxId H + 1

theorem Heap.lookup_gt_maxId_none :
    ∀ (H : Heap) (aid : AllocId), Heap.maxId H < aid → Heap.lookup H aid = none
  | [], _, _ => rfl
  | (id0, _) :: rest, aid, hLt => by
      dsimp only [Heap.maxId, List.foldr] at hLt
      have hId0 : id0 < aid := Nat.lt_of_le_of_lt (Nat.le_max_left id0 (Heap.maxId rest)) hLt
      have hRest : Heap.maxId rest < aid :=
        Nat.lt_of_le_of_lt (Nat.le_max_right id0 (Heap.maxId rest)) hLt
      have hNe : id0 ≠ aid := Nat.ne_of_lt hId0
      dsimp only [Heap.lookup, List.foldr]
      simp only [hNe, ite_false]
      exact Heap.lookup_gt_maxId_none rest aid hRest

theorem Heap.lookup_freshId_none (H : Heap) :
    Heap.lookup H (Heap.freshId H) = none :=
  Heap.lookup_gt_maxId_none H (Heap.freshId H) (Nat.lt_succ_self (Heap.maxId H))

theorem Heap.lookup_update_eq (H : Heap) (aid : AllocId) (a : Allocation) :
    Heap.lookup (Heap.update H aid a) aid = some a := by
  simp [Heap.update, Heap.lookup]

theorem Heap.lookup_update_ne (H : Heap) (aid aid' : AllocId) (a : Allocation)
    (hNe : aid ≠ aid') :
    Heap.lookup (Heap.update H aid a) aid' = Heap.lookup H aid' := by
  simp [Heap.update, Heap.lookup, hNe]

/-! ## 2. Concrete Allocator Layout and 3-Valued `ptr_guaranteed_cmp` -/

structure ConcreteLayout where
  baseAddr : AllocId → Nat

def ConcreteLayout.addrOf (L : ConcreteLayout) (aid : AllocId) (off : Nat) : Nat :=
  L.baseAddr aid + off

/-- Admissible concrete runtime placement of allocations:
    1. Every allocation has a non-null positive base address (`0 < L.baseAddr aid`);
    2. Every live allocation respects its declared alignment;
    3. Distinct `staticItem` (`GlobalAlloc::Static`) allocations occupy disjoint
       address ranges `[base, base + size)`. `constMemory` (`GlobalAlloc::Memory`)
       is intentionally NOT assumed disjoint across distinct `AllocId`s because LLVM / CGU
       constant merging may alias identical read-only constants (`#73722`, `#128775`). -/
structure ValidLayout (H : Heap) (L : ConcreteLayout) : Prop where
  nonNull : ∀ aid, 0 < L.baseAddr aid
  aligned : ∀ aid a, Heap.lookup H aid = some a → 0 < a.align → (L.baseAddr aid) % a.align = 0
  staticDisjoint :
    ∀ aid1 a1 aid2 a2,
      Heap.lookup H aid1 = some a1 →
      Heap.lookup H aid2 = some a2 →
      aid1 ≠ aid2 →
      a1.kind = .staticItem →
      a2.kind = .staticItem →
      L.baseAddr aid1 + a1.size ≤ L.baseAddr aid2 ∨
      L.baseAddr aid2 + a2.size ≤ L.baseAddr aid1

/-- Mirrors `CompileTimeMachine::ptr_guaranteed_cmp` (`const_eval/machine.rs:278-387`):
    decides equality for `GlobalAlloc::Static` pairs (same `AllocId`, or distinct `AllocId`
    with both offsets strictly in-bounds `off < size`), and returns `none` (`2`) for
    `constMemory`, `stackLocal`, or out-of-bounds one-past-the-end pointers. -/
def ctfeGuaranteedPtrEq (H : Heap) (aid1 off1 aid2 off2 : Nat) : Option Bool :=
  match Heap.lookup H aid1, Heap.lookup H aid2 with
  | some a1, some a2 =>
      match a1.kind, a2.kind with
      | .staticItem, .staticItem =>
          if aid1 = aid2 then
            some (decide (off1 = off2))
          else if decide (off1 < a1.size) && decide (off2 < a2.size) then
            some false
          else
            none
      | _, _ => none
  | _, _ => none

private theorem add_left_eq_decide (base x y : Nat) :
    decide (base + x = base + y) = decide (x = y) := by
  by_cases h : x = y
  · subst h
    rw [decide_eq_true rfl, decide_eq_true rfl]
  · have hAddNe : base + x ≠ base + y := fun hEq => h (Nat.add_left_cancel hEq)
    rw [decide_eq_false h, decide_eq_false hAddNe]

/-- **Theorem 1 (`ctfeGuaranteedPtrEq` Soundness):**
    Whenever `ctfeGuaranteedPtrEq` returns a definite answer `some b`, concrete runtime
    pointer equality agrees with `b` under EVERY valid concrete allocator layout `L`. -/
theorem ctfe_guaranteed_ptr_eq_sound
    {H : Heap} {L : ConcreteLayout} {aid1 off1 aid2 off2 : Nat} {b : Bool}
    (hLayout : ValidLayout H L)
    (hGuaranteed : ctfeGuaranteedPtrEq H aid1 off1 aid2 off2 = some b) :
    decide (L.addrOf aid1 off1 = L.addrOf aid2 off2) = b := by
  unfold ctfeGuaranteedPtrEq at hGuaranteed
  cases h1 : Heap.lookup H aid1 with
  | none => rw [h1] at hGuaranteed; cases hGuaranteed
  | some a1 =>
      rw [h1] at hGuaranteed
      cases h2 : Heap.lookup H aid2 with
      | none => rw [h2] at hGuaranteed; cases hGuaranteed
      | some a2 =>
          rw [h2] at hGuaranteed
          dsimp only at hGuaranteed
          cases hk1 : a1.kind <;> cases hk2 : a2.kind <;>
            rw [hk1, hk2] at hGuaranteed <;> dsimp only at hGuaranteed
          case staticItem.staticItem =>
            by_cases hAid : aid1 = aid2
            · simp only [hAid, ite_true] at hGuaranteed
              injection hGuaranteed with hB
              subst hAid
              unfold ConcreteLayout.addrOf
              rw [add_left_eq_decide]
              exact hB
            · simp only [hAid, ite_false] at hGuaranteed
              cases ho1 : decide (off1 < a1.size) with
              | false =>
                  rw [ho1] at hGuaranteed
                  simp at hGuaranteed
              | true =>
                  cases ho2 : decide (off2 < a2.size) with
                  | false =>
                      rw [ho1, ho2] at hGuaranteed
                      simp at hGuaranteed
                  | true =>
                      rw [ho1, ho2] at hGuaranteed
                      simp at hGuaranteed
                      have hOff1 : off1 < a1.size := of_decide_eq_true ho1
                      have hOff2 : off2 < a2.size := of_decide_eq_true ho2
                      have hDisj := hLayout.staticDisjoint aid1 a1 aid2 a2 h1 h2 hAid hk1 hk2
                      have hAddrNe : L.addrOf aid1 off1 ≠ L.addrOf aid2 off2 := by
                        unfold ConcreteLayout.addrOf
                        cases hDisj with
                        | inl hLeft =>
                            have s1 : L.baseAddr aid1 + off1 < L.baseAddr aid1 + a1.size :=
                              Nat.add_lt_add_left hOff1 (L.baseAddr aid1)
                            have s2 : L.baseAddr aid1 + off1 < L.baseAddr aid2 :=
                              Nat.lt_of_lt_of_le s1 hLeft
                            have s3 : L.baseAddr aid1 + off1 < L.baseAddr aid2 + off2 :=
                              Nat.lt_of_lt_of_le s2 (Nat.le_add_right (L.baseAddr aid2) off2)
                            exact Nat.ne_of_lt s3
                        | inr hRight =>
                            have s1 : L.baseAddr aid2 + off2 < L.baseAddr aid2 + a2.size :=
                              Nat.add_lt_add_left hOff2 (L.baseAddr aid2)
                            have s2 : L.baseAddr aid2 + off2 < L.baseAddr aid1 :=
                              Nat.lt_of_lt_of_le s1 hRight
                            have s3 : L.baseAddr aid2 + off2 < L.baseAddr aid1 + off1 :=
                              Nat.lt_of_lt_of_le s2 (Nat.le_add_right (L.baseAddr aid1) off1)
                            exact Ne.symm (Nat.ne_of_lt s3)
                      rw [decide_eq_false hAddrNe]
                      exact hGuaranteed.symm
          all_goals cases hGuaranteed

private def constWitnessAlloc : Allocation := {
  kind := .constMemory
  mutbl := .immut
  align := 1
  slots := [{ val := .scalar 104, cell := .frozen }]
}

private def constWitnessHeap : Heap :=
  [(1, constWitnessAlloc), (2, constWitnessAlloc)]

private def mergedConstLayout : ConcreteLayout :=
  { baseAddr := fun _ => 64 }

private def splitConstLayout : ConcreteLayout :=
  { baseAddr := fun aid => if aid = 1 then 64 else 128 }

/-- **Theorem 2 (Necessity of `none` on `constMemory` / `GlobalAlloc::Memory`):**
    Two distinct `constMemory` allocations admit BOTH a deduplicated `ValidLayout` where
    their runtime addresses coincide AND a non-deduplicated `ValidLayout` where their
    runtime addresses differ, proving CTFE cannot soundly decide equality either way. -/
theorem const_memory_guaranteed_eq_indeterminate_necessary :
    ∃ (H : Heap) (L_merged L_split : ConcreteLayout),
      ValidLayout H L_merged ∧
      ValidLayout H L_split ∧
      ctfeGuaranteedPtrEq H 1 0 2 0 = none ∧
      decide (L_merged.addrOf 1 0 = L_merged.addrOf 2 0) = true ∧
      decide (L_split.addrOf 1 0 = L_split.addrOf 2 0) = false := by
  refine ⟨constWitnessHeap, mergedConstLayout, splitConstLayout, ?_, ?_, rfl, rfl, rfl⟩
  · refine ⟨fun _ => Nat.zero_lt_succ 63, ?_, ?_⟩
    · intro aid a hLook _
      by_cases h1 : 1 = aid
      · simp [constWitnessHeap, Heap.lookup, h1] at hLook
        rw [← hLook]; exact Nat.mod_one 64
      · by_cases h2 : 2 = aid
        · simp [constWitnessHeap, Heap.lookup, h1, h2] at hLook
          rw [← hLook]; exact Nat.mod_one 64
        · simp [constWitnessHeap, Heap.lookup, h1, h2] at hLook
    · intro aid1 a1 _ _ hLook1 _ _ hk1 _
      by_cases h1 : 1 = aid1
      · simp [constWitnessHeap, Heap.lookup, h1] at hLook1
        rw [← hLook1] at hk1; cases hk1
      · by_cases h2 : 2 = aid1
        · simp [constWitnessHeap, Heap.lookup, h1, h2] at hLook1
          rw [← hLook1] at hk1; cases hk1
        · simp [constWitnessHeap, Heap.lookup, h1, h2] at hLook1
  · refine ⟨?_, ?_, ?_⟩
    · intro aid
      by_cases h1 : aid = 1
      · simp [splitConstLayout, h1]
      · simp [splitConstLayout, h1]
    · intro aid a hLook _
      by_cases h1 : 1 = aid
      · simp [constWitnessHeap, Heap.lookup, h1] at hLook
        rw [← hLook]; exact Nat.mod_one (splitConstLayout.baseAddr aid)
      · by_cases h2 : 2 = aid
        · simp [constWitnessHeap, Heap.lookup, h1, h2] at hLook
          rw [← hLook]; exact Nat.mod_one (splitConstLayout.baseAddr aid)
        · simp [constWitnessHeap, Heap.lookup, h1, h2] at hLook
    · intro aid1 a1 _ _ hLook1 _ _ hk1 _
      by_cases h1 : 1 = aid1
      · simp [constWitnessHeap, Heap.lookup, h1] at hLook1
        rw [← hLook1] at hk1; cases hk1
      · by_cases h2 : 2 = aid1
        · simp [constWitnessHeap, Heap.lookup, h1, h2] at hLook1
          rw [← hLook1] at hk1; cases hk1
        · simp [constWitnessHeap, Heap.lookup, h1, h2] at hLook1

/-! ## 3. Deep Validity & `Freeze` / `UnsafeCell` Interning Gate -/

inductive InternMode where
  | constByValue
  | promotedSharedRef
  | staticImmutDecl
  | staticMutDecl
  deriving DecidableEq

/-- Exact mutability computation in `intern_const_alloc_recursive` (`intern.rs:214-240`). -/
def internBaseMutability (mode : InternMode) (isFreeze : Bool) : Mutability :=
  match mode with
  | .constByValue => .immut
  | .promotedSharedRef => .immut
  | .staticImmutDecl => if isFreeze then .immut else .mutWritable
  | .staticMutDecl => .mutWritable

theorem static_unsafecell_interned_writable :
    internBaseMutability .staticImmutDecl false = .mutWritable ∧
    internBaseMutability .staticImmutDecl true = .immut :=
  ⟨rfl, rfl⟩

def allSlotsInit (slots : List Slot) : Bool :=
  slots.foldr (fun s rec => decide (s.val ≠ .uninit) && rec) true

def allSlotsFrozen (slots : List Slot) : Bool :=
  slots.foldr (fun s rec => decide (s.cell = .frozen) && rec) true

/-- Executable boolean checker for `InternValidFreeze` (`const_validate_mplace` +
    `CtfeValidationMode`, including the `validity.rs:1383` ZST `UnsafeCell` carve-out:
    a 0-slot allocation permits `UnsafeCell` element tags, whereas any allocation with
    `0 < a.size` behind an immutable reference requires `allSlotsFrozen a.slots = true`). -/
def checkInternValidFreeze (H : Heap) (v : Val) : Bool :=
  match v with
  | .scalar _ => true
  | .zst => true
  | .uninit => false
  | .ptr aid off =>
      match Heap.lookup H aid with
      | none => false
      | some a =>
          decide (a.mutbl = .immut) &&
          (decide (off < a.size) || (decide (off = 0) && decide (a.size = 0))) &&
          allSlotsInit a.slots &&
          (decide (a.size = 0) || allSlotsFrozen a.slots)

def InternValidFreeze (H : Heap) (v : Val) : Prop :=
  checkInternValidFreeze H v = true

theorem allSlotsInit_read_ne_uninit :
    ∀ (slots : List Slot) (off : Nat) (s : Slot),
      allSlotsInit slots = true →
      readSlotAt slots off = some s →
      s.val ≠ .uninit
  | [], _, _, _, hRead => by cases hRead
  | _ :: _, 0, _, hInit, hRead => by
      simp only [allSlotsInit, List.foldr, Bool.and_eq_true] at hInit
      injection hRead with hEq
      rw [← hEq]
      exact of_decide_eq_true hInit.1
  | _ :: rest, k + 1, s, hInit, hRead => by
      simp only [allSlotsInit, List.foldr, Bool.and_eq_true] at hInit
      exact allSlotsInit_read_ne_uninit rest k s hInit.2 hRead

/-! ## 4. Dual-Mode MIR Expression Language (`ctfeEval` vs. `rtEval`) -/

inductive CtfeErr where
  | outOfFuel
  | uninitRead
  | typeMismatchOrPtrAsInt
  | danglingOrOob
  | writeToImmut
  | unsupportedPtrToInt
  | indeterminatePtrCmp
  | invalidConstIntern
  | constPanic
  deriving DecidableEq

inductive RtErr where
  | outOfFuel
  | uninitRead
  | typeMismatch
  | danglingOrOob
  | writeToImmut
  | rtPanic
  deriving DecidableEq

inductive EvalRes (E : Type) (A : Type) where
  | ok (val : A)
  | err (e : E)
  deriving DecidableEq

inductive MirExpr where
  | lit (v : Val)
  | panic
  | add (e1 e2 : MirExpr)
  | eqScalar (e1 e2 : MirExpr)
  | ptrOffset (base : MirExpr) (delta : MirExpr)
  | ptrAddrMod (ptrExpr : MirExpr) (modulus : Nat)
  | guaranteedPtrEq (p1 p2 : MirExpr)
  | load (ptrExpr : MirExpr)
  | store (ptrExpr : MirExpr) (valExpr : MirExpr)
  | allocLocal (align : Nat) (cell : CellKind) (initExpr : MirExpr)
  | seq (e1 e2 : MirExpr)
  | letBind (bound : MirExpr) (cont : Val → MirExpr)
  | iteNonZero (cond : MirExpr) (thenBr elseBr : MirExpr)
  | constEvalSelect (site : Nat) (arg : MirExpr) (ctArm : Val → MirExpr) (rtArm : Val → MirExpr)
  | isValStaticallyKnown (site : Nat) (arg : MirExpr) (kArm : Bool → MirExpr)
  | unevalConst (body : MirExpr)

def ctfeEvalStep (step : Heap → MirExpr → EvalRes CtfeErr (Val × Heap))
    (H : Heap) (expr : MirExpr) : EvalRes CtfeErr (Val × Heap) :=
  match expr with
  | .lit .uninit => .err .uninitRead
  | .lit v => .ok (v, H)
  | .panic => .err .constPanic
  | .add e1 e2 =>
      match step H e1 with
      | .err err => .err err
      | .ok (v1, H1) =>
          match step H1 e2 with
          | .err err => .err err
          | .ok (v2, H2) =>
              match v1, v2 with
              | .scalar n1, .scalar n2 => .ok (.scalar (n1 + n2), H2)
              | .uninit, _ => .err .uninitRead
              | _, .uninit => .err .uninitRead
              | _, _ => .err .typeMismatchOrPtrAsInt
  | .eqScalar e1 e2 =>
      match step H e1 with
      | .err err => .err err
      | .ok (v1, H1) =>
          match step H1 e2 with
          | .err err => .err err
          | .ok (v2, H2) =>
              match v1, v2 with
              | .scalar n1, .scalar n2 =>
                  .ok (.scalar (if n1 = n2 then 1 else 0), H2)
              | .uninit, _ => .err .uninitRead
              | _, .uninit => .err .uninitRead
              | _, _ => .err .typeMismatchOrPtrAsInt
  | .ptrOffset base delta =>
      match step H base with
      | .err err => .err err
      | .ok (vb, H1) =>
          match step H1 delta with
          | .err err => .err err
          | .ok (vd, H2) =>
              match vb, vd with
              | .ptr aid off, .scalar d =>
                  match Heap.lookup H2 aid with
                  | some a =>
                      if off + d ≤ a.size then
                        .ok (.ptr aid (off + d), H2)
                      else
                        .err .danglingOrOob
                  | none => .err .danglingOrOob
              | _, _ => .err .typeMismatchOrPtrAsInt
  | .ptrAddrMod _ _ => .err .unsupportedPtrToInt
  | .guaranteedPtrEq p1 p2 =>
      match step H p1 with
      | .err err => .err err
      | .ok (v1, H1) =>
          match step H1 p2 with
          | .err err => .err err
          | .ok (v2, H2) =>
              match v1, v2 with
              | .ptr a1 o1, .ptr a2 o2 =>
                  match ctfeGuaranteedPtrEq H2 a1 o1 a2 o2 with
                  | some true => .ok (.scalar 1, H2)
                  | some false => .ok (.scalar 0, H2)
                  | none => .err .indeterminatePtrCmp
              | _, _ => .err .typeMismatchOrPtrAsInt
  | .load ptrExpr =>
      match step H ptrExpr with
      | .err err => .err err
      | .ok (vp, H1) =>
          match vp with
          | .ptr aid off =>
              match Heap.lookup H1 aid with
              | none => .err .danglingOrOob
              | some a =>
                  match readSlotAt a.slots off with
                  | none => .err .danglingOrOob
                  | some s =>
                      match s.val with
                      | .uninit => .err .uninitRead
                      | v => .ok (v, H1)
          | _ => .err .typeMismatchOrPtrAsInt
  | .store ptrExpr valExpr =>
      match step H ptrExpr with
      | .err err => .err err
      | .ok (vp, H1) =>
          match step H1 valExpr with
          | .err err => .err err
          | .ok (vv, H2) =>
              match vp with
              | .ptr aid off =>
                  match Heap.lookup H2 aid with
                  | none => .err .danglingOrOob
                  | some a =>
                      match a.mutbl with
                      | .immut => .err .writeToImmut
                      | .mutWritable =>
                          match writeSlotAt a.slots off vv with
                          | none => .err .danglingOrOob
                          | some slots' =>
                              .ok (.zst, Heap.update H2 aid { a with slots := slots' })
              | _ => .err .typeMismatchOrPtrAsInt
  | .allocLocal align cell initExpr =>
      match step H initExpr with
      | .err err => .err err
      | .ok (vInit, H1) =>
          if decide (align = 0) || decide (vInit = .uninit) then
            .err .uninitRead
          else
            let aid := Heap.freshId H1
            let alloc : Allocation := {
              kind := .stackLocal
              mutbl := .mutWritable
              align := 1
              slots := [{ val := vInit, cell := cell }]
            }
            .ok (.ptr aid 0, Heap.update H1 aid alloc)
  | .seq e1 e2 =>
      match step H e1 with
      | .err err => .err err
      | .ok (_, H1) => step H1 e2
  | .letBind bound cont =>
      match step H bound with
      | .err err => .err err
      | .ok (vb, H1) => step H1 (cont vb)
  | .iteNonZero cond thenBr elseBr =>
      match step H cond with
      | .err err => .err err
      | .ok (vc, H1) =>
          match vc with
          | .scalar 0 => step H1 elseBr
          | .scalar (_ + 1) => step H1 thenBr
          | .uninit => .err .uninitRead
          | _ => .err .typeMismatchOrPtrAsInt
  | .constEvalSelect _ arg ctArm _ =>
      match step H arg with
      | .err err => .err err
      | .ok (vArg, H1) => step H1 (ctArm vArg)
  | .isValStaticallyKnown _ arg kArm =>
      match step H arg with
      | .err err => .err err
      | .ok (_, H1) => step H1 (kArm false)
  | .unevalConst body =>
      match step H body with
      | .err err => .err err
      | .ok (v, H1) =>
          if checkInternValidFreeze H1 v then .ok (v, H1) else .err .invalidConstIntern

def ctfeEval (fuel : Nat) (H : Heap) (expr : MirExpr) : EvalRes CtfeErr (Val × Heap) :=
  (Nat.repeat ctfeEvalStep fuel (fun _ _ => .err .outOfFuel)) H expr

def rtEvalStep (L : ConcreteLayout) (oracle : Nat → Bool)
    (step : Heap → MirExpr → EvalRes RtErr (Val × Heap))
    (H : Heap) (expr : MirExpr) : EvalRes RtErr (Val × Heap) :=
  match expr with
  | .lit .uninit => .err .uninitRead
  | .lit v => .ok (v, H)
  | .panic => .err .rtPanic
  | .add e1 e2 =>
      match step H e1 with
      | .err err => .err err
      | .ok (v1, H1) =>
          match step H1 e2 with
          | .err err => .err err
          | .ok (v2, H2) =>
              match v1, v2 with
              | .scalar n1, .scalar n2 => .ok (.scalar (n1 + n2), H2)
              | .uninit, _ => .err .uninitRead
              | _, .uninit => .err .uninitRead
              | _, _ => .err .typeMismatch
  | .eqScalar e1 e2 =>
      match step H e1 with
      | .err err => .err err
      | .ok (v1, H1) =>
          match step H1 e2 with
          | .err err => .err err
          | .ok (v2, H2) =>
              match v1, v2 with
              | .scalar n1, .scalar n2 =>
                  .ok (.scalar (if n1 = n2 then 1 else 0), H2)
              | .uninit, _ => .err .uninitRead
              | _, .uninit => .err .uninitRead
              | _, _ => .err .typeMismatch
  | .ptrOffset base delta =>
      match step H base with
      | .err err => .err err
      | .ok (vb, H1) =>
          match step H1 delta with
          | .err err => .err err
          | .ok (vd, H2) =>
              match vb, vd with
              | .ptr aid off, .scalar d =>
                  match Heap.lookup H2 aid with
                  | some a =>
                      if off + d ≤ a.size then
                        .ok (.ptr aid (off + d), H2)
                      else
                        .err .danglingOrOob
                  | none => .err .danglingOrOob
              | _, _ => .err .typeMismatch
  | .ptrAddrMod ptrExpr modulus =>
      match step H ptrExpr with
      | .err err => .err err
      | .ok (vp, H1) =>
          match vp with
          | .ptr aid off =>
              if modulus = 0 then .err .rtPanic
              else .ok (.scalar ((L.addrOf aid off) % modulus), H1)
          | _ => .err .typeMismatch
  | .guaranteedPtrEq p1 p2 =>
      match step H p1 with
      | .err err => .err err
      | .ok (v1, H1) =>
          match step H1 p2 with
          | .err err => .err err
          | .ok (v2, H2) =>
              match v1, v2 with
              | .ptr a1 o1, .ptr a2 o2 =>
                  let b := decide (L.addrOf a1 o1 = L.addrOf a2 o2)
                  .ok (.scalar (if b then 1 else 0), H2)
              | _, _ => .err .typeMismatch
  | .load ptrExpr =>
      match step H ptrExpr with
      | .err err => .err err
      | .ok (vp, H1) =>
          match vp with
          | .ptr aid off =>
              match Heap.lookup H1 aid with
              | none => .err .danglingOrOob
              | some a =>
                  match readSlotAt a.slots off with
                  | none => .err .danglingOrOob
                  | some s =>
                      match s.val with
                      | .uninit => .err .uninitRead
                      | v => .ok (v, H1)
          | _ => .err .typeMismatch
  | .store ptrExpr valExpr =>
      match step H ptrExpr with
      | .err err => .err err
      | .ok (vp, H1) =>
          match step H1 valExpr with
          | .err err => .err err
          | .ok (vv, H2) =>
              match vp with
              | .ptr aid off =>
                  match Heap.lookup H2 aid with
                  | none => .err .danglingOrOob
                  | some a =>
                      match a.mutbl with
                      | .immut => .err .writeToImmut
                      | .mutWritable =>
                          match writeSlotAt a.slots off vv with
                          | none => .err .danglingOrOob
                          | some slots' =>
                              .ok (.zst, Heap.update H2 aid { a with slots := slots' })
              | _ => .err .typeMismatch
  | .allocLocal align cell initExpr =>
      match step H initExpr with
      | .err err => .err err
      | .ok (vInit, H1) =>
          if decide (align = 0) || decide (vInit = .uninit) then
            .err .uninitRead
          else
            let aid := Heap.freshId H1
            let alloc : Allocation := {
              kind := .stackLocal
              mutbl := .mutWritable
              align := 1
              slots := [{ val := vInit, cell := cell }]
            }
            .ok (.ptr aid 0, Heap.update H1 aid alloc)
  | .seq e1 e2 =>
      match step H e1 with
      | .err err => .err err
      | .ok (_, H1) => step H1 e2
  | .letBind bound cont =>
      match step H bound with
      | .err err => .err err
      | .ok (vb, H1) => step H1 (cont vb)
  | .iteNonZero cond thenBr elseBr =>
      match step H cond with
      | .err err => .err err
      | .ok (vc, H1) =>
          match vc with
          | .scalar 0 => step H1 elseBr
          | .scalar (_ + 1) => step H1 thenBr
          | .uninit => .err .uninitRead
          | _ => .err .typeMismatch
  | .constEvalSelect _ arg _ rtArm =>
      match step H arg with
      | .err err => .err err
      | .ok (vArg, H1) => step H1 (rtArm vArg)
  | .isValStaticallyKnown site arg kArm =>
      match step H arg with
      | .err err => .err err
      | .ok (_, H1) => step H1 (kArm (oracle site))
  | .unevalConst body =>
      step H body

def rtEval (L : ConcreteLayout) (oracle : Nat → Bool)
    (fuel : Nat) (H : Heap) (expr : MirExpr) : EvalRes RtErr (Val × Heap) :=
  (Nat.repeat (rtEvalStep L oracle) fuel (fun _ _ => .err .outOfFuel)) H expr

@[simp] theorem ctfeEval_succ (fuel : Nat) (H : Heap) (expr : MirExpr) :
    ctfeEval (fuel + 1) H expr = ctfeEvalStep (ctfeEval fuel) H expr := rfl

@[simp] theorem rtEval_succ (L : ConcreteLayout) (oracle : Nat → Bool)
    (fuel : Nat) (H : Heap) (expr : MirExpr) :
    rtEval L oracle (fuel + 1) H expr = rtEvalStep L oracle (rtEval L oracle fuel) H expr := rfl

/-! ## 5. Heap Layout Preservation Across `ctfeEval` Transitions -/

theorem ValidLayout.update_slots
    {H : Heap} {L : ConcreteLayout} {aid : AllocId} {a : Allocation} {slots' : List Slot}
    (hLayout : ValidLayout H L)
    (hLook : Heap.lookup H aid = some a)
    (hLen : slots'.length = a.slots.length) :
    ValidLayout (Heap.update H aid { a with slots := slots' }) L := by
  refine ⟨hLayout.nonNull, ?_, ?_⟩
  · intro aid1 a1 hLook1 hAlign1
    by_cases hEq : aid = aid1
    · subst hEq
      rw [Heap.lookup_update_eq] at hLook1
      injection hLook1 with hA1
      rw [← hA1] at hAlign1 ⊢
      exact hLayout.aligned aid a hLook hAlign1
    · rw [Heap.lookup_update_ne H aid aid1 _ hEq] at hLook1
      exact hLayout.aligned aid1 a1 hLook1 hAlign1
  · intro aid1 a1 aid2 a2 hLook1 hLook2 hNe hk1 hk2
    have resolveStatic :
        ∀ x ax,
          Heap.lookup (Heap.update H aid { a with slots := slots' }) x = some ax →
          ax.kind = .staticItem →
          ∃ ax0, Heap.lookup H x = some ax0 ∧ ax0.kind = .staticItem ∧ ax0.size = ax.size := by
      intro x ax hx hkx
      by_cases hEq : aid = x
      · subst hEq
        rw [Heap.lookup_update_eq] at hx
        injection hx with hAx
        refine ⟨a, hLook, ?_, ?_⟩
        · rw [← hAx] at hkx; exact hkx
        · rw [← hAx]; unfold Allocation.size; exact hLen.symm
      · rw [Heap.lookup_update_ne H aid x _ hEq] at hx
        exact ⟨ax, hx, hkx, rfl⟩
    rcases resolveStatic aid1 a1 hLook1 hk1 with ⟨a1_0, hL1, hk1_0, hSz1⟩
    rcases resolveStatic aid2 a2 hLook2 hk2 with ⟨a2_0, hL2, hk2_0, hSz2⟩
    have hDisj := hLayout.staticDisjoint aid1 a1_0 aid2 a2_0 hL1 hL2 hNe hk1_0 hk2_0
    rw [hSz1, hSz2] at hDisj
    exact hDisj

theorem ValidLayout.alloc_stack_fresh
    {H : Heap} {L : ConcreteLayout} {cell : CellKind} {vInit : Val}
    (hLayout : ValidLayout H L) :
    let aid := Heap.freshId H
    let alloc : Allocation := {
      kind := .stackLocal
      mutbl := .mutWritable
      align := 1
      slots := [{ val := vInit, cell := cell }]
    }
    ValidLayout (Heap.update H aid alloc) L := by
  intro aid alloc
  refine ⟨hLayout.nonNull, ?_, ?_⟩
  · intro aid1 a1 hLook1 hAlign1
    by_cases hEq : aid = aid1
    · subst hEq
      rw [Heap.lookup_update_eq] at hLook1
      injection hLook1 with hA1
      rw [← hA1]
      exact Nat.mod_one (L.baseAddr aid)
    · rw [Heap.lookup_update_ne H aid aid1 alloc hEq] at hLook1
      exact hLayout.aligned aid1 a1 hLook1 hAlign1
  · intro aid1 a1 aid2 a2 hLook1 hLook2 hNe hk1 hk2
    have hNotAid1 : aid ≠ aid1 := by
      intro hEq
      subst hEq
      rw [Heap.lookup_update_eq] at hLook1
      injection hLook1 with hA1
      rw [← hA1] at hk1
      cases hk1
    have hNotAid2 : aid ≠ aid2 := by
      intro hEq
      subst hEq
      rw [Heap.lookup_update_eq] at hLook2
      injection hLook2 with hA2
      rw [← hA2] at hk2
      cases hk2
    rw [Heap.lookup_update_ne H aid aid1 alloc hNotAid1] at hLook1
    rw [Heap.lookup_update_ne H aid aid2 alloc hNotAid2] at hLook2
    exact hLayout.staticDisjoint aid1 a1 aid2 a2 hLook1 hLook2 hNe hk1 hk2

theorem ctfeEval_preserves_validLayout :
    ∀ (fuel : Nat) (H H' : Heap) (L : ConcreteLayout) (e : MirExpr) (v : Val),
      ValidLayout H L →
      ctfeEval fuel H e = .ok (v, H') →
      ValidLayout H' L
  | 0, _, _, _, _, _, _, hEval => by cases hEval
  | fuel + 1, H, H', L, expr, v, hLayout, hEval => by
      cases expr with
      | lit v0 =>
          cases v0 <;> rw [ctfeEval_succ] at hEval; dsimp only [ctfeEvalStep] at hEval
          case uninit => cases hEval
          all_goals (injection hEval with hPair; injection hPair with _ hH; rw [← hH]; exact hLayout)
      | panic => cases hEval
      | add e1 e2 =>
          rw [ctfeEval_succ] at hEval; dsimp only [ctfeEvalStep] at hEval
          cases h1 : ctfeEval fuel H e1 with
          | err _ => rw [h1] at hEval; cases hEval
          | ok p1 =>
              rcases p1 with ⟨v1, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have hL1 := ctfeEval_preserves_validLayout fuel H H1 L e1 v1 hLayout h1
              cases h2 : ctfeEval fuel H1 e2 with
              | err _ => rw [h2] at hEval; cases hEval
              | ok p2 =>
                  rcases p2 with ⟨v2, H2⟩
                  rw [h2] at hEval; dsimp only at hEval
                  have hL2 := ctfeEval_preserves_validLayout fuel H1 H2 L e2 v2 hL1 h2
                  cases v1 <;> cases v2 <;> dsimp only at hEval
                  case scalar.scalar =>
                    injection hEval with hPair; injection hPair with _ hH
                    rw [← hH]; exact hL2
                  all_goals cases hEval
      | eqScalar e1 e2 =>
          rw [ctfeEval_succ] at hEval; dsimp only [ctfeEvalStep] at hEval
          cases h1 : ctfeEval fuel H e1 with
          | err _ => rw [h1] at hEval; cases hEval
          | ok p1 =>
              rcases p1 with ⟨v1, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have hL1 := ctfeEval_preserves_validLayout fuel H H1 L e1 v1 hLayout h1
              cases h2 : ctfeEval fuel H1 e2 with
              | err _ => rw [h2] at hEval; cases hEval
              | ok p2 =>
                  rcases p2 with ⟨v2, H2⟩
                  rw [h2] at hEval; dsimp only at hEval
                  have hL2 := ctfeEval_preserves_validLayout fuel H1 H2 L e2 v2 hL1 h2
                  cases v1 <;> cases v2 <;> dsimp only at hEval
                  case scalar.scalar =>
                    injection hEval with hPair; injection hPair with _ hH
                    rw [← hH]; exact hL2
                  all_goals cases hEval
      | ptrOffset base delta =>
          rw [ctfeEval_succ] at hEval; dsimp only [ctfeEvalStep] at hEval
          cases h1 : ctfeEval fuel H base with
          | err _ => rw [h1] at hEval; cases hEval
          | ok p1 =>
              rcases p1 with ⟨vb, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have hL1 := ctfeEval_preserves_validLayout fuel H H1 L base vb hLayout h1
              cases h2 : ctfeEval fuel H1 delta with
              | err _ => rw [h2] at hEval; cases hEval
              | ok p2 =>
                  rcases p2 with ⟨vd, H2⟩
                  rw [h2] at hEval; dsimp only at hEval
                  have hL2 := ctfeEval_preserves_validLayout fuel H1 H2 L delta vd hL1 h2
                  cases vb <;> cases vd <;> dsimp only at hEval
                  case ptr.scalar aid off d =>
                    cases hLook : Heap.lookup H2 aid with
                    | none => rw [hLook] at hEval; cases hEval
                    | some a =>
                        rw [hLook] at hEval; dsimp only at hEval
                        by_cases hIn : off + d ≤ a.size
                        · simp only [hIn, ite_true] at hEval
                          injection hEval with hPair; injection hPair with _ hH
                          rw [← hH]; exact hL2
                        · simp only [hIn, ite_false] at hEval
                          cases hEval
                  all_goals cases hEval
      | ptrAddrMod _ _ => cases hEval
      | guaranteedPtrEq p1 p2 =>
          rw [ctfeEval_succ] at hEval; dsimp only [ctfeEvalStep] at hEval
          cases h1 : ctfeEval fuel H p1 with
          | err _ => rw [h1] at hEval; cases hEval
          | ok r1 =>
              rcases r1 with ⟨v1, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have hL1 := ctfeEval_preserves_validLayout fuel H H1 L p1 v1 hLayout h1
              cases h2 : ctfeEval fuel H1 p2 with
              | err _ => rw [h2] at hEval; cases hEval
              | ok r2 =>
                  rcases r2 with ⟨v2, H2⟩
                  rw [h2] at hEval; dsimp only at hEval
                  have hL2 := ctfeEval_preserves_validLayout fuel H1 H2 L p2 v2 hL1 h2
                  cases v1 <;> cases v2 <;> dsimp only at hEval
                  case ptr.ptr a1 o1 a2 o2 =>
                    cases hG : ctfeGuaranteedPtrEq H2 a1 o1 a2 o2 with
                    | none => rw [hG] at hEval; cases hEval
                    | some b =>
                        rw [hG] at hEval
                        cases b <;>
                          (injection hEval with hPair; injection hPair with _ hH; rw [← hH]; exact hL2)
                  all_goals cases hEval
      | load ptrExpr =>
          rw [ctfeEval_succ] at hEval; dsimp only [ctfeEvalStep] at hEval
          cases h1 : ctfeEval fuel H ptrExpr with
          | err _ => rw [h1] at hEval; cases hEval
          | ok r1 =>
              rcases r1 with ⟨vp, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have hL1 := ctfeEval_preserves_validLayout fuel H H1 L ptrExpr vp hLayout h1
              cases vp <;> dsimp only at hEval
              case ptr aid off =>
                cases hLook : Heap.lookup H1 aid with
                | none => rw [hLook] at hEval; cases hEval
                | some a =>
                    rw [hLook] at hEval; dsimp only at hEval
                    cases hRead : readSlotAt a.slots off with
                    | none => rw [hRead] at hEval; cases hEval
                    | some s =>
                        rw [hRead] at hEval; dsimp only at hEval
                        cases hs : s.val
                        case uninit =>
                          rw [hs] at hEval; cases hEval
                        all_goals
                          (rw [hs] at hEval; injection hEval with hPair; injection hPair with _ hH; rw [← hH]; exact hL1)
              all_goals cases hEval
      | store ptrExpr valExpr =>
          rw [ctfeEval_succ] at hEval; dsimp only [ctfeEvalStep] at hEval
          cases h1 : ctfeEval fuel H ptrExpr with
          | err _ => rw [h1] at hEval; cases hEval
          | ok r1 =>
              rcases r1 with ⟨vp, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have hL1 := ctfeEval_preserves_validLayout fuel H H1 L ptrExpr vp hLayout h1
              cases h2 : ctfeEval fuel H1 valExpr with
              | err _ => rw [h2] at hEval; cases hEval
              | ok r2 =>
                  rcases r2 with ⟨vv, H2⟩
                  rw [h2] at hEval; dsimp only at hEval
                  have hL2 := ctfeEval_preserves_validLayout fuel H1 H2 L valExpr vv hL1 h2
                  cases vp <;> dsimp only at hEval
                  case ptr aid off =>
                    cases hLook : Heap.lookup H2 aid with
                    | none => rw [hLook] at hEval; cases hEval
                    | some a =>
                        rw [hLook] at hEval; dsimp only at hEval
                        cases hMut : a.mutbl with
                        | immut =>
                            rw [hMut] at hEval; cases hEval
                        | mutWritable =>
                            rw [hMut] at hEval; dsimp only at hEval
                            cases hWr : writeSlotAt a.slots off vv with
                            | none => rw [hWr] at hEval; cases hEval
                            | some slots' =>
                                rw [hWr] at hEval; dsimp only at hEval
                                injection hEval with hPair
                                injection hPair with _ hH'
                                rw [← hH', ← hMut]
                                exact ValidLayout.update_slots hL2 hLook
                                  (writeSlotAt_length a.slots off vv slots' hWr)
                  all_goals cases hEval
      | allocLocal align cell initExpr =>
          rw [ctfeEval_succ] at hEval; dsimp only [ctfeEvalStep] at hEval
          cases h1 : ctfeEval fuel H initExpr with
          | err _ => rw [h1] at hEval; cases hEval
          | ok r1 =>
              rcases r1 with ⟨vInit, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have hL1 := ctfeEval_preserves_validLayout fuel H H1 L initExpr vInit hLayout h1
              cases hBad : (decide (align = 0) || decide (vInit = .uninit)) with
              | true => rw [hBad] at hEval; cases hEval
              | false =>
                  rw [hBad] at hEval
                  injection hEval with hPair; injection hPair with _ hH
                  rw [← hH]
                  exact ValidLayout.alloc_stack_fresh hL1
      | seq e1 e2 =>
          rw [ctfeEval_succ] at hEval; dsimp only [ctfeEvalStep] at hEval
          cases h1 : ctfeEval fuel H e1 with
          | err _ => rw [h1] at hEval; cases hEval
          | ok r1 =>
              rcases r1 with ⟨v1, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have hL1 := ctfeEval_preserves_validLayout fuel H H1 L e1 v1 hLayout h1
              exact ctfeEval_preserves_validLayout fuel H1 H' L e2 v hL1 hEval
      | letBind bound cont =>
          rw [ctfeEval_succ] at hEval; dsimp only [ctfeEvalStep] at hEval
          cases h1 : ctfeEval fuel H bound with
          | err _ => rw [h1] at hEval; cases hEval
          | ok r1 =>
              rcases r1 with ⟨vb, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have hL1 := ctfeEval_preserves_validLayout fuel H H1 L bound vb hLayout h1
              exact ctfeEval_preserves_validLayout fuel H1 H' L (cont vb) v hL1 hEval
      | iteNonZero cond thenBr elseBr =>
          rw [ctfeEval_succ] at hEval; dsimp only [ctfeEvalStep] at hEval
          cases h1 : ctfeEval fuel H cond with
          | err _ => rw [h1] at hEval; cases hEval
          | ok r1 =>
              rcases r1 with ⟨vc, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have hL1 := ctfeEval_preserves_validLayout fuel H H1 L cond vc hLayout h1
              cases vc with
              | scalar n =>
                  cases n with
                  | zero => exact ctfeEval_preserves_validLayout fuel H1 H' L elseBr v hL1 hEval
                  | succ _ => exact ctfeEval_preserves_validLayout fuel H1 H' L thenBr v hL1 hEval
              | ptr _ _ => cases hEval
              | zst => cases hEval
              | uninit => cases hEval
      | constEvalSelect _ arg ctArm _ =>
          rw [ctfeEval_succ] at hEval; dsimp only [ctfeEvalStep] at hEval
          cases h1 : ctfeEval fuel H arg with
          | err _ => rw [h1] at hEval; cases hEval
          | ok r1 =>
              rcases r1 with ⟨vArg, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have hL1 := ctfeEval_preserves_validLayout fuel H H1 L arg vArg hLayout h1
              exact ctfeEval_preserves_validLayout fuel H1 H' L (ctArm vArg) v hL1 hEval
      | isValStaticallyKnown _ arg kArm =>
          rw [ctfeEval_succ] at hEval; dsimp only [ctfeEvalStep] at hEval
          cases h1 : ctfeEval fuel H arg with
          | err _ => rw [h1] at hEval; cases hEval
          | ok r1 =>
              rcases r1 with ⟨vArg, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have hL1 := ctfeEval_preserves_validLayout fuel H H1 L arg vArg hLayout h1
              exact ctfeEval_preserves_validLayout fuel H1 H' L (kArm false) v hL1 hEval
      | unevalConst body =>
          rw [ctfeEval_succ] at hEval; dsimp only [ctfeEvalStep] at hEval
          cases h1 : ctfeEval fuel H body with
          | err _ => rw [h1] at hEval; cases hEval
          | ok r1 =>
              rcases r1 with ⟨v1, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have hL1 := ctfeEval_preserves_validLayout fuel H H1 L body v1 hLayout h1
              cases hValid : checkInternValidFreeze H1 v1 with
              | false => rw [hValid] at hEval; cases hEval
              | true =>
                  rw [hValid] at hEval
                  injection hEval with hPair; injection hPair with _ hH
                  rw [← hH]
                  exact hL1

/-! ## 6. Relational Simulation Contracts & Contextual Helper Soundness -/

/-- Direct Relational Simulation Contract for `const_eval_select(arg, ctArm, rtArm)`:
    Whenever `ctArm vArg` succeeds in `ctfeEval` from a valid heap `H`, `rtArm vArg` produces
    the identical result under EVERY valid concrete allocator placement `L` and oracle `oracle`. -/
def CesRelationalContract (ctArm rtArm : Val → MirExpr) : Prop :=
  ∀ (fuel : Nat) (H H' : Heap) (L : ConcreteLayout) (oracle : Nat → Bool) (vArg vRes : Val),
    ValidLayout H L →
    ctfeEval fuel H (ctArm vArg) = .ok (vRes, H') →
    rtEval L oracle fuel H (rtArm vArg) = .ok (vRes, H')

/-- Oracle-Bit Invariance for `is_val_statically_known`:
    Across every valid concrete allocator placement `L` and optimizer/Miri bit `b ∈ {false, true}`,
    the runtime continuation produces the same result as `kArm false`. -/
def IvskOracleInvariant (kArm : Bool → MirExpr) : Prop :=
  ∀ (fuel : Nat) (H : Heap) (L : ConcreteLayout) (oracle : Nat → Bool) (b : Bool),
    ValidLayout H L →
    rtEval L oracle fuel H (kArm b) = rtEval L oracle fuel H (kArm false)

/-- Inductive well-formedness of intrinsic obligations throughout a `MirExpr`. -/
inductive WellFormedContracts : MirExpr → Prop where
  | lit (v : Val) : WellFormedContracts (.lit v)
  | panic : WellFormedContracts .panic
  | add (e1 e2 : MirExpr) :
      WellFormedContracts e1 → WellFormedContracts e2 → WellFormedContracts (.add e1 e2)
  | eqScalar (e1 e2 : MirExpr) :
      WellFormedContracts e1 → WellFormedContracts e2 → WellFormedContracts (.eqScalar e1 e2)
  | ptrOffset (b d : MirExpr) :
      WellFormedContracts b → WellFormedContracts d → WellFormedContracts (.ptrOffset b d)
  | ptrAddrMod (p : MirExpr) (m : Nat) :
      WellFormedContracts p → WellFormedContracts (.ptrAddrMod p m)
  | guaranteedPtrEq (p1 p2 : MirExpr) :
      WellFormedContracts p1 → WellFormedContracts p2 → WellFormedContracts (.guaranteedPtrEq p1 p2)
  | load (p : MirExpr) : WellFormedContracts p → WellFormedContracts (.load p)
  | store (p v : MirExpr) :
      WellFormedContracts p → WellFormedContracts v → WellFormedContracts (.store p v)
  | allocLocal (align : Nat) (cell : CellKind) (initExpr : MirExpr) :
      WellFormedContracts initExpr → WellFormedContracts (.allocLocal align cell initExpr)
  | seq (e1 e2 : MirExpr) :
      WellFormedContracts e1 → WellFormedContracts e2 → WellFormedContracts (.seq e1 e2)
  | letBind (bound : MirExpr) (cont : Val → MirExpr) :
      WellFormedContracts bound →
      (∀ v, WellFormedContracts (cont v)) →
      WellFormedContracts (.letBind bound cont)
  | iteNonZero (c t f : MirExpr) :
      WellFormedContracts c → WellFormedContracts t → WellFormedContracts f →
      WellFormedContracts (.iteNonZero c t f)
  | constEvalSelect (site : Nat) (arg : MirExpr) (ctArm rtArm : Val → MirExpr) :
      WellFormedContracts arg →
      (∀ v, WellFormedContracts (ctArm v)) →
      CesRelationalContract ctArm rtArm →
      WellFormedContracts (.constEvalSelect site arg ctArm rtArm)
  | isValStaticallyKnown (site : Nat) (arg : MirExpr) (kArm : Bool → MirExpr) :
      WellFormedContracts arg →
      WellFormedContracts (kArm false) →
      IvskOracleInvariant kArm →
      WellFormedContracts (.isValStaticallyKnown site arg kArm)
  | unevalConst (body : MirExpr) :
      WellFormedContracts body → WellFormedContracts (.unevalConst body)

/-- **Theorem 3 (Contextual Helper-Invariant Soundness for `const_eval_select`):**
    Models encapsulated helpers such as `core/src/str/validations.rs:136`, where `ctArm`
    returns sentinel `usize::MAX` while `rtArm` returns `ptr.align_offset(8)` (`vCt ≠ vRt`),
    yet both satisfy a relational helper postcondition `HelperInv L H1 vArg res` under which
    the enclosing continuation `callerCtx` is invariant! -/
theorem constEvalSelect_contextual_helper_sound
    {site : Nat} {arg : MirExpr} {ctArm rtArm callerCtx : Val → MirExpr}
    {HelperInv : ConcreteLayout → Heap → Val → Val → Prop}
    {fuel : Nat} {H H1 H_fin : Heap} {L : ConcreteLayout} {oracle : Nat → Bool}
    {vArg vCt vOut : Val}
    (hArgCt : ctfeEval fuel H arg = .ok (vArg, H1))
    (hArgRt : rtEval L oracle fuel H arg = .ok (vArg, H1))
    (hCtArm : ctfeEval fuel H1 (ctArm vArg) = .ok (vCt, H1))
    (hHelperCt : HelperInv L H1 vArg vCt)
    (hHelperRt :
      ∃ vRt, rtEval L oracle fuel H1 (rtArm vArg) = .ok (vRt, H1) ∧ HelperInv L H1 vArg vRt)
    (hCallerCtToRt :
      ctfeEval (fuel + 1) H1 (callerCtx vCt) = .ok (vOut, H_fin) →
      rtEval L oracle (fuel + 1) H1 (callerCtx vCt) = .ok (vOut, H_fin))
    (hCallerInv :
      ∀ r1 r2,
        HelperInv L H1 vArg r1 →
        HelperInv L H1 vArg r2 →
        rtEval L oracle (fuel + 1) H1 (callerCtx r1) =
        rtEval L oracle (fuel + 1) H1 (callerCtx r2))
    (hWholeCt :
      ctfeEval (fuel + 2) H
        (.letBind (.constEvalSelect site arg ctArm rtArm) callerCtx) = .ok (vOut, H_fin)) :
    rtEval L oracle (fuel + 2) H
      (.letBind (.constEvalSelect site arg ctArm rtArm) callerCtx) = .ok (vOut, H_fin) := by
  rcases hHelperRt with ⟨vRt, hRtArm, hInvRt⟩
  change
    (match ctfeEval (fuel + 1) H (.constEvalSelect site arg ctArm rtArm) with
      | EvalRes.err err => EvalRes.err err
      | EvalRes.ok (vb, H1') => ctfeEval (fuel + 1) H1' (callerCtx vb)) = .ok (vOut, H_fin) at hWholeCt
  have hCesCt :
      ctfeEval (fuel + 1) H (.constEvalSelect site arg ctArm rtArm) = .ok (vCt, H1) := by
    rw [ctfeEval_succ]; dsimp only [ctfeEvalStep]
    rw [hArgCt]
    exact hCtArm
  rw [hCesCt] at hWholeCt
  dsimp only at hWholeCt
  have hCesRt :
      rtEval L oracle (fuel + 1) H (.constEvalSelect site arg ctArm rtArm) = .ok (vRt, H1) := by
    rw [rtEval_succ]; dsimp only [rtEvalStep]
    rw [hArgRt]
    exact hRtArm
  change
    (match rtEval L oracle (fuel + 1) H (.constEvalSelect site arg ctArm rtArm) with
      | EvalRes.err err => EvalRes.err err
      | EvalRes.ok (vb, H1') => rtEval L oracle (fuel + 1) H1' (callerCtx vb)) = .ok (vOut, H_fin)
  rw [hCesRt]
  dsimp only
  rw [hCallerInv vRt vCt hInvRt hHelperCt]
  exact hCallerCtToRt hWholeCt

/-! ## 7. Master CTFE-to-Runtime Refinement & `Const::Unevaluated` Elimination Soundness -/

private theorem ok_ctfe_to_rt {x y : Val × Heap}
    (h : (@EvalRes.ok CtfeErr (Val × Heap) x) = .ok y) :
    (@EvalRes.ok RtErr (Val × Heap) x) = .ok y := by
  injection h with hEq
  exact congrArg EvalRes.ok hEq

/-- **Theorem 4 (Dual-Mode CTFE-to-Runtime Operational Refinement):**
    For any `MirExpr` whose `constEvalSelect` sites satisfy `CesRelationalContract` and
    whose `isValStaticallyKnown` sites satisfy `IvskOracleInvariant`, successful evaluation
    under `ctfeEval` implies identical successful evaluation under `rtEval` across EVERY
    admissible concrete allocator layout `L` and EVERY optimizer/Miri oracle `oracle`. -/
theorem ctfe_eval_refines_rt_eval :
    ∀ (fuel : Nat) (H H' : Heap) (L : ConcreteLayout) (oracle : Nat → Bool)
      (e : MirExpr) (v : Val),
      ValidLayout H L →
      WellFormedContracts e →
      ctfeEval fuel H e = .ok (v, H') →
      rtEval L oracle fuel H e = .ok (v, H')
  | 0, _, _, _, _, _, _, _, _, hEval => by cases hEval
  | fuel + 1, H, H', L, oracle, _, v, hLayout, hWf, hEval => by
      cases hWf with
      | lit v0 =>
          cases v0 <;> rw [ctfeEval_succ] at hEval; rw [rtEval_succ]; dsimp only [ctfeEvalStep, rtEvalStep] at hEval ⊢
          case uninit => cases hEval
          all_goals exact ok_ctfe_to_rt hEval
      | panic => cases hEval
      | add e1 e2 wf1 wf2 =>
          rw [ctfeEval_succ] at hEval; rw [rtEval_succ]; dsimp only [ctfeEvalStep, rtEvalStep] at hEval ⊢
          cases h1 : ctfeEval fuel H e1 with
          | err _ => rw [h1] at hEval; cases hEval
          | ok r1 =>
              rcases r1 with ⟨v1, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have ih1 := ctfe_eval_refines_rt_eval fuel H H1 L oracle e1 v1 hLayout wf1 h1
              have hL1 := ctfeEval_preserves_validLayout fuel H H1 L e1 v1 hLayout h1
              rw [ih1]; dsimp only
              cases h2 : ctfeEval fuel H1 e2 with
              | err _ => rw [h2] at hEval; cases hEval
              | ok r2 =>
                  rcases r2 with ⟨v2, H2⟩
                  rw [h2] at hEval; dsimp only at hEval
                  have ih2 := ctfe_eval_refines_rt_eval fuel H1 H2 L oracle e2 v2 hL1 wf2 h2
                  rw [ih2]; dsimp only
                  cases v1 <;> cases v2 <;> dsimp only at hEval ⊢
                  case scalar.scalar => exact ok_ctfe_to_rt hEval
                  all_goals cases hEval
      | eqScalar e1 e2 wf1 wf2 =>
          rw [ctfeEval_succ] at hEval; rw [rtEval_succ]; dsimp only [ctfeEvalStep, rtEvalStep] at hEval ⊢
          cases h1 : ctfeEval fuel H e1 with
          | err _ => rw [h1] at hEval; cases hEval
          | ok r1 =>
              rcases r1 with ⟨v1, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have ih1 := ctfe_eval_refines_rt_eval fuel H H1 L oracle e1 v1 hLayout wf1 h1
              have hL1 := ctfeEval_preserves_validLayout fuel H H1 L e1 v1 hLayout h1
              rw [ih1]; dsimp only
              cases h2 : ctfeEval fuel H1 e2 with
              | err _ => rw [h2] at hEval; cases hEval
              | ok r2 =>
                  rcases r2 with ⟨v2, H2⟩
                  rw [h2] at hEval; dsimp only at hEval
                  have ih2 := ctfe_eval_refines_rt_eval fuel H1 H2 L oracle e2 v2 hL1 wf2 h2
                  rw [ih2]; dsimp only
                  cases v1 <;> cases v2 <;> dsimp only at hEval ⊢
                  case scalar.scalar => exact ok_ctfe_to_rt hEval
                  all_goals cases hEval
      | ptrOffset base delta wfB wfD =>
          rw [ctfeEval_succ] at hEval; rw [rtEval_succ]; dsimp only [ctfeEvalStep, rtEvalStep] at hEval ⊢
          cases h1 : ctfeEval fuel H base with
          | err _ => rw [h1] at hEval; cases hEval
          | ok r1 =>
              rcases r1 with ⟨vb, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have ih1 := ctfe_eval_refines_rt_eval fuel H H1 L oracle base vb hLayout wfB h1
              have hL1 := ctfeEval_preserves_validLayout fuel H H1 L base vb hLayout h1
              rw [ih1]; dsimp only
              cases h2 : ctfeEval fuel H1 delta with
              | err _ => rw [h2] at hEval; cases hEval
              | ok r2 =>
                  rcases r2 with ⟨vd, H2⟩
                  rw [h2] at hEval; dsimp only at hEval
                  have ih2 := ctfe_eval_refines_rt_eval fuel H1 H2 L oracle delta vd hL1 wfD h2
                  rw [ih2]; dsimp only
                  cases vb <;> cases vd <;> dsimp only at hEval ⊢
                  case ptr.scalar aid off d =>
                    cases hLook : Heap.lookup H2 aid with
                    | none => rw [hLook] at hEval; cases hEval
                    | some a =>
                        rw [hLook] at hEval; dsimp only at hEval ⊢
                        by_cases hIn : off + d ≤ a.size
                        · simp only [hIn, ite_true] at hEval ⊢; exact ok_ctfe_to_rt hEval
                        · simp only [hIn, ite_false] at hEval; cases hEval
                  all_goals cases hEval
      | ptrAddrMod _ _ _ => cases hEval
      | guaranteedPtrEq p1 p2 wf1 wf2 =>
          rw [ctfeEval_succ] at hEval; rw [rtEval_succ]; dsimp only [ctfeEvalStep, rtEvalStep] at hEval ⊢
          cases h1 : ctfeEval fuel H p1 with
          | err _ => rw [h1] at hEval; cases hEval
          | ok r1 =>
              rcases r1 with ⟨v1, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have ih1 := ctfe_eval_refines_rt_eval fuel H H1 L oracle p1 v1 hLayout wf1 h1
              have hL1 := ctfeEval_preserves_validLayout fuel H H1 L p1 v1 hLayout h1
              rw [ih1]; dsimp only
              cases h2 : ctfeEval fuel H1 p2 with
              | err _ => rw [h2] at hEval; cases hEval
              | ok r2 =>
                  rcases r2 with ⟨v2, H2⟩
                  rw [h2] at hEval; dsimp only at hEval
                  have ih2 := ctfe_eval_refines_rt_eval fuel H1 H2 L oracle p2 v2 hL1 wf2 h2
                  have hL2 := ctfeEval_preserves_validLayout fuel H1 H2 L p2 v2 hL1 h2
                  rw [ih2]; dsimp only
                  cases v1 <;> cases v2 <;> dsimp only at hEval ⊢
                  case ptr.ptr a1 o1 a2 o2 =>
                    cases hG : ctfeGuaranteedPtrEq H2 a1 o1 a2 o2 with
                    | none => rw [hG] at hEval; cases hEval
                    | some b =>
                        rw [hG] at hEval
                        have hSound := ctfe_guaranteed_ptr_eq_sound hL2 hG
                        rw [hSound]
                        cases b <;> exact ok_ctfe_to_rt hEval
                  all_goals cases hEval
      | load ptrExpr wfP =>
          rw [ctfeEval_succ] at hEval; rw [rtEval_succ]; dsimp only [ctfeEvalStep, rtEvalStep] at hEval ⊢
          cases h1 : ctfeEval fuel H ptrExpr with
          | err _ => rw [h1] at hEval; cases hEval
          | ok r1 =>
              rcases r1 with ⟨vp, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have ih1 := ctfe_eval_refines_rt_eval fuel H H1 L oracle ptrExpr vp hLayout wfP h1
              rw [ih1]; dsimp only
              cases vp <;> dsimp only at hEval ⊢
              case ptr aid off =>
                cases hLook : Heap.lookup H1 aid with
                | none => rw [hLook] at hEval; cases hEval
                | some a =>
                    rw [hLook] at hEval; dsimp only at hEval ⊢
                    cases hRead : readSlotAt a.slots off with
                    | none => rw [hRead] at hEval; cases hEval
                    | some s =>
                        rw [hRead] at hEval; dsimp only at hEval ⊢
                        cases hs : s.val
                        case uninit =>
                          rw [hs] at hEval; cases hEval
                        all_goals
                          (rw [hs] at hEval; dsimp only at hEval ⊢; exact ok_ctfe_to_rt hEval)
              all_goals cases hEval
      | store ptrExpr valExpr wfP wfV =>
          rw [ctfeEval_succ] at hEval; rw [rtEval_succ]; dsimp only [ctfeEvalStep, rtEvalStep] at hEval ⊢
          cases h1 : ctfeEval fuel H ptrExpr with
          | err _ => rw [h1] at hEval; cases hEval
          | ok r1 =>
              rcases r1 with ⟨vp, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have ih1 := ctfe_eval_refines_rt_eval fuel H H1 L oracle ptrExpr vp hLayout wfP h1
              have hL1 := ctfeEval_preserves_validLayout fuel H H1 L ptrExpr vp hLayout h1
              rw [ih1]; dsimp only
              cases h2 : ctfeEval fuel H1 valExpr with
              | err _ => rw [h2] at hEval; cases hEval
              | ok r2 =>
                  rcases r2 with ⟨vv, H2⟩
                  rw [h2] at hEval; dsimp only at hEval
                  have ih2 := ctfe_eval_refines_rt_eval fuel H1 H2 L oracle valExpr vv hL1 wfV h2
                  rw [ih2]; dsimp only
                  cases vp <;> dsimp only at hEval ⊢
                  case ptr aid off =>
                    cases hLook : Heap.lookup H2 aid with
                    | none => rw [hLook] at hEval; cases hEval
                    | some a =>
                        rw [hLook] at hEval; dsimp only at hEval ⊢
                        cases hMut : a.mutbl with
                        | immut =>
                            rw [hMut] at hEval; cases hEval
                        | mutWritable =>
                            rw [hMut] at hEval; dsimp only at hEval ⊢
                            cases hWr : writeSlotAt a.slots off vv with
                            | none => rw [hWr] at hEval; cases hEval
                            | some slots' =>
                                rw [hWr] at hEval; dsimp only at hEval ⊢
                                exact ok_ctfe_to_rt hEval
                  all_goals cases hEval
      | allocLocal align cell initExpr wfInit =>
          rw [ctfeEval_succ] at hEval; rw [rtEval_succ]; dsimp only [ctfeEvalStep, rtEvalStep] at hEval ⊢
          cases h1 : ctfeEval fuel H initExpr with
          | err _ => rw [h1] at hEval; cases hEval
          | ok r1 =>
              rcases r1 with ⟨vInit, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have ih1 := ctfe_eval_refines_rt_eval fuel H H1 L oracle initExpr vInit hLayout wfInit h1
              rw [ih1]; dsimp only
              cases hBad : (decide (align = 0) || decide (vInit = .uninit)) with
              | true => rw [hBad] at hEval; cases hEval
              | false =>
                  rw [hBad] at hEval
                  exact ok_ctfe_to_rt hEval
      | seq e1 e2 wf1 wf2 =>
          rw [ctfeEval_succ] at hEval; rw [rtEval_succ]; dsimp only [ctfeEvalStep, rtEvalStep] at hEval ⊢
          cases h1 : ctfeEval fuel H e1 with
          | err _ => rw [h1] at hEval; cases hEval
          | ok r1 =>
              rcases r1 with ⟨v1, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have ih1 := ctfe_eval_refines_rt_eval fuel H H1 L oracle e1 v1 hLayout wf1 h1
              have hL1 := ctfeEval_preserves_validLayout fuel H H1 L e1 v1 hLayout h1
              rw [ih1]; dsimp only
              exact ctfe_eval_refines_rt_eval fuel H1 H' L oracle e2 v hL1 wf2 hEval
      | letBind bound cont wfB wfCont =>
          rw [ctfeEval_succ] at hEval; rw [rtEval_succ]; dsimp only [ctfeEvalStep, rtEvalStep] at hEval ⊢
          cases h1 : ctfeEval fuel H bound with
          | err _ => rw [h1] at hEval; cases hEval
          | ok r1 =>
              rcases r1 with ⟨vb, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have ih1 := ctfe_eval_refines_rt_eval fuel H H1 L oracle bound vb hLayout wfB h1
              have hL1 := ctfeEval_preserves_validLayout fuel H H1 L bound vb hLayout h1
              rw [ih1]; dsimp only
              exact ctfe_eval_refines_rt_eval fuel H1 H' L oracle (cont vb) v hL1 (wfCont vb) hEval
      | iteNonZero cond thenBr elseBr wfC wfT wfF =>
          rw [ctfeEval_succ] at hEval; rw [rtEval_succ]; dsimp only [ctfeEvalStep, rtEvalStep] at hEval ⊢
          cases h1 : ctfeEval fuel H cond with
          | err _ => rw [h1] at hEval; cases hEval
          | ok r1 =>
              rcases r1 with ⟨vc, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have ih1 := ctfe_eval_refines_rt_eval fuel H H1 L oracle cond vc hLayout wfC h1
              have hL1 := ctfeEval_preserves_validLayout fuel H H1 L cond vc hLayout h1
              rw [ih1]; dsimp only
              cases vc with
              | scalar n =>
                  cases n with
                  | zero =>
                      exact ctfe_eval_refines_rt_eval fuel H1 H' L oracle elseBr v hL1 wfF hEval
                  | succ _ =>
                      exact ctfe_eval_refines_rt_eval fuel H1 H' L oracle thenBr v hL1 wfT hEval
              | ptr _ _ => cases hEval
              | zst => cases hEval
              | uninit => cases hEval
      | constEvalSelect site arg ctArm rtArm wfArg _ hCes =>
          rw [ctfeEval_succ] at hEval; rw [rtEval_succ]; dsimp only [ctfeEvalStep, rtEvalStep] at hEval ⊢
          cases h1 : ctfeEval fuel H arg with
          | err _ => rw [h1] at hEval; cases hEval
          | ok r1 =>
              rcases r1 with ⟨vArg, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have ihArg := ctfe_eval_refines_rt_eval fuel H H1 L oracle arg vArg hLayout wfArg h1
              have hL1 := ctfeEval_preserves_validLayout fuel H H1 L arg vArg hLayout h1
              rw [ihArg]; dsimp only
              exact hCes fuel H1 H' L oracle vArg v hL1 hEval
      | isValStaticallyKnown site arg kArm wfArg wfKFalse hIvsk =>
          rw [ctfeEval_succ] at hEval; rw [rtEval_succ]; dsimp only [ctfeEvalStep, rtEvalStep] at hEval ⊢
          cases h1 : ctfeEval fuel H arg with
          | err _ => rw [h1] at hEval; cases hEval
          | ok r1 =>
              rcases r1 with ⟨vArg, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              have ihArg := ctfe_eval_refines_rt_eval fuel H H1 L oracle arg vArg hLayout wfArg h1
              have hL1 := ctfeEval_preserves_validLayout fuel H H1 L arg vArg hLayout h1
              have ihFalse :=
                ctfe_eval_refines_rt_eval fuel H1 H' L oracle (kArm false) v hL1 wfKFalse hEval
              rw [ihArg]; dsimp only
              rw [hIvsk fuel H1 L oracle (oracle site) hL1]
              exact ihFalse
      | unevalConst body wfBody =>
          rw [ctfeEval_succ] at hEval; rw [rtEval_succ]; dsimp only [ctfeEvalStep, rtEvalStep] at hEval ⊢
          cases h1 : ctfeEval fuel H body with
          | err _ => rw [h1] at hEval; cases hEval
          | ok r1 =>
              rcases r1 with ⟨v1, H1⟩
              rw [h1] at hEval; dsimp only at hEval
              cases hValid : checkInternValidFreeze H1 v1 with
              | false => rw [hValid] at hEval; cases hEval
              | true =>
                  rw [hValid] at hEval
                  injection hEval with hPair
                  injection hPair with hv hH
                  rw [← hv, ← hH]
                  exact ctfe_eval_refines_rt_eval fuel H H1 L oracle body v1 hLayout wfBody h1

/-- Constant-folding / post-monomorphization `Const::Unevaluated` substitution pass on `MirExpr`:
    when `ctfeEval constFuel H e` succeeds without mutating pre-existing heap `H` and passes
    `checkInternValidFreeze H v`, replaces `e` with `.lit v`. -/
def substConstIfValid (constFuel : Nat) (H : Heap) (e : MirExpr) : MirExpr :=
  match ctfeEval constFuel H e with
  | .ok (v, H1) =>
      if checkInternValidFreeze H1 v && decide (H1 = H) then .lit v else e
  | .err _ => e

private theorem lit_not_uninit_rtEval
    {L : ConcreteLayout} {oracle : Nat → Bool} {rtFuel : Nat} {H : Heap} {v : Val}
    (hValid : InternValidFreeze H v) :
    rtEval L oracle (rtFuel + 1) H (.lit v) = .ok (v, H) := by
  cases v with
  | scalar _ => rfl
  | ptr _ _ => rfl
  | zst => rfl
  | uninit =>
      unfold InternValidFreeze checkInternValidFreeze at hValid
      cases hValid

/-- **Theorem 5 (Master CTFE-to-Runtime Substitution & `Const::Unevaluated` Elimination Soundness):**
    If `ctfeEval constFuel H e = .ok (v, H)`, `InternValidFreeze H v` holds (no uninitialized
    scalar, no dangling borrow, and no non-ZST `UnsafeCell` behind a shared `.rodata` pointer),
    and `WellFormedContracts e` holds (`const_eval_select` Relational Simulation +
    `is_val_statically_known` Oracle-Bit Invariance), then across EVERY valid concrete layout `L`
    and EVERY optimizer/Miri oracle `oracle`:
    1. Substituting `.lit v` for `e` evaluates to `.ok (v, H)` in 1 step;
    2. Evaluating the un-substituted `e` at runtime ALSO evaluates to `.ok (v, H)` (exact
       ConstProp / MIR GVN / `Const::Unevaluated` confluence across `-O0` and `-O3`); and
    3. Any shared reference `.ptr aid off` inside `v` points to an initialized, read-only
       allocation with zero non-ZST `UnsafeCell` bytes. -/
theorem ctfe_to_runtime_substitution_sound
    {constFuel rtFuel : Nat} {H : Heap} {L : ConcreteLayout} {oracle : Nat → Bool}
    {e : MirExpr} {v : Val}
    (hLayout : ValidLayout H L)
    (hWf : WellFormedContracts e)
    (hCtfe : ctfeEval constFuel H e = .ok (v, H))
    (hIntern : InternValidFreeze H v) :
    substConstIfValid constFuel H e = .lit v ∧
    rtEval L oracle (rtFuel + 1) H (substConstIfValid constFuel H e) = .ok (v, H) ∧
    rtEval L oracle constFuel H e = .ok (v, H) ∧
    (∀ aid off, v = .ptr aid off →
      ∃ a, Heap.lookup H aid = some a ∧
           a.mutbl = .immut ∧
           allSlotsInit a.slots = true ∧
           (0 < a.size → allSlotsFrozen a.slots = true)) := by
  have hSub : substConstIfValid constFuel H e = .lit v := by
    unfold substConstIfValid
    rw [hCtfe]; dsimp only
    unfold InternValidFreeze at hIntern
    simp [hIntern]
  refine ⟨hSub, ?_, ?_, ?_⟩
  · rw [hSub]
    exact lit_not_uninit_rtEval hIntern
  · exact ctfe_eval_refines_rt_eval constFuel H H L oracle e v hLayout hWf hCtfe
  · intro aid off hv
    subst hv
    unfold InternValidFreeze at hIntern
    dsimp only [checkInternValidFreeze] at hIntern
    cases hLook : Heap.lookup H aid with
    | none => rw [hLook] at hIntern; cases hIntern
    | some a =>
        rw [hLook] at hIntern; dsimp only at hIntern
        simp only [Bool.and_eq_true, Bool.or_eq_true] at hIntern
        rcases hIntern with ⟨⟨⟨hMut, _⟩, hInit⟩, hFreezeOrZst⟩
        refine ⟨a, rfl, of_decide_eq_true hMut, hInit, ?_⟩
        intro hPos
        cases hFreezeOrZst with
        | inl hZero =>
            have hZero' : a.size = 0 := of_decide_eq_true hZero
            rw [hZero'] at hPos
            cases hPos
        | inr hFrozen => exact hFrozen

/-! ## 8. Three Kernel-Checked Sharpness Counterexamples (`CE1`, `CE2`, `CE3`) -/

def witnessHeap : Heap :=
  [(1, {
    kind := .staticItem
    mutbl := .immut
    align := 8
    slots := [{ val := .scalar 42, cell := .frozen }]
  })]

def witnessLayout : ConcreteLayout :=
  { baseAddr := fun aid => (aid + 1) * 8 }

theorem witnessHeap_validLayout : ValidLayout witnessHeap witnessLayout := by
  refine ⟨?_, ?_, ?_⟩
  · intro aid
    exact Nat.mul_pos (Nat.succ_pos aid) (Nat.zero_lt_succ 7)
  · intro aid a hLook _
    by_cases h1 : 1 = aid
    · simp [witnessHeap, Heap.lookup, h1] at hLook
      rw [← hLook]
      exact Nat.mul_mod_left (aid + 1) 8
    · simp [witnessHeap, Heap.lookup, h1] at hLook
  · intro aid1 _ aid2 _ hLook1 hLook2 hNe _ _
    by_cases h1 : 1 = aid1
    · by_cases h2 : 1 = aid2
      · exfalso; exact hNe (h1.symm.trans h2)
      · simp [witnessHeap, Heap.lookup, h2] at hLook2
    · simp [witnessHeap, Heap.lookup, h1] at hLook1

/-- **Counterexample CE1 (Unsound `const_eval_select` Alignment Divergence):**
    `ctArm` returns `0`, whereas `rtArm` inspects concrete pointer alignment mod 8
    (`(ptr.addr() % 8 == 0) ? 1 : 0`).
    - Under CTFE / `-O3` ConstProp (`substConstIfValid`), the expression folds to `.scalar 0`;
    - Under `-O0` un-folded `rtEval` on the valid 8-byte-aligned `witnessLayout`, it evaluates
      to `.scalar 1`;
    - Hence `0 ≠ 1`, violating `-O0` vs. `-O3` ConstProp/GVN confluence when `CesRelationalContract`
      is omitted! -/
def ce1DivergentSelect : MirExpr :=
  .constEvalSelect 0 (.lit (.ptr 1 0))
    (fun _ => .lit (.scalar 0))
    (fun p => .eqScalar (.ptrAddrMod (.lit p) 8) (.lit (.scalar 0)))

theorem ce1_unsound_const_eval_select_breaks_gvn_confluence :
    ValidLayout witnessHeap witnessLayout ∧
    InternValidFreeze witnessHeap (.scalar 0) ∧
    ctfeEval 4 witnessHeap ce1DivergentSelect = .ok (.scalar 0, witnessHeap) ∧
    rtEval witnessLayout (fun _ => false) 4 witnessHeap
      (substConstIfValid 4 witnessHeap ce1DivergentSelect) = .ok (.scalar 0, witnessHeap) ∧
    rtEval witnessLayout (fun _ => false) 4 witnessHeap ce1DivergentSelect =
      .ok (.scalar 1, witnessHeap) ∧
    rtEval witnessLayout (fun _ => false) 4 witnessHeap
      (substConstIfValid 4 witnessHeap ce1DivergentSelect) ≠
      rtEval witnessLayout (fun _ => false) 4 witnessHeap ce1DivergentSelect := by
  refine ⟨witnessHeap_validLayout, rfl, rfl, rfl, rfl, ?_⟩
  decide

/-- **Counterexample CE2 (`UnsafeCell` Immutable `.rodata` Interning UB & Shared Aliasing):**
    Models `const CELL_CONST: Cell<u64> = Cell::new(100)`:
    1. **Read-Only `.rodata` Fault:** If interned directly into an immutable static/const place
       (`aid = 10`, `mutbl = .immut`, rejected by `checkInternValidFreeze = false`!), a runtime
       `Cell::set(999)` store faults with `.err .writeToImmut` (matching Miri's read-only UB);
    2. **Shared Writable Aliasing Bug:** If placed in a single shared writable place (`aid = 11`,
       `mutbl = .mutWritable`) without per-mention copying, `CELL_CONST.set(999)` on the first
       use mutates subsequent reads of `CELL_CONST` from `100` to `999`;
    3. **Sound Per-Mention Copy (`allocLocal .unsafeCell`):** Materializing a fresh local copy
       at each mention allows `a.set(999)` to succeed while `b.get()` still reads `100`. -/
def ce2BogusImmutCellHeap : Heap :=
  [(10, {
    kind := .constMemory
    mutbl := .immut
    align := 8
    slots := [{ val := .scalar 100, cell := .unsafeCell }]
  })]

def ce2SharedMutCellHeap : Heap :=
  [(11, {
    kind := .constMemory
    mutbl := .mutWritable
    align := 8
    slots := [{ val := .scalar 100, cell := .unsafeCell }]
  })]

def ce2PerMentionCopyProg : MirExpr :=
  .letBind (.allocLocal 8 .unsafeCell (.lit (.scalar 100))) (fun ptrA =>
    .seq (.store (.lit ptrA) (.lit (.scalar 999)))
      (.letBind (.allocLocal 8 .unsafeCell (.lit (.scalar 100))) (fun ptrB =>
        .load (.lit ptrB))))

theorem ce2_unsafecell_rodata_interning_ub_and_aliasing :
    checkInternValidFreeze ce2BogusImmutCellHeap (.ptr 10 0) = false ∧
    rtEval witnessLayout (fun _ => false) 3 ce2BogusImmutCellHeap
      (.store (.lit (.ptr 10 0)) (.lit (.scalar 999))) = .err .writeToImmut ∧
    (∃ H_aliased,
      rtEval witnessLayout (fun _ => false) 4 ce2SharedMutCellHeap
        (.seq (.store (.lit (.ptr 11 0)) (.lit (.scalar 999))) (.load (.lit (.ptr 11 0)))) =
        .ok (.scalar 999, H_aliased)) ∧
    (∃ H_fresh,
      rtEval witnessLayout (fun _ => false) 6 [] ce2PerMentionCopyProg =
        .ok (.scalar 100, H_fresh)) := by
  refine ⟨rfl, rfl, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- **Counterexample CE3 (Non-Invariant `is_val_statically_known` Branch):**
    Branching observationally on `is_val_statically_known(42)` (`true -> 100`, `false -> 200`):
    - At `-O0` (`oracle := fun _ => false`), evaluates to `.scalar 200`;
    - At `-O3` after LLVM inlining folds `@llvm.is.constant` (`oracle := fun _ => true`),
      evaluates to `.scalar 100`;
    - Proves `rtEval (-O0) ≠ rtEval (-O3)`, breaking optimization refinement when
      `IvskOracleInvariant` is violated! -/
def ce3NonInvariantIvsk : MirExpr :=
  .isValStaticallyKnown 0 (.lit (.scalar 42))
    (fun b => if b then .lit (.scalar 100) else .lit (.scalar 200))

theorem ce3_non_invariant_ivsk_breaks_opt_refinement :
    ValidLayout witnessHeap witnessLayout ∧
    ctfeEval 3 witnessHeap ce3NonInvariantIvsk = .ok (.scalar 200, witnessHeap) ∧
    rtEval witnessLayout (fun _ => false) 3 witnessHeap ce3NonInvariantIvsk =
      .ok (.scalar 200, witnessHeap) ∧
    rtEval witnessLayout (fun _ => true) 3 witnessHeap ce3NonInvariantIvsk =
      .ok (.scalar 100, witnessHeap) ∧
    rtEval witnessLayout (fun _ => false) 3 witnessHeap ce3NonInvariantIvsk ≠
      rtEval witnessLayout (fun _ => true) 3 witnessHeap ce3NonInvariantIvsk := by
  refine ⟨witnessHeap_validLayout, rfl, rfl, rfl, ?_⟩
  decide

end CtfeAndConstEvalSelectSoundness
