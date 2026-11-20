import ToyAlias.CalleeInvariant

/-!
# Reference-based optimizations across unknown code (toy stack model)

Each optimization is a pair of concrete program shapes: a source body and a
transformed body. Every body begins with the *function-entry reborrow* of its
reference argument: `x := retag a p prot`, where `a` is the tag of the argument as
passed by the caller, `p` the permission of the reference type, and `prot` whether
the entry reborrow is protected (Stacked Borrows' `retag[fn]`). The fresh tag of `x`
is always `m.next`. The unknown code receives the tags `ts` (any tags; they may
include parents of `x`, unrelated tags, or `m.next` itself, which means passing `x`).

Each main result has the form `Refines (tgt …) (src …)` for **all** parameters
satisfying the stated hypotheses, in particular for all unknown code `c` and all
initial states `m`. Each hypothesis has a counterexample stating that the other
hypotheses hold, the hypothesis fails, and both `Refines` and `VisiblyRefines` fail
(so the difference is in UB, halting, observations, or the stored value, not merely in
borrow-tracking state).

Only one location is tracked. Under the protected results for `&mut`, a callee that
accesses that location before halting has UB
(`runCallee_ub_of_touches_of_protected_unique_head`); the results therefore concern
callees that act observably (`emit`), create `sharedRW` reborrows, halt, or (without a
protector) access the location and then halt.
-/

namespace Toy.Alias

/-! ## Program shapes -/

/-- Read elimination, source: `x := retag a p prot; v₁ := *x; f(ts); v₂ := *x;
return (v₁, v₂)`. -/
def readElimSrc (p : Perm) (prot : Bool) (a : Tag) (ts : List Tag) (c : List COp)
    (m : Mem) : Outcome :=
  liftO (retag a p prot m) fun (x, m) =>
  liftO (read x m) fun (v₁, m) =>
  (runCallee ts c m).bind fun obs m =>
  liftO (read x m) fun (v₂, m) =>
  .done (obs ++ [v₁, v₂]) m

/-- Read elimination, target: the read after the call is replaced by the value read
before the call: `x := retag a p prot; v₁ := *x; f(ts); return (v₁, v₁)`. -/
def readElimTgt (p : Perm) (prot : Bool) (a : Tag) (ts : List Tag) (c : List COp)
    (m : Mem) : Outcome :=
  liftO (retag a p prot m) fun (x, m) =>
  liftO (read x m) fun (v₁, m) =>
  (runCallee ts c m).bind fun obs m =>
  .done (obs ++ [v₁, v₁]) m

/-- Read deferral (moving a read down across the call), source:
`x := retag a p prot; v := *x; f(ts); return v`. -/
def readDeferSrc (p : Perm) (prot : Bool) (a : Tag) (ts : List Tag) (c : List COp)
    (m : Mem) : Outcome :=
  liftO (retag a p prot m) fun (x, m) =>
  liftO (read x m) fun (v, m) =>
  (runCallee ts c m).bind fun obs m =>
  .done (obs ++ [v]) m

/-- Read deferral, target: `x := retag a p prot; f(ts); v := *x; return v`. -/
def readDeferTgt (p : Perm) (prot : Bool) (a : Tag) (ts : List Tag) (c : List COp)
    (m : Mem) : Outcome :=
  liftO (retag a p prot m) fun (x, m) =>
  (runCallee ts c m).bind fun obs m =>
  liftO (read x m) fun (v, m) =>
  .done (obs ++ [v]) m

/-- Dead-store elimination across a call, source:
`x := retag a p prot; *x = v₁; f(ts); *x = v₂; return`. -/
def dseSrc (p : Perm) (prot : Bool) (a : Tag) (ts : List Tag) (c : List COp)
    (v₁ v₂ : Nat) (m : Mem) : Outcome :=
  liftO (retag a p prot m) fun (x, m) =>
  liftO (write x v₁ m) fun m =>
  (runCallee ts c m).bind fun obs m =>
  liftO (write x v₂ m) fun m =>
  .done obs m

/-- Dead-store elimination, target: the first store is removed:
`x := retag a p prot; f(ts); *x = v₂; return`. -/
def dseTgt (p : Perm) (prot : Bool) (a : Tag) (ts : List Tag) (c : List COp)
    (v₂ : Nat) (m : Mem) : Outcome :=
  liftO (retag a p prot m) fun (x, m) =>
  (runCallee ts c m).bind fun obs m =>
  liftO (write x v₂ m) fun m =>
  .done obs m

/-- Store elimination *without* a later overwrite, source:
`x := retag a p prot; *x = v₁; f(ts); return`. -/
def storeElimSrc (p : Perm) (prot : Bool) (a : Tag) (ts : List Tag) (c : List COp)
    (v₁ : Nat) (m : Mem) : Outcome :=
  liftO (retag a p prot m) fun (x, m) =>
  liftO (write x v₁ m) fun m =>
  (runCallee ts c m).bind fun obs m =>
  .done obs m

/-- Store elimination without a later overwrite, target:
`x := retag a p prot; f(ts); return`. -/
def storeElimTgt (p : Perm) (prot : Bool) (a : Tag) (ts : List Tag) (c : List COp)
    (m : Mem) : Outcome :=
  liftO (retag a p prot m) fun (_, m) =>
  (runCallee ts c m).bind fun obs m =>
  .done obs m

/-! ### Examples for the program shapes -/

/-- Positive example: with a callee that does nothing, read elimination returns the same
outcome on both sides. -/
theorem readElim_shapes_example_pos :
    readElimSrc .unique true 0 [] [] initMem = readElimTgt .unique true 0 [] [] initMem := by
  decide

/-- Negative example: when the callee writes through `x` itself (tag `1`), the source
and target return different values. -/
theorem readElim_shapes_example_neg :
    readElimSrc .unique false 0 [1] [.write 0 9] initMem ≠
      readElimTgt .unique false 0 [1] [.write 0 9] initMem := by decide

/-- Positive example: the dead-store shapes agree when the callee does nothing. -/
theorem dse_shapes_example_pos :
    dseSrc .unique true 0 [] [] 5 7 initMem = dseTgt .unique true 0 [] [] 7 initMem := by decide

/-- Negative example: the read-deferral target is UB when the callee read through the
parent invalidated the unprotected `x`. -/
theorem readDefer_shapes_example_neg :
    readDeferTgt .unique false 0 [0] [.read 0] initMem = .ub := by decide

/-- Example for the no-overwrite store shapes: they differ in the final stored value. -/
theorem storeElim_shapes_example :
    storeElimSrc .unique true 0 [] [] 5 initMem ≠ storeElimTgt .unique true 0 [] [] initMem := by
  decide

/-! ## Concrete states used by counterexamples -/

/-- A state violating `NextFresh`: an old `unique` item already carries the tag `1`
that the next reborrow will issue. It violates `TagsBelowNext`, so no sequence of
operations reaches it from `initMem` (`not_tagsBelowNext_memDupNext`). -/
def memDupNext : Mem := ⟨0, [⟨.unique, 0, false⟩, ⟨.unique, 1, false⟩], 1⟩

/-- `memDupNext` violates `TagsBelowNext`, which `initMem` satisfies and every operation
preserves; hence it is unreachable from `initMem`. -/
theorem not_tagsBelowNext_memDupNext : ¬ TagsBelowNext memDupNext := by decide

/-- A state where a `sharedRW` sibling (tag `1`, e.g. a raw pointer) sits above the root
`unique` item (tag `0`). It satisfies `NextFresh`. -/
def memSibling : Mem := ⟨0, [⟨.sharedRW, 1, false⟩, ⟨.unique, 0, false⟩], 2⟩

/-- `memSibling` satisfies `NextFresh`. -/
theorem nextFresh_memSibling : NextFresh memSibling := by decide

/-- `memSibling` is reached from `initMem` by one unprotected `sharedRW` reborrow of the
root. -/
theorem memSibling_reachable : retag 0 .sharedRW false initMem = some (1, memSibling) := by
  decide

/-! ## Read elimination through an unpassed mutable reference -/

/-- Proof-internal generalization of the next theorem to every `p ≠ sharedRW`. -/
private theorem readElim_refines_of_not_sharedRW_aux
    (p : Perm) (prot : Bool) (a : Tag) (ts : List Tag) (c : List COp) (m : Mem)
    (hfresh : NextFresh m ∨ prot = true) (hp : p ≠ .sharedRW) (hts : m.next ∉ ts) :
    Refines (readElimTgt p prot a ts c m) (readElimSrc p prot a ts c m) := by
  intro hne
  unfold readElimTgt
  unfold readElimSrc at hne ⊢
  cases hr : retag a p prot m with
  | none => simp [hr, liftO] at hne
  | some xm =>
    rcases xm with ⟨x, m₁⟩
    simp only [hr, liftO] at hne ⊢
    have hm1 : x = m.next ∧ m₁.val = m.val ∧ m₁.next = m.next + 1 ∧
        ∃ s₁, m₁.stack = ⟨p, m.next, prot⟩ :: s₁ ∧ (NextFresh m → ∀ i ∈ s₁, i.tag ≠ m.next) := by
      unfold retag at hr
      cases p with
      | sharedRW => exact absurd rfl hp
      | unique =>
        cases ha : accessStack .write a m.stack with
        | none => simp [ha] at hr
        | some s₁ =>
          simp only [ha, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          exact ⟨rfl, rfl, rfl, s₁, rfl, fun hfr => accessStack_sublist_prop hfr ha⟩
      | sharedRO =>
        cases ha : accessStack .read a m.stack with
        | none => simp [ha] at hr
        | some s₁ =>
          simp only [ha, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          exact ⟨rfl, rfl, rfl, s₁, rfl, fun hfr => accessStack_sublist_prop hfr ha⟩
    obtain ⟨rfl, hval1, hnxt1, s₁, hst1, hfr1⟩ := hm1
    have hrd1 : Toy.Alias.read m.next m₁ = some (m.val, m₁) := by
      unfold Toy.Alias.read accessStack
      rw [hst1]
      have hg : p.grants .read = true := by cases p <;> rfl
      simp only [findGranting, hg, and_self, ite_true, List.any_nil, Bool.false_eq_true, ite_false,
        List.filter_nil, List.nil_append, Option.map_some, Option.some.injEq, Prod.mk.injEq]
      cases m₁; simp_all
    simp only [hrd1] at hne ⊢
    cases hrc : runCallee ts c m₁ with
    | ub => simp [hrc, Outcome.bind] at hne
    | halted obs => simp [Outcome.bind]
    | done obs m₂ =>
      simp only [hrc, Outcome.bind] at hne ⊢
      let freshB : Bool := decide (NextFresh m)
      have hf : freshB = true ∨ prot = true := by
        rcases hfresh with h | h
        · exact Or.inl (decide_eq_true h)
        · exact Or.inr h
      have hinv0 : CalleeInv.Inv p prot m.next m.val true freshB ts m₁ :=
        Or.inl ⟨hval1, by rw [hnxt1]; exact Nat.lt_succ_self _, fun _ => hts, [], s₁, by simpa using hst1,
          fun _ h => (by cases h), fun hfb => hfr1 (of_decide_eq_true hfb)⟩
      obtain ⟨env', hinv2⟩ := CalleeInv.inv_runCallee hp (fun _ => rfl) hf c ts m₁ obs m₂ hinv0 hrc
      rcases CalleeInv.read_at_inv_good hinv2 with hrd2 | ⟨_, hnone⟩
      · simp [hrd2]
      · simp [hnone] at hne

/-- **Read elimination across unknown code, mutable reference not passed.** If the
reference is `unique` (a `&mut`), the unknown code is not given the reference's tag,
and either the next tag is fresh or the entry reborrow is protected, then replacing the
read after the call by the value read before the call is a refinement, for all callee
code and all initial states. -/
theorem readElim_refines_of_fresh_or_protected_of_unique_of_unpassed
    (p : Perm) (prot : Bool) (a : Tag) (ts : List Tag) (c : List COp) (m : Mem)
    (hfresh : NextFresh m ∨ prot = true) (hp : p = .unique) (hts : m.next ∉ ts) :
    Refines (readElimTgt p prot a ts c m) (readElimSrc p prot a ts c m) := by
  exact readElim_refines_of_not_sharedRW_aux p prot a ts c m hfresh (by subst hp; decide) hts

/-- Tightness of `hts` in `readElim_refines_of_fresh_or_protected_of_unique_of_unpassed`:
`x` itself (tag `1`) is passed to unknown code that writes through it. All other
hypotheses hold and refinement fails visibly. -/
theorem readElim_unpassed_needed :
    (NextFresh initMem ∨ false = true) ∧ Perm.unique = .unique ∧ ¬ initMem.next ∉ [1] ∧
      ¬ Refines (readElimTgt .unique false 0 [1] [.write 0 9] initMem)
          (readElimSrc .unique false 0 [1] [.write 0 9] initMem) ∧
      ¬ VisiblyRefines (readElimTgt .unique false 0 [1] [.write 0 9] initMem)
          (readElimSrc .unique false 0 [1] [.write 0 9] initMem) := by decide

/-- Tightness of `hp` in `readElim_refines_of_fresh_or_protected_of_unique_of_unpassed`:
with `p = sharedRW`, the new item is inserted directly above the root, below an
existing `sharedRW` sibling (tag `1`); the callee writes through the sibling without
removing `x`. All other hypotheses hold and refinement fails visibly. -/
theorem readElim_unique_needed :
    (NextFresh memSibling ∨ false = true) ∧ ¬ Perm.sharedRW = .unique ∧
      memSibling.next ∉ [1] ∧
      ¬ Refines (readElimTgt .sharedRW false 0 [1] [.write 0 9] memSibling)
          (readElimSrc .sharedRW false 0 [1] [.write 0 9] memSibling) ∧
      ¬ VisiblyRefines (readElimTgt .sharedRW false 0 [1] [.write 0 9] memSibling)
          (readElimSrc .sharedRW false 0 [1] [.write 0 9] memSibling) := by decide

/-- Tightness of `hfresh` in `readElim_refines_of_fresh_or_protected_of_unique_of_unpassed`:
the tag is not fresh (an old item already carries the tag of `x`, in the unreachable
state `memDupNext`) and the reborrow is unprotected; the callee writes through the
parent, removing `x`, and the source's second read silently uses the old item. All
other hypotheses hold and refinement fails visibly. -/
theorem readElim_fresh_or_protected_needed :
    ¬ (NextFresh memDupNext ∨ false = true) ∧ Perm.unique = .unique ∧
      memDupNext.next ∉ [0] ∧
      ¬ Refines (readElimTgt .unique false 0 [0] [.write 0 9] memDupNext)
          (readElimSrc .unique false 0 [0] [.write 0 9] memDupNext) ∧
      ¬ VisiblyRefines (readElimTgt .unique false 0 [0] [.write 0 9] memDupNext)
          (readElimSrc .unique false 0 [0] [.write 0 9] memDupNext) := by decide

/-- Non-vacuity of `readElim_refines_of_fresh_or_protected_of_unique_of_unpassed`: all
hypotheses hold for an unprotected `&mut` and a callee that holds the parent tag, acts
observably, creates a `sharedRW` child of the parent, and returns; the source is defined
with observations `[3, 4, 0, 0]`. -/
theorem readElim_unpassed_nonvacuous :
    (NextFresh initMem ∨ false = true) ∧ Perm.unique = .unique ∧ initMem.next ∉ [0] ∧
      (readElimSrc .unique false 0 [0] [.emit 3, .retag 0 .sharedRW, .emit 4] initMem).visible =
        some (true, [3, 4, 0, 0], some 0) := by decide

/-- A second instance of all hypotheses of
`readElim_refines_of_fresh_or_protected_of_unique_of_unpassed` in which the callee does
access the location: it writes through the parent (removing the unprotected `x`) and
then halts, so neither side reaches the eliminated read; the source is defined. -/
theorem readElim_unpassed_nonvacuous_halting :
    (NextFresh initMem ∨ false = true) ∧ Perm.unique = .unique ∧ initMem.next ∉ [0] ∧
      (readElimSrc .unique false 0 [0] [.write 0 9, .read 0, .halt] initMem).visible =
        some (false, [9], none) := by decide

/-! ## Read elimination through a read-only shared reference -/

/-- **Read elimination across unknown code, read-only shared reference.** If the
reference is `sharedRO` (a shared reference without interior mutability) and either the
next tag is fresh or the entry reborrow is protected, replacing the read after the call
by the value read before the call is a refinement, for **any** tags handed to the
callee, including the reference itself. -/
theorem readElim_refines_of_fresh_or_protected_of_sharedRO
    (p : Perm) (prot : Bool) (a : Tag) (ts : List Tag) (c : List COp) (m : Mem)
    (hfresh : NextFresh m ∨ prot = true) (hp : p = .sharedRO) :
    Refines (readElimTgt p prot a ts c m) (readElimSrc p prot a ts c m) := by
  subst hp
  intro hne
  unfold readElimTgt
  unfold readElimSrc at hne ⊢
  cases hr : retag a .sharedRO prot m with
  | none => simp [hr, liftO] at hne
  | some xm =>
    rcases xm with ⟨x, m₁⟩
    simp only [hr, liftO] at hne ⊢
    unfold retag at hr
    cases ha : accessStack .read a m.stack with
    | none => simp [ha] at hr
    | some s₁ =>
      simp only [ha, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      have hrd1 : Toy.Alias.read m.next
          { val := m.val, stack := ⟨.sharedRO, m.next, prot⟩ :: s₁, next := m.next + 1 } =
          some (m.val, { val := m.val, stack := ⟨.sharedRO, m.next, prot⟩ :: s₁, next := m.next + 1 }) := by
        simp [Toy.Alias.read, accessStack, findGranting, Perm.grants]
      simp only [hrd1] at hne ⊢
      cases hrc : runCallee ts c
          { val := m.val, stack := ⟨.sharedRO, m.next, prot⟩ :: s₁, next := m.next + 1 } with
      | ub => simp [hrc, Outcome.bind] at hne
      | halted obs => simp [Outcome.bind]
      | done obs m₂ =>
        simp only [hrc, Outcome.bind] at hne ⊢
        let freshB : Bool := decide (NextFresh m)
        have hf : freshB = true ∨ prot = true := by
          rcases hfresh with h | h
          · exact Or.inl (decide_eq_true h)
          · exact Or.inr h
        have hinv0 : CalleeInv.Inv .sharedRO prot m.next m.val false freshB ts
            { val := m.val, stack := ⟨.sharedRO, m.next, prot⟩ :: s₁, next := m.next + 1 } :=
          Or.inl ⟨rfl, Nat.lt_succ_self _, fun h => (by cases h), [], s₁, rfl,
            fun _ h => (by cases h),
            fun hfb => accessStack_sublist_prop (of_decide_eq_true hfb) ha⟩
        obtain ⟨env', hinv2⟩ := CalleeInv.inv_runCallee (by decide) (fun h => (by cases h)) hf c ts _ obs m₂ hinv0 hrc
        rcases CalleeInv.read_at_inv_good hinv2 with hrd2 | ⟨_, hnone⟩
        · simp [hrd2]
        · simp [hnone] at hne

/-- Tightness of `hp` in `readElim_refines_of_fresh_or_protected_of_sharedRO`: an
interior-mutable shared reference (`sharedRW`) handed to the callee, which writes
through it. All other hypotheses hold and refinement fails visibly. -/
theorem readElim_sharedRO_needed :
    (NextFresh initMem ∨ false = true) ∧ ¬ Perm.sharedRW = .sharedRO ∧
      ¬ Refines (readElimTgt .sharedRW false 0 [1] [.write 0 9] initMem)
          (readElimSrc .sharedRW false 0 [1] [.write 0 9] initMem) ∧
      ¬ VisiblyRefines (readElimTgt .sharedRW false 0 [1] [.write 0 9] initMem)
          (readElimSrc .sharedRW false 0 [1] [.write 0 9] initMem) := by decide

/-- Tightness of `hfresh` in `readElim_refines_of_fresh_or_protected_of_sharedRO`: the tag
is not fresh (an old write-capable item already carries the tag of the shared
reference, in the unreachable state `memDupNext`) and the reborrow is unprotected; the
callee "writes through the shared reference", which uses the old item. All other
hypotheses hold and refinement fails visibly. -/
theorem readElim_sharedRO_fresh_or_protected_needed :
    ¬ (NextFresh memDupNext ∨ false = true) ∧ Perm.sharedRO = .sharedRO ∧
      ¬ Refines (readElimTgt .sharedRO false 0 [1] [.write 0 9] memDupNext)
          (readElimSrc .sharedRO false 0 [1] [.write 0 9] memDupNext) ∧
      ¬ VisiblyRefines (readElimTgt .sharedRO false 0 [1] [.write 0 9] memDupNext)
          (readElimSrc .sharedRO false 0 [1] [.write 0 9] memDupNext) := by decide

/-- Non-vacuity of `readElim_refines_of_fresh_or_protected_of_sharedRO`: the shared
reference is handed to the callee, which reads through it, reborrows it, and reads
through the reborrow; the source is defined. -/
theorem readElim_sharedRO_nonvacuous :
    (NextFresh initMem ∨ false = true) ∧ Perm.sharedRO = .sharedRO ∧
      (readElimSrc .sharedRO false 0 [1] [.read 0, .retag 0 .sharedRO, .read 1]
        initMem).visible = some (true, [0, 0, 0, 0], some 0) := by decide

/-! ## Moving a read through a protected mutable reference down across the call -/

/-- Proof-internal: under the hypotheses of the next theorem (for any `p ≠ sharedRW`), the
target and source are equal. -/
private theorem readDefer_eq_of_protected_of_not_sharedRW_aux
    (p : Perm) (prot : Bool) (a : Tag) (ts : List Tag) (c : List COp) (m : Mem)
    (hprot : prot = true) (hp : p ≠ .sharedRW) (hts : m.next ∉ ts) :
    readDeferTgt p prot a ts c m = readDeferSrc p prot a ts c m := by
  subst hprot
  unfold readDeferTgt readDeferSrc
  cases hr : retag a p true m with
  | none => rfl
  | some xm =>
    rcases xm with ⟨x, m₁⟩
    simp only [liftO]
    have hm1 : x = m.next ∧ m₁.val = m.val ∧ m₁.next = m.next + 1 ∧
        ∃ s₁, m₁.stack = ⟨p, m.next, true⟩ :: s₁ := by
      unfold retag at hr
      cases p with
      | sharedRW => exact absurd rfl hp
      | unique =>
        cases ha : accessStack .write a m.stack with
        | none => simp [ha] at hr
        | some s₁ =>
          simp only [ha, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr; exact ⟨rfl, rfl, rfl, s₁, rfl⟩
      | sharedRO =>
        cases ha : accessStack .read a m.stack with
        | none => simp [ha] at hr
        | some s₁ =>
          simp only [ha, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr; exact ⟨rfl, rfl, rfl, s₁, rfl⟩
    obtain ⟨rfl, hval1, hnxt1, s₁, hst1⟩ := hm1
    have hrd1 : Toy.Alias.read m.next m₁ = some (m.val, m₁) := by
      unfold Toy.Alias.read accessStack
      rw [hst1]
      have hg : p.grants .read = true := by cases p <;> rfl
      simp only [findGranting, hg, and_self, ite_true, List.any_nil, Bool.false_eq_true, ite_false,
        List.filter_nil, List.nil_append, Option.map_some, Option.some.injEq, Prod.mk.injEq]
      cases m₁; simp_all
    simp only [hrd1]
    cases hrc : runCallee ts c m₁ with
    | ub => rfl
    | halted obs => rfl
    | done obs m₂ =>
      simp only [Outcome.bind]
      have hinv0 : CalleeInv.Inv p true m.next m.val true false ts m₁ :=
        Or.inl ⟨hval1, by rw [hnxt1]; exact Nat.lt_succ_self _, fun _ => hts, [], s₁, by simpa using hst1,
          fun _ h => (by cases h), fun h => (by cases h)⟩
      obtain ⟨env', hinv2⟩ := CalleeInv.inv_runCallee hp (fun _ => rfl) (Or.inr rfl) c ts m₁ obs m₂ hinv0 hrc
      rcases CalleeInv.read_at_inv_good hinv2 with hrd2 | ⟨hff, _⟩
      · simp [hrd2]
      · cases hff

/-- **Read deferral across unknown code, protected mutable reference not passed.** If the
entry reborrow is protected, the reference is `unique` (a `&mut`), and the unknown code
is not given the reference's tag, then moving the read from before the call to after it
is a refinement. No freshness hypothesis is needed. -/
theorem readDefer_refines_of_protected_of_unique_of_unpassed
    (p : Perm) (prot : Bool) (a : Tag) (ts : List Tag) (c : List COp) (m : Mem)
    (hprot : prot = true) (hp : p = .unique) (hts : m.next ∉ ts) :
    Refines (readDeferTgt p prot a ts c m) (readDeferSrc p prot a ts c m) := by
  exact fun _ => readDefer_eq_of_protected_of_not_sharedRW_aux p prot a ts c m hprot (by subst hp; decide) hts

/-- Tightness of `hprot` in `readDefer_refines_of_protected_of_unique_of_unpassed`:
without a protector, a callee holding the parent tag merely *reads* through it; this
removes `x`, so the target's deferred read is UB while the source is defined. All other
hypotheses hold. -/
theorem readDefer_protected_needed :
    ¬ false = true ∧ Perm.unique = .unique ∧ initMem.next ∉ [0] ∧
      ¬ Refines (readDeferTgt .unique false 0 [0] [.read 0] initMem)
          (readDeferSrc .unique false 0 [0] [.read 0] initMem) ∧
      ¬ VisiblyRefines (readDeferTgt .unique false 0 [0] [.read 0] initMem)
          (readDeferSrc .unique false 0 [0] [.read 0] initMem) := by decide

/-- Tightness of `hts` in `readDefer_refines_of_protected_of_unique_of_unpassed`: `x`
itself is passed and the callee writes through it. All other hypotheses hold. -/
theorem readDefer_unpassed_needed :
    true = true ∧ Perm.unique = .unique ∧ ¬ initMem.next ∉ [1] ∧
      ¬ Refines (readDeferTgt .unique true 0 [1] [.write 0 9] initMem)
          (readDeferSrc .unique true 0 [1] [.write 0 9] initMem) ∧
      ¬ VisiblyRefines (readDeferTgt .unique true 0 [1] [.write 0 9] initMem)
          (readDeferSrc .unique true 0 [1] [.write 0 9] initMem) := by decide

/-- Tightness of `hp` in `readDefer_refines_of_protected_of_unique_of_unpassed`: a
protected `sharedRW` reference sits below a `sharedRW` sibling, through which the callee
writes without removing `x`. All other hypotheses hold. -/
theorem readDefer_unique_needed :
    true = true ∧ ¬ Perm.sharedRW = .unique ∧ memSibling.next ∉ [1] ∧
      ¬ Refines (readDeferTgt .sharedRW true 0 [1] [.write 0 9] memSibling)
          (readDeferSrc .sharedRW true 0 [1] [.write 0 9] memSibling) ∧
      ¬ VisiblyRefines (readDeferTgt .sharedRW true 0 [1] [.write 0 9] memSibling)
          (readDeferSrc .sharedRW true 0 [1] [.write 0 9] memSibling) := by decide

/-- Non-vacuity of `readDefer_refines_of_protected_of_unique_of_unpassed`: a protected
`&mut` and a callee holding the parent tag that acts observably and creates a
`sharedRW` child of the parent; the source is defined. -/
theorem readDefer_unpassed_nonvacuous :
    true = true ∧ Perm.unique = .unique ∧ initMem.next ∉ [0] ∧
      (readDeferSrc .unique true 0 [0] [.emit 3, .retag 0 .sharedRW] initMem).visible =
        some (true, [3, 0], some 0) := by decide

/-! ## Moving a read through a protected read-only shared reference down -/

/-- Proof-internal: under the hypotheses of the next theorem, target and source are
equal. -/
private theorem readDefer_eq_of_protected_of_sharedRO_aux
    (p : Perm) (prot : Bool) (a : Tag) (ts : List Tag) (c : List COp) (m : Mem)
    (hprot : prot = true) (hp : p = .sharedRO) :
    readDeferTgt p prot a ts c m = readDeferSrc p prot a ts c m := by
  subst hprot hp
  unfold readDeferTgt readDeferSrc
  cases hr : retag a .sharedRO true m with
  | none => rfl
  | some xm =>
    rcases xm with ⟨x, m₁⟩
    simp only [liftO]
    unfold retag at hr
    cases ha : accessStack .read a m.stack with
    | none => simp [ha] at hr
    | some s₁ =>
      simp only [ha, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      have hrd1 : Toy.Alias.read m.next
          { val := m.val, stack := ⟨.sharedRO, m.next, true⟩ :: s₁, next := m.next + 1 } =
          some (m.val, { val := m.val, stack := ⟨.sharedRO, m.next, true⟩ :: s₁, next := m.next + 1 }) := by
        simp [Toy.Alias.read, accessStack, findGranting, Perm.grants]
      simp only [hrd1]
      cases hrc : runCallee ts c
          { val := m.val, stack := ⟨.sharedRO, m.next, true⟩ :: s₁, next := m.next + 1 } with
      | ub => rfl
      | halted obs => rfl
      | done obs m₂ =>
        simp only [Outcome.bind]
        have hinv0 : CalleeInv.Inv .sharedRO true m.next m.val false false ts
            { val := m.val, stack := ⟨.sharedRO, m.next, true⟩ :: s₁, next := m.next + 1 } :=
          Or.inl ⟨rfl, Nat.lt_succ_self _, fun h => (by cases h), [], s₁, rfl,
            fun _ h => (by cases h), fun h => (by cases h)⟩
        obtain ⟨env', hinv2⟩ := CalleeInv.inv_runCallee (by decide) (fun h => (by cases h)) (Or.inr rfl)
          c ts _ obs m₂ hinv0 hrc
        rcases CalleeInv.read_at_inv_good hinv2 with hrd2 | ⟨hff, _⟩
        · simp [hrd2]
        · cases hff

/-- **Read deferral across unknown code, protected read-only shared reference.** If the
entry reborrow is protected and the reference is `sharedRO`, moving the read from
before the call to after it is a refinement, for any tags handed to the callee
(including the reference itself). -/
theorem readDefer_refines_of_protected_of_sharedRO
    (p : Perm) (prot : Bool) (a : Tag) (ts : List Tag) (c : List COp) (m : Mem)
    (hprot : prot = true) (hp : p = .sharedRO) :
    Refines (readDeferTgt p prot a ts c m) (readDeferSrc p prot a ts c m) := by
  exact fun _ => readDefer_eq_of_protected_of_sharedRO_aux p prot a ts c m hprot hp

/-- Tightness of `hprot` in `readDefer_refines_of_protected_of_sharedRO`: without a
protector, a callee holding the parent tag writes through it, removing the shared
reference; the target's deferred read is UB. All other hypotheses hold. -/
theorem readDefer_sharedRO_protected_needed :
    ¬ false = true ∧ Perm.sharedRO = .sharedRO ∧
      ¬ Refines (readDeferTgt .sharedRO false 0 [0] [.write 0 9] initMem)
          (readDeferSrc .sharedRO false 0 [0] [.write 0 9] initMem) ∧
      ¬ VisiblyRefines (readDeferTgt .sharedRO false 0 [0] [.write 0 9] initMem)
          (readDeferSrc .sharedRO false 0 [0] [.write 0 9] initMem) := by decide

/-- Tightness of `hp` in `readDefer_refines_of_protected_of_sharedRO`: a protected
interior-mutable shared reference handed to the callee, which writes through it. All
other hypotheses hold. -/
theorem readDefer_sharedRO_needed :
    true = true ∧ ¬ Perm.sharedRW = .sharedRO ∧
      ¬ Refines (readDeferTgt .sharedRW true 0 [1] [.write 0 9] initMem)
          (readDeferSrc .sharedRW true 0 [1] [.write 0 9] initMem) ∧
      ¬ VisiblyRefines (readDeferTgt .sharedRW true 0 [1] [.write 0 9] initMem)
          (readDeferSrc .sharedRW true 0 [1] [.write 0 9] initMem) := by decide

/-- Non-vacuity of `readDefer_refines_of_protected_of_sharedRO`: the protected shared
reference is handed to the callee, which reads through it; the source is defined. -/
theorem readDefer_sharedRO_nonvacuous :
    true = true ∧ Perm.sharedRO = .sharedRO ∧
      (readDeferSrc .sharedRO true 0 [1] [.read 0] initMem).visible =
        some (true, [0, 0], some 0) := by decide

/-! ## Dead-store elimination before unknown code -/

/-- Proof-internal: under the hypotheses of the next theorem, target and source are
equal. -/
private theorem dse_eq_of_protected_of_unique_of_unpassed_aux
    (a : Tag) (ts : List Tag) (c : List COp) (v₁ v₂ : Nat) (m : Mem)
    (hts : m.next ∉ ts) :
    dseTgt .unique true a ts c v₂ m = dseSrc .unique true a ts c v₁ v₂ m := by
  unfold dseTgt dseSrc
  cases hr : retag a .unique true m with
  | none => rfl
  | some xm1 =>
    rcases xm1 with ⟨x, m₁⟩
    unfold retag at hr
    cases ha : accessStack .write a m.stack with
    | none => simp [ha] at hr
    | some s₁ =>
      simp only [ha, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      have hw : Toy.Alias.write m.next v₁
          { val := m.val, stack := ⟨.unique, m.next, true⟩ :: s₁, next := m.next + 1 } =
          some { val := v₁, stack := ⟨.unique, m.next, true⟩ :: s₁, next := m.next + 1 } := by
        simp [Toy.Alias.write, accessStack, findGranting, Perm.grants]
      simp only [liftO, hw]
      have hvi := CalleeInv.runCallee_val_indep_under_protected_unique c ts m.next v₁ m.val s₁ (m.next + 1)
        hts (Nat.lt_succ_self _)
      cases h1 : runCallee ts c ⟨v₁, ⟨.unique, m.next, true⟩ :: s₁, m.next + 1⟩ with
      | ub =>
        cases h2 : runCallee ts c ⟨m.val, ⟨.unique, m.next, true⟩ :: s₁, m.next + 1⟩ with
        | ub => rfl
        | halted _ => simp [h1, h2] at hvi
        | done _ _ => simp [h1, h2] at hvi
      | halted o1 =>
        cases h2 : runCallee ts c ⟨m.val, ⟨.unique, m.next, true⟩ :: s₁, m.next + 1⟩ with
        | ub => simp [h1, h2] at hvi
        | halted o2 => simp only [h1, h2] at hvi; subst hvi; rfl
        | done _ _ => simp [h1, h2] at hvi
      | done o1 m1 =>
        cases h2 : runCallee ts c ⟨m.val, ⟨.unique, m.next, true⟩ :: s₁, m.next + 1⟩ with
        | ub => simp [h1, h2] at hvi
        | halted _ => simp [h1, h2] at hvi
        | done o2 m2 =>
          simp only [h1, h2] at hvi
          obtain ⟨rfl, hst, hnx, r, hr1⟩ := hvi
          simp only [Outcome.bind]
          have hw1 : Toy.Alias.write m.next v₂ m1 =
              some { val := v₂, stack := ⟨.unique, m.next, true⟩ :: r, next := m1.next } := by
            unfold Toy.Alias.write accessStack; rw [hr1]; simp [findGranting, Perm.grants]
          have hr2 : m2.stack = ⟨.unique, m.next, true⟩ :: r := hst.symm.trans hr1
          have hw2 : Toy.Alias.write m.next v₂ m2 =
              some { val := v₂, stack := ⟨.unique, m.next, true⟩ :: r, next := m2.next } := by
            unfold Toy.Alias.write accessStack; rw [hr2]; simp [findGranting, Perm.grants]
          simp only [hw1, hw2, hnx]

/-- **Dead-store elimination across unknown code.** For `*x = v₁; f(ts); *x = v₂`,
removing the first store is a refinement if the entry reborrow is protected, the
reference is `unique` (a `&mut`), and the unknown code is not given the reference's tag.
No freshness hypothesis is needed. -/
theorem dse_refines_of_protected_of_unique_of_unpassed
    (p : Perm) (prot : Bool) (a : Tag) (ts : List Tag) (c : List COp) (v₁ v₂ : Nat) (m : Mem)
    (hprot : prot = true) (hp : p = .unique) (hts : m.next ∉ ts) :
    Refines (dseTgt p prot a ts c v₂ m) (dseSrc p prot a ts c v₁ v₂ m) := by
  subst hprot hp
  exact fun _ => dse_eq_of_protected_of_unique_of_unpassed_aux a ts c v₁ v₂ m hts

/-- Tightness of `hprot` in `dse_refines_of_protected_of_unique_of_unpassed`: without a
protector, a callee holding the parent tag reads the stored value through the parent
(removing `x`) and then halts, so the source's second store, which would be UB, is
never reached. The callee observes `5` in the source and `0` in the target. All other
hypotheses hold. -/
theorem dse_protected_needed :
    ¬ false = true ∧ Perm.unique = .unique ∧ initMem.next ∉ [0] ∧
      ¬ Refines (dseTgt .unique false 0 [0] [.read 0, .halt] 7 initMem)
          (dseSrc .unique false 0 [0] [.read 0, .halt] 5 7 initMem) ∧
      ¬ VisiblyRefines (dseTgt .unique false 0 [0] [.read 0, .halt] 7 initMem)
          (dseSrc .unique false 0 [0] [.read 0, .halt] 5 7 initMem) := by decide

/-- Tightness of `hp` in `dse_refines_of_protected_of_unique_of_unpassed`: a protected
`sharedRW` reference survives a read through the parent, so the callee observes the
store and the source's second store still succeeds. All other hypotheses hold. -/
theorem dse_unique_needed :
    true = true ∧ ¬ Perm.sharedRW = .unique ∧ initMem.next ∉ [0] ∧
      ¬ Refines (dseTgt .sharedRW true 0 [0] [.read 0] 7 initMem)
          (dseSrc .sharedRW true 0 [0] [.read 0] 5 7 initMem) ∧
      ¬ VisiblyRefines (dseTgt .sharedRW true 0 [0] [.read 0] 7 initMem)
          (dseSrc .sharedRW true 0 [0] [.read 0] 5 7 initMem) := by decide

/-- Tightness of `hts` in `dse_refines_of_protected_of_unique_of_unpassed`: `x` itself is
passed and the callee reads through it. All other hypotheses hold. -/
theorem dse_unpassed_needed :
    true = true ∧ Perm.unique = .unique ∧ ¬ initMem.next ∉ [1] ∧
      ¬ Refines (dseTgt .unique true 0 [1] [.read 0] 7 initMem)
          (dseSrc .unique true 0 [1] [.read 0] 5 7 initMem) ∧
      ¬ VisiblyRefines (dseTgt .unique true 0 [1] [.read 0] 7 initMem)
          (dseSrc .unique true 0 [1] [.read 0] 5 7 initMem) := by decide

/-- Non-vacuity of `dse_refines_of_protected_of_unique_of_unpassed`: a protected `&mut`
and a callee holding the parent tag that acts observably and creates a `sharedRW` child
of the parent; the source is defined. -/
theorem dse_nonvacuous :
    true = true ∧ Perm.unique = .unique ∧ initMem.next ∉ [0] ∧
      (dseSrc .unique true 0 [0] [.emit 3, .retag 0 .sharedRW] 5 7 initMem).visible =
        some (true, [3], some 7) := by decide

/-- A second instance of all hypotheses of
`dse_refines_of_protected_of_unique_of_unpassed`, with a callee that acts observably and
never returns; the source is defined. -/
theorem dse_nonvacuous_halting :
    true = true ∧ Perm.unique = .unique ∧ initMem.next ∉ [0] ∧
      (dseSrc .unique true 0 [0] [.emit 3, .halt] 5 7 initMem).visible =
        some (false, [3], none) := by decide

/-- The later overwrite is part of the dead-store shape: removing `*x = 5` before an
unknown call that does nothing, with nothing overwriting it afterwards, changes the
final stored value (`5` versus `0`; observations and borrow stacks agree), even though
the reference is a protected, unpassed `&mut` with a fresh tag. -/
theorem storeElim_without_overwrite_not_refines :
    (true = true ∧ Perm.unique = .unique ∧ initMem.next ∉ ([] : List Tag) ∧
        NextFresh initMem) ∧
      storeElimSrc .unique true 0 [] [] 5 initMem =
        .done [] ⟨5, [⟨.unique, 1, true⟩, ⟨.unique, 0, false⟩], 2⟩ ∧
      storeElimTgt .unique true 0 [] [] initMem =
        .done [] ⟨0, [⟨.unique, 1, true⟩, ⟨.unique, 0, false⟩], 2⟩ ∧
      ¬ Refines (storeElimTgt .unique true 0 [] [] initMem)
          (storeElimSrc .unique true 0 [] [] 5 initMem) ∧
      ¬ VisiblyRefines (storeElimTgt .unique true 0 [] [] initMem)
          (storeElimSrc .unique true 0 [] [] 5 initMem) := by decide

/-! ## Boundary facts

Two facts that delimit what the results above say. First, a protected read-only shared
reference cannot be written at all, so the dead-store shape is UB from its first store
for `p = sharedRO` (`dseSrc_sharedRO_protected_ub`); this is why the dead-store result is
stated for `p = unique` only. Second, with a single tracked location, a protected
`unique` item at the top of the stack whose tag the callee does not hold makes every
callee access to the location UB (`runCallee_ub_of_touches_of_protected_unique_head`):
the only non-UB callees under the protected results for `&mut` are those that, before
halting, only act observably (`emit`) or create `sharedRW` reborrows
(`dseSrc_ub_of_touches`, `readDeferSrc_unique_ub_of_touches`). -/

/-- A protected read-only shared reference makes the dead-store source UB at its first
store, for every parent tag, callee, values, and initial state. -/
theorem dseSrc_sharedRO_protected_ub
    (a : Tag) (ts : List Tag) (c : List COp) (v₁ v₂ : Nat) (m : Mem) :
    dseSrc .sharedRO true a ts c v₁ v₂ m = .ub := by
  unfold dseSrc
  cases hr : retag a .sharedRO true m with
  | none => rfl
  | some xm =>
    rcases xm with ⟨x, m₁⟩
    unfold retag at hr
    cases ha : accessStack .read a m.stack with
    | none => simp [ha] at hr
    | some s₁ =>
      simp only [ha, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      have hw : write m.next v₁
          { val := m.val, stack := ⟨.sharedRO, m.next, true⟩ :: s₁, next := m.next + 1 } =
            none := by
        unfold write accessStack
        have hfalse : ¬ (({ perm := .sharedRO, tag := m.next, prot := true } : Item).tag =
            m.next ∧ Perm.sharedRO.grants .write = true) := by simp [Perm.grants]
        rw [findGranting_cons_skip hfalse]
        cases findGranting .write m.next s₁ with
        | none => rfl
        | some res =>
          rcases res with ⟨ab, g, bl⟩
          simp [invalidatedBy]
      simp [liftO, hw]

/-- For `p = sharedRO` the dead-store target can be defined while the source is UB, so a
refinement statement for `p = sharedRO` would hold only because the source is UB. -/
theorem dse_sharedRO_tgt_defined_src_ub :
    dseSrc .sharedRO true 0 [] [.halt] 5 7 initMem = .ub ∧
      dseTgt .sharedRO true 0 [] [.halt] 7 initMem = .halted [] := by decide

/-- Whether a callee operation accesses the tracked location. `emit` does not, and
neither does creating a `sharedRW` reborrow, which inserts an item without an access;
`halt` ends the callee. -/
def COp.touchesLocation : COp → Bool
  | .read _ => true
  | .write _ _ => true
  | .retag _ .unique => true
  | .retag _ .sharedRO => true
  | .retag _ .sharedRW => false
  | .emit _ => false
  | .halt => false

/-- `TouchesBeforeHalt c`: some operation of `c` before its first `halt` (if any)
accesses the tracked location. -/
def TouchesBeforeHalt : List COp → Bool
  | [] => false
  | .halt :: _ => false
  | op :: c => op.touchesLocation || TouchesBeforeHalt c

/-- Positive example: a read before halting touches the location. -/
theorem touchesBeforeHalt_example_pos : TouchesBeforeHalt [.emit 1, .read 0, .halt] = true := by
  decide

/-- Negative example: accesses after `halt` are never executed. -/
theorem touchesBeforeHalt_example_neg :
    TouchesBeforeHalt [.emit 1, .retag 0 .sharedRW, .halt, .read 0] = false := by decide

private theorem accessStack_head_prot_unique_ub {k : AccessKind} {t x : Tag}
    {rest : List Item} (hne : t ≠ x) :
    accessStack k t (⟨.unique, x, true⟩ :: rest) = none := by
  unfold accessStack
  have h1 : ¬ (({ perm := .unique, tag := x, prot := true } : Item).tag = t ∧
      Perm.unique.grants k = true) := fun h => hne h.1.symm
  rw [findGranting_cons_skip h1]
  cases findGranting k t rest with
  | none => rfl
  | some res =>
    rcases res with ⟨ab, g, bl⟩
    cases k <;> simp [invalidatedBy]

private theorem insertAboveGranting_head_unique {t x : Tag} {new : Item} {rest : List Item}
    (hne : t ≠ x) :
    insertAboveGranting .write t new (⟨.unique, x, true⟩ :: rest) =
      (insertAboveGranting .write t new rest).map (⟨.unique, x, true⟩ :: ·) := by
  unfold insertAboveGranting
  have h1 : ¬ (({ perm := .unique, tag := x, prot := true } : Item).tag = t ∧
      Perm.unique.grants .write = true) := fun h => hne h.1.symm
  rw [findGranting_cons_skip h1]
  cases findGranting .write t rest <;> rfl

/-- **Single-location callee restriction.** If the top of the stack is a protected
`unique` item whose tag `x` the callee does not hold (and `x` is below the tag counter,
so the callee cannot create it), every callee that accesses the tracked location before
halting has UB. -/
theorem runCallee_ub_of_touches_of_protected_unique_head
    (c : List COp) (env : List Tag) (x : Tag) (m : Mem) (rest : List Item)
    (hstack : m.stack = ⟨.unique, x, true⟩ :: rest) (henv : x ∉ env) (hnext : x < m.next)
    (htouch : TouchesBeforeHalt c = true) :
    runCallee env c m = .ub := by
  induction c generalizing env m rest with
  | nil => simp [TouchesBeforeHalt] at htouch
  | cons op c ih =>
    cases op with
    | halt => simp [TouchesBeforeHalt] at htouch
    | emit v =>
      simp only [TouchesBeforeHalt, COp.touchesLocation, Bool.false_or] at htouch
      simp only [runCallee, ih env m rest hstack henv hnext htouch, Outcome.consObs]
    | read i =>
      unfold runCallee
      cases hi : env[i]? with
      | none => rfl
      | some t =>
        have hne : t ≠ x := fun heq => henv (heq ▸ List.mem_of_getElem? hi)
        have hr : read t m = none := by
          unfold read; rw [hstack, accessStack_head_prot_unique_ub hne]; rfl
        simp [liftO, hr]
    | write i v =>
      unfold runCallee
      cases hi : env[i]? with
      | none => rfl
      | some t =>
        have hne : t ≠ x := fun heq => henv (heq ▸ List.mem_of_getElem? hi)
        have hw : write t v m = none := by
          unfold write; rw [hstack, accessStack_head_prot_unique_ub hne]; rfl
        simp [liftO, hw]
    | retag i p' =>
      cases p' with
      | unique =>
        unfold runCallee
        cases hi : env[i]? with
        | none => rfl
        | some t =>
          have hne : t ≠ x := fun heq => henv (heq ▸ List.mem_of_getElem? hi)
          have hrt : retag t .unique false m = none := by
            unfold retag; rw [hstack, accessStack_head_prot_unique_ub hne]; rfl
          simp [liftO, hrt]
      | sharedRO =>
        unfold runCallee
        cases hi : env[i]? with
        | none => rfl
        | some t =>
          have hne : t ≠ x := fun heq => henv (heq ▸ List.mem_of_getElem? hi)
          have hrt : retag t .sharedRO false m = none := by
            dsimp only [retag]; rw [hstack, accessStack_head_prot_unique_ub hne]; rfl
          simp [liftO, hrt]
      | sharedRW =>
        simp only [TouchesBeforeHalt, COp.touchesLocation, Bool.false_or] at htouch
        unfold runCallee
        cases hi : env[i]? with
        | none => rfl
        | some t =>
          have hne : t ≠ x := fun heq => henv (heq ▸ List.mem_of_getElem? hi)
          have hrt : retag t .sharedRW false m =
              (insertAboveGranting .write t ⟨.sharedRW, m.next, false⟩ rest).map fun rest' =>
                (m.next, { m with stack := ⟨.unique, x, true⟩ :: rest', next := m.next + 1 }) := by
            unfold retag
            simp only [hstack, insertAboveGranting_head_unique hne]
            cases insertAboveGranting .write t ⟨.sharedRW, m.next, false⟩ rest <;> simp
          simp only [liftO, hrt]
          cases hins : insertAboveGranting .write t ⟨.sharedRW, m.next, false⟩ rest with
          | none => rfl
          | some rest' =>
            simp only [Option.map_some]
            have henv' : x ∉ env ++ [m.next] := by
              simp only [List.mem_append, List.mem_singleton, not_or]
              exact ⟨henv, Nat.ne_of_lt hnext⟩
            exact ih (env ++ [m.next])
              { m with stack := ⟨.unique, x, true⟩ :: rest', next := m.next + 1 }
              rest' rfl henv' (Nat.lt_succ_of_lt hnext) htouch

/-- Under the hypotheses of `dse_refines_of_protected_of_unique_of_unpassed`, a callee
that accesses the tracked location before halting makes the dead-store source UB. -/
theorem dseSrc_ub_of_touches (a : Tag) (ts : List Tag) (c : List COp) (v₁ v₂ : Nat)
    (m : Mem) (hts : m.next ∉ ts) (htouch : TouchesBeforeHalt c = true) :
    dseSrc .unique true a ts c v₁ v₂ m = .ub := by
  unfold dseSrc
  cases ha : accessStack .write a m.stack with
  | none => simp [retag, ha, liftO]
  | some s =>
    have hr : retag a .unique true m =
        some (m.next, { m with stack := ⟨.unique, m.next, true⟩ :: s, next := m.next + 1 }) := by
      simp [retag, ha]
    have hw : write m.next v₁ { m with stack := ⟨.unique, m.next, true⟩ :: s, next := m.next + 1 } =
        some { val := v₁, stack := ⟨.unique, m.next, true⟩ :: s, next := m.next + 1 } := by
      simp [write, accessStack, findGranting, Perm.grants]
    have hc := runCallee_ub_of_touches_of_protected_unique_head c ts m.next
      { val := v₁, stack := ⟨.unique, m.next, true⟩ :: s, next := m.next + 1 } s rfl hts
      (Nat.lt_succ_self _) htouch
    simp [hr, hw, liftO, hc, Outcome.bind]

/-- Under the hypotheses of `readDefer_refines_of_protected_of_unique_of_unpassed`, a
callee that accesses the tracked location before halting makes the read-deferral source
UB. -/
theorem readDeferSrc_unique_ub_of_touches (a : Tag) (ts : List Tag) (c : List COp) (m : Mem)
    (hts : m.next ∉ ts) (htouch : TouchesBeforeHalt c = true) :
    readDeferSrc .unique true a ts c m = .ub := by
  unfold readDeferSrc
  cases ha : accessStack .write a m.stack with
  | none => simp [retag, ha, liftO]
  | some s =>
    have hr : retag a .unique true m =
        some (m.next, { m with stack := ⟨.unique, m.next, true⟩ :: s, next := m.next + 1 }) := by
      simp [retag, ha]
    have hrd : read m.next { m with stack := ⟨.unique, m.next, true⟩ :: s, next := m.next + 1 } =
        some (m.val, { m with stack := ⟨.unique, m.next, true⟩ :: s, next := m.next + 1 }) := by
      simp [read, accessStack, findGranting, Perm.grants]
    have hc := runCallee_ub_of_touches_of_protected_unique_head c ts m.next
      { m with stack := ⟨.unique, m.next, true⟩ :: s, next := m.next + 1 } s rfl hts
      (Nat.lt_succ_self _) htouch
    simp [hr, hrd, liftO, hc, Outcome.bind]

end Toy.Alias
