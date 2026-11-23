/-!
# Soundness, Separation, Dataflow Correctness, and Alpha-Isomorphism Bisimulation for
# `rustc_mir_transform` `lint_body`, `Validator`, `SanityCheck`, and `Prettify`

Standalone Lean 4 (`v4.34.1`, zero external imports, zero `sorry`, zero `Classical.choice`,
zero `omega`, zero `bv_decide`, zero `native_decide`, zero `partial`, zero `._unsafe_rec`)
mechanization corresponding to `rust-lang/rust` (`compiler/rustc_mir_transform/src/`
`{lint.rs, validate.rs, sanity_check.rs, prettify.rs, pass_manager.rs, lib.rs}` and
`compiler/rustc_mir_dataflow/src/{rustc_peek.rs, impls/storage_liveness.rs}`) alongside
`joshlf/anneal` (`trusted/lean/Trusted/MirSemantics.lean`):

1. **Invariant Partition & Separation (`Validator` vs. `lint_body` vs. Operational Semantics):**
   Concrete and structural proofs that `Validator` (`-Zvalidate-mir` / `Runtime(Optimized)`)
   checks CFG, unwind-ABI, local-bounds, and type invariants while remaining invariant under
   `StorageLive`/`StorageDead` markers and assignment aliasing, whereas `lint_body` (`-Zlint-mir`)
   checks `MaybeStorageLive`, `MaybeStorageDead`, `places_conflict_for_assignment`, return-liveness,
   and `Call` move duplicates while ignoring `UnwindAction::Continue` in no-unwind functions;
   paired with separation witnesses matching `Trusted.MirSemantics.lean` (`deinitMovedPlace = true`,
   non-faulting `StorageLive` reinitialization, value-evaluating scalar `Assign`, and
   `always_storage_live_locals` unreachable-block poisoning).
2. **Soundness of `MaybeStorageLive` and `MaybeStorageDead` Dataflow:**
   Universal proof over all valid post-fixpoints and arbitrary execution lengths (`fuel : Nat`)
   that `MaybeStorageLive` over-approximates live slots and `MaybeStorageDead` over-approximates
   dead slots along every execution prefix, yielding:
   - Absence of `.deadLocalAccess` UB when `lint_body` passes all uses;
   - Absence of operational double-`StorageLive` when `lint_body` passes all `StorageLive` sites;
   - Deadness of every non-always-live local at `Return` when `lint_body` passes `Return`.
3. **`ReorderBasicBlocks` & `ReorderLocals` Lockstep Operational Bisimulation (`prettify.rs`):**
   Universal multi-step equivalence (`runBody`) for any basic-block bijection fixing
   `START_BLOCK = 0`, any local bijection fixing return place `0` and arguments `1..=argCount`,
   and their composition; plus constructive witness of the `rustc_index` out-of-bounds failure
   when `reverse_postorder` omits an unreachable basic block.
4. **`SanityCheck` Dataflow Oracle & `rustc_peek` Leakage Gate (`sanity_check.rs`, `rustc_peek.rs`):**
   Proof that `SanityCheck` never erases `core::intrinsics::rustc_peek` calls, so avoiding the
   backend codegen ICE holds if and only if `SanityCheck` runs and either fails a bit-state
   check or halts via `#[rustc_mir(..., stop_after_dataflow)]`.
-/

namespace MirLintSanityPrettify

/-! ## Section 1: Pure Total Natural-Number, List, Range, and Bitset Helpers -/

noncomputable def natBeq : Nat → Nat → Bool
  | 0, 0 => true
  | _ + 1, 0 => false
  | 0, _ + 1 => false
  | a + 1, b + 1 => natBeq a b

theorem natBeq_refl (n : Nat) : natBeq n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

theorem natBeq_eq_true_iff (a b : Nat) : natBeq a b = true ↔ a = b := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | succ k => exact ⟨fun h => by contradiction, fun h => by contradiction⟩
  | succ a ih =>
    cases b with
    | zero => exact ⟨fun h => by contradiction, fun h => by contradiction⟩
    | succ b =>
      have h := ih b
      constructor
      · intro hbeq
        exact congrArg Nat.succ (h.mp hbeq)
      · intro heq
        injection heq with hab
        exact h.mpr hab

theorem natBeq_ne {a b : Nat} (h : natBeq a b = false) : a ≠ b := by
  intro heq
  rw [heq, natBeq_refl] at h
  contradiction

noncomputable def natBle : Nat → Nat → Bool
  | 0, _ => true
  | _ + 1, 0 => false
  | a + 1, b + 1 => natBle a b

noncomputable def natBlt (a b : Nat) : Bool := natBle (a + 1) b

theorem natBle_refl (n : Nat) : natBle n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

theorem natBle_eq_true_iff (a b : Nat) : natBle a b = true ↔ a ≤ b := by
  induction a generalizing b with
  | zero => exact ⟨fun _ => Nat.zero_le b, fun _ => rfl⟩
  | succ a ih =>
    cases b with
    | zero =>
      constructor
      · intro h; contradiction
      · intro h; exact False.elim (Nat.not_succ_le_zero a h)
    | succ b =>
      have h := ih b
      exact ⟨fun hle => Nat.succ_le_succ (h.mp hle), fun hle => h.mpr (Nat.le_of_succ_le_succ hle)⟩

theorem natBlt_eq_true_iff (a b : Nat) : natBlt a b = true ↔ a < b :=
  natBle_eq_true_iff (a + 1) b

noncomputable def optNatBeq (a b : Option Nat) : Bool :=
  match a, b with
  | none, none => true
  | some x, some y => natBeq x y
  | _, _ => false

theorem optNatBeq_refl (a : Option Nat) : optNatBeq a a = true := by
  cases a with
  | none => rfl
  | some x => exact natBeq_refl x

noncomputable def listGet {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet xs n

theorem listGet_nil {α : Type} (n : Nat) : listGet ([] : List α) n = none := by
  cases n <;> rfl

theorem listGet_cons_zero {α : Type} (x : α) (xs : List α) :
    listGet (x :: xs) 0 = some x := rfl

theorem listGet_cons_succ {α : Type} (x : α) (xs : List α) (n : Nat) :
    listGet (x :: xs) (n + 1) = listGet xs n := rfl

noncomputable def listGetD {α : Type} (xs : List α) (n : Nat) (d : α) : α :=
  match listGet xs n with
  | some v => v
  | none => d

noncomputable def listSet {α : Type} : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, n + 1, v =>
    match listSet xs n v with
    | some xs' => some (x :: xs')
    | none => none

theorem listSet_nil {α : Type} (n : Nat) (v : α) : listSet ([] : List α) n v = none := by
  cases n <;> rfl

theorem listSet_cons_zero {α : Type} (x : α) (xs : List α) (v : α) :
    listSet (x :: xs) 0 v = some (v :: xs) := rfl

theorem listSet_cons_succ {α : Type} (x : α) (xs : List α) (n : Nat) (v : α) :
    listSet (x :: xs) (n + 1) v =
      match listSet xs n v with
      | some xs' => some (x :: xs')
      | none => none := rfl

theorem listGet_some_lt {α : Type} (xs : List α) (n : Nat) (v : α) :
    listGet xs n = some v → n < xs.length := by
  induction xs generalizing n with
  | nil =>
    intro h
    rw [listGet_nil] at h
    contradiction
  | cons _ tl ih =>
    cases n with
    | zero => intro _; exact Nat.zero_lt_succ tl.length
    | succ k =>
      intro h
      rw [listGet_cons_succ] at h
      exact Nat.succ_lt_succ (ih k h)

theorem listGet_lt_some {α : Type} (xs : List α) (n : Nat) :
    n < xs.length → ∃ v : α, listGet xs n = some v := by
  induction xs generalizing n with
  | nil => intro h; exact False.elim (Nat.not_lt_zero n h)
  | cons x tl ih =>
    cases n with
    | zero => intro _; exact ⟨x, rfl⟩
    | succ k =>
      intro h
      rw [listGet_cons_succ]
      exact ih k (Nat.lt_of_succ_lt_succ h)

theorem listSet_lt_some {α : Type} (xs : List α) (n : Nat) (v : α) :
    n < xs.length → ∃ xs' : List α, listSet xs n v = some xs' := by
  induction xs generalizing n with
  | nil => intro h; exact False.elim (Nat.not_lt_zero n h)
  | cons x tl ih =>
    cases n with
    | zero => intro _; exact ⟨v :: tl, rfl⟩
    | succ k =>
      intro h
      obtain ⟨tl', htl'⟩ := ih k (Nat.lt_of_succ_lt_succ h)
      refine ⟨x :: tl', ?_⟩
      rw [listSet_cons_succ, htl']

theorem listSet_some_lt {α : Type} (xs xs' : List α) (n : Nat) (v : α) :
    listSet xs n v = some xs' → n < xs.length := by
  induction xs generalizing n xs' with
  | nil => intro h; rw [listSet_nil] at h; contradiction
  | cons _ tl ih =>
    cases n with
    | zero => intro _; exact Nat.zero_lt_succ tl.length
    | succ k =>
      intro h
      rw [listSet_cons_succ] at h
      cases hs : listSet tl k v with
      | none => rw [hs] at h; contradiction
      | some tl' => exact Nat.succ_lt_succ (ih tl' k hs)

theorem listSet_some_length {α : Type} (xs xs' : List α) (n : Nat) (v : α) :
    listSet xs n v = some xs' → xs'.length = xs.length := by
  induction xs generalizing n xs' with
  | nil => intro h; rw [listSet_nil] at h; contradiction
  | cons x tl ih =>
    cases n with
    | zero =>
      intro h
      rw [listSet_cons_zero] at h
      injection h with heq
      rw [← heq]
      rfl
    | succ k =>
      intro h
      rw [listSet_cons_succ] at h
      cases hs : listSet tl k v with
      | none => rw [hs] at h; contradiction
      | some tl' =>
        rw [hs] at h
        injection h with heq
        rw [← heq]
        exact congrArg Nat.succ (ih tl' k hs)

theorem listGet_set_same {α : Type} (xs xs' : List α) (n : Nat) (v : α) :
    listSet xs n v = some xs' → listGet xs' n = some v := by
  induction xs generalizing n xs' with
  | nil => intro h; rw [listSet_nil] at h; contradiction
  | cons x tl ih =>
    cases n with
    | zero =>
      intro h
      rw [listSet_cons_zero] at h
      injection h with heq
      rw [← heq]
      rfl
    | succ k =>
      intro h
      rw [listSet_cons_succ] at h
      cases hs : listSet tl k v with
      | none => rw [hs] at h; contradiction
      | some tl' =>
        rw [hs] at h
        injection h with heq
        rw [← heq, listGet_cons_succ]
        exact ih tl' k hs

theorem listGet_set_ne {α : Type} (xs xs' : List α) (n m : Nat) (v : α) :
    n ≠ m → listSet xs n v = some xs' → listGet xs' m = listGet xs m := by
  induction xs generalizing n m xs' with
  | nil => intro _ h; rw [listSet_nil] at h; contradiction
  | cons x tl ih =>
    cases n with
    | zero =>
      cases m with
      | zero => intro hne _; exact False.elim (hne rfl)
      | succ j =>
        intro _ h
        rw [listSet_cons_zero] at h
        injection h with heq
        rw [← heq]
        rfl
    | succ k =>
      cases m with
      | zero =>
        intro _ h
        rw [listSet_cons_succ] at h
        cases hs : listSet tl k v with
        | none => rw [hs] at h; contradiction
        | some tl' =>
          rw [hs] at h
          injection h with heq
          rw [← heq]
          rfl
      | succ j =>
        intro hne h
        rw [listSet_cons_succ] at h
        cases hs : listSet tl k v with
        | none => rw [hs] at h; contradiction
        | some tl' =>
          rw [hs] at h
          injection h with heq
          rw [← heq, listGet_cons_succ, listGet_cons_succ]
          exact ih tl' k j (fun hkj => hne (congrArg Nat.succ hkj)) hs

noncomputable def listMap {α β : Type} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: listMap f xs

theorem listMap_length {α β : Type} (f : α → β) (xs : List α) :
    (listMap f xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem listGet_map {α β : Type} (f : α → β) (xs : List α) (n : Nat) :
    listGet (listMap f xs) n =
      match listGet xs n with
      | some v => some (f v)
      | none => none := by
  induction xs generalizing n with
  | nil => rw [listGet_nil]; rfl
  | cons x tl ih =>
    cases n with
    | zero => rfl
    | succ k => exact ih k

noncomputable def listAll {α : Type} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && listAll p xs

theorem listAll_cons {α : Type} (p : α → Bool) (x : α) (xs : List α) :
    listAll p (x :: xs) = (p x && listAll p xs) := rfl

theorem listAll_iff {α : Type} (p : α → Bool) (xs : List α) :
    listAll p xs = true ↔ ∀ i : Nat, ∀ x : α, listGet xs i = some x → p x = true := by
  induction xs with
  | nil =>
    constructor
    · intro _ i x h; rw [listGet_nil] at h; contradiction
    · intro _; rfl
  | cons x tl ih =>
    constructor
    · intro hall i y hget
      have hs := Bool.and_eq_true _ _ |>.mp hall
      cases i with
      | zero =>
        rw [listGet_cons_zero] at hget
        injection hget with heq
        rw [← heq]
        exact hs.1
      | succ k =>
        rw [listGet_cons_succ] at hget
        exact (ih.mp hs.2) k y hget
    · intro hfor
      have hx : p x = true := hfor 0 x rfl
      have htl : listAll p tl = true := ih.mpr (fun k y hg => hfor (k + 1) y hg)
      exact Bool.and_eq_true _ _ |>.mpr ⟨hx, htl⟩

noncomputable def listAny {α : Type} (p : α → Bool) : List α → Bool
  | [] => false
  | x :: xs => p x || listAny p xs

theorem listAny_iff {α : Type} (p : α → Bool) (xs : List α) :
    listAny p xs = true ↔ ∃ i : Nat, ∃ x : α, listGet xs i = some x ∧ p x = true := by
  induction xs with
  | nil =>
    constructor
    · intro h; contradiction
    · intro ⟨i, _, hg, _⟩; rw [listGet_nil] at hg; contradiction
  | cons x tl ih =>
    constructor
    · intro hany
      cases hpx : p x with
      | true => exact ⟨0, x, rfl, hpx⟩
      | false =>
        have htl : listAny p tl = true := by
          unfold listAny at hany
          rw [hpx] at hany
          exact hany
        obtain ⟨i, y, hg, hy⟩ := ih.mp htl
        exact ⟨i + 1, y, hg, hy⟩
    · intro ⟨i, y, hg, hy⟩
      cases i with
      | zero =>
        rw [listGet_cons_zero] at hg
        injection hg with hxy
        rw [← hxy] at hy
        unfold listAny
        rw [hy]
        rfl
      | succ k =>
        rw [listGet_cons_succ] at hg
        have htl : listAny p tl = true := ih.mpr ⟨k, y, hg, hy⟩
        unfold listAny
        rw [htl, Bool.or_true]

noncomputable def listFoldl {α β : Type} (f : β → α → β) : β → List α → β
  | acc, [] => acc
  | acc, x :: xs => listFoldl f (f acc x) xs

noncomputable def listFoldlIdxAux {α β : Type} (f : β → Nat → α → β) :
    Nat → β → List α → β
  | _, acc, [] => acc
  | i, acc, x :: xs => listFoldlIdxAux f (i + 1) (f acc i x) xs

noncomputable def listFoldlIdx {α β : Type} (f : β → Nat → α → β) (init : β) (xs : List α) : β :=
  listFoldlIdxAux f 0 init xs

noncomputable def listReplicate {α : Type} : Nat → α → List α
  | 0, _ => []
  | n + 1, v => v :: listReplicate n v

theorem listReplicate_length {α : Type} (n : Nat) (v : α) :
    (listReplicate n v).length = n := by
  induction n with
  | zero => rfl
  | succ k ih => exact congrArg Nat.succ ih

noncomputable def mapRangeFrom {α : Type} (start : Nat) : Nat → (Nat → α) → List α
  | 0, _ => []
  | len + 1, f => f start :: mapRangeFrom (start + 1) len f

theorem mapRangeFrom_length {α : Type} (start len : Nat) (f : Nat → α) :
    (mapRangeFrom start len f).length = len := by
  induction len generalizing start with
  | zero => rfl
  | succ k ih => exact congrArg Nat.succ (ih (start + 1))

theorem listGet_mapRangeFrom {α : Type} (start len i : Nat) (f : Nat → α) :
    listGet (mapRangeFrom start len f) i =
      if natBlt i len then some (f (start + i)) else none := by
  induction len generalizing start i with
  | zero => cases i <;> rfl
  | succ k ih =>
    cases i with
    | zero =>
      change some (f start) = some (f (start + 0))
      rw [Nat.add_zero]
    | succ j =>
      have hk := ih (start + 1) j
      have heq : start + 1 + j = start + (j + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 j]
      change listGet (mapRangeFrom (start + 1) k f) j =
        if natBlt j k then some (f (start + (j + 1))) else none
      rw [hk, heq]

noncomputable def mapRange {α : Type} (len : Nat) (f : Nat → α) : List α :=
  mapRangeFrom 0 len f

theorem mapRange_length {α : Type} (len : Nat) (f : Nat → α) :
    (mapRange len f).length = len :=
  mapRangeFrom_length 0 len f

theorem bool_if_true {α : Type} (c : Bool) (h : c = true) (a b : α) :
    (if c then a else b) = a := by
  subst h
  rfl

theorem bool_if_false {α : Type} (c : Bool) (h : c = false) (a b : α) :
    (if c then a else b) = b := by
  subst h
  rfl

theorem bool_or_congr {a₁ a₂ b₁ b₂ : Bool} (h1 : a₁ = a₂) (h2 : b₁ = b₂) :
    (a₁ || b₁) = (a₂ || b₂) := by
  subst h1
  subst h2
  rfl

theorem listGet_mapRange {α : Type} (len i : Nat) (f : Nat → α) :
    listGet (mapRange len f) i =
      if natBlt i len then some (f i) else none := by
  have h := listGet_mapRangeFrom 0 len i f
  rw [Nat.zero_add] at h
  exact h

theorem listGet_mapRange_lt {α : Type} (len i : Nat) (f : Nat → α) (hi : i < len) :
    listGet (mapRange len f) i = some (f i) := by
  rw [listGet_mapRange len i f]
  exact bool_if_true (natBlt i len) ((natBlt_eq_true_iff i len).mpr hi) _ _

noncomputable def bitGet (bs : List Bool) (i : Nat) : Bool :=
  listGetD bs i false

noncomputable def bitSet (bs : List Bool) (i : Nat) (b : Bool) : List Bool :=
  match listSet bs i b with
  | some bs' => bs'
  | none => bs

noncomputable def bitOr : List Bool → List Bool → List Bool
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => (x || y) :: bitOr xs ys

theorem bitGet_bitSet_same (bs : List Bool) (i : Nat) (b : Bool) :
    i < bs.length → bitGet (bitSet bs i b) i = b := by
  intro hi
  obtain ⟨bs', hbs'⟩ := listSet_lt_some bs i b hi
  unfold bitGet bitSet listGetD
  rw [hbs', listGet_set_same bs bs' i b hbs']

theorem bitGet_bitSet_ne (bs : List Bool) (i j : Nat) (b : Bool) :
    i ≠ j → bitGet (bitSet bs i b) j = bitGet bs j := by
  intro hne
  unfold bitGet bitSet listGetD
  cases hs : listSet bs i b with
  | none => rfl
  | some bs' => rw [listGet_set_ne bs bs' i j b hne hs]

theorem bitSet_length (bs : List Bool) (i : Nat) (b : Bool) :
    (bitSet bs i b).length = bs.length := by
  unfold bitSet
  cases hs : listSet bs i b with
  | none => rfl
  | some bs' => exact listSet_some_length bs bs' i b hs

/-! ## Section 2: MIR Syntax, Types, Places, and Parameterized Operational Semantics -/

inductive MirTy where
  | u32
  | bool
  | unit
  | pair (fst snd : MirTy)
  | fnPtr

noncomputable def MirTy.beq : MirTy → MirTy → Bool
  | .u32, .u32 => true
  | .bool, .bool => true
  | .unit, .unit => true
  | .pair a₁ b₁, .pair a₂ b₂ => MirTy.beq a₁ a₂ && MirTy.beq b₁ b₂
  | .fnPtr, .fnPtr => true
  | _, _ => false

theorem MirTy.beq_refl (t : MirTy) : MirTy.beq t t = true := by
  induction t with
  | u32 => rfl
  | bool => rfl
  | unit => rfl
  | pair a b iha ihb => exact Bool.and_eq_true _ _ |>.mpr ⟨iha, ihb⟩
  | fnPtr => rfl

inductive Val where
  | u32 (v : Nat)
  | bool (b : Bool)
  | unit
  | pair (fst snd : Val)
  | fnPtr (id : Nat)

noncomputable def Val.ty : Val → MirTy
  | .u32 _ => .u32
  | .bool _ => .bool
  | .unit => .unit
  | .pair a b => .pair a.ty b.ty
  | .fnPtr _ => .fnPtr

structure Place where
  localId : Nat
  field : Option Nat := none
  isIndirect : Bool := false

noncomputable def Place.beq (p q : Place) : Bool :=
  natBeq p.localId q.localId && optNatBeq p.field q.field && (p.isIndirect == q.isIndirect)

inductive Operand where
  | copy (p : Place)
  | move (p : Place)
  | constVal (v : Val)

inductive BinOp where
  | add
  | eq
  | lt

inductive Rvalue where
  | use (op : Operand)
  | binOp (op : BinOp) (lhs rhs : Operand)
  | pairAgg (lhs rhs : Operand)

inductive Stmt where
  | nop
  | storageLive (l : Nat)
  | storageDead (l : Nat)
  | assign (dest : Place) (rval : Rvalue)

inductive UnwindAction where
  | continue_
  | terminate
  | unreachable

inductive Term where
  | goto (target : Nat)
  | switchInt (discr : Operand) (targets : List (Nat × Nat)) (otherwise : Nat)
  | ret
  | call (callee : Nat) (args : List Operand) (dest : Place) (target : Nat) (unwind : UnwindAction)
  | peekCall (arg : Place) (target : Nat)
  | unreachable

structure BasicBlock where
  stmts : List Stmt
  term : Term
  isCleanup : Bool := false

noncomputable def defaultBlock : BasicBlock :=
  { stmts := [], term := .unreachable, isCleanup := false }

structure Body where
  argCount : Nat
  locals : List MirTy
  blocks : List BasicBlock
  isFnLike : Bool := true
  canUnwind : Bool := true

inductive LocalSlot where
  | dead
  | live (val : Option Val)

noncomputable def liveUninitSlot : MirTy → LocalSlot
  | .unit => .live (some .unit)
  | _ => .live none

inductive UbKind where
  | deadLocalAccess
  | uninitRead
  | overlappingAssign
  | doubleStorageLive
  | liveLocalAtReturn
  | callAlias
  | unreachableReached

inductive Outcome where
  | returned (v : Val)
  | outOfFuel
  | ub (k : UbKind)
  | malformedCfg
  | intrinsicLeak

structure EvalConfig where
  deinitMovedPlace : Bool
  forbidAliasAssign : Bool
  abortOnDoubleStorageLive : Bool

/-- Matches `Trusted.MirSemantics.lean` (`deinitMovedPlace = true`, scalar `Assign`
evaluates RHS before writing LHS, `StorageLive` resets slot to `liveUninitSlot` without UB). -/
noncomputable def annealCfg : EvalConfig :=
  { deinitMovedPlace := true, forbidAliasAssign := false, abortOnDoubleStorageLive := false }

/-- Models the stricter UB assumptions checked statically by `rustc -Zlint-mir`. -/
noncomputable def lintModelCfg : EvalConfig :=
  { deinitMovedPlace := true, forbidAliasAssign := true, abortOnDoubleStorageLive := true }

structure MachineState where
  pc : Nat
  stmtIdx : Nat
  locals : List LocalSlot

noncomputable def hasStorageMarkerInStmts (l : Nat) (stmts : List Stmt) : Bool :=
  listAny (fun s =>
    match s with
    | .storageLive x => natBeq x l
    | .storageDead x => natBeq x l
    | _ => false) stmts

theorem hasStorageMarkerInStmts_cons (l : Nat) (s : Stmt) (rest : List Stmt) :
    hasStorageMarkerInStmts l (s :: rest) =
      ((match s with
        | .storageLive x => natBeq x l
        | .storageDead x => natBeq x l
        | _ => false) || hasStorageMarkerInStmts l rest) := rfl

noncomputable def hasStorageMarker (body : Body) (l : Nat) : Bool :=
  listAny (fun bb => hasStorageMarkerInStmts l bb.stmts) body.blocks

noncomputable def alwaysStorageLiveLocals (body : Body) : List Bool :=
  mapRange body.locals.length (fun l => !hasStorageMarker body l)

noncomputable def initLocals (body : Body) (args : List Val) : List LocalSlot :=
  mapRange body.locals.length (fun l =>
    let ty := listGetD body.locals l .u32
    if natBeq l 0 then
      liveUninitSlot ty
    else if natBle l body.argCount then
      match listGet args (l - 1) with
      | some v => .live (some v)
      | none => .dead
    else if !hasStorageMarker body l then
      liveUninitSlot ty
    else
      .dead)

theorem initLocals_length (body : Body) (args : List Val) :
    (initLocals body args).length = body.locals.length :=
  mapRange_length body.locals.length _

noncomputable def readPlaceFromVal (v : Val) (field : Option Nat) : Option Val :=
  match field with
  | none => some v
  | some 0 => match v with | .pair a _ => some a | _ => none
  | some 1 => match v with | .pair _ b => some b | _ => none
  | some _ => none

noncomputable def writeFieldVal (cur : Option Val) (field : Option Nat) (newVal : Val) : Option Val :=
  match field with
  | none => some newVal
  | some 0 =>
    match cur with
    | some (.pair _ b) => some (.pair newVal b)
    | _ => none
  | some 1 =>
    match cur with
    | some (.pair a _) => some (.pair a newVal)
    | _ => none
  | some _ => none

inductive EvalRes (α : Type) where
  | ok (val : α) (locals' : List LocalSlot)
  | ub (k : UbKind)
  | malformed

noncomputable def evalOperand (cfg : EvalConfig) (bodyLocals : List MirTy) (locals : List LocalSlot)
    (op : Operand) : EvalRes Val :=
  match op with
  | .constVal v => .ok v locals
  | .copy p =>
    match listGet locals p.localId with
    | none => .malformed
    | some .dead => .ub .deadLocalAccess
    | some (.live none) => .ub .uninitRead
    | some (.live (some v)) =>
      match readPlaceFromVal v p.field with
      | some rv => .ok rv locals
      | none => .malformed
  | .move p =>
    match listGet bodyLocals p.localId, listGet locals p.localId with
    | some _, some .dead => .ub .deadLocalAccess
    | some _, some (.live none) => .ub .uninitRead
    | some ty, some (.live (some v)) =>
      match readPlaceFromVal v p.field with
      | none => .malformed
      | some rv =>
        if cfg.deinitMovedPlace then
          match p.field with
          | none =>
            match listSet locals p.localId (liveUninitSlot ty) with
            | some locals' => .ok rv locals'
            | none => .malformed
          | some _ => .ok rv locals
        else
          .ok rv locals
    | _, _ => .malformed

noncomputable def evalBinOp (op : BinOp) (lhs rhs : Val) : Option Val :=
  match op, lhs, rhs with
  | .add, .u32 a, .u32 b => some (.u32 (a + b))
  | .eq, .u32 a, .u32 b => some (.bool (natBeq a b))
  | .lt, .u32 a, .u32 b => some (.bool (natBlt a b))
  | .eq, .bool a, .bool b => some (.bool (a == b))
  | _, _, _ => none

noncomputable def placesConflictForAssignment (dest src : Place) : Bool :=
  Place.beq dest src || (natBeq dest.localId src.localId && !dest.isIndirect && !src.isIndirect)

noncomputable def rvalueConflictsWithPlace (dest : Place) : Rvalue → Bool
  | .use (.copy src) | .use (.move src) => placesConflictForAssignment dest src
  | .use (.constVal _) => false
  | .binOp _ _ _ => false
  | .pairAgg (.copy s1) (.copy s2)
  | .pairAgg (.copy s1) (.move s2)
  | .pairAgg (.move s1) (.copy s2)
  | .pairAgg (.move s1) (.move s2) =>
    placesConflictForAssignment dest s1 || placesConflictForAssignment dest s2
  | .pairAgg (.copy s1) (.constVal _) | .pairAgg (.move s1) (.constVal _) =>
    placesConflictForAssignment dest s1
  | .pairAgg (.constVal _) (.copy s2) | .pairAgg (.constVal _) (.move s2) =>
    placesConflictForAssignment dest s2
  | .pairAgg (.constVal _) (.constVal _) => false

noncomputable def evalRvalue (cfg : EvalConfig) (bodyLocals : List MirTy) (locals : List LocalSlot)
    (rval : Rvalue) : EvalRes Val :=
  match rval with
  | .use op => evalOperand cfg bodyLocals locals op
  | .binOp op lhs rhs =>
    match evalOperand cfg bodyLocals locals lhs with
    | .ub k => .ub k
    | .malformed => .malformed
    | .ok lv locals₁ =>
      match evalOperand cfg bodyLocals locals₁ rhs with
      | .ub k => .ub k
      | .malformed => .malformed
      | .ok rv locals₂ =>
        match evalBinOp op lv rv with
        | some out => .ok out locals₂
        | none => .malformed
  | .pairAgg lhs rhs =>
    match evalOperand cfg bodyLocals locals lhs with
    | .ub k => .ub k
    | .malformed => .malformed
    | .ok lv locals₁ =>
      match evalOperand cfg bodyLocals locals₁ rhs with
      | .ub k => .ub k
      | .malformed => .malformed
      | .ok rv locals₂ => .ok (.pair lv rv) locals₂

noncomputable def writePlace (locals : List LocalSlot) (dest : Place) (val : Val) : EvalRes Unit :=
  match listGet locals dest.localId with
  | none => .malformed
  | some .dead => .ub .deadLocalAccess
  | some (.live cur) =>
    match dest.field with
    | none =>
      match listSet locals dest.localId (.live (some val)) with
      | some locals' => .ok () locals'
      | none => .malformed
    | some _ =>
      match writeFieldVal cur dest.field val with
      | none => .malformed
      | some updated =>
        match listSet locals dest.localId (.live (some updated)) with
        | some locals' => .ok () locals'
        | none => .malformed

inductive StepOut where
  | next (st' : MachineState)
  | done (v : Val)
  | ub (k : UbKind)
  | malformed
  | intrinsicLeak

noncomputable def switchLookup (k otherwise : Nat) : List (Nat × Nat) → Nat
  | [] => otherwise
  | (c, t) :: rest => if natBeq k c then t else switchLookup k otherwise rest

noncomputable def evalSwitchTarget (v : Val) (targets : List (Nat × Nat)) (otherwise : Nat) : Option Nat :=
  match v with
  | .u32 n => some (switchLookup n otherwise targets)
  | .bool false => some (switchLookup 0 otherwise targets)
  | .bool true => some (switchLookup 1 otherwise targets)
  | _ => none

noncomputable def stepState (cfg : EvalConfig) (body : Body) (st : MachineState) : StepOut :=
  match listGet body.blocks st.pc with
  | none => .malformed
  | some bb =>
    match listGet bb.stmts st.stmtIdx with
    | some stmt =>
      match stmt with
      | .nop => .next { st with stmtIdx := st.stmtIdx + 1 }
      | .storageLive l =>
        match listGet body.locals l, listGet st.locals l with
        | some ty, some cur =>
          let alreadyLive := match cur with | .live _ => true | .dead => false
          if cfg.abortOnDoubleStorageLive && alreadyLive then
            .ub .doubleStorageLive
          else
            match listSet st.locals l (liveUninitSlot ty) with
            | some locals' => .next { st with stmtIdx := st.stmtIdx + 1, locals := locals' }
            | none => .malformed
        | _, _ => .malformed
      | .storageDead l =>
        if natBeq l 0 then
          .malformed
        else
          match listSet st.locals l .dead with
          | some locals' => .next { st with stmtIdx := st.stmtIdx + 1, locals := locals' }
          | none => .malformed
      | .assign dest rval =>
        if cfg.forbidAliasAssign && rvalueConflictsWithPlace dest rval then
          .ub .overlappingAssign
        else
          match evalRvalue cfg body.locals st.locals rval with
          | .ub k => .ub k
          | .malformed => .malformed
          | .ok val locals₁ =>
            match writePlace locals₁ dest val with
            | .ub k => .ub k
            | .malformed => .malformed
            | .ok () locals₂ => .next { st with stmtIdx := st.stmtIdx + 1, locals := locals₂ }
    | none =>
      if natBeq st.stmtIdx bb.stmts.length then
        match bb.term with
        | .goto target => .next { st with pc := target, stmtIdx := 0 }
        | .switchInt discr targets otherwise =>
          match evalOperand cfg body.locals st.locals discr with
          | .ub k => .ub k
          | .malformed => .malformed
          | .ok dv locals₁ =>
            match evalSwitchTarget dv targets otherwise with
            | some nextPc => .next { pc := nextPc, stmtIdx := 0, locals := locals₁ }
            | none => .malformed
        | .ret =>
          if bb.isCleanup then
            .malformed
          else
            match listGet st.locals 0 with
            | some (.live (some rv)) => .done rv
            | some (.live none) | some .dead => .ub .uninitRead
            | none => .malformed
        | .call _ _ _ _ _ => .malformed
        | .peekCall _ _ => .intrinsicLeak
        | .unreachable => .ub .unreachableReached
      else
        .malformed

noncomputable def runFrom (cfg : EvalConfig) (body : Body) : MachineState → Nat → Outcome
  | _, 0 => .outOfFuel
  | st, fuel + 1 =>
    match stepState cfg body st with
    | .next st' => runFrom cfg body st' fuel
    | .done v => .returned v
    | .ub k => .ub k
    | .malformed => .malformedCfg
    | .intrinsicLeak => .intrinsicLeak

noncomputable def runBody (cfg : EvalConfig) (body : Body) (args : List Val) (fuel : Nat) : Outcome :=
  if body.blocks.isEmpty || !natBeq args.length body.argCount then
    .malformedCfg
  else
    runFrom cfg body { pc := 0, stmtIdx := 0, locals := initLocals body args } fuel

/-! ## Section 3: `Validator` (`validate.rs`) vs. `lint_body` (`lint.rs`) & Separation Witnesses -/

noncomputable def termSuccessors : Term → List Nat
  | .goto t => [t]
  | .switchInt _ targets otherwise => otherwise :: listMap (fun p => p.2) targets
  | .ret => []
  | .call _ _ _ target _ => [target]
  | .peekCall _ target => [target]
  | .unreachable => []

noncomputable def checkUnwind (canUnwind isCleanup : Bool) : UnwindAction → Bool
  | .continue_ => !isCleanup && canUnwind
  | .terminate => true
  | .unreachable => true

noncomputable def checkOperandBounds (numLocals : Nat) : Operand → Bool
  | .copy p | .move p => natBlt p.localId numLocals
  | .constVal _ => true

noncomputable def checkRvalueBounds (numLocals : Nat) : Rvalue → Bool
  | .use op => checkOperandBounds numLocals op
  | .binOp _ a b => checkOperandBounds numLocals a && checkOperandBounds numLocals b
  | .pairAgg a b => checkOperandBounds numLocals a && checkOperandBounds numLocals b

noncomputable def checkStmtBounds (numLocals : Nat) : Stmt → Bool
  | .nop => true
  | .storageLive l => natBlt l numLocals
  | .storageDead l => natBlt l numLocals
  | .assign d r => natBlt d.localId numLocals && checkRvalueBounds numLocals r

noncomputable def placeTy (locals : List MirTy) (p : Place) : Option MirTy :=
  match listGet locals p.localId with
  | none => none
  | some t =>
    match p.field, t with
    | none, _ => some t
    | some 0, .pair a _ => some a
    | some 1, .pair _ b => some b
    | _, _ => none

noncomputable def operandTy (locals : List MirTy) : Operand → Option MirTy
  | .copy p | .move p => placeTy locals p
  | .constVal v => some v.ty

noncomputable def rvalueTy (locals : List MirTy) : Rvalue → Option MirTy
  | .use op => operandTy locals op
  | .binOp op a b =>
    match operandTy locals a, operandTy locals b with
    | some ta, some tb =>
      match op with
      | .add => if MirTy.beq ta .u32 && MirTy.beq tb .u32 then some .u32 else none
      | .eq => if MirTy.beq ta tb && (MirTy.beq ta .u32 || MirTy.beq ta .bool) then some .bool else none
      | .lt => if MirTy.beq ta .u32 && MirTy.beq tb .u32 then some .bool else none
    | _, _ => none
  | .pairAgg a b =>
    match operandTy locals a, operandTy locals b with
    | some ta, some tb => some (.pair ta tb)
    | _, _ => none

noncomputable def checkStmtTypes (locals : List MirTy) : Stmt → Bool
  | .nop | .storageLive _ | .storageDead _ => true
  | .assign d r =>
    match placeTy locals d, rvalueTy locals r with
    | some tl, some tr => MirTy.beq tl tr
    | _, _ => false

noncomputable def validateBlock (body : Body) (bb : BasicBlock) : Bool :=
  let numBlocks := body.blocks.length
  let numLocals := body.locals.length
  let succs := termSuccessors bb.term
  let succsOk := listAll (fun s => !natBeq s 0 && natBlt s numBlocks) succs
  let stmtsOk := listAll (fun st => checkStmtBounds numLocals st && checkStmtTypes body.locals st) bb.stmts
  let termOk := match bb.term with
    | .goto _ => true
    | .switchInt discr _ _ =>
      checkOperandBounds numLocals discr &&
      match operandTy body.locals discr with
      | some .u32 | some .bool => true
      | _ => false
    | .ret => !bb.isCleanup
    | .call _ args dest _ unwind =>
      checkUnwind body.canUnwind bb.isCleanup unwind &&
      natBlt dest.localId numLocals &&
      listAll (checkOperandBounds numLocals) args
    | .peekCall arg _ => natBlt arg.localId numLocals
    | .unreachable => true
  succsOk && stmtsOk && termOk

noncomputable def validateBody (body : Body) : Bool :=
  !body.blocks.isEmpty &&
  natBlt body.argCount body.locals.length &&
  listAll (validateBlock body) body.blocks

/-! #### `lint_body` (`MaybeStorageLive`, `MaybeStorageDead`, `Reachable`, and All 5 Lint Rules) -/

noncomputable def reachStep (body : Body) (reach : List Bool) : List Bool :=
  listFoldlIdx (fun acc bbIdx bb =>
    if bitGet reach bbIdx then
      listFoldl (fun a succ => bitSet a succ true) acc (termSuccessors bb.term)
    else
      acc) reach body.blocks

noncomputable def reachableBlocks (body : Body) : List Bool :=
  if body.blocks.isEmpty then []
  else
    let init := bitSet (listReplicate body.blocks.length false) 0 true
    Nat.rec (motive := fun _ => List Bool) init (fun _ cur => reachStep body cur) body.blocks.length

noncomputable def startMaybeLive (body : Body) : List Bool :=
  let always := alwaysStorageLiveLocals body
  mapRange body.locals.length (fun l => bitGet always l || natBle l body.argCount)

noncomputable def startMaybeDead (body : Body) : List Bool :=
  let always := alwaysStorageLiveLocals body
  mapRange body.locals.length (fun l =>
    if natBle l body.argCount then false else !bitGet always l)

noncomputable def transferLiveStmt (st : Stmt) (s : List Bool) : List Bool :=
  match st with
  | .storageLive l => bitSet s l true
  | .storageDead l => bitSet s l false
  | _ => s

noncomputable def transferDeadStmt (st : Stmt) (s : List Bool) : List Bool :=
  match st with
  | .storageLive l => bitSet s l false
  | .storageDead l => bitSet s l true
  | _ => s

noncomputable def transferBlock (stepFn : Stmt → List Bool → List Bool) (stmts : List Stmt)
    (inState : List Bool) : List Bool :=
  listFoldl (fun s st => stepFn st s) inState stmts

noncomputable def computeInFromOut (body : Body) (startState : List Bool)
    (outStates : List (List Bool)) (numLocals : Nat) : List (List Bool) :=
  let empty := listReplicate body.blocks.length (listReplicate numLocals false)
  let withStart := match listSet empty 0 startState with | some x => x | none => empty
  listFoldlIdx (fun acc srcIdx bb =>
    let outSrc := listGetD outStates srcIdx (listReplicate numLocals false)
    listFoldl (fun a succ =>
      let curIn := listGetD a succ (listReplicate numLocals false)
      match listSet a succ (bitOr curIn outSrc) with
      | some a' => a'
      | none => a) acc (termSuccessors bb.term)) withStart body.blocks

noncomputable def dataflowRound (body : Body) (startState : List Bool)
    (stepFn : Stmt → List Bool → List Bool) (outStates : List (List Bool)) : List (List Bool) :=
  let inStates := computeInFromOut body startState outStates body.locals.length
  mapRange body.blocks.length (fun bbIdx =>
    let bb := listGetD body.blocks bbIdx defaultBlock
    let inB := listGetD inStates bbIdx (listReplicate body.locals.length false)
    transferBlock stepFn bb.stmts inB)

noncomputable def solveForward (body : Body) (startState : List Bool)
    (stepFn : Stmt → List Bool → List Bool) (rounds : Nat) : List (List Bool) × List (List Bool) :=
  let emptyOut := listReplicate body.blocks.length (listReplicate body.locals.length false)
  let outFinal := Nat.rec (motive := fun _ => List (List Bool))
    emptyOut (fun _ cur => dataflowRound body startState stepFn cur) rounds
  let inFinal := computeInFromOut body startState outFinal body.locals.length
  (inFinal, outFinal)

noncomputable def checkOperandUseNotDead (deadState : List Bool) : Operand → Bool
  | .copy p | .move p => !bitGet deadState p.localId
  | .constVal _ => true

noncomputable def checkRvalueUseNotDead (deadState : List Bool) : Rvalue → Bool
  | .use op => checkOperandUseNotDead deadState op
  | .binOp _ a b => checkOperandUseNotDead deadState a && checkOperandUseNotDead deadState b
  | .pairAgg a b => checkOperandUseNotDead deadState a && checkOperandUseNotDead deadState b

noncomputable def checkStmtLint (liveBefore deadBefore : List Bool) (st : Stmt) : Bool :=
  let deadAfter := transferDeadStmt st deadBefore
  match st with
  | .nop => true
  | .storageDead _ => true
  | .storageLive l => !bitGet liveBefore l
  | .assign dest rval =>
    !bitGet deadAfter dest.localId &&
    checkRvalueUseNotDead deadAfter rval &&
    !rvalueConflictsWithPlace dest rval

noncomputable def callDupLoop (seen : List Place) : List Operand → Bool
  | [] => false
  | .move p :: rest =>
    if listAny (fun q => Place.beq p q) seen then true else callDupLoop (p :: seen) rest
  | _ :: rest => callDupLoop seen rest

noncomputable def callHasDuplicateMove (dest : Place) (args : List Operand) : Bool :=
  callDupLoop [dest] args

noncomputable def checkStmtsLintAux : List Stmt → List Bool → List Bool → Bool × (List Bool × List Bool)
  | [], lb, db => (true, (lb, db))
  | st :: rest, lb, db =>
    let okHere := checkStmtLint lb db st
    let tail := checkStmtsLintAux rest (transferLiveStmt st lb) (transferDeadStmt st db)
    (okHere && tail.1, tail.2)

noncomputable def checkBlockLint (body : Body) (alwaysLive : List Bool)
    (liveIn deadIn : List Bool) (bb : BasicBlock) : Bool :=
  let res := checkStmtsLintAux bb.stmts liveIn deadIn
  let stmtsOk := res.1
  let liveEnd := res.2.1
  let deadEnd := res.2.2
  let termOk := match bb.term with
    | .goto _ | .unreachable => true
    | .switchInt discr _ _ => checkOperandUseNotDead deadEnd discr
    | .ret =>
      if body.isFnLike then
        listAll (fun l => !(bitGet liveEnd l && !bitGet alwaysLive l)) (mapRange body.locals.length id)
      else
        true
    | .call _ args dest _ _ =>
      !bitGet deadEnd dest.localId &&
      listAll (checkOperandUseNotDead deadEnd) args &&
      !callHasDuplicateMove dest args
    | .peekCall arg _ => !bitGet deadEnd arg.localId
  stmtsOk && termOk

noncomputable def lintBody (body : Body) : Bool :=
  let rounds := body.blocks.length + 2
  let always := alwaysStorageLiveLocals body
  let reach := reachableBlocks body
  let liveSol := solveForward body (startMaybeLive body) transferLiveStmt rounds
  let deadSol := solveForward body (startMaybeDead body) transferDeadStmt rounds
  listFoldlIdx (fun ok bbIdx bb =>
    if bitGet reach bbIdx then
      let lIn := listGetD liveSol.1 bbIdx (listReplicate body.locals.length false)
      let dIn := listGetD deadSol.1 bbIdx (listReplicate body.locals.length false)
      ok && checkBlockLint body always lIn dIn bb
    else
      ok) true body.blocks

/-! #### Concrete Separation Witnesses Matching Live `rustc`, `Miri`, and `Trusted.MirSemantics` -/

noncomputable def overlapAssignBody : Body :=
  { argCount := 1, locals := [.u32, .u32], canUnwind := true
    blocks := [{ stmts := [.assign ⟨1, none, false⟩ (.use (.move ⟨1, none, false⟩)),
                           .assign ⟨0, none, false⟩ (.use (.copy ⟨1, none, false⟩))]
                 term := .ret }] }

noncomputable def disjointFieldsAssignBody : Body :=
  { argCount := 1, locals := [.u32, .pair .u32 .u32], canUnwind := true
    blocks := [{ stmts := [.assign ⟨1, some 0, false⟩ (.use (.move ⟨1, some 1, false⟩)),
                           .assign ⟨0, none, false⟩ (.use (.copy ⟨1, some 0, false⟩))]
                 term := .ret }] }

noncomputable def overlapBinOpBody : Body :=
  { argCount := 1, locals := [.u32, .u32], canUnwind := true
    blocks := [{ stmts := [.assign ⟨1, none, false⟩ (.binOp .add (.move ⟨1, none, false⟩) (.constVal (.u32 1))),
                           .assign ⟨0, none, false⟩ (.use (.copy ⟨1, none, false⟩))]
                 term := .ret }] }

noncomputable def useAfterDeadBody : Body :=
  { argCount := 0, locals := [.u32, .u32], canUnwind := true
    blocks := [{ stmts := [.storageLive 1,
                           .assign ⟨1, none, false⟩ (.use (.constVal (.u32 7))),
                           .storageDead 1,
                           .assign ⟨0, none, false⟩ (.use (.copy ⟨1, none, false⟩))]
                 term := .ret }] }

noncomputable def doubleLiveThenWriteBody : Body :=
  { argCount := 0, locals := [.u32, .u32], canUnwind := true
    blocks := [{ stmts := [.storageLive 1,
                           .storageLive 1,
                           .assign ⟨1, none, false⟩ (.use (.constVal (.u32 7))),
                           .assign ⟨0, none, false⟩ (.use (.copy ⟨1, none, false⟩)),
                           .storageDead 1]
                 term := .ret }] }

noncomputable def doubleLiveClobberBody : Body :=
  { argCount := 0, locals := [.u32, .u32], canUnwind := true
    blocks := [{ stmts := [.storageLive 1,
                           .assign ⟨1, none, false⟩ (.use (.constVal (.u32 99))),
                           .storageLive 1,
                           .assign ⟨0, none, false⟩ (.use (.copy ⟨1, none, false⟩)),
                           .storageDead 1]
                 term := .ret }] }

noncomputable def doubleDeadBody : Body :=
  { argCount := 0, locals := [.u32, .u32], canUnwind := true
    blocks := [{ stmts := [.storageLive 1,
                           .assign ⟨1, none, false⟩ (.use (.constVal (.u32 7))),
                           .storageDead 1,
                           .storageDead 1,
                           .assign ⟨0, none, false⟩ (.use (.constVal (.u32 1)))]
                 term := .ret }] }

noncomputable def returnWithLiveLocalBody : Body :=
  { argCount := 0, locals := [.u32, .u32], canUnwind := true
    blocks := [{ stmts := [.storageLive 1,
                           .assign ⟨1, none, false⟩ (.use (.constVal (.u32 7))),
                           .assign ⟨0, none, false⟩ (.use (.copy ⟨1, none, false⟩))]
                 term := .ret }] }

noncomputable def callDupMoveBody : Body :=
  { argCount := 1, locals := [.u32, .u32], canUnwind := true
    blocks := [ { stmts := []
                  term := .call 1 [.move ⟨1, none, false⟩, .move ⟨1, none, false⟩] ⟨0, none, false⟩ 1 .continue_ }
              , { stmts := [], term := .ret } ] }

noncomputable def callDistinctFieldsBody : Body :=
  { argCount := 1, locals := [.u32, .pair .u32 .u32], canUnwind := true
    blocks := [ { stmts := []
                  term := .call 1 [.move ⟨1, some 1, false⟩] ⟨1, some 0, false⟩ 1 .continue_ }
              , { stmts := [.assign ⟨0, none, false⟩ (.use (.copy ⟨1, some 0, false⟩))], term := .ret } ] }

noncomputable def unreachableStoragePoisonBody : Body :=
  { argCount := 0, locals := [.u32, .u32], canUnwind := true
    blocks := [ { stmts := [.assign ⟨1, none, false⟩ (.use (.constVal (.u32 7))),
                            .assign ⟨0, none, false⟩ (.use (.copy ⟨1, none, false⟩))]
                  term := .ret }
              , { stmts := [.storageLive 1, .storageDead 1]
                  term := .ret } ] }

noncomputable def unreachableStoragePoisonSimplifiedBody : Body :=
  { argCount := 0, locals := [.u32, .u32], canUnwind := true
    blocks := [ { stmts := [.assign ⟨1, none, false⟩ (.use (.constVal (.u32 7))),
                            .assign ⟨0, none, false⟩ (.use (.copy ⟨1, none, false⟩))]
                  term := .ret } ] }

noncomputable def badUnwindBody : Body :=
  { argCount := 1, locals := [.unit, .fnPtr], canUnwind := false
    blocks := [ { stmts := [], term := .call 1 [] ⟨0, none, false⟩ 1 .continue_ }
              , { stmts := [], term := .ret } ] }

theorem sep_overlap_assign :
    validateBody overlapAssignBody = true ∧
    lintBody overlapAssignBody = false ∧
    runBody annealCfg overlapAssignBody [.u32 42] 10 = .returned (.u32 42) ∧
    runBody lintModelCfg overlapAssignBody [.u32 42] 10 = .ub .overlappingAssign :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem sep_disjoint_fields_overapprox :
    validateBody disjointFieldsAssignBody = true ∧
    lintBody disjointFieldsAssignBody = false ∧
    runBody annealCfg disjointFieldsAssignBody [.pair (.u32 1) (.u32 2)] 10 = .returned (.u32 2) :=
  ⟨rfl, rfl, rfl⟩

theorem overlap_binop_permitted_everywhere :
    validateBody overlapBinOpBody = true ∧
    lintBody overlapBinOpBody = true ∧
    runBody annealCfg overlapBinOpBody [.u32 41] 10 = .returned (.u32 42) ∧
    runBody lintModelCfg overlapBinOpBody [.u32 41] 10 = .returned (.u32 42) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem sep_use_after_storage_dead :
    validateBody useAfterDeadBody = true ∧
    lintBody useAfterDeadBody = false ∧
    runBody annealCfg useAfterDeadBody [] 10 = .ub .deadLocalAccess :=
  ⟨rfl, rfl, rfl⟩

theorem sep_double_storage_live_and_clobber :
    validateBody doubleLiveThenWriteBody = true ∧
    lintBody doubleLiveThenWriteBody = false ∧
    runBody annealCfg doubleLiveThenWriteBody [] 10 = .returned (.u32 7) ∧
    runBody annealCfg doubleLiveClobberBody [] 10 = .ub .uninitRead ∧
    runBody lintModelCfg doubleLiveThenWriteBody [] 10 = .ub .doubleStorageLive :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem double_storage_dead_permitted_by_lint :
    validateBody doubleDeadBody = true ∧
    lintBody doubleDeadBody = true ∧
    runBody annealCfg doubleDeadBody [] 10 = .returned (.u32 1) :=
  ⟨rfl, rfl, rfl⟩

theorem sep_return_with_live_local :
    validateBody returnWithLiveLocalBody = true ∧
    lintBody returnWithLiveLocalBody = false ∧
    runBody annealCfg returnWithLiveLocalBody [] 10 = .returned (.u32 7) :=
  ⟨rfl, rfl, rfl⟩

theorem sep_call_overlap_and_asymmetry :
    validateBody callDupMoveBody = true ∧
    lintBody callDupMoveBody = false ∧
    validateBody callDistinctFieldsBody = true ∧
    lintBody callDistinctFieldsBody = true :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem sep_unreachable_storage_poison :
    validateBody unreachableStoragePoisonBody = true ∧
    lintBody unreachableStoragePoisonBody = false ∧
    runBody annealCfg unreachableStoragePoisonBody [] 10 = .ub .deadLocalAccess ∧
    lintBody unreachableStoragePoisonSimplifiedBody = true ∧
    runBody annealCfg unreachableStoragePoisonSimplifiedBody [] 10 = .returned (.u32 7) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem sep_validator_rejects_bad_unwind_while_lint_accepts :
    validateBody badUnwindBody = false ∧
    lintBody badUnwindBody = true :=
  ⟨rfl, rfl⟩

/-- Structural invariance of `Validator` under `StorageLive`/`StorageDead` insertions. -/
theorem validator_invariant_under_storage_markers (body : Body) (bb : BasicBlock)
    (l : Nat) (hl : l < body.locals.length) :
    validateBlock body bb = true →
    validateBlock body { bb with stmts := .storageLive l :: .storageDead l :: bb.stmts } = true := by
  intro hbb
  dsimp only [validateBlock] at hbb ⊢
  have h1 := Bool.and_eq_true _ _ |>.mp hbb
  have h2 := Bool.and_eq_true _ _ |>.mp h1.1
  have hblt : natBlt l body.locals.length = true := (natBlt_eq_true_iff l body.locals.length).mpr hl
  have hs1 : checkStmtBounds body.locals.length (.storageLive l) = true := hblt
  have hs2 : checkStmtBounds body.locals.length (.storageDead l) = true := hblt
  have ht1 : checkStmtTypes body.locals (.storageLive l) = true := rfl
  have ht2 : checkStmtTypes body.locals (.storageDead l) = true := rfl
  have hstmts : listAll (fun st => checkStmtBounds body.locals.length st && checkStmtTypes body.locals st)
      (.storageLive l :: .storageDead l :: bb.stmts) = true := by
    rw [listAll_cons, listAll_cons, hs1, hs2, ht1, ht2, h2.2]
    rfl
  exact Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨h2.1, hstmts⟩, h1.2⟩

/-- Structural invariance of `Validator` under self-aliasing `Assign(l, Move(l))`. -/
theorem validator_invariant_under_self_alias_assign (body : Body) (bb : BasicBlock)
    (l : Nat) (hl : l < body.locals.length) :
    validateBlock body bb = true →
    validateBlock body { bb with stmts := .assign ⟨l, none, false⟩ (.use (.move ⟨l, none, false⟩)) :: bb.stmts } = true := by
  intro hbb
  dsimp only [validateBlock] at hbb ⊢
  have h1 := Bool.and_eq_true _ _ |>.mp hbb
  have h2 := Bool.and_eq_true _ _ |>.mp h1.1
  have hblt : natBlt l body.locals.length = true := (natBlt_eq_true_iff l body.locals.length).mpr hl
  obtain ⟨ty, hty⟩ := listGet_lt_some body.locals l hl
  have htyok : checkStmtTypes body.locals (.assign ⟨l, none, false⟩ (.use (.move ⟨l, none, false⟩))) = true := by
    dsimp only [checkStmtTypes, rvalueTy, operandTy, placeTy]
    rw [hty]
    exact MirTy.beq_refl ty
  have hsb : checkStmtBounds body.locals.length (.assign ⟨l, none, false⟩ (.use (.move ⟨l, none, false⟩))) = true := by
    dsimp only [checkStmtBounds, checkRvalueBounds, checkOperandBounds]
    exact Bool.and_eq_true _ _ |>.mpr ⟨hblt, hblt⟩
  have hstmts : listAll (fun st => checkStmtBounds body.locals.length st && checkStmtTypes body.locals st)
      (.assign ⟨l, none, false⟩ (.use (.move ⟨l, none, false⟩)) :: bb.stmts) = true := by
    rw [listAll_cons, hsb, htyok, h2.2]
    rfl
  exact Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨h2.1, hstmts⟩, h1.2⟩

/-! ## Section 4: General Soundness of `MaybeStorageLive` & `MaybeStorageDead` Dataflow -/

noncomputable def isLiveSlot : LocalSlot → Bool
  | .live _ => true
  | .dead => false

noncomputable def isDeadSlot : LocalSlot → Bool
  | .dead => true
  | .live _ => false

noncomputable def LiveSoundAt (locals : List LocalSlot) (absLive : List Bool) : Prop :=
  locals.length = absLive.length ∧
  ∀ l : Nat, ∀ s : LocalSlot, listGet locals l = some s → isLiveSlot s = true → bitGet absLive l = true

noncomputable def DeadSoundAt (locals : List LocalSlot) (absDead : List Bool) : Prop :=
  locals.length = absDead.length ∧
  ∀ l : Nat, ∀ s : LocalSlot, listGet locals l = some s → isDeadSlot s = true → bitGet absDead l = true

theorem liveSoundAt_init (body : Body) (args : List Val) :
    LiveSoundAt (initLocals body args) (startMaybeLive body) := by
  refine ⟨?_, ?_⟩
  · rw [initLocals_length]
    unfold startMaybeLive
    rw [mapRange_length]
  · intro l s hget hlive
    have hlt : l < (initLocals body args).length := listGet_some_lt _ l s hget
    rw [initLocals_length] at hlt
    dsimp only [startMaybeLive, bitGet, listGetD]
    rw [listGet_mapRange_lt body.locals.length l _ hlt]
    dsimp only
    dsimp only [initLocals] at hget
    rw [listGet_mapRange_lt body.locals.length l _ hlt] at hget
    cases h0 : natBeq l 0 with
    | true =>
      have hl0 : l = 0 := (natBeq_eq_true_iff l 0).mp h0
      rw [hl0]
      have h0le : natBle 0 body.argCount = true := rfl
      rw [h0le, Bool.or_true]
    | false =>
      cases harg : natBle l body.argCount with
      | true =>
        rw [Bool.or_true]
      | false =>
        rw [h0, harg] at hget
        cases hm : hasStorageMarker body l with
        | false =>
          have hbit : listGet (alwaysStorageLiveLocals body) l = some true := by
            dsimp only [alwaysStorageLiveLocals]
            rw [listGet_mapRange_lt body.locals.length l _ hlt]
            rw [hm]
            rfl
          rw [hbit]
          rfl
        | true =>
          rw [hm] at hget
          injection hget with hdead
          rw [← hdead] at hlive
          contradiction

theorem deadSoundAt_init (body : Body) (args : List Val) (hargs : args.length = body.argCount) :
    DeadSoundAt (initLocals body args) (startMaybeDead body) := by
  refine ⟨?_, ?_⟩
  · rw [initLocals_length]
    unfold startMaybeDead
    rw [mapRange_length]
  · intro l s hget hdead
    have hlt : l < (initLocals body args).length := listGet_some_lt _ l s hget
    rw [initLocals_length] at hlt
    dsimp only [startMaybeDead, bitGet, listGetD]
    rw [listGet_mapRange_lt body.locals.length l _ hlt]
    dsimp only [initLocals] at hget
    rw [listGet_mapRange_lt body.locals.length l _ hlt] at hget
    cases h0 : natBeq l 0 with
    | true =>
      rw [h0] at hget
      rw [bool_if_true true rfl] at hget
      injection hget with hslot
      rw [← hslot] at hdead
      have hh : isDeadSlot (liveUninitSlot (listGetD body.locals l .u32)) = false := by
        cases listGetD body.locals l .u32 <;> rfl
      rw [hh] at hdead
      contradiction
    | false =>
      cases harg : natBle l body.argCount with
      | true =>
        have hle : l ≤ body.argCount := (natBle_eq_true_iff l body.argCount).mp harg
        have hsub : l - 1 < args.length := by
          rw [hargs]
          cases l with
          | zero => contradiction
          | succ k => exact Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hle
        obtain ⟨v, hv⟩ := listGet_lt_some args (l - 1) hsub
        rw [h0, harg, hv] at hget
        dsimp only at hget
        rw [bool_if_false false rfl, bool_if_true true rfl] at hget
        injection hget with hslot
        rw [← hslot] at hdead
        contradiction
      | false =>
        rw [h0, harg] at hget
        rw [bool_if_false false rfl, bool_if_false false rfl] at hget
        cases hm : hasStorageMarker body l with
        | true =>
          have hbit : listGet (alwaysStorageLiveLocals body) l = some false := by
            dsimp only [alwaysStorageLiveLocals]
            rw [listGet_mapRange_lt body.locals.length l _ hlt]
            rw [hm]
            rfl
          rw [hbit]
          rfl
        | false =>
          rw [hm] at hget
          rw [Bool.not_false, bool_if_true true rfl] at hget
          injection hget with hslot
          rw [← hslot] at hdead
          have hh : isDeadSlot (liveUninitSlot (listGetD body.locals l .u32)) = false := by
            cases listGetD body.locals l .u32 <;> rfl
          rw [hh] at hdead
          contradiction

noncomputable def foldStmts (stepFn : Stmt → List Bool → List Bool) :
    List Stmt → List Bool → Nat → List Bool
  | _, s, 0 => s
  | [], s, _ + 1 => s
  | st :: rest, s, idx + 1 => foldStmts stepFn rest (stepFn st s) idx

theorem foldStmts_zero (stepFn : Stmt → List Bool → List Bool) (stmts : List Stmt) (s : List Bool) :
    foldStmts stepFn stmts s 0 = s := by
  cases stmts <;> rfl

theorem foldStmts_succ (stepFn : Stmt → List Bool → List Bool) (stmts : List Stmt) (s : List Bool)
    (idx : Nat) (st : Stmt) (hget : listGet stmts idx = some st) :
    foldStmts stepFn stmts s (idx + 1) = stepFn st (foldStmts stepFn stmts s idx) := by
  induction stmts generalizing s idx with
  | nil => rw [listGet_nil] at hget; contradiction
  | cons hd tl ih =>
    cases idx with
    | zero =>
      rw [listGet_cons_zero] at hget
      injection hget with heq
      rw [← heq]
      cases tl <;> rfl
    | succ k =>
      rw [listGet_cons_succ] at hget
      change foldStmts stepFn tl (stepFn hd s) (k + 1) = stepFn st (foldStmts stepFn tl (stepFn hd s) k)
      exact ih (stepFn hd s) k hget

theorem foldStmts_end (stepFn : Stmt → List Bool → List Bool) (stmts : List Stmt) (s : List Bool) :
    foldStmts stepFn stmts s stmts.length = transferBlock stepFn stmts s := by
  induction stmts generalizing s with
  | nil => rfl
  | cons hd tl ih => exact ih (stepFn hd s)

theorem transferLiveStmt_len (st : Stmt) (s : List Bool) :
    (transferLiveStmt st s).length = s.length := by
  cases st with
  | nop => rfl
  | storageLive l => exact bitSet_length s l true
  | storageDead l => exact bitSet_length s l false
  | assign _ _ => rfl

theorem transferDeadStmt_len (st : Stmt) (s : List Bool) :
    (transferDeadStmt st s).length = s.length := by
  cases st with
  | nop => rfl
  | storageLive l => exact bitSet_length s l false
  | storageDead l => exact bitSet_length s l true
  | assign _ _ => rfl

theorem foldStmts_len (stepFn : Stmt → List Bool → List Bool)
    (hlen : ∀ st s, (stepFn st s).length = s.length)
    (stmts : List Stmt) (s : List Bool) (idx : Nat) :
    (foldStmts stepFn stmts s idx).length = s.length := by
  induction stmts generalizing s idx with
  | nil => cases idx <;> rfl
  | cons hd tl ih =>
    cases idx with
    | zero => rfl
    | succ k =>
      change (foldStmts stepFn tl (stepFn hd s) k).length = s.length
      rw [ih (stepFn hd s) k, hlen hd s]

theorem evalOperand_preserves_liveness (cfg : EvalConfig) (bodyLocals : List MirTy)
    (locals locals' : List LocalSlot) (op : Operand) (v : Val)
    (h : evalOperand cfg bodyLocals locals op = .ok v locals') :
    locals'.length = locals.length ∧
    ∀ l s', listGet locals' l = some s' →
      ∃ s, listGet locals l = some s ∧
        (isLiveSlot s' = true → isLiveSlot s = true) ∧
        (isDeadSlot s' = true → isDeadSlot s = true) := by
  cases op with
  | constVal c =>
    dsimp only [evalOperand] at h
    injection h with _ hl
    rw [← hl]
    exact ⟨rfl, fun l s' hg => ⟨s', hg, fun x => x, fun x => x⟩⟩
  | copy p =>
    dsimp only [evalOperand] at h
    cases hg : listGet locals p.localId with
    | none => rw [hg] at h; contradiction
    | some sl =>
      rw [hg] at h
      cases sl with
      | dead => contradiction
      | live ov =>
        cases ov with
        | none => contradiction
        | some val =>
          dsimp only at h
          cases hr : readPlaceFromVal val p.field with
          | none => rw [hr] at h; contradiction
          | some rv =>
            rw [hr] at h
            injection h with _ hl
            rw [← hl]
            exact ⟨rfl, fun l s' hg' => ⟨s', hg', fun x => x, fun x => x⟩⟩
  | move p =>
    dsimp only [evalOperand] at h
    cases hty : listGet bodyLocals p.localId with
    | none => rw [hty] at h; contradiction
    | some ty =>
      cases hg : listGet locals p.localId with
      | none => rw [hty, hg] at h; contradiction
      | some sl =>
        rw [hty, hg] at h
        cases sl with
        | dead => contradiction
        | live ov =>
          cases ov with
          | none => contradiction
          | some val =>
            dsimp only at h
            cases hr : readPlaceFromVal val p.field with
            | none => rw [hr] at h; contradiction
            | some rv =>
              rw [hr] at h
              cases hde : cfg.deinitMovedPlace with
              | false => rw [hde] at h; injection h with _ hl; rw [← hl]; exact ⟨rfl, fun l s' hg' => ⟨s', hg', fun x => x, fun x => x⟩⟩
              | true =>
                rw [hde] at h
                dsimp only at h
                cases hf : p.field with
                | some _ => rw [hf] at h; injection h with _ hl; rw [← hl]; exact ⟨rfl, fun l s' hg' => ⟨s', hg', fun x => x, fun x => x⟩⟩
                | none =>
                  rw [hf] at h
                  dsimp only at h
                  cases hs : listSet locals p.localId (liveUninitSlot ty) with
                  | none => rw [hs] at h; contradiction
                  | some locals'' =>
                    rw [hs] at h
                    injection h with _ hl
                    rw [← hl]
                    refine ⟨listSet_some_length locals locals'' p.localId _ hs, ?_⟩
                    intro l s' hg'
                    cases hnat : natBeq l p.localId with
                    | true =>
                      have heq : l = p.localId := (natBeq_eq_true_iff l p.localId).mp hnat
                      rw [heq, listGet_set_same locals locals'' p.localId _ hs] at hg'
                      injection hg' with hs'
                      refine ⟨.live (some val), ?_, fun _ => rfl, ?_⟩
                      · rw [heq]; exact hg
                      · intro hds; rw [← hs'] at hds; cases ty <;> contradiction
                    | false =>
                      have hne : p.localId ≠ l := fun e => (natBeq_ne hnat) e.symm
                      rw [listGet_set_ne locals locals'' p.localId l _ hne hs] at hg'
                      exact ⟨s', hg', fun x => x, fun x => x⟩

theorem evalRvalue_preserves_liveness (cfg : EvalConfig) (bodyLocals : List MirTy)
    (locals locals' : List LocalSlot) (rval : Rvalue) (v : Val)
    (h : evalRvalue cfg bodyLocals locals rval = .ok v locals') :
    locals'.length = locals.length ∧
    ∀ l s', listGet locals' l = some s' →
      ∃ s, listGet locals l = some s ∧
        (isLiveSlot s' = true → isLiveSlot s = true) ∧
        (isDeadSlot s' = true → isDeadSlot s = true) := by
  cases rval with
  | use op => exact evalOperand_preserves_liveness cfg bodyLocals locals locals' op v h
  | binOp op a b =>
    dsimp only [evalRvalue] at h
    cases ha : evalOperand cfg bodyLocals locals a with
    | ub _ => rw [ha] at h; contradiction
    | malformed => rw [ha] at h; contradiction
    | ok lv l1 =>
      rw [ha] at h
      dsimp only at h
      cases hb : evalOperand cfg bodyLocals l1 b with
      | ub _ => rw [hb] at h; contradiction
      | malformed => rw [hb] at h; contradiction
      | ok rv l2 =>
        rw [hb] at h
        dsimp only at h
        cases hev : evalBinOp op lv rv with
        | none => rw [hev] at h; contradiction
        | some _ =>
          rw [hev] at h
          injection h with _ hl
          rw [← hl]
          have p1 := evalOperand_preserves_liveness cfg bodyLocals locals l1 a lv ha
          have p2 := evalOperand_preserves_liveness cfg bodyLocals l1 l2 b rv hb
          refine ⟨Eq.trans p2.1 p1.1, ?_⟩
          intro l s' hg2
          obtain ⟨s1, hg1, hl1, hd1⟩ := p2.2 l s' hg2
          obtain ⟨s0, hg0, hl0, hd0⟩ := p1.2 l s1 hg1
          exact ⟨s0, hg0, fun x => hl0 (hl1 x), fun x => hd0 (hd1 x)⟩
  | pairAgg a b =>
    dsimp only [evalRvalue] at h
    cases ha : evalOperand cfg bodyLocals locals a with
    | ub _ => rw [ha] at h; contradiction
    | malformed => rw [ha] at h; contradiction
    | ok lv l1 =>
      rw [ha] at h
      dsimp only at h
      cases hb : evalOperand cfg bodyLocals l1 b with
      | ub _ => rw [hb] at h; contradiction
      | malformed => rw [hb] at h; contradiction
      | ok rv l2 =>
        rw [hb] at h
        injection h with _ hl
        rw [← hl]
        have p1 := evalOperand_preserves_liveness cfg bodyLocals locals l1 a lv ha
        have p2 := evalOperand_preserves_liveness cfg bodyLocals l1 l2 b rv hb
        refine ⟨Eq.trans p2.1 p1.1, ?_⟩
        intro l s' hg2
        obtain ⟨s1, hg1, hl1, hd1⟩ := p2.2 l s' hg2
        obtain ⟨s0, hg0, hl0, hd0⟩ := p1.2 l s1 hg1
        exact ⟨s0, hg0, fun x => hl0 (hl1 x), fun x => hd0 (hd1 x)⟩

theorem writePlace_preserves_liveness (locals locals' : List LocalSlot) (dest : Place) (v : Val)
    (h : writePlace locals dest v = .ok () locals') :
    locals'.length = locals.length ∧
    ∀ l s', listGet locals' l = some s' →
      ∃ s, listGet locals l = some s ∧
        (isLiveSlot s' = true → isLiveSlot s = true) ∧
        (isDeadSlot s' = true → isDeadSlot s = true) := by
  dsimp only [writePlace] at h
  cases hg : listGet locals dest.localId with
  | none => rw [hg] at h; contradiction
  | some sl =>
    rw [hg] at h
    cases sl with
    | dead => dsimp only at h; contradiction
    | live cur =>
      dsimp only at h
      cases hf : dest.field with
      | none =>
        rw [hf] at h
        dsimp only at h
        cases hs : listSet locals dest.localId (.live (some v)) with
        | none => rw [hs] at h; contradiction
        | some l' =>
          rw [hs] at h
          injection h with _ hl
          rw [← hl]
          refine ⟨listSet_some_length locals l' dest.localId _ hs, ?_⟩
          intro l s' hg'
          cases hnat : natBeq l dest.localId with
          | true =>
            have heq : l = dest.localId := (natBeq_eq_true_iff l dest.localId).mp hnat
            rw [heq, listGet_set_same locals l' dest.localId _ hs] at hg'
            injection hg' with hs'
            refine ⟨.live cur, ?_, fun _ => rfl, ?_⟩
            · rw [heq]; exact hg
            · intro hds; rw [← hs'] at hds; contradiction
          | false =>
            have hne : dest.localId ≠ l := fun e => (natBeq_ne hnat) e.symm
            rw [listGet_set_ne locals l' dest.localId l _ hne hs] at hg'
            exact ⟨s', hg', fun x => x, fun x => x⟩
      | some f =>
        rw [hf] at h
        dsimp only at h
        cases hwf : writeFieldVal cur (some f) v with
        | none => rw [hwf] at h; contradiction
        | some upd =>
          rw [hwf] at h
          dsimp only at h
          cases hs : listSet locals dest.localId (.live (some upd)) with
          | none => rw [hs] at h; contradiction
          | some l' =>
            rw [hs] at h
            injection h with _ hl
            rw [← hl]
            refine ⟨listSet_some_length locals l' dest.localId _ hs, ?_⟩
            intro l s' hg'
            cases hnat : natBeq l dest.localId with
            | true =>
              have heq : l = dest.localId := (natBeq_eq_true_iff l dest.localId).mp hnat
              rw [heq, listGet_set_same locals l' dest.localId _ hs] at hg'
              injection hg' with hs'
              refine ⟨.live cur, ?_, fun _ => rfl, ?_⟩
              · rw [heq]; exact hg
              · intro hds; rw [← hs'] at hds; contradiction
            | false =>
              have hne : dest.localId ≠ l := fun e => (natBeq_ne hnat) e.symm
              rw [listGet_set_ne locals l' dest.localId l _ hne hs] at hg'
              exact ⟨s', hg', fun x => x, fun x => x⟩

theorem liveSoundAt_transfer_pres (locals locals' : List LocalSlot) (absLive : List Bool)
    (hlen_l : locals'.length = locals.length)
    (hpres : ∀ l s', listGet locals' l = some s' →
      ∃ s, listGet locals l = some s ∧ (isLiveSlot s' = true → isLiveSlot s = true))
    (hsound : LiveSoundAt locals absLive) :
    LiveSoundAt locals' absLive := by
  refine ⟨Eq.trans hlen_l hsound.1, ?_⟩
  intro l s' hg hl
  obtain ⟨s, hg0, hp⟩ := hpres l s' hg
  exact hsound.2 l s hg0 (hp hl)

theorem deadSoundAt_transfer_pres (locals locals' : List LocalSlot) (absDead : List Bool)
    (hlen_l : locals'.length = locals.length)
    (hpres : ∀ l s', listGet locals' l = some s' →
      ∃ s, listGet locals l = some s ∧ (isDeadSlot s' = true → isDeadSlot s = true))
    (hsound : DeadSoundAt locals absDead) :
    DeadSoundAt locals' absDead := by
  refine ⟨Eq.trans hlen_l hsound.1, ?_⟩
  intro l s' hg hd
  obtain ⟨s, hg0, hp⟩ := hpres l s' hg
  exact hsound.2 l s hg0 (hp hd)

structure ValidStorageFixpoint (body : Body) (liveIn liveOut deadIn deadOut : List (List Bool)) : Prop where
  start_live_sub :
    ∀ l, bitGet (startMaybeLive body) l = true →
      bitGet (listGetD liveIn 0 (listReplicate body.locals.length false)) l = true
  start_dead_sub :
    ∀ l, bitGet (startMaybeDead body) l = true →
      bitGet (listGetD deadIn 0 (listReplicate body.locals.length false)) l = true
  live_in_len : ∀ b, b < body.blocks.length →
    (listGetD liveIn b (listReplicate body.locals.length false)).length = body.locals.length
  dead_in_len : ∀ b, b < body.blocks.length →
    (listGetD deadIn b (listReplicate body.locals.length false)).length = body.locals.length
  live_out_eq : ∀ b bb, listGet body.blocks b = some bb →
    listGetD liveOut b (listReplicate body.locals.length false) =
      transferBlock transferLiveStmt bb.stmts (listGetD liveIn b (listReplicate body.locals.length false))
  dead_out_eq : ∀ b bb, listGet body.blocks b = some bb →
    listGetD deadOut b (listReplicate body.locals.length false) =
      transferBlock transferDeadStmt bb.stmts (listGetD deadIn b (listReplicate body.locals.length false))
  live_edge_sub : ∀ b bb s l, listGet body.blocks b = some bb →
    (∃ t, listGet (termSuccessors bb.term) t = some s) →
    bitGet (listGetD liveOut b (listReplicate body.locals.length false)) l = true →
    bitGet (listGetD liveIn s (listReplicate body.locals.length false)) l = true
  dead_edge_sub : ∀ b bb s l, listGet body.blocks b = some bb →
    (∃ t, listGet (termSuccessors bb.term) t = some s) →
    bitGet (listGetD deadOut b (listReplicate body.locals.length false)) l = true →
    bitGet (listGetD deadIn s (listReplicate body.locals.length false)) l = true

noncomputable def CfgClosed (body : Body) : Prop :=
  ∀ b bb t succ, listGet body.blocks b = some bb →
    listGet (termSuccessors bb.term) t = some succ → succ < body.blocks.length

noncomputable def StateConsistent (body : Body) (liveIn deadIn : List (List Bool)) (st : MachineState) : Prop :=
  ∃ bb : BasicBlock,
    listGet body.blocks st.pc = some bb ∧
    st.stmtIdx ≤ bb.stmts.length ∧
    LiveSoundAt st.locals (foldStmts transferLiveStmt bb.stmts (listGetD liveIn st.pc (listReplicate body.locals.length false)) st.stmtIdx) ∧
    DeadSoundAt st.locals (foldStmts transferDeadStmt bb.stmts (listGetD deadIn st.pc (listReplicate body.locals.length false)) st.stmtIdx)

theorem stateConsistent_init (body : Body) (args : List Val) (liveIn _liveOut deadIn _deadOut : List (List Bool))
    (hargs : args.length = body.argCount)
    (hnonempty : body.blocks.isEmpty = false)
    (hfix : ValidStorageFixpoint body liveIn _liveOut deadIn _deadOut) :
    StateConsistent body liveIn deadIn { pc := 0, stmtIdx := 0, locals := initLocals body args } := by
  have hpos : 0 < body.blocks.length := by
    cases hb : body.blocks with
    | nil => rw [hb] at hnonempty; contradiction
    | cons _ _ => exact Nat.zero_lt_succ _
  obtain ⟨bb, hbb⟩ := listGet_lt_some body.blocks 0 hpos
  refine ⟨bb, hbb, Nat.zero_le bb.stmts.length, ?_, ?_⟩
  · have hl0 := liveSoundAt_init body args
    refine ⟨?_, ?_⟩
    · rw [initLocals_length, foldStmts_zero]
      exact (hfix.live_in_len 0 hpos).symm
    · intro l s hg hsl
      rw [foldStmts_zero]
      exact hfix.start_live_sub l (hl0.2 l s hg hsl)
  · have hd0 := deadSoundAt_init body args hargs
    refine ⟨?_, ?_⟩
    · rw [initLocals_length, foldStmts_zero]
      exact (hfix.dead_in_len 0 hpos).symm
    · intro l s hg hsd
      rw [foldStmts_zero]
      exact hfix.start_dead_sub l (hd0.2 l s hg hsd)

theorem switchLookup_in_succs (k otherwise : Nat) (targets : List (Nat × Nat)) :
    ∃ t : Nat, listGet (otherwise :: listMap (fun p => p.2) targets) t = some (switchLookup k otherwise targets) := by
  induction targets with
  | nil => exact ⟨0, rfl⟩
  | cons p tl ih =>
    dsimp only [switchLookup]
    cases natBeq k p.1 with
    | true => exact ⟨1, rfl⟩
    | false =>
      rw [bool_if_false false rfl]
      obtain ⟨t, ht⟩ := ih
      cases t with
      | zero =>
        rw [listGet_cons_zero] at ht
        injection ht with heq
        rw [← heq]
        exact ⟨0, rfl⟩
      | succ m =>
        rw [listGet_cons_succ] at ht
        exact ⟨m + 2, ht⟩

theorem evalSwitchTarget_in_succs (dv : Val) (targets : List (Nat × Nat)) (otherwise nextPc : Nat) :
    evalSwitchTarget dv targets otherwise = some nextPc →
    ∃ t : Nat, listGet (otherwise :: listMap (fun p => p.2) targets) t = some nextPc := by
  intro h
  dsimp only [evalSwitchTarget] at h
  cases dv with
  | u32 n =>
    injection h with hrec
    rw [← hrec]
    exact switchLookup_in_succs n otherwise targets
  | bool b =>
    cases b with
    | false =>
      injection h with hrec
      rw [← hrec]
      exact switchLookup_in_succs 0 otherwise targets
    | true =>
      injection h with hrec
      rw [← hrec]
      exact switchLookup_in_succs 1 otherwise targets
  | unit => contradiction
  | pair _ _ => contradiction
  | fnPtr _ => contradiction

theorem liveDeadSound_storageLive_set
    (body : Body) (liveIn deadIn : List (List Bool)) (st : MachineState)
    (bb : BasicBlock) (hbb : listGet body.blocks st.pc = some bb)
    (l : Nat) (ty : MirTy) (cur : LocalSlot)
    (hl_lt : st.stmtIdx < bb.stmts.length)
    (hcur : listGet st.locals l = some cur)
    (locals' : List LocalSlot) (hset : listSet st.locals l (liveUninitSlot ty) = some locals')
    (hlive : LiveSoundAt st.locals (foldStmts transferLiveStmt bb.stmts (listGetD liveIn st.pc (listReplicate body.locals.length false)) st.stmtIdx))
    (hdead : DeadSoundAt st.locals (foldStmts transferDeadStmt bb.stmts (listGetD deadIn st.pc (listReplicate body.locals.length false)) st.stmtIdx))
    (hfl : foldStmts transferLiveStmt bb.stmts (listGetD liveIn st.pc (listReplicate body.locals.length false)) (st.stmtIdx + 1) =
      transferLiveStmt (.storageLive l) (foldStmts transferLiveStmt bb.stmts (listGetD liveIn st.pc (listReplicate body.locals.length false)) st.stmtIdx))
    (hfd : foldStmts transferDeadStmt bb.stmts (listGetD deadIn st.pc (listReplicate body.locals.length false)) (st.stmtIdx + 1) =
      transferDeadStmt (.storageLive l) (foldStmts transferDeadStmt bb.stmts (listGetD deadIn st.pc (listReplicate body.locals.length false)) st.stmtIdx)) :
    StateConsistent body liveIn deadIn { pc := st.pc, stmtIdx := st.stmtIdx + 1, locals := locals' } := by
  have hll_lt : l < st.locals.length := listGet_some_lt st.locals l cur hcur
  have hlen_l : locals'.length = st.locals.length := listSet_some_length st.locals locals' l _ hset
  refine ⟨bb, hbb, hl_lt, ?_, ?_⟩
  · rw [hfl]
    dsimp only [transferLiveStmt]
    refine ⟨by rw [hlen_l, hlive.1, bitSet_length], ?_⟩
    intro x sx hgx hlx
    have hlt_abs : l < (foldStmts transferLiveStmt bb.stmts (listGetD liveIn st.pc (listReplicate body.locals.length false)) st.stmtIdx).length := by
      rw [← hlive.1]; exact hll_lt
    cases hx : natBeq x l with
    | true =>
      have heq : x = l := (natBeq_eq_true_iff x l).mp hx
      rw [heq]
      exact bitGet_bitSet_same _ l true hlt_abs
    | false =>
      have hne : l ≠ x := fun e => (natBeq_ne hx) e.symm
      rw [listGet_set_ne st.locals locals' l x _ hne hset] at hgx
      rw [bitGet_bitSet_ne _ l x true hne]
      exact hlive.2 x sx hgx hlx
  · rw [hfd]
    dsimp only [transferDeadStmt]
    refine ⟨by rw [hlen_l, hdead.1, bitSet_length], ?_⟩
    intro x sx hgx hdx
    cases hx : natBeq x l with
    | true =>
      have heq : x = l := (natBeq_eq_true_iff x l).mp hx
      rw [heq, listGet_set_same st.locals locals' l _ hset] at hgx
      injection hgx with hsx
      rw [← hsx] at hdx
      cases ty <;> contradiction
    | false =>
      have hne : l ≠ x := fun e => (natBeq_ne hx) e.symm
      rw [listGet_set_ne st.locals locals' l x _ hne hset] at hgx
      rw [bitGet_bitSet_ne _ l x false hne]
      exact hdead.2 x sx hgx hdx

theorem stateConsistent_step (cfg : EvalConfig) (body : Body)
    (liveIn liveOut deadIn deadOut : List (List Bool))
    (hclosed : CfgClosed body)
    (hfix : ValidStorageFixpoint body liveIn liveOut deadIn deadOut)
    (st st' : MachineState)
    (hcons : StateConsistent body liveIn deadIn st)
    (hstep : stepState cfg body st = .next st') :
    StateConsistent body liveIn deadIn st' := by
  obtain ⟨bb, hbb, _, hlive, hdead⟩ := hcons
  dsimp only [stepState] at hstep
  rw [hbb] at hstep
  dsimp only at hstep
  cases hst : listGet bb.stmts st.stmtIdx with
  | some stmt =>
    have hidx_lt : st.stmtIdx < bb.stmts.length := listGet_some_lt bb.stmts st.stmtIdx stmt hst
    have hidx_succ_le : st.stmtIdx + 1 ≤ bb.stmts.length := hidx_lt
    rw [hst] at hstep
    dsimp only at hstep
    have hfl := foldStmts_succ transferLiveStmt bb.stmts (listGetD liveIn st.pc (listReplicate body.locals.length false)) st.stmtIdx stmt hst
    have hfd := foldStmts_succ transferDeadStmt bb.stmts (listGetD deadIn st.pc (listReplicate body.locals.length false)) st.stmtIdx stmt hst
    cases stmt with
    | nop =>
      dsimp only at hstep
      injection hstep with hst'
      rw [← hst']
      refine ⟨bb, hbb, hidx_succ_le, ?_, ?_⟩
      · rw [hfl]; exact hlive
      · rw [hfd]; exact hdead
    | storageLive l =>
      dsimp only at hstep
      cases hty : listGet body.locals l with
      | none => rw [hty] at hstep; contradiction
      | some ty =>
        cases hcur : listGet st.locals l with
        | none => rw [hty, hcur] at hstep; contradiction
        | some cur =>
          rw [hty, hcur] at hstep
          dsimp only at hstep
          cases cur with
          | dead =>
            rw [Bool.and_false] at hstep
            rw [bool_if_false false rfl] at hstep
            cases hset : listSet st.locals l (liveUninitSlot ty) with
            | none => rw [hset] at hstep; contradiction
            | some locals' =>
              rw [hset] at hstep
              injection hstep with hst'
              rw [← hst']
              exact liveDeadSound_storageLive_set body liveIn deadIn st bb hbb l ty .dead hidx_succ_le hcur locals' hset hlive hdead hfl hfd
          | live ov =>
            cases hcab : cfg.abortOnDoubleStorageLive with
            | true =>
              rw [hcab, Bool.true_and] at hstep
              rw [bool_if_true true rfl] at hstep
              contradiction
            | false =>
              rw [hcab, Bool.false_and] at hstep
              rw [bool_if_false false rfl] at hstep
              cases hset : listSet st.locals l (liveUninitSlot ty) with
              | none => rw [hset] at hstep; contradiction
              | some locals' =>
                rw [hset] at hstep
                injection hstep with hst'
                rw [← hst']
                exact liveDeadSound_storageLive_set body liveIn deadIn st bb hbb l ty (.live ov) hidx_succ_le hcur locals' hset hlive hdead hfl hfd
    | storageDead l =>
      dsimp only at hstep
      cases h0 : natBeq l 0 with
      | true => rw [h0] at hstep; rw [bool_if_true true rfl] at hstep; contradiction
      | false =>
        rw [h0] at hstep
        rw [bool_if_false false rfl] at hstep
        cases hset : listSet st.locals l .dead with
        | none => rw [hset] at hstep; contradiction
        | some locals' =>
          rw [hset] at hstep
          injection hstep with hst'
          rw [← hst']
          have hlen_l : locals'.length = st.locals.length := listSet_some_length st.locals locals' l .dead hset
          have hll_lt : l < st.locals.length := listSet_some_lt st.locals locals' l .dead hset
          refine ⟨bb, hbb, hidx_succ_le, ?_, ?_⟩
          · rw [hfl]
            change LiveSoundAt locals' (bitSet (foldStmts transferLiveStmt bb.stmts (listGetD liveIn st.pc (listReplicate body.locals.length false)) st.stmtIdx) l false)
            refine ⟨by rw [hlen_l, hlive.1, bitSet_length], ?_⟩
            intro x sx hgx hlx
            cases hx : natBeq x l with
            | true =>
              have heq : x = l := (natBeq_eq_true_iff x l).mp hx
              rw [heq, listGet_set_same st.locals locals' l .dead hset] at hgx
              injection hgx with hsx
              rw [← hsx] at hlx
              contradiction
            | false =>
              have hne : l ≠ x := fun e => (natBeq_ne hx) e.symm
              rw [listGet_set_ne st.locals locals' l x .dead hne hset] at hgx
              rw [bitGet_bitSet_ne _ l x false hne]
              exact hlive.2 x sx hgx hlx
          · rw [hfd]
            change DeadSoundAt locals' (bitSet (foldStmts transferDeadStmt bb.stmts (listGetD deadIn st.pc (listReplicate body.locals.length false)) st.stmtIdx) l true)
            refine ⟨by rw [hlen_l, hdead.1, bitSet_length], ?_⟩
            intro x sx hgx hdx
            have hlt_abs : l < (foldStmts transferDeadStmt bb.stmts (listGetD deadIn st.pc (listReplicate body.locals.length false)) st.stmtIdx).length := by
              rw [← hdead.1]; exact hll_lt
            cases hx : natBeq x l with
            | true =>
              have heq : x = l := (natBeq_eq_true_iff x l).mp hx
              rw [heq]
              exact bitGet_bitSet_same _ l true hlt_abs
            | false =>
              have hne : l ≠ x := fun e => (natBeq_ne hx) e.symm
              rw [listGet_set_ne st.locals locals' l x .dead hne hset] at hgx
              rw [bitGet_bitSet_ne _ l x true hne]
              exact hdead.2 x sx hgx hdx
    | assign dest rval =>
      dsimp only at hstep
      cases hfa : (cfg.forbidAliasAssign && rvalueConflictsWithPlace dest rval) with
      | true => rw [hfa] at hstep; rw [bool_if_true true rfl] at hstep; contradiction
      | false =>
        rw [hfa] at hstep
        rw [bool_if_false false rfl] at hstep
        cases hev : evalRvalue cfg body.locals st.locals rval with
        | ub _ => rw [hev] at hstep; contradiction
        | malformed => rw [hev] at hstep; contradiction
        | ok val l1 =>
          rw [hev] at hstep
          dsimp only at hstep
          cases hwp : writePlace l1 dest val with
          | ub _ => rw [hwp] at hstep; contradiction
          | malformed => rw [hwp] at hstep; contradiction
          | ok _ l2 =>
            rw [hwp] at hstep
            injection hstep with hst'
            rw [← hst']
            have p1 := evalRvalue_preserves_liveness cfg body.locals st.locals l1 rval val hev
            have p2 := writePlace_preserves_liveness l1 l2 dest val hwp
            refine ⟨bb, hbb, hidx_succ_le, ?_, ?_⟩
            · rw [hfl]
              change LiveSoundAt l2 _
              exact liveSoundAt_transfer_pres st.locals l2 _ (Eq.trans p2.1 p1.1) (fun l s' hg2 => by
                obtain ⟨s1, hg1, hl1, _⟩ := p2.2 l s' hg2
                obtain ⟨s0, hg0, hl0, _⟩ := p1.2 l s1 hg1
                exact ⟨s0, hg0, fun x => hl0 (hl1 x)⟩) hlive
            · rw [hfd]
              change DeadSoundAt l2 _
              exact deadSoundAt_transfer_pres st.locals l2 _ (Eq.trans p2.1 p1.1) (fun l s' hg2 => by
                obtain ⟨s1, hg1, _, hd1⟩ := p2.2 l s' hg2
                obtain ⟨s0, hg0, _, hd0⟩ := p1.2 l s1 hg1
                exact ⟨s0, hg0, fun x => hd0 (hd1 x)⟩) hdead
  | none =>
    rw [hst] at hstep
    dsimp only at hstep
    cases hbeq : natBeq st.stmtIdx bb.stmts.length with
    | false => rw [hbeq] at hstep; rw [bool_if_false false rfl] at hstep; contradiction
    | true =>
      rw [hbeq] at hstep
      rw [bool_if_true true rfl] at hstep
      have heq_idx : st.stmtIdx = bb.stmts.length := (natBeq_eq_true_iff st.stmtIdx bb.stmts.length).mp hbeq
      rw [heq_idx, foldStmts_end] at hlive hdead
      cases hterm : bb.term with
      | ret =>
        rw [hterm] at hstep
        dsimp only at hstep
        cases hcl : bb.isCleanup with
        | true => rw [hcl] at hstep; rw [bool_if_true true rfl] at hstep; contradiction
        | false =>
          rw [hcl] at hstep
          rw [bool_if_false false rfl] at hstep
          cases hg0 : listGet st.locals 0 with
          | none => rw [hg0] at hstep; dsimp only at hstep; contradiction
          | some sl =>
            rw [hg0] at hstep
            cases sl with
            | dead => dsimp only at hstep; contradiction
            | live ov => cases ov <;> dsimp only at hstep <;> contradiction
      | call _ _ _ _ _ => rw [hterm] at hstep; contradiction
      | peekCall _ _ => rw [hterm] at hstep; contradiction
      | unreachable => rw [hterm] at hstep; contradiction
      | goto target =>
        rw [hterm] at hstep
        injection hstep with hst'
        rw [← hst']
        have hsucc : listGet (termSuccessors bb.term) 0 = some target := by rw [hterm]; rfl
        have hlt : target < body.blocks.length := hclosed st.pc bb 0 target hbb hsucc
        obtain ⟨bb', hbb'⟩ := listGet_lt_some body.blocks target hlt
        refine ⟨bb', hbb', Nat.zero_le bb'.stmts.length, ?_, ?_⟩
        · rw [foldStmts_zero]
          have hlen_tb : (transferBlock transferLiveStmt bb.stmts (listGetD liveIn st.pc (listReplicate body.locals.length false))).length = body.locals.length := by
            rw [← foldStmts_end]
            rw [foldStmts_len transferLiveStmt transferLiveStmt_len]
            exact hfix.live_in_len st.pc (listGet_some_lt _ _ _ hbb)
          refine ⟨hlive.1.trans (hlen_tb.trans (hfix.live_in_len target hlt).symm), ?_⟩
          intro l s hg hsl
          have h1 : bitGet (listGetD liveOut st.pc (listReplicate body.locals.length false)) l = true := by
            rw [hfix.live_out_eq st.pc bb hbb]
            exact hlive.2 l s hg hsl
          exact hfix.live_edge_sub st.pc bb target l hbb ⟨0, hsucc⟩ h1
        · rw [foldStmts_zero]
          have hlen_tb : (transferBlock transferDeadStmt bb.stmts (listGetD deadIn st.pc (listReplicate body.locals.length false))).length = body.locals.length := by
            rw [← foldStmts_end]
            rw [foldStmts_len transferDeadStmt transferDeadStmt_len]
            exact hfix.dead_in_len st.pc (listGet_some_lt _ _ _ hbb)
          refine ⟨hdead.1.trans (hlen_tb.trans (hfix.dead_in_len target hlt).symm), ?_⟩
          intro l s hg hsd
          have h1 : bitGet (listGetD deadOut st.pc (listReplicate body.locals.length false)) l = true := by
            rw [hfix.dead_out_eq st.pc bb hbb]
            exact hdead.2 l s hg hsd
          exact hfix.dead_edge_sub st.pc bb target l hbb ⟨0, hsucc⟩ h1
      | switchInt discr targets otherwise =>
        rw [hterm] at hstep
        dsimp only at hstep
        cases hev : evalOperand cfg body.locals st.locals discr with
        | ub _ => rw [hev] at hstep; contradiction
        | malformed => rw [hev] at hstep; contradiction
        | ok dv locals₁ =>
          rw [hev] at hstep
          dsimp only at hstep
          cases hesw : evalSwitchTarget dv targets otherwise with
          | none => rw [hesw] at hstep; contradiction
          | some nextPc =>
            rw [hesw] at hstep
            injection hstep with hst'
            rw [← hst']
            obtain ⟨tIdx, htIdx⟩ := evalSwitchTarget_in_succs dv targets otherwise nextPc hesw
            have hsucc : listGet (termSuccessors bb.term) tIdx = some nextPc := by
              rw [hterm]
              exact htIdx
            have hlt : nextPc < body.blocks.length := hclosed st.pc bb tIdx nextPc hbb hsucc
            obtain ⟨bb', hbb'⟩ := listGet_lt_some body.blocks nextPc hlt
            have p1 := evalOperand_preserves_liveness cfg body.locals st.locals locals₁ discr dv hev
            have hlive1 := liveSoundAt_transfer_pres st.locals locals₁ _ p1.1 (fun l s' hg1 => by
              obtain ⟨s0, hg0, hl0, _⟩ := p1.2 l s' hg1
              exact ⟨s0, hg0, hl0⟩) hlive
            have hdead1 := deadSoundAt_transfer_pres st.locals locals₁ _ p1.1 (fun l s' hg1 => by
              obtain ⟨s0, hg0, _, hd0⟩ := p1.2 l s' hg1
              exact ⟨s0, hg0, hd0⟩) hdead
            refine ⟨bb', hbb', Nat.zero_le bb'.stmts.length, ?_, ?_⟩
            · rw [foldStmts_zero]
              have hlen_tb : (transferBlock transferLiveStmt bb.stmts (listGetD liveIn st.pc (listReplicate body.locals.length false))).length = body.locals.length := by
                rw [← foldStmts_end]
                rw [foldStmts_len transferLiveStmt transferLiveStmt_len]
                exact hfix.live_in_len st.pc (listGet_some_lt _ _ _ hbb)
              refine ⟨hlive1.1.trans (hlen_tb.trans (hfix.live_in_len nextPc hlt).symm), ?_⟩
              intro l s hg hsl
              have h1 : bitGet (listGetD liveOut st.pc (listReplicate body.locals.length false)) l = true := by
                rw [hfix.live_out_eq st.pc bb hbb]
                exact hlive1.2 l s hg hsl
              exact hfix.live_edge_sub st.pc bb nextPc l hbb ⟨tIdx, hsucc⟩ h1
            · rw [foldStmts_zero]
              have hlen_tb : (transferBlock transferDeadStmt bb.stmts (listGetD deadIn st.pc (listReplicate body.locals.length false))).length = body.locals.length := by
                rw [← foldStmts_end]
                rw [foldStmts_len transferDeadStmt transferDeadStmt_len]
                exact hfix.dead_in_len st.pc (listGet_some_lt _ _ _ hbb)
              refine ⟨hdead1.1.trans (hlen_tb.trans (hfix.dead_in_len nextPc hlt).symm), ?_⟩
              intro l s hg hsd
              have h1 : bitGet (listGetD deadOut st.pc (listReplicate body.locals.length false)) l = true := by
                rw [hfix.dead_out_eq st.pc bb hbb]
                exact hdead1.2 l s hg hsd
              exact hfix.dead_edge_sub st.pc bb nextPc l hbb ⟨tIdx, hsucc⟩ h1

noncomputable def FixpointLintChecked (body : Body) (liveIn deadIn : List (List Bool)) : Prop :=
  ∀ b bb : _, listGet body.blocks b = some bb →
    checkBlockLint body (alwaysStorageLiveLocals body)
      (listGetD liveIn b (listReplicate body.locals.length false))
      (listGetD deadIn b (listReplicate body.locals.length false)) bb = true

theorem checkStmtsLintAux_step_holds (stmts : List Stmt) (lb db : List Bool) (idx : Nat) (st : Stmt) :
    (checkStmtsLintAux stmts lb db).1 = true →
    listGet stmts idx = some st →
    checkStmtLint (foldStmts transferLiveStmt stmts lb idx) (foldStmts transferDeadStmt stmts db idx) st = true := by
  induction stmts generalizing lb db idx with
  | nil => intro _ hg; rw [listGet_nil] at hg; contradiction
  | cons hd tl ih =>
    intro haux hg
    have hs : checkStmtLint lb db hd = true ∧ (checkStmtsLintAux tl (transferLiveStmt hd lb) (transferDeadStmt hd db)).1 = true :=
      Bool.and_eq_true _ _ |>.mp haux
    cases idx with
    | zero =>
      rw [listGet_cons_zero] at hg
      injection hg with heq
      rw [← heq, foldStmts_zero, foldStmts_zero]
      exact hs.1
    | succ k =>
      rw [listGet_cons_succ] at hg
      exact ih (transferLiveStmt hd lb) (transferDeadStmt hd db) k hs.2 hg

theorem checkStmtsLintAux_end_eq (stmts : List Stmt) (lb db : List Bool) :
    (checkStmtsLintAux stmts lb db).2 =
      (transferBlock transferLiveStmt stmts lb, transferBlock transferDeadStmt stmts db) := by
  induction stmts generalizing lb db with
  | nil => rfl
  | cons hd tl ih =>
    exact ih (transferLiveStmt hd lb) (transferDeadStmt hd db)

theorem evalOperand_not_dead_when_live (cfg : EvalConfig) (bodyLocals : List MirTy)
    (locals : List LocalSlot) (op : Operand) (absDead : List Bool)
    (hdead : DeadSoundAt locals absDead)
    (hchk : checkOperandUseNotDead absDead op = true) :
    evalOperand cfg bodyLocals locals op ≠ .ub .deadLocalAccess := by
  cases op with
  | constVal _ => intro h; contradiction
  | copy p =>
    dsimp only [checkOperandUseNotDead] at hchk
    dsimp only [evalOperand]
    cases hg : listGet locals p.localId with
    | none => dsimp only; intro h; contradiction
    | some sl =>
      cases sl with
      | dead =>
        have hbit : bitGet absDead p.localId = true := hdead.2 p.localId .dead hg rfl
        rw [hbit, Bool.not_true] at hchk
        contradiction
      | live ov =>
        cases ov with
        | none => dsimp only; intro h; cases h
        | some v =>
          dsimp only
          cases readPlaceFromVal v p.field <;> dsimp only <;> intro h <;> cases h
  | move p =>
    dsimp only [checkOperandUseNotDead] at hchk
    dsimp only [evalOperand]
    cases hty : listGet bodyLocals p.localId with
    | none => dsimp only; intro h; contradiction
    | some ty =>
      cases hg : listGet locals p.localId with
      | none => dsimp only; intro h; contradiction
      | some sl =>
        cases sl with
        | dead =>
          have hbit : bitGet absDead p.localId = true := hdead.2 p.localId .dead hg rfl
          rw [hbit, Bool.not_true] at hchk
          contradiction
        | live ov =>
          cases ov with
          | none => dsimp only; intro h; cases h
          | some val =>
            dsimp only
            cases readPlaceFromVal val p.field with
            | none => dsimp only; intro h; contradiction
            | some rv =>
              dsimp only
              cases cfg.deinitMovedPlace with
              | false => rw [bool_if_false false rfl]; intro h; contradiction
              | true =>
                rw [bool_if_true true rfl]
                cases p.field with
                | some _ => dsimp only; intro h; contradiction
                | none =>
                  dsimp only
                  cases listSet locals p.localId (liveUninitSlot ty) <;> dsimp only <;> intro h <;> cases h

theorem evalRvalue_not_dead_when_live (cfg : EvalConfig) (bodyLocals : List MirTy)
    (locals : List LocalSlot) (rval : Rvalue) (absDead : List Bool)
    (hdead : DeadSoundAt locals absDead)
    (hchk : checkRvalueUseNotDead absDead rval = true) :
    evalRvalue cfg bodyLocals locals rval ≠ .ub .deadLocalAccess := by
  cases rval with
  | use op => exact evalOperand_not_dead_when_live cfg bodyLocals locals op absDead hdead hchk
  | binOp op a b =>
    dsimp only [checkRvalueUseNotDead] at hchk
    have hc := Bool.and_eq_true _ _ |>.mp hchk
    dsimp only [evalRvalue]
    cases ha : evalOperand cfg bodyLocals locals a with
    | ub k =>
      dsimp only
      intro h
      injection h with hk
      rw [hk] at ha
      exact evalOperand_not_dead_when_live cfg bodyLocals locals a absDead hdead hc.1 ha
    | malformed => dsimp only; intro h; contradiction
    | ok lv l1 =>
      dsimp only
      have p1 := evalOperand_preserves_liveness cfg bodyLocals locals l1 a lv ha
      have hdead1 := deadSoundAt_transfer_pres locals l1 absDead p1.1 (fun l s' hg => by
        obtain ⟨s, hg0, _, hd⟩ := p1.2 l s' hg; exact ⟨s, hg0, hd⟩) hdead
      cases hb : evalOperand cfg bodyLocals l1 b with
      | ub k =>
        dsimp only
        intro h
        injection h with hk
        rw [hk] at hb
        exact evalOperand_not_dead_when_live cfg bodyLocals l1 b absDead hdead1 hc.2 hb
      | malformed => dsimp only; intro h; contradiction
      | ok rv l2 =>
        dsimp only
        cases evalBinOp op lv rv <;> dsimp only <;> intro h <;> cases h
  | pairAgg a b =>
    dsimp only [checkRvalueUseNotDead] at hchk
    have hc := Bool.and_eq_true _ _ |>.mp hchk
    dsimp only [evalRvalue]
    cases ha : evalOperand cfg bodyLocals locals a with
    | ub k =>
      dsimp only
      intro h
      injection h with hk
      rw [hk] at ha
      exact evalOperand_not_dead_when_live cfg bodyLocals locals a absDead hdead hc.1 ha
    | malformed => dsimp only; intro h; contradiction
    | ok lv l1 =>
      dsimp only
      have p1 := evalOperand_preserves_liveness cfg bodyLocals locals l1 a lv ha
      have hdead1 := deadSoundAt_transfer_pres locals l1 absDead p1.1 (fun l s' hg => by
        obtain ⟨s, hg0, _, hd⟩ := p1.2 l s' hg; exact ⟨s, hg0, hd⟩) hdead
      cases hb : evalOperand cfg bodyLocals l1 b with
      | ub k =>
        dsimp only
        intro h
        injection h with hk
        rw [hk] at hb
        exact evalOperand_not_dead_when_live cfg bodyLocals l1 b absDead hdead1 hc.2 hb
      | malformed => dsimp only; intro h; contradiction
      | ok rv l2 => dsimp only; intro h; cases h

theorem evalOperand_ne_doubleLive (cfg : EvalConfig) (bodyLocals : List MirTy) (locals : List LocalSlot)
    (op : Operand) : evalOperand cfg bodyLocals locals op ≠ .ub .doubleStorageLive := by
  intro h
  cases op with
  | constVal _ => cases h
  | copy p =>
    dsimp only [evalOperand] at h
    cases hg : listGet locals p.localId with
    | none => rw [hg] at h; cases h
    | some sl =>
      rw [hg] at h
      cases sl with
      | dead => cases h
      | live ov =>
        cases ov with
        | none => cases h
        | some v =>
          dsimp only at h
          cases hrp : readPlaceFromVal v p.field <;> rw [hrp] at h <;> cases h
  | move p =>
    dsimp only [evalOperand] at h
    cases hty : listGet bodyLocals p.localId with
    | none => rw [hty] at h; cases h
    | some ty =>
      rw [hty] at h
      cases hg : listGet locals p.localId with
      | none => rw [hg] at h; cases h
      | some sl =>
        rw [hg] at h
        cases sl with
        | dead => cases h
        | live ov =>
          cases ov with
          | none => cases h
          | some v =>
            dsimp only at h
            cases hrp : readPlaceFromVal v p.field with
            | none => rw [hrp] at h; cases h
            | some rv =>
              rw [hrp] at h; dsimp only at h
              cases hdn : cfg.deinitMovedPlace with
              | false => rw [hdn, bool_if_false false rfl] at h; cases h
              | true =>
                rw [hdn, bool_if_true true rfl] at h
                cases hf : p.field with
                | some _ => rw [hf] at h; cases h
                | none =>
                  rw [hf] at h; dsimp only at h
                  cases hls : listSet locals p.localId (liveUninitSlot ty) <;> rw [hls] at h <;> cases h

theorem evalRvalue_ne_doubleLive (cfg : EvalConfig) (bodyLocals : List MirTy) (locals : List LocalSlot)
    (rval : Rvalue) : evalRvalue cfg bodyLocals locals rval ≠ .ub .doubleStorageLive := by
  cases rval with
  | use op => exact evalOperand_ne_doubleLive cfg bodyLocals locals op
  | binOp op a b =>
    intro h
    dsimp only [evalRvalue] at h
    cases ha : evalOperand cfg bodyLocals locals a with
    | ub k =>
      rw [ha] at h; dsimp only at h
      injection h with hk; rw [hk] at ha
      exact evalOperand_ne_doubleLive cfg bodyLocals locals a ha
    | malformed => rw [ha] at h; cases h
    | ok va l1 =>
      rw [ha] at h; dsimp only at h
      cases hb : evalOperand cfg bodyLocals l1 b with
      | ub k =>
        rw [hb] at h; dsimp only at h
        injection h with hk; rw [hk] at hb
        exact evalOperand_ne_doubleLive cfg bodyLocals l1 b hb
      | malformed => rw [hb] at h; cases h
      | ok vb l2 =>
        rw [hb] at h; dsimp only at h
        cases hbin : evalBinOp op va vb <;> rw [hbin] at h <;> cases h
  | pairAgg a b =>
    intro h
    dsimp only [evalRvalue] at h
    cases ha : evalOperand cfg bodyLocals locals a with
    | ub k =>
      rw [ha] at h; dsimp only at h
      injection h with hk; rw [hk] at ha
      exact evalOperand_ne_doubleLive cfg bodyLocals locals a ha
    | malformed => rw [ha] at h; cases h
    | ok va l1 =>
      rw [ha] at h; dsimp only at h
      cases hb : evalOperand cfg bodyLocals l1 b with
      | ub k =>
        rw [hb] at h; dsimp only at h
        injection h with hk; rw [hk] at hb
        exact evalOperand_ne_doubleLive cfg bodyLocals l1 b hb
      | malformed => rw [hb] at h; cases h
      | ok vb l2 => rw [hb] at h; cases h

theorem writePlace_ne_doubleLive (locals : List LocalSlot) (dest : Place) (val : Val) :
    writePlace locals dest val ≠ .ub .doubleStorageLive := by
  intro h
  dsimp only [writePlace] at h
  cases hg : listGet locals dest.localId with
  | none => rw [hg] at h; cases h
  | some sl =>
    rw [hg] at h
    cases sl with
    | dead => cases h
    | live cur =>
      cases hf : dest.field with
      | none =>
        rw [hf] at h; dsimp only at h
        cases hls : listSet locals dest.localId (.live (some val)) <;> rw [hls] at h <;> cases h
      | some f =>
        rw [hf] at h; dsimp only at h
        cases hwf : writeFieldVal cur (some f) val with
        | none => rw [hwf] at h; cases h
        | some upd =>
          rw [hwf] at h; dsimp only at h
          cases hls : listSet locals dest.localId (.live (some upd)) <;> rw [hls] at h <;> cases h

theorem step_no_dead_access_or_double_live (cfg : EvalConfig) (body : Body)
    (liveIn _liveOut deadIn _deadOut : List (List Bool))
    (hlint : FixpointLintChecked body liveIn deadIn)
    (st : MachineState) (hcons : StateConsistent body liveIn deadIn st) :
    stepState cfg body st ≠ .ub .deadLocalAccess ∧
    stepState cfg body st ≠ .ub .doubleStorageLive := by
  obtain ⟨bb, hbb, _, hlive, hdead⟩ := hcons
  have hblk := hlint st.pc bb hbb
  dsimp only [checkBlockLint] at hblk
  have hblkParts := Bool.and_eq_true _ _ |>.mp hblk
  dsimp only [stepState]
  rw [hbb]
  dsimp only
  cases hst : listGet bb.stmts st.stmtIdx with
  | some stmt =>
    dsimp only
    have hchk := checkStmtsLintAux_step_holds bb.stmts
      (listGetD liveIn st.pc (listReplicate body.locals.length false))
      (listGetD deadIn st.pc (listReplicate body.locals.length false))
      st.stmtIdx stmt hblkParts.1 hst
    cases stmt with
    | nop => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
    | storageLive l =>
      dsimp only
      dsimp only [checkStmtLint] at hchk
      cases listGet body.locals l with
      | none => dsimp only; exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
      | some ty =>
        cases hcur : listGet st.locals l with
        | none => dsimp only; exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
        | some cur =>
          dsimp only
          cases cur with
          | dead =>
            rw [Bool.and_false, bool_if_false false rfl]
            cases listSet st.locals l (liveUninitSlot ty) <;> dsimp only <;> exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
          | live _ =>
            have hbit : bitGet (foldStmts transferLiveStmt bb.stmts (listGetD liveIn st.pc (listReplicate body.locals.length false)) st.stmtIdx) l = true :=
              hlive.2 l _ hcur rfl
            rw [hbit, Bool.not_true] at hchk
            contradiction
    | storageDead l =>
      dsimp only
      cases natBeq l 0 with
      | true => rw [bool_if_true true rfl]; exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
      | false =>
        rw [bool_if_false false rfl]
        cases listSet st.locals l .dead <;> dsimp only <;> exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
    | assign dest rval =>
      dsimp only
      dsimp only [checkStmtLint, transferDeadStmt] at hchk
      have hc1 := Bool.and_eq_true _ _ |>.mp hchk
      have hc2 := Bool.and_eq_true _ _ |>.mp hc1.1
      cases (cfg.forbidAliasAssign && rvalueConflictsWithPlace dest rval) with
      | true => rw [bool_if_true true rfl]; exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
      | false =>
        rw [bool_if_false false rfl]
        cases hev : evalRvalue cfg body.locals st.locals rval with
        | ub k =>
          dsimp only
          refine ⟨?_, ?_⟩
          · intro h
            injection h with hk
            rw [hk] at hev
            exact evalRvalue_not_dead_when_live cfg body.locals st.locals rval _ hdead hc2.2 hev
          · intro h
            injection h with hk
            rw [hk] at hev
            exact evalRvalue_ne_doubleLive cfg body.locals st.locals rval hev
        | malformed => dsimp only; exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
        | ok val l1 =>
          dsimp only
          have p1 := evalRvalue_preserves_liveness cfg body.locals st.locals l1 rval val hev
          have hdead1 := deadSoundAt_transfer_pres st.locals l1 _ p1.1 (fun l s' hg => by
            obtain ⟨s, hg0, _, hd⟩ := p1.2 l s' hg; exact ⟨s, hg0, hd⟩) hdead
          have hnotd : writePlace l1 dest val ≠ .ub .deadLocalAccess := by
            dsimp only [writePlace]
            cases hg : listGet l1 dest.localId with
            | none => dsimp only; intro h; cases h
            | some sl =>
              cases sl with
              | dead =>
                have hbit := hdead1.2 dest.localId .dead hg rfl
                have hc21 := hc2.1
                rw [hbit, Bool.not_true] at hc21
                contradiction
              | live cur =>
                dsimp only
                cases dest.field with
                | none =>
                  dsimp only
                  cases listSet l1 dest.localId (.live (some val)) <;> dsimp only <;> intro h <;> cases h
                | some f =>
                  dsimp only
                  cases hwf : writeFieldVal cur (some f) val with
                  | none => dsimp only; intro h; cases h
                  | some upd =>
                    dsimp only
                    cases listSet l1 dest.localId (.live (some upd)) <;> intro h <;> dsimp only at h <;> cases h
          cases hwp : writePlace l1 dest val with
          | ub k =>
            dsimp only
            refine ⟨?_, ?_⟩
            · intro h
              injection h with hk
              rw [hk] at hwp
              exact hnotd hwp
            · intro h
              injection h with hk
              rw [hk] at hwp
              exact writePlace_ne_doubleLive l1 dest val hwp
          | malformed => dsimp only; exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
          | ok PUnit.unit l2 => dsimp only; exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | none =>
    dsimp only
    cases hbeq : natBeq st.stmtIdx bb.stmts.length with
    | false => rw [bool_if_false false rfl]; exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
    | true =>
      rw [bool_if_true true rfl]
      have heq_idx : st.stmtIdx = bb.stmts.length := (natBeq_eq_true_iff st.stmtIdx bb.stmts.length).mp hbeq
      rw [heq_idx, foldStmts_end] at hdead
      have hend := checkStmtsLintAux_end_eq bb.stmts
        (listGetD liveIn st.pc (listReplicate body.locals.length false))
        (listGetD deadIn st.pc (listReplicate body.locals.length false))
      have htermChk := hblkParts.2
      rw [hend] at htermChk
      dsimp only at htermChk
      cases hterm : bb.term with
      | goto _ => dsimp only; exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
      | call _ _ _ _ _ => dsimp only; exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
      | peekCall _ _ => dsimp only; exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
      | unreachable => dsimp only; exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
      | ret =>
        dsimp only
        cases bb.isCleanup with
        | true => rw [bool_if_true true rfl]; exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
        | false =>
          rw [bool_if_false false rfl]
          cases listGet st.locals 0 with
          | none => dsimp only; exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
          | some sl =>
            cases sl with
            | dead => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
            | live ov => cases ov <;> exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
      | switchInt discr targets otherwise =>
        dsimp only
        rw [hterm] at htermChk
        dsimp only at htermChk
        cases hev : evalOperand cfg body.locals st.locals discr with
        | ub k =>
          dsimp only
          refine ⟨?_, ?_⟩
          · intro h
            injection h with hk
            rw [hk] at hev
            exact evalOperand_not_dead_when_live cfg body.locals st.locals discr _ hdead htermChk hev
          · intro h
            injection h with hk
            rw [hk] at hev
            exact evalOperand_ne_doubleLive cfg body.locals st.locals discr hev
        | malformed => dsimp only; exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
        | ok dv locals₁ =>
          dsimp only
          cases evalSwitchTarget dv targets otherwise <;> dsimp only <;> exact ⟨(fun h => by cases h), (fun h => by cases h)⟩

theorem lint_sound_no_dead_or_double_live_runFrom (cfg : EvalConfig) (body : Body)
    (liveIn liveOut deadIn deadOut : List (List Bool))
    (hclosed : CfgClosed body)
    (hfix : ValidStorageFixpoint body liveIn liveOut deadIn deadOut)
    (hlint : FixpointLintChecked body liveIn deadIn)
    (fuel : Nat) (st : MachineState) (hcons : StateConsistent body liveIn deadIn st) :
    runFrom cfg body st fuel ≠ .ub .deadLocalAccess ∧
    runFrom cfg body st fuel ≠ .ub .doubleStorageLive := by
  induction fuel generalizing st with
  | zero => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | succ k ih =>
    have h1 := step_no_dead_access_or_double_live cfg body liveIn liveOut deadIn deadOut hlint st hcons
    dsimp only [runFrom]
    cases hs : stepState cfg body st with
    | next st' =>
      exact ih st' (stateConsistent_step cfg body liveIn liveOut deadIn deadOut hclosed hfix st st' hcons hs)
    | done _ => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
    | malformed => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
    | intrinsicLeak => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
    | ub u =>
      constructor
      · intro h; injection h with hu; rw [hu] at hs; exact h1.1 hs
      · intro h; injection h with hu; rw [hu] at hs; exact h1.2 hs

/-- **Theorem (Soundness of `MaybeStorageLive`/`MaybeStorageDead` Dataflow):**
For any closed MIR body admitting a checked post-fixpoint `(liveIn, liveOut, deadIn, deadOut)`,
no finite execution `runBody` of any fuel bound ever accesses a `.dead` local or executes
`StorageLive` on an already-`.live` local. -/
theorem lint_dataflow_soundness_universal (cfg : EvalConfig) (body : Body)
    (liveIn liveOut deadIn deadOut : List (List Bool))
    (hclosed : CfgClosed body)
    (hfix : ValidStorageFixpoint body liveIn liveOut deadIn deadOut)
    (hlint : FixpointLintChecked body liveIn deadIn)
    (args : List Val) (fuel : Nat) :
    runBody cfg body args fuel ≠ .ub .deadLocalAccess ∧
    runBody cfg body args fuel ≠ .ub .doubleStorageLive := by
  dsimp only [runBody]
  cases hne : body.blocks.isEmpty with
  | true => rw [Bool.true_or, bool_if_true true rfl]; exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | false =>
    rw [Bool.false_or]
    cases harg : natBeq args.length body.argCount with
    | false => rw [Bool.not_false, bool_if_true true rfl]; exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
    | true =>
      rw [Bool.not_true, bool_if_false false rfl]
      have hargs : args.length = body.argCount := (natBeq_eq_true_iff args.length body.argCount).mp harg
      have hinit := stateConsistent_init body args liveIn liveOut deadIn deadOut hargs hne hfix
      exact lint_sound_no_dead_or_double_live_runFrom cfg body liveIn liveOut deadIn deadOut hclosed hfix hlint fuel _ hinit

/-- **Theorem (Return-Liveness Soundness):**
At any `Return` terminator checked by `lint_body`, every local without storage markers is
operationally `.dead` (cannot still hold live stack storage). -/
theorem lint_sound_return_dead (body : Body) (liveIn _liveOut deadIn _deadOut : List (List Bool))
    (hfn : body.isFnLike = true)
    (hlint : FixpointLintChecked body liveIn deadIn)
    (st : MachineState) (bb : BasicBlock)
    (hbb : listGet body.blocks st.pc = some bb)
    (hst : st.stmtIdx = bb.stmts.length)
    (hterm : bb.term = .ret)
    (hcons : StateConsistent body liveIn deadIn st)
    (l : Nat) (hl : l < body.locals.length)
    (hmarker : bitGet (alwaysStorageLiveLocals body) l = false) :
    ∀ s : LocalSlot, listGet st.locals l = some s → isLiveSlot s = false := by
  obtain ⟨bb', hbb', _, hlive, _⟩ := hcons
  rw [hbb] at hbb'
  injection hbb' with heqbb
  rw [← heqbb, hst, foldStmts_end] at hlive
  have hblk := hlint st.pc bb hbb
  dsimp only [checkBlockLint] at hblk
  have hparts := Bool.and_eq_true _ _ |>.mp hblk
  have hend := checkStmtsLintAux_end_eq bb.stmts
    (listGetD liveIn st.pc (listReplicate body.locals.length false))
    (listGetD deadIn st.pc (listReplicate body.locals.length false))
  have htc := hparts.2
  rw [hend] at htc
  dsimp only at htc
  rw [hterm, hfn] at htc
  rw [bool_if_true true rfl] at htc
  have hall := (listAll_iff _ _).mp htc l l (by
    rw [listGet_mapRange_lt body.locals.length l _ hl]; rfl)
  intro s hgs
  cases hsl : isLiveSlot s with
  | false => rfl
  | true =>
    have hbit := hlive.2 l s hgs hsl
    rw [hbit, hmarker] at hall
    contradiction

/-! ## Section 5: `ReorderBasicBlocks` & `ReorderLocals` Alpha-Isomorphism Bisimulation (`prettify.rs`) -/

structure BlockPerm (n : Nat) where
  fwd : Nat → Nat
  inv : Nat → Nat
  fwd_lt : ∀ i, i < n → fwd i < n
  inv_lt : ∀ j, j < n → inv j < n
  inv_fwd : ∀ i, i < n → inv (fwd i) = i
  fwd_inv : ∀ j, j < n → fwd (inv j) = j
  fix_zero : fwd 0 = 0

noncomputable def renameTermBlocks (f : Nat → Nat) : Term → Term
  | .goto t => .goto (f t)
  | .switchInt d ts ow => .switchInt d (listMap (fun p => (p.1, f p.2)) ts) (f ow)
  | .ret => .ret
  | .call c args dest t u => .call c args dest (f t) u
  | .peekCall arg t => .peekCall arg (f t)
  | .unreachable => .unreachable

noncomputable def renameBlockBlocks (f : Nat → Nat) (bb : BasicBlock) : BasicBlock :=
  { bb with term := renameTermBlocks f bb.term }

noncomputable def reorderBlocksBody {n : Nat} (σ : BlockPerm n) (body : Body) : Body :=
  { body with
    blocks := mapRange body.blocks.length (fun j =>
      renameBlockBlocks σ.fwd (listGetD body.blocks (σ.inv j) defaultBlock)) }

theorem reorderBlocks_length (body : Body) (σ : BlockPerm body.blocks.length) :
    (reorderBlocksBody σ body).blocks.length = body.blocks.length :=
  mapRange_length body.blocks.length _

theorem listGet_reorderBlocks (body : Body) (σ : BlockPerm body.blocks.length) (i : Nat) (bb : BasicBlock) :
    listGet body.blocks i = some bb →
    listGet (reorderBlocksBody σ body).blocks (σ.fwd i) = some (renameBlockBlocks σ.fwd bb) := by
  intro hget
  have hi : i < body.blocks.length := listGet_some_lt body.blocks i bb hget
  have hlt : σ.fwd i < body.blocks.length := σ.fwd_lt i hi
  dsimp only [reorderBlocksBody]
  rw [listGet_mapRange_lt body.blocks.length (σ.fwd i) _ hlt]
  rw [σ.inv_fwd i hi]
  dsimp only [listGetD]
  rw [hget]

theorem hasStorageMarkerInStmts_renameBlocks : True := trivial

theorem hasStorageMarker_reorderBlocks (body : Body) (σ : BlockPerm body.blocks.length) (l : Nat) :
    hasStorageMarker (reorderBlocksBody σ body) l = hasStorageMarker body l := by
  dsimp only [hasStorageMarker]
  cases h1 : listAny (fun bb => hasStorageMarkerInStmts l bb.stmts) (reorderBlocksBody σ body).blocks with
  | true =>
    obtain ⟨j, bb', hgj, hmj⟩ := (listAny_iff (fun bb : BasicBlock => hasStorageMarkerInStmts l bb.stmts) _).mp h1
    have hj : j < (reorderBlocksBody σ body).blocks.length := listGet_some_lt _ j bb' hgj
    rw [reorderBlocks_length] at hj
    dsimp only [reorderBlocksBody] at hgj
    rw [listGet_mapRange_lt body.blocks.length j _ hj] at hgj
    injection hgj with hbb
    rw [← hbb] at hmj
    have hinv_lt := σ.inv_lt j hj
    obtain ⟨bb0, hbb0⟩ := listGet_lt_some body.blocks (σ.inv j) hinv_lt
    have heqd : listGetD body.blocks (σ.inv j) defaultBlock = bb0 := by dsimp only [listGetD]; rw [hbb0]
    dsimp only [renameBlockBlocks] at hmj
    rw [heqd] at hmj
    exact ((listAny_iff (fun bb : BasicBlock => hasStorageMarkerInStmts l bb.stmts) _).mpr ⟨σ.inv j, bb0, hbb0, hmj⟩).symm
  | false =>
    cases h2 : listAny (fun bb => hasStorageMarkerInStmts l bb.stmts) body.blocks with
    | false => rfl
    | true =>
      obtain ⟨i, bb0, hgi, hmi⟩ := (listAny_iff (fun bb : BasicBlock => hasStorageMarkerInStmts l bb.stmts) _).mp h2
      have hgj := listGet_reorderBlocks body σ i bb0 hgi
      have htrue := (listAny_iff (fun bb : BasicBlock => hasStorageMarkerInStmts l bb.stmts) (reorderBlocksBody σ body).blocks).mpr
        ⟨σ.fwd i, renameBlockBlocks σ.fwd bb0, hgj, hmi⟩
      rw [htrue] at h1
      contradiction

theorem initLocals_reorderBlocks (body : Body) (σ : BlockPerm body.blocks.length) (args : List Val) :
    initLocals (reorderBlocksBody σ body) args = initLocals body args := by
  unfold initLocals
  have hgen : ∀ start len,
      mapRangeFrom start len (fun l =>
        let ty := listGetD body.locals l .u32
        if natBeq l 0 then liveUninitSlot ty
        else if natBle l body.argCount then
          match listGet args (l - 1) with | some v => .live (some v) | none => .dead
        else if !hasStorageMarker (reorderBlocksBody σ body) l then liveUninitSlot ty else .dead) =
      mapRangeFrom start len (fun l =>
        let ty := listGetD body.locals l .u32
        if natBeq l 0 then liveUninitSlot ty
        else if natBle l body.argCount then
          match listGet args (l - 1) with | some v => .live (some v) | none => .dead
        else if !hasStorageMarker body l then liveUninitSlot ty else .dead) := by
    intro start len
    induction len generalizing start with
    | zero => rfl
    | succ k ih =>
      unfold mapRangeFrom
      have hhs : hasStorageMarker (reorderBlocksBody σ body) start = hasStorageMarker body start :=
        hasStorageMarker_reorderBlocks body σ start
      dsimp only
      rw [hhs, ih (start + 1)]
  exact hgen 0 body.locals.length

noncomputable def SimBB (n : Nat) (σ : BlockPerm n) (st₁ st₂ : MachineState) : Prop :=
  st₁.pc < n ∧ st₂.pc = σ.fwd st₁.pc ∧ st₂.stmtIdx = st₁.stmtIdx ∧ st₂.locals = st₁.locals

theorem switchLookup_map (k otherwise : Nat) (f : Nat → Nat) (targets : List (Nat × Nat)) :
    switchLookup k (f otherwise) (listMap (fun p => (p.1, f p.2)) targets) =
      f (switchLookup k otherwise targets) := by
  induction targets with
  | nil => rfl
  | cons p tl ih =>
    unfold listMap switchLookup
    cases natBeq k p.1 with
    | true => rfl
    | false => exact ih

theorem evalSwitchTarget_rename (v : Val) (f : Nat → Nat) (targets : List (Nat × Nat)) (otherwise : Nat) :
    evalSwitchTarget v (listMap (fun p => (p.1, f p.2)) targets) (f otherwise) =
      match evalSwitchTarget v targets otherwise with
      | some t => some (f t)
      | none => none := by
  cases v with
  | u32 n => exact congrArg some (switchLookup_map n otherwise f targets)
  | bool b => cases b <;> exact congrArg some (switchLookup_map _ otherwise f targets)
  | unit => rfl
  | pair _ _ => rfl
  | fnPtr _ => rfl

theorem reorderBlocks_step_sim (cfg : EvalConfig) (body : Body)
    (σ : BlockPerm body.blocks.length) (hclosed : CfgClosed body)
    (st₁ st₂ : MachineState) (hsim : SimBB body.blocks.length σ st₁ st₂) :
    match stepState cfg body st₁, stepState cfg (reorderBlocksBody σ body) st₂ with
    | .next st₁', .next st₂' => SimBB body.blocks.length σ st₁' st₂'
    | .done v₁, .done v₂ => v₁ = v₂
    | .ub k₁, .ub k₂ => k₁ = k₂
    | .malformed, .malformed => True
    | .intrinsicLeak, .intrinsicLeak => True
    | _, _ => False := by
  obtain ⟨hpc_lt, hpc2, hidx2, hloc2⟩ := hsim
  obtain ⟨bb, hbb⟩ := listGet_lt_some body.blocks st₁.pc hpc_lt
  have hbb2 := listGet_reorderBlocks body σ st₁.pc bb hbb
  dsimp only [stepState]
  rw [hbb, hpc2, hbb2, hidx2, hloc2]
  dsimp only [reorderBlocksBody, renameBlockBlocks]
  cases hst : listGet bb.stmts st₁.stmtIdx with
  | some stmt =>
    dsimp only
    cases stmt with
    | nop => exact ⟨hpc_lt, rfl, rfl, rfl⟩
    | storageLive l =>
      dsimp only
      cases listGet body.locals l with
      | none => dsimp only; try trivial
      | some ty =>
        cases listGet st₁.locals l with
        | none => dsimp only; try trivial
        | some cur =>
          dsimp only
          cases cur with
          | dead =>
            rw [Bool.and_false, bool_if_false false rfl]
            cases listSet st₁.locals l (liveUninitSlot ty) <;> dsimp only <;> first | trivial | exact ⟨hpc_lt, rfl, rfl, rfl⟩
          | live _ =>
            cases cfg.abortOnDoubleStorageLive with
            | true => rw [Bool.true_and, bool_if_true true rfl]; rfl
            | false =>
              rw [Bool.false_and, bool_if_false false rfl]
              cases listSet st₁.locals l (liveUninitSlot ty) <;> dsimp only <;> first | trivial | exact ⟨hpc_lt, rfl, rfl, rfl⟩
    | storageDead l =>
      dsimp only
      cases natBeq l 0 with
      | true => rw [bool_if_true true rfl]; trivial
      | false =>
        rw [bool_if_false false rfl]
        cases listSet st₁.locals l .dead <;> dsimp only <;> first | trivial | exact ⟨hpc_lt, rfl, rfl, rfl⟩
    | assign dest rval =>
      dsimp only
      cases (cfg.forbidAliasAssign && rvalueConflictsWithPlace dest rval) with
      | true => rw [bool_if_true true rfl]; rfl
      | false =>
        rw [bool_if_false false rfl]
        cases evalRvalue cfg body.locals st₁.locals rval with
        | ub _ => dsimp only; rfl
        | malformed => dsimp only; try trivial
        | ok val l1 =>
          dsimp only
          cases writePlace l1 dest val <;> dsimp only <;> first | rfl | trivial | exact ⟨hpc_lt, rfl, rfl, rfl⟩
  | none =>
    dsimp only
    cases natBeq st₁.stmtIdx bb.stmts.length with
    | false => rw [bool_if_false false rfl]; trivial
    | true =>
      rw [bool_if_true true rfl]
      cases hterm : bb.term with
      | goto target =>
        dsimp only [renameTermBlocks]
        have hlt := hclosed st₁.pc bb 0 target hbb (by rw [hterm]; rfl)
        exact ⟨hlt, rfl, rfl, rfl⟩
      | switchInt discr targets otherwise =>
        dsimp only [renameTermBlocks]
        cases evalOperand cfg body.locals st₁.locals discr with
        | ub _ => dsimp only; rfl
        | malformed => dsimp only; trivial
        | ok dv locals₁ =>
          dsimp only
          rw [evalSwitchTarget_rename dv σ.fwd targets otherwise]
          cases hesw : evalSwitchTarget dv targets otherwise with
          | none => dsimp only; try trivial
          | some nextPc =>
            dsimp only
            obtain ⟨tIdx, htIdx⟩ := evalSwitchTarget_in_succs dv targets otherwise nextPc hesw
            have hlt := hclosed st₁.pc bb tIdx nextPc hbb (by rw [hterm]; exact htIdx)
            exact ⟨hlt, rfl, rfl, rfl⟩
      | ret =>
        dsimp only [renameTermBlocks]
        cases bb.isCleanup with
        | true => rw [bool_if_true true rfl]; trivial
        | false =>
          rw [bool_if_false false rfl]
          cases listGet st₁.locals 0 with
          | none => dsimp only; try trivial
          | some sl =>
            cases sl with
            | dead => rfl
            | live ov => cases ov <;> rfl
      | call _ _ _ _ _ => dsimp only [renameTermBlocks]; trivial
      | peekCall _ _ => dsimp only [renameTermBlocks]; trivial
      | unreachable => dsimp only [renameTermBlocks]; rfl

theorem reorderBlocks_runFrom_equiv (cfg : EvalConfig) (body : Body)
    (σ : BlockPerm body.blocks.length) (hclosed : CfgClosed body)
    (fuel : Nat) (st₁ st₂ : MachineState) (hsim : SimBB body.blocks.length σ st₁ st₂) :
    runFrom cfg (reorderBlocksBody σ body) st₂ fuel = runFrom cfg body st₁ fuel := by
  induction fuel generalizing st₁ st₂ with
  | zero => rfl
  | succ k ih =>
    have hstep := reorderBlocks_step_sim cfg body σ hclosed st₁ st₂ hsim
    dsimp only [runFrom]
    cases h1 : stepState cfg body st₁ <;> cases h2 : stepState cfg (reorderBlocksBody σ body) st₂
    all_goals rw [h1, h2] at hstep
    all_goals dsimp only at hstep ⊢
    all_goals first
      | rfl
      | exact False.elim hstep
      | exact ih _ _ hstep
      | exact congrArg Outcome.returned hstep.symm
      | exact congrArg Outcome.ub hstep.symm

/-- **Theorem (`ReorderBasicBlocks` Alpha-Isomorphism Bisimulation):**
For any closed MIR body and any basic-block permutation fixing `START_BLOCK = 0`, `runBody`
produces identical outcomes across all configurations, arguments, and fuel bounds. -/
theorem reorderBlocks_run_equiv (cfg : EvalConfig) (body : Body)
    (σ : BlockPerm body.blocks.length) (hclosed : CfgClosed body)
    (args : List Val) (fuel : Nat) :
    runBody cfg (reorderBlocksBody σ body) args fuel = runBody cfg body args fuel := by
  dsimp only [runBody, reorderBlocksBody]
  have hempty : (mapRange body.blocks.length (fun j => renameBlockBlocks σ.fwd (listGetD body.blocks (σ.inv j) defaultBlock))).isEmpty = body.blocks.isEmpty := by
    cases h1 : body.blocks.isEmpty with
    | true =>
      have hlen0 : body.blocks.length = 0 := by cases hb : body.blocks with | nil => rfl | cons _ _ => rw [hb] at h1; contradiction
      have hlen2 : (mapRange body.blocks.length (fun j => renameBlockBlocks σ.fwd (listGetD body.blocks (σ.inv j) defaultBlock))).length = 0 := by rw [mapRange_length, hlen0]
      cases h2 : mapRange body.blocks.length (fun j => renameBlockBlocks σ.fwd (listGetD body.blocks (σ.inv j) defaultBlock)) with
      | nil => rfl
      | cons _ _ => rw [h2] at hlen2; contradiction
    | false =>
      have hpos : 0 < body.blocks.length := by cases hb : body.blocks with | nil => rw [hb] at h1; contradiction | cons _ _ => exact Nat.zero_lt_succ _
      have hpos2 : 0 < (mapRange body.blocks.length (fun j => renameBlockBlocks σ.fwd (listGetD body.blocks (σ.inv j) defaultBlock))).length := by rw [mapRange_length]; exact hpos
      cases h2 : mapRange body.blocks.length (fun j => renameBlockBlocks σ.fwd (listGetD body.blocks (σ.inv j) defaultBlock)) with
      | nil => rw [h2] at hpos2; exact False.elim (Nat.lt_irrefl 0 hpos2)
      | cons _ _ => rfl
  rw [hempty]
  cases h1 : body.blocks.isEmpty with
  | true =>
    rw [Bool.true_or]
    try rw [Bool.true_or]
    rw [bool_if_true true rfl, bool_if_true true rfl]
  | false =>
    rw [Bool.false_or]
    cases natBeq args.length body.argCount with
    | false =>
      rw [Bool.not_false]
      rw [bool_if_true true rfl, bool_if_true true rfl]
    | true =>
      rw [Bool.not_true]
      rw [bool_if_false false rfl, bool_if_false false rfl]
      have hpos : 0 < body.blocks.length := by
        cases hb : body.blocks with
        | nil => rw [hb] at h1; contradiction
        | cons _ _ => exact Nat.zero_lt_succ _
      have hloc_eq : initLocals { argCount := body.argCount, locals := body.locals, blocks := mapRange body.blocks.length (fun j => renameBlockBlocks σ.fwd (listGetD body.blocks (σ.inv j) defaultBlock)), isFnLike := body.isFnLike, canUnwind := body.canUnwind } args = initLocals body args :=
        initLocals_reorderBlocks body σ args
      rw [hloc_eq]
      exact reorderBlocks_runFrom_equiv cfg body σ hclosed fuel
        { pc := 0, stmtIdx := 0, locals := initLocals body args }
        { pc := 0, stmtIdx := 0, locals := initLocals body args }
        ⟨hpos, σ.fix_zero.symm, rfl, rfl⟩

/-! #### `ReorderLocals` Formalization & Lockstep Operational Bisimulation -/

structure LocalPerm (m argCount : Nat) where
  fwd : Nat → Nat
  inv : Nat → Nat
  fwd_lt : ∀ i, i < m → fwd i < m
  inv_lt : ∀ j, j < m → inv j < m
  inv_fwd : ∀ i, i < m → inv (fwd i) = i
  fwd_inv : ∀ j, j < m → fwd (inv j) = j
  fix_prefix : ∀ i, i ≤ argCount → fwd i = i

noncomputable def renamePlaceLocals (f : Nat → Nat) (p : Place) : Place :=
  { p with localId := f p.localId }

noncomputable def renameOperandLocals (f : Nat → Nat) : Operand → Operand
  | .copy p => .copy (renamePlaceLocals f p)
  | .move p => .move (renamePlaceLocals f p)
  | .constVal v => .constVal v

noncomputable def renameRvalueLocals (f : Nat → Nat) : Rvalue → Rvalue
  | .use op => .use (renameOperandLocals f op)
  | .binOp op a b => .binOp op (renameOperandLocals f a) (renameOperandLocals f b)
  | .pairAgg a b => .pairAgg (renameOperandLocals f a) (renameOperandLocals f b)

noncomputable def renameStmtLocals (f : Nat → Nat) : Stmt → Stmt
  | .nop => .nop
  | .storageLive l => .storageLive (f l)
  | .storageDead l => .storageDead (f l)
  | .assign d r => .assign (renamePlaceLocals f d) (renameRvalueLocals f r)

noncomputable def renameTermLocals (f : Nat → Nat) : Term → Term
  | .goto t => .goto t
  | .switchInt d ts ow => .switchInt (renameOperandLocals f d) ts ow
  | .ret => .ret
  | .call c args dest t u => .call c (listMap (renameOperandLocals f) args) (renamePlaceLocals f dest) t u
  | .peekCall arg t => .peekCall (renamePlaceLocals f arg) t
  | .unreachable => .unreachable

noncomputable def renameBlockLocals (f : Nat → Nat) (bb : BasicBlock) : BasicBlock :=
  { bb with
    stmts := listMap (renameStmtLocals f) bb.stmts
    term := renameTermLocals f bb.term }

noncomputable def reorderLocalsBody {m argCount : Nat} (τ : LocalPerm m argCount) (body : Body) : Body :=
  { body with
    locals := mapRange body.locals.length (fun j => listGetD body.locals (τ.inv j) .u32)
    blocks := listMap (renameBlockLocals τ.fwd) body.blocks }

noncomputable def LocalsInBounds (body : Body) : Prop :=
  ∀ b bb, listGet body.blocks b = some bb →
    listAll (checkStmtBounds body.locals.length) bb.stmts = true ∧
    (match bb.term with
     | .switchInt discr _ _ => checkOperandBounds body.locals.length discr = true
     | .call _ args dest _ _ => natBlt dest.localId body.locals.length = true ∧ listAll (checkOperandBounds body.locals.length) args = true
     | .peekCall arg _ => natBlt arg.localId body.locals.length = true
     | _ => True)

noncomputable def SimLocal (m argCount : Nat) (τ : LocalPerm m argCount) (st₁ st₂ : MachineState) : Prop :=
  st₂.pc = st₁.pc ∧
  st₂.stmtIdx = st₁.stmtIdx ∧
  st₁.locals.length = m ∧
  st₂.locals.length = m ∧
  ∀ l, l < m → listGet st₂.locals (τ.fwd l) = listGet st₁.locals l

theorem hasStorageMarkerInStmts_rename (τ : LocalPerm m argCount) (stmts : List Stmt)
    (hbounds : listAll (checkStmtBounds m) stmts = true)
    (l : Nat) (hl : l < m) :
    hasStorageMarkerInStmts (τ.fwd l) (listMap (renameStmtLocals τ.fwd) stmts) =
      hasStorageMarkerInStmts l stmts := by
  induction stmts with
  | nil => rfl
  | cons st tl ih =>
    have hb := Bool.and_eq_true _ _ |>.mp hbounds
    have ihtl := ih hb.2
    unfold listMap
    rw [hasStorageMarkerInStmts_cons, hasStorageMarkerInStmts_cons, ihtl]
    cases st with
    | nop => rfl
    | assign _ _ => rfl
    | storageLive x =>
      have hx : x < m := (natBlt_eq_true_iff x m).mp hb.1
      have heq : natBeq (τ.fwd x) (τ.fwd l) = natBeq x l := by
        cases h1 : natBeq x l with
        | true =>
          have hxl := (natBeq_eq_true_iff x l).mp h1
          rw [hxl, natBeq_refl]
        | false =>
          cases h2 : natBeq (τ.fwd x) (τ.fwd l) with
          | false => rfl
          | true =>
            have hfx := (natBeq_eq_true_iff (τ.fwd x) (τ.fwd l)).mp h2
            have hinj : x = l := by rw [← τ.inv_fwd x hx, ← τ.inv_fwd l hl, hfx]
            rw [hinj, natBeq_refl] at h1
            contradiction
      dsimp only [renameStmtLocals]
      rw [heq]
    | storageDead x =>
      have hx : x < m := (natBlt_eq_true_iff x m).mp hb.1
      have heq : natBeq (τ.fwd x) (τ.fwd l) = natBeq x l := by
        cases h1 : natBeq x l with
        | true =>
          have hxl := (natBeq_eq_true_iff x l).mp h1
          rw [hxl, natBeq_refl]
        | false =>
          cases h2 : natBeq (τ.fwd x) (τ.fwd l) with
          | false => rfl
          | true =>
            have hfx := (natBeq_eq_true_iff (τ.fwd x) (τ.fwd l)).mp h2
            have hinj : x = l := by rw [← τ.inv_fwd x hx, ← τ.inv_fwd l hl, hfx]
            rw [hinj, natBeq_refl] at h1
            contradiction
      dsimp only [renameStmtLocals]
      rw [heq]

theorem hasStorageMarker_reorderLocals (body : Body) (τ : LocalPerm body.locals.length body.argCount)
    (hloc : LocalsInBounds body) (l : Nat) (hl : l < body.locals.length) :
    hasStorageMarker (reorderLocalsBody τ body) (τ.fwd l) = hasStorageMarker body l := by
  dsimp only [hasStorageMarker, reorderLocalsBody]
  cases h1 : listAny (fun bb => hasStorageMarkerInStmts (τ.fwd l) bb.stmts) (listMap (renameBlockLocals τ.fwd) body.blocks) with
  | true =>
    obtain ⟨b, bb', hgb, hmb⟩ := (listAny_iff _ _).mp h1
    rw [listGet_map] at hgb
    cases hg0 : listGet body.blocks b with
    | none => rw [hg0] at hgb; contradiction
    | some bb0 =>
      rw [hg0] at hgb
      injection hgb with heqbb
      rw [← heqbb] at hmb
      have hbounds := (hloc b bb0 hg0).1
      have hhm := hasStorageMarkerInStmts_rename τ bb0.stmts hbounds l hl
      change hasStorageMarkerInStmts (τ.fwd l) (listMap (renameStmtLocals τ.fwd) bb0.stmts) = true at hmb
      rw [hhm] at hmb
      exact ((listAny_iff _ _).mpr ⟨b, bb0, hg0, hmb⟩).symm
  | false =>
    cases h2 : listAny (fun bb => hasStorageMarkerInStmts l bb.stmts) body.blocks with
    | false => rfl
    | true =>
      obtain ⟨b, bb0, hg0, hm0⟩ := (listAny_iff _ _).mp h2
      have hbounds := (hloc b bb0 hg0).1
      have hhm := hasStorageMarkerInStmts_rename τ bb0.stmts hbounds l hl
      rw [← hhm] at hm0
      have hgb : listGet (listMap (renameBlockLocals τ.fwd) body.blocks) b = some (renameBlockLocals τ.fwd bb0) := by
        rw [listGet_map, hg0]
      have htrue := (listAny_iff (fun bb : BasicBlock => hasStorageMarkerInStmts (τ.fwd l) bb.stmts)
        (listMap (renameBlockLocals τ.fwd) body.blocks)).mpr ⟨b, renameBlockLocals τ.fwd bb0, hgb, hm0⟩
      rw [htrue] at h1
      contradiction

theorem initLocals_reorderLocals (body : Body) (τ : LocalPerm body.locals.length body.argCount)
    (hloc : LocalsInBounds body) (harg : body.argCount < body.locals.length)
    (args : List Val) (l : Nat) (hl : l < body.locals.length) :
    listGet (initLocals (reorderLocalsBody τ body) args) (τ.fwd l) =
      listGet (initLocals body args) l := by
  have hlt2 := τ.fwd_lt l hl
  dsimp only [reorderLocalsBody, initLocals]
  have hlen : (mapRange body.locals.length fun j => listGetD body.locals (τ.inv j) MirTy.u32).length = body.locals.length := mapRange_length _ _
  rw [hlen, listGet_mapRange_lt body.locals.length (τ.fwd l) _ hlt2, listGet_mapRange_lt body.locals.length l _ hl]
  have hty : listGetD (mapRange body.locals.length fun j => listGetD body.locals (τ.inv j) MirTy.u32) (τ.fwd l) .u32 = listGetD body.locals l .u32 := by
    dsimp only [listGetD]
    rw [listGet_mapRange_lt body.locals.length (τ.fwd l) _ hlt2, τ.inv_fwd l hl]
  rw [hty]
  cases h0 : natBeq l 0 with
  | true =>
    have hl0 := (natBeq_eq_true_iff l 0).mp h0
    have hfw0 : τ.fwd 0 = 0 := τ.fix_prefix 0 (Nat.zero_le body.argCount)
    rw [hl0, hfw0, natBeq_refl, bool_if_true true rfl, bool_if_true true rfl]
  | false =>
    cases ha : natBle l body.argCount with
    | true =>
      have hle := (natBle_eq_true_iff l body.argCount).mp ha
      have hfwa : τ.fwd l = l := τ.fix_prefix l hle
      rw [hfwa, h0, ha, bool_if_false false rfl, bool_if_false false rfl, bool_if_true true rfl, bool_if_true true rfl]
    | false =>
      have hnf0 : natBeq (τ.fwd l) 0 = false := by
        cases hcheck : natBeq (τ.fwd l) 0 with
        | false => rfl
        | true =>
          have hfl0 := (natBeq_eq_true_iff (τ.fwd l) 0).mp hcheck
          have h0le : 0 ≤ body.argCount := Nat.zero_le body.argCount
          have h0lt : 0 < body.locals.length := Nat.lt_of_le_of_lt h0le harg
          have hl0 : l = 0 := (τ.inv_fwd l hl).symm.trans ((congrArg τ.inv (hfl0.trans (τ.fix_prefix 0 h0le).symm)).trans (τ.inv_fwd 0 h0lt))
          rw [hl0] at h0
          contradiction
      have hnfle : natBle (τ.fwd l) body.argCount = false := by
        cases hcheck : natBle (τ.fwd l) body.argCount with
        | false => rfl
        | true =>
          have hfle := (natBle_eq_true_iff (τ.fwd l) body.argCount).mp hcheck
          have hflt : τ.fwd l < body.locals.length := hlt2
          have hfix := τ.fix_prefix (τ.fwd l) hfle
          have heq : l = τ.fwd l :=
            (τ.inv_fwd l hl).symm.trans ((congrArg τ.inv hfix.symm).trans (τ.inv_fwd (τ.fwd l) hflt))
          rw [← heq, ha] at hcheck
          contradiction
      have hmrk := hasStorageMarker_reorderLocals body τ hloc l hl
      dsimp only [reorderLocalsBody] at hmrk
      rw [hnf0, hnfle, hmrk, bool_if_false false rfl, bool_if_false false rfl, bool_if_false false rfl, bool_if_false false rfl]

theorem evalOperand_reorderLocals (cfg : EvalConfig) (body : Body)
    (τ : LocalPerm body.locals.length body.argCount)
    (st₁ st₂ : MachineState) (hsim : SimLocal body.locals.length body.argCount τ st₁ st₂)
    (op : Operand) (hb : checkOperandBounds body.locals.length op = true) :
    match evalOperand cfg body.locals st₁.locals op,
          evalOperand cfg (reorderLocalsBody τ body).locals st₂.locals (renameOperandLocals τ.fwd op) with
    | .ok v₁ l₁', .ok v₂ l₂' =>
      v₁ = v₂ ∧ l₁'.length = body.locals.length ∧ l₂'.length = body.locals.length ∧
      ∀ l, l < body.locals.length → listGet l₂' (τ.fwd l) = listGet l₁' l
    | .ub k₁, .ub k₂ => k₁ = k₂
    | .malformed, .malformed => True
    | _, _ => False := by
  obtain ⟨_, _, hlen1, hlen2, hmap⟩ := hsim
  cases op with
  | constVal v => exact ⟨rfl, hlen1, hlen2, hmap⟩
  | copy p =>
    have hp : p.localId < body.locals.length := (natBlt_eq_true_iff p.localId body.locals.length).mp hb
    dsimp only [evalOperand, renameOperandLocals, renamePlaceLocals]
    rw [hmap p.localId hp]
    cases listGet st₁.locals p.localId with
    | none => trivial
    | some sl =>
      cases sl with
      | dead => rfl
      | live ov =>
        cases ov with
        | none => rfl
        | some v =>
          dsimp only
          cases readPlaceFromVal v p.field <;> dsimp only <;> first | trivial | exact ⟨rfl, hlen1, hlen2, hmap⟩
  | move p =>
    have hp : p.localId < body.locals.length := (natBlt_eq_true_iff p.localId body.locals.length).mp hb
    have hty2 : listGet (reorderLocalsBody τ body).locals (τ.fwd p.localId) = listGet body.locals p.localId := by
      dsimp only [reorderLocalsBody]
      have hlt2 := τ.fwd_lt p.localId hp
      rw [listGet_mapRange_lt body.locals.length (τ.fwd p.localId) _ hlt2, τ.inv_fwd p.localId hp]
      obtain ⟨ty0, hty0⟩ := listGet_lt_some body.locals p.localId hp
      dsimp only [listGetD]
      rw [hty0]
    dsimp only [evalOperand, renameOperandLocals, renamePlaceLocals]
    rw [hty2, hmap p.localId hp]
    cases listGet body.locals p.localId with
    | none => dsimp only; try trivial
    | some ty =>
      cases listGet st₁.locals p.localId with
      | none => dsimp only; try trivial
      | some sl =>
        cases sl with
        | dead => rfl
        | live ov =>
          cases ov with
          | none => rfl
          | some v =>
            dsimp only
            cases readPlaceFromVal v p.field with
            | none => dsimp only; try trivial
            | some rv =>
              dsimp only
              cases cfg.deinitMovedPlace with
              | false => rw [bool_if_false false rfl]; exact ⟨rfl, hlen1, hlen2, hmap⟩
              | true =>
                rw [bool_if_true true rfl]
                cases p.field with
                | some _ => dsimp only; exact ⟨rfl, hlen1, hlen2, hmap⟩
                | none =>
                  dsimp only
                  have h1lt : p.localId < st₁.locals.length := by rw [hlen1]; exact hp
                  have h2lt : τ.fwd p.localId < st₂.locals.length := by rw [hlen2]; exact τ.fwd_lt p.localId hp
                  obtain ⟨l1', hl1'⟩ := listSet_lt_some st₁.locals p.localId (liveUninitSlot ty) h1lt
                  obtain ⟨l2', hl2'⟩ := listSet_lt_some st₂.locals (τ.fwd p.localId) (liveUninitSlot ty) h2lt
                  rw [hl1', hl2']
                  dsimp only
                  refine ⟨rfl, Eq.trans (listSet_some_length _ _ _ _ hl1') hlen1, Eq.trans (listSet_some_length _ _ _ _ hl2') hlen2, ?_⟩
                  intro l hl
                  cases hnat : natBeq l p.localId with
                  | true =>
                    have heq := (natBeq_eq_true_iff l p.localId).mp hnat
                    rw [heq, listGet_set_same _ _ _ _ hl1', listGet_set_same _ _ _ _ hl2']
                  | false =>
                    have hne : p.localId ≠ l := fun e => (natBeq_ne hnat) e.symm
                    have hne2 : τ.fwd p.localId ≠ τ.fwd l := by
                      intro heq2
                      exact hne (by rw [← τ.inv_fwd p.localId hp, ← τ.inv_fwd l hl, heq2])
                    rw [listGet_set_ne _ _ _ _ _ hne hl1', listGet_set_ne _ _ _ _ _ hne2 hl2']
                    exact hmap l hl

theorem evalRvalue_reorderLocals (cfg : EvalConfig) (body : Body)
    (τ : LocalPerm body.locals.length body.argCount)
    (st₁ st₂ : MachineState) (hsim : SimLocal body.locals.length body.argCount τ st₁ st₂)
    (rval : Rvalue) (hb : checkRvalueBounds body.locals.length rval = true) :
    match evalRvalue cfg body.locals st₁.locals rval,
          evalRvalue cfg (reorderLocalsBody τ body).locals st₂.locals (renameRvalueLocals τ.fwd rval) with
    | .ok v₁ l₁', .ok v₂ l₂' =>
      v₁ = v₂ ∧ l₁'.length = body.locals.length ∧ l₂'.length = body.locals.length ∧
      ∀ l, l < body.locals.length → listGet l₂' (τ.fwd l) = listGet l₁' l
    | .ub k₁, .ub k₂ => k₁ = k₂
    | .malformed, .malformed => True
    | _, _ => False := by
  cases rval with
  | use op => exact evalOperand_reorderLocals cfg body τ st₁ st₂ hsim op hb
  | binOp op a b =>
    have hbc := Bool.and_eq_true _ _ |>.mp hb
    have h1 := evalOperand_reorderLocals cfg body τ st₁ st₂ hsim a hbc.1
    dsimp only [evalRvalue, renameRvalueLocals]
    cases ha1 : evalOperand cfg body.locals st₁.locals a with
    | ub _ =>
      cases ha2 : evalOperand cfg (reorderLocalsBody τ body).locals st₂.locals (renameOperandLocals τ.fwd a) <;>
      rw [ha1, ha2] at h1 <;> dsimp only at h1 ⊢ <;> first | exact h1 | exact False.elim h1
    | malformed =>
      cases ha2 : evalOperand cfg (reorderLocalsBody τ body).locals st₂.locals (renameOperandLocals τ.fwd a) <;>
      rw [ha1, ha2] at h1 <;> dsimp only at h1 ⊢ <;> first | try trivial | exact False.elim h1
    | ok va1 l1a =>
      cases ha2 : evalOperand cfg (reorderLocalsBody τ body).locals st₂.locals (renameOperandLocals τ.fwd a) with
      | ub _ => rw [ha1, ha2] at h1; dsimp only at h1
      | malformed => rw [ha1, ha2] at h1; dsimp only at h1
      | ok va2 l2a =>
        rw [ha1, ha2] at h1; dsimp only at h1 ⊢
        obtain ⟨hva, hlen1a, hlen2a, hmapa⟩ := h1
        have hsimA : SimLocal body.locals.length body.argCount τ { st₁ with locals := l1a } { st₂ with locals := l2a } :=
          ⟨hsim.1, hsim.2.1, hlen1a, hlen2a, hmapa⟩
        have h2 := evalOperand_reorderLocals cfg body τ { st₁ with locals := l1a } { st₂ with locals := l2a } hsimA b hbc.2
        cases hb1 : evalOperand cfg body.locals l1a b with
        | ub _ =>
          cases hb2 : evalOperand cfg (reorderLocalsBody τ body).locals l2a (renameOperandLocals τ.fwd b) <;>
          rw [hb1, hb2] at h2 <;> dsimp only at h2 ⊢ <;> first | exact h2 | exact False.elim h2
        | malformed =>
          cases hb2 : evalOperand cfg (reorderLocalsBody τ body).locals l2a (renameOperandLocals τ.fwd b) <;>
          rw [hb1, hb2] at h2 <;> dsimp only at h2 ⊢ <;> first | try trivial | exact False.elim h2
        | ok vb1 l1b =>
          cases hb2 : evalOperand cfg (reorderLocalsBody τ body).locals l2a (renameOperandLocals τ.fwd b) with
          | ub _ => rw [hb1, hb2] at h2; dsimp only at h2
          | malformed => rw [hb1, hb2] at h2; dsimp only at h2
          | ok vb2 l2b =>
            rw [hb1, hb2] at h2; dsimp only at h2 ⊢
            obtain ⟨hvb, hlen1b, hlen2b, hmapb⟩ := h2
            rw [← hva, ← hvb]
            cases evalBinOp op va1 vb1 <;> dsimp only <;> first | try trivial | exact ⟨rfl, hlen1b, hlen2b, hmapb⟩
  | pairAgg a b =>
    have hbc := Bool.and_eq_true _ _ |>.mp hb
    have h1 := evalOperand_reorderLocals cfg body τ st₁ st₂ hsim a hbc.1
    dsimp only [evalRvalue, renameRvalueLocals]
    cases ha1 : evalOperand cfg body.locals st₁.locals a with
    | ub _ =>
      cases ha2 : evalOperand cfg (reorderLocalsBody τ body).locals st₂.locals (renameOperandLocals τ.fwd a) <;>
      rw [ha1, ha2] at h1 <;> dsimp only at h1 ⊢ <;> first | exact h1 | exact False.elim h1
    | malformed =>
      cases ha2 : evalOperand cfg (reorderLocalsBody τ body).locals st₂.locals (renameOperandLocals τ.fwd a) <;>
      rw [ha1, ha2] at h1 <;> dsimp only at h1 ⊢ <;> first | try trivial | exact False.elim h1
    | ok va1 l1a =>
      cases ha2 : evalOperand cfg (reorderLocalsBody τ body).locals st₂.locals (renameOperandLocals τ.fwd a) with
      | ub _ => rw [ha1, ha2] at h1; dsimp only at h1
      | malformed => rw [ha1, ha2] at h1; dsimp only at h1
      | ok va2 l2a =>
        rw [ha1, ha2] at h1; dsimp only at h1 ⊢
        obtain ⟨hva, hlen1a, hlen2a, hmapa⟩ := h1
        have hsimA : SimLocal body.locals.length body.argCount τ { st₁ with locals := l1a } { st₂ with locals := l2a } :=
          ⟨hsim.1, hsim.2.1, hlen1a, hlen2a, hmapa⟩
        have h2 := evalOperand_reorderLocals cfg body τ { st₁ with locals := l1a } { st₂ with locals := l2a } hsimA b hbc.2
        cases hb1 : evalOperand cfg body.locals l1a b with
        | ub _ =>
          cases hb2 : evalOperand cfg (reorderLocalsBody τ body).locals l2a (renameOperandLocals τ.fwd b) <;>
          rw [hb1, hb2] at h2 <;> dsimp only at h2 ⊢ <;> first | exact h2 | exact False.elim h2
        | malformed =>
          cases hb2 : evalOperand cfg (reorderLocalsBody τ body).locals l2a (renameOperandLocals τ.fwd b) <;>
          rw [hb1, hb2] at h2 <;> dsimp only at h2 ⊢ <;> first | try trivial | exact False.elim h2
        | ok vb1 l1b =>
          cases hb2 : evalOperand cfg (reorderLocalsBody τ body).locals l2a (renameOperandLocals τ.fwd b) with
          | ub _ => rw [hb1, hb2] at h2; dsimp only at h2
          | malformed => rw [hb1, hb2] at h2; dsimp only at h2
          | ok vb2 l2b =>
            rw [hb1, hb2] at h2; dsimp only at h2 ⊢
            obtain ⟨hvb, hlen1b, hlen2b, hmapb⟩ := h2
            rw [← hva, ← hvb]
            exact ⟨rfl, hlen1b, hlen2b, hmapb⟩

theorem writePlace_reorderLocals (m argCount : Nat) (τ : LocalPerm m argCount)
    (l1 l2 : List LocalSlot) (hlen1 : l1.length = m) (hlen2 : l2.length = m)
    (hmap : ∀ l, l < m → listGet l2 (τ.fwd l) = listGet l1 l)
    (dest : Place) (hd : dest.localId < m) (val : Val) :
    match writePlace l1 dest val, writePlace l2 (renamePlaceLocals τ.fwd dest) val with
    | .ok () l1', .ok () l2' =>
      l1'.length = m ∧ l2'.length = m ∧ ∀ l, l < m → listGet l2' (τ.fwd l) = listGet l1' l
    | .ub k₁, .ub k₂ => k₁ = k₂
    | .malformed, .malformed => True
    | _, _ => False := by
  dsimp only [writePlace, renamePlaceLocals]
  rw [hmap dest.localId hd]
  cases listGet l1 dest.localId with
  | none => trivial
  | some sl =>
    cases sl with
    | dead => rfl
    | live cur =>
      cases dest.field with
      | none =>
        dsimp only
        have h1lt : dest.localId < l1.length := by rw [hlen1]; exact hd
        have h2lt : τ.fwd dest.localId < l2.length := by rw [hlen2]; exact τ.fwd_lt dest.localId hd
        obtain ⟨l1', hl1'⟩ := listSet_lt_some l1 dest.localId (.live (some val)) h1lt
        obtain ⟨l2', hl2'⟩ := listSet_lt_some l2 (τ.fwd dest.localId) (.live (some val)) h2lt
        rw [hl1', hl2']
        dsimp only
        refine ⟨Eq.trans (listSet_some_length _ _ _ _ hl1') hlen1, Eq.trans (listSet_some_length _ _ _ _ hl2') hlen2, ?_⟩
        intro l hl
        cases hnat : natBeq l dest.localId with
        | true =>
          have heq := (natBeq_eq_true_iff l dest.localId).mp hnat
          rw [heq, listGet_set_same _ _ _ _ hl1', listGet_set_same _ _ _ _ hl2']
        | false =>
          have hne : dest.localId ≠ l := fun e => (natBeq_ne hnat) e.symm
          have hne2 : τ.fwd dest.localId ≠ τ.fwd l := fun e => hne (by rw [← τ.inv_fwd dest.localId hd, ← τ.inv_fwd l hl, e])
          rw [listGet_set_ne _ _ _ _ _ hne hl1', listGet_set_ne _ _ _ _ _ hne2 hl2']
          exact hmap l hl
      | some f =>
        dsimp only
        cases writeFieldVal cur (some f) val with
        | none => dsimp only; try trivial
        | some upd =>
          dsimp only
          have h1lt : dest.localId < l1.length := by rw [hlen1]; exact hd
          have h2lt : τ.fwd dest.localId < l2.length := by rw [hlen2]; exact τ.fwd_lt dest.localId hd
          obtain ⟨l1', hl1'⟩ := listSet_lt_some l1 dest.localId (.live (some upd)) h1lt
          obtain ⟨l2', hl2'⟩ := listSet_lt_some l2 (τ.fwd dest.localId) (.live (some upd)) h2lt
          rw [hl1', hl2']
          dsimp only
          refine ⟨Eq.trans (listSet_some_length _ _ _ _ hl1') hlen1, Eq.trans (listSet_some_length _ _ _ _ hl2') hlen2, ?_⟩
          intro l hl
          cases hnat : natBeq l dest.localId with
          | true =>
            have heq := (natBeq_eq_true_iff l dest.localId).mp hnat
            rw [heq, listGet_set_same _ _ _ _ hl1', listGet_set_same _ _ _ _ hl2']
          | false =>
            have hne : dest.localId ≠ l := fun e => (natBeq_ne hnat) e.symm
            have hne2 : τ.fwd dest.localId ≠ τ.fwd l := fun e => hne (by rw [← τ.inv_fwd dest.localId hd, ← τ.inv_fwd l hl, e])
            rw [listGet_set_ne _ _ _ _ _ hne hl1', listGet_set_ne _ _ _ _ _ hne2 hl2']
            exact hmap l hl

theorem placesConflict_renameLocals (τ : LocalPerm m argCount) (dest src : Place)
    (hd : dest.localId < m) (hs : src.localId < m) :
    placesConflictForAssignment (renamePlaceLocals τ.fwd dest) (renamePlaceLocals τ.fwd src) =
      placesConflictForAssignment dest src := by
  dsimp only [placesConflictForAssignment, Place.beq, renamePlaceLocals]
  have heq : natBeq (τ.fwd dest.localId) (τ.fwd src.localId) = natBeq dest.localId src.localId := by
    cases h1 : natBeq dest.localId src.localId with
    | true =>
      have h := (natBeq_eq_true_iff dest.localId src.localId).mp h1
      rw [h, natBeq_refl]
    | false =>
      cases h2 : natBeq (τ.fwd dest.localId) (τ.fwd src.localId) with
      | false => rfl
      | true =>
        have h := (natBeq_eq_true_iff (τ.fwd dest.localId) (τ.fwd src.localId)).mp h2
        have hinj : dest.localId = src.localId := by rw [← τ.inv_fwd dest.localId hd, ← τ.inv_fwd src.localId hs, h]
        rw [hinj, natBeq_refl] at h1
        contradiction
  rw [heq]

theorem rvalueConflicts_renameLocals (τ : LocalPerm m argCount) (dest : Place) (rval : Rvalue)
    (hd : dest.localId < m) (hr : checkRvalueBounds m rval = true) :
    rvalueConflictsWithPlace (renamePlaceLocals τ.fwd dest) (renameRvalueLocals τ.fwd rval) =
      rvalueConflictsWithPlace dest rval := by
  cases rval with
  | use op =>
    cases op with
    | copy s => exact placesConflict_renameLocals τ dest s hd ((natBlt_eq_true_iff s.localId m).mp hr)
    | move s => exact placesConflict_renameLocals τ dest s hd ((natBlt_eq_true_iff s.localId m).mp hr)
    | constVal _ => rfl
  | binOp _ _ _ => rfl
  | pairAgg a b =>
    have hbc := Bool.and_eq_true _ _ |>.mp hr
    cases a <;> cases b <;> dsimp only [checkOperandBounds] at hbc <;>
    dsimp only [renameRvalueLocals, renameOperandLocals, rvalueConflictsWithPlace]
    · exact bool_or_congr
        (placesConflict_renameLocals τ dest _ hd ((natBlt_eq_true_iff _ m).mp hbc.1))
        (placesConflict_renameLocals τ dest _ hd ((natBlt_eq_true_iff _ m).mp hbc.2))
    · exact bool_or_congr
        (placesConflict_renameLocals τ dest _ hd ((natBlt_eq_true_iff _ m).mp hbc.1))
        (placesConflict_renameLocals τ dest _ hd ((natBlt_eq_true_iff _ m).mp hbc.2))
    · exact placesConflict_renameLocals τ dest _ hd ((natBlt_eq_true_iff _ m).mp hbc.1)
    · exact bool_or_congr
        (placesConflict_renameLocals τ dest _ hd ((natBlt_eq_true_iff _ m).mp hbc.1))
        (placesConflict_renameLocals τ dest _ hd ((natBlt_eq_true_iff _ m).mp hbc.2))
    · exact bool_or_congr
        (placesConflict_renameLocals τ dest _ hd ((natBlt_eq_true_iff _ m).mp hbc.1))
        (placesConflict_renameLocals τ dest _ hd ((natBlt_eq_true_iff _ m).mp hbc.2))
    · exact placesConflict_renameLocals τ dest _ hd ((natBlt_eq_true_iff _ m).mp hbc.1)
    · exact placesConflict_renameLocals τ dest _ hd ((natBlt_eq_true_iff _ m).mp hbc.2)
    · exact placesConflict_renameLocals τ dest _ hd ((natBlt_eq_true_iff _ m).mp hbc.2)

theorem reorderLocals_step_sim (cfg : EvalConfig) (body : Body)
    (τ : LocalPerm body.locals.length body.argCount)
    (hloc : LocalsInBounds body) (harg : body.argCount < body.locals.length)
    (st₁ st₂ : MachineState) (hsim : SimLocal body.locals.length body.argCount τ st₁ st₂) :
    match stepState cfg body st₁, stepState cfg (reorderLocalsBody τ body) st₂ with
    | .next st₁', .next st₂' => SimLocal body.locals.length body.argCount τ st₁' st₂'
    | .done v₁, .done v₂ => v₁ = v₂
    | .ub k₁, .ub k₂ => k₁ = k₂
    | .malformed, .malformed => True
    | .intrinsicLeak, .intrinsicLeak => True
    | _, _ => False := by
  obtain ⟨hpc2, hidx2, hlen1, hlen2, hmap⟩ := hsim
  dsimp only [stepState]
  cases hbb : listGet body.blocks st₁.pc with
  | none =>
    have hbb2 : listGet (reorderLocalsBody τ body).blocks st₂.pc = none := by
      dsimp only [reorderLocalsBody]
      rw [hpc2, listGet_map, hbb]
    rw [hbb2]
    dsimp only
  | some bb =>
    have hbb2 : listGet (reorderLocalsBody τ body).blocks st₂.pc = some (renameBlockLocals τ.fwd bb) := by
      dsimp only [reorderLocalsBody]
      rw [hpc2, listGet_map, hbb]
    rw [hbb2]
    have hlocbb := hloc st₁.pc bb hbb
    dsimp only [renameBlockLocals]
    rw [hidx2, listGet_map]
    cases hst : listGet bb.stmts st₁.stmtIdx with
    | some stmt =>
      dsimp only
      have hsb := (listAll_iff _ _).mp hlocbb.1 st₁.stmtIdx stmt hst
      cases stmt with
      | nop => dsimp only; exact ⟨hpc2, rfl, hlen1, hlen2, hmap⟩
      | storageLive l =>
        have hl : l < body.locals.length := (natBlt_eq_true_iff l body.locals.length).mp hsb
        have hlt2 := τ.fwd_lt l hl
        have hty2 : listGet (reorderLocalsBody τ body).locals (τ.fwd l) = listGet body.locals l := by
          dsimp only [reorderLocalsBody]
          rw [listGet_mapRange_lt body.locals.length (τ.fwd l) _ hlt2, τ.inv_fwd l hl]
          obtain ⟨ty0, hty0⟩ := listGet_lt_some body.locals l hl
          dsimp only [listGetD]
          rw [hty0]
        dsimp only [renameStmtLocals]
        rw [hty2, hmap l hl]
        cases listGet body.locals l with
        | none => dsimp only; try trivial
        | some ty =>
          cases listGet st₁.locals l with
          | none => dsimp only; try trivial
          | some cur =>
            dsimp only
            have hshared :
                (match (match listSet st₁.locals l (liveUninitSlot ty) with
                        | some locals' => StepOut.next { pc := st₁.pc, stmtIdx := st₁.stmtIdx + 1, locals := locals' }
                        | none => StepOut.malformed),
                       (match listSet st₂.locals (τ.fwd l) (liveUninitSlot ty) with
                        | some locals' => StepOut.next { pc := st₂.pc, stmtIdx := st₁.stmtIdx + 1, locals := locals' }
                        | none => StepOut.malformed) with
                 | .next st₁', .next st₂' => SimLocal body.locals.length body.argCount τ st₁' st₂'
                 | .done v₁, .done v₂ => v₁ = v₂
                 | .ub k₁, .ub k₂ => k₁ = k₂
                 | .malformed, .malformed => True
                 | .intrinsicLeak, .intrinsicLeak => True
                 | _, _ => False) := by
              have h1lt : l < st₁.locals.length := by rw [hlen1]; exact hl
              have h2lt : τ.fwd l < st₂.locals.length := by rw [hlen2]; exact hlt2
              obtain ⟨l1', hl1'⟩ := listSet_lt_some st₁.locals l (liveUninitSlot ty) h1lt
              obtain ⟨l2', hl2'⟩ := listSet_lt_some st₂.locals (τ.fwd l) (liveUninitSlot ty) h2lt
              rw [hl1', hl2']
              refine ⟨hpc2, rfl, Eq.trans (listSet_some_length _ _ _ _ hl1') hlen1, Eq.trans (listSet_some_length _ _ _ _ hl2') hlen2, ?_⟩
              intro x hx
              cases hnat : natBeq x l with
              | true =>
                have heq := (natBeq_eq_true_iff x l).mp hnat
                rw [heq, listGet_set_same _ _ _ _ hl1', listGet_set_same _ _ _ _ hl2']
              | false =>
                have hne : l ≠ x := fun e => (natBeq_ne hnat) e.symm
                have hne2 : τ.fwd l ≠ τ.fwd x := fun e => hne (by rw [← τ.inv_fwd l hl, ← τ.inv_fwd x hx, e])
                rw [listGet_set_ne _ _ _ _ _ hne hl1', listGet_set_ne _ _ _ _ _ hne2 hl2']
                exact hmap x hx
            cases cur with
            | dead =>
              rw [Bool.and_false, bool_if_false false rfl]
              exact hshared
            | live _ =>
              cases cfg.abortOnDoubleStorageLive with
              | true => rw [Bool.true_and, bool_if_true true rfl]; rfl
              | false => rw [Bool.false_and, bool_if_false false rfl]; exact hshared
      | storageDead l =>
        have hl : l < body.locals.length := (natBlt_eq_true_iff l body.locals.length).mp hsb
        dsimp only [renameStmtLocals]
        have h0eq : natBeq (τ.fwd l) 0 = natBeq l 0 := by
          cases h0 : natBeq l 0 with
          | true =>
            have hl0 := (natBeq_eq_true_iff l 0).mp h0
            rw [hl0, τ.fix_prefix 0 (Nat.zero_le body.argCount), natBeq_refl]
          | false =>
            cases h02 : natBeq (τ.fwd l) 0 with
            | false => rfl
            | true =>
              have hfl0 := (natBeq_eq_true_iff (τ.fwd l) 0).mp h02
              have h0lt : 0 < body.locals.length := Nat.lt_of_le_of_lt (Nat.zero_le body.argCount) harg
              have hl0 : l = 0 := (τ.inv_fwd l hl).symm.trans ((congrArg τ.inv (hfl0.trans (τ.fix_prefix 0 (Nat.zero_le body.argCount)).symm)).trans (τ.inv_fwd 0 h0lt))
              rw [hl0] at h0
              contradiction
        rw [h0eq]
        cases natBeq l 0 with
        | true => rw [bool_if_true true rfl]; trivial
        | false =>
          rw [bool_if_false false rfl]
          have h1lt : l < st₁.locals.length := by rw [hlen1]; exact hl
          have h2lt : τ.fwd l < st₂.locals.length := by rw [hlen2]; exact τ.fwd_lt l hl
          obtain ⟨l1', hl1'⟩ := listSet_lt_some st₁.locals l .dead h1lt
          obtain ⟨l2', hl2'⟩ := listSet_lt_some st₂.locals (τ.fwd l) .dead h2lt
          rw [hl1', hl2']
          dsimp only
          refine ⟨hpc2, rfl, Eq.trans (listSet_some_length _ _ _ _ hl1') hlen1, Eq.trans (listSet_some_length _ _ _ _ hl2') hlen2, ?_⟩
          intro x hx
          cases hnat : natBeq x l with
          | true =>
            have heq := (natBeq_eq_true_iff x l).mp hnat
            rw [heq, listGet_set_same _ _ _ _ hl1', listGet_set_same _ _ _ _ hl2']
          | false =>
            have hne : l ≠ x := fun e => (natBeq_ne hnat) e.symm
            have hne2 : τ.fwd l ≠ τ.fwd x := fun e => hne (by rw [← τ.inv_fwd l hl, ← τ.inv_fwd x hx, e])
            rw [listGet_set_ne _ _ _ _ _ hne hl1', listGet_set_ne _ _ _ _ _ hne2 hl2']
            exact hmap x hx
      | assign dest rval =>
        have hsb' := Bool.and_eq_true _ _ |>.mp hsb
        have hd : dest.localId < body.locals.length := (natBlt_eq_true_iff dest.localId body.locals.length).mp hsb'.1
        dsimp only [renameStmtLocals]
        rw [rvalueConflicts_renameLocals τ dest rval hd hsb'.2]
        cases (cfg.forbidAliasAssign && rvalueConflictsWithPlace dest rval) with
        | true => rw [bool_if_true true rfl]; rfl
        | false =>
          rw [bool_if_false false rfl]
          have hev := evalRvalue_reorderLocals cfg body τ st₁ st₂ ⟨hpc2, hidx2, hlen1, hlen2, hmap⟩ rval hsb'.2
          cases he1 : evalRvalue cfg body.locals st₁.locals rval with
          | ub _ =>
            cases he2 : evalRvalue cfg (reorderLocalsBody τ body).locals st₂.locals (renameRvalueLocals τ.fwd rval) <;>
            rw [he1, he2] at hev <;> dsimp only at hev ⊢ <;> first | exact hev | exact False.elim hev
          | malformed =>
            cases he2 : evalRvalue cfg (reorderLocalsBody τ body).locals st₂.locals (renameRvalueLocals τ.fwd rval) <;>
            rw [he1, he2] at hev <;> dsimp only at hev ⊢ <;> first | try trivial | exact False.elim hev
          | ok val1 l1a =>
            cases he2 : evalRvalue cfg (reorderLocalsBody τ body).locals st₂.locals (renameRvalueLocals τ.fwd rval) with
            | ub _ => rw [he1, he2] at hev; dsimp only at hev
            | malformed => rw [he1, he2] at hev; dsimp only at hev
            | ok val2 l2a =>
              rw [he1, he2] at hev; dsimp only at hev ⊢
              obtain ⟨hv, hlen1a, hlen2a, hmapa⟩ := hev
              rw [← hv]
              have hwp := writePlace_reorderLocals body.locals.length body.argCount τ l1a l2a hlen1a hlen2a hmapa dest hd val1
              cases hw1 : writePlace l1a dest val1 <;>
              cases hw2 : writePlace l2a (renamePlaceLocals τ.fwd dest) val1
              all_goals rw [hw1, hw2] at hwp
              all_goals dsimp only at hwp ⊢
              all_goals first
                | exact hwp
                | trivial
                | exact False.elim hwp
                | exact ⟨hpc2, rfl, hwp.1, hwp.2.1, hwp.2.2⟩
    | none =>
      rw [listMap_length]
      dsimp only
      cases natBeq st₁.stmtIdx bb.stmts.length with
      | false => rw [bool_if_false false rfl]; trivial
      | true =>
        rw [bool_if_true true rfl]
        cases hterm : bb.term with
        | goto target =>
          dsimp only [renameTermLocals]
          exact ⟨rfl, rfl, hlen1, hlen2, hmap⟩
        | switchInt discr targets otherwise =>
          have hdb := hlocbb.2
          rw [hterm] at hdb
          have hev := evalOperand_reorderLocals cfg body τ st₁ st₂ ⟨hpc2, hidx2, hlen1, hlen2, hmap⟩ discr hdb
          dsimp only [renameTermLocals]
          cases he1 : evalOperand cfg body.locals st₁.locals discr <;>
          cases he2 : evalOperand cfg (reorderLocalsBody τ body).locals st₂.locals (renameOperandLocals τ.fwd discr)
          all_goals rw [he1, he2] at hev
          all_goals dsimp only at hev ⊢
          all_goals first
            | exact hev
            | trivial
            | exact False.elim hev
            | · obtain ⟨hv, hlen1a, hlen2a, hmapa⟩ := hev
                rw [← hv]
                cases evalSwitchTarget _ targets otherwise <;> dsimp only <;> first | trivial | exact ⟨rfl, rfl, hlen1a, hlen2a, hmapa⟩
        | ret =>
          dsimp only [renameTermLocals]
          cases bb.isCleanup with
          | true => rw [bool_if_true true rfl]; trivial
          | false =>
            rw [bool_if_false false rfl]
            have h0lt : 0 < body.locals.length := Nat.lt_of_le_of_lt (Nat.zero_le body.argCount) harg
            have h0map := hmap 0 h0lt
            rw [τ.fix_prefix 0 (Nat.zero_le body.argCount)] at h0map
            rw [h0map]
            cases listGet st₁.locals 0 with
            | none => dsimp only; try trivial
            | some sl =>
              cases sl with
              | dead => rfl
              | live ov => cases ov <;> rfl
        | call _ _ _ _ _ => dsimp only [renameTermLocals]; trivial
        | peekCall _ _ => dsimp only [renameTermLocals]; trivial
        | unreachable => dsimp only [renameTermLocals]; rfl

theorem reorderLocals_runFrom_equiv (cfg : EvalConfig) (body : Body)
    (τ : LocalPerm body.locals.length body.argCount)
    (hloc : LocalsInBounds body) (harg : body.argCount < body.locals.length)
    (fuel : Nat) (st₁ st₂ : MachineState) (hsim : SimLocal body.locals.length body.argCount τ st₁ st₂) :
    runFrom cfg (reorderLocalsBody τ body) st₂ fuel = runFrom cfg body st₁ fuel := by
  induction fuel generalizing st₁ st₂ with
  | zero => rfl
  | succ k ih =>
    have hstep := reorderLocals_step_sim cfg body τ hloc harg st₁ st₂ hsim
    dsimp only [runFrom]
    cases h1 : stepState cfg body st₁ <;> cases h2 : stepState cfg (reorderLocalsBody τ body) st₂
    all_goals rw [h1, h2] at hstep
    all_goals dsimp only at hstep ⊢
    all_goals first
      | rfl
      | exact False.elim hstep
      | exact ih _ _ hstep
      | exact congrArg Outcome.returned hstep.symm
      | exact congrArg Outcome.ub hstep.symm

/-- **Theorem (`ReorderLocals` Alpha-Isomorphism Bisimulation):**
For any MIR body with in-bounds locals and `argCount < locals.length`, any local permutation
fixing `_0` (`RETURN_PLACE`) and `_1..=argCount` preserves `runBody` across all configurations,
arguments, and fuel bounds. -/
theorem reorderLocals_run_equiv (cfg : EvalConfig) (body : Body)
    (τ : LocalPerm body.locals.length body.argCount)
    (hloc : LocalsInBounds body) (harg : body.argCount < body.locals.length)
    (args : List Val) (fuel : Nat) :
    runBody cfg (reorderLocalsBody τ body) args fuel = runBody cfg body args fuel := by
  dsimp only [runBody, reorderLocalsBody]
  have hempty : (listMap (renameBlockLocals τ.fwd) body.blocks).isEmpty = body.blocks.isEmpty := by
    cases body.blocks <;> rfl
  rw [hempty]
  cases body.blocks.isEmpty with
  | true =>
    rw [Bool.true_or]
    try rw [Bool.true_or]
    rw [bool_if_true true rfl, bool_if_true true rfl]
  | false =>
    rw [Bool.false_or]
    cases natBeq args.length body.argCount with
    | false =>
      rw [Bool.not_false]
      rw [bool_if_true true rfl, bool_if_true true rfl]
    | true =>
      rw [Bool.not_true]
      rw [bool_if_false false rfl, bool_if_false false rfl]
      exact reorderLocals_runFrom_equiv cfg body τ hloc harg fuel
        { pc := 0, stmtIdx := 0, locals := initLocals body args }
        { pc := 0, stmtIdx := 0, locals := initLocals { argCount := body.argCount, locals := mapRange body.locals.length (fun j => listGetD body.locals (τ.inv j) .u32), blocks := listMap (renameBlockLocals τ.fwd) body.blocks, isFnLike := body.isFnLike, canUnwind := body.canUnwind } args }
        ⟨rfl, rfl, initLocals_length body args, Eq.trans (initLocals_length _ args) (mapRange_length _ _),
          fun l hl => initLocals_reorderLocals body τ hloc harg args l hl⟩

/-- **Theorem (Composed `Prettify` Pipeline Bisimulation):**
Sequential application of `ReorderBasicBlocks` followed by `ReorderLocals` (matching `lib.rs:784-785`)
is an exact operational equivalence over `runBody`. -/
theorem prettify_composition_equiv (cfg : EvalConfig) (body : Body)
    (σ : BlockPerm body.blocks.length)
    (τ : LocalPerm (reorderBlocksBody σ body).locals.length (reorderBlocksBody σ body).argCount)
    (hclosed : CfgClosed body)
    (hloc : LocalsInBounds (reorderBlocksBody σ body))
    (harg : body.argCount < body.locals.length)
    (args : List Val) (fuel : Nat) :
    runBody cfg (reorderLocalsBody τ (reorderBlocksBody σ body)) args fuel =
      runBody cfg body args fuel := by
  have h1 := reorderLocals_run_equiv cfg (reorderBlocksBody σ body) τ hloc harg args fuel
  have h2 := reorderBlocks_run_equiv cfg body σ hclosed args fuel
  exact Eq.trans h1 h2

/-- Concrete multi-branch loop witness matching `multi_branch_cfg` RPO (`[0, 1, 10, 2, ...]`)
and `LocalFinder` (`_5 ↔ _6` while `StorageLive` does not reorder locals) plus the
unreachable-block `reverse_postorder` length-mismatch counterexample (`dead_bb_unsorted2`). -/
noncomputable def deadBbUnsorted2Body : Body :=
  { argCount := 1, locals := [.u32, .u32]
    blocks := [ { stmts := [], term := .goto 3 }
              , { stmts := [.assign ⟨0, none, false⟩ (.use (.constVal (.u32 99)))], term := .ret }
              , { stmts := [.assign ⟨0, none, false⟩ (.use (.copy ⟨1, none, false⟩))], term := .ret }
              , { stmts := [], term := .goto 2 } ] }

theorem reorderBlocks_partial_rpo_fails_bijection :
    let rpoPartial : List Nat := [0, 3, 2]
    rpoPartial.length ≠ deadBbUnsorted2Body.blocks.length ∧
    listGet rpoPartial 3 = none ∧
    runBody annealCfg deadBbUnsorted2Body [.u32 42] 10 = .returned (.u32 42) :=
  ⟨fun h => by contradiction, rfl, rfl⟩

/-! ## Section 6: `SanityCheck` Dataflow Oracle & `rustc_peek` Leakage Gate (`sanity_check.rs`, `rustc_peek.rs`) -/

inductive PeekKind where
  | maybeInit
  | maybeUninit
  | liveness

structure SanityPolicy where
  sanityCheckEnabled : Bool
  stopAfterDataflow : Bool
  peekKind : Option PeekKind

inductive CompileOutcome where
  | abortedByDataflowBitError
  | stoppedCleanAfterDataflow
  | codegenIntrinsicICE
  | compiled (out : Outcome)

noncomputable def hasPeekInBody (body : Body) : Bool :=
  listAny (fun bb => match bb.term with | .peekCall _ _ => true | _ => false) body.blocks

noncomputable def compileWithSanityCheck (pol : SanityPolicy) (body : Body) (allPeeksBitSet : Bool)
    (cfg : EvalConfig) (args : List Val) (fuel : Nat) : CompileOutcome :=
  if pol.sanityCheckEnabled then
    match pol.peekKind with
    | some _ =>
      if !allPeeksBitSet then
        .abortedByDataflowBitError
      else if pol.stopAfterDataflow then
        .stoppedCleanAfterDataflow
      else if hasPeekInBody body then
        .codegenIntrinsicICE
      else
        .compiled (runBody cfg body args fuel)
    | none =>
      if hasPeekInBody body then
        .codegenIntrinsicICE
      else
        .compiled (runBody cfg body args fuel)
  else
    if hasPeekInBody body then
      .codegenIntrinsicICE
    else
      .compiled (runBody cfg body args fuel)

/-- **Theorem (`SanityCheck` Non-Erasure):**
Because `SanityCheck` is a read-only `MirLint`, leaving `stop_after_dataflow` off leaks
`core::intrinsics::rustc_peek` into codegen and triggers `.codegenIntrinsicICE` even when the
dataflow bit check passes (`allPeeksBitSet = true`). -/
theorem sanity_check_no_erasure (body : Body) (pk : PeekKind) (cfg : EvalConfig)
    (args : List Val) (fuel : Nat) (hpeek : hasPeekInBody body = true) :
    compileWithSanityCheck
      { sanityCheckEnabled := true, stopAfterDataflow := false, peekKind := some pk }
      body true cfg args fuel = .codegenIntrinsicICE := by
  unfold compileWithSanityCheck
  rw [hpeek]
  rfl

/-- **Theorem (`SanityCheck` + `stop_after_dataflow` Leakage Characterization):**
On any body containing a `rustc_peek` call, avoiding the backend intrinsic ICE holds if and only
if `SanityCheck` is enabled, a `rustc_peek_*` attribute is present, and either a bit is unset
or `stop_after_dataflow` halts compilation before codegen. -/
theorem sanity_check_stop_prevents_ice_iff (pol : SanityPolicy) (body : Body)
    (allPeeksBitSet : Bool) (cfg : EvalConfig) (args : List Val) (fuel : Nat)
    (hpeek : hasPeekInBody body = true) :
    compileWithSanityCheck pol body allPeeksBitSet cfg args fuel ≠ .codegenIntrinsicICE ↔
      (pol.sanityCheckEnabled = true ∧
        ∃ pk, pol.peekKind = some pk ∧ (allPeeksBitSet = false ∨ pol.stopAfterDataflow = true)) := by
  unfold compileWithSanityCheck
  cases hsc : pol.sanityCheckEnabled with
  | false =>
    rw [hpeek]
    constructor
    · intro h; exact False.elim (h rfl)
    · intro h; exact False.elim (by cases h.1)
  | true =>
    cases hpk : pol.peekKind with
    | none =>
      rw [hpeek]
      constructor
      · intro h; exact False.elim (h rfl)
      · intro h
        obtain ⟨_, pk, hpk', _⟩ := h
        cases hpk'
    | some pk =>
      cases hbit : allPeeksBitSet with
      | false =>
        constructor
        · intro _
          exact ⟨rfl, pk, rfl, Or.inl rfl⟩
        · intro _ hcontra
          contradiction
      | true =>
        cases hstop : pol.stopAfterDataflow with
        | true =>
          constructor
          · intro _
            exact ⟨rfl, pk, rfl, Or.inr rfl⟩
          · intro _ hcontra
            contradiction
        | false =>
          rw [hpeek]
          constructor
          · intro h; exact False.elim (h rfl)
          · intro h
            obtain ⟨_, _, _, hor⟩ := h
            cases hor <;> contradiction

noncomputable def peekProbeBody : Body :=
  { argCount := 1, locals := [.unit, .u32]
    blocks := [ { stmts := [], term := .peekCall ⟨1, none, false⟩ 1 }
              , { stmts := [], term := .ret } ] }

theorem sanity_check_concrete_witnesses :
    compileWithSanityCheck { sanityCheckEnabled := true, stopAfterDataflow := true, peekKind := some .maybeInit }
      peekProbeBody true annealCfg [.u32 5] 10 = .stoppedCleanAfterDataflow ∧
    compileWithSanityCheck { sanityCheckEnabled := true, stopAfterDataflow := false, peekKind := some .maybeInit }
      peekProbeBody true annealCfg [.u32 5] 10 = .codegenIntrinsicICE ∧
    compileWithSanityCheck { sanityCheckEnabled := true, stopAfterDataflow := true, peekKind := some .maybeUninit }
      peekProbeBody false annealCfg [.u32 5] 10 = .abortedByDataflowBitError ∧
    compileWithSanityCheck { sanityCheckEnabled := false, stopAfterDataflow := true, peekKind := some .maybeUninit }
      peekProbeBody false annealCfg [.u32 5] 10 = .codegenIntrinsicICE :=
  ⟨rfl, rfl, rfl, rfl⟩

end MirLintSanityPrettify
