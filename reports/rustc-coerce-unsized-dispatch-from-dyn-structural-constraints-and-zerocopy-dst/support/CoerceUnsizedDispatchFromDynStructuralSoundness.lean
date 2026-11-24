/-
  CoerceUnsized, DispatchFromDyn, Tail-Only Unsize, and Zerocopy DST Soundness
  ============================================================================

  Kernel-checked Lean v4.34.1 mechanization (pure `prelude` + `Init.*` foundation;
  0 `sorry`, 0 `Classical.choice`, 0 `omega`, 0 `bv_decide`, 0 `native_decide`,
  0 `partial def`, 0 `._unsafe_rec`) modeling:

    1. Builtin `CoerceUnsized` structural checker (`E0374`, `E0375`, `E0377`,
       including non-struct enums/unions after folding legacy `E0376`) matching
       `compiler/rustc_hir_analysis/src/coherence/builtin.rs` (`rust-lang/rust`).
    2. Builtin `DispatchFromDyn` structural + 1-ZST + representation checker
       (`E0378`, `!ty.has_non_region_param()`, `layout.is_1zst()`, forbidding
       `#[repr(C)]` and `#[repr(packed)]`) and downstream `make_thin_self_ptr`
       ABI extraction (`compiler/rustc_ty_utils/src/abi.rs`).
    3. Builtin `Unsize` tail-only `?Sized` WF checks (`E0277`, `wfcheck.rs`) and
       `unsizing_params_for_adt` prefix exclusion (`rustc_ty_utils/src/ty.rs`,
       `rustc_trait_selection/src/traits/select/confirmation.rs`).
    4. Mechanized theorems:
       - Single-Field Unsize Structural Preservation
         (`coerceUnsized_single_field_preservation` +
          `coerceWitness_preserves_ptr_address`)
       - `DispatchFromDyn` ABI Register-Equivalence
         (`dispatchFromDyn_implies_coerceUnsized` +
          `dispatchFromDyn_strong_non_1zst` +
          `dispatchFromDyn_abi_register_equivalence` +
          `adding_1zst_siblings_preserves_thin_self_ptr`)
       - Tail-Only `?Sized` Prefix-Offset Invariance
         (`tail_only_unsized_prefix_offset_invariance` +
          `unsize_preserves_prefix_offsets`)
       - Necessity counterexamples for `E0374`, `E0375`, `E0377`, `E0378`,
         `E0277`, and prefix-parameter capture (`E0308`).
    5. Stable `zerocopy` slice-DST invariants (`Ref::from_bytes_with_elems`,
       `DstLayout::validate_cast_and_convert_metadata`) and the architectural
       `#[repr(C)]` disjointness (`repr_c_duality_disjoint` +
       `packet_repr_c_duality_witness`).
-/

prelude
import Init.Prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.List.Basic
import Init.Data.Option.Basic

namespace CoerceUnsizedDispatchFromDynStructuralSoundness

/-!
## Section 1: Pure `Bool`, `Nat`, Alignment, and `List` Helpers
-/

theorem boolAndLeft : ∀ {a b : Bool}, Bool.and a b = true → a = true
  | true, _, _ => rfl
  | false, _, h => Bool.noConfusion h

theorem boolAndRight : ∀ {a b : Bool}, Bool.and a b = true → b = true
  | true, true, _ => rfl
  | true, false, h => Bool.noConfusion h
  | false, _, h => Bool.noConfusion h

theorem boolAndIntro : ∀ {a b : Bool}, a = true → b = true → Bool.and a b = true
  | true, true, _, _ => rfl
  | false, _, h, _ => Bool.noConfusion h
  | true, false, _, h => Bool.noConfusion h

theorem natBeq_refl : ∀ (n : Nat), Nat.beq n n = true
  | 0 => rfl
  | Nat.succ k => natBeq_refl k

theorem natBeq_eq_true : ∀ {a b : Nat}, Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, Nat.succ _, h => by dsimp only [Nat.beq] at h; exact Bool.noConfusion h
  | Nat.succ _, 0, h => by dsimp only [Nat.beq] at h; exact Bool.noConfusion h
  | Nat.succ _, Nat.succ _, h => congrArg Nat.succ (natBeq_eq_true h)

theorem eq_imp_natBeq : ∀ {a b : Nat}, a = b → Nat.beq a b = true
  | a, _, rfl => natBeq_refl a

theorem natBeq_eq_true_iff (a b : Nat) : Nat.beq a b = true ↔ a = b :=
  ⟨natBeq_eq_true, eq_imp_natBeq⟩

theorem natBeq_symm : ∀ {a b : Nat}, Nat.beq a b = Nat.beq b a
  | 0, 0 => rfl
  | 0, Nat.succ _ => rfl
  | Nat.succ _, 0 => rfl
  | Nat.succ a, Nat.succ b => natBeq_symm (a := a) (b := b)

theorem nat_le_of_ble_false : ∀ {a b : Nat}, Nat.ble a b = false → b ≤ a
  | 0, _, h => Bool.noConfusion h
  | Nat.succ _, 0, _ => Nat.zero_le _
  | Nat.succ _, Nat.succ _, h => Nat.succ_le_succ (nat_le_of_ble_false h)

noncomputable def maxNat (a b : Nat) : Nat :=
  match Nat.ble a b with
  | true => b
  | false => a

noncomputable def minNat (a b : Nat) : Nat :=
  match Nat.ble a b with
  | true => a
  | false => b

theorem maxNat_ge_first : ∀ (a b : Nat), a ≤ maxNat a b := by
  intro a b
  dsimp only [maxNat]
  cases h : Nat.ble a b with
  | false => exact Nat.le_refl a
  | true => exact Nat.le_of_ble_eq_true h

theorem maxNat_ge_second : ∀ (a b : Nat), b ≤ maxNat a b := by
  intro a b
  dsimp only [maxNat]
  cases h : Nat.ble a b with
  | false => exact nat_le_of_ble_false h
  | true => exact Nat.le_refl b

theorem maxNat_ge_two_left : ∀ (a b : Nat), Nat.ble 2 a = true → Nat.ble 2 (maxNat a b) = true := by
  intro a b hge
  have ha : 2 ≤ a := Nat.le_of_ble_eq_true hge
  have hm : 2 ≤ maxNat a b := Nat.le_trans ha (maxNat_ge_first a b)
  exact Nat.ble_eq_true_of_le hm

theorem maxNat_ge_two_right : ∀ (a b : Nat), Nat.ble 2 b = true → Nat.ble 2 (maxNat a b) = true := by
  intro a b hge
  have hb : 2 ≤ b := Nat.le_of_ble_eq_true hge
  have hm : 2 ≤ maxNat a b := Nat.le_trans hb (maxNat_ge_second a b)
  exact Nat.ble_eq_true_of_le hm

noncomputable def alignUp (x a : Nat) : Nat :=
  match Nat.beq a 0 with
  | true => x
  | false =>
    let rem := Nat.mod x a
    match Nat.beq rem 0 with
    | true => x
    | false => x + (a - rem)

noncomputable def roundDown (x a : Nat) : Nat :=
  match Nat.beq a 0 with
  | true => x
  | false => x - Nat.mod x a

theorem alignUp_zero (x : Nat) : alignUp x 0 = x := rfl

theorem alignUp_ge (x a : Nat) : x ≤ alignUp x a := by
  dsimp only [alignUp]
  cases Nat.beq a 0 with
  | true => exact Nat.le_refl x
  | false =>
    cases Nat.beq (Nat.mod x a) 0 with
    | true => exact Nat.le_refl x
    | false => exact Nat.le_add_right x (a - Nat.mod x a)

theorem roundDown_le (x a : Nat) : roundDown x a ≤ x := by
  dsimp only [roundDown]
  cases Nat.beq a 0 with
  | true => exact Nat.le_refl x
  | false => exact Nat.sub_le x (Nat.mod x a)

noncomputable def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, Nat.succ i => listGet? xs i

noncomputable def listSet {α : Type} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, Nat.succ i, v => x :: listSet xs i v

theorem listSet_length {α : Type} : ∀ (xs : List α) (i : Nat) (v : α),
    (listSet xs i v).length = xs.length
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: xs, Nat.succ i, v => congrArg Nat.succ (listSet_length xs i v)

theorem listGet_listSet_eq {α : Type} : ∀ (xs : List α) (i : Nat) (old v : α),
    listGet? xs i = some old → listGet? (listSet xs i v) i = some v
  | [], _, _, _, h => by dsimp only [listGet?] at h; cases h
  | _ :: _, 0, _, _, _ => rfl
  | _ :: xs, Nat.succ i, old, v, h => listGet_listSet_eq xs i old v h

theorem listGet_listSet_ne {α : Type} : ∀ (xs : List α) (i j : Nat) (v : α),
    Nat.beq j i = false → listGet? (listSet xs i v) j = listGet? xs j
  | [], _, _, _, _ => rfl
  | _ :: _, 0, 0, _, h => Bool.noConfusion h
  | _ :: _, 0, Nat.succ _, _, _ => rfl
  | _ :: _, Nat.succ _, 0, _, _ => rfl
  | _ :: xs, Nat.succ i, Nat.succ j, v, h => listGet_listSet_ne xs i j v h

noncomputable def listContainsNat : List Nat → Nat → Bool
  | [], _ => false
  | x :: xs, y =>
    match Nat.beq x y with
    | true => true
    | false => listContainsNat xs y

theorem listContainsNat_append_left : ∀ (xs ys : List Nat) (p : Nat),
    listContainsNat xs p = true → listContainsNat (xs ++ ys) p = true
  | [], _, _, h => Bool.noConfusion h
  | x :: xs, ys, p, h => by
    dsimp only [listContainsNat] at h
    cases hx : Nat.beq x p with
    | true =>
      change (match Nat.beq x p with | true => true | false => listContainsNat (xs ++ ys) p) = true
      rw [hx]
    | false =>
      rw [hx] at h
      change (match Nat.beq x p with | true => true | false => listContainsNat (xs ++ ys) p) = true
      rw [hx]
      exact listContainsNat_append_left xs ys p h

theorem listContainsNat_append_right : ∀ (xs ys : List Nat) (p : Nat),
    listContainsNat ys p = true → listContainsNat (xs ++ ys) p = true
  | [], _, _, h => h
  | x :: xs, ys, p, h => by
    change (match Nat.beq x p with | true => true | false => listContainsNat (xs ++ ys) p) = true
    cases Nat.beq x p with
    | true => rfl
    | false => exact listContainsNat_append_right xs ys p h

noncomputable def filterNotIn (xs banned : List Nat) : List Nat :=
  match xs with
  | [] => []
  | x :: rest =>
    match listContainsNat banned x with
    | true => filterNotIn rest banned
    | false => x :: filterNotIn rest banned

theorem listContainsNat_true_of_mem_filterNotIn_false :
    ∀ (xs banned : List Nat) (p : Nat),
      listContainsNat (filterNotIn xs banned) p = true →
      listContainsNat banned p = false
  | [], _, _, h => Bool.noConfusion h
  | x :: rest, banned, p, h => by
    dsimp only [filterNotIn] at h
    cases hb : listContainsNat banned x with
    | true =>
      rw [hb] at h
      exact listContainsNat_true_of_mem_filterNotIn_false rest banned p h
    | false =>
      rw [hb] at h
      dsimp only [listContainsNat] at h
      cases hp : Nat.beq x p with
      | true =>
        have hxp : x = p := natBeq_eq_true hp
        rw [← hxp]
        exact hb
      | false =>
        rw [hp] at h
        exact listContainsNat_true_of_mem_filterNotIn_false rest banned p h

noncomputable def dropLast {α : Type} : List α → List α
  | [] => []
  | [_] => []
  | x :: y :: rest => x :: dropLast (y :: rest)

noncomputable def lastElem? {α : Type} : List α → Option α
  | [] => none
  | [x] => some x
  | _ :: y :: rest => lastElem? (y :: rest)

theorem dropLast_lastElem_length {α : Type} : ∀ (xs : List α) (t : α),
    lastElem? xs = some t → xs.length = (dropLast xs).length + 1
  | [], _, h => by dsimp only [lastElem?] at h; cases h
  | [_], _, _ => rfl
  | _ :: y :: rest, t, h => by
    have ih := dropLast_lastElem_length (y :: rest) t h
    dsimp only [dropLast, List.length]
    exact congrArg Nat.succ ih

theorem dropLast_append_singleton {α : Type} : ∀ (xs : List α) (t : α),
    dropLast (xs ++ [t]) = xs
  | [], _ => rfl
  | [_], _ => rfl
  | x :: y :: rest, t => by
    have ih := dropLast_append_singleton (y :: rest) t
    change x :: dropLast ((y :: rest) ++ [t]) = x :: (y :: rest)
    exact congrArg (List.cons x) ih

theorem lastElem_append_singleton {α : Type} : ∀ (xs : List α) (t : α),
    lastElem? (xs ++ [t]) = some t
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: y :: rest, t => lastElem_append_singleton (y :: rest) t

noncomputable def allBool {α : Type} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => Bool.and (p x) (allBool p xs)

/-!
## Section 2: Mutability, Type AST, Syntactic Equality, Params, and Substitution
-/

inductive Mutability where
  | imm : Mutability
  | mutbl : Mutability

noncomputable def mutBeq : Mutability → Mutability → Bool
  | .imm, .imm => true
  | .mutbl, .mutbl => true
  | _, _ => false

theorem mutBeq_refl : ∀ (m : Mutability), mutBeq m m = true
  | .imm => rfl
  | .mutbl => rfl

theorem mutBeq_eq_true : ∀ {m1 m2 : Mutability}, mutBeq m1 m2 = true → m1 = m2
  | .imm, .imm, _ => rfl
  | .mutbl, .mutbl, _ => rfl
  | .imm, .mutbl, h => Bool.noConfusion h
  | .mutbl, .imm, h => Bool.noConfusion h

/-- Models `mt_a.mutbl >= mt_b.mutbl` in `compiler/rustc_hir_analysis/src/coherence/builtin.rs`
    allowing `&mut -> &`, `&mut -> *const`, `&mut -> *mut`, `& -> *const`, `*mut -> *const`,
    while rejecting `*const -> *mut` and `& -> &mut`. -/
noncomputable def mutCoercible : Mutability → Mutability → Bool
  | .mutbl, _ => true
  | .imm, .imm => true
  | .imm, .mutbl => false

theorem mutBeq_implies_mutCoercible : ∀ {m1 m2 : Mutability},
    mutBeq m1 m2 = true → mutCoercible m1 m2 = true
  | .imm, .imm, _ => rfl
  | .mutbl, .mutbl, _ => rfl
  | .imm, .mutbl, h => Bool.noConfusion h
  | .mutbl, .imm, h => Bool.noConfusion h

inductive Ty where
  | unit : Ty
  | scalar : Nat → Nat → Nat → Ty
  | param : Nat → Ty
  | region : Nat → Ty
  | array : Ty → Nat → Ty
  | slice : Ty → Ty
  | ref : Nat → Mutability → Ty → Ty
  | rawPtr : Mutability → Ty → Ty
  | phantom : Ty → Ty
  | adt : Nat → List Ty → Ty
  | traitObj : Nat → Ty

mutual
noncomputable def tyBeq : Ty → Ty → Bool
  | .unit, .unit => true
  | .scalar id1 s1 a1, .scalar id2 s2 a2 =>
    Bool.and (Nat.beq id1 id2) (Bool.and (Nat.beq s1 s2) (Nat.beq a1 a2))
  | .param i1, .param i2 => Nat.beq i1 i2
  | .region r1, .region r2 => Nat.beq r1 r2
  | .array e1 n1, .array e2 n2 => Bool.and (tyBeq e1 e2) (Nat.beq n1 n2)
  | .slice e1, .slice e2 => tyBeq e1 e2
  | .ref r1 m1 p1, .ref r2 m2 p2 =>
    Bool.and (Nat.beq r1 r2) (Bool.and (mutBeq m1 m2) (tyBeq p1 p2))
  | .rawPtr m1 p1, .rawPtr m2 p2 =>
    Bool.and (mutBeq m1 m2) (tyBeq p1 p2)
  | .phantom inner1, .phantom inner2 => tyBeq inner1 inner2
  | .adt d1 args1, .adt d2 args2 =>
    Bool.and (Nat.beq d1 d2) (tyListBeq args1 args2)
  | .traitObj t1, .traitObj t2 => Nat.beq t1 t2
  | _, _ => false

noncomputable def tyListBeq : List Ty → List Ty → Bool
  | [], [] => true
  | x :: xs, y :: ys => Bool.and (tyBeq x y) (tyListBeq xs ys)
  | _, _ => false
end

mutual
theorem tyBeq_refl : ∀ (t : Ty), tyBeq t t = true
  | .unit => rfl
  | .scalar id s a => by
    dsimp only [tyBeq]
    exact boolAndIntro (natBeq_refl id) (boolAndIntro (natBeq_refl s) (natBeq_refl a))
  | .param i => natBeq_refl i
  | .region r => natBeq_refl r
  | .array e n => boolAndIntro (tyBeq_refl e) (natBeq_refl n)
  | .slice e => tyBeq_refl e
  | .ref r m p => by
    dsimp only [tyBeq]
    exact boolAndIntro (natBeq_refl r) (boolAndIntro (mutBeq_refl m) (tyBeq_refl p))
  | .rawPtr m p => boolAndIntro (mutBeq_refl m) (tyBeq_refl p)
  | .phantom inner => tyBeq_refl inner
  | .adt d args => boolAndIntro (natBeq_refl d) (tyListBeq_refl args)
  | .traitObj t => natBeq_refl t

theorem tyListBeq_refl : ∀ (ts : List Ty), tyListBeq ts ts = true
  | [] => rfl
  | t :: ts => boolAndIntro (tyBeq_refl t) (tyListBeq_refl ts)
end

mutual
theorem tyBeq_eq_true : ∀ {t1 t2 : Ty}, tyBeq t1 t2 = true → t1 = t2
  | .unit, .unit, _ => rfl
  | .scalar id1 s1 a1, .scalar id2 s2 a2, h => by
    dsimp only [tyBeq] at h
    have hid := natBeq_eq_true (boolAndLeft h)
    have hrest := boolAndRight h
    have hs := natBeq_eq_true (boolAndLeft hrest)
    have ha := natBeq_eq_true (boolAndRight hrest)
    rw [hid, hs, ha]
  | .param _, .param _, h => congrArg Ty.param (natBeq_eq_true h)
  | .region _, .region _, h => congrArg Ty.region (natBeq_eq_true h)
  | .array e1 n1, .array e2 n2, h => by
    dsimp only [tyBeq] at h
    have he := tyBeq_eq_true (boolAndLeft h)
    have hn := natBeq_eq_true (boolAndRight h)
    rw [he, hn]
  | .slice _, .slice _, h => congrArg Ty.slice (tyBeq_eq_true h)
  | .ref r1 m1 p1, .ref r2 m2 p2, h => by
    dsimp only [tyBeq] at h
    have hr := natBeq_eq_true (boolAndLeft h)
    have hrest := boolAndRight h
    have hm := mutBeq_eq_true (boolAndLeft hrest)
    have hp := tyBeq_eq_true (boolAndRight hrest)
    rw [hr, hm, hp]
  | .rawPtr m1 p1, .rawPtr m2 p2, h => by
    dsimp only [tyBeq] at h
    have hm := mutBeq_eq_true (boolAndLeft h)
    have hp := tyBeq_eq_true (boolAndRight h)
    rw [hm, hp]
  | .phantom _, .phantom _, h => congrArg Ty.phantom (tyBeq_eq_true h)
  | .adt d1 args1, .adt d2 args2, h => by
    dsimp only [tyBeq] at h
    have hd := natBeq_eq_true (boolAndLeft h)
    have hargs := tyListBeq_eq_true (boolAndRight h)
    rw [hd, hargs]
  | .traitObj _, .traitObj _, h => congrArg Ty.traitObj (natBeq_eq_true h)
  | .unit, .scalar _ _ _, h => Bool.noConfusion h
  | .unit, .param _, h => Bool.noConfusion h
  | .unit, .region _, h => Bool.noConfusion h
  | .unit, .array _ _, h => Bool.noConfusion h
  | .unit, .slice _, h => Bool.noConfusion h
  | .unit, .ref _ _ _, h => Bool.noConfusion h
  | .unit, .rawPtr _ _, h => Bool.noConfusion h
  | .unit, .phantom _, h => Bool.noConfusion h
  | .unit, .adt _ _, h => Bool.noConfusion h
  | .unit, .traitObj _, h => Bool.noConfusion h
  | .scalar _ _ _, .unit, h => Bool.noConfusion h
  | .scalar _ _ _, .param _, h => Bool.noConfusion h
  | .scalar _ _ _, .region _, h => Bool.noConfusion h
  | .scalar _ _ _, .array _ _, h => Bool.noConfusion h
  | .scalar _ _ _, .slice _, h => Bool.noConfusion h
  | .scalar _ _ _, .ref _ _ _, h => Bool.noConfusion h
  | .scalar _ _ _, .rawPtr _ _, h => Bool.noConfusion h
  | .scalar _ _ _, .phantom _, h => Bool.noConfusion h
  | .scalar _ _ _, .adt _ _, h => Bool.noConfusion h
  | .scalar _ _ _, .traitObj _, h => Bool.noConfusion h
  | .param _, .unit, h => Bool.noConfusion h
  | .param _, .scalar _ _ _, h => Bool.noConfusion h
  | .param _, .region _, h => Bool.noConfusion h
  | .param _, .array _ _, h => Bool.noConfusion h
  | .param _, .slice _, h => Bool.noConfusion h
  | .param _, .ref _ _ _, h => Bool.noConfusion h
  | .param _, .rawPtr _ _, h => Bool.noConfusion h
  | .param _, .phantom _, h => Bool.noConfusion h
  | .param _, .adt _ _, h => Bool.noConfusion h
  | .param _, .traitObj _, h => Bool.noConfusion h
  | .region _, .unit, h => Bool.noConfusion h
  | .region _, .scalar _ _ _, h => Bool.noConfusion h
  | .region _, .param _, h => Bool.noConfusion h
  | .region _, .array _ _, h => Bool.noConfusion h
  | .region _, .slice _, h => Bool.noConfusion h
  | .region _, .ref _ _ _, h => Bool.noConfusion h
  | .region _, .rawPtr _ _, h => Bool.noConfusion h
  | .region _, .phantom _, h => Bool.noConfusion h
  | .region _, .adt _ _, h => Bool.noConfusion h
  | .region _, .traitObj _, h => Bool.noConfusion h
  | .array _ _, .unit, h => Bool.noConfusion h
  | .array _ _, .scalar _ _ _, h => Bool.noConfusion h
  | .array _ _, .param _, h => Bool.noConfusion h
  | .array _ _, .region _, h => Bool.noConfusion h
  | .array _ _, .slice _, h => Bool.noConfusion h
  | .array _ _, .ref _ _ _, h => Bool.noConfusion h
  | .array _ _, .rawPtr _ _, h => Bool.noConfusion h
  | .array _ _, .phantom _, h => Bool.noConfusion h
  | .array _ _, .adt _ _, h => Bool.noConfusion h
  | .array _ _, .traitObj _, h => Bool.noConfusion h
  | .slice _, .unit, h => Bool.noConfusion h
  | .slice _, .scalar _ _ _, h => Bool.noConfusion h
  | .slice _, .param _, h => Bool.noConfusion h
  | .slice _, .region _, h => Bool.noConfusion h
  | .slice _, .array _ _, h => Bool.noConfusion h
  | .slice _, .ref _ _ _, h => Bool.noConfusion h
  | .slice _, .rawPtr _ _, h => Bool.noConfusion h
  | .slice _, .phantom _, h => Bool.noConfusion h
  | .slice _, .adt _ _, h => Bool.noConfusion h
  | .slice _, .traitObj _, h => Bool.noConfusion h
  | .ref _ _ _, .unit, h => Bool.noConfusion h
  | .ref _ _ _, .scalar _ _ _, h => Bool.noConfusion h
  | .ref _ _ _, .param _, h => Bool.noConfusion h
  | .ref _ _ _, .region _, h => Bool.noConfusion h
  | .ref _ _ _, .array _ _, h => Bool.noConfusion h
  | .ref _ _ _, .slice _, h => Bool.noConfusion h
  | .ref _ _ _, .rawPtr _ _, h => Bool.noConfusion h
  | .ref _ _ _, .phantom _, h => Bool.noConfusion h
  | .ref _ _ _, .adt _ _, h => Bool.noConfusion h
  | .ref _ _ _, .traitObj _, h => Bool.noConfusion h
  | .rawPtr _ _, .unit, h => Bool.noConfusion h
  | .rawPtr _ _, .scalar _ _ _, h => Bool.noConfusion h
  | .rawPtr _ _, .param _, h => Bool.noConfusion h
  | .rawPtr _ _, .region _, h => Bool.noConfusion h
  | .rawPtr _ _, .array _ _, h => Bool.noConfusion h
  | .rawPtr _ _, .slice _, h => Bool.noConfusion h
  | .rawPtr _ _, .ref _ _ _, h => Bool.noConfusion h
  | .rawPtr _ _, .phantom _, h => Bool.noConfusion h
  | .rawPtr _ _, .adt _ _, h => Bool.noConfusion h
  | .rawPtr _ _, .traitObj _, h => Bool.noConfusion h
  | .phantom _, .unit, h => Bool.noConfusion h
  | .phantom _, .scalar _ _ _, h => Bool.noConfusion h
  | .phantom _, .param _, h => Bool.noConfusion h
  | .phantom _, .region _, h => Bool.noConfusion h
  | .phantom _, .array _ _, h => Bool.noConfusion h
  | .phantom _, .slice _, h => Bool.noConfusion h
  | .phantom _, .ref _ _ _, h => Bool.noConfusion h
  | .phantom _, .rawPtr _ _, h => Bool.noConfusion h
  | .phantom _, .adt _ _, h => Bool.noConfusion h
  | .phantom _, .traitObj _, h => Bool.noConfusion h
  | .adt _ _, .unit, h => Bool.noConfusion h
  | .adt _ _, .scalar _ _ _, h => Bool.noConfusion h
  | .adt _ _, .param _, h => Bool.noConfusion h
  | .adt _ _, .region _, h => Bool.noConfusion h
  | .adt _ _, .array _ _, h => Bool.noConfusion h
  | .adt _ _, .slice _, h => Bool.noConfusion h
  | .adt _ _, .ref _ _ _, h => Bool.noConfusion h
  | .adt _ _, .rawPtr _ _, h => Bool.noConfusion h
  | .adt _ _, .phantom _, h => Bool.noConfusion h
  | .adt _ _, .traitObj _, h => Bool.noConfusion h
  | .traitObj _, .unit, h => Bool.noConfusion h
  | .traitObj _, .scalar _ _ _, h => Bool.noConfusion h
  | .traitObj _, .param _, h => Bool.noConfusion h
  | .traitObj _, .region _, h => Bool.noConfusion h
  | .traitObj _, .array _ _, h => Bool.noConfusion h
  | .traitObj _, .slice _, h => Bool.noConfusion h
  | .traitObj _, .ref _ _ _, h => Bool.noConfusion h
  | .traitObj _, .rawPtr _ _, h => Bool.noConfusion h
  | .traitObj _, .phantom _, h => Bool.noConfusion h
  | .traitObj _, .adt _ _, h => Bool.noConfusion h

theorem tyListBeq_eq_true : ∀ {ts1 ts2 : List Ty}, tyListBeq ts1 ts2 = true → ts1 = ts2
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | x :: xs, y :: ys, h => by
    dsimp only [tyListBeq] at h
    have hx := tyBeq_eq_true (boolAndLeft h)
    have hxs := tyListBeq_eq_true (boolAndRight h)
    rw [hx, hxs]
end

theorem tyBeq_eq_iff (t1 t2 : Ty) : tyBeq t1 t2 = true ↔ t1 = t2 :=
  ⟨tyBeq_eq_true, fun h => by rw [h]; exact tyBeq_refl t2⟩

mutual
noncomputable def hasNonRegionParam : Ty → Bool
  | .unit => false
  | .scalar _ _ _ => false
  | .param _ => true
  | .region _ => false
  | .array e _ => hasNonRegionParam e
  | .slice e => hasNonRegionParam e
  | .ref _ _ p => hasNonRegionParam p
  | .rawPtr _ p => hasNonRegionParam p
  | .phantom inner => hasNonRegionParam inner
  | .adt _ args => hasNonRegionParamList args
  | .traitObj _ => false

noncomputable def hasNonRegionParamList : List Ty → Bool
  | [] => false
  | t :: ts =>
    match hasNonRegionParam t with
    | true => true
    | false => hasNonRegionParamList ts
end

mutual
noncomputable def paramOccursInTy (p : Nat) : Ty → Bool
  | .unit => false
  | .scalar _ _ _ => false
  | .param idx => Nat.beq p idx
  | .region _ => false
  | .array e _ => paramOccursInTy p e
  | .slice e => paramOccursInTy p e
  | .ref _ _ pt => paramOccursInTy p pt
  | .rawPtr _ pt => paramOccursInTy p pt
  | .phantom inner => paramOccursInTy p inner
  | .adt _ args => paramOccursInList p args
  | .traitObj _ => false

noncomputable def paramOccursInList (p : Nat) : List Ty → Bool
  | [] => false
  | t :: ts =>
    match paramOccursInTy p t with
    | true => true
    | false => paramOccursInList p ts
end

mutual
noncomputable def collectParamsTy : Ty → List Nat
  | .unit => []
  | .scalar _ _ _ => []
  | .param idx => [idx]
  | .region _ => []
  | .array e _ => collectParamsTy e
  | .slice e => collectParamsTy e
  | .ref _ _ pt => collectParamsTy pt
  | .rawPtr _ pt => collectParamsTy pt
  | .phantom inner => collectParamsTy inner
  | .adt _ args => collectParamsList args
  | .traitObj _ => []

noncomputable def collectParamsList : List Ty → List Nat
  | [] => []
  | t :: ts => collectParamsTy t ++ collectParamsList ts
end

mutual
theorem paramOccursInTy_implies_mem_collectParams :
    ∀ (t : Ty) (p : Nat),
      paramOccursInTy p t = true → listContainsNat (collectParamsTy t) p = true
  | .unit, _, h => Bool.noConfusion h
  | .scalar _ _ _, _, h => Bool.noConfusion h
  | .param idx, p, h => by
    dsimp only [paramOccursInTy] at h
    dsimp only [collectParamsTy, listContainsNat]
    rw [natBeq_symm, h]
  | .region _, _, h => Bool.noConfusion h
  | .array e _, p, h => paramOccursInTy_implies_mem_collectParams e p h
  | .slice e, p, h => paramOccursInTy_implies_mem_collectParams e p h
  | .ref _ _ pt, p, h => paramOccursInTy_implies_mem_collectParams pt p h
  | .rawPtr _ pt, p, h => paramOccursInTy_implies_mem_collectParams pt p h
  | .phantom inner, p, h => paramOccursInTy_implies_mem_collectParams inner p h
  | .adt _ args, p, h => paramOccursInList_implies_mem_collectParams args p h
  | .traitObj _, _, h => Bool.noConfusion h

theorem paramOccursInList_implies_mem_collectParams :
    ∀ (ts : List Ty) (p : Nat),
      paramOccursInList p ts = true → listContainsNat (collectParamsList ts) p = true
  | [], _, h => Bool.noConfusion h
  | t :: ts, p, h => by
    dsimp only [paramOccursInList] at h
    dsimp only [collectParamsList]
    cases ht : paramOccursInTy p t with
    | true =>
      exact listContainsNat_append_left (collectParamsTy t) (collectParamsList ts) p
        (paramOccursInTy_implies_mem_collectParams t p ht)
    | false =>
      rw [ht] at h
      exact listContainsNat_append_right (collectParamsTy t) (collectParamsList ts) p
        (paramOccursInList_implies_mem_collectParams ts p h)
end

mutual
noncomputable def substTy (args : List Ty) : Ty → Ty
  | .unit => .unit
  | .scalar id s a => .scalar id s a
  | .param idx =>
    match listGet? args idx with
    | some replacement => replacement
    | none => .param idx
  | .region r => .region r
  | .array e n => .array (substTy args e) n
  | .slice e => .slice (substTy args e)
  | .ref r m pt => .ref r m (substTy args pt)
  | .rawPtr m pt => .rawPtr m (substTy args pt)
  | .phantom inner => .phantom (substTy args inner)
  | .adt d subArgs => .adt d (substTyList args subArgs)
  | .traitObj t => .traitObj t

noncomputable def substTyList (args : List Ty) : List Ty → List Ty
  | [] => []
  | t :: ts => substTy args t :: substTyList args ts
end

mutual
theorem substTy_irrelevant_of_agree :
    ∀ (t : Ty) (args1 args2 : List Ty),
      (∀ p, paramOccursInTy p t = true → listGet? args1 p = listGet? args2 p) →
      substTy args1 t = substTy args2 t
  | .unit, _, _, _ => rfl
  | .scalar _ _ _, _, _, _ => rfl
  | .param idx, args1, args2, h => by
    dsimp only [substTy]
    have hOcc : paramOccursInTy idx (.param idx) = true := natBeq_refl idx
    have hEq := h idx hOcc
    rw [hEq]
  | .region _, _, _, _ => rfl
  | .array e n, args1, args2, h => by
    dsimp only [substTy]
    exact congrArg (fun x => Ty.array x n) (substTy_irrelevant_of_agree e args1 args2 h)
  | .slice e, args1, args2, h => by
    dsimp only [substTy]
    exact congrArg Ty.slice (substTy_irrelevant_of_agree e args1 args2 h)
  | .ref r m pt, args1, args2, h => by
    dsimp only [substTy]
    exact congrArg (Ty.ref r m) (substTy_irrelevant_of_agree pt args1 args2 h)
  | .rawPtr m pt, args1, args2, h => by
    dsimp only [substTy]
    exact congrArg (Ty.rawPtr m) (substTy_irrelevant_of_agree pt args1 args2 h)
  | .phantom inner, args1, args2, h => by
    dsimp only [substTy]
    exact congrArg Ty.phantom (substTy_irrelevant_of_agree inner args1 args2 h)
  | .adt d subArgs, args1, args2, h => by
    dsimp only [substTy]
    exact congrArg (Ty.adt d) (substTyList_irrelevant_of_agree subArgs args1 args2 h)
  | .traitObj _, _, _, _ => rfl

theorem substTyList_irrelevant_of_agree :
    ∀ (ts : List Ty) (args1 args2 : List Ty),
      (∀ p, paramOccursInList p ts = true → listGet? args1 p = listGet? args2 p) →
      substTyList args1 ts = substTyList args2 ts
  | [], _, _, _ => rfl
  | t :: ts, args1, args2, h => by
    dsimp only [substTyList]
    have ht : ∀ p, paramOccursInTy p t = true → listGet? args1 p = listGet? args2 p := by
      intro p hp
      apply h p
      dsimp only [paramOccursInList]
      rw [hp]
    have hts : ∀ p, paramOccursInList p ts = true → listGet? args1 p = listGet? args2 p := by
      intro p hp
      apply h p
      dsimp only [paramOccursInList]
      cases hpt : paramOccursInTy p t with
      | true => rfl
      | false => dsimp only; exact hp
    have eq1 := substTy_irrelevant_of_agree t args1 args2 ht
    have eq2 := substTyList_irrelevant_of_agree ts args1 args2 hts
    rw [eq1, eq2]
end

/-!
## Section 3: ADT Definitions, Structural Layout, 1-ZST Calculus, & Prefix Offsets
-/

inductive AdtKind where
  | structKind : AdtKind
  | enumKind : AdtKind
  | unionKind : AdtKind

inductive ReprKind where
  | reprRust : ReprKind
  | reprC : ReprKind
  | reprPacked : Nat → ReprKind
  | reprTransparent : ReprKind

noncomputable def reprAllowedForDispatch : ReprKind → Bool
  | .reprRust => true
  | .reprTransparent => true
  | .reprC => false
  | .reprPacked _ => false

structure FieldDef where
  fieldId : Nat
  rawTy : Ty

structure AdtDef where
  defId : Nat
  kind : AdtKind
  repr : ReprKind
  numParams : Nat
  fields : List FieldDef
  isLangPhantom : Bool

structure TraitImpl where
  concreteTy : Ty
  traitId : Nat
  vtableId : Nat

structure TypeEnv where
  adts : List AdtDef
  traitImpls : List TraitImpl
  regionSub : Nat → Nat → Bool

noncomputable def lookupAdt : List AdtDef → Nat → Option AdtDef
  | [], _ => none
  | d :: ds, targetId =>
    match Nat.beq d.defId targetId with
    | true => some d
    | false => lookupAdt ds targetId

noncomputable def findTraitImpl : List TraitImpl → Ty → Nat → Option Nat
  | [], _, _ => none
  | imp :: rest, cTy, tId =>
    match Bool.and (Nat.beq imp.traitId tId) (tyBeq imp.concreteTy cTy) with
    | true => some imp.vtableId
    | false => findTraitImpl rest cTy tId

noncomputable def isPhantomTy (env : TypeEnv) : Ty → Bool
  | .phantom _ => true
  | .adt defId _ =>
    match lookupAdt env.adts defId with
    | some d => d.isLangPhantom
    | none => false
  | _ => false

structure TyLayout where
  isSized : Bool
  byteSize : Nat
  byteAlign : Nat
  isZeroSized : Bool
  is1Zst : Bool

noncomputable def combineAdtFieldLayouts (curSize curAlign : Nat)
    (fieldLayouts : List TyLayout) (repr : ReprKind) : TyLayout :=
  match fieldLayouts with
  | [] =>
    let al := match repr with
      | .reprPacked p => minNat curAlign p
      | _ => curAlign
    let finalSz := match repr with
      | .reprPacked p => alignUp curSize (minNat curAlign p)
      | _ => alignUp curSize al
    { isSized := true
    , byteSize := finalSz
    , byteAlign := al
    , isZeroSized := Nat.beq finalSz 0
    , is1Zst := Bool.and (Nat.beq finalSz 0) (Nat.beq al 1) }
  | fl :: rest =>
    match fl.isSized with
    | true =>
      let fAlign := match repr with
        | .reprPacked p => minNat fl.byteAlign p
        | _ => fl.byteAlign
      let aligned := alignUp curSize fAlign
      let nextSize := aligned + fl.byteSize
      let nextAlign := maxNat curAlign fAlign
      combineAdtFieldLayouts nextSize nextAlign rest repr
    | false =>
      let fAlign := match repr with
        | .reprPacked p => minNat fl.byteAlign p
        | _ => fl.byteAlign
      let aligned := alignUp curSize fAlign
      let totalAlign := maxNat curAlign fAlign
      { isSized := false
      , byteSize := aligned
      , byteAlign := totalAlign
      , isZeroSized := false
      , is1Zst := false }

noncomputable def evalFieldsLayout (evalTy : Ty → TyLayout) (args : List Ty) : List FieldDef → List TyLayout
  | [] => []
  | f :: fs => evalTy (substTy args f.rawTy) :: evalFieldsLayout evalTy args fs

noncomputable def layoutOfFuel (adts : List AdtDef) : Nat → Ty → TyLayout
  | 0, _ => { isSized := true, byteSize := 0, byteAlign := 1, isZeroSized := false, is1Zst := false }
  | Nat.succ fuel, ty =>
    match ty with
    | .unit => { isSized := true, byteSize := 0, byteAlign := 1, isZeroSized := true, is1Zst := true }
    | .scalar _ sz al =>
      { isSized := true
      , byteSize := sz
      , byteAlign := al
      , isZeroSized := Nat.beq sz 0
      , is1Zst := Bool.and (Nat.beq sz 0) (Nat.beq al 1) }
    | .param _ =>
      { isSized := true, byteSize := 0, byteAlign := 1, isZeroSized := false, is1Zst := false }
    | .region _ =>
      { isSized := true, byteSize := 0, byteAlign := 1, isZeroSized := false, is1Zst := false }
    | .phantom _ =>
      { isSized := true, byteSize := 0, byteAlign := 1, isZeroSized := true, is1Zst := true }
    | .slice elem =>
      let el := layoutOfFuel adts fuel elem
      { isSized := false, byteSize := 0, byteAlign := el.byteAlign, isZeroSized := false, is1Zst := false }
    | .traitObj _ =>
      { isSized := false, byteSize := 0, byteAlign := 1, isZeroSized := false, is1Zst := false }
    | .array elem len =>
      let el := layoutOfFuel adts fuel elem
      let stride := alignUp el.byteSize el.byteAlign
      let sz := stride * len
      let al := el.byteAlign
      { isSized := el.isSized
      , byteSize := sz
      , byteAlign := al
      , isZeroSized := Bool.and el.isSized (Nat.beq sz 0)
      , is1Zst := Bool.and el.isSized (Bool.and (Nat.beq sz 0) (Nat.beq al 1)) }
    | .ref _ _ pt =>
      let pl := layoutOfFuel adts fuel pt
      let sz := match pl.isSized with | true => 8 | false => 16
      { isSized := true, byteSize := sz, byteAlign := 8, isZeroSized := false, is1Zst := false }
    | .rawPtr _ pt =>
      let pl := layoutOfFuel adts fuel pt
      let sz := match pl.isSized with | true => 8 | false => 16
      { isSized := true, byteSize := sz, byteAlign := 8, isZeroSized := false, is1Zst := false }
    | .adt defId args =>
      match lookupAdt adts defId with
      | none =>
        { isSized := true, byteSize := 0, byteAlign := 1, isZeroSized := false, is1Zst := false }
      | some d =>
        match d.isLangPhantom with
        | true =>
          { isSized := true, byteSize := 0, byteAlign := 1, isZeroSized := true, is1Zst := true }
        | false =>
          let fieldLays := evalFieldsLayout (layoutOfFuel adts fuel) args d.fields
          combineAdtFieldLayouts 0 1 fieldLays d.repr

noncomputable def computePrefixOffsets (adts : List AdtDef) (fuel : Nat) (repr : ReprKind)
    (args : List Ty) (curSize curAlign : Nat) : List FieldDef → Option (List Nat × Nat × Nat)
  | [] => some ([], curSize, curAlign)
  | f :: fs =>
    let fl := layoutOfFuel adts fuel (substTy args f.rawTy)
    match fl.isSized with
    | false => none
    | true =>
      let fAlign := match repr with
        | .reprPacked p => minNat fl.byteAlign p
        | _ => fl.byteAlign
      let off := alignUp curSize fAlign
      let nextSize := off + fl.byteSize
      let nextAlign := maxNat curAlign fAlign
      match computePrefixOffsets adts fuel repr args nextSize nextAlign fs with
      | none => none
      | some (offs, totSz, totAl) => some (off :: offs, totSz, totAl)

theorem computePrefixOffsets_invariance_aux :
    ∀ (fs : List FieldDef) (adts : List AdtDef) (fuel : Nat)
      (repr : ReprKind) (args1 args2 : List Ty) (curSize curAlign : Nat),
      (∀ p, paramOccursInList p (fs.map FieldDef.rawTy) = true →
        listGet? args1 p = listGet? args2 p) →
      computePrefixOffsets adts fuel repr args1 curSize curAlign fs =
      computePrefixOffsets adts fuel repr args2 curSize curAlign fs
  | [], _, _, _, _, _, _, _, _ => rfl
  | f :: rest, adts, fuel, repr, args1, args2, curSize, curAlign, hAgree => by
    have hHead : ∀ p, paramOccursInTy p f.rawTy = true → listGet? args1 p = listGet? args2 p := by
      intro p hp
      apply hAgree p
      dsimp only [List.map, paramOccursInList]
      rw [hp]
    have hTail : ∀ p, paramOccursInList p (rest.map FieldDef.rawTy) = true →
        listGet? args1 p = listGet? args2 p := by
      intro p hp
      apply hAgree p
      dsimp only [List.map, paramOccursInList]
      cases hf : paramOccursInTy p f.rawTy with
      | true => rfl
      | false => dsimp only; exact hp
    have hSubst : substTy args1 f.rawTy = substTy args2 f.rawTy :=
      substTy_irrelevant_of_agree f.rawTy args1 args2 hHead
    have hRec := computePrefixOffsets_invariance_aux rest adts fuel repr args1 args2
    dsimp only [computePrefixOffsets]
    rw [hSubst]
    cases (layoutOfFuel adts fuel (substTy args2 f.rawTy)).isSized with
    | false => rfl
    | true =>
      dsimp only
      rw [hRec _ _ hTail]

theorem isPhantomTy_implies_is1Zst :
    ∀ (env : TypeEnv) (fuel : Nat) (ty : Ty),
      isPhantomTy env ty = true →
      (layoutOfFuel env.adts (Nat.succ fuel) ty).is1Zst = true
  | _, _, .unit, h => Bool.noConfusion h
  | _, _, .scalar _ _ _, h => Bool.noConfusion h
  | _, _, .param _, h => Bool.noConfusion h
  | _, _, .region _, h => Bool.noConfusion h
  | _, _, .array _ _, h => Bool.noConfusion h
  | _, _, .slice _, h => Bool.noConfusion h
  | _, _, .ref _ _ _, h => Bool.noConfusion h
  | _, _, .rawPtr _ _, h => Bool.noConfusion h
  | _, _, .traitObj _, h => Bool.noConfusion h
  | _, _, .phantom _, _ => rfl
  | env, _, .adt defId _, h => by
    dsimp only [isPhantomTy] at h
    dsimp only [layoutOfFuel]
    cases hlook : lookupAdt env.adts defId with
    | none => rw [hlook] at h; exact Bool.noConfusion h
    | some _ =>
      rw [hlook] at h
      dsimp only at h
      dsimp only
      rw [h]

/-- Strong non-1-ZST layout property preserved under wrapping in non-packed structs. -/
noncomputable def not1ZstStrong (l : TyLayout) : Prop :=
  (1 ≤ l.byteSize ∨ Nat.ble 2 l.byteAlign = true ∨ l.isSized = false) ∧ l.is1Zst = false

theorem combineAdtFieldLayouts_strong_pos_size :
    ∀ (fs : List TyLayout) (curSize curAlign : Nat) (repr : ReprKind),
      1 ≤ curSize →
      reprAllowedForDispatch repr = true →
      not1ZstStrong (combineAdtFieldLayouts curSize curAlign fs repr)
  | [], curSize, curAlign, repr, hsz, hrepr => by
    dsimp only [combineAdtFieldLayouts]
    cases repr with
    | reprC => exact Bool.noConfusion hrepr
    | reprPacked _ => exact Bool.noConfusion hrepr
    | reprRust =>
      have hge := Nat.le_trans hsz (alignUp_ge curSize curAlign)
      cases hfin : alignUp curSize curAlign with
      | zero => rw [hfin] at hge; cases hge
      | succ k =>
        refine ⟨Or.inl ?_, ?_⟩
        { dsimp only; exact Nat.succ_le_succ (Nat.zero_le k) }
        { dsimp only; rfl }
    | reprTransparent =>
      have hge := Nat.le_trans hsz (alignUp_ge curSize curAlign)
      cases hfin : alignUp curSize curAlign with
      | zero => rw [hfin] at hge; cases hge
      | succ k =>
        refine ⟨Or.inl ?_, ?_⟩
        { dsimp only; exact Nat.succ_le_succ (Nat.zero_le k) }
        { dsimp only; rfl }
  | fl :: rest, curSize, curAlign, repr, hsz, hrepr => by
    dsimp only [combineAdtFieldLayouts]
    cases fl.isSized with
    | false => exact ⟨Or.inr (Or.inr rfl), rfl⟩
    | true =>
      dsimp only
      cases repr with
      | reprC => exact Bool.noConfusion hrepr
      | reprPacked _ => exact Bool.noConfusion hrepr
      | reprRust =>
        dsimp only
        have hal := alignUp_ge curSize fl.byteAlign
        exact combineAdtFieldLayouts_strong_pos_size rest _ _ .reprRust
          (Nat.le_trans hsz (Nat.le_trans hal (Nat.le_add_right _ _))) hrepr
      | reprTransparent =>
        dsimp only
        have hal := alignUp_ge curSize fl.byteAlign
        exact combineAdtFieldLayouts_strong_pos_size rest _ _ .reprTransparent
          (Nat.le_trans hsz (Nat.le_trans hal (Nat.le_add_right _ _))) hrepr

theorem combineAdtFieldLayouts_strong_align :
    ∀ (fs : List TyLayout) (curSize curAlign : Nat) (repr : ReprKind),
      Nat.ble 2 curAlign = true →
      reprAllowedForDispatch repr = true →
      not1ZstStrong (combineAdtFieldLayouts curSize curAlign fs repr)
  | [], curSize, curAlign, repr, hal, hrepr => by
    dsimp only [combineAdtFieldLayouts]
    have hcur : 2 ≤ curAlign := Nat.le_of_ble_eq_true hal
    cases repr with
    | reprC => exact Bool.noConfusion hrepr
    | reprPacked _ => exact Bool.noConfusion hrepr
    | reprRust =>
      refine ⟨Or.inr (Or.inl hal), ?_⟩
      dsimp only
      cases Nat.beq (alignUp curSize curAlign) 0 with
      | false => rfl
      | true =>
        cases curAlign with
        | zero => cases hcur
        | succ k =>
          cases k with
          | zero => cases hcur with | step hk => cases hk
          | succ _ => rfl
    | reprTransparent =>
      refine ⟨Or.inr (Or.inl hal), ?_⟩
      dsimp only
      cases Nat.beq (alignUp curSize curAlign) 0 with
      | false => rfl
      | true =>
        cases curAlign with
        | zero => cases hcur
        | succ k =>
          cases k with
          | zero => cases hcur with | step hk => cases hk
          | succ _ => rfl
  | fl :: rest, curSize, curAlign, repr, hal, hrepr => by
    dsimp only [combineAdtFieldLayouts]
    cases fl.isSized with
    | false => exact ⟨Or.inr (Or.inr rfl), rfl⟩
    | true =>
      dsimp only
      cases repr with
      | reprC => exact Bool.noConfusion hrepr
      | reprPacked _ => exact Bool.noConfusion hrepr
      | reprRust =>
        exact combineAdtFieldLayouts_strong_align rest _ _ .reprRust (maxNat_ge_two_left curAlign fl.byteAlign hal) rfl
      | reprTransparent =>
        exact combineAdtFieldLayouts_strong_align rest _ _ .reprTransparent (maxNat_ge_two_left curAlign fl.byteAlign hal) rfl

theorem combineAdtFieldLayouts_strong_of_elem :
    ∀ (pre : List TyLayout) (fl : TyLayout) (post : List TyLayout)
      (curSize curAlign : Nat) (repr : ReprKind),
      reprAllowedForDispatch repr = true →
      not1ZstStrong fl →
      not1ZstStrong (combineAdtFieldLayouts curSize curAlign (pre ++ fl :: post) repr)
  | [], fl, post, curSize, curAlign, repr, hrepr, hstrong => by
    change not1ZstStrong (combineAdtFieldLayouts curSize curAlign (fl :: post) repr)
    dsimp only [combineAdtFieldLayouts]
    cases hsized : fl.isSized with
    | false => exact ⟨Or.inr (Or.inr rfl), rfl⟩
    | true =>
      cases repr with
      | reprC => exact Bool.noConfusion hrepr
      | reprPacked _ => exact Bool.noConfusion hrepr
      | reprRust =>
        dsimp only
        cases hstrong.1 with
        | inl hsz =>
          exact combineAdtFieldLayouts_strong_pos_size post (alignUp curSize fl.byteAlign + fl.byteSize)
            (maxNat curAlign fl.byteAlign) .reprRust (Nat.le_trans hsz (Nat.le_add_left _ _)) rfl
        | inr hrest =>
          cases hrest with
          | inl hal =>
            exact combineAdtFieldLayouts_strong_align post (alignUp curSize fl.byteAlign + fl.byteSize)
              (maxNat curAlign fl.byteAlign) .reprRust (maxNat_ge_two_right curAlign fl.byteAlign hal) rfl
          | inr hns => rw [hns] at hsized; exact Bool.noConfusion hsized
      | reprTransparent =>
        dsimp only
        cases hstrong.1 with
        | inl hsz =>
          exact combineAdtFieldLayouts_strong_pos_size post (alignUp curSize fl.byteAlign + fl.byteSize)
            (maxNat curAlign fl.byteAlign) .reprTransparent (Nat.le_trans hsz (Nat.le_add_left _ _)) rfl
        | inr hrest =>
          cases hrest with
          | inl hal =>
            exact combineAdtFieldLayouts_strong_align post (alignUp curSize fl.byteAlign + fl.byteSize)
              (maxNat curAlign fl.byteAlign) .reprTransparent (maxNat_ge_two_right curAlign fl.byteAlign hal) rfl
          | inr hns => rw [hns] at hsized; exact Bool.noConfusion hsized
  | p :: pre, fl, post, curSize, curAlign, repr, hrepr, hstrong => by
    change not1ZstStrong (combineAdtFieldLayouts curSize curAlign (p :: (pre ++ fl :: post)) repr)
    dsimp only [combineAdtFieldLayouts]
    cases p.isSized with
    | false => exact ⟨Or.inr (Or.inr rfl), rfl⟩
    | true => exact combineAdtFieldLayouts_strong_of_elem pre fl post _ _ repr hrepr hstrong

theorem evalFieldsLayout_append : ∀ (ev : Ty → TyLayout) (args : List Ty)
    (fs1 fs2 : List FieldDef),
    evalFieldsLayout ev args (fs1 ++ fs2) =
    evalFieldsLayout ev args fs1 ++ evalFieldsLayout ev args fs2
  | _, _, [], _ => rfl
  | ev, args, f :: fs1, fs2 => by
    dsimp only [List.append, evalFieldsLayout]
    exact congrArg (List.cons _) (evalFieldsLayout_append ev args fs1 fs2)

/-!
## Section 4: Diagnostic Codes, `wfcheck` (`E0277`), `unsizingParams`, `Unsize`, `CoerceUnsized`, & `DispatchFromDyn`
-/

inductive DiagCode where
  | ok : DiagCode
  | e0277NonLastUnsized : DiagCode
  | e0374NoField : DiagCode
  | e0375MultiField : DiagCode
  | e0377SameStructOrNonStruct : DiagCode
  | e0378DispatchReprForbidden : DiagCode
  | e0378DispatchExtraNon1Zst : DiagCode
  | e0378DispatchExtraGenericParam : DiagCode
  | e0308PrefixParamCapture : DiagCode
  | e0277UnsizeNotApplicable : DiagCode
  | ptrMutOrRegionRejected : DiagCode
  | fuelExhausted : DiagCode

inductive CheckResult (α : Type) where
  | ok : α → CheckResult α
  | err : DiagCode → CheckResult α

noncomputable def allFieldsSized (env : TypeEnv) (fuel : Nat) (args : List Ty) : List FieldDef → Bool
  | [] => true
  | f :: fs =>
    let fl := layoutOfFuel env.adts fuel (substTy args f.rawTy)
    Bool.and fl.isSized (allFieldsSized env fuel args fs)

noncomputable def wfAdtFields (env : TypeEnv) (fuel : Nat) (d : AdtDef) (args : List Ty) : DiagCode :=
  match d.kind with
  | .structKind =>
    match d.repr with
    | .reprPacked _ =>
      match allFieldsSized env fuel args d.fields with
      | true => .ok
      | false => .e0277NonLastUnsized
    | _ =>
      match allFieldsSized env fuel args (dropLast d.fields) with
      | true => .ok
      | false => .e0277NonLastUnsized
  | .enumKind =>
    match allFieldsSized env fuel args d.fields with
    | true => .ok
    | false => .e0277NonLastUnsized
  | .unionKind =>
    match allFieldsSized env fuel args d.fields with
    | true => .ok
    | false => .e0277NonLastUnsized

noncomputable def collectParamsFields : List FieldDef → List Nat
  | [] => []
  | f :: fs => collectParamsTy f.rawTy ++ collectParamsFields fs

theorem paramOccursInFields_implies_mem_collectParamsFields :
    ∀ (fs : List FieldDef) (p : Nat),
      paramOccursInList p (fs.map FieldDef.rawTy) = true →
      listContainsNat (collectParamsFields fs) p = true
  | [], _, h => Bool.noConfusion h
  | f :: fs, p, h => by
    dsimp only [List.map, paramOccursInList] at h
    dsimp only [collectParamsFields]
    cases hf : paramOccursInTy p f.rawTy with
    | true =>
      exact listContainsNat_append_left (collectParamsTy f.rawTy) (collectParamsFields fs) p
        (paramOccursInTy_implies_mem_collectParams f.rawTy p hf)
    | false =>
      rw [hf] at h
      exact listContainsNat_append_right (collectParamsTy f.rawTy) (collectParamsFields fs) p
        (paramOccursInFields_implies_mem_collectParamsFields fs p h)

noncomputable def unsizingParamsForAdt (d : AdtDef) : List Nat :=
  match lastElem? d.fields with
  | none => []
  | some tail =>
    let tailParams := collectParamsTy tail.rawTy
    let prefixBanned := collectParamsFields (dropLast d.fields)
    filterNotIn tailParams prefixBanned

theorem unsizingParams_disjoint_from_prefix :
    ∀ (d : AdtDef) (p : Nat),
      listContainsNat (unsizingParamsForAdt d) p = true →
      paramOccursInList p ((dropLast d.fields).map FieldDef.rawTy) = false := by
  intro d p hmem
  dsimp only [unsizingParamsForAdt] at hmem
  cases ht : lastElem? d.fields with
  | none =>
    rw [ht] at hmem
    exact Bool.noConfusion hmem
  | some tail =>
    rw [ht] at hmem
    have hnot : listContainsNat (collectParamsFields (dropLast d.fields)) p = false :=
      listContainsNat_true_of_mem_filterNotIn_false (collectParamsTy tail.rawTy) _ p hmem
    cases hocc : paramOccursInList p ((dropLast d.fields).map FieldDef.rawTy) with
    | false => rfl
    | true =>
      have hcontra := paramOccursInFields_implies_mem_collectParamsFields (dropLast d.fields) p hocc
      rw [hcontra] at hnot
      exact Bool.noConfusion hnot

noncomputable def argsAgreeOutside (unsizedParams : List Nat) : Nat → List Ty → List Ty → Bool
  | _, [], [] => true
  | idx, a :: as, b :: bs =>
    let okHere := match listContainsNat unsizedParams idx with
      | true => true
      | false => tyBeq a b
    Bool.and okHere (argsAgreeOutside unsizedParams (Nat.succ idx) as bs)
  | _, _, _ => false

theorem argsAgreeOutside_spec :
    ∀ (up : List Nat) (startIdx p : Nat) (args1 args2 : List Ty),
      argsAgreeOutside up startIdx args1 args2 = true →
      listContainsNat up (startIdx + p) = false →
      listGet? args1 p = listGet? args2 p
  | _, _, _, [], [], _, _ => rfl
  | _, _, _, [], _ :: _, h, _ => Bool.noConfusion h
  | _, _, _, _ :: _, [], h, _ => Bool.noConfusion h
  | up, startIdx, 0, a :: _, b :: _, h, hnot => by
    dsimp only [argsAgreeOutside] at h
    have okH := boolAndLeft h
    dsimp only [listGet?]
    rw [Nat.add_zero] at hnot
    rw [hnot] at okH
    have heq := tyBeq_eq_true okH
    rw [heq]
  | up, startIdx, Nat.succ p', _ :: as, _ :: bs, h, hnot => by
    dsimp only [argsAgreeOutside] at h
    have okRest := boolAndRight h
    have hadd : Nat.succ startIdx + p' = startIdx + Nat.succ p' := Nat.succ_add startIdx p'
    have hnot' : listContainsNat up (Nat.succ startIdx + p') = false := by
      rw [hadd]
      exact hnot
    exact argsAgreeOutside_spec up (Nat.succ startIdx) p' as bs okRest hnot'

inductive UnsizeWitness where
  | arrayToSlice : Ty → Nat → UnsizeWitness
  | concreteToDyn : Ty → Nat → Nat → UnsizeWitness
  | structTail : Nat → Nat → UnsizeWitness → UnsizeWitness

noncomputable def checkUnsizeFuel (env : TypeEnv) : Nat → Ty → Ty → CheckResult UnsizeWitness
  | 0, _, _ => .err .fuelExhausted
  | Nat.succ fuel, src, dst =>
    match src, dst with
    | .array elem len, .slice elem' =>
      match tyBeq elem elem' with
      | true => .ok (.arrayToSlice elem len)
      | false => .err .e0277UnsizeNotApplicable
    | _, .traitObj tid =>
      match (layoutOfFuel env.adts fuel src).isSized with
      | false => .err .e0277UnsizeNotApplicable
      | true =>
        match findTraitImpl env.traitImpls src tid with
        | some vid => .ok (.concreteToDyn src tid vid)
        | none => .err .e0277UnsizeNotApplicable
    | .adt d1 args1, .adt d2 args2 =>
      match Nat.beq d1 d2 with
      | false => .err .e0277UnsizeNotApplicable
      | true =>
        match lookupAdt env.adts d1 with
        | none => .err .e0277UnsizeNotApplicable
        | some d =>
          match d.kind with
          | .structKind =>
            match wfAdtFields env fuel d args1 with
            | .ok =>
              match wfAdtFields env fuel d args2 with
              | .ok =>
                match lastElem? d.fields with
                | none => .err .e0277UnsizeNotApplicable
                | some tail =>
                  let up := unsizingParamsForAdt d
                  match up with
                  | [] => .err .e0308PrefixParamCapture
                  | _ =>
                    match argsAgreeOutside up 0 args1 args2 with
                    | false => .err .e0308PrefixParamCapture
                    | true =>
                      match checkUnsizeFuel env fuel (substTy args1 tail.rawTy) (substTy args2 tail.rawTy) with
                      | .ok inner => .ok (.structTail d1 tail.fieldId inner)
                      | .err e => .err e
              | e2 => .err e2
            | e1 => .err e1
          | _ => .err .e0277UnsizeNotApplicable
    | _, _ => .err .e0277UnsizeNotApplicable

/-- **Theorem 3A (Tail-Only `?Sized` Prefix-Offset Invariance):**
    All prefix field byte offsets (`dropLast d.fields`) are bit-for-bit invariant
    across any two parameter lists agreeing outside `unsizingParamsForAdt d`. -/
theorem tail_only_unsized_prefix_offset_invariance :
    ∀ (d : AdtDef) (adts : List AdtDef) (fuel : Nat) (args1 args2 : List Ty),
      argsAgreeOutside (unsizingParamsForAdt d) 0 args1 args2 = true →
      computePrefixOffsets adts fuel d.repr args1 0 1 (dropLast d.fields) =
      computePrefixOffsets adts fuel d.repr args2 0 1 (dropLast d.fields) := by
  intro d adts fuel args1 args2 hAgree
  apply computePrefixOffsets_invariance_aux
  intro p hpOcc
  have hpNotInUp : listContainsNat (unsizingParamsForAdt d) p = false := by
    cases hmem : listContainsNat (unsizingParamsForAdt d) p with
    | false => rfl
    | true =>
      have hcontra := unsizingParams_disjoint_from_prefix d p hmem
      rw [hcontra] at hpOcc
      exact Bool.noConfusion hpOcc
  have hZeroAdd : 0 + p = p := Nat.zero_add p
  have hpNot' : listContainsNat (unsizingParamsForAdt d) (0 + p) = false := by
    rw [hZeroAdd]
    exact hpNotInUp
  exact argsAgreeOutside_spec (unsizingParamsForAdt d) 0 p args1 args2 hAgree hpNot'

/-- **Theorem 3B (End-to-End `Unsize` Prefix-Offset Invariance):**
    Any ADT coercion confirmed by `checkUnsizeFuel` leaves all non-tail prefix byte offsets identical. -/
theorem unsize_preserves_prefix_offsets :
    ∀ (env : TypeEnv) (fuel dId : Nat) (d : AdtDef) (args1 args2 : List Ty) (w : UnsizeWitness),
      lookupAdt env.adts dId = some d →
      checkUnsizeFuel env (Nat.succ fuel) (.adt dId args1) (.adt dId args2) = .ok w →
      computePrefixOffsets env.adts fuel d.repr args1 0 1 (dropLast d.fields) =
      computePrefixOffsets env.adts fuel d.repr args2 0 1 (dropLast d.fields) := by
  intro env fuel dId d args1 args2 _ hlook hchk
  dsimp only [checkUnsizeFuel] at hchk
  rw [natBeq_refl dId, hlook] at hchk
  dsimp only at hchk
  cases hk : d.kind with
  | enumKind => rw [hk] at hchk; cases hchk
  | unionKind => rw [hk] at hchk; cases hchk
  | structKind =>
    rw [hk] at hchk
    dsimp only at hchk
    cases hwf1 : wfAdtFields env fuel d args1 with
    | ok =>
      rw [hwf1] at hchk
      dsimp only at hchk
      cases hwf2 : wfAdtFields env fuel d args2 with
      | ok =>
        rw [hwf2] at hchk
        cases htail : lastElem? d.fields with
        | none => rw [htail] at hchk; cases hchk
        | some tail =>
          rw [htail] at hchk
          cases hup : unsizingParamsForAdt d with
          | nil => rw [hup] at hchk; cases hchk
          | cons u us =>
            rw [hup] at hchk
            dsimp only at hchk
            cases hagree : argsAgreeOutside (u :: us) 0 args1 args2 with
            | false => rw [hagree] at hchk; cases hchk
            | true =>
              rw [← hup] at hagree
              exact tail_only_unsized_prefix_offset_invariance d env.adts fuel args1 args2 hagree
      | e0277NonLastUnsized => rw [hwf2] at hchk; cases hchk
      | e0374NoField => rw [hwf2] at hchk; cases hchk
      | e0375MultiField => rw [hwf2] at hchk; cases hchk
      | e0377SameStructOrNonStruct => rw [hwf2] at hchk; cases hchk
      | e0378DispatchReprForbidden => rw [hwf2] at hchk; cases hchk
      | e0378DispatchExtraNon1Zst => rw [hwf2] at hchk; cases hchk
      | e0378DispatchExtraGenericParam => rw [hwf2] at hchk; cases hchk
      | e0308PrefixParamCapture => rw [hwf2] at hchk; cases hchk
      | e0277UnsizeNotApplicable => rw [hwf2] at hchk; cases hchk
      | ptrMutOrRegionRejected => rw [hwf2] at hchk; cases hchk
      | fuelExhausted => rw [hwf2] at hchk; cases hchk
    | e0277NonLastUnsized => rw [hwf1] at hchk; cases hchk
    | e0374NoField => rw [hwf1] at hchk; cases hchk
    | e0375MultiField => rw [hwf1] at hchk; cases hchk
    | e0377SameStructOrNonStruct => rw [hwf1] at hchk; cases hchk
    | e0378DispatchReprForbidden => rw [hwf1] at hchk; cases hchk
    | e0378DispatchExtraNon1Zst => rw [hwf1] at hchk; cases hchk
    | e0378DispatchExtraGenericParam => rw [hwf1] at hchk; cases hchk
    | e0308PrefixParamCapture => rw [hwf1] at hchk; cases hchk
    | e0277UnsizeNotApplicable => rw [hwf1] at hchk; cases hchk
    | ptrMutOrRegionRejected => rw [hwf1] at hchk; cases hchk
    | fuelExhausted => rw [hwf1] at hchk; cases hchk

inductive CoerceWitness where
  | ptrCoerce : UnsizeWitness → CoerceWitness
  | structField : Nat → Nat → CoerceWitness → CoerceWitness

noncomputable def collectDiffFieldsCoerce (env : TypeEnv) (argsA argsB : List Ty) :
    Nat → List FieldDef → List (Nat × Ty × Ty)
  | _, [] => []
  | idx, f :: rest =>
    let tyA := substTy argsA f.rawTy
    let tyB := substTy argsB f.rawTy
    let tailDiffs := collectDiffFieldsCoerce env argsA argsB (Nat.succ idx) rest
    match Bool.and (isPhantomTy env tyA) (isPhantomTy env tyB) with
    | true => tailDiffs
    | false =>
      match tyBeq tyA tyB with
      | true => tailDiffs
      | false => (idx, tyA, tyB) :: tailDiffs

noncomputable def collectDiffFieldsDispatch (env : TypeEnv) (fuel : Nat) (argsA argsB : List Ty) :
    Nat → List FieldDef → CheckResult (List (Nat × Ty × Ty))
  | _, [] => .ok []
  | idx, f :: rest =>
    let tyA := substTy argsA f.rawTy
    let tyB := substTy argsB f.rawTy
    match Bool.and (isPhantomTy env tyA) (isPhantomTy env tyB) with
    | true => collectDiffFieldsDispatch env fuel argsA argsB (Nat.succ idx) rest
    | false =>
      match tyBeq tyA tyB with
      | true =>
        match hasNonRegionParam tyA with
        | true => .err .e0378DispatchExtraGenericParam
        | false =>
          match (layoutOfFuel env.adts fuel tyA).is1Zst with
          | false => .err .e0378DispatchExtraNon1Zst
          | true => collectDiffFieldsDispatch env fuel argsA argsB (Nat.succ idx) rest
      | false =>
        match collectDiffFieldsDispatch env fuel argsA argsB (Nat.succ idx) rest with
        | .ok tailDiffs => .ok ((idx, tyA, tyB) :: tailDiffs)
        | .err e => .err e

theorem collectDiffFieldsDispatch_implies_coerce :
    ∀ (fs : List FieldDef) (env : TypeEnv) (fuel : Nat) (argsA argsB : List Ty)
      (idx : Nat) (diffs : List (Nat × Ty × Ty)),
      collectDiffFieldsDispatch env fuel argsA argsB idx fs = .ok diffs →
      collectDiffFieldsCoerce env argsA argsB idx fs = diffs
  | [], _, _, _, _, _, diffs, h => by
    dsimp only [collectDiffFieldsDispatch] at h
    injection h with hd
    first | done | (rw [← hd]; dsimp only [collectDiffFieldsCoerce]; rfl)
  | f :: rest, env, fuel, argsA, argsB, idx, diffs, h => by
    dsimp only [collectDiffFieldsDispatch] at h
    dsimp only [collectDiffFieldsCoerce]
    cases hp : Bool.and (isPhantomTy env (substTy argsA f.rawTy)) (isPhantomTy env (substTy argsB f.rawTy)) with
    | true =>
      rw [hp] at h
      exact collectDiffFieldsDispatch_implies_coerce rest env fuel argsA argsB (Nat.succ idx) diffs h
    | false =>
      rw [hp] at h
      dsimp only at h ⊢
      cases heq : tyBeq (substTy argsA f.rawTy) (substTy argsB f.rawTy) with
      | false =>
        rw [heq] at h
        dsimp only at h ⊢
        cases hrec : collectDiffFieldsDispatch env fuel argsA argsB (Nat.succ idx) rest with
        | err _ => rw [hrec] at h; cases h
        | ok tailDiffs =>
          rw [hrec] at h
          injection h with hdiff
          rw [← hdiff]
          exact congrArg (List.cons (idx, substTy argsA f.rawTy, substTy argsB f.rawTy))
            (collectDiffFieldsDispatch_implies_coerce rest env fuel argsA argsB (Nat.succ idx) tailDiffs hrec)
      | true =>
        rw [heq] at h
        dsimp only at h
        cases hnr : hasNonRegionParam (substTy argsA f.rawTy) with
        | true => rw [hnr] at h; cases h
        | false =>
          rw [hnr] at h
          dsimp only at h
          cases hz : (layoutOfFuel env.adts fuel (substTy argsA f.rawTy)).is1Zst with
          | false => rw [hz] at h; cases h
          | true =>
            rw [hz] at h
            exact collectDiffFieldsDispatch_implies_coerce rest env fuel argsA argsB (Nat.succ idx) diffs h

noncomputable def checkCoerceUnsizedFuel (env : TypeEnv) : Nat → Ty → Ty → CheckResult CoerceWitness
  | 0, _, _ => .err .fuelExhausted
  | Nat.succ fuel, src, dst =>
    match src, dst with
    | .ref rA mA ptA, .ref rB mB ptB =>
      match Bool.and (mutCoercible mA mB) (env.regionSub rA rB) with
      | false => .err .ptrMutOrRegionRejected
      | true =>
        match checkUnsizeFuel env fuel ptA ptB with
        | .ok uw => .ok (.ptrCoerce uw)
        | .err e => .err e
    | .ref _ mA ptA, .rawPtr mB ptB =>
      match mutCoercible mA mB with
      | false => .err .ptrMutOrRegionRejected
      | true =>
        match checkUnsizeFuel env fuel ptA ptB with
        | .ok uw => .ok (.ptrCoerce uw)
        | .err e => .err e
    | .rawPtr mA ptA, .rawPtr mB ptB =>
      match mutCoercible mA mB with
      | false => .err .ptrMutOrRegionRejected
      | true =>
        match checkUnsizeFuel env fuel ptA ptB with
        | .ok uw => .ok (.ptrCoerce uw)
        | .err e => .err e
    | .adt dA argsA, .adt dB argsB =>
      match Nat.beq dA dB with
      | false => .err .e0377SameStructOrNonStruct
      | true =>
        match lookupAdt env.adts dA with
        | none => .err .e0377SameStructOrNonStruct
        | some d =>
          match Bool.and (match d.kind with | .structKind => true | _ => false) (Bool.not d.isLangPhantom) with
          | false => .err .e0377SameStructOrNonStruct
          | true =>
            match collectDiffFieldsCoerce env argsA argsB 0 d.fields with
            | [] => .err .e0374NoField
            | [(idx, innerA, innerB)] =>
              match checkCoerceUnsizedFuel env fuel innerA innerB with
              | .ok innerW => .ok (.structField dA idx innerW)
              | .err e => .err e
            | _ :: _ :: _ => .err .e0375MultiField
    | _, _ => .err .e0377SameStructOrNonStruct

noncomputable def checkDispatchFromDynFuel (env : TypeEnv) : Nat → Ty → Ty → CheckResult CoerceWitness
  | 0, _, _ => .err .fuelExhausted
  | Nat.succ fuel, src, dst =>
    match src, dst with
    | .ref rA mA ptA, .ref rB mB ptB =>
      match Bool.and (Nat.beq rA rB) (mutBeq mA mB) with
      | false => .err .ptrMutOrRegionRejected
      | true =>
        match checkUnsizeFuel env fuel ptA ptB with
        | .ok uw => .ok (.ptrCoerce uw)
        | .err e => .err e
    | .rawPtr mA ptA, .rawPtr mB ptB =>
      match mutBeq mA mB with
      | false => .err .ptrMutOrRegionRejected
      | true =>
        match checkUnsizeFuel env fuel ptA ptB with
        | .ok uw => .ok (.ptrCoerce uw)
        | .err e => .err e
    | .adt dA argsA, .adt dB argsB =>
      match Nat.beq dA dB with
      | false => .err .e0377SameStructOrNonStruct
      | true =>
        match lookupAdt env.adts dA with
        | none => .err .e0377SameStructOrNonStruct
        | some d =>
          match Bool.and (match d.kind with | .structKind => true | _ => false) (Bool.not d.isLangPhantom) with
          | false => .err .e0377SameStructOrNonStruct
          | true =>
            match reprAllowedForDispatch d.repr with
            | false => .err .e0378DispatchReprForbidden
            | true =>
              match collectDiffFieldsDispatch env fuel argsA argsB 0 d.fields with
              | .err e => .err e
              | .ok [] => .err .e0374NoField
              | .ok [(idx, innerA, innerB)] =>
                match checkDispatchFromDynFuel env fuel innerA innerB with
                | .ok innerW => .ok (.structField dA idx innerW)
                | .err e => .err e
              | .ok (_ :: _ :: _) => .err .e0375MultiField
    | _, _ => .err .e0377SameStructOrNonStruct

/-- Theorem: Every valid `DispatchFromDyn` derivation strictly entails `CoerceUnsized`
    producing the identical `CoerceWitness` (assuming reflexive region outlives). -/
theorem dispatchFromDyn_implies_coerceUnsized :
    ∀ (fuel : Nat) (env : TypeEnv) (src dst : Ty) (w : CoerceWitness),
      (∀ r, env.regionSub r r = true) →
      checkDispatchFromDynFuel env fuel src dst = .ok w →
      checkCoerceUnsizedFuel env fuel src dst = .ok w
  | 0, _, _, _, _, _, h => by dsimp only [checkDispatchFromDynFuel] at h; cases h
  | Nat.succ fuel, env, src, dst, w, hrefl, h => by
    cases src <;> cases dst
    case ref.ref rA mA ptA rB mB ptB =>
      dsimp only [checkDispatchFromDynFuel] at h
      dsimp only [checkCoerceUnsizedFuel]
      cases hok : Bool.and (Nat.beq rA rB) (mutBeq mA mB) with
      | false => rw [hok] at h; cases h
      | true =>
        rw [hok] at h
        have hr : rA = rB := natBeq_eq_true (boolAndLeft hok)
        have hm : mutCoercible mA mB = true := mutBeq_implies_mutCoercible (boolAndRight hok)
        have hreg : env.regionSub rA rB = true := by rw [hr]; exact hrefl rB
        rw [boolAndIntro hm hreg]
        exact h
    case rawPtr.rawPtr mA ptA mB ptB =>
      dsimp only [checkDispatchFromDynFuel] at h
      dsimp only [checkCoerceUnsizedFuel]
      cases hm : mutBeq mA mB with
      | false => rw [hm] at h; cases h
      | true =>
        rw [hm] at h
        rw [mutBeq_implies_mutCoercible hm]
        exact h
    case adt.adt dA argsA dB argsB =>
      dsimp only [checkDispatchFromDynFuel] at h
      dsimp only [checkCoerceUnsizedFuel]
      cases hd : Nat.beq dA dB with
      | false => rw [hd] at h; cases h
      | true =>
        rw [hd] at h
        cases hlook : lookupAdt env.adts dA with
        | none => rw [hlook] at h; cases h
        | some adtDef =>
          rw [hlook] at h
          dsimp only at h ⊢
          cases hk : Bool.and (match adtDef.kind with | .structKind => true | _ => false) (Bool.not adtDef.isLangPhantom) with
          | false => rw [hk] at h; cases h
          | true =>
            rw [hk] at h
            dsimp only at h ⊢
            cases hrepr : reprAllowedForDispatch adtDef.repr with
            | false => rw [hrepr] at h; cases h
            | true =>
              rw [hrepr] at h
              dsimp only at h
              cases hdiffs : collectDiffFieldsDispatch env fuel argsA argsB 0 adtDef.fields with
              | err _ => rw [hdiffs] at h; cases h
              | ok diffs =>
                rw [hdiffs] at h
                have hcoerce := collectDiffFieldsDispatch_implies_coerce adtDef.fields env fuel argsA argsB 0 diffs hdiffs
                rw [hcoerce]
                cases diffs with
                | nil => cases h
                | cons head tail =>
                  cases tail with
                  | cons _ _ => cases h
                  | nil =>
                    dsimp only at h ⊢
                    cases hinner : checkDispatchFromDynFuel env fuel head.2.1 head.2.2 with
                    | err _ => rw [hinner] at h; cases h
                    | ok innerW =>
                      rw [hinner] at h
                      have ih := dispatchFromDyn_implies_coerceUnsized fuel env head.2.1 head.2.2 innerW hrefl hinner
                      rw [ih]
                      exact h
    all_goals (dsimp only [checkDispatchFromDynFuel] at h; cases h)

theorem collectDiffFieldsDispatch_split_fields :
    ∀ (fs : List FieldDef) (env : TypeEnv) (fuel : Nat) (argsA argsB : List Ty)
      (startIdx idx : Nat) (innerA innerB : Ty),
      collectDiffFieldsDispatch env fuel argsA argsB startIdx fs = .ok [(idx, innerA, innerB)] →
      Exists (fun pre => Exists (fun f => Exists (fun post =>
        fs = pre ++ f :: post ∧
        substTy argsA f.rawTy = innerA ∧
        substTy argsB f.rawTy = innerB)))
  | [], _, _, _, _, _, _, _, _, h => by
    dsimp only [collectDiffFieldsDispatch] at h
    cases h
  | f :: rest, env, fuel, argsA, argsB, startIdx, idx, innerA, innerB, h => by
    dsimp only [collectDiffFieldsDispatch] at h
    cases hp : Bool.and (isPhantomTy env (substTy argsA f.rawTy)) (isPhantomTy env (substTy argsB f.rawTy)) with
    | true =>
      rw [hp] at h
      have ⟨pre, f', post, hfs, hA, hB⟩ :=
        collectDiffFieldsDispatch_split_fields rest env fuel argsA argsB (Nat.succ startIdx) idx innerA innerB h
      refine ⟨f :: pre, f', post, congrArg (List.cons f) hfs, hA, hB⟩
    | false =>
      rw [hp] at h; dsimp only at h
      cases heq : tyBeq (substTy argsA f.rawTy) (substTy argsB f.rawTy) with
      | false =>
        rw [heq] at h; dsimp only at h
        cases hrec : collectDiffFieldsDispatch env fuel argsA argsB (Nat.succ startIdx) rest with
        | err _ => rw [hrec] at h; cases h
        | ok tailDiffs =>
          rw [hrec] at h
          cases tailDiffs with
          | cons _ _ => cases h
          | nil =>
            injection h with hl
            injection hl with hpair
            injection hpair with _ h2
            injection h2 with hA hB
            refine ⟨[], f, rest, rfl, hA, hB⟩
      | true =>
        rw [heq] at h; dsimp only at h
        cases hnr : hasNonRegionParam (substTy argsA f.rawTy) with
        | true => rw [hnr] at h; cases h
        | false =>
          rw [hnr] at h; dsimp only at h
          cases hz : (layoutOfFuel env.adts fuel (substTy argsA f.rawTy)).is1Zst with
          | false => rw [hz] at h; cases h
          | true =>
            rw [hz] at h
            have ⟨pre, f', post, hfs, hA, hB⟩ :=
              collectDiffFieldsDispatch_split_fields rest env fuel argsA argsB (Nat.succ startIdx) idx innerA innerB h
            refine ⟨f :: pre, f', post, congrArg (List.cons f) hfs, hA, hB⟩

theorem layoutOfFuel_adt_struct :
    ∀ (adts : List AdtDef) (f defId : Nat) (args : List Ty) (d : AdtDef),
      lookupAdt adts defId = some d →
      d.isLangPhantom = false →
      layoutOfFuel adts (Nat.succ f) (.adt defId args) =
      combineAdtFieldLayouts 0 1 (evalFieldsLayout (layoutOfFuel adts f) args d.fields) d.repr := by
  intro adts f defId args d hl hph
  dsimp only [layoutOfFuel]
  rw [hl]
  dsimp only
  rw [hph]

/-- Theorem: Any type accepted by `checkDispatchFromDynFuel` satisfies `not1ZstStrong`
    (so its layout has `is1Zst = false` and carries a non-zero data/vtable pointer). -/
theorem dispatchFromDyn_strong_non_1zst :
    ∀ (fuel : Nat) (env : TypeEnv) (src dst : Ty) (w : CoerceWitness),
      checkDispatchFromDynFuel env fuel src dst = .ok w →
      not1ZstStrong (layoutOfFuel env.adts fuel src) ∧
      not1ZstStrong (layoutOfFuel env.adts fuel dst)
  | 0, _, _, _, _, h => by dsimp only [checkDispatchFromDynFuel] at h; cases h
  | Nat.succ 0, env, src, dst, _, h => by
    cases src <;> cases dst
    case ref.ref rA mA ptA rB mB ptB =>
      dsimp only [checkDispatchFromDynFuel] at h
      cases hok : Bool.and (Nat.beq rA rB) (mutBeq mA mB) with
      | false => rw [hok] at h; cases h
      | true =>
        rw [hok] at h
        dsimp only [checkUnsizeFuel] at h
        cases h
    case rawPtr.rawPtr mA ptA mB ptB =>
      dsimp only [checkDispatchFromDynFuel] at h
      cases hm : mutBeq mA mB with
      | false => rw [hm] at h; cases h
      | true =>
        rw [hm] at h
        dsimp only [checkUnsizeFuel] at h
        cases h
    case adt.adt dA argsA dB argsB =>
      dsimp only [checkDispatchFromDynFuel] at h
      cases hd : Nat.beq dA dB with
      | false => rw [hd] at h; cases h
      | true =>
        rw [hd] at h
        cases hl : lookupAdt env.adts dA with
        | none => rw [hl] at h; cases h
        | some d =>
          rw [hl] at h; dsimp only at h
          cases hk : Bool.and (match d.kind with | .structKind => true | _ => false) (Bool.not d.isLangPhantom) with
          | false => rw [hk] at h; cases h
          | true =>
            rw [hk] at h; dsimp only at h
            cases hr : reprAllowedForDispatch d.repr with
            | false => rw [hr] at h; cases h
            | true =>
              rw [hr] at h; dsimp only at h
              cases hdiffs : collectDiffFieldsDispatch env 0 argsA argsB 0 d.fields with
              | err _ => rw [hdiffs] at h; cases h
              | ok diffs =>
                rw [hdiffs] at h
                cases diffs with
                | nil => cases h
                | cons head tail =>
                  cases tail with
                  | cons _ _ => cases h
                  | nil =>
                    dsimp only at h
                    cases h
    all_goals (dsimp only [checkDispatchFromDynFuel] at h; cases h)
  | Nat.succ (Nat.succ f'), env, src, dst, _, h => by
    cases src <;> cases dst
    case ref.ref =>
      exact ⟨⟨Or.inr (Or.inl rfl), rfl⟩, ⟨Or.inr (Or.inl rfl), rfl⟩⟩
    case rawPtr.rawPtr =>
      exact ⟨⟨Or.inr (Or.inl rfl), rfl⟩, ⟨Or.inr (Or.inl rfl), rfl⟩⟩
    case adt.adt dA argsA dB argsB =>
      dsimp only [checkDispatchFromDynFuel] at h
      cases hd : Nat.beq dA dB with
      | false => rw [hd] at h; cases h
      | true =>
        rw [hd] at h
        have hdEq : dA = dB := natBeq_eq_true hd
        cases hlook : lookupAdt env.adts dA with
        | none => rw [hlook] at h; cases h
        | some adtDef =>
          rw [hlook] at h; dsimp only at h
          cases hk : Bool.and (match adtDef.kind with | .structKind => true | _ => false) (Bool.not adtDef.isLangPhantom) with
          | false => rw [hk] at h; cases h
          | true =>
            rw [hk] at h; dsimp only at h
            have hNotPh : adtDef.isLangPhantom = false := by
              have hbr := boolAndRight hk
              cases hpv : adtDef.isLangPhantom with
              | false => rfl
              | true => rw [hpv] at hbr; exact Bool.noConfusion hbr
            cases hrepr : reprAllowedForDispatch adtDef.repr with
            | false => rw [hrepr] at h; cases h
            | true =>
              rw [hrepr] at h; dsimp only at h
              cases hdiffs : collectDiffFieldsDispatch env (Nat.succ f') argsA argsB 0 adtDef.fields with
              | err _ => rw [hdiffs] at h; cases h
              | ok diffs =>
                rw [hdiffs] at h
                cases diffs with
                | nil => cases h
                | cons head tail =>
                  cases tail with
                  | cons _ _ => cases h
                  | nil =>
                    dsimp only at h
                    change (match checkDispatchFromDynFuel env (Nat.succ f') head.2.1 head.2.2 with
                      | CheckResult.ok innerW => CheckResult.ok (CoerceWitness.structField dA head.1 innerW)
                      | CheckResult.err e => CheckResult.err e) = _ at h
                    cases hinner : checkDispatchFromDynFuel env (Nat.succ f') head.2.1 head.2.2 with
                    | err _ => rw [hinner] at h; cases h
                    | ok innerW =>
                      have ⟨ihA, ihB⟩ := dispatchFromDyn_strong_non_1zst (Nat.succ f') env head.2.1 head.2.2 innerW hinner
                      have ⟨pre, f, post, hsplit, hA, hB⟩ :=
                        collectDiffFieldsDispatch_split_fields adtDef.fields env (Nat.succ f') argsA argsB 0 head.1 head.2.1 head.2.2 hdiffs
                      constructor
                      { rw [layoutOfFuel_adt_struct env.adts (Nat.succ f') dA argsA adtDef hlook hNotPh, hsplit]
                        rw [evalFieldsLayout_append (layoutOfFuel env.adts (Nat.succ f')) argsA pre (f :: post)]
                        dsimp only [evalFieldsLayout]
                        rw [hA]
                        exact combineAdtFieldLayouts_strong_of_elem _ _ _ 0 1 adtDef.repr hrepr ihA }
                      { rw [← hdEq, layoutOfFuel_adt_struct env.adts (Nat.succ f') dA argsB adtDef hlook hNotPh, hsplit]
                        rw [evalFieldsLayout_append (layoutOfFuel env.adts (Nat.succ f')) argsB pre (f :: post)]
                        dsimp only [evalFieldsLayout]
                        rw [hB]
                        exact combineAdtFieldLayouts_strong_of_elem _ _ _ 0 1 adtDef.repr hrepr ihB }
    all_goals (dsimp only [checkDispatchFromDynFuel] at h; cases h)

/-!
## Section 5: Runtime Values, Coercion Operational Semantics, & `make_thin_self_ptr` ABI
-/

inductive PtrMeta where
  | thin : PtrMeta
  | sliceLen : Nat → PtrMeta
  | vtable : Nat → PtrMeta

inductive RuntimeVal where
  | zstVal : RuntimeVal
  | scalarVal : Nat → RuntimeVal
  | ptrVal : Nat → PtrMeta → RuntimeVal
  | structVal : Nat → List RuntimeVal → RuntimeVal

noncomputable def applyUnsizeMeta : UnsizeWitness → PtrMeta → Option PtrMeta
  | .arrayToSlice _ len, .thin => some (.sliceLen len)
  | .concreteToDyn _ _ vid, .thin => some (.vtable vid)
  | .structTail _ _ inner, m => applyUnsizeMeta inner m
  | _, _ => none

noncomputable def coerceRuntimeVal : CoerceWitness → RuntimeVal → Option RuntimeVal
  | .ptrCoerce uw, .ptrVal addr mdata =>
    match applyUnsizeMeta uw mdata with
    | some mdata' => some (.ptrVal addr mdata')
    | none => none
  | .structField d idx innerW, .structVal d' fvs =>
    match Nat.beq d d' with
    | false => none
    | true =>
      match listGet? fvs idx with
      | none => none
      | some fv =>
        match coerceRuntimeVal innerW fv with
        | none => none
        | some fv' => some (.structVal d' (listSet fvs idx fv'))
  | _, _ => none

noncomputable def targetPtrAddr : CoerceWitness → RuntimeVal → Option Nat
  | .ptrCoerce _, .ptrVal addr _ => some addr
  | .structField _ idx innerW, .structVal _ fvs =>
    match listGet? fvs idx with
    | none => none
    | some fv => targetPtrAddr innerW fv
  | _, _ => none

/-- **Theorem 1A (Single-Field Unsize Structural Preservation):**
    Every valid struct `CoerceUnsized` coercion preserves ADT identity and field count,
    modifies strictly field `idx`, and leaves every sibling field `j ≠ idx` untouched bit-for-bit. -/
theorem coerceUnsized_single_field_preservation :
    ∀ (d idx : Nat) (innerW : CoerceWitness) (dIn : Nat) (fvs : List RuntimeVal) (vOut : RuntimeVal),
      coerceRuntimeVal (.structField d idx innerW) (.structVal dIn fvs) = some vOut →
      Exists (fun fvsOut => Exists (fun fv => Exists (fun fv' =>
        vOut = .structVal d fvsOut ∧
        fvsOut.length = fvs.length ∧
        listGet? fvs idx = some fv ∧
        listGet? fvsOut idx = some fv' ∧
        coerceRuntimeVal innerW fv = some fv' ∧
        (∀ j, Nat.beq j idx = false → listGet? fvsOut j = listGet? fvs j)))) := by
  intro d idx innerW dIn fvs vOut h
  dsimp only [coerceRuntimeVal] at h
  cases hd : Nat.beq d dIn with
  | false => rw [hd] at h; cases h
  | true =>
    rw [hd] at h
    have hdEq : d = dIn := natBeq_eq_true hd
    cases hget : listGet? fvs idx with
    | none => rw [hget] at h; cases h
    | some fv =>
      rw [hget] at h
      dsimp only at h
      cases hinner : coerceRuntimeVal innerW fv with
      | none => rw [hinner] at h; cases h
      | some fv' =>
        rw [hinner] at h
        injection h with hvOut
        refine ⟨listSet fvs idx fv', fv, fv', ?_, ?_, rfl, ?_, hinner, ?_⟩
        { rw [← hvOut, hdEq] }
        { exact listSet_length fvs idx fv' }
        { exact listGet_listSet_eq fvs idx fv fv' hget }
        { intro j hjne
          exact listGet_listSet_ne fvs idx j fv' hjne }

/-- **Theorem 1B (Pointer Address Preservation Across Coercion):**
    Under arbitrary nesting, `CoerceUnsized` never alters thin data pointer address. -/
theorem coerceWitness_preserves_ptr_address :
    ∀ (w : CoerceWitness) (v v' : RuntimeVal) (addr : Nat),
      coerceRuntimeVal w v = some v' →
      targetPtrAddr w v = some addr →
      targetPtrAddr w v' = some addr
  | .ptrCoerce uw, .ptrVal a mdata, v', addr, hcoerce, haddr => by
    dsimp only [coerceRuntimeVal] at hcoerce
    dsimp only [targetPtrAddr] at haddr
    injection haddr with ha
    cases hm : applyUnsizeMeta uw mdata with
    | none => rw [hm] at hcoerce; cases hcoerce
    | some mdata' =>
      rw [hm] at hcoerce
      injection hcoerce with hv'
      rw [← hv']
      dsimp only [targetPtrAddr]
      exact congrArg some ha
  | .structField d idx innerW, .structVal d' fvs, v', addr, hcoerce, haddr => by
    dsimp only [coerceRuntimeVal] at hcoerce
    dsimp only [targetPtrAddr] at haddr
    cases hd : Nat.beq d d' with
    | false => rw [hd] at hcoerce; cases hcoerce
    | true =>
      rw [hd] at hcoerce
      dsimp only at hcoerce
      cases hget : listGet? fvs idx with
      | none => rw [hget] at hcoerce; cases hcoerce
      | some fv =>
        rw [hget] at hcoerce haddr
        dsimp only at hcoerce haddr
        cases hinner : coerceRuntimeVal innerW fv with
        | none => rw [hinner] at hcoerce; cases hcoerce
        | some fv' =>
          rw [hinner] at hcoerce
          injection hcoerce with hv'
          rw [← hv']
          dsimp only [targetPtrAddr]
          rw [listGet_listSet_eq fvs idx fv fv' hget]
          exact coerceWitness_preserves_ptr_address innerW fv fv' addr hinner haddr
  | .ptrCoerce _, .zstVal, _, _, hcoerce, _ => by dsimp only [coerceRuntimeVal] at hcoerce; cases hcoerce
  | .ptrCoerce _, .scalarVal _, _, _, hcoerce, _ => by dsimp only [coerceRuntimeVal] at hcoerce; cases hcoerce
  | .ptrCoerce _, .structVal _ _, _, _, hcoerce, _ => by dsimp only [coerceRuntimeVal] at hcoerce; cases hcoerce
  | .structField _ _ _, .zstVal, _, _, hcoerce, _ => by dsimp only [coerceRuntimeVal] at hcoerce; cases hcoerce
  | .structField _ _ _, .scalarVal _, _, _, hcoerce, _ => by dsimp only [coerceRuntimeVal] at hcoerce; cases hcoerce
  | .structField _ _ _, .ptrVal _ _, _, _, hcoerce, _ => by dsimp only [coerceRuntimeVal] at hcoerce; cases hcoerce

noncomputable def collectNon1ZstFields (env : TypeEnv) (fuel : Nat) (args : List Ty) :
    List FieldDef → List RuntimeVal → Option (List (Ty × RuntimeVal))
  | [], [] => some []
  | f :: fs, fv :: fvs =>
    let fTy := substTy args f.rawTy
    match collectNon1ZstFields env fuel args fs fvs with
    | none => none
    | some rest =>
      match (layoutOfFuel env.adts fuel fTy).is1Zst with
      | true => some rest
      | false => some ((fTy, fv) :: rest)
  | _, _ => none

noncomputable def extractThinSelfPtr (env : TypeEnv) : Nat → Ty → RuntimeVal → Option (Nat × PtrMeta)
  | 0, _, _ => none
  | Nat.succ fuel, ty, v =>
    match ty, v with
    | .ref _ _ _, .ptrVal addr mdata => some (addr, mdata)
    | .rawPtr _ _, .ptrVal addr mdata => some (addr, mdata)
    | .adt defId args, .structVal d' fvs =>
      match Nat.beq defId d' with
      | false => none
      | true =>
        match lookupAdt env.adts defId with
        | none => none
        | some d =>
          match d.kind with
          | .structKind =>
            match collectNon1ZstFields env fuel args d.fields fvs with
            | some [(singleTy, singleVal)] => extractThinSelfPtr env fuel singleTy singleVal
            | _ => none
          | _ => none
    | _, _ => none

mutual
noncomputable def valShapeMatchesFuel (env : TypeEnv) : Nat → Ty → RuntimeVal → Bool
  | 0, _, _ => true
  | Nat.succ fuel, ty, v =>
    match ty, v with
    | .unit, .zstVal => true
    | .phantom _, .zstVal => true
    | .scalar _ _ _, .scalarVal _ => true
    | .ref _ _ _, .ptrVal _ _ => true
    | .rawPtr _ _, .ptrVal _ _ => true
    | .adt d args, .structVal d' fvs =>
      match Nat.beq d d' with
      | false => false
      | true =>
        match lookupAdt env.adts d with
        | none => false
        | some adtDef => valListMatchesFuel env fuel args adtDef.fields fvs
    | _, _ => false

noncomputable def valListMatchesFuel (env : TypeEnv) (fuel : Nat) (args : List Ty) :
    List FieldDef → List RuntimeVal → Bool
  | [], [] => true
  | f :: fs, fv :: fvs =>
    Bool.and (valShapeMatchesFuel env fuel (substTy args f.rawTy) fv)
      (valListMatchesFuel env fuel args fs fvs)
  | _, _ => false
end

theorem valListMatches_length :
    ∀ (fs : List FieldDef) (fvs : List RuntimeVal) (env : TypeEnv) (fuel : Nat) (args : List Ty),
      valListMatchesFuel env fuel args fs fvs = true → fs.length = fvs.length
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, h => Bool.noConfusion h
  | _ :: _, [], _, _, _, h => Bool.noConfusion h
  | _ :: fs, _ :: fvs, env, fuel, args, h => by
    dsimp only [valListMatchesFuel] at h
    exact congrArg Nat.succ (valListMatches_length fs fvs env fuel args (boolAndRight h))

theorem valListMatches_get :
    ∀ (fs : List FieldDef) (fvs : List RuntimeVal) (env : TypeEnv) (fuel : Nat)
      (args : List Ty) (idx : Nat) (f : FieldDef) (fv : RuntimeVal),
      valListMatchesFuel env fuel args fs fvs = true →
      listGet? fs idx = some f →
      listGet? fvs idx = some fv →
      valShapeMatchesFuel env fuel (substTy args f.rawTy) fv = true
  | [], _, _, _, _, _, _, _, _, hf, _ => by dsimp only [listGet?] at hf; cases hf
  | _ :: _, [], _, _, _, _, _, _, h, _, _ => by dsimp only [valListMatchesFuel] at h; cases h
  | _ :: _, _ :: _, _, _, _, 0, _, _, h, hf, hfv => by
    dsimp only [listGet?] at hf hfv
    injection hf with hf0
    injection hfv with hfv0
    dsimp only [valListMatchesFuel] at h
    rw [← hf0, ← hfv0]
    exact boolAndLeft h
  | _ :: fs, _ :: fvs, env, fuel, args, Nat.succ idx, f, fv, h, hf, hfv => by
    dsimp only [valListMatchesFuel] at h
    exact valListMatches_get fs fvs env fuel args idx f fv (boolAndRight h) hf hfv

theorem collectNon1Zst_empty_of_dispatch_nil :
    ∀ (fs : List FieldDef) (fvs : List RuntimeVal) (env : TypeEnv) (fuel k : Nat) (argsA argsB : List Ty),
      fs.length = fvs.length →
      collectDiffFieldsDispatch env (Nat.succ fuel) argsA argsB k fs = .ok [] →
      collectNon1ZstFields env (Nat.succ fuel) argsA fs fvs = some [] ∧
      collectNon1ZstFields env (Nat.succ fuel) argsB fs fvs = some []
  | [], [], _, _, _, _, _, _, _ => ⟨rfl, rfl⟩
  | [], _ :: _, _, _, _, _, _, hlen, _ => Nat.noConfusion hlen
  | _ :: _, [], _, _, _, _, _, hlen, _ => Nat.noConfusion hlen
  | f :: rest, fv :: fvs', env, fuel, k, argsA, argsB, hlen, h => by
    have hrestLen : rest.length = fvs'.length := Nat.succ.inj hlen
    dsimp only [collectDiffFieldsDispatch] at h
    cases hp : Bool.and (isPhantomTy env (substTy argsA f.rawTy)) (isPhantomTy env (substTy argsB f.rawTy)) with
    | true =>
      rw [hp] at h
      have hzA := isPhantomTy_implies_is1Zst env fuel (substTy argsA f.rawTy) (boolAndLeft hp)
      have hzB := isPhantomTy_implies_is1Zst env fuel (substTy argsB f.rawTy) (boolAndRight hp)
      have ih := collectNon1Zst_empty_of_dispatch_nil rest fvs' env fuel (Nat.succ k) argsA argsB hrestLen h
      dsimp only [collectNon1ZstFields]
      rw [ih.1, ih.2, hzA, hzB]
      exact ⟨rfl, rfl⟩
    | false =>
      rw [hp] at h; dsimp only at h
      cases heq : tyBeq (substTy argsA f.rawTy) (substTy argsB f.rawTy) with
      | false =>
        rw [heq] at h; dsimp only at h
        cases hrec : collectDiffFieldsDispatch env (Nat.succ fuel) argsA argsB (Nat.succ k) rest with
        | err _ => rw [hrec] at h; cases h
        | ok _ => rw [hrec] at h; cases h
      | true =>
        rw [heq] at h; dsimp only at h
        have htyEq : substTy argsA f.rawTy = substTy argsB f.rawTy := tyBeq_eq_true heq
        cases hnr : hasNonRegionParam (substTy argsA f.rawTy) with
        | true => rw [hnr] at h; cases h
        | false =>
          rw [hnr] at h; dsimp only at h
          cases hz : (layoutOfFuel env.adts (Nat.succ fuel) (substTy argsA f.rawTy)).is1Zst with
          | false => rw [hz] at h; cases h
          | true =>
            rw [hz] at h
            have ih := collectNon1Zst_empty_of_dispatch_nil rest fvs' env fuel (Nat.succ k) argsA argsB hrestLen h
            dsimp only [collectNon1ZstFields]
            rw [ih.1, ih.2, hz]
            dsimp only
            rw [← htyEq, hz]
            exact ⟨rfl, rfl⟩

theorem collectNon1Zst_singleton_of_dispatch_single :
    ∀ (fs : List FieldDef) (fvs : List RuntimeVal) (env : TypeEnv) (fuel startIdx idx : Nat)
      (argsA argsB : List Ty) (innerA innerB : Ty),
      fs.length = fvs.length →
      collectDiffFieldsDispatch env (Nat.succ fuel) argsA argsB startIdx fs = .ok [(idx, innerA, innerB)] →
      (layoutOfFuel env.adts (Nat.succ fuel) innerA).is1Zst = false →
      (layoutOfFuel env.adts (Nat.succ fuel) innerB).is1Zst = false →
      Exists (fun off => Exists (fun fv => Exists (fun fdef =>
        idx = startIdx + off ∧
        listGet? fs off = some fdef ∧
        substTy argsA fdef.rawTy = innerA ∧
        substTy argsB fdef.rawTy = innerB ∧
        listGet? fvs off = some fv ∧
        collectNon1ZstFields env (Nat.succ fuel) argsA fs fvs = some [(innerA, fv)] ∧
        (∀ fv', collectNon1ZstFields env (Nat.succ fuel) argsB fs (listSet fvs off fv') = some [(innerB, fv')]))))
  | [], _, _, _, _, _, _, _, _, _, _, h, _, _ => by
    dsimp only [collectDiffFieldsDispatch] at h
    cases h
  | _ :: _, [], _, _, _, _, _, _, _, _, hlen, _, _, _ => Nat.noConfusion hlen
  | f :: rest, fv :: fvs', env, fuel, startIdx, idx, argsA, argsB, innerA, innerB, hlen, h, hzA, hzB => by
    have hrestLen : rest.length = fvs'.length := Nat.succ.inj hlen
    dsimp only [collectDiffFieldsDispatch] at h
    cases hp : Bool.and (isPhantomTy env (substTy argsA f.rawTy)) (isPhantomTy env (substTy argsB f.rawTy)) with
    | true =>
      rw [hp] at h
      have hfzA := isPhantomTy_implies_is1Zst env fuel (substTy argsA f.rawTy) (boolAndLeft hp)
      have hfzB := isPhantomTy_implies_is1Zst env fuel (substTy argsB f.rawTy) (boolAndRight hp)
      have ⟨off, fvRec, fdef, hidx, hfdef, hA, hB, hget, hcA, hcB⟩ :=
        collectNon1Zst_singleton_of_dispatch_single rest fvs' env fuel (Nat.succ startIdx) idx argsA argsB innerA innerB hrestLen h hzA hzB
      refine ⟨Nat.succ off, fvRec, fdef, ?_, hfdef, hA, hB, hget, ?_, ?_⟩
      { rw [Nat.add_succ, ← Nat.succ_add]; exact hidx }
      { dsimp only [collectNon1ZstFields]
        rw [hcA, hfzA] }
      { intro fv'
        dsimp only [listSet, collectNon1ZstFields]
        rw [hcB fv', hfzB] }
    | false =>
      rw [hp] at h; dsimp only at h
      cases heq : tyBeq (substTy argsA f.rawTy) (substTy argsB f.rawTy) with
      | false =>
        rw [heq] at h; dsimp only at h
        cases hrec : collectDiffFieldsDispatch env (Nat.succ fuel) argsA argsB (Nat.succ startIdx) rest with
        | err _ => rw [hrec] at h; cases h
        | ok td =>
          rw [hrec] at h
          cases td with
          | cons _ _ => cases h
          | nil =>
            injection h with hl
            injection hl with hpair
            injection hpair with hidx hpair2
            injection hpair2 with hA hB
            have hEmpty := collectNon1Zst_empty_of_dispatch_nil rest fvs' env fuel (Nat.succ startIdx) argsA argsB hrestLen hrec
            refine ⟨0, fv, f, ?_, rfl, hA, hB, rfl, ?_, ?_⟩
            { rw [Nat.add_zero]; exact hidx.symm }
            { dsimp only [collectNon1ZstFields]
              rw [hEmpty.1, hA, hzA] }
            { intro fv'
              dsimp only [listSet, collectNon1ZstFields]
              rw [hEmpty.2, hB, hzB] }
      | true =>
        rw [heq] at h; dsimp only at h
        have htyEq : substTy argsA f.rawTy = substTy argsB f.rawTy := tyBeq_eq_true heq
        cases hnr : hasNonRegionParam (substTy argsA f.rawTy) with
        | true => rw [hnr] at h; cases h
        | false =>
          rw [hnr] at h; dsimp only at h
          cases hfz : (layoutOfFuel env.adts (Nat.succ fuel) (substTy argsA f.rawTy)).is1Zst with
          | false => rw [hfz] at h; cases h
          | true =>
            rw [hfz] at h
            have ⟨off, fvRec, fdef, hidx, hfdef, hA, hB, hget, hcA, hcB⟩ :=
              collectNon1Zst_singleton_of_dispatch_single rest fvs' env fuel (Nat.succ startIdx) idx argsA argsB innerA innerB hrestLen h hzA hzB
            refine ⟨Nat.succ off, fvRec, fdef, ?_, hfdef, hA, hB, hget, ?_, ?_⟩
            { rw [Nat.add_succ, ← Nat.succ_add]; exact hidx }
            { dsimp only [collectNon1ZstFields]
              rw [hcA, hfz] }
            { intro fv'
              dsimp only [listSet, collectNon1ZstFields]
              rw [hcB fv', ← htyEq, hfz] }

theorem extractThinSelfPtr_adt_singleton :
    ∀ (env : TypeEnv) (fuel defId d' : Nat) (args : List Ty) (fvs : List RuntimeVal)
      (d : AdtDef) (singleTy : Ty) (singleVal : RuntimeVal),
      Nat.beq defId d' = true →
      lookupAdt env.adts defId = some d →
      d.kind = .structKind →
      collectNon1ZstFields env fuel args d.fields fvs = some [(singleTy, singleVal)] →
      extractThinSelfPtr env (Nat.succ fuel) (.adt defId args) (.structVal d' fvs) =
      extractThinSelfPtr env fuel singleTy singleVal := by
  intro env fuel defId d' args fvs d singleTy singleVal hbeq hl hk hcol
  dsimp only [extractThinSelfPtr]
  rw [hbeq, hl]
  dsimp only
  rw [hk]
  dsimp only
  rw [hcol]

/-- **Theorem 2A & 2B (`DispatchFromDyn` ABI Register-Equivalence):**
    1. Every value matching a `DispatchFromDyn`-admissible receiver has a unique
       non-1-ZST scalar-pair pointer extracted by `extractThinSelfPtr` (`make_thin_self_ptr`).
    2. Coercing via `coerceRuntimeVal` preserves that exact thin data pointer `addr`
       while updating ONLY its vtable/slice metadata (`*mut ()` thunk ABI equivalence). -/
theorem dispatchFromDyn_abi_register_equivalence :
    ∀ (fuel : Nat) (env : TypeEnv) (src dst : Ty) (w : CoerceWitness) (v : RuntimeVal),
      checkDispatchFromDynFuel env fuel src dst = .ok w →
      valShapeMatchesFuel env fuel src v = true →
      (Exists (fun addr => Exists (fun mdata => extractThinSelfPtr env fuel src v = some (addr, mdata)))) ∧
      (∀ addr mdata v',
        extractThinSelfPtr env fuel src v = some (addr, mdata) →
        coerceRuntimeVal w v = some v' →
        Exists (fun mdata' => extractThinSelfPtr env fuel dst v' = some (addr, mdata')))
  | 0, _, _, _, _, _, hchk, _ => by dsimp only [checkDispatchFromDynFuel] at hchk; cases hchk
  | Nat.succ 0, env, src, dst, _, _, hchk, _ => by
    cases src with
    | ref rA mA ptA =>
      cases dst with
      | ref rB mB ptB =>
        dsimp only [checkDispatchFromDynFuel] at hchk
        cases hok : Bool.and (Nat.beq rA rB) (mutBeq mA mB) with
        | false => rw [hok] at hchk; cases hchk
        | true =>
          rw [hok] at hchk
          dsimp only [checkUnsizeFuel] at hchk
          cases hchk
      | _ => dsimp only [checkDispatchFromDynFuel] at hchk; cases hchk
    | rawPtr mA ptA =>
      cases dst with
      | rawPtr mB ptB =>
        dsimp only [checkDispatchFromDynFuel] at hchk
        cases hm : mutBeq mA mB with
        | false => rw [hm] at hchk; cases hchk
        | true =>
          rw [hm] at hchk
          dsimp only [checkUnsizeFuel] at hchk
          cases hchk
      | _ => dsimp only [checkDispatchFromDynFuel] at hchk; cases hchk
    | adt dA argsA =>
      cases dst with
      | adt dB argsB =>
        dsimp only [checkDispatchFromDynFuel] at hchk
        cases hd : Nat.beq dA dB with
        | false => rw [hd] at hchk; cases hchk
        | true =>
          rw [hd] at hchk
          cases hl : lookupAdt env.adts dA with
          | none => rw [hl] at hchk; cases hchk
          | some d =>
            rw [hl] at hchk; dsimp only at hchk
            cases hk : Bool.and (match d.kind with | .structKind => true | _ => false) (Bool.not d.isLangPhantom) with
            | false => rw [hk] at hchk; cases hchk
            | true =>
              rw [hk] at hchk; dsimp only at hchk
              cases hr : reprAllowedForDispatch d.repr with
              | false => rw [hr] at hchk; cases hchk
              | true =>
                rw [hr] at hchk; dsimp only at hchk
                cases hdiffs : collectDiffFieldsDispatch env 0 argsA argsB 0 d.fields with
                | err _ => rw [hdiffs] at hchk; cases hchk
                | ok diffs =>
                  rw [hdiffs] at hchk
                  cases diffs with
                  | nil => cases hchk
                  | cons head tail =>
                    cases tail with
                    | cons _ _ => cases hchk
                    | nil =>
                      dsimp only at hchk
                      cases hchk
      | _ => dsimp only [checkDispatchFromDynFuel] at hchk; cases hchk
    | _ => dsimp only [checkDispatchFromDynFuel] at hchk; cases hchk
  | Nat.succ (Nat.succ f'), env, src, dst, w, v, hchk, hshape => by
    cases src <;> cases dst
    case ref.ref rA mA ptA rB mB ptB =>
      cases v with
      | ptrVal addr mdata =>
        dsimp only [checkDispatchFromDynFuel] at hchk
        cases hok : Bool.and (Nat.beq rA rB) (mutBeq mA mB) with
        | false => rw [hok] at hchk; cases hchk
        | true =>
          rw [hok] at hchk
          cases hu : checkUnsizeFuel env (Nat.succ f') ptA ptB with
          | err _ => rw [hu] at hchk; cases hchk
          | ok uw =>
            rw [hu] at hchk
            injection hchk with hw
            constructor
            { exact ⟨addr, mdata, rfl⟩ }
            { intro addr0 mdata0 v' hex hco
              dsimp only [extractThinSelfPtr] at hex
              injection hex with hp0
              injection hp0 with ha0 _
              rw [← hw] at hco
              dsimp only [coerceRuntimeVal] at hco
              cases ha : applyUnsizeMeta uw mdata with
              | none => rw [ha] at hco; cases hco
              | some mdata' =>
                rw [ha] at hco
                injection hco with hv'
                rw [← hv', ha0]
                exact ⟨mdata', rfl⟩ }
      | zstVal => dsimp only [valShapeMatchesFuel] at hshape; cases hshape
      | scalarVal _ => dsimp only [valShapeMatchesFuel] at hshape; cases hshape
      | structVal _ _ => dsimp only [valShapeMatchesFuel] at hshape; cases hshape
    case rawPtr.rawPtr mA ptA mB ptB =>
      cases v with
      | ptrVal addr mdata =>
        dsimp only [checkDispatchFromDynFuel] at hchk
        cases hm : mutBeq mA mB with
        | false => rw [hm] at hchk; cases hchk
        | true =>
          rw [hm] at hchk
          cases hu : checkUnsizeFuel env (Nat.succ f') ptA ptB with
          | err _ => rw [hu] at hchk; cases hchk
          | ok uw =>
            rw [hu] at hchk
            injection hchk with hw
            constructor
            { exact ⟨addr, mdata, rfl⟩ }
            { intro addr0 mdata0 v' hex hco
              dsimp only [extractThinSelfPtr] at hex
              injection hex with hp0
              injection hp0 with ha0 _
              rw [← hw] at hco
              dsimp only [coerceRuntimeVal] at hco
              cases ha : applyUnsizeMeta uw mdata with
              | none => rw [ha] at hco; cases hco
              | some mdata' =>
                rw [ha] at hco
                injection hco with hv'
                rw [← hv', ha0]
                exact ⟨mdata', rfl⟩ }
      | zstVal => dsimp only [valShapeMatchesFuel] at hshape; cases hshape
      | scalarVal _ => dsimp only [valShapeMatchesFuel] at hshape; cases hshape
      | structVal _ _ => dsimp only [valShapeMatchesFuel] at hshape; cases hshape
    case adt.adt dA argsA dB argsB =>
      cases v with
      | zstVal => dsimp only [valShapeMatchesFuel] at hshape; cases hshape
      | scalarVal _ => dsimp only [valShapeMatchesFuel] at hshape; cases hshape
      | ptrVal _ _ => dsimp only [valShapeMatchesFuel] at hshape; cases hshape
      | structVal d' fvs =>
        dsimp only [checkDispatchFromDynFuel] at hchk
        cases hd : Nat.beq dA dB with
        | false => rw [hd] at hchk; cases hchk
        | true =>
          rw [hd] at hchk
          have hdEq : dA = dB := natBeq_eq_true hd
          cases hl : lookupAdt env.adts dA with
          | none => rw [hl] at hchk; cases hchk
          | some adtDef =>
            rw [hl] at hchk; dsimp only at hchk
            cases hk : Bool.and (match adtDef.kind with | .structKind => true | _ => false) (Bool.not adtDef.isLangPhantom) with
            | false => rw [hk] at hchk; cases hchk
            | true =>
              rw [hk] at hchk; dsimp only at hchk
              have hKind : adtDef.kind = .structKind := by
                have hkL := boolAndLeft hk
                cases adk : adtDef.kind with
                | structKind => rfl
                | enumKind => rw [adk] at hkL; cases hkL
                | unionKind => rw [adk] at hkL; cases hkL
              cases hrepr : reprAllowedForDispatch adtDef.repr with
              | false => rw [hrepr] at hchk; cases hchk
              | true =>
                rw [hrepr] at hchk; dsimp only at hchk
                cases hdiffs : collectDiffFieldsDispatch env (Nat.succ f') argsA argsB 0 adtDef.fields with
                | err _ => rw [hdiffs] at hchk; cases hchk
                | ok diffs =>
                  rw [hdiffs] at hchk
                  cases diffs with
                  | nil => cases hchk
                  | cons head tail =>
                    cases tail with
                    | cons _ _ => cases hchk
                    | nil =>
                      dsimp only at hchk
                      change (match checkDispatchFromDynFuel env (Nat.succ f') head.2.1 head.2.2 with
                        | CheckResult.ok innerW => CheckResult.ok (CoerceWitness.structField dA head.1 innerW)
                        | CheckResult.err e => CheckResult.err e) = _ at hchk
                      cases hinner : checkDispatchFromDynFuel env (Nat.succ f') head.2.1 head.2.2 with
                      | err _ => rw [hinner] at hchk; cases hchk
                      | ok innerW =>
                        rw [hinner] at hchk
                        injection hchk with hw
                        dsimp only [valShapeMatchesFuel] at hshape
                        cases hd' : Nat.beq dA d' with
                        | false => rw [hd'] at hshape; cases hshape
                        | true =>
                          rw [hd'] at hshape
                          rw [hl] at hshape
                          dsimp only at hshape
                          have hlen := valListMatches_length adtDef.fields fvs env (Nat.succ f') argsA hshape
                          have hnon1 := dispatchFromDyn_strong_non_1zst (Nat.succ f') env head.2.1 head.2.2 innerW hinner
                          have ⟨off, fv, fdef, hidx, hfdef, hA, hB, hget, hcA, hcB⟩ :=
                            collectNon1Zst_singleton_of_dispatch_single adtDef.fields fvs env f' 0 head.1 argsA argsB head.2.1 head.2.2 hlen hdiffs hnon1.1.2 hnon1.2.2
                          have hZeroAdd : 0 + off = off := Nat.zero_add off
                          rw [hZeroAdd] at hidx
                          have hfvShape : valShapeMatchesFuel env (Nat.succ f') head.2.1 fv = true := by
                            rw [← hA]
                            exact valListMatches_get adtDef.fields fvs env (Nat.succ f') argsA off fdef fv hshape hfdef hget
                          have ih := dispatchFromDyn_abi_register_equivalence (Nat.succ f') env head.2.1 head.2.2 innerW fv hinner hfvShape
                          constructor
                          { have ⟨addr, mdata, hex⟩ := ih.1
                            refine ⟨addr, mdata, ?_⟩
                            rw [extractThinSelfPtr_adt_singleton env (Nat.succ f') dA d' argsA fvs adtDef head.2.1 fv hd' hl hKind hcA]
                            exact hex }
                          { intro addr mdata v' hex hco
                            rw [extractThinSelfPtr_adt_singleton env (Nat.succ f') dA d' argsA fvs adtDef head.2.1 fv hd' hl hKind hcA] at hex
                            rw [← hw] at hco
                            dsimp only [coerceRuntimeVal] at hco
                            rw [hd', hidx, hget] at hco
                            dsimp only at hco
                            cases hic : coerceRuntimeVal innerW fv with
                            | none => rw [hic] at hco; cases hco
                            | some fv' =>
                              rw [hic] at hco
                              injection hco with hv'
                              have ⟨mdata', hex'⟩ := ih.2 addr mdata fv' hex hic
                              refine ⟨mdata', ?_⟩
                              rw [← hv', ← hdEq]
                              rw [extractThinSelfPtr_adt_singleton env (Nat.succ f') dA d' argsB (listSet fvs off fv') adtDef head.2.2 fv' hd' hl hKind (hcB fv')]
                              exact hex' }
    all_goals (dsimp only [checkDispatchFromDynFuel] at hchk; cases hchk)

/-- **Corollary (`adding_1zst_siblings_preserves_thin_self_ptr`):**
    Wrapping any valid pointer in arbitrary leading/trailing concrete 1-ZST fields leaves
    both `DispatchFromDyn` admissibility and extracted `(addr, mdata)` intact. -/
theorem adding_1zst_siblings_preserves_thin_self_ptr :
    ∀ (env : TypeEnv) (fuel wrapId ptrFieldId zstId : Nat)
      (m : Mutability) (srcPointee : Ty) (addr : Nat) (mdata : PtrMeta),
      lookupAdt env.adts wrapId = some {
        defId := wrapId
        kind := .structKind
        repr := .reprRust
        numParams := 1
        fields := [
          { fieldId := 1, rawTy := .unit },
          { fieldId := ptrFieldId, rawTy := .rawPtr m (.param 0) },
          { fieldId := zstId, rawTy := .phantom (.param 0) }
        ]
        isLangPhantom := false
      } →
      extractThinSelfPtr env (Nat.succ (Nat.succ fuel)) (.adt wrapId [srcPointee])
        (.structVal wrapId [.zstVal, .ptrVal addr mdata, .zstVal]) =
      extractThinSelfPtr env (Nat.succ fuel) (.rawPtr m srcPointee) (.ptrVal addr mdata) := by
  intro env fuel wrapId _ _ m srcPointee addr mdata hlook
  dsimp only [extractThinSelfPtr]
  rw [natBeq_refl wrapId, hlook]
  rfl

/-!
## Section 6: Constructive Kernel-Checked Counterexamples (`E0374`/`E0375`/`E0377`/`E0378`/`E0277`/Prefix)
-/

noncomputable def tyU8 : Ty := .scalar 1 1 1
noncomputable def tyU16 : Ty := .scalar 2 2 2
noncomputable def tyU32 : Ty := .scalar 3 4 4

noncomputable def defMyPtr : AdtDef := {
  defId := 1, kind := .structKind, repr := .reprRust, numParams := 1,
  fields := [{ fieldId := 0, rawTy := .rawPtr .imm (.param 0) }],
  isLangPhantom := false
}

noncomputable def defMyUnit : AdtDef := {
  defId := 20, kind := .structKind, repr := .reprRust, numParams := 0,
  fields := [], isLangPhantom := false
}

noncomputable def defTaggedPtr : AdtDef := {
  defId := 2, kind := .structKind, repr := .reprRust, numParams := 1,
  fields := [
    { fieldId := 0, rawTy := .rawPtr .imm (.param 0) },
    { fieldId := 1, rawTy := .adt 20 [] }
  ],
  isLangPhantom := false
}

noncomputable def defZeroFields : AdtDef := {
  defId := 3, kind := .structKind, repr := .reprRust, numParams := 1,
  fields := [
    { fieldId := 0, rawTy := tyU32 },
    { fieldId := 1, rawTy := .phantom (.param 0) }
  ],
  isLangPhantom := false
}

noncomputable def defTwoPtrs : AdtDef := {
  defId := 4, kind := .structKind, repr := .reprRust, numParams := 1,
  fields := [
    { fieldId := 0, rawTy := .rawPtr .imm (.param 0) },
    { fieldId := 1, rawTy := .rawPtr .imm (.param 0) }
  ],
  isLangPhantom := false
}

noncomputable def defPtrA : AdtDef := {
  defId := 5, kind := .structKind, repr := .reprRust, numParams := 1,
  fields := [{ fieldId := 0, rawTy := .rawPtr .imm (.param 0) }], isLangPhantom := false
}
noncomputable def defPtrB : AdtDef := {
  defId := 6, kind := .structKind, repr := .reprRust, numParams := 1,
  fields := [{ fieldId := 0, rawTy := .rawPtr .imm (.param 0) }], isLangPhantom := false
}
noncomputable def defEnumPtr : AdtDef := {
  defId := 7, kind := .enumKind, repr := .reprRust, numParams := 1,
  fields := [{ fieldId := 0, rawTy := .rawPtr .imm (.param 0) }], isLangPhantom := false
}

noncomputable def defAlign8Zst : AdtDef := {
  defId := 21, kind := .structKind, repr := .reprRust, numParams := 0,
  fields := [{ fieldId := 0, rawTy := .array (.scalar 4 8 8) 0 }],
  isLangPhantom := false
}
noncomputable def defMarkerGeneric : AdtDef := {
  defId := 22, kind := .structKind, repr := .reprRust, numParams := 1,
  fields := [{ fieldId := 0, rawTy := .phantom (.param 0) }],
  isLangPhantom := false
}
noncomputable def defBadExtraU32 : AdtDef := {
  defId := 8, kind := .structKind, repr := .reprRust, numParams := 1,
  fields := [{ fieldId := 0, rawTy := .rawPtr .imm (.param 0) }, { fieldId := 1, rawTy := tyU32 }],
  isLangPhantom := false
}
noncomputable def defBadAlign8Zst : AdtDef := {
  defId := 9, kind := .structKind, repr := .reprRust, numParams := 1,
  fields := [{ fieldId := 0, rawTy := .rawPtr .imm (.param 0) }, { fieldId := 1, rawTy := .adt 21 [] }],
  isLangPhantom := false
}
noncomputable def defBadGenericZst : AdtDef := {
  defId := 10, kind := .structKind, repr := .reprRust, numParams := 2,
  fields := [
    { fieldId := 0, rawTy := .rawPtr .imm (.param 0) },
    { fieldId := 1, rawTy := .adt 22 [.param 1] }
  ],
  isLangPhantom := false
}
noncomputable def defBadReprC : AdtDef := {
  defId := 11, kind := .structKind, repr := .reprC, numParams := 1,
  fields := [{ fieldId := 0, rawTy := .rawPtr .imm (.param 0) }],
  isLangPhantom := false
}
noncomputable def defBadReprPacked : AdtDef := {
  defId := 12, kind := .structKind, repr := .reprPacked 1, numParams := 1,
  fields := [{ fieldId := 0, rawTy := .rawPtr .imm (.param 0) }],
  isLangPhantom := false
}

noncomputable def defPacket : AdtDef := {
  defId := 13, kind := .structKind, repr := .reprC, numParams := 1,
  fields := [
    { fieldId := 0, rawTy := tyU32 },
    { fieldId := 1, rawTy := tyU16 },
    { fieldId := 2, rawTy := .param 0 }
  ],
  isLangPhantom := false
}
noncomputable def defMiddleUnsized : AdtDef := {
  defId := 14, kind := .structKind, repr := .reprRust, numParams := 1,
  fields := [{ fieldId := 0, rawTy := .param 0 }, { fieldId := 1, rawTy := tyU32 }],
  isLangPhantom := false
}
noncomputable def defTwoUnsized : AdtDef := {
  defId := 15, kind := .structKind, repr := .reprRust, numParams := 2,
  fields := [{ fieldId := 0, rawTy := .param 0 }, { fieldId := 1, rawTy := .param 1 }],
  isLangPhantom := false
}
noncomputable def defPrefixCapturesParam : AdtDef := {
  defId := 16, kind := .structKind, repr := .reprRust, numParams := 1,
  fields := [
    { fieldId := 0, rawTy := .rawPtr .imm (.param 0) },
    { fieldId := 1, rawTy := .param 0 }
  ],
  isLangPhantom := false
}
noncomputable def defRustPacket : AdtDef := {
  defId := 17, kind := .structKind, repr := .reprRust, numParams := 1,
  fields := [{ fieldId := 0, rawTy := tyU32 }, { fieldId := 1, rawTy := .param 0 }],
  isLangPhantom := false
}

noncomputable def stdEnv : TypeEnv := {
  adts := [
    defMyPtr, defTaggedPtr, defZeroFields, defTwoPtrs, defPtrA, defPtrB,
    defEnumPtr, defBadExtraU32, defBadAlign8Zst, defBadGenericZst, defBadReprC,
    defBadReprPacked, defPacket, defMiddleUnsized, defTwoUnsized,
    defPrefixCapturesParam, defRustPacket, defMyUnit, defAlign8Zst, defMarkerGeneric
  ]
  traitImpls := [{ concreteTy := .scalar 99 4 4, traitId := 10, vtableId := 77 }]
  regionSub := fun a b => Nat.beq a b
}

-- Positive Witnesses
theorem valid_myptr_slice_coerce_and_dispatch :
    checkDispatchFromDynFuel stdEnv 6 (.adt 1 [.array tyU8 4]) (.adt 1 [.slice tyU8]) =
    .ok (.structField 1 0 (.ptrCoerce (.arrayToSlice tyU8 4))) := rfl

theorem valid_myptr_dyn_coerce_and_dispatch :
    checkDispatchFromDynFuel stdEnv 6 (.adt 1 [.scalar 99 4 4]) (.adt 1 [.traitObj 10]) =
    .ok (.structField 1 0 (.ptrCoerce (.concreteToDyn (.scalar 99 4 4) 10 77))) := rfl

theorem valid_tagged_non_generic_1zst_dispatch :
    checkDispatchFromDynFuel stdEnv 6 (.adt 2 [.scalar 99 4 4]) (.adt 2 [.traitObj 10]) =
    .ok (.structField 2 0 (.ptrCoerce (.concreteToDyn (.scalar 99 4 4) 10 77))) := rfl

-- E0374 / E0375 / E0377 (incl. folded E0376) Counterexamples
theorem e0374_zero_fields_rejected :
    checkCoerceUnsizedFuel stdEnv 6 (.adt 3 [.array tyU8 4]) (.adt 3 [.slice tyU8]) =
    .err .e0374NoField := rfl

theorem e0375_multi_fields_rejected :
    checkCoerceUnsizedFuel stdEnv 6 (.adt 4 [.array tyU8 4]) (.adt 4 [.slice tyU8]) =
    .err .e0375MultiField := rfl

theorem e0375_ambiguity_counterexample :
    let vIn := RuntimeVal.structVal 4 [
      RuntimeVal.ptrVal 100 .thin,
      RuntimeVal.ptrVal 200 .thin
    ]
    let wLeft := CoerceWitness.structField 4 0 (.ptrCoerce (.arrayToSlice tyU8 4))
    let wRight := CoerceWitness.structField 4 1 (.ptrCoerce (.arrayToSlice tyU8 4))
    coerceRuntimeVal wLeft vIn = some (.structVal 4 [.ptrVal 100 (.sliceLen 4), .ptrVal 200 .thin]) ∧
    coerceRuntimeVal wRight vIn = some (.structVal 4 [.ptrVal 100 .thin, .ptrVal 200 (.sliceLen 4)]) := ⟨rfl, rfl⟩

theorem e0377_distinct_structs_rejected :
    checkCoerceUnsizedFuel stdEnv 6 (.adt 5 [.array tyU8 4]) (.adt 6 [.slice tyU8]) =
    .err .e0377SameStructOrNonStruct := rfl

theorem e0377_enum_rejected_formerly_e0376 :
    checkCoerceUnsizedFuel stdEnv 6 (.adt 7 [.array tyU8 4]) (.adt 7 [.slice tyU8]) =
    .err .e0377SameStructOrNonStruct := rfl

-- E0378 Separation (`CoerceUnsized` succeeds, `DispatchFromDyn` fails!) & ABI Break
theorem e0378_extra_u32_coerce_ok_dispatch_rejected :
    checkCoerceUnsizedFuel stdEnv 6 (.adt 8 [.scalar 99 4 4]) (.adt 8 [.traitObj 10]) =
      .ok (.structField 8 0 (.ptrCoerce (.concreteToDyn (.scalar 99 4 4) 10 77))) ∧
    checkDispatchFromDynFuel stdEnv 6 (.adt 8 [.scalar 99 4 4]) (.adt 8 [.traitObj 10]) =
      .err .e0378DispatchExtraNon1Zst := ⟨rfl, rfl⟩

theorem e0378_extra_u32_breaks_thin_ptr_extraction :
    extractThinSelfPtr stdEnv 6 (.adt 8 [.traitObj 10])
      (.structVal 8 [.ptrVal 4096 (.vtable 77), .scalarVal 42]) = none := rfl

theorem e0378_overaligned_zst_coerce_ok_dispatch_rejected :
    checkCoerceUnsizedFuel stdEnv 6 (.adt 9 [.scalar 99 4 4]) (.adt 9 [.traitObj 10]) =
      .ok (.structField 9 0 (.ptrCoerce (.concreteToDyn (.scalar 99 4 4) 10 77))) ∧
    checkDispatchFromDynFuel stdEnv 6 (.adt 9 [.scalar 99 4 4]) (.adt 9 [.traitObj 10]) =
      .err .e0378DispatchExtraNon1Zst := ⟨rfl, rfl⟩

theorem e0378_generic_zst_polymorphic_rejected :
    checkCoerceUnsizedFuel stdEnv 6 (.adt 10 [.scalar 99 4 4, .param 1]) (.adt 10 [.traitObj 10, .param 1]) =
      .ok (.structField 10 0 (.ptrCoerce (.concreteToDyn (.scalar 99 4 4) 10 77))) ∧
    checkDispatchFromDynFuel stdEnv 6 (.adt 10 [.scalar 99 4 4, .param 1]) (.adt 10 [.traitObj 10, .param 1]) =
      .err .e0378DispatchExtraGenericParam := ⟨rfl, rfl⟩

theorem e0378_repr_c_coerce_ok_dispatch_rejected :
    checkCoerceUnsizedFuel stdEnv 6 (.adt 11 [.scalar 99 4 4]) (.adt 11 [.traitObj 10]) =
      .ok (.structField 11 0 (.ptrCoerce (.concreteToDyn (.scalar 99 4 4) 10 77))) ∧
    checkDispatchFromDynFuel stdEnv 6 (.adt 11 [.scalar 99 4 4]) (.adt 11 [.traitObj 10]) =
      .err .e0378DispatchReprForbidden := ⟨rfl, rfl⟩

theorem e0378_repr_packed_coerce_ok_dispatch_rejected :
    checkCoerceUnsizedFuel stdEnv 6 (.adt 12 [.scalar 99 4 4]) (.adt 12 [.traitObj 10]) =
      .ok (.structField 12 0 (.ptrCoerce (.concreteToDyn (.scalar 99 4 4) 10 77))) ∧
    checkDispatchFromDynFuel stdEnv 6 (.adt 12 [.scalar 99 4 4]) (.adt 12 [.traitObj 10]) =
      .err .e0378DispatchReprForbidden := ⟨rfl, rfl⟩

-- E0277 Tail-Only `?Sized`, Prefix Offsets, & Prefix-Param Capture (`E0308`)
theorem packet_custom_dst_wf_and_unsize_ok :
    wfAdtFields stdEnv 5 defPacket [.slice tyU16] = .ok ∧
    unsizingParamsForAdt defPacket = [0] ∧
    checkUnsizeFuel stdEnv 6 (.adt 13 [.array tyU16 4]) (.adt 13 [.slice tyU16]) =
      .ok (.structTail 13 2 (.arrayToSlice tyU16 4)) := ⟨rfl, rfl, rfl⟩

theorem packet_prefix_offsets_invariant_concrete :
    computePrefixOffsets stdEnv.adts 5 .reprC [.array tyU16 4] 0 1 (dropLast defPacket.fields) =
      some ([0, 4], 6, 4) ∧
    computePrefixOffsets stdEnv.adts 5 .reprC [.slice tyU16] 0 1 (dropLast defPacket.fields) =
      some ([0, 4], 6, 4) := ⟨rfl, rfl⟩

theorem e0277_middle_unsized_rejected :
    wfAdtFields stdEnv 5 defMiddleUnsized [.slice tyU8] = .e0277NonLastUnsized := rfl

theorem e0277_two_unsized_rejected :
    wfAdtFields stdEnv 5 defTwoUnsized [.slice tyU8, .slice tyU8] = .e0277NonLastUnsized := rfl

theorem prefix_mentions_param_wf_ok_yet_unsize_rejected :
    wfAdtFields stdEnv 5 defPrefixCapturesParam [.slice tyU8] = .ok ∧
    unsizingParamsForAdt defPrefixCapturesParam = [] ∧
    checkUnsizeFuel stdEnv 6 (.adt 16 [.array tyU8 4]) (.adt 16 [.slice tyU8]) =
      .err .e0308PrefixParamCapture := ⟨rfl, rfl, rfl⟩

/-!
## Section 7: `zerocopy` DST Layout, `from_bytes_with_elems`, & `#[repr(C)]` Duality
-/

structure TrailingSliceLayout where
  prefixSize : Nat
  prefixAlign : Nat
  elemSize : Nat
  elemAlign : Nat
  repr : ReprKind

noncomputable def trailingDstAlign (l : TrailingSliceLayout) : Nat :=
  maxNat l.prefixAlign l.elemAlign

noncomputable def trailingSizeBase (l : TrailingSliceLayout) : Nat :=
  alignUp l.prefixSize l.elemAlign

noncomputable def trailingSizeForElems (l : TrailingSliceLayout) (elems : Nat) : Nat :=
  alignUp (trailingSizeBase l + elems * l.elemSize) (trailingDstAlign l)

noncomputable def zerocopyDeriveDstEligible (d : AdtDef) : Bool :=
  match d.kind, d.repr with
  | .structKind, .reprC =>
    match lastElem? d.fields with
    | some _ => true
    | none => false
  | _, _ => false

noncomputable def fromBytesWithElemsValid (l : TrailingSliceLayout) (addr bytesLen elems : Nat) : Bool :=
  let al := trailingDstAlign l
  let reqBytes := trailingSizeForElems l elems
  Bool.and (Nat.ble 1 l.elemSize)
    (Bool.and (Nat.beq (Nat.mod addr al) 0) (Nat.beq reqBytes bytesLen))

inductive TrailingCastType where
  | castPrefix : TrailingCastType
  | castSuffix : TrailingCastType

noncomputable def trailingSizePhaseBase (l : TrailingSliceLayout) : Nat :=
  trailingSizeBase l

noncomputable def trailingNormSizeBase (l : TrailingSliceLayout) : Nat :=
  roundDown (trailingSizePhaseBase l) (trailingDstAlign l)

noncomputable def trailingNormSizePhase (l : TrailingSliceLayout) : Nat :=
  Nat.mod (trailingSizePhaseBase l) (trailingDstAlign l)

/-- Models `DstLayout::validate_cast_and_convert_metadata` (`google/zerocopy/src/layout.rs:1705-1852`)
    with normalized alignment-unit base `trailingNormSizeBase` and phase `trailingNormSizePhase`. -/
noncomputable def validateCastAndConvertMetadata (l : TrailingSliceLayout)
    (addr bytesLen : Nat) (ct : TrailingCastType) : Option (Nat × Nat) :=
  let al := trailingDstAlign l
  let minAligned := alignUp (trailingSizePhaseBase l) al
  let sBase := trailingNormSizeBase l
  let sPhase := trailingNormSizePhase l
  let off := match ct with | .castPrefix => 0 | .castSuffix => bytesLen
  match Nat.ble 1 l.elemSize with
  | false => none
  | true =>
    match Nat.beq (Nat.mod (addr + off) al) 0 with
    | false => none
    | true =>
      match Nat.ble minAligned bytesLen with
      | false => none
      | true =>
        let maxRounded := roundDown (bytesLen - sBase) al
        let maxSliceBytes := maxRounded - sPhase
        let elems := Nat.div maxSliceBytes l.elemSize
        let unused := Nat.mod maxSliceBytes l.elemSize
        let unusedAligned := roundDown unused al
        let selfBytes := sBase + (maxRounded - unusedAligned)
        let splitAt := match ct with
          | .castPrefix => selfBytes
          | .castSuffix => bytesLen - selfBytes
        some (elems, splitAt)

/-- **Theorem 5A (`validate_cast_splitAt_bounds`):**
    Whenever `validateCastAndConvertMetadata` succeeds, `splitAt ≤ bytesLen`. -/
theorem validateCast_splitAt_bounds :
    ∀ (l : TrailingSliceLayout) (addr bytesLen : Nat) (ct : TrailingCastType) (elems splitAt : Nat),
      validateCastAndConvertMetadata l addr bytesLen ct = some (elems, splitAt) →
      splitAt ≤ bytesLen := by
  intro l addr bytesLen ct elems splitAt h
  dsimp only [validateCastAndConvertMetadata] at h
  cases hpos : Nat.ble 1 l.elemSize with
  | false => rw [hpos] at h; cases h
  | true =>
    rw [hpos] at h
    cases ct with
    | castPrefix =>
      dsimp only at h
      cases hal : Nat.beq (Nat.mod (addr + 0) (trailingDstAlign l)) 0 with
      | false => rw [hal] at h; cases h
      | true =>
        rw [hal] at h
        cases hbase : Nat.ble (alignUp (trailingSizePhaseBase l) (trailingDstAlign l)) bytesLen with
        | false => rw [hbase] at h; cases h
        | true =>
          rw [hbase] at h
          injection h with hp
          injection hp with _ hsplit
          have hminLe : alignUp (trailingSizePhaseBase l) (trailingDstAlign l) ≤ bytesLen :=
            Nat.le_of_ble_eq_true hbase
          have hsBaseLe : trailingNormSizeBase l ≤ bytesLen :=
            Nat.le_trans (roundDown_le _ _) (Nat.le_trans (alignUp_ge _ _) hminLe)
          have hmr : roundDown (bytesLen - trailingNormSizeBase l) (trailingDstAlign l) ≤ bytesLen - trailingNormSizeBase l :=
            roundDown_le _ _
          have hdiff : roundDown (bytesLen - trailingNormSizeBase l) (trailingDstAlign l) -
              roundDown (Nat.mod (roundDown (bytesLen - trailingNormSizeBase l) (trailingDstAlign l) - trailingNormSizePhase l) l.elemSize) (trailingDstAlign l) ≤
              bytesLen - trailingNormSizeBase l :=
            Nat.le_trans (Nat.sub_le _ _) hmr
          have hsum : trailingNormSizeBase l + (roundDown (bytesLen - trailingNormSizeBase l) (trailingDstAlign l) -
              roundDown (Nat.mod (roundDown (bytesLen - trailingNormSizeBase l) (trailingDstAlign l) - trailingNormSizePhase l) l.elemSize) (trailingDstAlign l)) ≤
              trailingNormSizeBase l + (bytesLen - trailingNormSizeBase l) :=
            Nat.add_le_add_left hdiff (trailingNormSizeBase l)
          rw [← hsplit]
          exact Nat.le_trans hsum (Nat.le_of_eq (Nat.add_sub_of_le hsBaseLe))
    | castSuffix =>
      dsimp only at h
      cases hal : Nat.beq (Nat.mod (addr + bytesLen) (trailingDstAlign l)) 0 with
      | false => rw [hal] at h; cases h
      | true =>
        rw [hal] at h
        cases hbase : Nat.ble (alignUp (trailingSizePhaseBase l) (trailingDstAlign l)) bytesLen with
        | false => rw [hbase] at h; cases h
        | true =>
          rw [hbase] at h
          injection h with hp
          injection hp with _ hsplit
          rw [← hsplit]
          exact Nat.sub_le bytesLen _

/-- **Theorem 5B (`prefix_suffix_splitAt_complement`):**
    When both prefix and suffix casts succeed on `bytesLen`, `sPref + sSuff = bytesLen`. -/
theorem prefix_suffix_splitAt_complement :
    ∀ (l : TrailingSliceLayout) (addr bytesLen : Nat) (e1 sPref e2 sSuff : Nat),
      validateCastAndConvertMetadata l addr bytesLen .castPrefix = some (e1, sPref) →
      validateCastAndConvertMetadata l addr bytesLen .castSuffix = some (e2, sSuff) →
      sPref + sSuff = bytesLen := by
  intro l addr bytesLen e1 sPref e2 sSuff hp hs
  dsimp only [validateCastAndConvertMetadata] at hp hs
  cases hpos : Nat.ble 1 l.elemSize with
  | false => rw [hpos] at hp; cases hp
  | true =>
    rw [hpos] at hp hs
    cases ha1 : Nat.beq (Nat.mod (addr + 0) (trailingDstAlign l)) 0 with
    | false => rw [ha1] at hp; cases hp
    | true =>
      cases ha2 : Nat.beq (Nat.mod (addr + bytesLen) (trailingDstAlign l)) 0 with
      | false => rw [ha2] at hs; cases hs
      | true =>
        rw [ha1] at hp
        rw [ha2] at hs
        cases hb : Nat.ble (alignUp (trailingSizePhaseBase l) (trailingDstAlign l)) bytesLen with
        | false => rw [hb] at hp; cases hp
        | true =>
          rw [hb] at hp hs
          injection hp with hp'
          injection hp' with _ hsp
          injection hs with hs'
          injection hs' with _ hss
          have hminLe : alignUp (trailingSizePhaseBase l) (trailingDstAlign l) ≤ bytesLen :=
            Nat.le_of_ble_eq_true hb
          have hsBaseLe : trailingNormSizeBase l ≤ bytesLen :=
            Nat.le_trans (roundDown_le _ _) (Nat.le_trans (alignUp_ge _ _) hminLe)
          have hmr : roundDown (bytesLen - trailingNormSizeBase l) (trailingDstAlign l) ≤ bytesLen - trailingNormSizeBase l :=
            roundDown_le _ _
          have hdiff : roundDown (bytesLen - trailingNormSizeBase l) (trailingDstAlign l) -
              roundDown (Nat.mod (roundDown (bytesLen - trailingNormSizeBase l) (trailingDstAlign l) - trailingNormSizePhase l) l.elemSize) (trailingDstAlign l) ≤
              bytesLen - trailingNormSizeBase l :=
            Nat.le_trans (Nat.sub_le _ _) hmr
          have hsum : trailingNormSizeBase l + (roundDown (bytesLen - trailingNormSizeBase l) (trailingDstAlign l) -
              roundDown (Nat.mod (roundDown (bytesLen - trailingNormSizeBase l) (trailingDstAlign l) - trailingNormSizePhase l) l.elemSize) (trailingDstAlign l)) ≤
              trailingNormSizeBase l + (bytesLen - trailingNormSizeBase l) :=
            Nat.add_le_add_left hdiff (trailingNormSizeBase l)
          have hselfLe : trailingNormSizeBase l + (roundDown (bytesLen - trailingNormSizeBase l) (trailingDstAlign l) -
              roundDown (Nat.mod (roundDown (bytesLen - trailingNormSizeBase l) (trailingDstAlign l) - trailingNormSizePhase l) l.elemSize) (trailingDstAlign l)) ≤ bytesLen :=
            Nat.le_trans hsum (Nat.le_of_eq (Nat.add_sub_of_le hsBaseLe))
          rw [← hsp, ← hss]
          exact Nat.add_sub_of_le hselfLe

noncomputable def packetLayout : TrailingSliceLayout := {
  prefixSize := 6, prefixAlign := 4, elemSize := 2, elemAlign := 2, repr := .reprC
}

theorem packet_dst_elems5_vs_elems4_witness :
    fromBytesWithElemsValid packetLayout 64 16 5 = true ∧
    fromBytesWithElemsValid packetLayout 64 16 4 = true ∧
    fromBytesWithElemsValid packetLayout 64 16 6 = false ∧
    validateCastAndConvertMetadata packetLayout 64 16 .castPrefix = some (5, 16) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Theorem 5C (Structural Disjointness of `zerocopy` DST `KnownLayout` vs `DispatchFromDyn`):**
    No struct representation `repr : ReprKind` simultaneously admits `#[derive(KnownLayout)]`
    DST support (`#[repr(C)]`) and `DispatchFromDyn` admissibility (`#[repr(Rust)]`/`#[repr(transparent)]`). -/
theorem repr_c_duality_disjoint :
    ∀ (d : AdtDef),
      ¬ (zerocopyDeriveDstEligible d = true ∧ reprAllowedForDispatch d.repr = true) := by
  intro d h
  have h1 := h.1
  have h2 := h.2
  dsimp only [zerocopyDeriveDstEligible] at h1
  cases hk : d.kind with
  | enumKind => rw [hk] at h1; exact Bool.noConfusion h1
  | unionKind => rw [hk] at h1; exact Bool.noConfusion h1
  | structKind =>
    rw [hk] at h1
    cases hr : d.repr with
    | reprRust => rw [hr] at h1; exact Bool.noConfusion h1
    | reprTransparent => rw [hr] at h1; exact Bool.noConfusion h1
    | reprPacked _ => rw [hr] at h1; exact Bool.noConfusion h1
    | reprC => rw [hr] at h2; exact Bool.noConfusion h2

theorem packet_repr_c_duality_witness :
    zerocopyDeriveDstEligible defPacket = true ∧
    zerocopyDeriveDstEligible defRustPacket = false ∧
    checkDispatchFromDynFuel stdEnv 6 (.adt 11 [.scalar 99 4 4]) (.adt 11 [.traitObj 10]) =
      .err .e0378DispatchReprForbidden ∧
    checkDispatchFromDynFuel stdEnv 6 (.adt 1 [.scalar 99 4 4]) (.adt 1 [.traitObj 10]) =
      .ok (.structField 1 0 (.ptrCoerce (.concreteToDyn (.scalar 99 4 4) 10 77))) :=
  ⟨rfl, rfl, rfl, rfl⟩

end CoerceUnsizedDispatchFromDynStructuralSoundness
