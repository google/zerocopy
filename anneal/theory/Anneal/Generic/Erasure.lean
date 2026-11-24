-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.NotationExtra
public import Init.Data.BitVec.BasicAux
public import Init.Data.Char.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Basic
public import Init.Data.List.Basic
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.Generic.Syntax
public import Anneal.Generic.TypeSpec
public import Anneal.Generic.OpenSemantics

public section

namespace Anneal.Generic

open Trusted.MirAst Trusted.MirSemantics

/-!
# Closed-Instantiation Erasure (`Anneal.Generic.Erasure`)

Monomorphization erasure from open generic MIR bodies (`OpenBody`,
`OpenProgram`) at closed well-formed type substitutions `σ` down to closed
Day-1 MIR (`Body`, `Program`), together with:
1. Pure `TypeSpec` and `OpenSemantics` foundational lemmas in `anneal/theory/`
   (`0` `trusted/` changes);
2. `ClosedOpenInstantiationTransfer`: constructs concrete `paramSpecs`,
   `paramInvs`, and `assocSpecs`, discharges `AllWhereParamsSem` **from**
   `AllWhereDischarged`, and invokes `ParametricBodyVerified` to yield
   `OpenWellFormed`;
3. `ClosedInstantiationTransfer`: proves
   `OpenInstantiationErasureClaim eraseOpenBody eraseOpenProgram` via a genuine
   lockstep simulation between Day-1 `evalStep` and `OpenStep` with zero
   caller-supplied `wellFormedTransfer` escape hatches.

Scope note: closed-instantiation transfer to Day-1 `BodyVerified` currently
covers only entry bodies satisfying `openBodyIsDay1Erasable` (whose basic
blocks use only `.goto`, `.switchInt`, `.return_`, `.unreachable`, or
`.unsupported` terminators). Erasure of `.traitCall`, `.call`, `.assert`, and
`.unwindResume` bodies is future work.
-/

/-! ## Part I: Erased Day-1 AST Translation -/

/-- Erase a closed `OpenMirTy` to `MirTy`, mapping open or extended types to
`.unsupported`. -/
@[expose] noncomputable def eraseOpenTy (ty : OpenMirTy) : MirTy :=
  match OpenMirTy.toClosedMirTy? ty with
  | some mty => mty
  | none => .unsupported

/-- Total Day-1 erasure of `OpenProjectionElem`. -/
@[expose] noncomputable def eraseOpenProjectionElem :
    OpenProjectionElem → ProjectionElem
  | .deref => .deref
  | .field idx ty => .field idx (eraseOpenTy ty)
  | .unsupported => .unsupported

/-- Total Day-1 erasure of `OpenPlace`. -/
@[expose] noncomputable def eraseOpenPlace (p : OpenPlace) : Place :=
  { localId := p.localId
  , projection := p.projection.map eraseOpenProjectionElem }

/-- Total Day-1 erasure of `OpenOperand`. -/
@[expose] noncomputable def eraseOpenOperand : OpenOperand → Operand
  | .copy p => .copy (eraseOpenPlace p)
  | .move p => .move (eraseOpenPlace p)
  | .constant c => .constant { ty := eraseOpenTy c.ty, lit := c.lit }

/-- Total Day-1 erasure of `OpenRvalue`. -/
@[expose] noncomputable def eraseOpenRvalue : OpenRvalue → Rvalue
  | .use op => .use (eraseOpenOperand op)
  | .binaryOp op lhs rhs =>
      .binaryOp op (eraseOpenOperand lhs) (eraseOpenOperand rhs)
  | .unaryOp op opnd => .unaryOp op (eraseOpenOperand opnd)
  | .cast kind opnd ty => .cast kind (eraseOpenOperand opnd) (eraseOpenTy ty)
  | .discriminant p => .discriminant (eraseOpenPlace p)
  | .ref m p => .ref m (eraseOpenPlace p)
  | .addressOf m p => .addressOf m (eraseOpenPlace p)
  | .aggregateTuple fs => .aggregateTuple (fs.map eraseOpenOperand)
  | .unsupported => .unsupported

/-- Total Day-1 erasure of `OpenStatementKind`. -/
@[expose] noncomputable def eraseOpenStatementKind :
    OpenStatementKind → StatementKind
  | .assign dst rv => .assign (eraseOpenPlace dst) (eraseOpenRvalue rv)
  | .storageLive l => .storageLive l
  | .storageDead l => .storageDead l
  | .nop => .nop
  | .unsupported => .unsupported

/-- Total Day-1 erasure of `OpenTerminatorKind`. `.traitCall` and generic
`.call` with non-empty substitutions erase to `.unsupported`. -/
@[expose] noncomputable def eraseOpenTerminatorKind :
    OpenTerminatorKind → TerminatorKind
  | .goto t => .goto t
  | .switchInt d tgts => .switchInt (eraseOpenOperand d) tgts
  | .return_ => .return_
  | .unreachable => .unreachable
  | .unwindResume => .unwindResume
  | .assert cond exp msg tgt uw =>
      .assert (eraseOpenOperand cond) exp msg tgt uw
  | .call callee substs args dst tgt uw =>
      match substs with
      | [] =>
          .call callee (args.map eraseOpenOperand) (eraseOpenPlace dst) tgt uw
      | _ :: _ => .unsupported
  | .traitCall _ _ _ _ _ _ _ _ => .unsupported
  | .unsupported => .unsupported

/-- Total Day-1 erasure of `OpenBasicBlock`. -/
@[expose] noncomputable def eraseOpenBasicBlock (bb : OpenBasicBlock) :
    BasicBlock :=
  { statements := bb.statements.map eraseOpenStatementKind
  , terminator := eraseOpenTerminatorKind bb.terminator
  , cleanup := bb.cleanup }

/-- Substitute `σ` using `reg`, normalize associated projections, and erase
an `OpenBody` to a closed Day-1 `Body`. -/
@[expose] noncomputable def eraseOpenBody (reg : TraitRegistry)
    (σ : List OpenMirTy) (ob : OpenBody) : Body :=
  let inst := OpenBody.subst reg normFuel σ ob
  { argumentCount := inst.argumentCount
  , locals := inst.locals.map eraseOpenTy
  , basicBlocks := inst.basicBlocks.map eraseOpenBasicBlock
  , isUnsafe := inst.isUnsafe
  , identity := inst.identity }

/-- Substitute `σ` across every body in `prog` and erase to a closed Day-1
`Program`. -/
@[expose] noncomputable def eraseOpenProgram (σ : List OpenMirTy)
    (prog : OpenProgram) : Program :=
  { bodies := prog.bodies.map (eraseOpenBody prog.traitRegistry σ)
  , entryDefId := prog.entryDefId
  , pointerWidthBits := prog.pointerWidthBits
  , mirProfileVersion := prog.mirProfileVersion
  , scope := prog.scope }

/-- Evaluate a list of closed `OpenMirTy`s to `TypeLayoutSpec`s. -/
@[expose] noncomputable def evalSubstSpecs (prog : OpenProgram)
    (env : OpenExecEnv) (σ : List OpenMirTy) : Option (List TypeLayoutSpec) :=
  evalNormOpenTySpecList env.typeSpecs
    (σ.map (normalizeOpenTy prog.traitRegistry normFuel))

/-! ## Part II: Pure Layout, Registry, List, and Bool Lemmas -/

theorem length_map_eq {α β : Type} (f : α → β) :
    ∀ xs : List α, (xs.map f).length = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (length_map_eq f xs)

/-- Length of `repeatItem x n` equals `n`. -/
theorem length_repeatItem {α : Type} (x : α) :
    ∀ n : Nat, (repeatItem x n).length = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (length_repeatItem x n)

/-- Length of `xs ++ ys` equals `xs.length + ys.length`. -/
theorem length_append_eq {α : Type} :
    ∀ (xs ys : List α), (xs ++ ys).length = xs.length + ys.length
  | [], _ => Eq.symm (Nat.zero_add _)
  | _ :: xs, ys =>
      Eq.trans (congrArg Nat.succ (length_append_eq xs ys))
        (Eq.symm (Nat.succ_add xs.length ys.length))

/-- Length of `repeatConcat xs m` equals `xs.length * m`. -/
theorem length_repeatConcat {α : Type} (xs : List α) :
    ∀ m : Nat, (repeatConcat xs m).length = xs.length * m
  | 0 => Eq.symm (Nat.mul_zero xs.length)
  | m + 1 =>
      Eq.trans (length_append_eq xs (repeatConcat xs m))
        (Eq.trans
          (Nat.add_comm xs.length (repeatConcat xs m).length)
          (Eq.trans
            (congrArg (fun k => k + xs.length) (length_repeatConcat xs m))
            (Eq.symm (Nat.mul_succ xs.length m))))

/-- Exponent step `Nat.pow a (n + 1) = Nat.pow a n * a`. -/
theorem nat_pow_succ_eq (a n : Nat) : Nat.pow a (n + 1) = Nat.pow a n * a :=
  rfl

/-- Exponent addition law `Nat.pow a (b + c) = Nat.pow a b * Nat.pow a c`. -/
theorem nat_pow_add (a b : Nat) :
    ∀ c : Nat, Nat.pow a (b + c) = Nat.pow a b * Nat.pow a c
  | 0 => Eq.symm (Nat.mul_one (Nat.pow a b))
  | c + 1 => by
      rw [← Nat.add_assoc, nat_pow_succ_eq a (b + c), nat_pow_add a b c,
        nat_pow_succ_eq a c, Nat.mul_assoc]

/-- Witness that `32 ≤ isizeMax`. -/
theorem le_isizeMax_32 : 32 ≤ isizeMax :=
  Nat.le_sub_of_add_le
    (Nat.le_trans (show 32 + 1 ≤ Nat.pow 2 6 from by decide)
      (Nat.pow_le_pow_right (by decide) (by decide)))

/-- Any `n ≤ 32` fits within `isizeMax`. -/
theorem le_isizeMax_of_le_32 {n : Nat} (h : n ≤ 32) : n ≤ isizeMax :=
  Nat.le_trans h le_isizeMax_32

/-- `Bool.and` left conjunct helper. -/
theorem bool_and_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | true => rfl
  | false => cases h

/-- `Bool.and` right conjunct helper. -/
theorem bool_and_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | true => exact h
  | false => cases h

/-- `Bool.and` constructor helper. -/
theorem bool_and_eq_true {a b : Bool} (ha : a = true) (hb : b = true) :
    (a && b) = true := by
  subst ha hb; rfl

/-- `Bool.or` left-false helper. -/
theorem bool_or_eq_false_left {a b : Bool} (h : (a || b) = false) :
    a = false := by
  cases a with
  | false => rfl
  | true => cases h

/-- `Bool.or` right-false helper. -/
theorem bool_or_eq_false_right {a b : Bool} (h : (a || b) = false) :
    b = false := by
  cases a with
  | false => exact h
  | true => cases h

/-- Negated boolean helper: `!b = true → b = false`. -/
theorem not_bool_eq_true {b : Bool} (h : (!b) = true) : b = false := by
  cases b with
  | false => rfl
  | true => cases h

/-- Negated boolean helper: `!b = false → b = true`. -/
theorem not_bool_eq_false {b : Bool} (h : (!b) = false) : b = true := by
  cases b with
  | true => rfl
  | false => cases h

/-- `Nat.beq a b = true` implies `a = b`. -/
theorem nat_beq_eq {a b : Nat} (h : Nat.beq a b = true) : a = b :=
  Nat.eq_of_beq_eq_true h

/-- `Trusted.MirSemantics.getElem?` coincides with `openListGet?`. -/
theorem getElem?_eq_openListGet? {α : Type} :
    ∀ (xs : List α) (i : Nat),
      Trusted.MirSemantics.getElem? xs i = openListGet? xs i
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, i + 1 => getElem?_eq_openListGet? xs i

/-- Lookup in `xs.map f` via `Trusted.MirSemantics.getElem?`. -/
theorem mirGetElem?_map {α β : Type} (f : α → β) :
    ∀ (xs : List α) (i : Nat),
      Trusted.MirSemantics.getElem? (xs.map f) i =
        (Trusted.MirSemantics.getElem? xs i).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, i + 1 => mirGetElem?_map f xs i

/-- Lookup in `xs.map f` via `openListGet?`. -/
theorem openListGet?_map {α β : Type} (f : α → β) (xs : List α) (i : Nat) :
    openListGet? (xs.map f) i = (openListGet? xs i).map f := by
  rw [← getElem?_eq_openListGet?, ← getElem?_eq_openListGet?]
  exact mirGetElem?_map f xs i

/-- Lookup in `List.replicate ys.length x` when `openListGet? ys i = some y`.
-/
theorem openListGet?_replicate {α β : Type} (x : β) :
    ∀ (ys : List α) (i : Nat) (y : α),
      openListGet? ys i = some y →
      openListGet? (List.replicate ys.length x) i = some x
  | [], _, _, h => by cases h
  | _ :: _, 0, _, _ => rfl
  | _ :: ys, i + 1, y, h => openListGet?_replicate x ys i y h

/-- Membership in `xs.map f`. -/
theorem mem_of_mem_map {α β : Type} (f : α → β) :
    ∀ {xs : List α} {y : β}, y ∈ xs.map f → ∃ x, x ∈ xs ∧ f x = y
  | [], _, h => by cases h
  | x :: xs, y, h => by
      cases h with
      | head _ => exact ⟨x, List.Mem.head xs, rfl⟩
      | tail _ hMem =>
          let ⟨x', hx', hEq⟩ := mem_of_mem_map f hMem
          exact ⟨x', List.Mem.tail x hx', hEq⟩

theorem openTyListNoOpenTuple_mem :
    ∀ (xs : List OpenMirTy) (a : OpenMirTy),
      openTyListNoOpenTuple xs = true → a ∈ xs → openTyNoOpenTuple a = true
  | [], _, _, h => by cases h
  | x :: xs, a, hTup, hMem => by
      dsimp only [openTyListNoOpenTuple] at hTup
      cases hMem with
      | head _ => exact bool_and_left hTup
      | tail _ ht => exact openTyListNoOpenTuple_mem xs a (bool_and_right hTup) ht

theorem mem_map_of_mem {α β : Type} (f : α → β) :
    ∀ {xs : List α} {a : α}, a ∈ xs → f a ∈ xs.map f
  | [], _, h => by cases h
  | _ :: _, _, .head _ => List.Mem.head _
  | x :: _, _, .tail _ ht => List.Mem.tail (f x) (mem_map_of_mem f ht)

/-- `xs.all p = true` yields `p x = true` at indexed element `x`. -/
theorem all_getElem?_eq_true {α : Type} {p : α → Bool} :
    ∀ {xs : List α} {i : Nat} {x : α},
      xs.all p = true → Trusted.MirSemantics.getElem? xs i = some x →
      p x = true
  | [], _, _, _, h => by cases h
  | x :: _, 0, y, hAll, hEq => by
      cases hEq
      simp only [List.all_cons] at hAll
      exact bool_and_left hAll
  | _ :: xs, i + 1, y, hAll, hEq => by
      simp only [List.all_cons] at hAll
      exact all_getElem?_eq_true (bool_and_right hAll) hEq

/-- `natListBeq xs xs = true`. -/
theorem natListBeq_self : ∀ xs : List Nat, natListBeq xs xs = true
  | [] => rfl
  | x :: xs => by
      unfold natListBeq
      rw [Nat.beq_refl, natListBeq_self xs]
      rfl

/-- `natListBeq xs ys = true → xs = ys`. -/
theorem natListBeq_eq :
    ∀ {xs ys : List Nat}, natListBeq xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
      unfold natListBeq at h
      have hxy := nat_beq_eq (bool_and_left h)
      have hxs := natListBeq_eq (bool_and_right h)
      subst hxy hxs; rfl

/-- `IntWidth.beq` is reflexive. -/
theorem intWidth_beq_self : ∀ w : IntWidth, IntWidth.beq w w = true
  | .i8 | .i16 | .i32 | .i64 | .i128 | .isize => rfl

/-- `IntWidth.beq` implies equality. -/
theorem intWidth_beq_eq : ∀ {a b : IntWidth}, IntWidth.beq a b = true → a = b
  | .i8, .i8, _ => rfl | .i16, .i16, _ => rfl | .i32, .i32, _ => rfl
  | .i64, .i64, _ => rfl | .i128, .i128, _ => rfl | .isize, .isize, _ => rfl

/-- `Mutability.beq` implies equality. -/
theorem mutability_beq_eq :
    ∀ {a b : Mutability}, Mutability.beq a b = true → a = b
  | .shared, .shared, _ => rfl
  | .mut, .mut, _ => rfl

/-- `EnumTagRepr.beq` is reflexive. -/
theorem enumTagRepr_beq_self :
    ∀ r : EnumTagRepr, EnumTagRepr.beq r r = true
  | .zeroSized => rfl
  | .scalar w s => by
      dsimp only [EnumTagRepr.beq]
      rw [intWidth_beq_self w]
      cases s <;> rfl

/-- `EnumTagRepr.beq` implies equality. -/
theorem enumTagRepr_beq_eq :
    ∀ {a b : EnumTagRepr}, EnumTagRepr.beq a b = true → a = b
  | .zeroSized, .zeroSized, _ => rfl
  | .scalar w₁ s₁, .scalar w₂ s₂, h => by
      dsimp only [EnumTagRepr.beq] at h
      have hw := intWidth_beq_eq (bool_and_left h)
      have hs := eq_of_beq (bool_and_right h)
      subst hw hs; rfl

/-- `EnumTy.beq` is reflexive. -/
theorem enumTy_beq_self (e : EnumTy) : EnumTy.beq e e = true := by
  unfold EnumTy.beq
  rw [Nat.beq_refl e.id, intWidth_beq_self e.discrWidth,
    enumTagRepr_beq_self e.tagRepr, natListBeq_self e.discriminants]
  cases e.discrSigned <;> rfl

/-- `EnumTy.beq` implies equality. -/
theorem enumTy_beq_eq : ∀ {a b : EnumTy}, EnumTy.beq a b = true → a = b
  | ⟨id₁, w₁, s₁, t₁, d₁⟩, ⟨id₂, w₂, s₂, t₂, d₂⟩, h => by
      unfold EnumTy.beq at h
      have hd := natListBeq_eq (bool_and_right h)
      have h1 := bool_and_left h
      have ht := enumTagRepr_beq_eq (bool_and_right h1)
      have h2 := bool_and_left h1
      have hs := eq_of_beq (bool_and_right h2)
      have h3 := bool_and_left h2
      have hi := nat_beq_eq (bool_and_left h3)
      have hw := intWidth_beq_eq (bool_and_right h3)
      subst hi hw hs ht hd; rfl

/-- `ByteRole.beq` is reflexive. -/
theorem byteRole_beq_self : ∀ r : ByteRole, ByteRole.beq r r = true
  | .padding => rfl
  | .valueByte .anyByte | .valueByte .boolByte
  | .valueByte .orderingByte => rfl
  | .valueByte (.charScalar p) => Nat.beq_refl p
  | .valueByte (.intRange lo hi w) => by
      change (Nat.beq lo lo && Nat.beq hi hi && IntWidth.beq w w) = true
      rw [Nat.beq_refl, Nat.beq_refl, intWidth_beq_self w]
      rfl
  | .valueByte (.enumDiscr ety) => enumTy_beq_self ety
  | .valueByte (.refPtr al r) => by
      change (Nat.beq al al && (r == r)) = true
      rw [Nat.beq_refl]
      cases r <;> rfl

/-- `byteRolesBeq rs rs = true` for any `rs`. -/
theorem byteRolesBeq_self : ∀ rs : List ByteRole, byteRolesBeq rs rs = true
  | [] => rfl
  | r :: rs => by
      change (ByteRole.beq r r && byteRolesBeq rs rs) = true
      rw [byteRole_beq_self r, byteRolesBeq_self rs]
      rfl

/-- `allRolesMatchExact r (repeatItem r n) = true`. -/
theorem allRolesMatchExact_repeatItem (r : ByteRole) :
    ∀ n : Nat, allRolesMatchExact r (repeatItem r n) = true
  | 0 => rfl
  | n + 1 => by
      change (ByteRole.beq r r &&
        allRolesMatchExact r (repeatItem r n)) = true
      rw [byteRole_beq_self r, allRolesMatchExact_repeatItem r n]
      rfl

mutual
/-- `OpenMirTy.beq` implies equality (with `OpenMirTy.beqList`). -/
theorem openMirTy_beq_eq :
    ∀ {a b : OpenMirTy}, OpenMirTy.beq a b = true → a = b
  | .bool, .bool, _ => rfl
  | .int w₁ s₁, .int w₂ s₂, h => by
      change (IntWidth.beq w₁ w₂ && (s₁ == s₂)) = true at h
      have hw := intWidth_beq_eq (bool_and_left h)
      have hs := eq_of_beq (bool_and_right h)
      subst hw hs; rfl
  | .unit, .unit, _ => rfl
  | .never, .never, _ => rfl
  | .char, .char, _ => rfl
  | .ordering, .ordering, _ => rfl
  | .enum e₁, .enum e₂, h => congrArg OpenMirTy.enum (enumTy_beq_eq h)
  | .tuple fs₁, .tuple fs₂, h =>
      congrArg OpenMirTy.tuple (openMirTyList_beq_eq h)
  | .slice e₁, .slice e₂, h =>
      congrArg OpenMirTy.slice (openMirTy_beq_eq h)
  | .array e₁ n₁, .array e₂ n₂, h => by
      change (OpenMirTy.beq e₁ e₂ && Nat.beq n₁ n₂) = true at h
      have he := openMirTy_beq_eq (bool_and_left h)
      have hn := nat_beq_eq (bool_and_right h)
      subst he hn; rfl
  | .adt id₁ as₁, .adt id₂ as₂, h => by
      change (Nat.beq id₁ id₂ && OpenMirTy.beqList as₁ as₂) = true at h
      have hi := nat_beq_eq (bool_and_left h)
      have ha := openMirTyList_beq_eq (bool_and_right h)
      subst hi ha; rfl
  | .ref m₁ p₁, .ref m₂ p₂, h => by
      change (Mutability.beq m₁ m₂ && OpenMirTy.beq p₁ p₂) = true at h
      have hm := mutability_beq_eq (bool_and_left h)
      have hp := openMirTy_beq_eq (bool_and_right h)
      subst hm hp; rfl
  | .rawPtr m₁ p₁, .rawPtr m₂ p₂, h => by
      change (Mutability.beq m₁ m₂ && OpenMirTy.beq p₁ p₂) = true at h
      have hm := mutability_beq_eq (bool_and_left h)
      have hp := openMirTy_beq_eq (bool_and_right h)
      subst hm hp; rfl
  | .param id₁, .param id₂, h =>
      congrArg OpenMirTy.param (nat_beq_eq h)
  | .assocProj s₁ tr₁ as₁ i₁, .assocProj s₂ tr₂ as₂ i₂, h => by
      change (OpenMirTy.beq s₁ s₂ && Nat.beq tr₁ tr₂ &&
        OpenMirTy.beqList as₁ as₂ && Nat.beq i₁ i₂) = true at h
      have hi := nat_beq_eq (bool_and_right h)
      have h1 := bool_and_left h
      have ha := openMirTyList_beq_eq (bool_and_right h1)
      have h2 := bool_and_left h1
      have hs := openMirTy_beq_eq (bool_and_left h2)
      have ht := nat_beq_eq (bool_and_right h2)
      subst hs ht ha hi; rfl
  | .unsupported, .unsupported, _ => rfl

theorem openMirTyList_beq_eq :
      ∀ {xs ys : List OpenMirTy}, OpenMirTy.beqList xs ys = true → xs = ys
    | [], [], _ => rfl
    | x :: xs, y :: ys, h => by
        change (OpenMirTy.beq x y && OpenMirTy.beqList xs ys) = true at h
        rw [openMirTy_beq_eq (bool_and_left h),
          openMirTyList_beq_eq (bool_and_right h)]
end

/-- `ImplKey.beq a b = true` implies `a = b`. -/
theorem implKey_beq_eq :
    ∀ {a b : ImplKey}, ImplKey.beq a b = true → a = b
  | ⟨s₁, t₁, a₁⟩, ⟨s₂, t₂, a₂⟩, h => by
      unfold ImplKey.beq at h
      have ha := openMirTyList_beq_eq (bool_and_right h)
      have h1 := bool_and_left h
      have hs := openMirTy_beq_eq (bool_and_left h1)
      have ht := nat_beq_eq (bool_and_right h1)
      subst hs ht ha; rfl

/-- If `implKeyInRegistry key reg = false`, then `lookupImpl reg key = none`. -/
theorem implKeyInRegistry_false_lookupImpl_none (key : ImplKey) :
    ∀ reg : TraitRegistry,
      implKeyInRegistry key reg = false → lookupImpl reg key = none
  | [], _ => rfl
  | (k, b) :: rest, h => by
      have hNeq := bool_or_eq_false_left h
      have hTail := bool_or_eq_false_right h
      change (if ImplKey.beq k key then some b else lookupImpl rest key) = none
      rw [hNeq]
      exact implKeyInRegistry_false_lookupImpl_none key rest hTail

/-- Coherence uniqueness: in any well-formed `TraitRegistry`, the head entry
`k` cannot be shadowed or duplicated anywhere in `rest`. -/
theorem traitRegistryWf_no_tail_shadow (k : ImplKey) (b : ImplBinding)
    (rest : TraitRegistry)
    (hWf : TraitRegistryWf ((k, b) :: rest) = true) :
    lookupImpl rest k = none := by
  have hDistinct := bool_and_left hWf
  have hNotIn := bool_and_left hDistinct
  cases hIn : implKeyInRegistry k rest with
  | false => exact implKeyInRegistry_false_lookupImpl_none k rest hIn
  | true =>
      rw [hIn] at hNotIn
      cases hNotIn

/-- Look up element `idx` in `xs` while proving `WellFormedTypeLayoutSpec` if
`AllParamSpecsWf xs` holds. -/
theorem allParamSpecsWf_get? :
    ∀ (xs : List TypeLayoutSpec) (idx : Nat) (spec : TypeLayoutSpec),
      AllParamSpecsWf xs → openListGet? xs idx = some spec →
        WellFormedTypeLayoutSpec spec
  | [], _, _, _, h => by cases h
  | s :: _, 0, spec, hWf, hEq => by
      cases hEq
      exact hWf.1
  | _ :: xs, n + 1, spec, hWf, hEq =>
      allParamSpecsWf_get? xs n spec hWf.2 hEq

/-- Helper proving `Nat.mod (2^56) (2^al) = 0` for `al ≤ 29`. -/
theorem pow56_mod_pow_eq_zero (al : Nat) (hAl : al ≤ 29) :
    Nat.mod (Nat.pow 2 56) (Nat.pow 2 al) = 0 := by
  have hSub : al ≤ 56 := Nat.le_trans hAl (by decide)
  have hAdd : al + (56 - al) = 56 := Nat.add_sub_of_le hSub
  have hComm : (56 - al) + al = 56 := by
    rw [Nat.add_comm]; exact hAdd
  rw [← hComm, nat_pow_add 2 (56 - al) al]
  exact Nat.mul_mod_left (Nat.pow 2 (56 - al)) (Nat.pow 2 al)

/-- Helper proving `LangValid` succeeds on plain zero bytes for `intRoles w`.
-/
theorem int_zero_bytes_valid :
    ∀ w : IntWidth,
      LangValid (intTypeLayoutSpec w) .none
        (repeatItem (.init (0 : UInt8) none) w.byteSize)
  | .i8 => by unfold LangValid; rfl
  | .i16 => by unfold LangValid; rfl
  | .i32 => by unfold LangValid; rfl
  | .i64 => by unfold LangValid; rfl
  | .isize => by unfold LangValid; rfl
  | .i128 => by unfold LangValid; rfl

/-- `boolTypeLayoutSpec` satisfies `WellFormedTypeLayoutSpec`. -/
theorem wellFormed_boolTypeLayoutSpec :
    WellFormedTypeLayoutSpec boolTypeLayoutSpec := by
  refine ⟨fun _ => ⟨1, [.valueByte .boolByte], rfl, rfl, rfl⟩,
    ?_, ?_, by decide,
    fun _ => ⟨fun _ => ⟨[.init 0 none], by unfold LangValid; rfl⟩,
      fun h => by cases h⟩⟩
  · intro m sz h
    cases m with
    | none => cases h; exact ⟨le_isizeMax_of_le_32 (by decide), _, rfl, rfl⟩
    | sliceLen _ | vtable _ => cases h
  · intro m rs h
    cases m with
    | none => cases h; exact ⟨1, rfl, rfl⟩
    | sliceLen _ | vtable _ => cases h

/-- `unitTypeLayoutSpec` satisfies `WellFormedTypeLayoutSpec`. -/
theorem wellFormed_unitTypeLayoutSpec :
    WellFormedTypeLayoutSpec unitTypeLayoutSpec := by
  refine ⟨fun _ => ⟨0, [], rfl, rfl, rfl⟩, ?_, ?_, by decide,
    fun _ => ⟨fun _ => ⟨[], by unfold LangValid; rfl⟩,
      fun h => by cases h⟩⟩
  · intro m sz h
    cases m with
    | none => cases h; exact ⟨le_isizeMax_of_le_32 (by decide), _, rfl, rfl⟩
    | sliceLen _ | vtable _ => cases h
  · intro m rs h
    cases m with
    | none => cases h; exact ⟨0, rfl, rfl⟩
    | sliceLen _ | vtable _ => cases h

/-- `intTypeLayoutSpec w` satisfies `WellFormedTypeLayoutSpec`. -/
theorem wellFormed_intTypeLayoutSpec (w : IntWidth) :
    WellFormedTypeLayoutSpec (intTypeLayoutSpec w) := by
  have hSz : (intLayout w).size = w.byteSize := by
    cases w <;> rfl
  have hSzLe : (intLayout w).size ≤ 32 := by
    cases w <;> decide
  have hAl : (intLayout w).alignLog2 ≤ maxAlignLog2 := by
    cases w <;> decide
  have hRolesLen : (intRoles w).length = (intLayout w).size := by
    rw [intRoles, length_repeatItem, hSz]
  refine ⟨fun _ => ⟨(intLayout w).size, intRoles w, rfl, rfl, hRolesLen⟩,
    ?_, ?_, hAl, fun _ => ⟨fun _ => ?_, fun h => by cases h⟩⟩
  · intro m sz h
    cases m with
    | none =>
        cases h
        exact ⟨le_isizeMax_of_le_32 hSzLe, intRoles w, rfl, hRolesLen⟩
    | sliceLen _ | vtable _ => cases h
  · intro m rs h
    cases m with
    | none =>
        cases h
        exact ⟨(intLayout w).size, rfl, hRolesLen⟩
    | sliceLen _ | vtable _ => cases h
  · exact ⟨repeatItem (.init 0 none) w.byteSize, int_zero_bytes_valid w⟩

/-- Witness of a valid 8-byte aligned provenance-carrying reference (`2^56`).
-/
@[expose] noncomputable def validRefPtrBytes8 : List AllocByte :=
  [ .init 1 (some 1), .init 0 (some 1), .init 0 (some 1), .init 0 (some 1),
    .init 0 (some 1), .init 0 (some 1), .init 0 (some 1), .init 0 (some 1) ]

/-- `checkRefPtrSpan al validRefPtrBytes8 = true` whenever `al ≤ 29`. -/
theorem checkRefPtrSpan_validRefPtrBytes8 (al : Nat) (hAl : al ≤ 29) :
    checkRefPtrSpan al validRefPtrBytes8 = true := by
  unfold checkRefPtrSpan validRefPtrBytes8
  have hProv :
      initProvBytes?
          [ AllocByte.init 1 (some 1), AllocByte.init 0 (some 1),
            AllocByte.init 0 (some 1), AllocByte.init 0 (some 1),
            AllocByte.init 0 (some 1), AllocByte.init 0 (some 1),
            AllocByte.init 0 (some 1), AllocByte.init 0 (some 1) ] =
        some [1, 0, 0, 0, 0, 0, 0, 0] := rfl
  rw [hProv]
  dsimp only
  have hDec :
      decodeUInt profileTargetEndian [1, 0, 0, 0, 0, 0, 0, 0] =
        Nat.pow 2 56 := rfl
  rw [hDec, pow56_mod_pow_eq_zero al hAl]
  rfl

/-- `allBytesMatchRolesAux` helper for 8-byte `rawPtr` roles followed by
`rTail`. -/
theorem allBytesMatchRolesAux_rawPtr8 (f : Nat) (al : Nat)
    (bTail : List AllocByte) (rTail : List ByteRole)
    (hTail : allBytesMatchRolesAux f bTail rTail = true) :
    allBytesMatchRolesAux (f + 8)
      (repeatItem (.init (0 : UInt8) none) 8 ++ bTail)
      (repeatItem (ByteRole.valueByte (.refPtr al false)) 8 ++ rTail) =
      true := by
  simp [repeatItem, allBytesMatchRolesAux, ByteMatchesRoleBool, hTail]

/-- `allBytesMatchRolesAux` helper for 8-byte `refPtr al true` span followed by
`rTail`. -/
theorem allBytesMatchRolesAux_refPtr8 (f : Nat) (al : Nat) (hAl : al ≤ 29)
    (bTail : List AllocByte) (rTail : List ByteRole)
    (hTail : allBytesMatchRolesAux f bTail rTail = true) :
    allBytesMatchRolesAux (f + 1)
      (validRefPtrBytes8 ++ bTail)
      (repeatItem (ByteRole.valueByte (.refPtr al true)) 8 ++ rTail) =
      true := by
  have hSpan : checkRefPtrSpan al validRefPtrBytes8 = true :=
    checkRefPtrSpan_validRefPtrBytes8 al hAl
  have hRoles :
      allRolesMatchExact (ByteRole.valueByte (.refPtr al true))
        (repeatItem (ByteRole.valueByte (.refPtr al true)) 8) = true :=
    allRolesMatchExact_repeatItem (ByteRole.valueByte (.refPtr al true)) 8
  have hHead :
      ByteMatchesRoleBool (AllocByte.init 1 (some 1))
        (ByteRole.valueByte (.refPtr al true)) = true := rfl
  let r := ByteRole.valueByte (.refPtr al true)
  have hSplitB :
      takeSplit? 8
          (AllocByte.init 1 (some 1) :: AllocByte.init 0 (some 1) ::
            AllocByte.init 0 (some 1) :: AllocByte.init 0 (some 1) ::
            AllocByte.init 0 (some 1) :: AllocByte.init 0 (some 1) ::
            AllocByte.init 0 (some 1) :: AllocByte.init 0 (some 1) :: bTail) =
        some (validRefPtrBytes8, bTail) := rfl
  have hSplitR :
      takeSplit? 8 (r :: r :: r :: r :: r :: r :: r :: r :: rTail) =
        some (repeatItem r 8, rTail) := rfl
  unfold validRefPtrBytes8 repeatItem
  simp only [List.cons_append, List.nil_append]
  unfold allBytesMatchRolesAux
  change (if !ByteMatchesRoleBool (AllocByte.init 1 (some 1)) r then false
    else
      match takeSplit? 8
              (AllocByte.init 1 (some 1) :: AllocByte.init 0 (some 1) ::
                AllocByte.init 0 (some 1) :: AllocByte.init 0 (some 1) ::
                AllocByte.init 0 (some 1) :: AllocByte.init 0 (some 1) ::
                AllocByte.init 0 (some 1) :: AllocByte.init 0 (some 1) :: bTail),
            takeSplit? 8 (r :: r :: r :: r :: r :: r :: r :: r :: rTail) with
      | some (bSpan, bRest), some (rSpan, rRest) =>
          allRolesMatchExact r rSpan && checkRefPtrSpan al bSpan &&
            allBytesMatchRolesAux f bRest rRest
      | _, _ => false) = true
  rw [hHead]
  rw [hSplitB, hSplitR]
  dsimp only
  rw [hRoles, hSpan, hTail]
  rfl

/-- `allBytesMatchRolesAux` helper for 8-byte `isize` metadata slice zeros. -/
theorem allBytesMatchRolesAux_meta8 :
    allBytesMatchRolesAux 9
      (repeatItem (.init (0 : UInt8) none) 8)
      (repeatItem (ByteRole.valueByte (.intRange 0 isizeMax .isize)) 8) =
      true := by
  rfl

/-- Helper: unsized `pointerTypeLayoutSpec` is well-formed. -/
theorem wellFormed_pointerTypeLayoutSpec_unsized (al : Nat) (isRef : Bool)
    (hAl : al ≤ maxAlignLog2) :
    WellFormedTypeLayoutSpec
      { isSized := true, alignLog2 := 3
      , sizeForMeta := fun m => match m with | .none => some 16 | _ => none
      , inhabited := true, hasUnsafeCell := false
      , rolesForMeta := fun m => match m with
        | .none =>
            some (repeatItem (ByteRole.valueByte (.refPtr al isRef)) 8 ++
              repeatItem (ByteRole.valueByte (.intRange 0 isizeMax .isize)) 8)
        | _ => none } := by
  let rs :=
    repeatItem (ByteRole.valueByte (.refPtr al isRef)) 8 ++
      repeatItem (ByteRole.valueByte (.intRange 0 isizeMax .isize)) 8
  have hRolesLen : rs.length = 16 := by
    rw [length_append_eq, length_repeatItem, length_repeatItem]
  refine ⟨fun _ => ⟨16, rs, rfl, rfl, hRolesLen⟩, ?_, ?_,
    (show (3 : Nat) ≤ maxAlignLog2 from by decide), ?_⟩
  · intro m sz h
    cases m with
    | none =>
        cases h; exact ⟨le_isizeMax_of_le_32 (by decide), rs, rfl, hRolesLen⟩
    | sliceLen _ | vtable _ => cases h
  · intro m rs' h
    cases m with
    | none => cases h; exact ⟨16, rfl, hRolesLen⟩
    | sliceLen _ | vtable _ => cases h
  · intro _
    refine ⟨fun _ => ?_, fun h => by cases h⟩
    cases isRef
    · refine ⟨repeatItem (AllocByte.init 0 none) 8 ++
          repeatItem (AllocByte.init 0 none) 8, ?_⟩
      dsimp only [LangValid, LangValidBool, allBytesMatchRolesBool]
      have hLen : (repeatItem (AllocByte.init 0 none) 8 ++
          repeatItem (AllocByte.init 0 none) 8).length = 16 := rfl
      have hP := allBytesMatchRolesAux_rawPtr8 9 al
        (repeatItem (AllocByte.init 0 none) 8)
        (repeatItem (ByteRole.valueByte (.intRange 0 isizeMax .isize)) 8)
        allBytesMatchRolesAux_meta8
      rw [hLen, hRolesLen]
      exact hP
    · refine ⟨validRefPtrBytes8 ++ repeatItem (AllocByte.init 0 none) 8, ?_⟩
      dsimp only [LangValid, LangValidBool, allBytesMatchRolesBool]
      have hLen : (validRefPtrBytes8 ++
          repeatItem (AllocByte.init 0 none) 8).length = 16 := rfl
      have hTail : allBytesMatchRolesAux 16
          (repeatItem (AllocByte.init 0 none) 8)
          (repeatItem (ByteRole.valueByte (.intRange 0 isizeMax .isize)) 8) =
          true := rfl
      have hP := allBytesMatchRolesAux_refPtr8 16 al hAl
        (repeatItem (AllocByte.init 0 none) 8)
        (repeatItem (ByteRole.valueByte (.intRange 0 isizeMax .isize)) 8)
        hTail
      rw [hLen, hRolesLen]
      exact hP

/-- Helper: sized `pointerTypeLayoutSpec` is well-formed. -/
theorem wellFormed_pointerTypeLayoutSpec_sized (al : Nat) (isRef : Bool)
    (hAl : al ≤ maxAlignLog2) :
    WellFormedTypeLayoutSpec
      { isSized := true, alignLog2 := 3
      , sizeForMeta := fun m => match m with | .none => some 8 | _ => none
      , inhabited := true, hasUnsafeCell := false
      , rolesForMeta := fun m => match m with
        | .none => some (repeatItem (ByteRole.valueByte (.refPtr al isRef)) 8)
        | _ => none } := by
  let rs := repeatItem (ByteRole.valueByte (.refPtr al isRef)) 8
  have hRolesLen : rs.length = 8 := length_repeatItem _ 8
  refine ⟨fun _ => ⟨8, rs, rfl, rfl, hRolesLen⟩, ?_, ?_,
    (show (3 : Nat) ≤ maxAlignLog2 from by decide), ?_⟩
  · intro m sz h
    cases m with
    | none =>
        cases h; exact ⟨le_isizeMax_of_le_32 (by decide), rs, rfl, hRolesLen⟩
    | sliceLen _ | vtable _ => cases h
  · intro m rs' h
    cases m with
    | none => cases h; exact ⟨8, rfl, hRolesLen⟩
    | sliceLen _ | vtable _ => cases h
  · intro _
    refine ⟨fun _ => ?_, fun h => by cases h⟩
    cases isRef
    · refine ⟨repeatItem (AllocByte.init 0 none) 8, ?_⟩
      dsimp only [LangValid, LangValidBool, allBytesMatchRolesBool]
      have hLen : (repeatItem (AllocByte.init 0 none) 8).length = 8 := rfl
      have hBase : allBytesMatchRolesAux 1 [] [] = true := rfl
      have h8 := allBytesMatchRolesAux_rawPtr8 1 al [] [] hBase
      simp only [List.append_nil] at h8
      rw [hLen, hRolesLen]
      exact h8
    · refine ⟨validRefPtrBytes8, ?_⟩
      dsimp only [LangValid, LangValidBool, allBytesMatchRolesBool]
      have hLen : validRefPtrBytes8.length = 8 := rfl
      have hBase : allBytesMatchRolesAux 8 [] [] = true := rfl
      have h8 := allBytesMatchRolesAux_refPtr8 8 al hAl [] [] hBase
      simp only [List.append_nil] at h8
      rw [hLen, hRolesLen]
      exact h8

/-- `pointerTypeLayoutSpec pointeeSpec isRef` satisfies
`WellFormedTypeLayoutSpec` whenever `pointeeSpec.alignLog2 ≤ maxAlignLog2`. -/
theorem wellFormed_pointerTypeLayoutSpec (pointeeSpec : TypeLayoutSpec)
    (isRef : Bool) (hAl : pointeeSpec.alignLog2 ≤ maxAlignLog2) :
    WellFormedTypeLayoutSpec (pointerTypeLayoutSpec pointeeSpec isRef) := by
  unfold pointerTypeLayoutSpec
  cases pointeeSpec.isSized with
  | false =>
      exact wellFormed_pointerTypeLayoutSpec_unsized pointeeSpec.alignLog2 isRef
        hAl
  | true =>
      exact wellFormed_pointerTypeLayoutSpec_sized pointeeSpec.alignLog2 isRef hAl

/-! ## Part III: Normalization Idempotence and Instantiation Transfer -/

mutual
/-- Any `isClosed` `OpenMirTy` satisfies `openMirTyNoParam = true`. -/
theorem openMirTy_isClosed_noParam :
    ∀ ty : OpenMirTy, OpenMirTy.isClosed ty = true →
      openMirTyNoParam ty = true
  | .bool, _ | .int _ _, _ | .unit, _ | .never, _ | .char, _ | .ordering, _
  | .enum _, _ => rfl
  | .param _, h | .assocProj _ _ _ _, h | .unsupported, h => by cases h
  | .slice e, h | .array e _, h | .ref _ e, h | .rawPtr _ e, h =>
      openMirTy_isClosed_noParam e h
  | .tuple fs, h | .adt _ fs, h => openMirTyList_isClosed_noParam fs h

theorem openMirTyList_isClosed_noParam :
      ∀ fs : List OpenMirTy, OpenMirTy.isClosedList fs = true →
        openMirTyListNoParam fs = true
    | [], _ => rfl
    | x :: xs, h => by
        dsimp only [OpenMirTy.isClosedList] at h
        dsimp only [openMirTyListNoParam]
        exact bool_and_eq_true (openMirTy_isClosed_noParam x (bool_and_left h))
          (openMirTyList_isClosed_noParam xs (bool_and_right h))
end

mutual
/-- Any `OpenMirTy` with `isClosed = true` is invariant under
`normalizeOpenTyStep`. -/
theorem normalizeOpenTyStep_isClosed (reg : TraitRegistry) :
    ∀ ty : OpenMirTy, OpenMirTy.isClosed ty = true →
      normalizeOpenTyStep reg ty = ty
  | .bool, _ | .int _ _, _ | .unit, _ | .never, _ | .char, _ | .ordering, _
  | .enum _, _ => rfl
  | .param _, h | .assocProj _ _ _ _, h | .unsupported, h => by cases h
  | .slice e, h => congrArg OpenMirTy.slice (normalizeOpenTyStep_isClosed reg e h)
  | .array e n, h =>
      congrArg (fun x => OpenMirTy.array x n)
        (normalizeOpenTyStep_isClosed reg e h)
  | .ref m p, h =>
      congrArg (OpenMirTy.ref m) (normalizeOpenTyStep_isClosed reg p h)
  | .rawPtr m p, h =>
      congrArg (OpenMirTy.rawPtr m) (normalizeOpenTyStep_isClosed reg p h)
  | .tuple fs, h =>
      congrArg OpenMirTy.tuple (normalizeOpenTyStepList_isClosed reg fs h)
  | .adt id args, h =>
      congrArg (OpenMirTy.adt id) (normalizeOpenTyStepList_isClosed reg args h)

theorem normalizeOpenTyStepList_isClosed (reg : TraitRegistry) :
      ∀ fs : List OpenMirTy, OpenMirTy.isClosedList fs = true →
        normalizeOpenTyStepList reg fs = fs
    | [], _ => rfl
    | x :: xs, h => by
        dsimp only [OpenMirTy.isClosedList] at h
        change normalizeOpenTyStep reg x ::
            normalizeOpenTyStepList reg xs = x :: xs
        rw [normalizeOpenTyStep_isClosed reg x (bool_and_left h),
          normalizeOpenTyStepList_isClosed reg xs (bool_and_right h)]
end

/-- Any `OpenMirTy` with `isClosed = true` is invariant under
`normalizeOpenTy`. -/
theorem normalizeOpenTy_isClosed (reg : TraitRegistry) :
    ∀ k : Nat, ∀ ty : OpenMirTy, OpenMirTy.isClosed ty = true →
      normalizeOpenTy reg k ty = ty
  | 0, _, _ => rfl
  | k + 1, ty, h => by
      unfold normalizeOpenTy
      rw [normalizeOpenTyStep_isClosed reg ty h]
      exact normalizeOpenTy_isClosed reg k ty h

mutual
/-- Any `OpenMirTy` with `isClosed = true` is invariant under
`OpenMirTy.subst σ`. -/
theorem openMirTy_subst_isClosed (σ : List OpenMirTy) :
    ∀ ty : OpenMirTy, OpenMirTy.isClosed ty = true →
      OpenMirTy.subst σ ty = ty
  | .bool, _ | .int _ _, _ | .unit, _ | .never, _ | .char, _ | .ordering, _
  | .enum _, _ => rfl
  | .param _, h | .assocProj _ _ _ _, h | .unsupported, h => by cases h
  | .slice e, h => congrArg OpenMirTy.slice (openMirTy_subst_isClosed σ e h)
  | .array e n, h =>
      congrArg (fun x => OpenMirTy.array x n) (openMirTy_subst_isClosed σ e h)
  | .ref m p, h =>
      congrArg (OpenMirTy.ref m) (openMirTy_subst_isClosed σ p h)
  | .rawPtr m p, h =>
      congrArg (OpenMirTy.rawPtr m) (openMirTy_subst_isClosed σ p h)
  | .tuple fs, h =>
      congrArg OpenMirTy.tuple (openMirTy_substList_isClosed σ fs h)
  | .adt id args, h =>
      congrArg (OpenMirTy.adt id) (openMirTy_substList_isClosed σ args h)

theorem openMirTy_substList_isClosed (σ : List OpenMirTy) :
      ∀ fs : List OpenMirTy, OpenMirTy.isClosedList fs = true →
        OpenMirTy.substList σ fs = fs
    | [], _ => rfl
    | x :: xs, h => by
        dsimp only [OpenMirTy.isClosedList] at h
        change OpenMirTy.subst σ x :: OpenMirTy.substList σ xs = x :: xs
        rw [openMirTy_subst_isClosed σ x (bool_and_left h),
          openMirTy_substList_isClosed σ xs (bool_and_right h)]
end

mutual
/-- Any `OpenMirTy` with `openMirTyNoParam = true` is invariant under
`OpenMirTy.subst σ`. -/
theorem openMirTy_subst_noParam (σ : List OpenMirTy) :
    ∀ ty : OpenMirTy, openMirTyNoParam ty = true →
      OpenMirTy.subst σ ty = ty
  | .bool, _ | .int _ _, _ | .unit, _ | .never, _ | .char, _ | .ordering, _
  | .enum _, _ | .unsupported, _ => rfl
  | .param _, h => by cases h
  | .slice e, h => congrArg OpenMirTy.slice (openMirTy_subst_noParam σ e h)
  | .array e n, h =>
      congrArg (fun x => OpenMirTy.array x n) (openMirTy_subst_noParam σ e h)
  | .ref m p, h =>
      congrArg (OpenMirTy.ref m) (openMirTy_subst_noParam σ p h)
  | .rawPtr m p, h =>
      congrArg (OpenMirTy.rawPtr m) (openMirTy_subst_noParam σ p h)
  | .tuple fs, h =>
      congrArg OpenMirTy.tuple (openMirTyList_subst_noParam σ fs h)
  | .adt id args, h =>
      congrArg (OpenMirTy.adt id) (openMirTyList_subst_noParam σ args h)
  | .assocProj s tr args idx, h => by
      have hs := bool_and_left h
      have hargs := bool_and_right h
      change OpenMirTy.assocProj (OpenMirTy.subst σ s) tr
          (OpenMirTy.substList σ args) idx = .assocProj s tr args idx
      rw [openMirTy_subst_noParam σ s hs, openMirTyList_subst_noParam σ args hargs]

theorem openMirTyList_subst_noParam (σ : List OpenMirTy) :
      ∀ fs : List OpenMirTy, openMirTyListNoParam fs = true →
        OpenMirTy.substList σ fs = fs
    | [], _ => rfl
    | x :: xs, h => by
        dsimp only [openMirTyListNoParam] at h
        change OpenMirTy.subst σ x :: OpenMirTy.substList σ xs = x :: xs
        rw [openMirTy_subst_noParam σ x (bool_and_left h),
          openMirTyList_subst_noParam σ xs (bool_and_right h)]
end

/-- Any `assocTypesWf` list guarantees `isClosed = true` for every resolved
associated-type RHS. -/
theorem assocTypesWf_lookup_isClosed :
    ∀ (xs : List AssocTypeBinding) (idx : AssocItemIdx) (rhs : OpenMirTy),
      assocTypesWf xs = true → lookupAssocType xs idx = some rhs →
      OpenMirTy.isClosed rhs = true
  | [], _, _, _, h => by cases h
  | b :: rest, idx, rhs, hWf, hLook => by
      simp only [assocTypesWf] at hWf
      have hRhs := bool_and_right (bool_and_left hWf)
      have hRest := bool_and_right hWf
      simp only [lookupAssocType] at hLook
      cases hEq : Nat.beq b.assocIdx idx with
      | true =>
          rw [hEq] at hLook
          cases hLook
          exact hRhs
      | false =>
          rw [hEq] at hLook
          exact assocTypesWf_lookup_isClosed rest idx rhs hRest hLook

/-- Well-formed registry entries guarantee `assocTypesWf` and closed keys on
any matching `lookupImpl`. -/
theorem implRegistryEntriesWf_lookupImpl :
    ∀ (reg : TraitRegistry) (key : ImplKey) (binding : ImplBinding),
      ImplRegistryEntriesWf reg = true → lookupImpl reg key = some binding →
      OpenMirTy.isClosed key.selfTy = true ∧
      OpenMirTy.isClosedList key.args = true ∧
      assocTypesWf binding.assocTypes = true
  | [], _, _, _, h => by cases h
  | (k, b) :: rest, key, binding, hWf, hLook => by
      simp only [ImplRegistryEntriesWf] at hWf
      have hRest := bool_and_right hWf
      have h5 := bool_and_left hWf
      have hAssoc := bool_and_right (bool_and_left h5)
      have h4 := bool_and_left (bool_and_left h5)
      have h3 := bool_and_left h4
      have h2 := bool_and_left h3
      have hSelf := bool_and_left h2
      have hArgs := bool_and_right h2
      simp only [lookupImpl] at hLook
      cases hEq : ImplKey.beq k key with
      | true =>
          rw [hEq] at hLook
          have hKey := implKey_beq_eq hEq
          cases hLook
          rw [← hKey]
          exact ⟨hSelf, hArgs, hAssoc⟩
      | false =>
          rw [hEq] at hLook
          exact implRegistryEntriesWf_lookupImpl rest key binding hRest hLook

/-- Well-formed registry entries guarantee `WhereClause.isClosedList` on any
matching `lookupImpl`. -/
theorem implRegistryEntriesWf_whereClosed :
    ∀ (reg : TraitRegistry) (key : ImplKey) (binding : ImplBinding),
      ImplRegistryEntriesWf reg = true → lookupImpl reg key = some binding →
      WhereClause.isClosedList binding.whereClauses = true
  | [], _, _, _, h => by cases h
  | (k, b) :: rest, key, binding, hWf, hLook => by
      simp only [ImplRegistryEntriesWf] at hWf
      have hRest := bool_and_right hWf
      have h5 := bool_and_left hWf
      have h4 := bool_and_left (bool_and_left h5)
      have hWcs := bool_and_right h4
      simp only [lookupImpl] at hLook
      cases hEq : ImplKey.beq k key with
      | true =>
          rw [hEq] at hLook
          cases hLook
          exact hWcs
      | false =>
          rw [hEq] at hLook
          exact implRegistryEntriesWf_whereClosed rest key binding hRest hLook

/-- Any successful `resolveAssocType` in a `TraitRegistryWf` registry implies
closed keys `(s, args)` and closed RHS `rhs`. -/
theorem resolveAssocType_wf_info (reg : TraitRegistry)
    (hWf : TraitRegistryWf reg = true) (s : OpenMirTy) (tr : TraitDefId)
    (args : List OpenMirTy) (idx : AssocItemIdx) (rhs : OpenMirTy)
    (hRes : resolveAssocType reg s tr args idx = some rhs) :
    OpenMirTy.isClosed s = true ∧
    OpenMirTy.isClosedList args = true ∧
    OpenMirTy.isClosed rhs = true := by
  have hEntries := bool_and_right hWf
  unfold resolveAssocType at hRes
  cases hImpl : lookupImpl reg ⟨s, tr, args⟩ with
  | none => rw [hImpl] at hRes; cases hRes
  | some b =>
      rw [hImpl] at hRes
      have hInfo := implRegistryEntriesWf_lookupImpl reg ⟨s, tr, args⟩ b
        hEntries hImpl
      exact ⟨hInfo.1, hInfo.2.1,
        assocTypesWf_lookup_isClosed b.assocTypes idx rhs hInfo.2.2 hRes⟩

mutual
/-- `normalizeOpenTyStep` preserves `openMirTyNoParam` when
`TraitRegistryWf reg = true`. -/
theorem normalizeOpenTyStep_noParam (reg : TraitRegistry)
    (hWf : TraitRegistryWf reg = true) :
    ∀ ty : OpenMirTy, openMirTyNoParam ty = true →
      openMirTyNoParam (normalizeOpenTyStep reg ty) = true
  | .bool, _ | .int _ _, _ | .unit, _ | .never, _ | .char, _ | .ordering, _
  | .enum _, _ | .unsupported, _ => rfl
  | .param _, h => by cases h
  | .slice e, h | .array e _, h | .ref _ e, h | .rawPtr _ e, h =>
      normalizeOpenTyStep_noParam reg hWf e h
  | .tuple fs, h | .adt _ fs, h =>
      normalizeOpenTyStepList_noParam reg hWf fs h
  | .assocProj s tr args idx, h => by
      dsimp only [openMirTyNoParam] at h
      dsimp only [normalizeOpenTyStep]
      cases hRes : resolveAssocType reg (normalizeOpenTyStep reg s) tr
          (normalizeOpenTyStepList reg args) idx with
      | some rhs =>
          have hInfo := resolveAssocType_wf_info reg hWf
            (normalizeOpenTyStep reg s) tr
            (normalizeOpenTyStepList reg args) idx rhs hRes
          exact openMirTy_isClosed_noParam rhs hInfo.2.2
      | none =>
          dsimp only [openMirTyNoParam]
          exact bool_and_eq_true
            (normalizeOpenTyStep_noParam reg hWf s (bool_and_left h))
            (normalizeOpenTyStepList_noParam reg hWf args (bool_and_right h))

theorem normalizeOpenTyStepList_noParam (reg : TraitRegistry)
      (hWf : TraitRegistryWf reg = true) :
      ∀ fs : List OpenMirTy, openMirTyListNoParam fs = true →
        openMirTyListNoParam (normalizeOpenTyStepList reg fs) = true
    | [], _ => rfl
    | x :: xs, h => by
        dsimp only [openMirTyListNoParam] at h
        dsimp only [normalizeOpenTyStepList, openMirTyListNoParam]
        exact bool_and_eq_true
          (normalizeOpenTyStep_noParam reg hWf x (bool_and_left h))
          (normalizeOpenTyStepList_noParam reg hWf xs (bool_and_right h))
end

mutual
/-- Single-step bottom-up normalization is idempotent on any `OpenMirTy` when
`TraitRegistryWf reg = true`. -/
theorem normalizeOpenTyStep_idempotent (reg : TraitRegistry)
    (hWf : TraitRegistryWf reg = true) :
    ∀ ty : OpenMirTy,
      normalizeOpenTyStep reg (normalizeOpenTyStep reg ty) =
        normalizeOpenTyStep reg ty
  | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
  | .param _ | .unsupported => rfl
  | .slice e => congrArg OpenMirTy.slice (normalizeOpenTyStep_idempotent reg hWf e)
  | .array e n =>
      congrArg (fun x => OpenMirTy.array x n)
        (normalizeOpenTyStep_idempotent reg hWf e)
  | .ref m p =>
      congrArg (OpenMirTy.ref m) (normalizeOpenTyStep_idempotent reg hWf p)
  | .rawPtr m p =>
      congrArg (OpenMirTy.rawPtr m) (normalizeOpenTyStep_idempotent reg hWf p)
  | .tuple fs =>
      congrArg OpenMirTy.tuple (normalizeOpenTyStepList_idempotent reg hWf fs)
  | .adt id args =>
      congrArg (OpenMirTy.adt id)
        (normalizeOpenTyStepList_idempotent reg hWf args)
  | .assocProj s tr args idx => by
      dsimp only [normalizeOpenTyStep]
      cases hRes : resolveAssocType reg (normalizeOpenTyStep reg s) tr
          (normalizeOpenTyStepList reg args) idx with
      | some rhs =>
          have hInfo := resolveAssocType_wf_info reg hWf
            (normalizeOpenTyStep reg s) tr
            (normalizeOpenTyStepList reg args) idx rhs hRes
          exact normalizeOpenTyStep_isClosed reg rhs hInfo.2.2
      | none =>
          dsimp only [normalizeOpenTyStep]
          rw [normalizeOpenTyStep_idempotent reg hWf s,
            normalizeOpenTyStepList_idempotent reg hWf args, hRes]

theorem normalizeOpenTyStepList_idempotent (reg : TraitRegistry)
      (hWf : TraitRegistryWf reg = true) :
      ∀ fs : List OpenMirTy,
        normalizeOpenTyStepList reg (normalizeOpenTyStepList reg fs) =
          normalizeOpenTyStepList reg fs
    | [] => rfl
    | x :: xs => by
        change normalizeOpenTyStep reg (normalizeOpenTyStep reg x) ::
            normalizeOpenTyStepList reg (normalizeOpenTyStepList reg xs) =
          normalizeOpenTyStep reg x :: normalizeOpenTyStepList reg xs
        rw [normalizeOpenTyStep_idempotent reg hWf x,
          normalizeOpenTyStepList_idempotent reg hWf xs]
end

/-- Any non-zero normalization fuel agrees with one `normalizeOpenTyStep` pass
when `TraitRegistryWf reg = true`. -/
theorem normalizeOpenTy_succ_eq_step (reg : TraitRegistry)
    (hWf : TraitRegistryWf reg = true) :
    ∀ (k : Nat) (ty : OpenMirTy),
      normalizeOpenTy reg (k + 1) ty = normalizeOpenTyStep reg ty
  | 0, _ => rfl
  | k + 1, ty => by
      unfold normalizeOpenTy
      rw [normalizeOpenTy_succ_eq_step reg hWf k (normalizeOpenTyStep reg ty),
        normalizeOpenTyStep_idempotent reg hWf ty]

/-- `normalizeOpenTy reg normFuel ty` reduces cleanly to
`normalizeOpenTyStep reg ty`. -/
theorem normalizeOpenTy_normFuel_eq_step (reg : TraitRegistry)
    (hWf : TraitRegistryWf reg = true) (ty : OpenMirTy) :
    normalizeOpenTy reg normFuel ty = normalizeOpenTyStep reg ty := by
  have hF : normFuel = 15 + 1 := rfl
  rw [hF]
  exact normalizeOpenTy_succ_eq_step reg hWf 15 ty

mutual
/-- Whenever the normalized result `normalizeOpenTyStep reg ty` is closed, `ty`
contains zero `.param`s (`openMirTyNoParam`) and `normalizeOpenTyStep` on
`OpenMirTy.subst σ ty` produces that same closed type. -/
theorem normalizeOpenTyStep_closed_subst (reg : TraitRegistry)
    (hWf : TraitRegistryWf reg = true) (σ : List OpenMirTy) :
    ∀ ty : OpenMirTy,
      OpenMirTy.isClosed (normalizeOpenTyStep reg ty) = true →
      openMirTyNoParam ty = true ∧
      normalizeOpenTyStep reg (OpenMirTy.subst σ ty) =
        normalizeOpenTyStep reg ty
  | .bool, _ | .int _ _, _ | .unit, _ | .never, _ | .char, _ | .ordering, _
  | .enum _, _ => ⟨rfl, rfl⟩
  | .param _, h | .unsupported, h => by cases h
  | .slice e, h => by
      have ih := normalizeOpenTyStep_closed_subst reg hWf σ e h
      exact ⟨ih.1, congrArg OpenMirTy.slice ih.2⟩
  | .array e n, h => by
      have ih := normalizeOpenTyStep_closed_subst reg hWf σ e h
      exact ⟨ih.1, congrArg (fun x => OpenMirTy.array x n) ih.2⟩
  | .ref m p, h => by
      have ih := normalizeOpenTyStep_closed_subst reg hWf σ p h
      exact ⟨ih.1, congrArg (OpenMirTy.ref m) ih.2⟩
  | .rawPtr m p, h => by
      have ih := normalizeOpenTyStep_closed_subst reg hWf σ p h
      exact ⟨ih.1, congrArg (OpenMirTy.rawPtr m) ih.2⟩
  | .tuple fs, h => by
      have ih := normalizeOpenTyStepList_closed_subst reg hWf σ fs h
      exact ⟨ih.1, congrArg OpenMirTy.tuple ih.2⟩
  | .adt id args, h => by
      have ih := normalizeOpenTyStepList_closed_subst reg hWf σ args h
      exact ⟨ih.1, congrArg (OpenMirTy.adt id) ih.2⟩
  | .assocProj s tr args idx, h => by
      dsimp only [normalizeOpenTyStep] at h
      dsimp only [normalizeOpenTyStep]
      cases hRes : resolveAssocType reg (normalizeOpenTyStep reg s) tr
          (normalizeOpenTyStepList reg args) idx with
      | none =>
          rw [hRes] at h
          cases h
      | some rhs =>
          have hInfo := resolveAssocType_wf_info reg hWf
            (normalizeOpenTyStep reg s) tr
            (normalizeOpenTyStepList reg args) idx rhs hRes
          have ihS := normalizeOpenTyStep_closed_subst reg hWf σ s hInfo.1
          have ihA := normalizeOpenTyStepList_closed_subst reg hWf σ args
            hInfo.2.1
          refine ⟨bool_and_eq_true ihS.1 ihA.1, ?_⟩
          dsimp only [OpenMirTy.subst, normalizeOpenTyStep]
          rw [ihS.2, ihA.2, hRes]

theorem normalizeOpenTyStepList_closed_subst (reg : TraitRegistry)
      (hWf : TraitRegistryWf reg = true) (σ : List OpenMirTy) :
      ∀ fs : List OpenMirTy,
        OpenMirTy.isClosedList (normalizeOpenTyStepList reg fs) = true →
        openMirTyListNoParam fs = true ∧
        normalizeOpenTyStepList reg (OpenMirTy.substList σ fs) =
          normalizeOpenTyStepList reg fs
    | [], _ => ⟨rfl, rfl⟩
    | x :: xs, h => by
        dsimp only [normalizeOpenTyStepList, OpenMirTy.isClosedList] at h
        have ihX := normalizeOpenTyStep_closed_subst reg hWf σ x
          (bool_and_left h)
        have ihXs := normalizeOpenTyStepList_closed_subst reg hWf σ xs
          (bool_and_right h)
        refine ⟨bool_and_eq_true ihX.1 ihXs.1, ?_⟩
        change normalizeOpenTyStep reg (OpenMirTy.subst σ x) ::
            normalizeOpenTyStepList reg (OpenMirTy.substList σ xs) =
          normalizeOpenTyStep reg x :: normalizeOpenTyStepList reg xs
        rw [ihX.2, ihXs.2]
end

mutual
/-- Normalization commutes cleanly with `OpenMirTy.subst σ`: normalizing before
substitution does not alter the final normalized substituted type. -/
theorem normalizeOpenTyStep_subst_idem (reg : TraitRegistry)
    (hWf : TraitRegistryWf reg = true) (σ : List OpenMirTy) :
    ∀ ty : OpenMirTy,
      normalizeOpenTyStep reg (OpenMirTy.subst σ (normalizeOpenTyStep reg ty)) =
        normalizeOpenTyStep reg (OpenMirTy.subst σ ty)
  | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
  | .param _ | .unsupported => rfl
  | .slice e =>
      congrArg OpenMirTy.slice (normalizeOpenTyStep_subst_idem reg hWf σ e)
  | .array e n =>
      congrArg (fun x => OpenMirTy.array x n)
        (normalizeOpenTyStep_subst_idem reg hWf σ e)
  | .ref m p =>
      congrArg (OpenMirTy.ref m) (normalizeOpenTyStep_subst_idem reg hWf σ p)
  | .rawPtr m p =>
      congrArg (OpenMirTy.rawPtr m)
        (normalizeOpenTyStep_subst_idem reg hWf σ p)
  | .tuple fs =>
      congrArg OpenMirTy.tuple
        (normalizeOpenTyStepList_subst_idem reg hWf σ fs)
  | .adt id args =>
      congrArg (OpenMirTy.adt id)
        (normalizeOpenTyStepList_subst_idem reg hWf σ args)
  | .assocProj s tr args idx => by
      dsimp only [normalizeOpenTyStep]
      cases hRes : resolveAssocType reg (normalizeOpenTyStep reg s) tr
          (normalizeOpenTyStepList reg args) idx with
      | some rhs =>
          have hInfo := resolveAssocType_wf_info reg hWf
            (normalizeOpenTyStep reg s) tr
            (normalizeOpenTyStepList reg args) idx rhs hRes
          have hSubRhs := openMirTy_subst_isClosed σ rhs hInfo.2.2
          have hNormRhs := normalizeOpenTyStep_isClosed reg rhs hInfo.2.2
          have hS := normalizeOpenTyStep_closed_subst reg hWf σ s hInfo.1
          have hA :=
            (normalizeOpenTyStepList_closed_subst
              reg hWf σ args hInfo.2.1).2
          dsimp only [OpenMirTy.subst, normalizeOpenTyStep]
          rw [hSubRhs, hNormRhs, hS.2, hA, hRes]
      | none =>
          dsimp only [OpenMirTy.subst, normalizeOpenTyStep]
          rw [normalizeOpenTyStep_subst_idem reg hWf σ s,
            normalizeOpenTyStepList_subst_idem reg hWf σ args]

theorem normalizeOpenTyStepList_subst_idem (reg : TraitRegistry)
      (hWf : TraitRegistryWf reg = true) (σ : List OpenMirTy) :
      ∀ fs : List OpenMirTy,
        normalizeOpenTyStepList reg
            (OpenMirTy.substList σ (normalizeOpenTyStepList reg fs)) =
          normalizeOpenTyStepList reg (OpenMirTy.substList σ fs)
    | [] => rfl
    | x :: xs => by
        change normalizeOpenTyStep reg
              (OpenMirTy.subst σ (normalizeOpenTyStep reg x)) ::
            normalizeOpenTyStepList reg
              (OpenMirTy.substList σ (normalizeOpenTyStepList reg xs)) =
          normalizeOpenTyStep reg (OpenMirTy.subst σ x) ::
            normalizeOpenTyStepList reg (OpenMirTy.substList σ xs)
        rw [normalizeOpenTyStep_subst_idem reg hWf σ x,
          normalizeOpenTyStepList_subst_idem reg hWf σ xs]
end

/-- Congruence of `substAndNormalize` with pre-normalization. -/
theorem substAndNormalize_normalize_eq (reg : TraitRegistry)
    (hWf : TraitRegistryWf reg = true) (σ : List OpenMirTy) (ty : OpenMirTy) :
    OpenMirTy.substAndNormalize reg normFuel σ
        (normalizeOpenTy reg normFuel ty) =
      OpenMirTy.substAndNormalize reg normFuel σ ty := by
  unfold OpenMirTy.substAndNormalize
  rw [normalizeOpenTy_normFuel_eq_step reg hWf ty,
    normalizeOpenTy_normFuel_eq_step reg hWf (OpenMirTy.subst σ ty),
    normalizeOpenTy_normFuel_eq_step reg hWf
      (OpenMirTy.subst σ (normalizeOpenTyStep reg ty)),
    normalizeOpenTyStep_subst_idem reg hWf σ ty]

/-- Helper avoiding exponential `cases` on `.tuple fs` in `evalNormOpenTySpec`
congruence. -/
theorem evalNormOpenTySpec_tuple_congr (env₁ env₂ : TypeSpecEnv) :
    ∀ fs : List OpenMirTy,
      evalNormOpenTySpec env₁ (.tuple fs) =
        evalNormOpenTySpec env₂ (.tuple fs)
  | [] => rfl
  | [a] => by cases a <;> rfl
  | a :: b :: [] => by
      cases a with
      | int w s =>
          cases b with
          | bool => rfl
          | int _ _ | unit | never | char | ordering | enum _
          | tuple _ | slice _ | array _ _ | adt _ _ | ref _ _ | rawPtr _ _
          | param _ | assocProj _ _ _ _ | unsupported => rfl
      | bool | unit | never | char | ordering | enum _
      | tuple _ | slice _ | array _ _ | adt _ _ | ref _ _ | rawPtr _ _
      | param _ | assocProj _ _ _ _ | unsupported => rfl
  | a :: b :: _ :: _ => by
      cases a with
      | int w s => cases b <;> rfl
      | bool | unit | never | char | ordering | enum _
      | tuple _ | slice _ | array _ _ | adt _ _ | ref _ _ | rawPtr _ _
      | param _ | assocProj _ _ _ _ | unsupported => rfl

mutual
/-- Closedness under `evalNormOpenTySpec`: `paramSpecs` and `assocSpecs` are
not inspected when evaluating a `TypeLayoutSpec` for a closed `OpenMirTy`. -/
theorem evalNormOpenTySpec_isClosed_env_congr (env₁ env₂ : TypeSpecEnv)
    (hAdt : env₁.adtSpecs = env₂.adtSpecs) :
    ∀ ty : OpenMirTy, OpenMirTy.isClosed ty = true →
      evalNormOpenTySpec env₁ ty = evalNormOpenTySpec env₂ ty
  | .bool, _ | .int _ _, _ | .unit, _ | .never, _ | .char, _ | .ordering, _
  | .enum _, _ => rfl
  | .param _, h | .assocProj _ _ _ _, h | .unsupported, h => by cases h
  | .tuple fs, _ => evalNormOpenTySpec_tuple_congr env₁ env₂ fs
  | .slice e, h => by
      unfold evalNormOpenTySpec
      rw [evalNormOpenTySpec_isClosed_env_congr env₁ env₂ hAdt e h]
  | .array e n, h => by
      unfold evalNormOpenTySpec
      rw [evalNormOpenTySpec_isClosed_env_congr env₁ env₂ hAdt e h]
  | .ref m p, h => by
      unfold evalNormOpenTySpec
      rw [evalNormOpenTySpec_isClosed_env_congr env₁ env₂ hAdt p h]
  | .rawPtr m p, h => by
      unfold evalNormOpenTySpec
      rw [evalNormOpenTySpec_isClosed_env_congr env₁ env₂ hAdt p h]
  | .adt id args, h => by
      unfold evalNormOpenTySpec
      rw [hAdt, evalNormOpenTySpecList_isClosed_env_congr env₁ env₂ hAdt args h]

theorem evalNormOpenTySpecList_isClosed_env_congr (env₁ env₂ : TypeSpecEnv)
      (hAdt : env₁.adtSpecs = env₂.adtSpecs) :
      ∀ fs : List OpenMirTy, OpenMirTy.isClosedList fs = true →
        evalNormOpenTySpecList env₁ fs = evalNormOpenTySpecList env₂ fs
    | [], _ => rfl
    | x :: xs, h => by
        dsimp only [OpenMirTy.isClosedList] at h
        unfold evalNormOpenTySpecList
        rw [evalNormOpenTySpec_isClosed_env_congr env₁ env₂ hAdt x
              (bool_and_left h),
          evalNormOpenTySpecList_isClosed_env_congr env₁ env₂ hAdt xs
            (bool_and_right h)]
end

mutual
/-- `evalNormOpenTySpec` commutes with `env₁.adtSpecs = env₂.adtSpecs` and
`env₁.assocSpecs = env₂.assocSpecs` on all `openMirTyNoParam` types. -/
theorem evalNormOpenTySpec_noParam_congr (env₁ env₂ : TypeSpecEnv)
    (hAdt : env₁.adtSpecs = env₂.adtSpecs)
    (hAssoc : ∀ s tr as idx, openMirTyNoParam s = true →
      openMirTyListNoParam as = true →
      env₁.assocSpecs s tr as idx = env₂.assocSpecs s tr as idx) :
    ∀ ty : OpenMirTy, openMirTyNoParam ty = true →
      evalNormOpenTySpec env₁ ty = evalNormOpenTySpec env₂ ty
  | .bool, _ | .int _ _, _ | .unit, _ | .never, _ | .char, _ | .ordering, _
  | .enum _, _ | .unsupported, _ => rfl
  | .param _, h => by cases h
  | .tuple fs, _ => evalNormOpenTySpec_tuple_congr env₁ env₂ fs
  | .slice e, h => by
      unfold evalNormOpenTySpec
      rw [evalNormOpenTySpec_noParam_congr env₁ env₂ hAdt hAssoc e h]
  | .array e n, h => by
      unfold evalNormOpenTySpec
      rw [evalNormOpenTySpec_noParam_congr env₁ env₂ hAdt hAssoc e h]
  | .ref m p, h => by
      unfold evalNormOpenTySpec
      rw [evalNormOpenTySpec_noParam_congr env₁ env₂ hAdt hAssoc p h]
  | .rawPtr m p, h => by
      unfold evalNormOpenTySpec
      rw [evalNormOpenTySpec_noParam_congr env₁ env₂ hAdt hAssoc p h]
  | .adt id args, h => by
      unfold evalNormOpenTySpec
      rw [hAdt, evalNormOpenTySpecList_noParam_congr env₁ env₂ hAdt hAssoc args h]
  | .assocProj s tr args idx, h =>
      hAssoc s tr args idx (bool_and_left h) (bool_and_right h)

theorem evalNormOpenTySpecList_noParam_congr (env₁ env₂ : TypeSpecEnv)
      (hAdt : env₁.adtSpecs = env₂.adtSpecs)
      (hAssoc : ∀ s tr as idx, openMirTyNoParam s = true →
        openMirTyListNoParam as = true →
        env₁.assocSpecs s tr as idx = env₂.assocSpecs s tr as idx) :
      ∀ fs : List OpenMirTy, openMirTyListNoParam fs = true →
        evalNormOpenTySpecList env₁ fs = evalNormOpenTySpecList env₂ fs
    | [], _ => rfl
    | x :: xs, h => by
        dsimp only [openMirTyListNoParam] at h
        unfold evalNormOpenTySpecList
        rw [evalNormOpenTySpec_noParam_congr env₁ env₂ hAdt hAssoc x
              (bool_and_left h),
          evalNormOpenTySpecList_noParam_congr env₁ env₂ hAdt hAssoc xs
            (bool_and_right h)]
end

/-- `evalOpenTySpec` commutes cleanly on `openMirTyNoParam` types when
`adtSpecs` and `assocSpecs` (on `noParam` queries) match. -/
theorem evalOpenTySpec_noParam_congr (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env₁ env₂ : OpenExecEnv)
    (hAdt : env₁.typeSpecs.adtSpecs = env₂.typeSpecs.adtSpecs)
    (hAssoc : ∀ s tr as idx, openMirTyNoParam s = true →
      openMirTyListNoParam as = true →
      env₁.typeSpecs.assocSpecs s tr as idx =
        env₂.typeSpecs.assocSpecs s tr as idx)
    (ty : OpenMirTy) (hNoP : openMirTyNoParam ty = true) :
    evalOpenTySpec prog.traitRegistry normFuel env₁.typeSpecs ty =
      evalOpenTySpec prog.traitRegistry normFuel env₂.typeSpecs ty := by
  unfold evalOpenTySpec
  rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf ty]
  exact evalNormOpenTySpec_noParam_congr env₁.typeSpecs env₂.typeSpecs hAdt hAssoc
    (normalizeOpenTyStep prog.traitRegistry ty)
    (normalizeOpenTyStep_noParam prog.traitRegistry hRegWf ty hNoP)

/-- Extract well-formed `TypeLayoutSpec` list from `AllSubstTypesWellFormed`. -/
theorem substSpecs_of_allSubstTypesWellFormed (prog : OpenProgram)
    (env : OpenExecEnv) :
    ∀ σ : List OpenMirTy,
      AllSubstTypesWellFormed prog env σ →
        ∃ paramSpecs : List TypeLayoutSpec,
          paramSpecs.length = σ.length ∧
          AllParamSpecsWf paramSpecs ∧
          evalSubstSpecs prog env σ = some paramSpecs ∧
          (∀ (i : Nat) (ty : OpenMirTy),
            openListGet? σ i = some ty →
            ∃ sp : TypeLayoutSpec,
              openListGet? paramSpecs i = some sp ∧
              evalOpenTySpec prog.traitRegistry normFuel
                { env.typeSpecs with paramSpecs := [], paramInvs := [] } ty =
                some sp ∧
              WellFormedTypeLayoutSpec sp ∧
              OpenMirTy.isClosed ty = true)
  | [], _ => ⟨[], rfl, True.intro, rfl, fun _ _ h => by cases h⟩
  | ty :: rest, hAll => by
      have hTail : AllSubstTypesWellFormed prog env rest :=
        fun t hMem => hAll t (List.Mem.tail ty hMem)
      have hTy := hAll ty (List.Mem.head rest)
      let ⟨hClosed, _, sp, hEvalSp, hWfSp⟩ := hTy
      let ⟨restSpecs, hLenRest, hWfRest, hEvalRest, hGetRest⟩ :=
        substSpecs_of_allSubstTypesWellFormed prog env rest hTail
      have hNorm : normalizeOpenTy prog.traitRegistry normFuel ty = ty :=
        normalizeOpenTy_isClosed prog.traitRegistry normFuel ty hClosed
      have hEvalNorm : evalNormOpenTySpec env.typeSpecs ty = some sp := by
        unfold evalOpenTySpec at hEvalSp
        rw [hNorm] at hEvalSp
        exact hEvalSp
      have hEvalNormClosed :
          evalNormOpenTySpec
              { env.typeSpecs with paramSpecs := [], paramInvs := [] } ty =
            some sp := by
        rw [← evalNormOpenTySpec_isClosed_env_congr env.typeSpecs
          { env.typeSpecs with paramSpecs := [], paramInvs := [] } rfl ty
          hClosed]
        exact hEvalNorm
      have hEvalClosed :
          evalOpenTySpec prog.traitRegistry normFuel
              { env.typeSpecs with paramSpecs := [], paramInvs := [] } ty =
            some sp := by
        unfold evalOpenTySpec
        rw [hNorm]
        exact hEvalNormClosed
      have hListEval : evalSubstSpecs prog env (ty :: rest) =
          some (sp :: restSpecs) := by
        unfold evalSubstSpecs
        dsimp only [List.map, evalNormOpenTySpecList]
        rw [hNorm, hEvalNorm]
        change (match some sp, evalSubstSpecs prog env rest with
          | some sx, some sxs => some (sx :: sxs)
          | _, _ => none) = some (sp :: restSpecs)
        rw [hEvalRest]
      refine ⟨sp :: restSpecs, congrArg Nat.succ hLenRest, ⟨hWfSp, hWfRest⟩,
        hListEval, ?_⟩
      intro i t hGet
      cases i with
      | zero =>
          cases hGet
          exact ⟨sp, rfl, hEvalClosed, hWfSp, hClosed⟩
      | succ j => exact hGetRest j t hGet

/-- Construct trivial inhabited parameter safety invariants
(`fun _ => True`) satisfying `AllParamInvsWf` from `AllParamSpecsWf`. -/
theorem replicate_true_paramInvsWf :
    ∀ paramSpecs : List TypeLayoutSpec,
      AllParamSpecsWf paramSpecs →
      AllParamInvsWf paramSpecs (List.replicate paramSpecs.length (fun _ => True))
  | [], _ => True.intro
  | sp :: rest, hWf => by
      refine ⟨fun hInhab hSized => ?_, replicate_true_paramInvsWf rest hWf.2⟩
      let ⟨bs, hLang⟩ := (hWf.1.2.2.2.2 hInhab).1 hSized
      exact ⟨bs, hLang, True.intro⟩

mutual
/-- Core structural-recursion congruence on `evalNormOpenTySpec` with ZERO
`normFuel` dependence. -/
theorem evalNormOpenTySpec_subst_param_eq (reg : TraitRegistry)
    (hRegWf : TraitRegistryWf reg = true)
    (env' baseClosed : TypeSpecEnv) (σ : List OpenMirTy)
    (hAdt : env'.adtSpecs = baseClosed.adtSpecs)
    (hBaseParam : ∀ i : Nat, openListGet? baseClosed.paramSpecs i = none)
    (hParam : ∀ i : Nat,
      openListGet? env'.paramSpecs i =
        (openListGet? σ i).bind (fun rep =>
          evalNormOpenTySpec baseClosed (normalizeOpenTyStep reg rep)))
    (hClosed : ∀ (i : Nat) (rep : OpenMirTy),
      openListGet? σ i = some rep → OpenMirTy.isClosed rep = true)
    (hAssoc : ∀ (s : OpenMirTy) (tr : TraitDefId) (args : List OpenMirTy)
        (idx : AssocItemIdx),
      resolveAssocType reg (normalizeOpenTyStep reg s) tr
          (normalizeOpenTyStepList reg args) idx = none →
      env'.assocSpecs (normalizeOpenTyStep reg s) tr
          (normalizeOpenTyStepList reg args) idx =
        evalNormOpenTySpec baseClosed
          (normalizeOpenTyStep reg
            (.assocProj (OpenMirTy.subst σ s) tr
              (OpenMirTy.substList σ args) idx))) :
    ∀ (ty : OpenMirTy), openTyNoOpenTuple ty = true →
      evalNormOpenTySpec env' (normalizeOpenTyStep reg ty) =
        evalNormOpenTySpec baseClosed
          (normalizeOpenTyStep reg (OpenMirTy.subst σ ty))
  | .bool, _ | .int _ _, _ | .unit, _ | .never, _ | .char, _
  | .ordering, _ | .enum _, _ | .unsupported, _ => rfl
  | .tuple fs, hNoTup => by
      cases fs with
      | nil => rfl
      | cons a rest =>
          cases rest with
          | nil => cases a <;> cases hNoTup
          | cons b tl =>
              cases tl with
              | cons _ _ =>
                  cases a <;>
                    first
                    | (cases b <;> cases hNoTup)
                    | cases hNoTup
              | nil =>
                  cases a with
                  | int w s =>
                      cases b with
                      | bool => rfl
                      | _ => cases hNoTup
                  | _ => cases hNoTup
  | .param id, _ => by
      dsimp only [normalizeOpenTyStep, OpenMirTy.subst, evalNormOpenTySpec]
      rw [hParam id]
      cases hGet : openListGet? σ id with
      | none =>
          change none = evalNormOpenTySpec baseClosed (.param id)
          dsimp only [evalNormOpenTySpec]
          exact Eq.symm (hBaseParam id)
      | some rep =>
          change evalNormOpenTySpec baseClosed (normalizeOpenTyStep reg rep) =
            evalNormOpenTySpec baseClosed (normalizeOpenTyStep reg rep)
          rfl
  | .slice e, hNoTup => by
      dsimp only [normalizeOpenTyStep, OpenMirTy.subst, evalNormOpenTySpec]
      rw [evalNormOpenTySpec_subst_param_eq reg hRegWf env' baseClosed σ hAdt
        hBaseParam hParam hClosed hAssoc e hNoTup]
  | .array e n, hNoTup => by
      dsimp only [normalizeOpenTyStep, OpenMirTy.subst, evalNormOpenTySpec]
      rw [evalNormOpenTySpec_subst_param_eq reg hRegWf env' baseClosed σ hAdt
        hBaseParam hParam hClosed hAssoc e hNoTup]
  | .ref m p, hNoTup => by
      dsimp only [normalizeOpenTyStep, OpenMirTy.subst, evalNormOpenTySpec]
      rw [evalNormOpenTySpec_subst_param_eq reg hRegWf env' baseClosed σ hAdt
        hBaseParam hParam hClosed hAssoc p hNoTup]
  | .rawPtr m p, hNoTup => by
      dsimp only [normalizeOpenTyStep, OpenMirTy.subst, evalNormOpenTySpec]
      rw [evalNormOpenTySpec_subst_param_eq reg hRegWf env' baseClosed σ hAdt
        hBaseParam hParam hClosed hAssoc p hNoTup]
  | .adt id args, hNoTup => by
      dsimp only [normalizeOpenTyStep, OpenMirTy.subst, evalNormOpenTySpec]
      rw [hAdt, evalNormOpenTySpec_subst_param_eq_list reg hRegWf env' baseClosed
        σ hAdt hBaseParam hParam hClosed hAssoc args hNoTup]
  | .assocProj s tr args idx, _ => by
      dsimp only [normalizeOpenTyStep]
      cases hRes : resolveAssocType reg (normalizeOpenTyStep reg s) tr
          (normalizeOpenTyStepList reg args) idx with
      | some rhs =>
          have hInfo := resolveAssocType_wf_info reg hRegWf
            (normalizeOpenTyStep reg s) tr (normalizeOpenTyStepList reg args)
            idx rhs hRes
          have hS := normalizeOpenTyStep_closed_subst reg hRegWf σ s hInfo.1
          have hA :=
            (normalizeOpenTyStepList_closed_subst
              reg hRegWf σ args hInfo.2.1).2
          dsimp only [OpenMirTy.subst, normalizeOpenTyStep]
          rw [hS.2, hA, hRes]
          exact evalNormOpenTySpec_isClosed_env_congr env' baseClosed hAdt rhs
            hInfo.2.2
      | none =>
          dsimp only [evalNormOpenTySpec]
          exact hAssoc s tr args idx hRes

theorem evalNormOpenTySpec_subst_param_eq_list (reg : TraitRegistry)
      (hRegWf : TraitRegistryWf reg = true)
      (env' baseClosed : TypeSpecEnv) (σ : List OpenMirTy)
      (hAdt : env'.adtSpecs = baseClosed.adtSpecs)
      (hBaseParam : ∀ i : Nat, openListGet? baseClosed.paramSpecs i = none)
      (hParam : ∀ i : Nat,
        openListGet? env'.paramSpecs i =
          (openListGet? σ i).bind (fun rep =>
            evalNormOpenTySpec baseClosed (normalizeOpenTyStep reg rep)))
      (hClosed : ∀ (i : Nat) (rep : OpenMirTy),
        openListGet? σ i = some rep → OpenMirTy.isClosed rep = true)
      (hAssoc : ∀ (s : OpenMirTy) (tr : TraitDefId) (args : List OpenMirTy)
          (idx : AssocItemIdx),
        resolveAssocType reg (normalizeOpenTyStep reg s) tr
            (normalizeOpenTyStepList reg args) idx = none →
        env'.assocSpecs (normalizeOpenTyStep reg s) tr
            (normalizeOpenTyStepList reg args) idx =
          evalNormOpenTySpec baseClosed
            (normalizeOpenTyStep reg
              (.assocProj (OpenMirTy.subst σ s) tr
                (OpenMirTy.substList σ args) idx))) :
      ∀ (xs : List OpenMirTy), openTyListNoOpenTuple xs = true →
        evalNormOpenTySpecList env' (normalizeOpenTyStepList reg xs) =
          evalNormOpenTySpecList baseClosed
            (normalizeOpenTyStepList reg (OpenMirTy.substList σ xs))
    | [], _ => rfl
    | x :: xs, hTup => by
        dsimp only [openTyListNoOpenTuple] at hTup
        dsimp only [normalizeOpenTyStepList, OpenMirTy.substList,
          evalNormOpenTySpecList]
        rw [evalNormOpenTySpec_subst_param_eq reg hRegWf env' baseClosed σ hAdt
            hBaseParam hParam hClosed hAssoc x (bool_and_left hTup),
          evalNormOpenTySpec_subst_param_eq_list reg hRegWf env' baseClosed σ
            hAdt hBaseParam hParam hClosed hAssoc xs (bool_and_right hTup)]
end

/-- Core congruence: for every `ty` with `openTyNoOpenTuple ty = true`,
evaluating `ty` under `env'` equals evaluating `substAndNormalize σ ty` under
`baseClosed` (`{ env.typeSpecs with paramSpecs := [], paramInvs := [] }`). -/
theorem evalOpenTySpec_subst_param_eq (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env : OpenExecEnv) (σ : List OpenMirTy) (paramSpecs : List TypeLayoutSpec)
    (paramInvs : List (List AllocByte → Prop))
    (hLenEq : paramSpecs.length = σ.length)
    (hMap : ∀ (i : Nat) (ty : OpenMirTy), openListGet? σ i = some ty →
      ∃ sp : TypeLayoutSpec, openListGet? paramSpecs i = some sp ∧
        evalOpenTySpec prog.traitRegistry normFuel
          { env.typeSpecs with paramSpecs := [], paramInvs := [] } ty =
          some sp ∧
        OpenMirTy.isClosed ty = true) :
    let baseClosed : TypeSpecEnv :=
      { env.typeSpecs with paramSpecs := [], paramInvs := [] }
    let assocSpecFn := instAssocSpecs prog.traitRegistry env.typeSpecs σ
    let env' : OpenExecEnv :=
      { env with typeSpecs := (substTypeSpecEnv env.typeSpecs paramSpecs
          paramInvs assocSpecFn) }
    ∀ ty : OpenMirTy, openTyNoOpenTuple ty = true →
      evalOpenTySpec prog.traitRegistry normFuel env'.typeSpecs ty =
        evalOpenTySpec prog.traitRegistry normFuel baseClosed
          (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ ty) := by
  intro baseClosed assocSpecFn env' ty hNoTup
  have hParam : ∀ i : Nat,
      openListGet? env'.typeSpecs.paramSpecs i =
        (openListGet? σ i).bind (fun rep =>
          evalNormOpenTySpec baseClosed
            (normalizeOpenTyStep prog.traitRegistry rep)) := by
    intro i
    dsimp only [env', substTypeSpecEnv]
    cases hGet : openListGet? σ i with
    | some rep =>
        cases hMap i rep hGet with
        | intro sp hRest =>
            have hSp := hRest.1
            have hEvalRep := hRest.2.1
            unfold evalOpenTySpec at hEvalRep
            rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf rep]
              at hEvalRep
            rw [hSp]
            exact hEvalRep.symm
    | none =>
        have hAux : ∀ (ps : List TypeLayoutSpec) (ts : List OpenMirTy)
            (k : Nat), ps.length = ts.length → openListGet? ts k = none →
            openListGet? ps k = none := by
          intro ps
          induction ps with
          | nil => intro ts k _ _; cases k <;> rfl
          | cons p ps' ih =>
              intro ts k hL hN
              cases ts with
              | nil => cases hL
              | cons t ts' =>
                  cases k with
                  | zero => cases hN
                  | succ j => exact ih ts' j (Nat.succ.inj hL) hN
        exact hAux paramSpecs σ i hLenEq hGet
  have hClosed : ∀ (i : Nat) (rep : OpenMirTy),
      openListGet? σ i = some rep → OpenMirTy.isClosed rep = true := by
    intro i rep hGet
    cases hMap i rep hGet with
    | intro _ hRest => exact hRest.2.2
  have hAssoc : ∀ (s : OpenMirTy) (tr : TraitDefId) (args : List OpenMirTy)
      (idx : AssocItemIdx),
      resolveAssocType prog.traitRegistry
          (normalizeOpenTyStep prog.traitRegistry s) tr
          (normalizeOpenTyStepList prog.traitRegistry args) idx = none →
      env'.typeSpecs.assocSpecs (normalizeOpenTyStep prog.traitRegistry s) tr
          (normalizeOpenTyStepList prog.traitRegistry args) idx =
        evalNormOpenTySpec baseClosed
          (normalizeOpenTyStep prog.traitRegistry
            (.assocProj (OpenMirTy.subst σ s) tr
              (OpenMirTy.substList σ args) idx)) := by
    intro s tr args idx hRes
    dsimp only [env', substTypeSpecEnv, assocSpecFn, instAssocSpecs]
    cases hNoP :
        openMirTyNoParam (normalizeOpenTyStep prog.traitRegistry s) &&
          openMirTyListNoParam
            (normalizeOpenTyStepList prog.traitRegistry args) with
    | true =>
        have hSNoP := openMirTy_subst_noParam σ _ (bool_and_left hNoP)
        have hANoP := openMirTyList_subst_noParam σ _
          (bool_and_right hNoP)
        have hAList :
            normalizeOpenTyStepList prog.traitRegistry
                (OpenMirTy.substList σ args) =
              normalizeOpenTyStepList prog.traitRegistry args := by
          rw [← normalizeOpenTyStepList_subst_idem
            prog.traitRegistry hRegWf σ args, hANoP,
            normalizeOpenTyStepList_idempotent
              prog.traitRegistry hRegWf args]
        dsimp only [normalizeOpenTyStep]
        rw [← normalizeOpenTyStep_subst_idem prog.traitRegistry hRegWf σ s,
          hSNoP, normalizeOpenTyStep_idempotent prog.traitRegistry hRegWf s,
          hAList, hRes]
        rfl
    | false =>
        have hSIdem :
            normalizeOpenTyStep prog.traitRegistry
                (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ
                  (normalizeOpenTyStep prog.traitRegistry s)) =
              normalizeOpenTyStep prog.traitRegistry (OpenMirTy.subst σ s) := by
          dsimp only [OpenMirTy.substAndNormalize]
          rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf _,
            normalizeOpenTyStep_idempotent prog.traitRegistry hRegWf _,
            normalizeOpenTyStep_subst_idem prog.traitRegistry hRegWf σ s]
        have hAMapGen : ∀ ts : List OpenMirTy,
            normalizeOpenTyStepList prog.traitRegistry
                (List.map
                  (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ)
                  (normalizeOpenTyStepList prog.traitRegistry ts)) =
              normalizeOpenTyStepList prog.traitRegistry
                (OpenMirTy.substList σ ts) := by
          intro ts
          induction ts with
          | nil => rfl
          | cons a as ihAs =>
              change normalizeOpenTyStep prog.traitRegistry
                    (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ
                      (normalizeOpenTyStep prog.traitRegistry a)) ::
                  normalizeOpenTyStepList prog.traitRegistry
                    (List.map
                      (OpenMirTy.substAndNormalize prog.traitRegistry normFuel
                        σ)
                      (normalizeOpenTyStepList prog.traitRegistry as)) =
                normalizeOpenTyStep prog.traitRegistry (OpenMirTy.subst σ a) ::
                  normalizeOpenTyStepList prog.traitRegistry
                    (OpenMirTy.substList σ as)
              have hA1 : normalizeOpenTyStep prog.traitRegistry
                  (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ
                    (normalizeOpenTyStep prog.traitRegistry a)) =
                  normalizeOpenTyStep prog.traitRegistry
                    (OpenMirTy.subst σ a) := by
                dsimp only [OpenMirTy.substAndNormalize]
                rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf _,
                  normalizeOpenTyStep_idempotent prog.traitRegistry hRegWf _,
                  normalizeOpenTyStep_subst_idem prog.traitRegistry hRegWf σ a]
              rw [hA1, ihAs]
        have hAMap := hAMapGen args
        unfold evalOpenTySpec
        rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf _]
        apply congrArg (evalNormOpenTySpec baseClosed)
        dsimp only [normalizeOpenTyStep]
        rw [hSIdem, hAMap]
  unfold evalOpenTySpec OpenMirTy.substAndNormalize
  rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf ty,
    normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf
      (OpenMirTy.subst σ ty),
    normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf
      (normalizeOpenTyStep prog.traitRegistry (OpenMirTy.subst σ ty)),
    normalizeOpenTyStep_idempotent prog.traitRegistry hRegWf
      (OpenMirTy.subst σ ty)]
  exact evalNormOpenTySpec_subst_param_eq prog.traitRegistry hRegWf
    env'.typeSpecs baseClosed σ rfl (fun _ => rfl) hParam hClosed hAssoc ty
    hNoTup

/-- Direct `.assocProj` substitution congruence for already-normalized
`(selfN, argsN)`, without requiring `openTyNoOpenTuple`. -/
theorem evalOpenTySpec_subst_assocProj (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env : OpenExecEnv) (σ : List OpenMirTy) (paramSpecs : List TypeLayoutSpec)
    (paramInvs : List (List AllocByte → Prop))
    (selfN : OpenMirTy) (tr : TraitDefId) (argsN : List OpenMirTy)
    (idx : AssocItemIdx) :
    let baseClosed : TypeSpecEnv :=
      { env.typeSpecs with paramSpecs := [], paramInvs := [] }
    let assocSpecFn := instAssocSpecs prog.traitRegistry env.typeSpecs σ
    let env' : OpenExecEnv :=
      { env with typeSpecs := (substTypeSpecEnv env.typeSpecs paramSpecs
          paramInvs assocSpecFn) }
    evalOpenTySpec prog.traitRegistry normFuel env'.typeSpecs
        (.assocProj selfN tr argsN idx) =
      evalOpenTySpec prog.traitRegistry normFuel baseClosed
        (.assocProj (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ
            selfN) tr
          (argsN.map (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ))
          idx) := by
  intro baseClosed assocSpecFn env'
  unfold evalOpenTySpec
  rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf
      (.assocProj selfN tr argsN idx),
    normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf _]
  dsimp only [normalizeOpenTyStep]
  have hArgsNorm :
      normalizeOpenTyStepList prog.traitRegistry
          (List.map (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ)
            argsN) =
        List.map (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ)
          argsN := by
    induction argsN with
    | nil => rfl
    | cons a as ih =>
        dsimp only [List.map, normalizeOpenTyStepList,
          OpenMirTy.substAndNormalize]
        rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf _,
          normalizeOpenTyStep_idempotent prog.traitRegistry hRegWf _, ih]
  have hSelfNorm :
      normalizeOpenTyStep prog.traitRegistry
          (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ selfN) =
        OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ selfN := by
    dsimp only [OpenMirTy.substAndNormalize]
    rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf _,
      normalizeOpenTyStep_idempotent prog.traitRegistry hRegWf _]
  cases hRes : resolveAssocType prog.traitRegistry
      (normalizeOpenTyStep prog.traitRegistry selfN) tr
      (normalizeOpenTyStepList prog.traitRegistry argsN) idx with
  | some rhs =>
      have hInfo := resolveAssocType_wf_info prog.traitRegistry hRegWf
        (normalizeOpenTyStep prog.traitRegistry selfN) tr
        (normalizeOpenTyStepList prog.traitRegistry argsN) idx rhs hRes
      have hS1 := openMirTy_subst_isClosed σ _ hInfo.1
      have hA1 := openMirTy_substList_isClosed σ _
        hInfo.2.1
      have hSIdem :
          OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ selfN =
            normalizeOpenTyStep prog.traitRegistry
              (OpenMirTy.subst σ
                (normalizeOpenTyStep prog.traitRegistry selfN)) := by
        dsimp only [OpenMirTy.substAndNormalize]
        rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf _,
          normalizeOpenTyStep_subst_idem prog.traitRegistry hRegWf σ selfN]
      have hAMapGen : ∀ ts : List OpenMirTy,
          List.map (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ)
              ts =
            normalizeOpenTyStepList prog.traitRegistry
              (OpenMirTy.substList σ
                (normalizeOpenTyStepList prog.traitRegistry ts)) := by
        intro ts
        induction ts with
        | nil => rfl
        | cons a as ih =>
            change OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ
                  a ::
                List.map
                  (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ)
                  as =
              normalizeOpenTyStep prog.traitRegistry
                  (OpenMirTy.subst σ
                    (normalizeOpenTyStep prog.traitRegistry a)) ::
                normalizeOpenTyStepList prog.traitRegistry
                  (OpenMirTy.substList σ
                    (normalizeOpenTyStepList prog.traitRegistry as))
            have hOne :
                OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ a =
                  normalizeOpenTyStep prog.traitRegistry
                    (OpenMirTy.subst σ
                      (normalizeOpenTyStep prog.traitRegistry a)) := by
              dsimp only [OpenMirTy.substAndNormalize]
              rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf _,
                normalizeOpenTyStep_subst_idem prog.traitRegistry hRegWf σ a]
            rw [hOne, ih]
      have hAMap := hAMapGen argsN
      rw [hSelfNorm, hArgsNorm, hSIdem, hAMap, hS1, hA1,
        normalizeOpenTyStep_idempotent prog.traitRegistry hRegWf selfN,
        normalizeOpenTyStepList_idempotent
          prog.traitRegistry hRegWf argsN,
        hRes]
      exact evalNormOpenTySpec_isClosed_env_congr env'.typeSpecs baseClosed rfl
        rhs hInfo.2.2
  | none =>
      dsimp only [evalNormOpenTySpec, env', assocSpecFn, substTypeSpecEnv,
        instAssocSpecs]
      cases hNoP :
          openMirTyNoParam (normalizeOpenTyStep prog.traitRegistry selfN) &&
            openMirTyListNoParam
              (normalizeOpenTyStepList prog.traitRegistry argsN) with
      | true =>
          have hSNoP := openMirTy_subst_noParam σ _ (bool_and_left hNoP)
          have hANoP0 := bool_and_right hNoP
          have hSIdem :
              OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ selfN =
                normalizeOpenTyStep prog.traitRegistry selfN := by
            dsimp only [OpenMirTy.substAndNormalize]
            rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf _,
              ← normalizeOpenTyStep_subst_idem prog.traitRegistry hRegWf σ selfN,
              hSNoP, normalizeOpenTyStep_idempotent prog.traitRegistry hRegWf]
          have hAMapGen : ∀ ts : List OpenMirTy,
              openMirTyListNoParam
                  (normalizeOpenTyStepList prog.traitRegistry ts) = true →
              List.map
                  (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ)
                  ts =
                normalizeOpenTyStepList prog.traitRegistry ts := by
            intro ts hTs
            induction ts with
            | nil => rfl
            | cons a as ih =>
                dsimp only [normalizeOpenTyStepList, openMirTyListNoParam]
                  at hTs
                change OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ
                      a ::
                    List.map
                      (OpenMirTy.substAndNormalize prog.traitRegistry normFuel
                        σ)
                      as =
                  normalizeOpenTyStep prog.traitRegistry a ::
                    normalizeOpenTyStepList prog.traitRegistry as
                have hA1 :
                    OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ a =
                      normalizeOpenTyStep prog.traitRegistry a := by
                  dsimp only [OpenMirTy.substAndNormalize]
                  rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf
                      _,
                    ← normalizeOpenTyStep_subst_idem prog.traitRegistry hRegWf σ
                      a,
                    openMirTy_subst_noParam σ _ (bool_and_left hTs),
                    normalizeOpenTyStep_idempotent prog.traitRegistry hRegWf a]
                rw [hA1, ih (bool_and_right hTs)]
          have hAMap := hAMapGen argsN hANoP0
          rw [hSelfNorm, hArgsNorm, hSIdem, hAMap, hRes]
          rfl
      | false =>
          rw [hSelfNorm, hArgsNorm]
          have hSStep :
              OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ
                  (normalizeOpenTyStep prog.traitRegistry selfN) =
                OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ
                  selfN := by
            dsimp only [OpenMirTy.substAndNormalize]
            rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf _,
              normalizeOpenTyStep_subst_idem prog.traitRegistry hRegWf σ selfN,
              ← normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf _]
          have hAStepGen : ∀ ts : List OpenMirTy,
              List.map
                  (fun t => OpenMirTy.substAndNormalize prog.traitRegistry
                    normFuel σ t)
                  (normalizeOpenTyStepList prog.traitRegistry ts) =
                List.map
                  (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ)
                  ts := by
            intro ts
            induction ts with
            | nil => rfl
            | cons a as ih =>
                dsimp only [normalizeOpenTyStepList, List.map]
                have hOne :
                    OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ
                        (normalizeOpenTyStep prog.traitRegistry a) =
                      OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ
                        a := by
                  dsimp only [OpenMirTy.substAndNormalize]
                  rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf
                      _,
                    normalizeOpenTyStep_subst_idem prog.traitRegistry hRegWf σ
                      a,
                    ← normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf
                      _]
                rw [hOne, ih]
          have hAStep := hAStepGen argsN
          rw [hSStep, hAStep]
          unfold evalOpenTySpec
          rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf _]
          dsimp only [normalizeOpenTyStep]
          rw [hSelfNorm, hArgsNorm]
          cases resolveAssocType prog.traitRegistry
              (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ selfN)
              tr
              (List.map
                (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ)
                argsN) idx with
          | some _ => rfl
          | none => rfl

/-- If a normalized open type reduces to `.int w s`, substituting any type-arg
list preserves that normalized result. -/
theorem normalizeOpenTyStep_eq_int_subst (reg : TraitRegistry)
    (hRegWf : TraitRegistryWf reg = true) (σ : List OpenMirTy)
    (ty : OpenMirTy) (w : IntWidth) (s : Bool)
    (h : normalizeOpenTyStep reg ty = .int w s) :
    normalizeOpenTyStep reg (OpenMirTy.subst σ ty) = .int w s := by
  cases ty with
  | int _ _ => exact h
  | assocProj selfTy tr args idx =>
      dsimp only [normalizeOpenTyStep] at h
      cases hRes : resolveAssocType reg (normalizeOpenTyStep reg selfTy) tr
          (normalizeOpenTyStepList reg args) idx with
      | none => rw [hRes] at h; cases h
      | some rhs =>
          rw [hRes] at h
          have hInfo := resolveAssocType_wf_info reg hRegWf
            (normalizeOpenTyStep reg selfTy) tr
            (normalizeOpenTyStepList reg args) idx rhs hRes
          have hS := normalizeOpenTyStep_closed_subst reg hRegWf σ selfTy hInfo.1
          have hA :=
            (normalizeOpenTyStepList_closed_subst
              reg hRegWf σ args hInfo.2.1).2
          dsimp only [OpenMirTy.subst, normalizeOpenTyStep]
          rw [hS.2, hA, hRes]
          exact h
  | bool | unit | never | char | ordering | enum _ | tuple _ | slice _
  | array _ _ | adt _ _ | ref _ _ | rawPtr _ _ | param _ | unsupported =>
      cases h

/-- If a normalized open type reduces to `.bool`, substituting any type-arg
list preserves that normalized result. -/
theorem normalizeOpenTyStep_eq_bool_subst (reg : TraitRegistry)
    (hRegWf : TraitRegistryWf reg = true) (σ : List OpenMirTy)
    (ty : OpenMirTy) (h : normalizeOpenTyStep reg ty = .bool) :
    normalizeOpenTyStep reg (OpenMirTy.subst σ ty) = .bool := by
  cases ty with
  | bool => exact h
  | assocProj selfTy tr args idx =>
      dsimp only [normalizeOpenTyStep] at h
      cases hRes : resolveAssocType reg (normalizeOpenTyStep reg selfTy) tr
          (normalizeOpenTyStepList reg args) idx with
      | none => rw [hRes] at h; cases h
      | some rhs =>
          rw [hRes] at h
          have hInfo := resolveAssocType_wf_info reg hRegWf
            (normalizeOpenTyStep reg selfTy) tr
            (normalizeOpenTyStepList reg args) idx rhs hRes
          have hS := normalizeOpenTyStep_closed_subst reg hRegWf σ selfTy hInfo.1
          have hA :=
            (normalizeOpenTyStepList_closed_subst
              reg hRegWf σ args hInfo.2.1).2
          dsimp only [OpenMirTy.subst, normalizeOpenTyStep]
          rw [hS.2, hA, hRes]
          exact h
  | int _ _ | unit | never | char | ordering | enum _ | tuple _ | slice _
  | array _ _ | adt _ _ | ref _ _ | rawPtr _ _ | param _ | unsupported =>
      cases h

private theorem evalNormOpenTySpec_tuple_one (env : TypeSpecEnv)
    (a : OpenMirTy) :
    evalNormOpenTySpec env (.tuple [a]) = none := by
  cases a <;> rfl

private theorem evalNormOpenTySpec_tuple_three (env : TypeSpecEnv)
    (a b c : OpenMirTy) (tl : List OpenMirTy) :
    evalNormOpenTySpec env (.tuple (a :: b :: c :: tl)) = none := by
  cases a <;>
    first
    | (cases b <;> rfl)
    | rfl

private theorem evalNormOpenTySpec_tuple_two (env : TypeSpecEnv)
    (a b : OpenMirTy) (sp : TypeLayoutSpec)
    (h : evalNormOpenTySpec env (.tuple [a, b]) = some sp) :
    ∃ w s, a = .int w s ∧ b = .bool := by
  cases a with
  | int w s =>
      cases b with
      | bool => exact ⟨w, s, rfl, rfl⟩
      | _ => cases h
  | _ => cases h

mutual
/-- Reverse implication on normalized specs with ZERO `normFuel` dependence. -/
theorem evalNormOpenTySpec_subst_param_some (reg : TraitRegistry)
    (hRegWf : TraitRegistryWf reg = true)
    (env' baseClosed : TypeSpecEnv) (σ : List OpenMirTy)
    (hAdt : env'.adtSpecs = baseClosed.adtSpecs)
    (hParam : ∀ i : Nat,
      openListGet? env'.paramSpecs i =
        (openListGet? σ i).bind (fun rep =>
          evalNormOpenTySpec baseClosed (normalizeOpenTyStep reg rep)))
    (hClosed : ∀ (i : Nat) (rep : OpenMirTy),
      openListGet? σ i = some rep → OpenMirTy.isClosed rep = true)
    (hAssoc : ∀ (s : OpenMirTy) (tr : TraitDefId) (args : List OpenMirTy)
        (idx : AssocItemIdx),
      resolveAssocType reg (normalizeOpenTyStep reg s) tr
          (normalizeOpenTyStepList reg args) idx = none →
      env'.assocSpecs (normalizeOpenTyStep reg s) tr
          (normalizeOpenTyStepList reg args) idx =
        evalNormOpenTySpec baseClosed
          (normalizeOpenTyStep reg
            (.assocProj (OpenMirTy.subst σ s) tr
              (OpenMirTy.substList σ args) idx))) :
    ∀ (ty : OpenMirTy) (sp : TypeLayoutSpec),
      evalNormOpenTySpec env' (normalizeOpenTyStep reg ty) = some sp →
      evalNormOpenTySpec baseClosed
          (normalizeOpenTyStep reg (OpenMirTy.subst σ ty)) =
        some sp
  | .bool, _, hEval | .int _ _, _, hEval | .unit, _, hEval | .never, _, hEval
  | .char, _, hEval | .ordering, _, hEval | .enum _, _, hEval => hEval
  | .unsupported, _, hEval => by cases hEval
  | .tuple fs, sp, hEval => by
      dsimp only [normalizeOpenTyStep] at hEval
      cases fs with
      | nil => exact hEval
      | cons a rest =>
          cases rest with
          | nil =>
              dsimp only [normalizeOpenTyStepList] at hEval
              rw [evalNormOpenTySpec_tuple_one] at hEval
              cases hEval
          | cons b tl =>
              cases tl with
              | cons c cs =>
                  dsimp only [normalizeOpenTyStepList] at hEval
                  rw [evalNormOpenTySpec_tuple_three] at hEval
                  cases hEval
              | nil =>
                  dsimp only [normalizeOpenTyStepList] at hEval
                  let ⟨w, s, hA, hB⟩ := evalNormOpenTySpec_tuple_two env'
                    (normalizeOpenTyStep reg a) (normalizeOpenTyStep reg b) sp
                    hEval
                  rw [hA, hB] at hEval
                  have hA' := normalizeOpenTyStep_eq_int_subst reg hRegWf σ a
                    w s hA
                  have hB' := normalizeOpenTyStep_eq_bool_subst reg hRegWf σ b
                    hB
                  dsimp only [OpenMirTy.subst, OpenMirTy.substList,
                    normalizeOpenTyStep, normalizeOpenTyStepList]
                  rw [hA', hB']
                  exact hEval
  | .param id, sp, hEval => by
      dsimp only [normalizeOpenTyStep, evalNormOpenTySpec] at hEval
      rw [hParam id] at hEval
      cases hGet : openListGet? σ id with
      | none =>
          rw [hGet] at hEval
          change none = some sp at hEval
          cases hEval
      | some rep =>
          rw [hGet] at hEval
          change evalNormOpenTySpec baseClosed
              (normalizeOpenTyStep reg rep) =
            some sp at hEval
          dsimp only [normalizeOpenTyStep, OpenMirTy.subst]
          rw [hGet]
          exact hEval
  | .slice e, sp, hEval => by
      dsimp only [normalizeOpenTyStep, evalNormOpenTySpec] at hEval
      cases hE : evalNormOpenTySpec env' (normalizeOpenTyStep reg e) with
      | none => rw [hE] at hEval; cases hEval
      | some eSp =>
          rw [hE] at hEval
          dsimp only [normalizeOpenTyStep, OpenMirTy.subst, evalNormOpenTySpec]
          rw [evalNormOpenTySpec_subst_param_some reg hRegWf env' baseClosed σ
            hAdt hParam hClosed hAssoc e eSp hE]
          exact hEval
  | .array e n, sp, hEval => by
      dsimp only [normalizeOpenTyStep, evalNormOpenTySpec] at hEval
      cases hE : evalNormOpenTySpec env' (normalizeOpenTyStep reg e) with
      | none => rw [hE] at hEval; cases hEval
      | some eSp =>
          rw [hE] at hEval
          dsimp only [normalizeOpenTyStep, OpenMirTy.subst, evalNormOpenTySpec]
          rw [evalNormOpenTySpec_subst_param_some reg hRegWf env' baseClosed σ
            hAdt hParam hClosed hAssoc e eSp hE]
          exact hEval
  | .ref m p, sp, hEval => by
      dsimp only [normalizeOpenTyStep, evalNormOpenTySpec] at hEval
      cases hP : evalNormOpenTySpec env' (normalizeOpenTyStep reg p) with
      | none => rw [hP] at hEval; cases hEval
      | some pSp =>
          rw [hP] at hEval
          dsimp only [normalizeOpenTyStep, OpenMirTy.subst, evalNormOpenTySpec]
          rw [evalNormOpenTySpec_subst_param_some reg hRegWf env' baseClosed σ
            hAdt hParam hClosed hAssoc p pSp hP]
          exact hEval
  | .rawPtr m p, sp, hEval => by
      dsimp only [normalizeOpenTyStep, evalNormOpenTySpec] at hEval
      cases hP : evalNormOpenTySpec env' (normalizeOpenTyStep reg p) with
      | none => rw [hP] at hEval; cases hEval
      | some pSp =>
          rw [hP] at hEval
          dsimp only [normalizeOpenTyStep, OpenMirTy.subst, evalNormOpenTySpec]
          rw [evalNormOpenTySpec_subst_param_some reg hRegWf env' baseClosed σ
            hAdt hParam hClosed hAssoc p pSp hP]
          exact hEval
  | .adt id args, sp, hEval => by
      dsimp only [normalizeOpenTyStep, evalNormOpenTySpec] at hEval
      cases hAs : evalNormOpenTySpecList env'
          (normalizeOpenTyStepList reg args) with
      | none => rw [hAs] at hEval; cases hEval
      | some argSps =>
          rw [hAs] at hEval
          dsimp only [normalizeOpenTyStep, OpenMirTy.subst, evalNormOpenTySpec]
          rw [← hAdt, evalNormOpenTySpec_subst_param_some_list reg hRegWf env'
            baseClosed σ hAdt hParam hClosed hAssoc args argSps hAs]
          exact hEval
  | .assocProj s tr args idx, sp, hEval => by
      dsimp only [normalizeOpenTyStep] at hEval
      cases hRes : resolveAssocType reg (normalizeOpenTyStep reg s) tr
          (normalizeOpenTyStepList reg args) idx with
      | some rhs =>
          rw [hRes] at hEval
          have hInfo := resolveAssocType_wf_info reg hRegWf
            (normalizeOpenTyStep reg s) tr (normalizeOpenTyStepList reg args)
            idx rhs hRes
          have hS := normalizeOpenTyStep_closed_subst reg hRegWf σ s hInfo.1
          have hA :=
            (normalizeOpenTyStepList_closed_subst
              reg hRegWf σ args hInfo.2.1).2
          dsimp only [OpenMirTy.subst, normalizeOpenTyStep]
          rw [hS.2, hA, hRes]
          rw [← evalNormOpenTySpec_isClosed_env_congr env' baseClosed hAdt rhs
            hInfo.2.2]
          exact hEval
      | none =>
          rw [hRes] at hEval
          dsimp only [evalNormOpenTySpec] at hEval
          dsimp only [OpenMirTy.subst]
          rw [← hAssoc s tr args idx hRes]
          exact hEval

theorem evalNormOpenTySpec_subst_param_some_list (reg : TraitRegistry)
      (hRegWf : TraitRegistryWf reg = true)
      (env' baseClosed : TypeSpecEnv) (σ : List OpenMirTy)
      (hAdt : env'.adtSpecs = baseClosed.adtSpecs)
      (hParam : ∀ i : Nat,
        openListGet? env'.paramSpecs i =
          (openListGet? σ i).bind (fun rep =>
            evalNormOpenTySpec baseClosed (normalizeOpenTyStep reg rep)))
      (hClosed : ∀ (i : Nat) (rep : OpenMirTy),
        openListGet? σ i = some rep → OpenMirTy.isClosed rep = true)
      (hAssoc : ∀ (s : OpenMirTy) (tr : TraitDefId) (args : List OpenMirTy)
          (idx : AssocItemIdx),
        resolveAssocType reg (normalizeOpenTyStep reg s) tr
            (normalizeOpenTyStepList reg args) idx = none →
        env'.assocSpecs (normalizeOpenTyStep reg s) tr
            (normalizeOpenTyStepList reg args) idx =
          evalNormOpenTySpec baseClosed
            (normalizeOpenTyStep reg
              (.assocProj (OpenMirTy.subst σ s) tr
                (OpenMirTy.substList σ args) idx))) :
      ∀ (xs : List OpenMirTy) (sps : List TypeLayoutSpec),
        evalNormOpenTySpecList env' (normalizeOpenTyStepList reg xs) =
          some sps →
        evalNormOpenTySpecList baseClosed
          (normalizeOpenTyStepList reg (OpenMirTy.substList σ xs)) = some sps
    | [], sps, hL => by cases hL; rfl
    | x :: xs, sps, hL => by
        dsimp only [normalizeOpenTyStepList, evalNormOpenTySpecList] at hL
        cases hx : evalNormOpenTySpec env' (normalizeOpenTyStep reg x) with
        | none => rw [hx] at hL; cases hL
        | some xSp =>
            rw [hx] at hL
            cases hxs : evalNormOpenTySpecList env'
                (normalizeOpenTyStepList reg xs) with
            | none => rw [hxs] at hL; cases hL
            | some xsSps =>
                rw [hxs] at hL
                cases hL
                dsimp only [OpenMirTy.substList, normalizeOpenTyStepList,
                  evalNormOpenTySpecList]
                rw [evalNormOpenTySpec_subst_param_some reg hRegWf env'
                    baseClosed σ hAdt hParam hClosed hAssoc x xSp hx,
                  evalNormOpenTySpec_subst_param_some_list reg hRegWf env'
                    baseClosed σ hAdt hParam hClosed hAssoc xs xsSps hxs]
end

/-- Reverse implication (unconditional on `ty`): whenever `evalOpenTySpec`
succeeds on `env'.typeSpecs` with `sp`, `evalOpenTySpec` on `baseClosed` at
`substAndNormalize σ ty` also yields `sp`. -/
theorem evalOpenTySpec_subst_param_some (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env : OpenExecEnv) (σ : List OpenMirTy) (paramSpecs : List TypeLayoutSpec)
    (paramInvs : List (List AllocByte → Prop))
    (hLenEq : paramSpecs.length = σ.length)
    (hMap : ∀ (i : Nat) (ty : OpenMirTy), openListGet? σ i = some ty →
      ∃ sp : TypeLayoutSpec, openListGet? paramSpecs i = some sp ∧
        evalOpenTySpec prog.traitRegistry normFuel
          { env.typeSpecs with paramSpecs := [], paramInvs := [] } ty =
          some sp ∧
        OpenMirTy.isClosed ty = true) :
    let baseClosed : TypeSpecEnv :=
      { env.typeSpecs with paramSpecs := [], paramInvs := [] }
    let assocSpecFn := instAssocSpecs prog.traitRegistry env.typeSpecs σ
    let env' : OpenExecEnv :=
      { env with typeSpecs := (substTypeSpecEnv env.typeSpecs paramSpecs
          paramInvs assocSpecFn) }
    ∀ (ty : OpenMirTy) (sp : TypeLayoutSpec),
      evalOpenTySpec prog.traitRegistry normFuel env'.typeSpecs ty = some sp →
      evalOpenTySpec prog.traitRegistry normFuel baseClosed
        (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ ty) =
        some sp := by
  intro baseClosed assocSpecFn env' ty sp hEval
  have hParam : ∀ i : Nat,
      openListGet? env'.typeSpecs.paramSpecs i =
        (openListGet? σ i).bind (fun rep =>
          evalNormOpenTySpec baseClosed
            (normalizeOpenTyStep prog.traitRegistry rep)) := by
    intro i
    dsimp only [env', substTypeSpecEnv]
    cases hGet : openListGet? σ i with
    | some rep =>
        cases hMap i rep hGet with
        | intro sp hRest =>
            have hSp := hRest.1
            have hEvalRep := hRest.2.1
            unfold evalOpenTySpec at hEvalRep
            rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf rep]
              at hEvalRep
            rw [hSp]
            exact hEvalRep.symm
    | none =>
        have hAux : ∀ (ps : List TypeLayoutSpec) (ts : List OpenMirTy)
            (k : Nat), ps.length = ts.length → openListGet? ts k = none →
            openListGet? ps k = none := by
          intro ps
          induction ps with
          | nil => intro ts k _ _; cases k <;> rfl
          | cons p ps' ih =>
              intro ts k hL hN
              cases ts with
              | nil => cases hL
              | cons t ts' =>
                  cases k with
                  | zero => cases hN
                  | succ j => exact ih ts' j (Nat.succ.inj hL) hN
        exact hAux paramSpecs σ i hLenEq hGet
  have hClosed : ∀ (i : Nat) (rep : OpenMirTy),
      openListGet? σ i = some rep → OpenMirTy.isClosed rep = true := by
    intro i rep hGet
    cases hMap i rep hGet with
    | intro _ hRest => exact hRest.2.2
  have hAssoc : ∀ (s : OpenMirTy) (tr : TraitDefId) (args : List OpenMirTy)
      (idx : AssocItemIdx),
      resolveAssocType prog.traitRegistry
          (normalizeOpenTyStep prog.traitRegistry s) tr
          (normalizeOpenTyStepList prog.traitRegistry args) idx = none →
      env'.typeSpecs.assocSpecs (normalizeOpenTyStep prog.traitRegistry s) tr
          (normalizeOpenTyStepList prog.traitRegistry args) idx =
        evalNormOpenTySpec baseClosed
          (normalizeOpenTyStep prog.traitRegistry
            (.assocProj (OpenMirTy.subst σ s) tr
              (OpenMirTy.substList σ args) idx)) := by
    intro s tr args idx hRes
    dsimp only [env', substTypeSpecEnv, assocSpecFn, instAssocSpecs]
    cases hNoP :
        openMirTyNoParam (normalizeOpenTyStep prog.traitRegistry s) &&
          openMirTyListNoParam
            (normalizeOpenTyStepList prog.traitRegistry args) with
    | true =>
        have hSNoP := openMirTy_subst_noParam σ _ (bool_and_left hNoP)
        have hANoP := openMirTyList_subst_noParam σ _
          (bool_and_right hNoP)
        have hAList :
            normalizeOpenTyStepList prog.traitRegistry
                (OpenMirTy.substList σ args) =
              normalizeOpenTyStepList prog.traitRegistry args := by
          rw [← normalizeOpenTyStepList_subst_idem
            prog.traitRegistry hRegWf σ args, hANoP,
            normalizeOpenTyStepList_idempotent
              prog.traitRegistry hRegWf args]
        dsimp only [normalizeOpenTyStep]
        rw [← normalizeOpenTyStep_subst_idem prog.traitRegistry hRegWf σ s,
          hSNoP, normalizeOpenTyStep_idempotent prog.traitRegistry hRegWf s,
          hAList, hRes]
        rfl
    | false =>
        have hSIdem :
            normalizeOpenTyStep prog.traitRegistry
                (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ
                  (normalizeOpenTyStep prog.traitRegistry s)) =
              normalizeOpenTyStep prog.traitRegistry (OpenMirTy.subst σ s) := by
          dsimp only [OpenMirTy.substAndNormalize]
          rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf _,
            normalizeOpenTyStep_idempotent prog.traitRegistry hRegWf _,
            normalizeOpenTyStep_subst_idem prog.traitRegistry hRegWf σ s]
        have hAMapGen : ∀ ts : List OpenMirTy,
            normalizeOpenTyStepList prog.traitRegistry
                (List.map
                  (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ)
                  (normalizeOpenTyStepList prog.traitRegistry ts)) =
              normalizeOpenTyStepList prog.traitRegistry
                (OpenMirTy.substList σ ts) := by
          intro ts
          induction ts with
          | nil => rfl
          | cons a as ihAs =>
              change normalizeOpenTyStep prog.traitRegistry
                    (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ
                      (normalizeOpenTyStep prog.traitRegistry a)) ::
                  normalizeOpenTyStepList prog.traitRegistry
                    (List.map
                      (OpenMirTy.substAndNormalize prog.traitRegistry normFuel
                        σ)
                      (normalizeOpenTyStepList prog.traitRegistry as)) =
                normalizeOpenTyStep prog.traitRegistry (OpenMirTy.subst σ a) ::
                  normalizeOpenTyStepList prog.traitRegistry
                    (OpenMirTy.substList σ as)
              have hA1 : normalizeOpenTyStep prog.traitRegistry
                  (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ
                    (normalizeOpenTyStep prog.traitRegistry a)) =
                  normalizeOpenTyStep prog.traitRegistry
                    (OpenMirTy.subst σ a) := by
                dsimp only [OpenMirTy.substAndNormalize]
                rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf _,
                  normalizeOpenTyStep_idempotent prog.traitRegistry hRegWf _,
                  normalizeOpenTyStep_subst_idem prog.traitRegistry hRegWf σ a]
              rw [hA1, ihAs]
        have hAMap := hAMapGen args
        unfold evalOpenTySpec
        rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf _]
        apply congrArg (evalNormOpenTySpec baseClosed)
        dsimp only [normalizeOpenTyStep]
        rw [hSIdem, hAMap]
  unfold evalOpenTySpec at hEval
  unfold evalOpenTySpec OpenMirTy.substAndNormalize
  rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf ty] at hEval
  rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf
      (OpenMirTy.subst σ ty),
    normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf
      (normalizeOpenTyStep prog.traitRegistry (OpenMirTy.subst σ ty)),
    normalizeOpenTyStep_idempotent prog.traitRegistry hRegWf
      (OpenMirTy.subst σ ty)]
  exact evalNormOpenTySpec_subst_param_some prog.traitRegistry hRegWf
    env'.typeSpecs baseClosed σ rfl hParam hClosed hAssoc ty sp hEval

/-- Helper: `checkOpenArgsMatch` and `checkOpenVal` agree across `env₁, env₂`
on `openMirTyListNoParam`. -/
theorem checkOpenVal_noParam_congr (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env₁ env₂ : OpenExecEnv)
    (hAdt : env₁.typeSpecs.adtSpecs = env₂.typeSpecs.adtSpecs)
    (hAssoc : ∀ s tr as idx, openMirTyNoParam s = true →
      openMirTyListNoParam as = true →
      env₁.typeSpecs.assocSpecs s tr as idx =
        env₂.typeSpecs.assocSpecs s tr as idx)
    (v : Val) (ty : OpenMirTy) (hNoP : openMirTyNoParam ty = true) :
    checkOpenVal prog env₁ v ty = checkOpenVal prog env₂ v ty := by
  unfold checkOpenVal
  rw [evalOpenTySpec_noParam_congr prog hRegWf env₁ env₂ hAdt hAssoc ty hNoP]

theorem checkOpenArgsMatch_noParam_congr (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env₁ env₂ : OpenExecEnv)
    (hAdt : env₁.typeSpecs.adtSpecs = env₂.typeSpecs.adtSpecs)
    (hAssoc : ∀ s tr as idx, openMirTyNoParam s = true →
      openMirTyListNoParam as = true →
      env₁.typeSpecs.assocSpecs s tr as idx =
        env₂.typeSpecs.assocSpecs s tr as idx) :
    ∀ (vs : List Val) (tys : List OpenMirTy),
      openMirTyListNoParam tys = true →
      checkOpenArgsMatch prog env₁ vs tys = checkOpenArgsMatch prog env₂ vs tys
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | v :: vs, t :: ts, hNoP => by
      dsimp only [openMirTyListNoParam] at hNoP
      unfold checkOpenArgsMatch
      rw [checkOpenVal_noParam_congr prog hRegWf env₁ env₂ hAdt hAssoc v t
          (bool_and_left hNoP),
        checkOpenArgsMatch_noParam_congr prog hRegWf env₁ env₂ hAdt hAssoc vs ts
          (bool_and_right hNoP)]

theorem openLocalsAdmitted_noParam_congr (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env₁ env₂ : OpenExecEnv)
    (hAdt : env₁.typeSpecs.adtSpecs = env₂.typeSpecs.adtSpecs)
    (hAssoc : ∀ s tr as idx, openMirTyNoParam s = true →
      openMirTyListNoParam as = true →
      env₁.typeSpecs.assocSpecs s tr as idx =
        env₂.typeSpecs.assocSpecs s tr as idx) :
    ∀ tys : List OpenMirTy, openMirTyListNoParam tys = true →
      (openLocalsAdmitted prog env₁ tys ↔ openLocalsAdmitted prog env₂ tys)
  | [], _ => Iff.rfl
  | t :: ts, hNoP => by
      dsimp only [openMirTyListNoParam] at hNoP
      unfold openLocalsAdmitted
      rw [evalOpenTySpec_noParam_congr prog hRegWf env₁ env₂ hAdt hAssoc t
          (bool_and_left hNoP)]
      exact ⟨fun ⟨a, b⟩ => ⟨a, (openLocalsAdmitted_noParam_congr prog hRegWf
          env₁ env₂ hAdt hAssoc ts (bool_and_right hNoP)).mp b⟩,
        fun ⟨a, b⟩ => ⟨a, (openLocalsAdmitted_noParam_congr prog hRegWf
          env₁ env₂ hAdt hAssoc ts (bool_and_right hNoP)).mpr b⟩⟩

/-- Invariant that every active frame in `os.frames` points to a body in `prog`
with `openBodyNoParam = true`. -/
def FramesNoParam (prog : OpenProgram) :
    List OpenFrameState → Prop
  | [] => True
  | f :: fs =>
      (∃ b : OpenBody, openListGet? prog.bodies f.defId = some b ∧
        openBodyNoParam b = true) ∧
      FramesNoParam prog fs

/-- Helper unpacking `openBodyNoParam` conjuncts. -/
theorem openBodyNoParam_parts (ob : OpenBody) (h : openBodyNoParam ob = true) :
    openMirTyListNoParam ob.locals = true ∧
    openMirTyListNoParam ob.sig.argTys = true ∧
    openMirTyNoParam ob.sig.retTy = true ∧
    ob.sig.whereClauses.all openWhereNoParam = true ∧
    ob.basicBlocks.all (fun bb =>
      bb.statements.all openStmtNoParam && openTermNoParam bb.terminator) =
      true := by
  unfold openBodyNoParam at h
  exact ⟨bool_and_left (bool_and_left (bool_and_left (bool_and_left h))),
    bool_and_right (bool_and_left (bool_and_left (bool_and_left h))),
    bool_and_right (bool_and_left (bool_and_left h)),
    bool_and_right (bool_and_left h),
    bool_and_right h⟩

theorem openListGet?_openBodyNoParam_local (ob : OpenBody)
    (hNoP : openBodyNoParam ob = true) (lid : Nat) (ty : OpenMirTy)
    (hGet : openListGet? ob.locals lid = some ty) :
    openMirTyNoParam ty = true := by
  rw [← getElem?_eq_openListGet?] at hGet
  have hL := (openBodyNoParam_parts ob hNoP).1
  have hAll : ∀ (xs : List OpenMirTy) (i : Nat) (t : OpenMirTy),
      openMirTyListNoParam xs = true →
      Trusted.MirSemantics.getElem? xs i = some t →
      openMirTyNoParam t = true := by
    intro xs
    induction xs with
    | nil => intro _ _ _ h; cases h
    | cons x xs ih =>
        intro i t hList hEl
        dsimp only [openMirTyListNoParam] at hList
        cases i with
        | zero => cases hEl; exact bool_and_left hList
        | succ j => exact ih j t (bool_and_right hList) hEl
  exact hAll ob.locals lid ty hL hGet

theorem openMirTyListNoParam_drop_take (xs : List OpenMirTy) (k : Nat)
    (hL : openMirTyListNoParam xs = true) :
    openMirTyListNoParam ((xs.drop 1).take k) = true := by
  have hDrop : ∀ (ys : List OpenMirTy) (m : Nat),
      openMirTyListNoParam ys = true →
      openMirTyListNoParam (ys.drop m) = true := by
    intro ys
    induction ys with
    | nil => intro m _; cases m <;> rfl
    | cons y ys ih =>
        intro m hYs
        cases m with
        | zero => exact hYs
        | succ j => exact ih j (bool_and_right hYs)
  have hTake : ∀ (ys : List OpenMirTy) (m : Nat),
      openMirTyListNoParam ys = true →
      openMirTyListNoParam (ys.take m) = true := by
    intro ys
    induction ys with
    | nil => intro m _; cases m <;> rfl
    | cons y ys ih =>
        intro m hYs
        cases m with
        | zero => rfl
        | succ j =>
            dsimp only [List.take, openMirTyListNoParam]
            exact bool_and_eq_true (bool_and_left hYs)
              (ih j (bool_and_right hYs))
  exact hTake _ k (hDrop xs 1 hL)

theorem initOpenLocals_noParam_congr (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env₁ env₂ : OpenExecEnv)
    (hAdt : env₁.typeSpecs.adtSpecs = env₂.typeSpecs.adtSpecs)
    (hAssoc : ∀ s tr as idx, openMirTyNoParam s = true →
      openMirTyListNoParam as = true →
      env₁.typeSpecs.assocSpecs s tr as idx =
        env₂.typeSpecs.assocSpecs s tr as idx)
    (ob : OpenBody) (hNoP : openBodyNoParam ob = true) (args : List Val) :
    initOpenLocals prog env₁ ob args = initOpenLocals prog env₂ ob args := by
  unfold initOpenLocals
  have hParamNoP := openMirTyListNoParam_drop_take ob.locals ob.argumentCount
    (openBodyNoParam_parts ob hNoP).1
  have hChk := checkOpenArgsMatch_noParam_congr prog hRegWf env₁ env₂ hAdt hAssoc
    args ((ob.locals.drop 1).take ob.argumentCount) hParamNoP
  dsimp only
  rw [hChk]

/-- For any `openBodyNoParam` execution (`env₁` vs `env₂`), `openInitState` is
identical. -/
theorem openInitState_noParam_congr (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env₁ env₂ : OpenExecEnv)
    (hAdt : env₁.typeSpecs.adtSpecs = env₂.typeSpecs.adtSpecs)
    (hAssoc : ∀ s tr as idx, openMirTyNoParam s = true →
      openMirTyListNoParam as = true →
      env₁.typeSpecs.assocSpecs s tr as idx =
        env₂.typeSpecs.assocSpecs s tr as idx)
    (ob : OpenBody) (hGet : openListGet? prog.bodies prog.entryDefId = some ob)
    (hNoP : openBodyNoParam ob = true) (q : Query) :
    openInitState prog env₁ q = openInitState prog env₂ q := by
  unfold openInitState openInitStateAux
  cases OpenProgram.toDay1? prog with
  | some _ => rfl
  | none =>
      dsimp only
      cases hMem : (!q.callerMem.allocations.isEmpty) with
      | true => rfl
      | false =>
          rw [hGet]
          dsimp only
          cases hHdr : (!Nat.beq prog.pointerWidthBits 64 ||
              !Nat.beq prog.mirProfileVersion 1 ||
              ob.basicBlocks.isEmpty ||
              !Nat.blt ob.argumentCount ob.locals.length) with
          | true => rfl
          | false =>
              rw [initOpenLocals_noParam_congr prog hRegWf env₁ env₂ hAdt hAssoc
                ob hNoP q.args]

/-- Helper proving `evalOpenOperand` agrees across `env₁`, `env₂`. -/
theorem evalOpenOperand_noParam_congr (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env₁ env₂ : OpenExecEnv)
    (hAdt : env₁.typeSpecs.adtSpecs = env₂.typeSpecs.adtSpecs)
    (hAssoc : ∀ s tr as idx, openMirTyNoParam s = true →
      openMirTyListNoParam as = true →
      env₁.typeSpecs.assocSpecs s tr as idx =
        env₂.typeSpecs.assocSpecs s tr as idx)
    (ob : OpenBody) (frame : OpenFrameState) (op : OpenOperand)
    (hOp : openOperandNoParam op = true) :
    evalOpenOperand prog env₁ ob frame op =
      evalOpenOperand prog env₂ ob frame op := by
  cases op with
  | copy _ | move _ => rfl
  | constant c =>
      dsimp only [openOperandNoParam] at hOp
      cases hClosed : OpenMirTy.toClosedMirTy? c.ty with
      | some mty =>
          dsimp only [evalOpenOperand]
          rw [hClosed]
      | none =>
          cases hLit : c.lit with
          | scalar _ | rodataBytes _ | rodataRef _ _ _ _ =>
              dsimp only [evalOpenOperand]
              rw [hClosed, hLit]
          | zeroSized =>
              dsimp only [evalOpenOperand]
              rw [hClosed, hLit]
              dsimp only
              rw [evalOpenTySpec_noParam_congr prog hRegWf env₁ env₂ hAdt
                hAssoc c.ty hOp]

theorem evalOpenOperands_noParam_congr (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env₁ env₂ : OpenExecEnv)
    (hAdt : env₁.typeSpecs.adtSpecs = env₂.typeSpecs.adtSpecs)
    (hAssoc : ∀ s tr as idx, openMirTyNoParam s = true →
      openMirTyListNoParam as = true →
      env₁.typeSpecs.assocSpecs s tr as idx =
        env₂.typeSpecs.assocSpecs s tr as idx)
    (ob : OpenBody) (frame : OpenFrameState) :
    ∀ ops : List OpenOperand, ops.all openOperandNoParam = true →
      evalOpenOperands prog env₁ ob frame ops =
        evalOpenOperands prog env₂ ob frame ops
  | [], _ => rfl
  | op :: ops, hAll => by
      simp only [List.all_cons] at hAll
      have h1 := evalOpenOperand_noParam_congr prog hRegWf env₁ env₂ hAdt hAssoc
        ob frame op (bool_and_left hAll)
      unfold evalOpenOperands
      rw [h1]
      cases evalOpenOperand prog env₂ ob frame op with
      | error _ => rfl
      | ok res =>
          dsimp only
          rw [evalOpenOperands_noParam_congr prog hRegWf env₁ env₂ hAdt hAssoc ob
            res.2.2 ops (bool_and_right hAll)]

universe u v

private theorem if_true_eq {α : Sort u} {inst : Decidable (true = true)}
    (a b : α) :
    @ite α (true = true) inst a b = a := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hF => exact absurd rfl hF

private theorem if_false_eq {α : Sort u} {inst : Decidable (false = true)}
    (a b : α) :
    @ite α (false = true) inst a b = b := by
  cases inst with
  | isTrue hT => cases hT
  | isFalse _ => rfl

private theorem if_not_false_eq {α : Sort u}
    {inst : Decidable ((!false) = true)} (a b : α) :
    @ite α ((!false) = true) inst a b = a := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hF => exact absurd rfl hF

private theorem if_not_true_eq {α : Sort u}
    {inst : Decidable ((!true) = true)} (a b : α) :
    @ite α ((!true) = true) inst a b = b := by
  cases inst with
  | isTrue hT => cases hT
  | isFalse _ => rfl

private theorem prop_ite_true {inst : Decidable (true = true)} {P Q : Prop} :
    @ite Prop (true = true) inst P Q = P := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hF => exact absurd rfl hF

private theorem prop_ite_false {inst : Decidable (false = true)} {P Q : Prop} :
    @ite Prop (false = true) inst P Q = Q := by
  cases inst with
  | isTrue hT => cases hT
  | isFalse _ => rfl

private theorem ite_cond_true {α : Sort u} {c : Bool}
    {inst : Decidable (c = true)} (hc : c = true) (a b : α) :
    @ite α (c = true) inst a b = a := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hF => exact absurd hc hF

private theorem ite_cond_false {α : Sort u} {c : Bool}
    {inst : Decidable (c = true)} (hc : c = false) (a b : α) :
    @ite α (c = true) inst a b = b := by
  cases inst with
  | isTrue hT => rw [hc] at hT; cases hT
  | isFalse _ => rfl

private theorem ite_not_true {α : Sort u} {b : Bool}
    {inst : Decidable ((!b) = true)} (hb : b = true) (x y : α) :
    @ite α ((!b) = true) inst x y = y := by
  cases inst with
  | isTrue hT => rw [hb] at hT; cases hT
  | isFalse _ => rfl

private theorem ite_not_false {α : Sort u} {b : Bool}
    {inst : Decidable ((!b) = true)} (hb : b = false) (x y : α) :
    @ite α ((!b) = true) inst x y = x := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hF => exact absurd (by rw [hb]; rfl) hF

private theorem nat_beq_succ_zero (j : Nat) : Nat.beq (j + 1) 0 = false := rfl

private theorem nat_beq_self : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => nat_beq_self n

private theorem prop_ite_true_mp {b : Bool} {inst : Decidable (b = true)}
    {P Q : Prop} (hb : b = true) (h : @ite Prop (b = true) inst P Q) : P := by
  cases inst with
  | isTrue _ => exact h
  | isFalse hF => exact absurd hb hF

private theorem prop_ite_false_mp {b : Bool} {inst : Decidable (b = true)}
    {P Q : Prop} (hb : b = false) (h : @ite Prop (b = true) inst P Q) : Q := by
  cases inst with
  | isTrue hT => rw [hb] at hT; cases hT
  | isFalse _ => exact h

private theorem prop_ite_iff {b : Bool} {inst₁ inst₂ : Decidable (b = true)}
    {P₁ P₂ Q₁ Q₂ : Prop} (hP : b = true → (P₁ ↔ P₂))
    (hQ : b = false → (Q₁ ↔ Q₂)) :
    @ite Prop (b = true) inst₁ P₁ Q₁ ↔
      @ite Prop (b = true) inst₂ P₂ Q₂ := by
  cases b with
  | true =>
      rw [ite_eq_left_of_eq_true P₁ Q₁ (eq_true rfl),
        ite_eq_left_of_eq_true P₂ Q₂ (eq_true rfl)]
      exact hP rfl
  | false =>
      have hF : (false = true) = False := eq_false (fun h => by cases h)
      rw [ite_eq_right_of_eq_false P₁ Q₁ hF,
        ite_eq_right_of_eq_false P₂ Q₂ hF]
      exact hQ rfl

private theorem prop_ite_congr_same {b : Bool} {inst₁ inst₂ : Decidable (b = true)}
    {P Q₁ Q₂ : Prop} (hQ : b = false → (Q₁ ↔ Q₂)) :
    @ite Prop (b = true) inst₁ P Q₁ ↔ @ite Prop (b = true) inst₂ P Q₂ :=
  prop_ite_iff (fun _ => Iff.rfl) hQ

private theorem prop_ite_elim_step {b : Bool} {inst : Decidable (b = true)}
    {Out : Type} {k : FaultKind} {s' : OpenState} {Q : Prop}
    (h : @ite Prop (b = true) inst
        (@StepResult.step OpenState Out s' =
          @StepResult.fault OpenState Out k) Q) :
    b = false ∧ Q := by
  cases b with
  | true =>
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)] at h
      cases h
  | false =>
      rw [ite_eq_right_of_eq_false _ _ (eq_false (fun hc => by cases hc))] at h
      exact ⟨rfl, h⟩

private theorem prop_ite_step_rhs {P : Prop} {inst : Decidable P}
    {Out : Type} {k : FaultKind} {s' : OpenState} {Q : Prop}
    (h : @ite Prop P inst
        (@StepResult.step OpenState Out s' =
          @StepResult.fault OpenState Out k) Q) : Q := by
  cases inst with
  | isTrue _ => cases h
  | isFalse _ => exact h

/-- `prop_ite_step_rhs` for a hypothesis still in the goal. Use it via
`revert h; refine prop_ite_step_rhs_imp ?_; intro h` when the `ite`
condition is expensive to reduce: elaborating `prop_ite_step_rhs h` puts
the type of `h` in weak head normal form, which evaluates the condition,
whereas unifying against the goal does not. -/
private theorem prop_ite_step_rhs_imp {P : Prop} {inst : Decidable P}
    {Out : Type} {k : FaultKind} {s' : OpenState} {Q G : Prop}
    (hQ : Q → G) :
    @ite Prop P inst
        (@StepResult.step OpenState Out s' =
          @StepResult.fault OpenState Out k) Q → G :=
  fun h => hQ (prop_ite_step_rhs h)

private theorem except_ite_ok {α : Type} {b : Bool}
    {inst : Decidable (b = true)} {k : FaultKind} {x y : α}
    (h : @ite (Except FaultKind α) (b = true) inst (Except.ok x)
        (Except.error k) = Except.ok y) :
    x = y := by
  cases b with
  | true =>
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)] at h
      cases h; rfl
  | false =>
      rw [ite_eq_right_of_eq_false _ _ (eq_false (fun hc => by cases hc))] at h
      cases h

private theorem binop_match_congr
    (c1 c2 c3 : Option MirTy) (eb : Except FaultKind Val)
    (wf wf' : Val → StepResult OpenState TerminalOut)
    (hWf : ∀ resV, wf resV = wf' resV) :
    (match c1, c2, c3, eb with
    | some ml, some mr, some mDst, .ok resV =>
        if !isPrimitiveReadableTy ml || !isPrimitiveReadableTy mr ||
           !checkVal resV mDst then StepResult.fault FaultKind.unsupported
        else wf resV
    | _, _, _, .error k => StepResult.fault k
    | _, _, _, _ => StepResult.fault FaultKind.unsupported) =
    (match c1, c2, c3, eb with
    | some ml, some mr, some mDst, .ok resV =>
        if !isPrimitiveReadableTy ml || !isPrimitiveReadableTy mr ||
           !checkVal resV mDst then StepResult.fault FaultKind.unsupported
        else wf' resV
    | _, _, _, .error k => StepResult.fault k
    | _, _, _, _ => StepResult.fault FaultKind.unsupported) := by
  cases eb with
  | error k => cases c1 <;> cases c2 <;> cases c3 <;> rfl
  | ok resV =>
      cases c1 with
      | none => rfl
      | some ml =>
          cases c2 with
          | none => rfl
          | some mr =>
              cases c3 with
              | none => rfl
              | some mDst =>
                  dsimp only
                  cases hR : (!isPrimitiveReadableTy ml ||
                    !isPrimitiveReadableTy mr || !checkVal resV mDst) with
                  | true => rw [if_true_eq, if_true_eq]
                  | false => rw [if_false_eq, if_false_eq, hWf resV]

private theorem unop_match_congr
    (c1 c2 : Option MirTy) (eu : Except FaultKind Val)
    (wf wf' : Val → StepResult OpenState TerminalOut)
    (hWf : ∀ resV, wf resV = wf' resV) :
    (match c1, c2, eu with
    | some mSrc, some mDst, .ok resV =>
        if !isPrimitiveReadableTy mSrc || !checkVal resV mDst
        then StepResult.fault FaultKind.unsupported
        else wf resV
    | _, _, .error k => StepResult.fault k
    | _, _, _ => StepResult.fault FaultKind.unsupported) =
    (match c1, c2, eu with
    | some mSrc, some mDst, .ok resV =>
        if !isPrimitiveReadableTy mSrc || !checkVal resV mDst
        then StepResult.fault FaultKind.unsupported
        else wf' resV
    | _, _, .error k => StepResult.fault k
    | _, _, _ => StepResult.fault FaultKind.unsupported) := by
  cases eu with
  | error k => cases c1 <;> cases c2 <;> rfl
  | ok resV =>
      cases c1 with
      | none => rfl
      | some mSrc =>
          cases c2 with
          | none => rfl
          | some mDst =>
              dsimp only
              cases hR :
                  (!isPrimitiveReadableTy mSrc || !checkVal resV mDst) with
              | true => rw [if_true_eq, if_true_eq]
              | false => rw [if_false_eq, if_false_eq, hWf resV]

private theorem binop_match_step
    (c1 c2 c3 : Option MirTy) (eb : Except FaultKind Val)
    (wf : Val → StepResult OpenState TerminalOut) {s' : OpenState}
    (h : (match c1, c2, c3, eb with
      | some ml, some mr, some mDst, .ok resV =>
          if !isPrimitiveReadableTy ml || !isPrimitiveReadableTy mr ||
             !checkVal resV mDst then StepResult.fault FaultKind.unsupported
          else wf resV
      | _, _, _, .error k => StepResult.fault k
      | _, _, _, _ => StepResult.fault FaultKind.unsupported) = .step s') :
    ∃ resV, eb = .ok resV ∧ wf resV = .step s' := by
  cases eb with
  | error k => cases c1 <;> cases c2 <;> cases c3 <;> cases h
  | ok resV =>
      cases c1 with
      | none => cases h
      | some ml =>
          cases c2 with
          | none => cases h
          | some mr =>
              cases c3 with
              | none => cases h
              | some mDst =>
                  dsimp only at h
                  cases hR : (!isPrimitiveReadableTy ml ||
                    !isPrimitiveReadableTy mr || !checkVal resV mDst) with
                  | true => rw [hR, if_true_eq] at h; cases h
                  | false => rw [hR, if_false_eq] at h; exact ⟨resV, rfl, h⟩

private theorem unop_match_step
    (c1 c2 : Option MirTy) (eu : Except FaultKind Val)
    (wf : Val → StepResult OpenState TerminalOut) {s' : OpenState}
    (h : (match c1, c2, eu with
      | some mSrc, some mDst, .ok resV =>
          if !isPrimitiveReadableTy mSrc || !checkVal resV mDst
          then StepResult.fault FaultKind.unsupported
          else wf resV
      | _, _, .error k => StepResult.fault k
      | _, _, _ => StepResult.fault FaultKind.unsupported) = .step s') :
    ∃ resV, eu = .ok resV ∧ wf resV = .step s' := by
  cases eu with
  | error k => cases c1 <;> cases c2 <;> cases h
  | ok resV =>
      cases c1 with
      | none => cases h
      | some mSrc =>
          cases c2 with
          | none => cases h
          | some mDst =>
              dsimp only at h
              cases hR :
                  (!isPrimitiveReadableTy mSrc || !checkVal resV mDst) with
              | true => rw [hR, if_true_eq] at h; cases h
              | false => rw [hR, if_false_eq] at h; exact ⟨resV, rfl, h⟩

private theorem prop_and_congr {A₁ A₂ B₁ B₂ : Prop}
    (hA : A₁ ↔ A₂) (hB : B₁ ↔ B₂) :
    (A₁ ∧ B₁) ↔ (A₂ ∧ B₂) :=
  ⟨fun h => ⟨hA.mp h.1, hB.mp h.2⟩, fun h => ⟨hA.mpr h.1, hB.mpr h.2⟩⟩

private theorem prop_or_congr {A₁ A₂ B₁ B₂ : Prop}
    (hA : A₁ ↔ A₂) (hB : B₁ ↔ B₂) :
    (A₁ ∨ B₁) ↔ (A₂ ∨ B₂) :=
  ⟨fun h => h.elim (fun a => Or.inl (hA.mp a)) (fun b => Or.inr (hB.mp b)),
   fun h => h.elim (fun a => Or.inl (hA.mpr a)) (fun b => Or.inr (hB.mpr b))⟩

private theorem prop_exists_congr {α : Sort u} {P Q : α → Prop}
    (h : ∀ a, P a ↔ Q a) : (∃ a, P a) ↔ (∃ a, Q a) :=
  ⟨fun ⟨a, ha⟩ => ⟨a, (h a).mp ha⟩, fun ⟨a, ha⟩ => ⟨a, (h a).mpr ha⟩⟩

private theorem cast_match_congr
    (eo : Except FaultKind (Val × OpenMirTy × OpenFrameState))
    (cc : Option MirTy)
    (wf wf' : OpenFrameState → Val → StepResult OpenState TerminalOut)
    (hWf : ∀ f₁ resV, wf f₁ resV = wf' f₁ resV) :
    (match eo, cc with
    | .ok (v, srcTy, f₁), some mCast =>
        match OpenMirTy.toClosedMirTy? srcTy with
        | some mSrc =>
            if !isIntLikeTy mSrc then StepResult.fault FaultKind.unsupported
            else
              match evalIntToIntCast v mCast with
              | .error k => StepResult.fault k
              | .ok resV => wf f₁ resV
        | none => StepResult.fault FaultKind.unsupported
    | .error k, _ => StepResult.fault k
    | _, none => StepResult.fault FaultKind.unsupported) =
    (match eo, cc with
    | .ok (v, srcTy, f₁), some mCast =>
        match OpenMirTy.toClosedMirTy? srcTy with
        | some mSrc =>
            if !isIntLikeTy mSrc then StepResult.fault FaultKind.unsupported
            else
              match evalIntToIntCast v mCast with
              | .error k => StepResult.fault k
              | .ok resV => wf' f₁ resV
        | none => StepResult.fault FaultKind.unsupported
    | .error k, _ => StepResult.fault k
    | _, none => StepResult.fault FaultKind.unsupported) := by
  cases eo with
  | error k => cases cc <;> rfl
  | ok r₁ =>
      cases cc with
      | none => rfl
      | some mCast =>
          dsimp only
          cases OpenMirTy.toClosedMirTy? r₁.2.1 with
          | none => rfl
          | some mSrc =>
              dsimp only
              cases hInt : (!isIntLikeTy mSrc) with
              | true => rw [if_true_eq, if_true_eq]
              | false =>
                  rw [if_false_eq, if_false_eq]
                  cases evalIntToIntCast r₁.1 mCast with
                  | error _ => rfl
                  | ok resV => exact hWf r₁.2.2 resV

private theorem map_nil' {α : Type u} {β : Type v} (f : α → β) :
    List.map f [] = [] :=
  rfl

private theorem map_cons' {α : Type u} {β : Type v} (f : α → β) (x : α)
    (xs : List α) :
    List.map f (x :: xs) = f x :: List.map f xs :=
  rfl

private theorem ite_err_ok {α : Type} {k : FaultKind} {b : Bool}
    {e : Except FaultKind α} {v : α}
    (h : (if b = true then Except.error k else e) = .ok v) :
    b = false ∧ e = .ok v := by
  cases b with
  | false => exact ⟨rfl, h⟩
  | true => cases h

private theorem ite_fault_step {α β : Type} {k : FaultKind} {b : Bool}
    {s' : α} {s2 : StepResult α β}
    (h : (if b = true then StepResult.fault k else s2) = .step s') :
    s2 = .step s' := by
  cases b with
  | false => exact h
  | true => cases h

private theorem ite_step_fault_false {α β : Type} {k : FaultKind} {b : Bool}
    {s' : α} {s2 : StepResult α β}
    (h : (if b = true then s2 else StepResult.fault k) = .step s') :
    s2 = .step s' := by
  cases b with
  | true => exact h
  | false => cases h

theorem writeOpenPlace_noParam_congr (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env₁ env₂ : OpenExecEnv)
    (hAdt : env₁.typeSpecs.adtSpecs = env₂.typeSpecs.adtSpecs)
    (hAssoc : ∀ s tr as idx, openMirTyNoParam s = true →
      openMirTyListNoParam as = true →
      env₁.typeSpecs.assocSpecs s tr as idx =
        env₂.typeSpecs.assocSpecs s tr as idx)
    (ob : OpenBody) (hNoP : openBodyNoParam ob = true)
    (frame : OpenFrameState) (dst : OpenPlace) (v : Val) :
    writeOpenPlace prog env₁ ob frame dst v =
      writeOpenPlace prog env₂ ob frame dst v := by
  cases hEmp : dst.projection.isEmpty with
  | false =>
      dsimp only [writeOpenPlace]
      rw [hEmp, if_not_false_eq]
      rw [if_not_false_eq]
  | true =>
      dsimp only [writeOpenPlace]
      rw [hEmp, if_not_true_eq]
      rw [if_not_true_eq]
      cases hGet : openListGet? ob.locals dst.localId with
      | none => rfl
      | some dstTy =>
          have hTyNoP := openListGet?_openBodyNoParam_local ob hNoP dst.localId
            dstTy hGet
          have hChk := checkOpenVal_noParam_congr prog hRegWf env₁ env₂ hAdt
            hAssoc v dstTy hTyNoP
          dsimp only
          rw [hChk]

theorem resolveTraitAssocSpecsAux_noParam_congr (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env₁ env₂ : OpenExecEnv)
    (hAdt : env₁.typeSpecs.adtSpecs = env₂.typeSpecs.adtSpecs)
    (hAssoc : ∀ s tr as idx, openMirTyNoParam s = true →
      openMirTyListNoParam as = true →
      env₁.typeSpecs.assocSpecs s tr as idx =
        env₂.typeSpecs.assocSpecs s tr as idx)
    (selfTy : OpenMirTy) (tr : TraitDefId) (args : List OpenMirTy)
    (hS : openMirTyNoParam selfTy = true)
    (hA : openMirTyListNoParam args = true) :
    ∀ idx rem : Nat,
      resolveTraitAssocSpecsAux prog env₁ selfTy tr args idx rem =
        resolveTraitAssocSpecsAux prog env₂ selfTy tr args idx rem
  | _, 0 => rfl
  | idx, rem + 1 => by
      unfold resolveTraitAssocSpecsAux
      have hP : openMirTyNoParam (.assocProj selfTy tr args idx) = true :=
        bool_and_eq_true hS hA
      rw [evalOpenTySpec_noParam_congr prog hRegWf env₁ env₂ hAdt hAssoc _ hP,
        resolveTraitAssocSpecsAux_noParam_congr prog hRegWf env₁ env₂ hAdt hAssoc
          selfTy tr args hS hA (idx + 1) rem]

/-- Helper for `openEvalDetStep_noParam_congr` on `.assign`. -/
theorem openEvalDetStep_assign_noParam_congr (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env₁ env₂ : OpenExecEnv)
    (hAdt : env₁.typeSpecs.adtSpecs = env₂.typeSpecs.adtSpecs)
    (hAssoc : ∀ s tr as idx, openMirTyNoParam s = true →
      openMirTyListNoParam as = true →
      env₁.typeSpecs.assocSpecs s tr as idx =
        env₂.typeSpecs.assocSpecs s tr as idx)
    (s : OpenState) (ob : OpenBody) (hNoP : openBodyNoParam ob = true)
    (frame : OpenFrameState) (restFrames : List OpenFrameState)
    (dst : OpenPlace) (rv : OpenRvalue) :
    openRvalueNoParam rv = true →
    ((if !dst.projection.isEmpty then .fault .unsupported
      else match openListGet? ob.locals dst.localId with
      | none => .fault .unsupported
      | some dstTy =>
          let dstN := normalizeOpenTy prog.traitRegistry normFuel dstTy
          match rv with
          | .use op =>
              match evalOpenOperand prog env₁ ob frame op with
              | .error k => .fault k
              | .ok (v, srcTy, f₁) =>
                  let srcN := normalizeOpenTy prog.traitRegistry normFuel srcTy
                  if !OpenMirTy.beq srcN dstN then .fault .unsupported
                  else match writeOpenPlace prog env₁ ob f₁ dst v with
                    | .error k => .fault k
                    | .ok f₂ => .step { s with frames :=
                        { f₂ with stmtIdx := frame.stmtIdx + 1 } :: restFrames }
          | .binaryOp op lhs rhs =>
              match evalOpenOperand prog env₁ ob frame lhs with
              | .error k => .fault k
              | .ok (vl, srcL, f₁) =>
                  match evalOpenOperand prog env₁ ob f₁ rhs with
                  | .error k => .fault k
                  | .ok (vr, srcR, f₂) =>
                      match OpenMirTy.toClosedMirTy? srcL,
                            OpenMirTy.toClosedMirTy? srcR,
                            OpenMirTy.toClosedMirTy? dstN,
                            evalBinOp op vl vr with
                      | some ml, some mr, some mDst, .ok resV =>
                          if !isPrimitiveReadableTy ml ||
                             !isPrimitiveReadableTy mr || !checkVal resV mDst
                          then .fault .unsupported
                          else match writeOpenPlace prog env₁ ob f₂ dst resV with
                            | .error k => .fault k
                            | .ok f₃ => .step { s with frames :=
                                { f₃ with stmtIdx := frame.stmtIdx + 1 } ::
                                  restFrames }
                      | _, _, _, .error k => .fault k
                      | _, _, _, _ => .fault .unsupported
          | .unaryOp op opnd =>
              match evalOpenOperand prog env₁ ob frame opnd with
              | .error k => .fault k
              | .ok (v, srcTy, f₁) =>
                  match OpenMirTy.toClosedMirTy? srcTy,
                        OpenMirTy.toClosedMirTy? dstN, evalUnOp op v with
                  | some mSrc, some mDst, .ok resV =>
                      if !isPrimitiveReadableTy mSrc || !checkVal resV mDst
                      then .fault .unsupported
                      else match writeOpenPlace prog env₁ ob f₁ dst resV with
                        | .error k => .fault k
                        | .ok f₂ => .step { s with frames :=
                            { f₂ with stmtIdx := frame.stmtIdx + 1 } ::
                              restFrames }
                  | _, _, .error k => .fault k
                  | _, _, _ => .fault .unsupported
          | .cast .intToInt opnd castTy =>
              let castN := normalizeOpenTy prog.traitRegistry normFuel castTy
              if !OpenMirTy.beq castN dstN then .fault .unsupported
              else match evalOpenOperand prog env₁ ob frame opnd,
                         OpenMirTy.toClosedMirTy? castN with
                | .ok (v, srcTy, f₁), some mCast =>
                    match OpenMirTy.toClosedMirTy? srcTy with
                    | some mSrc =>
                        if !isIntLikeTy mSrc then .fault .unsupported
                        else match evalIntToIntCast v mCast with
                          | .error k => .fault k
                          | .ok resV =>
                              match writeOpenPlace prog env₁ ob f₁ dst resV with
                              | .error k => .fault k
                              | .ok f₂ => .step { s with frames :=
                                  { f₂ with stmtIdx := frame.stmtIdx + 1 } ::
                                    restFrames }
                    | none => .fault .unsupported
                | .error k, _ => .fault k
                | _, none => .fault .unsupported
          | _ => .fault .unsupported : StepResult OpenState TerminalOut)) =
      ((if !dst.projection.isEmpty then .fault .unsupported
      else match openListGet? ob.locals dst.localId with
      | none => .fault .unsupported
      | some dstTy =>
          let dstN := normalizeOpenTy prog.traitRegistry normFuel dstTy
          match rv with
          | .use op =>
              match evalOpenOperand prog env₂ ob frame op with
              | .error k => .fault k
              | .ok (v, srcTy, f₁) =>
                  let srcN := normalizeOpenTy prog.traitRegistry normFuel srcTy
                  if !OpenMirTy.beq srcN dstN then .fault .unsupported
                  else match writeOpenPlace prog env₂ ob f₁ dst v with
                    | .error k => .fault k
                    | .ok f₂ => .step { s with frames :=
                        { f₂ with stmtIdx := frame.stmtIdx + 1 } :: restFrames }
          | .binaryOp op lhs rhs =>
              match evalOpenOperand prog env₂ ob frame lhs with
              | .error k => .fault k
              | .ok (vl, srcL, f₁) =>
                  match evalOpenOperand prog env₂ ob f₁ rhs with
                  | .error k => .fault k
                  | .ok (vr, srcR, f₂) =>
                      match OpenMirTy.toClosedMirTy? srcL,
                            OpenMirTy.toClosedMirTy? srcR,
                            OpenMirTy.toClosedMirTy? dstN,
                            evalBinOp op vl vr with
                      | some ml, some mr, some mDst, .ok resV =>
                          if !isPrimitiveReadableTy ml ||
                             !isPrimitiveReadableTy mr || !checkVal resV mDst
                          then .fault .unsupported
                          else match writeOpenPlace prog env₂ ob f₂ dst resV with
                            | .error k => .fault k
                            | .ok f₃ => .step { s with frames :=
                                { f₃ with stmtIdx := frame.stmtIdx + 1 } ::
                                  restFrames }
                      | _, _, _, .error k => .fault k
                      | _, _, _, _ => .fault .unsupported
          | .unaryOp op opnd =>
              match evalOpenOperand prog env₂ ob frame opnd with
              | .error k => .fault k
              | .ok (v, srcTy, f₁) =>
                  match OpenMirTy.toClosedMirTy? srcTy,
                        OpenMirTy.toClosedMirTy? dstN, evalUnOp op v with
                  | some mSrc, some mDst, .ok resV =>
                      if !isPrimitiveReadableTy mSrc || !checkVal resV mDst
                      then .fault .unsupported
                      else match writeOpenPlace prog env₂ ob f₁ dst resV with
                        | .error k => .fault k
                        | .ok f₂ => .step { s with frames :=
                            { f₂ with stmtIdx := frame.stmtIdx + 1 } ::
                              restFrames }
                  | _, _, .error k => .fault k
                  | _, _, _ => .fault .unsupported
          | .cast .intToInt opnd castTy =>
              let castN := normalizeOpenTy prog.traitRegistry normFuel castTy
              if !OpenMirTy.beq castN dstN then .fault .unsupported
              else match evalOpenOperand prog env₂ ob frame opnd,
                         OpenMirTy.toClosedMirTy? castN with
                | .ok (v, srcTy, f₁), some mCast =>
                    match OpenMirTy.toClosedMirTy? srcTy with
                    | some mSrc =>
                        if !isIntLikeTy mSrc then .fault .unsupported
                        else match evalIntToIntCast v mCast with
                          | .error k => .fault k
                          | .ok resV =>
                              match writeOpenPlace prog env₂ ob f₁ dst resV with
                              | .error k => .fault k
                              | .ok f₂ => .step { s with frames :=
                                  { f₂ with stmtIdx := frame.stmtIdx + 1 } ::
                                    restFrames }
                    | none => .fault .unsupported
                | .error k, _ => .fault k
                | _, none => .fault .unsupported
          | _ => .fault .unsupported : StepResult OpenState TerminalOut)) := by
  intro hRv
  cases hEmp : dst.projection.isEmpty with
  | false =>
      dsimp only
      rw [if_not_false_eq]
      rw [if_not_false_eq]
  | true =>
      dsimp only
      rw [if_not_true_eq]
      rw [if_not_true_eq]
      cases hLoc : openListGet? ob.locals dst.localId with
      | none => rfl
      | some dstTy =>
          dsimp only
          cases rv with
          | discriminant _ | ref _ _ | addressOf _ _ | aggregateTuple _
          | unsupported => rfl
          | «use» op =>
              dsimp only
              dsimp only [openRvalueNoParam] at hRv
              have hOp := evalOpenOperand_noParam_congr prog hRegWf env₁ env₂
                hAdt hAssoc ob frame op hRv
              rw [hOp]
              cases evalOpenOperand prog env₂ ob frame op with
              | error _ => rfl
              | ok r =>
                  dsimp only
                  cases hGuard : (!OpenMirTy.beq
                      (normalizeOpenTy prog.traitRegistry normFuel r.2.1)
                      (normalizeOpenTy prog.traitRegistry normFuel dstTy)) with
                  | true =>
                      rw [if_true_eq]
                      rw [if_true_eq]
                  | false =>
                      rw [if_false_eq]
                      rw [if_false_eq]
                      rw [writeOpenPlace_noParam_congr prog hRegWf env₁ env₂
                        hAdt hAssoc ob hNoP r.2.2 dst r.1]
          | binaryOp op lhs rhs =>
              dsimp only
              dsimp only [openRvalueNoParam] at hRv
              have hL := evalOpenOperand_noParam_congr prog hRegWf env₁ env₂
                hAdt hAssoc ob frame lhs (bool_and_left hRv)
              rw [hL]
              cases evalOpenOperand prog env₂ ob frame lhs with
              | error _ => rfl
              | ok r₁ =>
                  dsimp only
                  have hR := evalOpenOperand_noParam_congr prog hRegWf env₁ env₂
                    hAdt hAssoc ob r₁.2.2 rhs (bool_and_right hRv)
                  rw [hR]
                  cases evalOpenOperand prog env₂ ob r₁.2.2 rhs with
                  | error _ => rfl
                  | ok r₂ =>
                      dsimp only
                      refine binop_match_congr _ _ _ _ _ _ (fun resV => ?_)
                      rw [writeOpenPlace_noParam_congr prog hRegWf env₁ env₂
                        hAdt hAssoc ob hNoP r₂.2.2 dst resV]
          | unaryOp op opnd =>
              dsimp only
              dsimp only [openRvalueNoParam] at hRv
              have hOp := evalOpenOperand_noParam_congr prog hRegWf env₁ env₂
                hAdt hAssoc ob frame opnd hRv
              rw [hOp]
              cases evalOpenOperand prog env₂ ob frame opnd with
              | error _ => rfl
              | ok r₁ =>
                  dsimp only
                  refine unop_match_congr _ _ _ _ _ (fun resV => ?_)
                  rw [writeOpenPlace_noParam_congr prog hRegWf env₁ env₂
                    hAdt hAssoc ob hNoP r₁.2.2 dst resV]
          | cast kind opnd castTy =>
              cases kind with
              | unsupported | ptrToPtr | intToPtr | unsize | boxAsRef => rfl
              | intToInt =>
                  dsimp only
                  dsimp only [openRvalueNoParam] at hRv
                  cases (!OpenMirTy.beq
                      (normalizeOpenTy prog.traitRegistry normFuel castTy)
                      (normalizeOpenTy prog.traitRegistry normFuel dstTy)) with
                  | true =>
                      rw [if_true_eq]
                      rw [if_true_eq]
                  | false =>
                      rw [if_false_eq]
                      rw [if_false_eq]
                      have hOp := evalOpenOperand_noParam_congr prog hRegWf env₁
                        env₂ hAdt hAssoc ob frame opnd (bool_and_left hRv)
                      rw [hOp]
                      refine cast_match_congr _ _ _ _ (fun f₁ resV => ?_)
                      rw [writeOpenPlace_noParam_congr prog hRegWf env₁ env₂
                        hAdt hAssoc ob hNoP f₁ dst resV]

/-- `openEvalDetStep` return-terminator congruence across environments. -/
private theorem openTerm_return_noParam_congr (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env₁ env₂ : OpenExecEnv)
    (hAdt : env₁.typeSpecs.adtSpecs = env₂.typeSpecs.adtSpecs)
    (hAssoc : ∀ s tr as idx, openMirTyNoParam s = true →
      openMirTyListNoParam as = true →
      env₁.typeSpecs.assocSpecs s tr as idx =
        env₂.typeSpecs.assocSpecs s tr as idx)
    (s : OpenState) (frame : OpenFrameState)
    (restFrames : List OpenFrameState) (retV : Val) :
    FramesNoParam prog restFrames →
    (match restFrames with
    | [] => StepResult.done (TerminalOut.returned ⟨retV, s.callerMem⟩)
    | caller :: tail =>
        match frame.retDst with
        | some (dst, some retBlk, _) =>
            match openListGet? prog.bodies caller.defId with
            | some callerBody =>
                match writeOpenPlace prog env₁ callerBody caller dst retV with
                | .error k => .fault k
                | .ok caller' =>
                    .step
                      { s with
                        frames :=
                          { caller' with blockIdx := retBlk, stmtIdx := 0 } ::
                          tail }
            | none => .fault .unsupported
        | some (_, none, _) => .fault .undefined
        | none => .fault .unsupported) =
    (match restFrames with
    | [] => StepResult.done (TerminalOut.returned ⟨retV, s.callerMem⟩)
    | caller :: tail =>
        match frame.retDst with
        | some (dst, some retBlk, _) =>
            match openListGet? prog.bodies caller.defId with
            | some callerBody =>
                match writeOpenPlace prog env₂ callerBody caller dst retV with
                | .error k => .fault k
                | .ok caller' =>
                    .step
                      { s with
                        frames :=
                          { caller' with blockIdx := retBlk, stmtIdx := 0 } ::
                          tail }
            | none => .fault .unsupported
        | some (_, none, _) => .fault .undefined
        | none => .fault .unsupported) := by
  intro hRest
  cases restFrames with
  | nil => rfl
  | cons caller tail =>
      cases frame.retDst with
      | none => rfl
      | some p =>
          cases p with
          | mk dstP uwPair =>
              cases uwPair with
              | mk tgtOpt uwP =>
                  cases tgtOpt with
                  | none => rfl
                  | some retBlk =>
                      dsimp only
                      cases hCB : openListGet? prog.bodies caller.defId with
                      | none => rfl
                      | some cb =>
                          let ⟨cb0, hCB0, hNoPCB0⟩ := hRest.1
                          have hEqCB : cb = cb0 := by
                            rw [hCB] at hCB0; cases hCB0; rfl
                          subst hEqCB
                          dsimp only
                          rw [writeOpenPlace_noParam_congr prog hRegWf env₁ env₂
                            hAdt hAssoc cb hNoPCB0 caller dstP retV]

/-- `openEvalDetStep` agrees across `env₁, env₂` on any state satisfying
`FramesNoParam prog s.frames`. -/
theorem openEvalDetStep_noParam_congr (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env₁ env₂ : OpenExecEnv)
    (hAdt : env₁.typeSpecs.adtSpecs = env₂.typeSpecs.adtSpecs)
    (hAssoc : ∀ s tr as idx, openMirTyNoParam s = true →
      openMirTyListNoParam as = true →
      env₁.typeSpecs.assocSpecs s tr as idx =
        env₂.typeSpecs.assocSpecs s tr as idx)
    (s : OpenState) (hFrames : FramesNoParam prog s.frames) :
    openEvalDetStep prog env₁ s = openEvalDetStep prog env₂ s := by
  unfold openEvalDetStep openEvalDetStepAux
  cases hD : OpenProgram.toDay1? prog with
  | some _ => rfl
  | none =>
      dsimp only
      cases hFr : s.frames with
      | nil => rfl
      | cons frame restFrames =>
          dsimp only
          rw [hFr] at hFrames
          let ⟨ob0, hGet0, hNoP0⟩ := hFrames.1
          cases hB : openListGet? prog.bodies frame.defId with
          | none => rfl
          | some ob =>
              dsimp only
              have hEqOb : ob = ob0 := by
                rw [hB] at hGet0; cases hGet0; rfl
              subst hEqOb
              cases hBb : openListGet? ob.basicBlocks frame.blockIdx with
              | none => rfl
              | some bb =>
                  dsimp only
                  have hBbNoP : (bb.statements.all openStmtNoParam &&
                      openTermNoParam bb.terminator) = true := by
                    rw [← getElem?_eq_openListGet?] at hBb
                    exact all_getElem?_eq_true
                      (p := fun b : OpenBasicBlock =>
                        b.statements.all openStmtNoParam &&
                          openTermNoParam b.terminator)
                      (openBodyNoParam_parts ob hNoP0).2.2.2.2 hBb
                  cases hSt : openListGet? bb.statements frame.stmtIdx with
                  | some stmt =>
                      dsimp only
                      have hStmtNoP : openStmtNoParam stmt = true := by
                        rw [← getElem?_eq_openListGet?] at hSt
                        exact all_getElem?_eq_true (p := openStmtNoParam)
                          (bool_and_left hBbNoP) hSt
                      cases stmt with
                      | nop | storageLive _ | storageDead _ | unsupported => rfl
                      | assign dst rv =>
                          dsimp only [openStmtNoParam] at hStmtNoP
                          exact openEvalDetStep_assign_noParam_congr prog hRegWf
                            env₁ env₂ hAdt hAssoc s ob hNoP0 frame restFrames
                            dst rv (bool_and_right hStmtNoP)
                  | none =>
                      dsimp only
                      cases hEnd : Nat.beq frame.stmtIdx bb.statements.length
                        with
                      | false =>
                          rw [if_not_false_eq]
                          rw [if_not_false_eq]
                      | true =>
                          rw [if_not_true_eq]
                          rw [if_not_true_eq]
                          have hTermNoP := bool_and_right hBbNoP
                          cases hTerm : bb.terminator with
                          | goto _ | unreachable | call _ _ _ _ _ _
                          | traitCall _ _ _ _ _ _ _ _ | unsupported => rfl
                          | return_ =>
                              dsimp only
                              cases hCl : bb.cleanup with
                              | true =>
                                  rw [if_true_eq]
                                  rw [if_true_eq]
                              | false =>
                                  rw [if_false_eq]
                                  rw [if_false_eq]
                                  cases Trusted.MirSemantics.getElem?
                                      frame.locals 0 with
                                  | none => rfl
                                  | some sl =>
                                      cases sl with
                                      | dead | partialTuple _ | indirect _ => rfl
                                      | immediate opt =>
                                          cases opt with
                                          | none => rfl
                                          | some retV =>
                                              dsimp only
                                              exact
                                                openTerm_return_noParam_congr
                                                  prog hRegWf env₁ env₂ hAdt
                                                  hAssoc s frame restFrames
                                                  retV hFrames.2
                          | unwindResume => rfl
                          | switchInt discr tgts =>
                              dsimp only [openTermNoParam] at hTermNoP
                              rw [hTerm] at hTermNoP
                              dsimp only
                              rw [evalOpenOperand_noParam_congr prog hRegWf env₁
                                env₂ hAdt hAssoc ob frame discr hTermNoP]
                          | assert cond exp msg tgt uw =>
                              dsimp only [openTermNoParam] at hTermNoP
                              rw [hTerm] at hTermNoP
                              dsimp only
                              rw [evalOpenOperand_noParam_congr prog hRegWf env₁
                                env₂ hAdt hAssoc ob frame cond hTermNoP]

/-- `openInitState` produces `FramesNoParam` when the entry body satisfies
`openBodyNoParam`. -/
theorem openInitState_framesNoParam (prog : OpenProgram) (env : OpenExecEnv)
    (q : Query) (s₀ : OpenState)
    (hEntry : ∃ b, openListGet? prog.bodies prog.entryDefId = some b ∧
      openBodyNoParam b = true)
    (hInit : openInitState prog env q = .ok s₀) :
    FramesNoParam prog s₀.frames := by
  unfold openInitState openInitStateAux at hInit
  cases hD : OpenProgram.toDay1? prog with
  | some day1Prog =>
      rw [hD] at hInit
      dsimp only at hInit
      cases hIS : initState day1Prog q with
      | error _ => rw [hIS] at hInit; cases hInit
      | ok ds =>
          rw [hIS] at hInit
          cases hInit
          unfold initState at hIS
          have hIS := (ite_err_ok hIS).2
          have hIS := (ite_err_ok hIS).2
          cases hB : Trusted.MirSemantics.getElem? day1Prog.bodies
              day1Prog.entryDefId with
          | none =>
              rw [hB] at hIS
              dsimp only at hIS
              cases hIS
          | some body =>
              rw [hB] at hIS
              dsimp only at hIS
              have hIS := (ite_err_ok hIS).2
              have hIS := (ite_err_ok hIS).2
              have hIS := (ite_err_ok hIS).2
              have hIS := (ite_err_ok hIS).2
              have hIS := (ite_err_ok hIS).2
              have hIS := (ite_err_ok hIS).2
              have hIS := (ite_err_ok hIS).2
              have hIS := (ite_err_ok hIS).2
              have hIS := (ite_err_ok hIS).2
              have hIS := (ite_err_ok hIS).2
              cases hIS
              have hEntryId : day1Prog.entryDefId = prog.entryDefId := by
                unfold OpenProgram.toDay1? at hD
                cases hL : OpenProgram.toDay1List? prog.bodies with
                | none => rw [hL] at hD; cases hD
                | some bs => rw [hL] at hD; cases hD; rfl
              change FramesNoParam prog
                [{ defId := day1Prog.entryDefId, blockIdx := 0, stmtIdx := 0,
                   locals := _, retDst := none }]
              rw [hEntryId]
              exact ⟨hEntry, True.intro⟩
  | none =>
      rw [hD] at hInit
      dsimp only at hInit
      have hInit := (ite_err_ok hInit).2
      cases hB : openListGet? prog.bodies prog.entryDefId with
      | none => rw [hB] at hInit; cases hInit
      | some ob =>
          rw [hB] at hInit
          dsimp only at hInit
          have hInit := (ite_err_ok hInit).2
          cases hLoc : initOpenLocals prog env ob q.args with
          | none => rw [hLoc] at hInit; cases hInit
          | some ls =>
              rw [hLoc] at hInit
              cases hInit
              exact ⟨hEntry, True.intro⟩

/-- Whether a Day-1 terminator is `.call` or `.sysrootCall` (the per-block test
inside `bodyHasAnyCall`). -/
private noncomputable def day1TermIsCall (t : TerminatorKind) : Bool :=
  match t with
  | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
  | _ => false

private theorem openTerm_toDay1_noCall (t : OpenTerminatorKind)
    (dt : TerminatorKind) (h : OpenTerminatorKind.toDay1? t = some dt) :
    day1TermIsCall dt = false := by
  cases t with
  | goto _ =>
      dsimp only [OpenTerminatorKind.toDay1?] at h
      injection h with h; subst h; rfl
  | switchInt d tgts =>
      dsimp only [OpenTerminatorKind.toDay1?] at h
      cases hd : OpenOperand.toDay1? d with
      | none => rw [hd] at h; cases h
      | some _ => rw [hd] at h; injection h with h; subst h; rfl
  | return_ =>
      dsimp only [OpenTerminatorKind.toDay1?] at h
      injection h with h; subst h; rfl
  | unreachable =>
      dsimp only [OpenTerminatorKind.toDay1?] at h
      injection h with h; subst h; rfl
  | unwindResume =>
      dsimp only [OpenTerminatorKind.toDay1?] at h
      injection h with h; subst h; rfl
  | assert cond _ _ _ _ =>
      dsimp only [OpenTerminatorKind.toDay1?] at h
      cases hc : OpenOperand.toDay1? cond with
      | none => rw [hc] at h; cases h
      | some _ => rw [hc] at h; injection h with h; subst h; rfl
  | call _ _ _ _ _ _ =>
      dsimp only [OpenTerminatorKind.toDay1?] at h
      cases h
  | traitCall _ _ _ _ _ _ _ _ =>
      dsimp only [OpenTerminatorKind.toDay1?] at h
      cases h
  | unsupported =>
      dsimp only [OpenTerminatorKind.toDay1?] at h
      injection h with h; subst h; rfl

private theorem openBlocks_toDay1_noCall :
    ∀ (obs : List OpenBasicBlock) (bs : List BasicBlock),
      OpenBasicBlock.toDay1List? obs = some bs →
      bs.any (fun b =>
        match b.terminator with
        | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
        | _ => false) = false
  | [], bs, h => by
      dsimp only [OpenBasicBlock.toDay1List?] at h
      injection h with h; subst h; rfl
  | ob :: rest, bs, h => by
      dsimp only [OpenBasicBlock.toDay1List?] at h
      cases hb : OpenBasicBlock.toDay1? ob with
      | none => rw [hb] at h; cases h
      | some db =>
          cases hr : OpenBasicBlock.toDay1List? rest with
          | none => rw [hb, hr] at h; cases h
          | some drest =>
              rw [hb, hr] at h
              injection h with h; subst h
              have hRest := openBlocks_toDay1_noCall rest drest hr
              unfold OpenBasicBlock.toDay1? at hb
              cases hs : OpenStatementKind.toDay1List? ob.statements with
              | none => rw [hs] at hb; cases hb
              | some stmts =>
                  cases ht : OpenTerminatorKind.toDay1? ob.terminator with
                  | none => rw [hs, ht] at hb; cases hb
                  | some term =>
                      rw [hs, ht] at hb
                      injection hb with hb; subst hb
                      have hT := openTerm_toDay1_noCall ob.terminator term ht
                      unfold List.any
                      dsimp only
                      change (day1TermIsCall term || drest.any _) = false
                      rw [hT, Bool.false_or]
                      exact hRest

private theorem openBody_toDay1_noCall (ob : OpenBody) (b : Body)
    (h : OpenBody.toDay1? ob = some b) : bodyHasAnyCall b = false := by
  unfold OpenBody.toDay1? at h
  cases hl : OpenMirTy.toClosedMirTyList? ob.locals with
  | none => rw [hl] at h; cases h
  | some dLocals =>
      cases hbs : OpenBasicBlock.toDay1List? ob.basicBlocks with
      | none => rw [hl, hbs] at h; cases h
      | some dBlocks =>
          rw [hl, hbs] at h
          injection h with h; subst h
          unfold bodyHasAnyCall
          exact openBlocks_toDay1_noCall ob.basicBlocks dBlocks hbs

private theorem openProgList_toDay1_noCall :
    ∀ (obs : List OpenBody) (bs : List Body),
      OpenProgram.toDay1List? obs = some bs →
      bs.all (fun b => !bodyHasAnyCall b) = true
  | [], bs, h => by
      dsimp only [OpenProgram.toDay1List?] at h
      injection h with h; subst h; rfl
  | ob :: rest, bs, h => by
      dsimp only [OpenProgram.toDay1List?] at h
      cases hb : OpenBody.toDay1? ob with
      | none => rw [hb] at h; cases h
      | some db =>
          cases hr : OpenProgram.toDay1List? rest with
          | none => rw [hb, hr] at h; cases h
          | some drest =>
              rw [hb, hr] at h
              injection h with h; subst h
              unfold List.all
              dsimp only
              rw [openBody_toDay1_noCall ob db hb, Bool.not_false,
                Bool.true_and]
              exact openProgList_toDay1_noCall rest drest hr

/-- Every Day-1 program produced by `OpenProgram.toDay1?` is call-free. -/
theorem toDay1?_noCall (prog : OpenProgram) (p : Program)
    (h : OpenProgram.toDay1? prog = some p) :
    p.bodies.all (fun b => !bodyHasAnyCall b) = true := by
  unfold OpenProgram.toDay1? at h
  cases hl : OpenProgram.toDay1List? prog.bodies with
  | none => rw [hl] at h; cases h
  | some bs =>
      rw [hl] at h
      injection h with h; subst h
      exact openProgList_toDay1_noCall prog.bodies bs hl

private theorem bodies_all_noCall_getElem? :
    ∀ (bodies : List Body) (defId : DefId) (b : Body),
      bodies.all (fun b => !bodyHasAnyCall b) = true →
      Trusted.MirSemantics.getElem? bodies defId = some b →
      bodyHasAnyCall b = false
  | [], _, _, _, hb => by cases hb
  | b0 :: rest, defId, b, hAll, hb => by
      unfold List.all at hAll
      dsimp only at hAll
      cases h0 : bodyHasAnyCall b0 with
      | true =>
          rw [h0, Bool.not_true, Bool.false_and] at hAll; cases hAll
      | false =>
          rw [h0, Bool.not_false, Bool.true_and] at hAll
          cases defId with
          | zero =>
              dsimp only [Trusted.MirSemantics.getElem?] at hb
              injection hb with hb; subst hb; exact h0
          | succ k =>
              dsimp only [Trusted.MirSemantics.getElem?] at hb
              exact bodies_all_noCall_getElem? rest k b hAll hb

/-- In a call-free program, every frame's active body (including a pinned
`sysrootNumBody`) is call-free. -/
theorem activeFrameBody_noCall (p : Program) (f : FrameState)
    (hAll : p.bodies.all (fun b => !bodyHasAnyCall b) = true) :
    ∀ b, activeFrameBody p f = some b → bodyHasAnyCall b = false := by
  intro b hb
  unfold activeFrameBody at hb
  cases hs : f.sysrootOp? with
  | some op =>
      rw [hs] at hb
      injection hb with hb; subst hb
      unfold bodyHasAnyCall
      cases op with
      | mk kind _ _ => cases kind <;> rfl
  | none =>
      rw [hs] at hb
      exact bodies_all_noCall_getElem? p.bodies f.defId b hAll hb

private theorem basicBlocks_noCall_term_aux
    {bbs : List BasicBlock} {blk : BasicBlockId} {bb : BasicBlock}
    (hNo : bbs.any (fun b =>
      match b.terminator with
      | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
      | _ => false) = false)
    (hBb : Trusted.MirSemantics.getElem? bbs blk = some bb) :
    (match bb.terminator with
     | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
     | _ => false) = false := by
  induction bbs generalizing blk with
  | nil => cases hBb
  | cons b rest ih =>
    unfold List.any at hNo
    dsimp only at hNo
    cases hOr : (match b.terminator with
      | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
      | _ => false)
    · rw [hOr, Bool.false_or] at hNo
      cases blk with
      | zero =>
        injection hBb with hEq; subst hEq; exact hOr
      | succ blk' =>
        exact ih hNo hBb
    · rw [hOr, Bool.true_or] at hNo
      cases hNo

/-- A basic block of a call-free body (`bodyHasAnyCall body = false`) never
ends in `.call` or `.sysrootCall`. -/
theorem basicBlocks_noCall_term {body : Body} {blk : BasicBlockId}
    {bb : BasicBlock} (hNo : bodyHasAnyCall body = false)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks blk = some bb) :
    (match bb.terminator with
     | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
     | _ => false) = false := by
  unfold bodyHasAnyCall at hNo
  exact basicBlocks_noCall_term_aux hNo hBb

/-- Day-1 `evalStep` on a singleton frame whose active body is call-free
preserves the active `defId` and `sysrootOp?` whenever it steps. -/
theorem evalStep_single_preserves_defId (p : Program) (df : FrameState)
    (mem : MemoryState) (cm : CallerMemory) (next : State)
    (hNoCall : ∀ b, activeFrameBody p df = some b → bodyHasAnyCall b = false)
    (h : evalStep p 0 { frames := [df], callerMem := cm, mem := mem } =
      .step next) :
    ∃ df', next.frames = [df'] ∧ df'.defId = df.defId ∧
      df'.sysrootOp? = df.sysrootOp? := by
  unfold evalStep at h
  dsimp only at h
  cases hB : activeFrameBody p df with
  | none => rw [hB] at h; cases h
  | some body =>
      rw [hB] at h
      dsimp only at h
      cases hBb : Trusted.MirSemantics.getElem? body.basicBlocks df.blockIdx with
      | none => rw [hBb] at h; cases h
      | some bb =>
          rw [hBb] at h
          dsimp only at h
          cases hSt : Trusted.MirSemantics.getElem? bb.statements df.stmtIdx
              with
          | some stmt =>
              rw [hSt] at h
              dsimp only [attachCallers] at h
              unfold evalStatement at h
              cases stmt with
              | nop => cases h; exact ⟨_, rfl, rfl, rfl⟩
              | storageLive lid =>
                  dsimp only at h
                  cases h1 : Trusted.MirSemantics.getElem? body.locals lid with
                  | none => rw [h1] at h; cases h
                  | some lty =>
                      rw [h1] at h
                      dsimp only at h
                      cases h2 : Trusted.MirSemantics.getElem? df.locals lid
                        with
                      | none => rw [h2] at h; cases h
                      | some _ =>
                          rw [h2] at h
                          dsimp only at h
                          cases h3 : setElem? df.locals lid
                              (liveUninitSlot lty) with
                          | none => rw [h3] at h; cases h
                          | some _ =>
                              rw [h3] at h
                              dsimp only at h
                              cases h4 : deallocateLocal mem _ with
                              | error _ => rw [h4] at h; cases h
                              | ok _ => rw [h4] at h; cases h; exact ⟨_, rfl, rfl, rfl⟩
              | storageDead lid =>
                  dsimp only at h
                  have h := ite_fault_step h
                  cases h1 : Trusted.MirSemantics.getElem? df.locals lid with
                  | none => rw [h1] at h; cases h
                  | some _ =>
                      rw [h1] at h
                      dsimp only at h
                      cases h2 : setElem? df.locals lid .dead with
                      | none => rw [h2] at h; cases h
                      | some _ =>
                          rw [h2] at h
                          dsimp only at h
                          cases h3 : deallocateLocal mem _ with
                          | error _ => rw [h3] at h; cases h
                          | ok _ => rw [h3] at h; cases h; exact ⟨_, rfl, rfl, rfl⟩
              | assign dst rv =>
                  dsimp only at h
                  have h := ite_fault_step h
                  cases h1 : Trusted.MirSemantics.getElem? body.locals
                      dst.localId with
                  | none => rw [h1] at h; cases h
                  | some dstTy =>
                      rw [h1] at h
                      dsimp only at h
                      cases h2 : evalRvalue body.locals df.locals mem dstTy rv
                        with
                      | error _ => rw [h2] at h; cases h
                      | ok r2 =>
                          rw [h2] at h
                          dsimp only at h
                          cases h3 : writePlace r2.2.1 r2.2.2 dst.localId dstTy
                              r2.1 with
                          | error _ => rw [h3] at h; cases h
                          | ok r3 => rw [h3] at h; cases h; exact ⟨_, rfl, rfl, rfl⟩
              | unsupported => cases h
          | none =>
              rw [hSt] at h
              dsimp only at h
              have h := ite_step_fault_false h
              unfold evalTerminator at h
              cases hTerm : bb.terminator with
              | goto tgt =>
                  rw [hTerm] at h
                  dsimp only [attachCallers] at h
                  unfold jumpToBlock at h
                  cases h; exact ⟨_, rfl, rfl, rfl⟩
              | switchInt discr tgts =>
                  rw [hTerm] at h
                  dsimp only [attachCallers] at h
                  cases h1 : evalPrimitiveOperand body.locals df.locals mem
                      discr with
                  | error _ => rw [h1] at h; cases h
                  | ok r1 =>
                      rw [h1] at h
                      dsimp only at h
                      cases hDv : r1.1 with
                      | scalar sv =>
                          rw [hDv] at h; dsimp only at h
                          cases h2 : evalSwitchBranches sv.width sv.bits
                              tgts.otherwise tgts.branches with
                          | error _ => rw [h2] at h; cases h
                          | ok _ =>
                              rw [h2] at h; dsimp only at h
                              unfold jumpToBlock at h
                              cases h; exact ⟨_, rfl, rfl, rfl⟩
                      | bool b =>
                          rw [hDv] at h; dsimp only at h
                          cases h2 : evalBoolSwitchBranches b tgts.otherwise
                              tgts.branches with
                          | error _ => rw [h2] at h; cases h
                          | ok _ =>
                              rw [h2] at h; dsimp only at h
                              unfold jumpToBlock at h
                              cases h; exact ⟨_, rfl, rfl, rfl⟩
                      | char c =>
                          rw [hDv] at h; dsimp only at h
                          cases h2 : evalCharSwitchBranches c tgts.otherwise
                              tgts.branches with
                          | error _ => rw [h2] at h; cases h
                          | ok _ =>
                              rw [h2] at h; dsimp only at h
                              unfold jumpToBlock at h
                              cases h; exact ⟨_, rfl, rfl, rfl⟩
                      | unit | enumVal _ _ | ordering _ | tuple _
                      | bytes _ | ptr _ | slicePtr _ _ | rangeTo _
                      | rangeFrom _ | array _ | optionVal _ | range _ _
                      | vec _ _ _ | boxPtr _ _ =>
                          rw [hDv] at h; dsimp only at h
                          cases hBr : tgts.branches with
                          | nil =>
                              rw [hBr] at h
                              unfold jumpToBlock at h
                              cases h; exact ⟨_, rfl, rfl, rfl⟩
                          | cons _ _ =>
                              rw [hBr] at h; cases h
              | return_ =>
                  rw [hTerm] at h
                  dsimp only [attachCallers] at h
                  have h := ite_fault_step h
                  cases h1 : Trusted.MirSemantics.getElem? df.locals 0 with
                  | none => rw [h1] at h; cases h
                  | some sl =>
                      rw [h1] at h
                      cases sl with
                      | dead => cases h
                      | partialTuple _ => cases h
                      | immediate opt =>
                          cases opt with
                          | none => cases h
                          | some _ => cases h
                      | indirect mp =>
                          cases h2 : Trusted.MirSemantics.getElem? body.locals 0
                            with
                          | none => rw [h2] at h; cases h
                          | some rty =>
                              rw [h2] at h
                              dsimp only at h
                              cases h3 : loadIndirect mem rty mp with
                              | error _ => rw [h3] at h; cases h
                              | ok opt =>
                                  rw [h3] at h
                                  cases opt <;> cases h
              | call _ _ _ _ _ | sysrootCall _ _ _ _ _ =>
                  have hc := basicBlocks_noCall_term (hNoCall body hB) hBb
                  rw [hTerm] at hc; cases hc
              | assert cond expected msg target unwind =>
                  rw [hTerm] at h
                  dsimp only [attachCallers] at h
                  cases hOp : evalPrimitiveOperand body.locals df.locals mem cond with
                  | error _ => rw [hOp] at h; cases h
                  | ok res =>
                      rw [hOp] at h
                      cases res with
                      | mk cv rest =>
                          cases rest with
                          | mk l₁ m₁ =>
                              dsimp only at h
                              cases cv with
                              | bool b =>
                                  dsimp only at h
                                  cases hEq : (b == expected) with
                                  | true =>
                                      rw [ite_cond_true hEq] at h
                                      unfold jumpToBlock at h
                                      cases h
                                      exact ⟨_, rfl, rfl, rfl⟩
                                  | false =>
                                      rw [ite_cond_false hEq] at h
                                      have hNe : ∀ (m : AssertKind) (ps : PanicStrategy)
                                          (uw : UnwindAction) (c : CallerMemory)
                                          (lh : Bool) (st : State),
                                          evalAssertFailure m ps uw c lh ≠ .step st := by
                                        intro m ps uw c lh st hEq'
                                        cases m with
                                        | misalignedPtrDeref | nullPtrDeref | overflowNeg
                                        | unsupported => cases hEq'
                                        | boundsCheck | divByZero | remByZero =>
                                            cases lh <;> cases ps <;> cases uw <;> cases hEq'
                                        | overflow op =>
                                            cases op <;>
                                              (first
                                                | cases hEq'
                                                | (cases lh <;> cases ps <;> cases uw <;>
                                                   cases hEq'))
                                      exact False.elim (hNe _ _ _ _ _ _ h)
                              | scalar _ | char _ | unit | enumVal _ _ | tuple _ | ptr _
                              | slicePtr _ _ | rangeTo _ | rangeFrom _ | bytes _
                              | array _ | ordering _ | range _ _ | boxPtr _ _
                              | vec _ _ _ => cases h
                              | optionVal optV => cases optV <;> (cases h)
              | unreachable | unwindResume
              | coreCall _ _ _ _ _ | unsupported =>
                  rw [hTerm] at h; dsimp only [attachCallers] at h; cases h

/-- `evalOpenOperand` preserves `frame.defId`. -/
theorem evalOpenOperand_preserves_defId (prog : OpenProgram) (env : OpenExecEnv)
    (ob : OpenBody) (frame : OpenFrameState) (op : OpenOperand)
    (v : Val) (ty : OpenMirTy) (f' : OpenFrameState)
    (h : evalOpenOperand prog env ob frame op = .ok (v, ty, f')) :
    f'.defId = frame.defId := by
  cases op with
  | copy p =>
      dsimp only [evalOpenOperand] at h
      cases h1 : openListGet? ob.locals p.localId with
      | none => rw [h1] at h; cases h
      | some ty =>
          rw [h1] at h
          cases h2 : Trusted.MirSemantics.getElem? frame.locals p.localId with
          | none => rw [h2] at h; cases h
          | some sl =>
              rw [h2] at h
              cases sl with
              | dead => cases h
              | partialTuple _ => cases h
              | indirect _ => cases h
              | immediate opt =>
                  cases hEmp : (!p.projection.isEmpty) with
                  | true => rw [hEmp] at h; cases h
                  | false =>
                      rw [hEmp] at h
                      cases opt with
                      | none => cases h
                      | some _ => cases h; rfl
  | move p =>
      dsimp only [evalOpenOperand] at h
      cases h1 : openListGet? ob.locals p.localId with
      | none => rw [h1] at h; cases h
      | some ty₁ =>
          rw [h1] at h
          cases h2 : Trusted.MirSemantics.getElem? frame.locals p.localId with
          | none => rw [h2] at h; cases h
          | some sl =>
              rw [h2] at h
              cases sl with
              | dead => cases h
              | partialTuple _ => cases h
              | indirect _ => cases h
              | immediate opt =>
                  dsimp only at h
                  cases hEmp : (!p.projection.isEmpty) with
                  | true => rw [hEmp, if_true_eq] at h; cases h
                  | false =>
                      rw [hEmp, if_false_eq] at h
                      cases opt with
                      | none => cases h
                      | some _ =>
                          cases h3 : setElem? frame.locals p.localId
                              (openLiveUninitSlot prog ty₁) with
                          | none => rw [h3] at h; cases h
                          | some ls' => rw [h3] at h; cases h; rfl
  | constant c =>
      cases hCl : OpenMirTy.toClosedMirTy? c.ty with
      | some mty =>
          dsimp only [evalOpenOperand] at h
          rw [hCl] at h
          dsimp only at h
          cases hEv : evalConstLit mty c.lit with
          | error _ => rw [hEv] at h; cases h
          | ok _ => rw [hEv] at h; cases h; rfl
      | none =>
          cases hLit : c.lit with
          | scalar _ | rodataBytes _ | rodataRef _ _ _ _ =>
              dsimp only [evalOpenOperand] at h
              rw [hCl, hLit] at h
              cases h
          | zeroSized =>
              dsimp only [evalOpenOperand] at h
              rw [hCl, hLit] at h
              dsimp only at h
              cases hE : evalOpenTySpec prog.traitRegistry normFuel
                  env.typeSpecs c.ty with
              | none => rw [hE] at h; cases h
              | some sp =>
                  rw [hE] at h
                  dsimp only at h
                  have hOk := except_ite_ok h
                  cases hOk; rfl

/-- `evalOpenOperands` preserves `frame.defId`. -/
theorem evalOpenOperands_preserves_defId (prog : OpenProgram)
    (env : OpenExecEnv) (ob : OpenBody) :
    ∀ (ops : List OpenOperand) (frame : OpenFrameState) (vs : List Val)
      (f' : OpenFrameState),
      evalOpenOperands prog env ob frame ops = .ok (vs, f') →
      f'.defId = frame.defId
  | [], frame, vs, f', h => by cases h; rfl
  | op :: ops, frame, vs, f', h => by
      unfold evalOpenOperands at h
      cases h1 : evalOpenOperand prog env ob frame op with
      | error _ => rw [h1] at h; cases h
      | ok r₁ =>
          rw [h1] at h
          dsimp only at h
          cases h2 : evalOpenOperands prog env ob r₁.2.2 ops with
          | error _ => rw [h2] at h; cases h
          | ok r₂ =>
              rw [h2] at h
              have hd1 := evalOpenOperand_preserves_defId prog env ob frame op
                r₁.1 r₁.2.1 r₁.2.2 h1
              have hd2 := evalOpenOperands_preserves_defId prog env ob ops
                r₁.2.2 r₂.1 r₂.2 h2
              cases h
              exact Eq.trans hd2 hd1

/-- `writeOpenPlace` preserves `frame.defId`. -/
theorem writeOpenPlace_preserves_defId (prog : OpenProgram) (env : OpenExecEnv)
    (ob : OpenBody) (frame : OpenFrameState) (dst : OpenPlace) (v : Val)
    (f' : OpenFrameState)
    (h : writeOpenPlace prog env ob frame dst v = .ok f') :
    f'.defId = frame.defId := by
  cases hEmp : dst.projection.isEmpty with
  | false =>
      unfold writeOpenPlace at h
      rw [hEmp, if_not_false_eq] at h
      cases h
  | true =>
      unfold writeOpenPlace at h
      rw [hEmp, if_not_true_eq] at h
      cases hGet : openListGet? ob.locals dst.localId with
      | none => rw [hGet] at h; cases h
      | some dstTy =>
          rw [hGet] at h
          dsimp only at h
          cases hChk : (!checkOpenVal prog env v dstTy) with
          | true => rw [hChk] at h; cases h
          | false =>
              rw [hChk] at h
              cases hLoc : Trusted.MirSemantics.getElem? frame.locals dst.localId
                with
              | none => rw [hLoc] at h; cases h
              | some sl =>
                  rw [hLoc] at h
                  cases sl with
                  | dead | partialTuple _ | indirect _ => cases h
                  | immediate _ =>
                      cases hSet : setElem? frame.locals dst.localId
                          (.immediate (some v)) with
                      | none => rw [hSet] at h; cases h
                      | some ls' => rw [hSet] at h; cases h; rfl

/-- `openUnwindWith` preserves `FramesNoParam prog`. -/
theorem openUnwindWith_preserves_framesNoParam (prog : OpenProgram) :
    ∀ (restFrames : List OpenFrameState) (s : OpenState) (cm : CallerMemory)
      (uw : UnwindAction) (cf? : Option OpenFrameState) (s' : OpenState),
      FramesNoParam prog restFrames →
      (∀ cf, cf? = some cf → ∃ b : OpenBody,
        openListGet? prog.bodies cf.defId = some b ∧
        openBodyNoParam b = true) →
      openUnwindWith s cm restFrames uw cf? = .step s' →
      FramesNoParam prog s'.frames
  | [], s, cm, uw, cf?, s', hRest, hCf, hStep => by
      unfold openUnwindWith at hStep
      cases uw with
      | continue_ | unreachable | terminate => cases hStep
      | cleanup blk =>
          cases cf? with
          | none => cases hStep
          | some f =>
              cases hStep
              exact ⟨hCf f rfl, hRest⟩
  | caller :: tail, s, cm, uw, cf?, s', hRest, hCf, hStep => by
      unfold openUnwindWith at hStep
      cases uw with
      | continue_ =>
          dsimp only at hStep
          cases hRet : caller.retDst with
          | none => rw [hRet] at hStep; cases hStep
          | some p =>
              rw [hRet] at hStep
              exact openUnwindWith_preserves_framesNoParam prog tail
                { s with callerMem := cm } cm p.2.2 none s' hRest.2
                (fun _ h => by cases h) hStep
      | unreachable | terminate => cases hStep
      | cleanup blk =>
          cases cf? with
          | some f =>
              cases hStep
              exact ⟨hCf f rfl, hRest⟩
          | none =>
              cases hStep
              exact hRest

private theorem openReturn_preserves_framesNoParam (prog : OpenProgram)
    (env : OpenExecEnv) (s : OpenState) (frame : OpenFrameState) (retV : Val)
    (restFrames : List OpenFrameState) (hRest : FramesNoParam prog restFrames)
    (s' : OpenState)
    (hStep : (match restFrames with
      | [] => StepResult.done (TerminalOut.returned ⟨retV, s.callerMem⟩)
      | caller :: tail =>
          match frame.retDst with
          | some (dst, some retBlk, _) =>
              match openListGet? prog.bodies caller.defId with
              | some callerBody =>
                  match writeOpenPlace prog env callerBody caller dst retV with
                  | .error k => .fault k
                  | .ok caller' =>
                      .step
                        { s with
                          frames :=
                            { caller' with blockIdx := retBlk, stmtIdx := 0 } ::
                            tail }
              | none => .fault .unsupported
          | some (_, none, _) => .fault .undefined
          | none => .fault .unsupported) = .step s') :
    FramesNoParam prog s'.frames := by
  cases restFrames with
  | nil => cases hStep
  | cons caller tail =>
      cases hRet : frame.retDst with
      | none => rw [hRet] at hStep; cases hStep
      | some p =>
          cases p with
          | mk dstSnd uwPair =>
              cases uwPair with
              | mk tgtOpt uwSnd =>
                  rw [hRet] at hStep
                  dsimp only at hStep
                  cases tgtOpt with
                  | none => cases hStep
                  | some _ =>
                      cases h4 : openListGet? prog.bodies caller.defId with
                      | none => rw [h4] at hStep; cases hStep
                      | some cb =>
                          rw [h4] at hStep
                          dsimp only at hStep
                          cases h5 : writeOpenPlace prog env cb caller dstSnd
                              retV with
                          | error _ => rw [h5] at hStep; cases hStep
                          | ok c' =>
                              rw [h5] at hStep
                              cases hStep
                              have hc := writeOpenPlace_preserves_defId prog env
                                cb caller dstSnd retV c' h5
                              refine ⟨?_, hRest.2⟩
                              change ∃ b,
                                openListGet? prog.bodies c'.defId = some b ∧
                                  openBodyNoParam b = true
                              rw [hc]
                              exact hRest.1

/-- `openEvalDetStep` preserves `FramesNoParam` whenever it steps. -/
theorem openEvalDetStep_preserves_framesNoParam (prog : OpenProgram)
    (env : OpenExecEnv) (s s' : OpenState)
    (hFrames : FramesNoParam prog s.frames)
    (hStep : openEvalDetStep prog env s = .step s') :
    FramesNoParam prog s'.frames := by
  unfold openEvalDetStep openEvalDetStepAux at hStep
  cases hD : OpenProgram.toDay1? prog with
  | some day1Prog =>
      rw [hD] at hStep
      dsimp only at hStep
      cases hSf : s.frames with
      | nil =>
          unfold OpenState.toState evalStep at hStep
          rw [hSf] at hStep
          cases hStep
      | cons of_ rt =>
          cases rt with
          | cons _ _ =>
              unfold OpenState.toState evalStep at hStep
              rw [hSf] at hStep
              cases hStep
          | nil =>
              rw [hSf] at hFrames hStep
              dsimp only at hStep
              have hStep' :
                  liftStepResult
                      (evalStep day1Prog 0
                        { frames := [OpenFrameState.toFrameState of_],
                          callerMem := s.callerMem, mem := s.mem }) =
                    .step s' := by
                change liftStepResult (evalStep day1Prog 0 (OpenState.toState s)) =
                  .step s' at hStep
                unfold OpenState.toState at hStep
                rw [hSf] at hStep
                exact hStep
              cases hEval : evalStep day1Prog 0
                  { frames := [OpenFrameState.toFrameState of_],
                    callerMem := s.callerMem, mem := s.mem } with
              | done _ => rw [hEval] at hStep'; cases hStep'
              | fault _ => rw [hEval] at hStep'; cases hStep'
              | step next =>
                  rw [hEval] at hStep'
                  cases hStep'
                  let ⟨df', hNextFr, hDefEq, _⟩ :=
                    evalStep_single_preserves_defId day1Prog
                      (OpenFrameState.toFrameState of_) s.mem s.callerMem next
                      (activeFrameBody_noCall day1Prog _
                        (toDay1?_noCall prog day1Prog hD))
                      hEval
                  change FramesNoParam prog
                    (next.frames.map OpenFrameState.ofFrameState)
                  rw [hNextFr]
                  dsimp only [List.map]
                  refine ⟨?_, True.intro⟩
                  change ∃ b, openListGet? prog.bodies df'.defId = some b ∧
                    openBodyNoParam b = true
                  rw [hDefEq]
                  exact hFrames.1
  | none =>
      rw [hD] at hStep
      dsimp only at hStep
      cases hFr : s.frames with
      | nil => rw [hFr] at hStep; cases hStep
      | cons frame restFrames =>
          rw [hFr] at hFrames hStep
          dsimp only at hStep
          cases hB : openListGet? prog.bodies frame.defId with
          | none => rw [hB] at hStep; cases hStep
          | some ob =>
              rw [hB] at hStep
              dsimp only at hStep
              cases hBb : openListGet? ob.basicBlocks frame.blockIdx with
              | none => rw [hBb] at hStep; cases hStep
              | some bb =>
                  rw [hBb] at hStep
                  dsimp only at hStep
                  cases hSt : openListGet? bb.statements frame.stmtIdx with
                  | some stmt =>
                      rw [hSt] at hStep
                      dsimp only at hStep
                      cases stmt with
                      | nop => cases hStep; exact hFrames
                      | storageLive lid =>
                          dsimp only at hStep
                          cases h1 : openListGet? ob.locals lid with
                          | none => rw [h1] at hStep; cases hStep
                          | some ty =>
                              rw [h1] at hStep
                              cases h2 : Trusted.MirSemantics.getElem?
                                  frame.locals lid with
                              | none => rw [h2] at hStep; cases hStep
                              | some old =>
                                  rw [h2] at hStep
                                  dsimp only at hStep
                                  cases h3 : setElem? frame.locals lid
                                      (openLiveUninitSlot prog ty) with
                                  | none => rw [h3] at hStep; cases hStep
                                  | some ls' =>
                                      rw [h3] at hStep
                                      cases h4 : deallocateLocal s.mem old with
                                      | error _ => rw [h4] at hStep; cases hStep
                                      | ok mem' =>
                                          rw [h4] at hStep
                                          cases hStep; exact hFrames
                      | storageDead lid =>
                          dsimp only at hStep
                          have hStep := ite_fault_step hStep
                          cases h2 : Trusted.MirSemantics.getElem? frame.locals
                              lid with
                          | none => rw [h2] at hStep; cases hStep
                          | some old =>
                              rw [h2] at hStep
                              dsimp only at hStep
                              cases h3 : setElem? frame.locals lid .dead with
                              | none => rw [h3] at hStep; cases hStep
                              | some ls' =>
                                  rw [h3] at hStep
                                  cases h4 : deallocateLocal s.mem old with
                                  | error _ => rw [h4] at hStep; cases hStep
                                  | ok mem' =>
                                      rw [h4] at hStep
                                      cases hStep; exact hFrames
                      | assign dst rv =>
                          dsimp only at hStep
                          have hStep := ite_fault_step hStep
                          cases h2 : openListGet? ob.locals dst.localId with
                          | none => rw [h2] at hStep; cases hStep
                          | some dstTy =>
                              rw [h2] at hStep
                              cases rv with
                              | discriminant _ | ref _ _ | addressOf _ _
                              | aggregateTuple _ | unsupported => cases hStep
                              | «use» op =>
                                  dsimp only at hStep
                                  cases h3 : evalOpenOperand prog env ob frame op
                                    with
                                  | error _ => rw [h3] at hStep; cases hStep
                                  | ok r =>
                                      rw [h3] at hStep
                                      dsimp only at hStep
                                      have hStep := ite_fault_step hStep
                                      cases h5 : writeOpenPlace prog env ob
                                          r.2.2 dst r.1 with
                                      | error _ => rw [h5] at hStep; cases hStep
                                      | ok f' =>
                                          rw [h5] at hStep
                                          cases hStep
                                          have hd1 :=
                                            evalOpenOperand_preserves_defId
                                              prog env ob frame op r.1 r.2.1
                                              r.2.2 h3
                                          have hd2 :=
                                            writeOpenPlace_preserves_defId
                                              prog env ob r.2.2 dst r.1 f' h5
                                          refine ⟨?_, hFrames.2⟩
                                          change ∃ b,
                                            openListGet? prog.bodies f'.defId =
                                                some b ∧
                                              openBodyNoParam b = true
                                          rw [hd2, hd1]
                                          exact hFrames.1
                              | binaryOp op lhs rhs =>
                                  dsimp only at hStep
                                  cases h3 : evalOpenOperand prog env ob frame lhs
                                    with
                                  | error _ => rw [h3] at hStep; cases hStep
                                  | ok r₁ =>
                                      rw [h3] at hStep
                                      dsimp only at hStep
                                      cases h4 : evalOpenOperand prog env ob
                                          r₁.2.2 rhs with
                                      | error _ => rw [h4] at hStep; cases hStep
                                      | ok r₂ =>
                                          rw [h4] at hStep
                                          dsimp only at hStep
                                          have ⟨resV, _, hWr⟩ :=
                                            binop_match_step _ _ _ _ _ hStep
                                          cases h5 : writeOpenPlace prog env ob
                                              r₂.2.2 dst resV with
                                          | error _ =>
                                              rw [h5] at hWr; cases hWr
                                          | ok f' =>
                                              rw [h5] at hWr; cases hWr
                                              have hd1 :=
                                                evalOpenOperand_preserves_defId
                                                  prog env ob frame lhs r₁.1
                                                  r₁.2.1 r₁.2.2 h3
                                              have hd2 :=
                                                evalOpenOperand_preserves_defId
                                                  prog env ob r₁.2.2 rhs r₂.1
                                                  r₂.2.1 r₂.2.2 h4
                                              have hd3 :=
                                                writeOpenPlace_preserves_defId
                                                  prog env ob r₂.2.2 dst resV f'
                                                  h5
                                              refine ⟨?_, hFrames.2⟩
                                              change ∃ b,
                                                openListGet? prog.bodies
                                                    f'.defId = some b ∧
                                                  openBodyNoParam b = true
                                              rw [hd3, hd2, hd1]
                                              exact hFrames.1
                              | unaryOp op opnd =>
                                  dsimp only at hStep
                                  cases h3 : evalOpenOperand prog env ob frame
                                      opnd with
                                  | error _ => rw [h3] at hStep; cases hStep
                                  | ok r₁ =>
                                      rw [h3] at hStep
                                      dsimp only at hStep
                                      have ⟨resV, _, hWr⟩ :=
                                        unop_match_step _ _ _ _ hStep
                                      cases h5 : writeOpenPlace prog env ob
                                          r₁.2.2 dst resV with
                                      | error _ => rw [h5] at hWr; cases hWr
                                      | ok f' =>
                                          rw [h5] at hWr; cases hWr
                                          have hd1 :=
                                            evalOpenOperand_preserves_defId
                                              prog env ob frame opnd r₁.1
                                              r₁.2.1 r₁.2.2 h3
                                          have hd2 :=
                                            writeOpenPlace_preserves_defId
                                              prog env ob r₁.2.2 dst resV f' h5
                                          refine ⟨?_, hFrames.2⟩
                                          change ∃ b,
                                            openListGet? prog.bodies
                                                f'.defId = some b ∧
                                              openBodyNoParam b = true
                                          rw [hd2, hd1]
                                          exact hFrames.1
                              | cast kind opnd castTy =>
                                  cases kind with
                                  | unsupported | ptrToPtr | intToPtr
                                  | unsize | boxAsRef =>
                                      cases hStep
                                  | intToInt =>
                                      dsimp only at hStep
                                      have hStep := ite_fault_step hStep
                                      cases h3 : evalOpenOperand prog env ob
                                          frame opnd with
                                      | error _ => rw [h3] at hStep; cases hStep
                                      | ok r₁ =>
                                          rw [h3] at hStep
                                          cases hc1 : OpenMirTy.toClosedMirTy?
                                              (normalizeOpenTy
                                                prog.traitRegistry normFuel
                                                castTy) with
                                          | none => rw [hc1] at hStep; cases hStep
                                          | some mCast =>
                                              rw [hc1] at hStep
                                              dsimp only at hStep
                                              cases hc2 :
                                                  OpenMirTy.toClosedMirTy?
                                                    r₁.2.1 with
                                              | none =>
                                                  rw [hc2] at hStep; cases hStep
                                              | some mSrc =>
                                                  rw [hc2] at hStep
                                                  dsimp only at hStep
                                                  have hStep :=
                                                    ite_fault_step hStep
                                                  cases hev : evalIntToIntCast
                                                      r₁.1 mCast with
                                                  | error _ =>
                                                      rw [hev] at hStep
                                                      cases hStep
                                                  | ok resV =>
                                                      rw [hev] at hStep
                                                      dsimp only at hStep
                                                      cases h5 : writeOpenPlace
                                                          prog env ob r₁.2.2 dst
                                                          resV with
                                                      | error _ =>
                                                          rw [h5] at hStep
                                                          cases hStep
                                                      | ok f' =>
                                                          rw [h5] at hStep
                                                          cases hStep
                                                          have hd1 :=
                                                            evalOpenOperand_preserves_defId
                                                              prog env ob frame
                                                              opnd r₁.1 r₁.2.1
                                                              r₁.2.2 h3
                                                          have hd2 :=
                                                            writeOpenPlace_preserves_defId
                                                              prog env ob r₁.2.2
                                                              dst resV f' h5
                                                          refine ⟨?_, hFrames.2⟩
                                                          change ∃ b,
                                                            openListGet?
                                                                prog.bodies
                                                                f'.defId =
                                                              some b ∧
                                                            openBodyNoParam b =
                                                              true
                                                          rw [hd2, hd1]
                                                          exact hFrames.1
                      | unsupported => cases hStep
                  | none =>
                      rw [hSt] at hStep
                      dsimp only at hStep
                      have hStep := ite_fault_step hStep
                      cases hTerm : bb.terminator with
                      | goto _ =>
                          rw [hTerm] at hStep; cases hStep; exact hFrames
                      | return_ =>
                          rw [hTerm] at hStep
                          dsimp only at hStep
                          have hStep := ite_fault_step hStep
                          cases h3 : Trusted.MirSemantics.getElem? frame.locals
                              0 with
                          | none => rw [h3] at hStep; cases hStep
                          | some sl =>
                              rw [h3] at hStep
                              cases sl with
                              | dead | partialTuple _ | indirect _ => cases hStep
                              | immediate opt =>
                                  cases opt with
                                  | none => cases hStep
                                  | some retV =>
                                      exact openReturn_preserves_framesNoParam
                                        prog env s frame retV restFrames
                                        hFrames.2 s' hStep
                      | unreachable => rw [hTerm] at hStep; cases hStep
                      | unwindResume =>
                          rw [hTerm] at hStep
                          dsimp only at hStep
                          have hStep := ite_fault_step hStep
                          cases restFrames with
                          | nil => cases hStep
                          | cons caller tail =>
                              cases hRet : frame.retDst with
                              | none => rw [hRet] at hStep; cases hStep
                              | some p =>
                                  cases p with
                                  | mk dstSnd uwPair =>
                                      cases uwPair with
                                      | mk tgtOpt uw =>
                                          rw [hRet] at hStep
                                          dsimp only at hStep
                                          exact
                                            openUnwindWith_preserves_framesNoParam
                                              prog (caller :: tail) s
                                              s.callerMem uw none s' hFrames.2
                                              (fun _ hc => by cases hc) hStep
                      | switchInt discr tgts =>
                          rw [hTerm] at hStep
                          dsimp only at hStep
                          cases h2 : evalOpenOperand prog env ob frame discr with
                          | error _ => rw [h2] at hStep; cases hStep
                          | ok r =>
                              rw [h2] at hStep
                              dsimp only at hStep
                              cases hc : OpenMirTy.toClosedMirTy? r.2.1 with
                              | none => rw [hc] at hStep; cases hStep
                              | some mTy =>
                                  rw [hc] at hStep
                                  dsimp only at hStep
                                  have hStep := ite_fault_step hStep
                                  cases hV : r.1 with
                                  | scalar sv =>
                                      rw [hV] at hStep; dsimp only at hStep
                                      cases hTgt : evalSwitchBranches sv.width
                                          sv.bits tgts.otherwise
                                          tgts.branches with
                                      | error _ => rw [hTgt] at hStep; cases hStep
                                      | ok _ =>
                                          rw [hTgt] at hStep
                                          cases hStep
                                          have hd := evalOpenOperand_preserves_defId
                                            prog env ob frame discr r.1 r.2.1
                                            r.2.2 h2
                                          refine ⟨?_, hFrames.2⟩
                                          change ∃ b,
                                            openListGet? prog.bodies
                                                r.2.2.defId = some b ∧
                                              openBodyNoParam b = true
                                          rw [hd]
                                          exact hFrames.1
                                  | bool b =>
                                      rw [hV] at hStep; dsimp only at hStep
                                      cases hTgt : evalBoolSwitchBranches b
                                          tgts.otherwise tgts.branches with
                                      | error _ => rw [hTgt] at hStep; cases hStep
                                      | ok _ =>
                                          rw [hTgt] at hStep
                                          cases hStep
                                          have hd := evalOpenOperand_preserves_defId
                                            prog env ob frame discr r.1 r.2.1
                                            r.2.2 h2
                                          refine ⟨?_, hFrames.2⟩
                                          change ∃ b,
                                            openListGet? prog.bodies
                                                r.2.2.defId = some b ∧
                                              openBodyNoParam b = true
                                          rw [hd]
                                          exact hFrames.1
                                  | char c =>
                                      rw [hV] at hStep; dsimp only at hStep
                                      cases hTgt : evalCharSwitchBranches c
                                          tgts.otherwise tgts.branches with
                                      | error _ => rw [hTgt] at hStep; cases hStep
                                      | ok _ =>
                                          rw [hTgt] at hStep
                                          cases hStep
                                          have hd := evalOpenOperand_preserves_defId
                                            prog env ob frame discr r.1 r.2.1
                                            r.2.2 h2
                                          refine ⟨?_, hFrames.2⟩
                                          change ∃ b,
                                            openListGet? prog.bodies
                                                r.2.2.defId = some b ∧
                                              openBodyNoParam b = true
                                          rw [hd]
                                          exact hFrames.1
                                  | unit | enumVal _ _ | ordering _ | tuple _
                                  | bytes _ | ptr _ | slicePtr _ _ | rangeTo _
                                  | rangeFrom _ | array _ | optionVal _
                                  | range _ _ | vec _ _ _ | boxPtr _ _ =>
                                      rw [hV] at hStep; dsimp only at hStep
                                      cases hBr : tgts.branches with
                                      | nil =>
                                          rw [hBr] at hStep
                                          cases hStep
                                          have hd := evalOpenOperand_preserves_defId
                                            prog env ob frame discr r.1 r.2.1
                                            r.2.2 h2
                                          refine ⟨?_, hFrames.2⟩
                                          change ∃ b,
                                            openListGet? prog.bodies
                                                r.2.2.defId = some b ∧
                                              openBodyNoParam b = true
                                          rw [hd]
                                          exact hFrames.1
                                      | cons _ _ =>
                                          rw [hBr] at hStep; cases hStep
                      | assert cond exp _ tgt uw =>
                          rw [hTerm] at hStep
                          dsimp only at hStep
                          cases h2 : evalOpenOperand prog env ob frame cond with
                          | error _ => rw [h2] at hStep; cases hStep
                          | ok r =>
                              rw [h2] at hStep
                              dsimp only at hStep
                              have hd := evalOpenOperand_preserves_defId prog env
                                ob frame cond r.1 r.2.1 r.2.2 h2
                              have hrFr : FramesNoParam prog (r.2.2 :: restFrames) := by
                                refine ⟨?_, hFrames.2⟩
                                change ∃ b,
                                  openListGet? prog.bodies r.2.2.defId = some b ∧
                                    openBodyNoParam b = true
                                rw [hd]
                                exact hFrames.1
                              cases hVal : r.1 with
                              | bool b =>
                                  rw [hVal] at hStep
                                  dsimp only at hStep
                                  cases h3 : b == exp with
                                  | true =>
                                      rw [h3, if_true_eq] at hStep
                                      cases hStep; exact hrFr
                                  | false =>
                                      rw [h3, if_false_eq] at hStep
                                      exact openUnwindWith_preserves_framesNoParam
                                        prog restFrames s s.callerMem uw
                                        (some r.2.2) s' hFrames.2
                                        (fun cf hCf => by cases hCf; exact hrFr.1)
                                        hStep
                              | _ =>
                                  rw [hVal] at hStep
                                  dsimp only at hStep
                                  cases hStep
                      | call _ _ _ _ _ _ | traitCall _ _ _ _ _ _ _ _
                      | unsupported => rw [hTerm] at hStep; cases hStep

mutual
  /-- Reverse `.param`-absence preservation for single-step normalization. -/
  theorem normalizeOpenTyStep_noParam_rev (reg : TraitRegistry)
      (hWf : TraitRegistryWf reg = true) :
      ∀ ty : OpenMirTy,
        openMirTyNoParam (normalizeOpenTyStep reg ty) = true →
        openMirTyNoParam ty = true
    | .bool, _ | .int _ _, _ | .unit, _ | .never, _ | .char, _ | .ordering, _
    | .enum _, _ | .unsupported, _ => rfl
    | .param _, h => by cases h
    | .slice e, h => normalizeOpenTyStep_noParam_rev reg hWf e h
    | .array e _, h => normalizeOpenTyStep_noParam_rev reg hWf e h
    | .ref _ p, h => normalizeOpenTyStep_noParam_rev reg hWf p h
    | .rawPtr _ p, h => normalizeOpenTyStep_noParam_rev reg hWf p h
    | .tuple fs, h => normalizeOpenTyStepList_noParam_rev reg hWf fs h
    | .adt _ args, h => normalizeOpenTyStepList_noParam_rev reg hWf args h
    | .assocProj s tr args idx, h => by
        dsimp only [normalizeOpenTyStep] at h
        cases hRes : resolveAssocType reg (normalizeOpenTyStep reg s) tr
            (normalizeOpenTyStepList reg args) idx with
        | some rhs =>
            have hInfo := resolveAssocType_wf_info reg hWf
              (normalizeOpenTyStep reg s) tr
              (normalizeOpenTyStepList reg args) idx rhs hRes
            have hS := normalizeOpenTyStep_closed_subst reg hWf [] s hInfo.1
            have hA :=
              (normalizeOpenTyStepList_closed_subst
                reg hWf [] args hInfo.2.1).1
            exact bool_and_eq_true hS.1 hA
        | none =>
            rw [hRes] at h
            dsimp only [openMirTyNoParam] at h
            exact bool_and_eq_true
              (normalizeOpenTyStep_noParam_rev reg hWf s (bool_and_left h))
              (normalizeOpenTyStepList_noParam_rev reg hWf args
                (bool_and_right h))

  theorem normalizeOpenTyStepList_noParam_rev (reg : TraitRegistry)
        (hWf : TraitRegistryWf reg = true) :
        ∀ fs : List OpenMirTy,
          openMirTyListNoParam (normalizeOpenTyStepList reg fs) = true →
          openMirTyListNoParam fs = true
      | [], _ => rfl
      | x :: xs, h => by
          dsimp only [normalizeOpenTyStepList, openMirTyListNoParam] at h
          exact bool_and_eq_true
            (normalizeOpenTyStep_noParam_rev reg hWf x (bool_and_left h))
            (normalizeOpenTyStepList_noParam_rev reg hWf xs (bool_and_right h))
end

/-- `openTyListsNormEq` preserves `openMirTyListNoParam` from LHS to RHS. -/
theorem openTyListsNormEq_noParam (reg : TraitRegistry)
    (hWf : TraitRegistryWf reg = true) :
    ∀ xs ys : List OpenMirTy,
      openTyListsNormEq reg xs ys = true →
      openMirTyListNoParam xs = true →
      openMirTyListNoParam ys = true := by
  intro xs
  induction xs with
  | nil =>
      intro ys hEq _
      cases ys with
      | nil => rfl
      | cons _ _ => cases hEq
  | cons x xs ih =>
      intro ys hEq hNoP
      cases ys with
      | nil => cases hEq
      | cons y ys =>
          unfold openTyListsNormEq at hEq
          unfold openMirTyListNoParam at hNoP
          unfold openMirTyListNoParam
          have hBeq := openMirTy_beq_eq (bool_and_left hEq)
          rw [normalizeOpenTy_normFuel_eq_step reg hWf x,
            normalizeOpenTy_normFuel_eq_step reg hWf y] at hBeq
          have hXNoP := normalizeOpenTyStep_noParam reg hWf x
            (bool_and_left hNoP)
          rw [hBeq] at hXNoP
          exact bool_and_eq_true
            (normalizeOpenTyStep_noParam_rev reg hWf y hXNoP)
            (ih ys (bool_and_right hEq) (bool_and_right hNoP))

/-- Every `wc ∈ wcs` satisfies `WhereClause.isClosed wc = true` when
`WhereClause.isClosedList wcs = true`. -/
theorem whereClause_isClosedList_mem :
    ∀ (wcs : List WhereClause) (wc : WhereClause),
      WhereClause.isClosedList wcs = true → wc ∈ wcs →
      WhereClause.isClosed wc = true
  | [], _, _, h => by cases h
  | w :: ws, wc, hCl, hMem => by
      dsimp only [WhereClause.isClosedList] at hCl
      cases hMem with
      | head _ => exact bool_and_left hCl
      | tail _ hTail =>
          exact whereClause_isClosedList_mem ws wc (bool_and_right hCl) hTail

/-- Elementwise `noParam` preservation for
`List.map (normalizeOpenTy reg normFuel)`. -/
theorem map_normalizeOpenTy_noParam (reg : TraitRegistry)
    (hRegWf : TraitRegistryWf reg = true) :
    ∀ ts : List OpenMirTy,
      openMirTyListNoParam ts = true →
      openMirTyListNoParam (ts.map (normalizeOpenTy reg normFuel)) = true := by
  intro ts hTs
  induction ts with
  | nil => rfl
  | cons a as ih =>
      change (openMirTyNoParam a && openMirTyListNoParam as) = true at hTs
      change (openMirTyNoParam (normalizeOpenTy reg normFuel a) &&
          openMirTyListNoParam (as.map (normalizeOpenTy reg normFuel))) = true
      rw [normalizeOpenTy_normFuel_eq_step reg hRegWf a]
      exact bool_and_eq_true
        (normalizeOpenTyStep_noParam reg hRegWf a (bool_and_left hTs))
        (ih (bool_and_right hTs))

/-- `concreteTraitCallStep` agrees across `env₁, env₂` when inputs have no
`.param`. -/
theorem concreteTraitCallStep_noParam_congr (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env₁ env₂ : OpenExecEnv)
    (hAdt : env₁.typeSpecs.adtSpecs = env₂.typeSpecs.adtSpecs)
    (hAssoc : ∀ s tr as idx, openMirTyNoParam s = true →
      openMirTyListNoParam as = true →
      env₁.typeSpecs.assocSpecs s tr as idx =
        env₂.typeSpecs.assocSpecs s tr as idx)
    (s : OpenState) (ob : OpenBody) (frame : OpenFrameState)
    (restFrames : List OpenFrameState) (selfN : OpenMirTy) (tr : TraitDefId)
    (argsN : List OpenMirTy) (mIdx : AssocItemIdx) (args : List OpenOperand)
    (hAArgs : args.all openOperandNoParam = true)
    (dst : OpenPlace) (tgt : Option BasicBlockId) (uw : UnwindAction) :
    concreteTraitCallStep prog env₁ s ob frame restFrames selfN tr argsN mIdx
        args dst tgt uw =
      concreteTraitCallStep prog env₂ s ob frame restFrames selfN tr argsN mIdx
        args dst tgt uw := by
  unfold concreteTraitCallStep
  rw [hRegWf, if_not_true_eq]
  rw [if_not_true_eq]
  dsimp only
  cases hL : lookupImpl prog.traitRegistry ⟨selfN, tr, argsN⟩ with
  | none => rfl
  | some binding =>
      dsimp only
      cases hB0 : (!Nat.beq binding.implTyParamCount 0) with
      | true =>
          rw [if_true_eq]
          rw [if_true_eq]
      | false =>
          rw [if_false_eq]
          rw [if_false_eq]
          cases hM : lookupImplMethod binding.methodDefIds mIdx with
          | none => rfl
          | some calleeId =>
              dsimp only
              cases hCB : openListGet? prog.bodies calleeId with
              | none => rfl
              | some calleeBody =>
                  dsimp only
                  cases hBad :
                      (!Nat.beq calleeBody.sig.tyParamCount 0 ||
                        !openBodyNoParam calleeBody ||
                        !openSigMatchesLocals prog calleeBody ||
                        calleeBody.basicBlocks.isEmpty) with
                  | true =>
                      rw [if_true_eq]
                      rw [if_true_eq]
                  | false =>
                      rw [if_false_eq]
                      rw [if_false_eq]
                      have hNoP_c : openBodyNoParam calleeBody = true :=
                        not_bool_eq_false
                          (bool_or_eq_false_right
                            (bool_or_eq_false_left
                              (bool_or_eq_false_left hBad)))
                      cases hProj : (!dst.projection.isEmpty) with
                      | true =>
                          rw [if_true_eq]
                          rw [if_true_eq]
                      | false =>
                          rw [if_false_eq]
                          rw [if_false_eq]
                          cases openListGet? ob.locals dst.localId with
                          | none => rfl
                          | some dstTy =>
                              dsimp only
                              cases
                                  (!OpenMirTy.beq
                                    (normalizeOpenTy prog.traitRegistry normFuel
                                      dstTy)
                                    (normalizeOpenTy prog.traitRegistry normFuel
                                      calleeBody.sig.retTy)) with
                              | true =>
                                  rw [if_true_eq]
                                  rw [if_true_eq]
                              | false =>
                                  rw [if_false_eq]
                                  rw [if_false_eq]
                                  rw [evalOpenOperands_noParam_congr prog hRegWf
                                    env₁ env₂ hAdt hAssoc ob frame args hAArgs]
                                  cases evalOpenOperands prog env₂ ob frame args
                                    with
                                  | error _ => rfl
                                  | ok r =>
                                      dsimp only
                                      rw [initOpenLocals_noParam_congr prog
                                        hRegWf env₁ env₂ hAdt hAssoc calleeBody
                                        hNoP_c r.1]

/-- `concreteTraitCallStep` preserves `FramesNoParam prog` whenever it steps.
-/
theorem concreteTraitCallStep_preserves_framesNoParam (prog : OpenProgram)
    (env : OpenExecEnv) (s : OpenState) (defId : DefId) (ob : OpenBody)
    (hB : openListGet? prog.bodies defId = some ob)
    (hNoP0 : openBodyNoParam ob = true)
    (frame : OpenFrameState) (hFrameDef : frame.defId = defId)
    (restFrames : List OpenFrameState) (hRest : FramesNoParam prog restFrames)
    (selfN : OpenMirTy) (tr : TraitDefId) (argsN : List OpenMirTy)
    (mIdx : AssocItemIdx) (args : List OpenOperand)
    (dst : OpenPlace) (tgt : Option BasicBlockId) (uw : UnwindAction)
    (s' : OpenState)
    (hStep : concreteTraitCallStep prog env s ob frame restFrames selfN tr
        argsN mIdx args dst tgt uw = .step s') :
    FramesNoParam prog s'.frames := by
  unfold concreteTraitCallStep at hStep
  cases hReg : (!TraitRegistryWf prog.traitRegistry) with
  | true => rw [hReg, if_true_eq] at hStep; cases hStep
  | false =>
      rw [hReg, if_false_eq] at hStep
      dsimp only at hStep
      cases hL : lookupImpl prog.traitRegistry ⟨selfN, tr, argsN⟩ with
      | none => rw [hL] at hStep; cases hStep
      | some binding =>
          rw [hL] at hStep
          dsimp only at hStep
          cases hB0 : (!Nat.beq binding.implTyParamCount 0) with
          | true => rw [hB0, if_true_eq] at hStep; cases hStep
          | false =>
              rw [hB0, if_false_eq] at hStep
              cases hM : lookupImplMethod binding.methodDefIds mIdx with
              | none => rw [hM] at hStep; cases hStep
              | some calleeId =>
                  rw [hM] at hStep
                  dsimp only at hStep
                  cases hCB : openListGet? prog.bodies calleeId with
                  | none => rw [hCB] at hStep; cases hStep
                  | some calleeBody =>
                      rw [hCB] at hStep
                      dsimp only at hStep
                      cases hBad :
                          (!Nat.beq calleeBody.sig.tyParamCount 0 ||
                            !openBodyNoParam calleeBody ||
                            !openSigMatchesLocals prog calleeBody ||
                            calleeBody.basicBlocks.isEmpty) with
                      | true => rw [hBad, if_true_eq] at hStep; cases hStep
                      | false =>
                          rw [hBad, if_false_eq] at hStep
                          have hNoP_c : openBodyNoParam calleeBody = true :=
                            not_bool_eq_false
                              (bool_or_eq_false_right
                                (bool_or_eq_false_left
                                  (bool_or_eq_false_left hBad)))
                          cases hProj : (!dst.projection.isEmpty) with
                          | true => rw [hProj, if_true_eq] at hStep; cases hStep
                          | false =>
                              rw [hProj, if_false_eq] at hStep
                              cases hDst : openListGet? ob.locals dst.localId
                                with
                              | none => rw [hDst] at hStep; cases hStep
                              | some dstTy =>
                                  rw [hDst] at hStep
                                  dsimp only at hStep
                                  cases hRetEq :
                                      (!OpenMirTy.beq
                                        (normalizeOpenTy prog.traitRegistry
                                          normFuel dstTy)
                                        (normalizeOpenTy prog.traitRegistry
                                          normFuel calleeBody.sig.retTy)) with
                                  | true =>
                                      rw [hRetEq, if_true_eq] at hStep
                                      cases hStep
                                  | false =>
                                      rw [hRetEq, if_false_eq] at hStep
                                      cases hOps :
                                          evalOpenOperands prog env ob frame
                                            args with
                                      | error _ =>
                                          rw [hOps] at hStep; cases hStep
                                      | ok r =>
                                          rw [hOps] at hStep
                                          dsimp only at hStep
                                          cases hInit :
                                              initOpenLocals prog env calleeBody
                                                r.1 with
                                          | none =>
                                              rw [hInit] at hStep; cases hStep
                                          | some ls =>
                                              rw [hInit] at hStep
                                              cases hStep
                                              have hDef1 :=
                                                evalOpenOperands_preserves_defId
                                                  prog env ob args frame r.1 r.2
                                                  hOps
                                              have hFr1 :
                                                  ∃ b,
                                                    openListGet? prog.bodies
                                                        r.2.defId = some b ∧
                                                      openBodyNoParam b =
                                                        true := by
                                                rw [hDef1, hFrameDef]
                                                exact ⟨ob, hB, hNoP0⟩
                                              exact
                                                ⟨⟨calleeBody, hCB, hNoP_c⟩,
                                                 hFr1, hRest⟩

/-- `AssumeGuaranteeTraitCall` agrees across `env₁, env₂` when `selfTy`,
`trArgs`, `args`, and `ob` have no `.param`. -/
theorem assumeGuaranteeTraitCall_noParam_congr (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env₁ env₂ : OpenExecEnv)
    (hContracts : env₁.traitContracts = env₂.traitContracts)
    (hAdt : env₁.typeSpecs.adtSpecs = env₂.typeSpecs.adtSpecs)
    (hAssoc : ∀ s tr as idx, openMirTyNoParam s = true →
      openMirTyListNoParam as = true →
      env₁.typeSpecs.assocSpecs s tr as idx =
        env₂.typeSpecs.assocSpecs s tr as idx)
    (wcs : List WhereClause) (s : OpenState) (ob : OpenBody)
    (hNoP0 : openBodyNoParam ob = true) (frame : OpenFrameState)
    (restFrames : List OpenFrameState) (selfTy : OpenMirTy)
    (hASelf : openMirTyNoParam selfTy = true) (tr : TraitDefId)
    (trArgs : List OpenMirTy) (hATrArgs : openMirTyListNoParam trArgs = true)
    (mIdx : AssocItemIdx) (args : List OpenOperand)
    (hAArgs : args.all openOperandNoParam = true)
    (dst : OpenPlace) (tgt : Option BasicBlockId) (uw : UnwindAction)
    (res : StepResult OpenState TerminalOut) :
    AssumeGuaranteeTraitCall prog env₁ wcs s ob frame restFrames selfTy tr
        trArgs mIdx args dst tgt uw res ↔
      AssumeGuaranteeTraitCall prog env₂ wcs s ob frame restFrames selfTy tr
        trArgs mIdx args dst tgt uw res := by
  have hSelfN :
      openMirTyNoParam (normalizeOpenTy prog.traitRegistry normFuel selfTy) =
        true := by
    rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf selfTy]
    exact normalizeOpenTyStep_noParam prog.traitRegistry hRegWf selfTy hASelf
  have hArgsN :
      openMirTyListNoParam
          (trArgs.map (normalizeOpenTy prog.traitRegistry normFuel)) = true :=
    map_normalizeOpenTy_noParam prog.traitRegistry hRegWf trArgs hATrArgs
  unfold AssumeGuaranteeTraitCall
  dsimp only
  rw [hContracts]
  refine prop_ite_congr_same (fun _ => ?_)
  cases env₂.traitContracts tr with
  | none => exact Iff.rfl
  | some contract =>
      refine prop_ite_congr_same (fun _ => ?_)
      cases lookupMethodSpec contract.methodSpecs mIdx with
      | none => exact Iff.rfl
      | some mspec =>
          dsimp only
          refine prop_ite_congr_same (fun _ => ?_)
          cases hDst : openListGet? ob.locals dst.localId with
          | none => exact Iff.rfl
          | some dstTy =>
              dsimp only
              refine prop_ite_congr_same (fun hBadR => ?_)
              have hDstEq := openMirTy_beq_eq
                (not_bool_eq_false (bool_or_eq_false_left hBadR))
              have hDstNoP :
                  openMirTyNoParam
                      (normalizeOpenTy prog.traitRegistry normFuel dstTy) =
                    true := by
                rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf
                  dstTy]
                exact normalizeOpenTyStep_noParam prog.traitRegistry hRegWf
                  dstTy
                  (openListGet?_openBodyNoParam_local ob hNoP0 dst.localId
                    dstTy hDst)
              have hRetNoP :
                  openMirTyNoParam
                      (OpenMirTy.substAndNormalize prog.traitRegistry normFuel
                        (normalizeOpenTy prog.traitRegistry normFuel selfTy ::
                          trArgs.map
                            (normalizeOpenTy prog.traitRegistry normFuel))
                        mspec.sig.retTy) = true := by
                rw [← hDstEq]
                exact hDstNoP
              have hNotArgs := bool_or_eq_false_right hBadR
              rw [hSelfN, hArgsN] at hNotArgs
              have hArgsNoP :
                  openMirTyListNoParam
                      (mspec.sig.argTys.map
                        (OpenMirTy.substAndNormalize prog.traitRegistry
                          normFuel
                          (normalizeOpenTy prog.traitRegistry normFuel selfTy ::
                            trArgs.map
                              (normalizeOpenTy prog.traitRegistry normFuel)))) =
                    true :=
                not_bool_eq_false
                  (bool_or_eq_false_left (bool_or_eq_false_left hNotArgs))
              have hSpecS := evalOpenTySpec_noParam_congr prog hRegWf env₁ env₂
                hAdt hAssoc (normalizeOpenTy prog.traitRegistry normFuel selfTy)
                hSelfN
              have hSpecAs :=
                evalNormOpenTySpecList_noParam_congr
                  env₁.typeSpecs env₂.typeSpecs hAdt hAssoc
                  (trArgs.map (normalizeOpenTy prog.traitRegistry normFuel))
                  hArgsN
              have hSpecAss :=
                resolveTraitAssocSpecsAux_noParam_congr prog hRegWf env₁ env₂
                  hAdt hAssoc
                  (normalizeOpenTy prog.traitRegistry normFuel selfTy) tr
                  (trArgs.map (normalizeOpenTy prog.traitRegistry normFuel))
                  hSelfN hArgsN 0 contract.assocTypeCount
              have hOps := evalOpenOperands_noParam_congr prog hRegWf env₁ env₂
                hAdt hAssoc ob frame args hAArgs
              unfold resolveTraitAssocSpecs
              rw [hSpecS, hSpecAs, hSpecAss]
              cases evalOpenTySpec prog.traitRegistry normFuel env₂.typeSpecs
                  (normalizeOpenTy prog.traitRegistry normFuel selfTy) with
              | none => exact Iff.rfl
              | some _ =>
                  cases evalNormOpenTySpecList env₂.typeSpecs
                      (trArgs.map
                        (normalizeOpenTy prog.traitRegistry normFuel)) with
                  | none => exact Iff.rfl
                  | some _ =>
                      cases hAss2 : resolveTraitAssocSpecsAux prog env₂
                          (normalizeOpenTy prog.traitRegistry normFuel selfTy) tr
                          (trArgs.map
                            (normalizeOpenTy prog.traitRegistry normFuel))
                          0 contract.assocTypeCount with
                      | none => exact Iff.rfl
                      | some _ =>
                          rw [hOps]
                          cases evalOpenOperands prog env₂ ob frame args with
                          | error _ => exact Iff.rfl
                          | ok r =>
                              dsimp only
                              have hCamEq := checkOpenArgsMatch_noParam_congr
                                prog hRegWf env₁ env₂ hAdt hAssoc r.1 _ hArgsNoP
                              rw [hCamEq]
                              refine prop_ite_congr_same (fun _ => ?_)
                              refine prop_or_congr Iff.rfl
                                (prop_and_congr Iff.rfl (prop_exists_congr ?_))
                              intro out
                              refine prop_and_congr Iff.rfl ?_
                              cases out with
                              | unwound _ => exact Iff.rfl
                              | aborted _ => exact Iff.rfl
                              | returned rv =>
                                  dsimp only
                                  have hCvEq := checkOpenVal_noParam_congr prog
                                    hRegWf env₁ env₂ hAdt hAssoc rv.ret _
                                    hRetNoP
                                  rw [hCvEq]
                                  refine prop_ite_congr_same (fun _ => ?_)
                                  cases tgt with
                                  | none => exact Iff.rfl
                                  | some _ =>
                                      dsimp only
                                      rw [writeOpenPlace_noParam_congr prog
                                        hRegWf env₁ env₂ hAdt hAssoc ob hNoP0
                                        r.2 dst rv.ret]

/-- `AssumeGuaranteeTraitCall` preserves `FramesNoParam prog` when it steps. -/
theorem assumeGuaranteeTraitCall_preserves_framesNoParam (prog : OpenProgram)
    (env : OpenExecEnv) (wcs : List WhereClause) (s : OpenState)
    (defId : DefId) (ob : OpenBody)
    (hB : openListGet? prog.bodies defId = some ob)
    (hNoP0 : openBodyNoParam ob = true)
    (frame : OpenFrameState) (hFrameDef : frame.defId = defId)
    (restFrames : List OpenFrameState) (hRest : FramesNoParam prog restFrames)
    (selfTy : OpenMirTy) (tr : TraitDefId) (trArgs : List OpenMirTy)
    (mIdx : AssocItemIdx) (args : List OpenOperand)
    (dst : OpenPlace) (tgt : Option BasicBlockId) (uw : UnwindAction)
    (s' : OpenState)
    (hStep : AssumeGuaranteeTraitCall prog env wcs s ob frame restFrames
        selfTy tr trArgs mIdx args dst tgt uw (.step s')) :
    FramesNoParam prog s'.frames := by
  unfold AssumeGuaranteeTraitCall at hStep
  dsimp only at hStep
  have hStep := prop_ite_step_rhs hStep
  cases hTc : env.traitContracts tr with
  | none => rw [hTc] at hStep; cases hStep
  | some contract =>
      rw [hTc] at hStep
      dsimp only at hStep
      have hStep := prop_ite_step_rhs hStep
      cases hMs : lookupMethodSpec contract.methodSpecs mIdx with
      | none => rw [hMs] at hStep; cases hStep
      | some mspec =>
          rw [hMs] at hStep
          dsimp only at hStep
          have hStep := prop_ite_step_rhs hStep
          cases hDst : openListGet? ob.locals dst.localId with
          | none => rw [hDst] at hStep; cases hStep
          | some _ =>
              rw [hDst] at hStep
              dsimp only at hStep
              rw [ite_eq_right_of_eq_false _ _
                (eq_false (fun hBad => by
                  rw [ite_eq_left_of_eq_true _ _ (eq_true hBad)] at hStep
                  cases hStep))] at hStep
              cases hSS : evalOpenTySpec prog.traitRegistry normFuel
                  env.typeSpecs
                  (normalizeOpenTy prog.traitRegistry normFuel selfTy)
                with
              | none => rw [hSS] at hStep; cases hStep
              | some _ =>
                  rw [hSS] at hStep
                  cases hSA : evalNormOpenTySpecList env.typeSpecs
                      (trArgs.map
                        (normalizeOpenTy prog.traitRegistry normFuel))
                    with
                  | none => rw [hSA] at hStep; cases hStep
                  | some _ =>
                      rw [hSA] at hStep
                      cases hSAss : resolveTraitAssocSpecs prog env
                          (normalizeOpenTy prog.traitRegistry normFuel
                            selfTy)
                          tr
                          (trArgs.map
                            (normalizeOpenTy prog.traitRegistry
                              normFuel))
                          contract.assocTypeCount with
                      | none => rw [hSAss] at hStep; cases hStep
                      | some _ =>
                          rw [hSAss] at hStep
                          cases hOps : evalOpenOperands prog env ob
                              frame args with
                          | error _ => rw [hOps] at hStep; cases hStep
                          | ok r =>
                              rw [hOps] at hStep
                              dsimp only at hStep
                              have hStep := prop_ite_step_rhs hStep
                              cases hStep with
                              | inl hL => cases hL.2
                              | inr hR =>
                                  let ⟨_, out, _, hOut⟩ := hR
                                  have hDef1 :=
                                    evalOpenOperands_preserves_defId
                                      prog env ob args frame r.1 r.2
                                      hOps
                                  have hFr1 :
                                      ∃ b,
                                        openListGet? prog.bodies
                                            r.2.defId = some b ∧
                                          openBodyNoParam b = true := by
                                    rw [hDef1, hFrameDef]
                                    exact ⟨ob, hB, hNoP0⟩
                                  cases out with
                                  | unwound cm' =>
                                      exact
                                        openUnwindWith_preserves_framesNoParam
                                          prog restFrames s cm' uw
                                          (some r.2) s' hRest
                                          (fun cf hCf => by
                                            cases hCf; exact hFr1)
                                          (Eq.symm hOut)
                                  | aborted _ => cases hOut
                                  | returned rv =>
                                      cases rv with
                                      | mk retVal cm' =>
                                          dsimp only at hOut
                                          revert hOut
                                          refine prop_ite_step_rhs_imp ?_
                                          intro hOut
                                          cases tgt with
                                          | none => cases hOut
                                          | some nextBlk =>
                                                          dsimp only at hOut
                                                          cases hWr :
                                                              writeOpenPlace
                                                                prog env ob r.2
                                                                dst retVal with
                                                          | error _ =>
                                                              rw [hWr] at hOut
                                                              cases hOut
                                                          | ok f₂ =>
                                                              rw [hWr] at hOut
                                                              cases hOut
                                                              have hDef2 :=
                                                                writeOpenPlace_preserves_defId
                                                                  prog env ob
                                                                  r.2 dst retVal
                                                                  f₂ hWr
                                                              have hFr2 :
                                                                  ∃ b,
                                                                    openListGet?
                                                                        prog.bodies
                                                                        f₂.defId =
                                                                      some b ∧
                                                                      openBodyNoParam
                                                                        b =
                                                                        true := by
                                                                rw [hDef2]
                                                                exact hFr1
                                                              exact
                                                                ⟨hFr2, hRest⟩

/-- `OpenStep` preserves `FramesNoParam prog` and agrees across `env₁, env₂`
when `traitContracts`, `adtSpecs`, and `assocSpecs` (on `noParam` types) agree.
-/
theorem openStep_noParam_congr (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env₁ env₂ : OpenExecEnv)
    (hContracts : env₁.traitContracts = env₂.traitContracts)
    (hAdt : env₁.typeSpecs.adtSpecs = env₂.typeSpecs.adtSpecs)
    (hAssoc : ∀ s tr as idx, openMirTyNoParam s = true →
      openMirTyListNoParam as = true →
      env₁.typeSpecs.assocSpecs s tr as idx =
        env₂.typeSpecs.assocSpecs s tr as idx)
    (wcs : List WhereClause) (s : OpenState)
    (hFrames : FramesNoParam prog s.frames)
    (res : StepResult OpenState TerminalOut) :
    (OpenStep prog env₁ wcs s res ↔ OpenStep prog env₂ wcs s res) ∧
    (∀ s', res = .step s' → OpenStep prog env₁ wcs s (.step s') →
      FramesNoParam prog s'.frames) := by
  have hDet := openEvalDetStep_noParam_congr prog hRegWf env₁ env₂ hAdt hAssoc s
    hFrames
  unfold OpenStep OpenStepOnFrames
  cases hFr : s.frames with
  | nil =>
      refine ⟨Iff.rfl, ?_⟩
      intro s' hEq hStep
      subst hEq
      cases hStep
  | cons frame restFrames =>
      rw [hFr] at hFrames
      dsimp only
      let ⟨ob0, hGet0, hNoP0⟩ := hFrames.1
      unfold OpenStepOnBodyOpt
      cases hB : openListGet? prog.bodies frame.defId with
      | none =>
          refine ⟨Iff.rfl, ?_⟩
          intro s' hEq hStep
          subst hEq
          cases hStep
      | some ob =>
          dsimp only
          have hEqOb : ob = ob0 := by
            rw [hB] at hGet0; cases hGet0; rfl
          subst hEqOb
          unfold OpenStepOnBlockOpt
          cases hBb : openListGet? ob.basicBlocks frame.blockIdx with
          | none =>
              refine ⟨Iff.rfl, ?_⟩
              intro s' hEq hStep
              subst hEq
              cases hStep
          | some bb =>
              dsimp only
              unfold OpenStepOnStmtEnd
              cases hEnd : Nat.beq frame.stmtIdx bb.statements.length with
              | false =>
                  dsimp only
                  refine ⟨by rw [hDet], ?_⟩
                  intro s' hEq hStep
                  subst hEq
                  exact openEvalDetStep_preserves_framesNoParam prog env₁ s s'
                    (by rw [hFr]; exact hFrames) (Eq.symm hStep)
              | true =>
                  dsimp only
                  unfold OpenStepOnTerm
                  cases hTerm : bb.terminator with
                  | goto _ | switchInt _ _ | return_ | unreachable
                  | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ _
                  | unsupported =>
                      dsimp only
                      refine ⟨by rw [hDet], ?_⟩
                      intro s' hEq hStep
                      subst hEq
                      exact openEvalDetStep_preserves_framesNoParam prog env₁ s
                        s' (by rw [hFr]; exact hFrames) (Eq.symm hStep)
                  | traitCall selfTy tr trArgs mIdx args dst tgt uw =>
                      dsimp only
                      have hBbNoP : (bb.statements.all openStmtNoParam &&
                          openTermNoParam bb.terminator) = true := by
                        rw [← getElem?_eq_openListGet?] at hBb
                        exact all_getElem?_eq_true
                          (p := fun b : OpenBasicBlock =>
                            b.statements.all openStmtNoParam &&
                              openTermNoParam b.terminator)
                          (openBodyNoParam_parts ob hNoP0).2.2.2.2 hBb
                      have hTermNoP := bool_and_right hBbNoP
                      rw [hTerm] at hTermNoP
                      unfold openTermNoParam at hTermNoP
                      have hADst := bool_and_right hTermNoP
                      have hAArgs := bool_and_right (bool_and_left hTermNoP)
                      have hATrArgs := bool_and_right
                        (bool_and_left (bool_and_left hTermNoP))
                      have hASelf := bool_and_left
                        (bool_and_left (bool_and_left hTermNoP))
                      cases hCl : (OpenMirTy.isClosed
                          (normalizeOpenTy prog.traitRegistry normFuel selfTy)
                          && OpenMirTy.isClosedList
                            (trArgs.map
                              (normalizeOpenTy prog.traitRegistry normFuel)))
                          with
                      | true =>
                          rw [prop_ite_true]
                          rw [prop_ite_true]
                          have hConc := concreteTraitCallStep_noParam_congr prog
                            hRegWf env₁ env₂ hAdt hAssoc s ob frame restFrames
                            (normalizeOpenTy prog.traitRegistry normFuel selfTy)
                            tr
                            (trArgs.map
                              (normalizeOpenTy prog.traitRegistry normFuel))
                            mIdx args hAArgs dst tgt uw
                          refine ⟨by rw [hConc], ?_⟩
                          intro s' hEq hStep
                          subst hEq
                          rw [prop_ite_true] at hStep
                          exact concreteTraitCallStep_preserves_framesNoParam
                            prog env₁ s frame.defId ob hB hNoP0 frame rfl
                            restFrames hFrames.2
                            (normalizeOpenTy prog.traitRegistry normFuel selfTy)
                            tr
                            (trArgs.map
                              (normalizeOpenTy prog.traitRegistry normFuel))
                            mIdx args dst tgt uw s' (Eq.symm hStep)
                      | false =>
                          rw [prop_ite_false]
                          rw [prop_ite_false]
                          refine ⟨assumeGuaranteeTraitCall_noParam_congr prog
                            hRegWf env₁ env₂ hContracts hAdt hAssoc wcs s ob
                            hNoP0 frame restFrames selfTy hASelf tr trArgs
                            hATrArgs mIdx args hAArgs dst tgt uw res, ?_⟩
                          intro s' hEq hStep
                          subst hEq
                          rw [prop_ite_false] at hStep
                          exact assumeGuaranteeTraitCall_preserves_framesNoParam
                            prog env₁ wcs s frame.defId ob hB hNoP0 frame rfl
                            restFrames hFrames.2 selfTy tr trArgs mIdx args dst
                            tgt uw s' hStep

/-- `OpenReaches` transfers across `env₁, env₂` from any state satisfying
`FramesNoParam prog`. -/
theorem openReaches_noParam_congr (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env₁ env₂ : OpenExecEnv)
    (hContracts : env₁.traitContracts = env₂.traitContracts)
    (hAdt : env₁.typeSpecs.adtSpecs = env₂.typeSpecs.adtSpecs)
    (hAssoc : ∀ s tr as idx, openMirTyNoParam s = true →
      openMirTyListNoParam as = true →
      env₁.typeSpecs.assocSpecs s tr as idx =
        env₂.typeSpecs.assocSpecs s tr as idx)
    (wcs : List WhereClause) {s₀ s : OpenState}
    (hReach : OpenReaches prog env₁ wcs s₀ s)
    (hFrames : FramesNoParam prog s₀.frames) :
    OpenReaches prog env₂ wcs s₀ s ∧ FramesNoParam prog s.frames := by
  induction hReach with
  | refl s₁ => exact ⟨.refl s₁, hFrames⟩
  | @step s₁ s₂ s₃ hStep _ ih =>
      have hC := openStep_noParam_congr prog hRegWf env₁ env₂ hContracts hAdt
        hAssoc wcs s₁ hFrames (.step s₂)
      have hFr2 := hC.2 s₂ rfl hStep
      have hStep2 := hC.1.mp hStep
      let ⟨hTail, hFr3⟩ := ih hFr2
      exact ⟨.step hStep2 hTail, hFr3⟩

/-- `OpenWellFormed` transfers across `env₁, env₂` when the entry body satisfies
`openBodyNoParam = true`. -/
theorem openWellFormed_noParam_congr (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env₁ env₂ : OpenExecEnv)
    (hContracts : env₁.traitContracts = env₂.traitContracts)
    (hAdt : env₁.typeSpecs.adtSpecs = env₂.typeSpecs.adtSpecs)
    (hAssoc : ∀ s tr as idx, openMirTyNoParam s = true →
      openMirTyListNoParam as = true →
      env₁.typeSpecs.assocSpecs s tr as idx =
        env₂.typeSpecs.assocSpecs s tr as idx)
    (wcs : List WhereClause) (q : Query) (ob : OpenBody)
    (hGet : openListGet? prog.bodies prog.entryDefId = some ob)
    (hNoP : openBodyNoParam ob = true)
    (hWf : OpenWellFormed prog env₁ wcs q) :
    OpenWellFormed prog env₂ wcs q := by
  have hInit := openInitState_noParam_congr prog hRegWf env₁ env₂ hAdt hAssoc ob
    hGet hNoP q
  constructor
  · let ⟨s₀, hI1, hProg⟩ := hWf.1
    refine ⟨s₀, by rw [← hInit]; exact hI1, ?_⟩
    intro s hReach2
    have hFr0 := openInitState_framesNoParam prog env₁ q s₀ ⟨ob, hGet, hNoP⟩ hI1
    have hSymAssoc : ∀ st tr as idx, openMirTyNoParam st = true →
        openMirTyListNoParam as = true →
        env₂.typeSpecs.assocSpecs st tr as idx =
          env₁.typeSpecs.assocSpecs st tr as idx :=
      fun st tr as idx h1 h2 => Eq.symm (hAssoc st tr as idx h1 h2)
    let ⟨hReach1, hFrS⟩ := openReaches_noParam_congr prog hRegWf env₂ env₁
      (Eq.symm hContracts) (Eq.symm hAdt) hSymAssoc wcs hReach2 hFr0
    let ⟨res, hStep1⟩ := hProg s hReach1
    have hC := openStep_noParam_congr prog hRegWf env₁ env₂ hContracts hAdt
      hAssoc wcs s hFrS res
    exact ⟨res, hC.1.mp hStep1⟩
  · intro s₀ hI2 s k hReach2 hFault2
    rw [← hInit] at hI2
    have hFr0 := openInitState_framesNoParam prog env₁ q s₀ ⟨ob, hGet, hNoP⟩ hI2
    have hSymAssoc : ∀ st tr as idx, openMirTyNoParam st = true →
        openMirTyListNoParam as = true →
        env₂.typeSpecs.assocSpecs st tr as idx =
          env₁.typeSpecs.assocSpecs st tr as idx :=
      fun st tr as idx h1 h2 => Eq.symm (hAssoc st tr as idx h1 h2)
    let ⟨hReach1, hFrS⟩ := openReaches_noParam_congr prog hRegWf env₂ env₁
      (Eq.symm hContracts) (Eq.symm hAdt) hSymAssoc wcs hReach2 hFr0
    have hC := openStep_noParam_congr prog hRegWf env₁ env₂ hContracts hAdt
      hAssoc wcs s hFrS (.fault k)
    exact hWf.2 s₀ hI2 s k hReach1 (hC.1.mpr hFault2)

/-- `OpenBehavior` transfers backward from `env₂` to `env₁` when the entry body
satisfies `openBodyNoParam = true`. -/
theorem openBehavior_noParam_congr (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env₁ env₂ : OpenExecEnv)
    (hContracts : env₁.traitContracts = env₂.traitContracts)
    (hAdt : env₁.typeSpecs.adtSpecs = env₂.typeSpecs.adtSpecs)
    (hAssoc : ∀ s tr as idx, openMirTyNoParam s = true →
      openMirTyListNoParam as = true →
      env₁.typeSpecs.assocSpecs s tr as idx =
        env₂.typeSpecs.assocSpecs s tr as idx)
    (wcs : List WhereClause) (q : Query) (out : TerminalOut) (ob : OpenBody)
    (hGet : openListGet? prog.bodies prog.entryDefId = some ob)
    (hNoP : openBodyNoParam ob = true)
    (hBeh : OpenBehavior prog env₂ wcs q out) :
    OpenBehavior prog env₁ wcs q out := by
  have hInit := openInitState_noParam_congr prog hRegWf env₁ env₂ hAdt hAssoc ob
    hGet hNoP q
  let ⟨s₀, s, hI2, hReach2, hStep2⟩ := hBeh
  rw [← hInit] at hI2
  have hFr0 := openInitState_framesNoParam prog env₁ q s₀ ⟨ob, hGet, hNoP⟩ hI2
  have hSymAssoc : ∀ st tr as idx, openMirTyNoParam st = true →
      openMirTyListNoParam as = true →
      env₂.typeSpecs.assocSpecs st tr as idx =
        env₁.typeSpecs.assocSpecs st tr as idx :=
    fun st tr as idx h1 h2 => Eq.symm (hAssoc st tr as idx h1 h2)
  let ⟨hReach1, hFrS⟩ := openReaches_noParam_congr prog hRegWf env₂ env₁
    (Eq.symm hContracts) (Eq.symm hAdt) hSymAssoc wcs hReach2 hFr0
  have hC := openStep_noParam_congr prog hRegWf env₁ env₂ hContracts hAdt
    hAssoc wcs s hFrS (.done out)
  exact ⟨s₀, s, hI2, hReach1, hC.1.mpr hStep2⟩

/-- Directional congruence for `SatisfiesTraitSemDepth` across `env₁, env₂`
agreeing on `traitContracts`, `adtSpecs`, and `assocSpecs` (on `noParam` types).
-/
theorem satisfiesTraitSemDepth_noParam_congr_dir (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true) :
    ∀ (d : Nat) (env₁ env₂ : OpenExecEnv),
      env₁.traitContracts = env₂.traitContracts →
      env₁.typeSpecs.adtSpecs = env₂.typeSpecs.adtSpecs →
      (∀ s tr as idx, openMirTyNoParam s = true →
        openMirTyListNoParam as = true →
        env₁.typeSpecs.assocSpecs s tr as idx =
          env₂.typeSpecs.assocSpecs s tr as idx) →
      ∀ (selfTy : OpenMirTy) (tr : TraitDefId) (traitArgs : List OpenMirTy)
        (contract : TraitContract),
        SatisfiesTraitSemDepth prog env₁ d selfTy tr traitArgs contract →
        SatisfiesTraitSemDepth prog env₂ d selfTy tr traitArgs contract
  | 0, _, _, _, _, _, _, _, _, _, hSat => hSat
  | d + 1, env₁, env₂, hContracts, hAdt, hAssoc, selfTy, traitId, traitArgs,
      contract, hSat => by
      unfold SatisfiesTraitSemDepth at hSat
      unfold SatisfiesTraitSemDepth
      let env₁C : OpenExecEnv :=
        { env₁ with
          typeSpecs :=
            { env₁.typeSpecs with paramSpecs := [], paramInvs := [] } }
      let env₂C : OpenExecEnv :=
        { env₂ with
          typeSpecs :=
            { env₂.typeSpecs with paramSpecs := [], paramInvs := [] } }
      have hCC : env₁C.traitContracts = env₂C.traitContracts := hContracts
      have hCAdt : env₁C.typeSpecs.adtSpecs = env₂C.typeSpecs.adtSpecs := hAdt
      have hCAssoc : ∀ s tr as idx, openMirTyNoParam s = true →
          openMirTyListNoParam as = true →
          env₁C.typeSpecs.assocSpecs s tr as idx =
            env₂C.typeSpecs.assocSpecs s tr as idx := hAssoc
      let selfN := normalizeOpenTy prog.traitRegistry normFuel selfTy
      let argsN := traitArgs.map (normalizeOpenTy prog.traitRegistry normFuel)
      refine ⟨hSat.1, by rw [← hContracts]; exact hSat.2.1, hSat.2.2.1,
        hSat.2.2.2.1, hSat.2.2.2.2.1, ?_, ?_, ?_⟩
      · intro a hMem
        let ⟨hACl, hASupp, aSp, hAEval, hAWf⟩ := hSat.2.2.2.2.2.1 a hMem
        refine ⟨hACl, hASupp, aSp, ?_, hAWf⟩
        rw [← evalOpenTySpec_noParam_congr prog hRegWf env₁C env₂C hCAdt hCAssoc
          a (openMirTy_isClosed_noParam a hACl)]
        exact hAEval
      · let ⟨selfSpec, hSEval, hSWf, hSInv⟩ := hSat.2.2.2.2.2.2.1
        refine ⟨selfSpec, ?_, hSWf, hSInv⟩
        rw [← evalOpenTySpec_noParam_congr prog hRegWf env₁C env₂C hCAdt hCAssoc
          selfN (openMirTy_isClosed_noParam selfN hSat.2.2.1)]
        exact hSEval
      · let ⟨binding, hBind, hZero, hWcs, assocSpecs, hAssEq, hAssWf,
            hAssTypes, selfSpec, argSpecs, hSelfSp, hArgSp, hMethods⟩ :=
          hSat.2.2.2.2.2.2.2
        have hBindWcs := implRegistryEntriesWf_whereClosed prog.traitRegistry
          ⟨selfN, traitId, argsN⟩ binding (bool_and_right hRegWf) hBind
        have hSelfNoP := openMirTy_isClosed_noParam selfN hSat.2.2.1
        have hArgsNoP : openMirTyListNoParam argsN = true := by
          have hAux : ∀ xs : List OpenMirTy,
              (∀ a, a ∈ xs → OpenMirTy.isClosed a = true) →
              openMirTyListNoParam xs = true := by
            intro xs hAll
            induction xs with
            | nil => rfl
            | cons a as ih =>
                exact bool_and_eq_true
                  (openMirTy_isClosed_noParam a (hAll a (List.Mem.head as)))
                  (ih (fun x hx => hAll x (List.Mem.tail a hx)))
          exact hAux argsN (fun a hMem => (hSat.2.2.2.2.2.1 a hMem).1)
        refine ⟨binding, hBind, hZero, ?_, assocSpecs, ?_, hAssWf, ?_,
          selfSpec, argSpecs, ?_, ?_, ?_⟩
        · intro wc hMem
          have hWcCl := whereClause_isClosedList_mem binding.whereClauses wc
            hBindWcs hMem
          cases wc with
          | traitBound wSelf wTr wArgs =>
              let ⟨wC, hWC, hWSat⟩ := hWcs (.traitBound wSelf wTr wArgs) hMem
              refine ⟨wC, by rw [← hCC]; exact hWC, ?_⟩
              exact satisfiesTraitSemDepth_noParam_congr_dir prog hRegWf d env₁C
                env₂C hCC hCAdt hCAssoc wSelf wTr wArgs wC hWSat
          | isSized ty =>
              let ⟨hSzSupp, sp, hSp, hWf, hSz⟩ := hWcs (.isSized ty) hMem
              refine ⟨hSzSupp, sp, ?_, hWf, hSz⟩
              rw [← evalOpenTySpec_noParam_congr prog hRegWf env₁C env₂C hCAdt
                hCAssoc ty (openMirTy_isClosed_noParam ty hWcCl)]
              exact hSp
          | typeEq lhs rhs =>
              let ⟨hEqSupp, hBeq, sp, hL, hR, hWf⟩ :=
                hWcs (.typeEq lhs rhs) hMem
              refine ⟨hEqSupp, hBeq, sp, ?_, ?_, hWf⟩
              · rw [← evalOpenTySpec_noParam_congr prog hRegWf env₁C env₂C hCAdt
                  hCAssoc lhs
                  (openMirTy_isClosed_noParam lhs (bool_and_left hWcCl))]
                exact hL
              · rw [← evalOpenTySpec_noParam_congr prog hRegWf env₁C env₂C hCAdt
                  hCAssoc rhs
                  (openMirTy_isClosed_noParam rhs (bool_and_right hWcCl))]
                exact hR
        · unfold resolveTraitAssocSpecs
          rw [← resolveTraitAssocSpecsAux_noParam_congr prog hRegWf env₁C env₂C
            hCAdt hCAssoc selfN traitId argsN hSelfNoP hArgsNoP 0
            contract.assocTypeCount]
          exact hAssEq
        · intro idx hLt
          let ⟨rhsTy, rhsSpec, hLook, hRhsCl, hRhsEval, hRhsWf⟩ :=
            hAssTypes idx hLt
          refine ⟨rhsTy, rhsSpec, hLook, hRhsCl, ?_, hRhsWf⟩
          rw [← evalOpenTySpec_noParam_congr prog hRegWf env₁C env₂C hCAdt
            hCAssoc rhsTy (openMirTy_isClosed_noParam rhsTy hRhsCl)]
          exact hRhsEval
        · rw [← evalOpenTySpec_noParam_congr prog hRegWf env₁C env₂C hCAdt
            hCAssoc selfN hSelfNoP]
          exact hSelfSp
        · rw [← evalNormOpenTySpecList_noParam_congr
            env₁C.typeSpecs env₂C.typeSpecs hCAdt hCAssoc argsN hArgsNoP]
          exact hArgSp
        · intro mspec hMem
          let ⟨calleeId, calleeBody, hCalId, hCalGet, hCalP0, hCalNoP,
              hCalUns, hCalAdm, hArgLen, hRetEq, hArgsEq, hBehs⟩ :=
            hMethods mspec hMem
          refine ⟨calleeId, calleeBody, hCalId, hCalGet, hCalP0, hCalNoP,
            hCalUns, ?_, hArgLen, hRetEq, hArgsEq, ?_⟩
          · refine ⟨hCalAdm.1, hCalAdm.2.1, hCalAdm.2.2.1, hCalAdm.2.2.2.1,
              hCalAdm.2.2.2.2.1, hCalAdm.2.2.2.2.2.1, hCalAdm.2.2.2.2.2.2.1,
              hCalAdm.2.2.2.2.2.2.2.1, hCalAdm.2.2.2.2.2.2.2.2.1, ?_⟩
            exact (openLocalsAdmitted_noParam_congr prog hRegWf env₁C env₂C hCAdt
              hCAssoc calleeBody.locals
              (openBodyNoParam_parts calleeBody hCalNoP).1).mp
              hCalAdm.2.2.2.2.2.2.2.2.2
          · intro argVals hMatch hPre
            have hInstArgNoP := openTyListsNormEq_noParam prog.traitRegistry
              hRegWf calleeBody.sig.argTys _ hArgsEq
              (openBodyNoParam_parts calleeBody hCalNoP).2.1
            rw [← checkOpenArgsMatch_noParam_congr prog hRegWf env₁C env₂C hCAdt
              hAssoc argVals _ hInstArgNoP] at hMatch
            let ⟨hCWf, hCBeh⟩ := hBehs argVals hMatch hPre
            refine ⟨?_, ?_⟩
            · exact openWellFormed_noParam_congr
                (entryOpenProgForBody prog calleeId) hRegWf env₁C env₂C hCC
                hCAdt hCAssoc calleeBody.sig.whereClauses { args := argVals }
                calleeBody hCalGet hCalNoP hCWf
            · intro out hBeh2
              exact hCBeh out
                (openBehavior_noParam_congr
                  (entryOpenProgForBody prog calleeId) hRegWf env₁C env₂C hCC
                  hCAdt hCAssoc calleeBody.sig.whereClauses { args := argVals }
                  out calleeBody hCalGet hCalNoP hBeh2)

/-- `SatisfiesTraitSem` is invariant under changing `paramSpecs`/`paramInvs`
and out-of-scope `assocSpecs` (requiring equality only on `noParam` types). -/
theorem satisfiesTraitSem_noParam_congr (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env₁ env₂ : OpenExecEnv)
    (hContracts : env₁.traitContracts = env₂.traitContracts)
    (hAdt : env₁.typeSpecs.adtSpecs = env₂.typeSpecs.adtSpecs)
    (hAssoc : ∀ s tr as idx, openMirTyNoParam s = true →
      openMirTyListNoParam as = true →
      env₁.typeSpecs.assocSpecs s tr as idx =
        env₂.typeSpecs.assocSpecs s tr as idx)
    (selfTy : OpenMirTy) (tr : TraitDefId) (traitArgs : List OpenMirTy)
    (contract : TraitContract) :
    SatisfiesTraitSem prog env₁ selfTy tr traitArgs contract ↔
      SatisfiesTraitSem prog env₂ selfTy tr traitArgs contract :=
  ⟨satisfiesTraitSemDepth_noParam_congr_dir prog hRegWf traitCheckDepth env₁ env₂
      hContracts hAdt hAssoc selfTy tr traitArgs contract,
   satisfiesTraitSemDepth_noParam_congr_dir prog hRegWf traitCheckDepth env₂ env₁
      (Eq.symm hContracts) (Eq.symm hAdt)
      (fun s tr as idx h1 h2 => Eq.symm (hAssoc s tr as idx h1 h2))
      selfTy tr traitArgs contract⟩

/-- Congruence on normalized `ty`: evaluating `normalizeOpenTy ... ty` under
`env'` equals evaluating `substAndNormalize σ ty` under `baseClosed`. -/
theorem evalOpenTySpec_subst_param_eq_norm (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env : OpenExecEnv) (σ : List OpenMirTy) (paramSpecs : List TypeLayoutSpec)
    (paramInvs : List (List AllocByte → Prop))
    (hLenEq : paramSpecs.length = σ.length)
    (hMap : ∀ (i : Nat) (ty : OpenMirTy), openListGet? σ i = some ty →
      ∃ sp : TypeLayoutSpec, openListGet? paramSpecs i = some sp ∧
        evalOpenTySpec prog.traitRegistry normFuel
          { env.typeSpecs with paramSpecs := [], paramInvs := [] } ty =
          some sp ∧
        OpenMirTy.isClosed ty = true)
    (ty : OpenMirTy) (hNoTup : openTyNoOpenTuple ty = true) :
    let baseClosed : TypeSpecEnv :=
      { env.typeSpecs with paramSpecs := [], paramInvs := [] }
    let assocSpecFn := instAssocSpecs prog.traitRegistry env.typeSpecs σ
    let env' : OpenExecEnv :=
      { env with typeSpecs := (substTypeSpecEnv env.typeSpecs paramSpecs
          paramInvs assocSpecFn) }
    evalOpenTySpec prog.traitRegistry normFuel env'.typeSpecs
        (normalizeOpenTy prog.traitRegistry normFuel ty) =
      evalOpenTySpec prog.traitRegistry normFuel baseClosed
        (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ ty) := by
  intro baseClosed assocSpecFn env'
  have h1 :
      evalOpenTySpec prog.traitRegistry normFuel env'.typeSpecs
          (normalizeOpenTy prog.traitRegistry normFuel ty) =
        evalOpenTySpec prog.traitRegistry normFuel env'.typeSpecs ty := by
    unfold evalOpenTySpec
    rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf ty,
      normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf
        (normalizeOpenTyStep prog.traitRegistry ty),
      normalizeOpenTyStep_idempotent prog.traitRegistry hRegWf ty]
  rw [h1]
  exact evalOpenTySpec_subst_param_eq prog hRegWf env σ paramSpecs paramInvs
    hLenEq hMap ty hNoTup

/-- `substAndNormalize` produces a fixed point of `normalizeOpenTy`. -/
theorem normalizeOpenTy_substAndNormalize_idem (reg : TraitRegistry)
    (hRegWf : TraitRegistryWf reg = true) (σ : List OpenMirTy)
    (ty : OpenMirTy) :
    normalizeOpenTy reg normFuel (OpenMirTy.substAndNormalize reg normFuel σ ty) =
      OpenMirTy.substAndNormalize reg normFuel σ ty := by
  dsimp only [OpenMirTy.substAndNormalize]
  rw [normalizeOpenTy_normFuel_eq_step reg hRegWf (OpenMirTy.subst σ ty),
    normalizeOpenTy_normFuel_eq_step reg hRegWf
      (normalizeOpenTyStep reg (OpenMirTy.subst σ ty)),
    normalizeOpenTyStep_idempotent reg hRegWf (OpenMirTy.subst σ ty)]

/-- Elementwise fixed-point law for `substAndNormalize`. -/
theorem map_normalizeOpenTy_substAndNormalize_idem (reg : TraitRegistry)
    (hRegWf : TraitRegistryWf reg = true) (σ : List OpenMirTy) :
    ∀ args : List OpenMirTy,
      List.map (normalizeOpenTy reg normFuel)
          (List.map (OpenMirTy.substAndNormalize reg normFuel σ) args) =
        List.map (OpenMirTy.substAndNormalize reg normFuel σ) args := by
  intro args
  induction args with
  | nil =>
      rw [map_nil', map_nil']
  | cons a as ih =>
      rw [map_cons', map_cons']
      rw [normalizeOpenTy_substAndNormalize_idem reg hRegWf σ a, ih]

/-- Elementwise `substAndNormalize (normalizeOpenTy ...)` equality. -/
theorem map_substAndNormalize_normalize_eq (reg : TraitRegistry)
    (hRegWf : TraitRegistryWf reg = true) (σ : List OpenMirTy) :
    ∀ args : List OpenMirTy,
      List.map (OpenMirTy.substAndNormalize reg normFuel σ)
          (List.map (normalizeOpenTy reg normFuel) args) =
        List.map (OpenMirTy.substAndNormalize reg normFuel σ) args := by
  intro args
  induction args with
  | nil =>
      rw [map_nil', map_nil']
  | cons a as ih =>
      rw [map_cons', map_cons', map_cons']
      rw [substAndNormalize_normalize_eq reg hRegWf σ a, ih]

/-- Elementwise invariance of `substAndNormalize` on `isClosedList` inputs. -/
theorem map_substAndNormalize_isClosed_eq (reg : TraitRegistry)
    (hRegWf : TraitRegistryWf reg = true) (σ : List OpenMirTy) :
    ∀ args : List OpenMirTy,
      OpenMirTy.isClosedList (args.map (normalizeOpenTy reg normFuel)) = true →
      List.map (OpenMirTy.substAndNormalize reg normFuel σ) args =
        args.map (normalizeOpenTy reg normFuel) := by
  intro args hCl
  induction args with
  | nil =>
      rw [map_nil', map_nil']
  | cons a as ih =>
      rw [map_cons'] at hCl
      unfold OpenMirTy.isClosedList at hCl
      have ha := bool_and_left hCl
      have hSub :
          OpenMirTy.substAndNormalize reg normFuel σ a =
            normalizeOpenTy reg normFuel a := by
        rw [← substAndNormalize_normalize_eq reg hRegWf σ a]
        dsimp only [OpenMirTy.substAndNormalize]
        rw [normalizeOpenTy_normFuel_eq_step reg hRegWf
            (OpenMirTy.subst σ (normalizeOpenTy reg normFuel a)),
          openMirTy_subst_isClosed σ (normalizeOpenTy reg normFuel a) ha,
          normalizeOpenTyStep_isClosed reg (normalizeOpenTy reg normFuel a) ha]
      rw [map_cons', map_cons']
      rw [hSub, ih (bool_and_right hCl)]

/-- Transfer `WhereClauseSem` on `WhereClause.substAndNormalize σ wc` into
`WhereClauseParamSem` on `wc` at the constructed environment with
`(paramSpecs, paramInvs, assocSpecFn)`. -/
theorem whereClauseParamSem_of_discharged (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env : OpenExecEnv) (σ : List OpenMirTy) (paramSpecs : List TypeLayoutSpec)
    (hLenEq : paramSpecs.length = σ.length)
    (hMap : ∀ (i : Nat) (ty : OpenMirTy), openListGet? σ i = some ty →
      ∃ sp : TypeLayoutSpec, openListGet? paramSpecs i = some sp ∧
        evalOpenTySpec prog.traitRegistry normFuel
          { env.typeSpecs with paramSpecs := [], paramInvs := [] } ty =
          some sp ∧
        WellFormedTypeLayoutSpec sp ∧
        OpenMirTy.isClosed ty = true)
    (wc : WhereClause)
    (hBound : openWhereClausesBounded normFuel [wc] = true)
    (hSem : WhereClauseSem prog env
      (WhereClause.substAndNormalize prog.traitRegistry normFuel σ wc)) :
    let paramInvs := List.replicate paramSpecs.length (fun _ : List AllocByte => True)
    let assocSpecFn := instAssocSpecs prog.traitRegistry env.typeSpecs σ
    let env' : OpenExecEnv :=
      { env with typeSpecs := (substTypeSpecEnv env.typeSpecs paramSpecs
          paramInvs assocSpecFn) }
    WhereClauseParamSem prog env' wc := by
  intro paramInvs assocSpecFn env'
  have hMap' : ∀ (i : Nat) (ty : OpenMirTy), openListGet? σ i = some ty →
      ∃ sp : TypeLayoutSpec, openListGet? paramSpecs i = some sp ∧
        evalOpenTySpec prog.traitRegistry normFuel
          { env.typeSpecs with paramSpecs := [], paramInvs := [] } ty =
          some sp ∧
        OpenMirTy.isClosed ty = true := by
    intro i ty hG
    let ⟨sp, h1, h2, _, h4⟩ := hMap i ty hG
    exact ⟨sp, h1, h2, h4⟩
  cases wc with
  | isSized ty =>
      dsimp only [openWhereClausesBounded] at hBound
      have hOk := bool_and_left hBound
      have hNoTup := bool_and_right hOk
      dsimp only [WhereClause.substAndNormalize, WhereClauseSem] at hSem
      let ⟨_, sp, hEval, hWf, hSz⟩ := hSem
      dsimp only [WhereClauseParamSem]
      refine ⟨sp, ?_, hWf, hSz⟩
      rw [evalOpenTySpec_subst_param_eq prog hRegWf env σ paramSpecs paramInvs
        hLenEq hMap' ty hNoTup]
      exact hEval
  | typeEq lhs rhs =>
      dsimp only [openWhereClausesBounded] at hBound
      have hOk := bool_and_left hBound
      have hLTup := bool_and_right (bool_and_left hOk)
      have hRTup := bool_and_right hOk
      dsimp only [WhereClause.substAndNormalize, WhereClauseSem] at hSem
      let ⟨_, _, sp, hL, hR, hWf⟩ := hSem
      dsimp only [WhereClauseParamSem]
      refine ⟨sp, ?_, ?_, hWf⟩
      · rw [evalOpenTySpec_subst_param_eq prog hRegWf env σ paramSpecs paramInvs
          hLenEq hMap' lhs hLTup]
        exact hL
      · rw [evalOpenTySpec_subst_param_eq prog hRegWf env σ paramSpecs paramInvs
          hLenEq hMap' rhs hRTup]
        exact hR
  | traitBound selfTy tr args =>
      dsimp only [openWhereClausesBounded] at hBound
      have hOk := bool_and_left hBound
      have hSTup := bool_and_right (bool_and_left hOk)
      have hATups := bool_and_right hOk
      dsimp only [WhereClause.substAndNormalize, WhereClauseSem] at hSem
      let ⟨contract, hContract, hSat⟩ := hSem
      let envC : OpenExecEnv :=
        { env with
          typeSpecs :=
            { env.typeSpecs with paramSpecs := [], paramInvs := [] } }
      let selfSub := OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ
        selfTy
      let argsSub := args.map
        (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ)
      have hSatOrig :
          SatisfiesTraitSem prog envC selfSub tr argsSub contract := hSat
      have hSat' := hSat
      unfold SatisfiesTraitSem at hSat'
      rw [traitCheckDepth] at hSat'
      unfold SatisfiesTraitSemDepth at hSat'
      have hSelfSubIdem :
          normalizeOpenTy prog.traitRegistry normFuel selfSub = selfSub :=
        normalizeOpenTy_substAndNormalize_idem prog.traitRegistry hRegWf σ
          selfTy
      have hArgsSubIdem :
          List.map (normalizeOpenTy prog.traitRegistry normFuel) argsSub =
            argsSub :=
        map_normalizeOpenTy_substAndNormalize_idem prog.traitRegistry hRegWf σ
          args
      let ⟨_, _, _, _, hArgsSubLen, hArgsSubWf, hSelfSpecBox, hBindEx⟩ := hSat'
      let ⟨_, _, _, _, assocSpecs, hAssEq, hAssWf, _⟩ := hBindEx
      rw [hSelfSubIdem] at hSelfSpecBox hAssEq
      rw [hArgsSubIdem] at hArgsSubLen hArgsSubWf hAssEq
      dsimp only [WhereClauseParamSem]
      refine ⟨contract, hContract,
        by rw [length_map_eq]; rw [length_map_eq] at hArgsSubLen; exact hArgsSubLen,
        ?_, ?_, ?_, ?_⟩
      · intro a hMem
        let ⟨a₀, ha₀Mem, ha₀Eq⟩ := mem_of_mem_map
          (normalizeOpenTy prog.traitRegistry normFuel) hMem
        subst ha₀Eq
        have ha₀Tup : openTyNoOpenTuple a₀ = true :=
          openTyListNoOpenTuple_mem args a₀ hATups ha₀Mem
        have haSubMem :
            OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ a₀ ∈
              argsSub :=
          mem_map_of_mem
            (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ) ha₀Mem
        let ⟨_, _, aSp, hAEval, hAWf⟩ := hArgsSubWf _ haSubMem
        refine ⟨aSp, ?_, hAWf⟩
        rw [evalOpenTySpec_subst_param_eq_norm prog hRegWf env σ paramSpecs
          paramInvs hLenEq hMap' a₀ ha₀Tup]
        exact hAEval
      · let ⟨selfSpec, hSEval, hSWf, hSInv⟩ := hSelfSpecBox
        have hSEval' :
            evalOpenTySpec prog.traitRegistry normFuel env'.typeSpecs
                (normalizeOpenTy prog.traitRegistry normFuel selfTy) =
              some selfSpec := by
          rw [evalOpenTySpec_subst_param_eq_norm prog hRegWf env σ paramSpecs
            paramInvs hLenEq hMap' selfTy hSTup]
          exact hSEval
        refine ⟨selfSpec, hSEval', hSWf, ?_⟩
        cases hSN : normalizeOpenTy prog.traitRegistry normFuel selfTy with
        | param i =>
            rw [hSN] at hSEval'
            unfold evalOpenTySpec at hSEval'
            rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf
              (.param i)] at hSEval'
            dsimp only [normalizeOpenTyStep, evalNormOpenTySpec, env',
              substTypeSpecEnv] at hSEval'
            have hInvGet :
                openListGet? env'.typeSpecs.paramInvs i =
                  some (fun _ => True) :=
              openListGet?_replicate (fun _ : List AllocByte => True)
                paramSpecs i selfSpec hSEval'
            dsimp only [env', substTypeSpecEnv, paramInvs] at hInvGet
            dsimp only [env', substTypeSpecEnv, paramInvs]
            rw [hInvGet]
            exact fun bs hLang _ => hSInv .none bs hLang
        | bool | int _ _ | unit | never | char | ordering | enum _ | tuple _
        | slice _ | array _ _ | adt _ _ | ref _ _ | rawPtr _ _
        | assocProj _ _ _ _ | unsupported =>
            exact hSInv
      · refine ⟨assocSpecs, ?_, hAssWf⟩
        have hAuxEq :
            ∀ rem idx : Nat,
              resolveTraitAssocSpecsAux prog env'
                  (normalizeOpenTy prog.traitRegistry normFuel selfTy) tr
                  (args.map (normalizeOpenTy prog.traitRegistry normFuel)) idx
                  rem =
                resolveTraitAssocSpecsAux prog envC selfSub tr argsSub idx
                  rem := by
          intro rem
          induction rem with
          | zero => intro _; rfl
          | succ r ih =>
              intro idx
              unfold resolveTraitAssocSpecsAux
              have hSIdem :
                  OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ
                      (normalizeOpenTy prog.traitRegistry normFuel selfTy) =
                    selfSub :=
                substAndNormalize_normalize_eq prog.traitRegistry hRegWf σ
                  selfTy
              have hAIdem :
                  List.map
                      (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ)
                      (List.map (normalizeOpenTy prog.traitRegistry normFuel)
                        args) =
                    argsSub :=
                map_substAndNormalize_normalize_eq prog.traitRegistry hRegWf σ
                  args
              have hProj := evalOpenTySpec_subst_assocProj prog hRegWf env σ
                paramSpecs paramInvs
                (normalizeOpenTy prog.traitRegistry normFuel selfTy) tr
                (args.map (normalizeOpenTy prog.traitRegistry normFuel)) idx
              rw [hSIdem, hAIdem] at hProj
              dsimp only [env', envC] at hProj
              dsimp only [env', envC]
              rw [hProj, ih (idx + 1)]
        unfold resolveTraitAssocSpecs at hAssEq
        unfold resolveTraitAssocSpecs
        rw [hAuxEq contract.assocTypeCount 0]
        exact hAssEq
      · intro hSelfCl hArgsCl
        have hSelfSubEq :
            selfSub = normalizeOpenTy prog.traitRegistry normFuel selfTy := by
          dsimp only [selfSub]
          rw [← substAndNormalize_normalize_eq prog.traitRegistry hRegWf σ
            selfTy]
          dsimp only [OpenMirTy.substAndNormalize]
          rw [normalizeOpenTy_normFuel_eq_step prog.traitRegistry hRegWf _,
            openMirTy_subst_isClosed σ _ hSelfCl,
            normalizeOpenTyStep_isClosed prog.traitRegistry _ hSelfCl]
        have hArgsSubEq :
            argsSub = args.map (normalizeOpenTy prog.traitRegistry normFuel) :=
          map_substAndNormalize_isClosed_eq prog.traitRegistry hRegWf σ args
            hArgsCl
        have hSatClosed :
            SatisfiesTraitSem prog envC
              (normalizeOpenTy prog.traitRegistry normFuel selfTy) tr
              (args.map (normalizeOpenTy prog.traitRegistry normFuel))
              contract := by
          rw [← hSelfSubEq, ← hArgsSubEq]
          exact hSatOrig
        have hAssocNoP :
            ∀ s tr' as' idx, openMirTyNoParam s = true →
              openMirTyListNoParam as' = true →
              envC.typeSpecs.assocSpecs s tr' as' idx =
                env'.typeSpecs.assocSpecs s tr' as' idx := by
          intro s tr' as' idx h1 h2
          dsimp only [env', envC, substTypeSpecEnv, assocSpecFn, instAssocSpecs]
          rw [bool_and_eq_true h1 h2]
          rfl
        exact (satisfiesTraitSem_noParam_congr prog hRegWf envC env' rfl rfl
          hAssocNoP _ tr _ contract).mp hSatClosed

/-- Lift `whereClauseParamSem_of_discharged` across `wcs`. -/
theorem allWhereParamsSem_of_discharged (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env : OpenExecEnv) (σ : List OpenMirTy) (paramSpecs : List TypeLayoutSpec)
    (hLenEq : paramSpecs.length = σ.length)
    (hMap : ∀ (i : Nat) (ty : OpenMirTy), openListGet? σ i = some ty →
      ∃ sp : TypeLayoutSpec, openListGet? paramSpecs i = some sp ∧
        evalOpenTySpec prog.traitRegistry normFuel
          { env.typeSpecs with paramSpecs := [], paramInvs := [] } ty =
          some sp ∧
        WellFormedTypeLayoutSpec sp ∧
        OpenMirTy.isClosed ty = true) :
    ∀ wcs : List WhereClause,
      openWhereClausesBounded normFuel wcs = true →
      AllWhereDischarged prog env σ wcs →
      let paramInvs :=
        List.replicate paramSpecs.length (fun _ : List AllocByte => True)
      let assocSpecFn := instAssocSpecs prog.traitRegistry env.typeSpecs σ
      let env' : OpenExecEnv :=
        { env with typeSpecs := (substTypeSpecEnv env.typeSpecs paramSpecs
            paramInvs assocSpecFn) }
      AllWhereParamsSem prog env' wcs
  | [], _, _ => True.intro
  | wc :: rest, hBound, hDisch => by
      dsimp only [openWhereClausesBounded] at hBound
      have hHeadB := bool_and_left hBound
      have hRestB := bool_and_right hBound
      have hOneB : openWhereClausesBounded normFuel [wc] = true := by
        dsimp only [openWhereClausesBounded]
        exact bool_and_eq_true hHeadB rfl
      have hHead := whereClauseParamSem_of_discharged prog hRegWf env σ
        paramSpecs hLenEq hMap wc hOneB (hDisch wc (List.Mem.head rest))
      have hTail := allWhereParamsSem_of_discharged prog hRegWf env σ
        paramSpecs hLenEq hMap rest hRestB
        (fun w hw => hDisch w (List.Mem.tail wc hw))
      exact ⟨hHead, hTail⟩

/-- `ClosedOpenInstantiationTransfer`: constructs concrete `paramSpecs`,
`paramInvs`, and `assocSpecs`, discharges `AllWhereParamsSem` **from**
`AllWhereDischarged`, and invokes `ParametricBodyVerified` to yield
`OpenWellFormed` without any trust-bypassing `wellFormedTransfer` parameter. -/
theorem ClosedOpenInstantiationTransfer (prog : OpenProgram) (env : OpenExecEnv)
    (defId : DefId) (ob : OpenBody) (σ : List OpenMirTy)
    (safetyPre : OpenExecEnv → List Val → Prop)
    (hParam : ParametricBodyVerified prog env defId ob safetyPre)
    (hLen : σ.length = ob.sig.tyParamCount)
    (hWfSubst : AllSubstTypesWellFormed prog env σ)
    (hWhereDisch : AllWhereDischarged prog env σ ob.sig.whereClauses)
    (hBounded : openWhereClausesBounded normFuel ob.sig.whereClauses = true) :
    ∃ paramSpecs : List TypeLayoutSpec,
      ∃ paramInvs : List (List AllocByte → Prop),
      let assocSpecFn := instAssocSpecs prog.traitRegistry env.typeSpecs σ
      let env' : OpenExecEnv :=
        { env with typeSpecs := (substTypeSpecEnv env.typeSpecs paramSpecs
            paramInvs assocSpecFn) }
      paramSpecs.length = ob.sig.tyParamCount ∧
      AllParamSpecsWf paramSpecs ∧
      AllParamInvsWf paramSpecs paramInvs ∧
      AllWhereParamsSem prog env' ob.sig.whereClauses ∧
      OpenBodyStaticAdmitted prog env' ob ∧
      ∀ args : List Val,
        ValidOpenEntryArgs prog env' ob args →
        (ob.isUnsafe = true → safetyPre env' args) →
        OpenWellFormed (entryOpenProgForBody prog defId) env'
          ob.sig.whereClauses { args := args } := by
  let ⟨paramSpecs, hPsLen, hPsWf, _, hMap⟩ :=
    substSpecs_of_allSubstTypesWellFormed prog env σ hWfSubst
  let paramInvs :=
    List.replicate paramSpecs.length (fun _ : List AllocByte => True)
  let assocSpecFn := instAssocSpecs prog.traitRegistry env.typeSpecs σ
  let env' : OpenExecEnv :=
    { env with typeSpecs := (substTypeSpecEnv env.typeSpecs paramSpecs
        paramInvs assocSpecFn) }
  have hInvsWf : AllParamInvsWf paramSpecs paramInvs :=
    replicate_true_paramInvsWf paramSpecs hPsWf
  have hWhereSem : AllWhereParamsSem prog env' ob.sig.whereClauses :=
    allWhereParamsSem_of_discharged prog hParam.2.1 env σ paramSpecs hPsLen
      hMap ob.sig.whereClauses hBounded hWhereDisch
  have hPsLenTy : paramSpecs.length = ob.sig.tyParamCount :=
    Eq.trans hPsLen hLen
  let ⟨hAdm, hWfs⟩ := hParam.2.2.2 paramSpecs paramInvs assocSpecFn hPsLenTy
    hPsWf hInvsWf hWhereSem
  exact ⟨paramSpecs, paramInvs, hPsLenTy, hPsWf, hInvsWf, hWhereSem, hAdm, hWfs⟩

/-! ## Part IV: Lockstep Simulation & `ClosedInstantiationTransfer` -/

private theorem nat_ble_true {a b : Nat} (h : a ≤ b) :
    Nat.ble a b = true :=
  (Nat.ble_eq).mpr h

private theorem nat_ble_false {a b : Nat} (h : b < a) :
    Nat.ble a b = false := by
  cases hB : Nat.ble a b with
  | false => rfl
  | true => exact False.elim (Nat.not_le_of_gt h (Nat.ble_eq.mp hB))

private theorem nat_lt_of_blt {a b : Nat} (h : Nat.blt a b = true) :
    a < b :=
  Nat.blt_eq.mp h

private theorem nat_ble_of_true {a b : Nat} (h : Nat.ble a b = true) :
    a ≤ b :=
  Nat.ble_eq.mp h

private theorem char_isUnicodeScalar (c : Char) :
    isUnicodeScalar c.toNat = true := by
  change (Nat.ble c.val.toNat 0x10ffff &&
    !(Nat.ble 0xd800 c.val.toNat && Nat.ble c.val.toNat 0xdfff)) = true
  cases c.valid with
  | inl hLo =>
      rw [nat_ble_true (Nat.le_trans (Nat.le_of_lt hLo) (by decide))]
      rw [nat_ble_false hLo]
      rfl
  | inr hHi =>
      rw [nat_ble_true (Nat.le_of_lt_succ hHi.2)]
      have hNotLe : Nat.ble c.val.toNat 0xdfff = false :=
        nat_ble_false (Nat.lt_of_le_of_lt (by decide) hHi.1)
      rw [hNotLe]
      cases Nat.ble 0xd800 c.val.toNat <;> rfl

private theorem fin_ofNat_toNat_lt {m a : Nat} (hm : 0 < m) (ha : a < m) :
    Fin.Internal.ofNat m hm a = ⟨a, ha⟩ := by
  cases m with
  | zero => cases hm
  | succ k =>
      apply Fin.eq_of_val_eq
      exact Nat.mod_eq_of_lt ha

private theorem bv_ofNat_toNat {w : Nat} (x : BitVec w) :
    BitVec.ofNat w x.toNat = x := by
  cases x with
  | ofFin f =>
      cases f with
      | mk val isLt =>
          exact congrArg BitVec.ofFin (fin_ofNat_toNat_lt _ isLt)

private theorem bv128_beq_self (x : BitVec 128) : (x == x) = true := by
  exact beq_self_eq_true x

private theorem truncateBits_toNat_lt (w : IntWidth) (x : BitVec 128) :
    (truncateBits w x).toNat < Nat.pow 2 w.bitWidth := by
  cases w with
  | i8 =>
      change HMod.hMod (HMod.hMod (HShiftRight.hShiftRight x.toNat 0)
        (Nat.pow 2 8)) (Nat.pow 2 128) < Nat.pow 2 8
      have hLt : HMod.hMod (HShiftRight.hShiftRight x.toNat 0) (Nat.pow 2 8) <
          Nat.pow 2 8 :=
        Nat.mod_lt _ (by decide)
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hLt (by decide))]
      exact hLt
  | i16 =>
      change HMod.hMod (HMod.hMod (HShiftRight.hShiftRight x.toNat 0)
        (Nat.pow 2 16)) (Nat.pow 2 128) < Nat.pow 2 16
      have hLt : HMod.hMod (HShiftRight.hShiftRight x.toNat 0) (Nat.pow 2 16) <
          Nat.pow 2 16 :=
        Nat.mod_lt _ (by decide)
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hLt (by decide))]
      exact hLt
  | i32 =>
      change HMod.hMod (HMod.hMod (HShiftRight.hShiftRight x.toNat 0)
        (Nat.pow 2 32)) (Nat.pow 2 128) < Nat.pow 2 32
      have hLt : HMod.hMod (HShiftRight.hShiftRight x.toNat 0) (Nat.pow 2 32) <
          Nat.pow 2 32 :=
        Nat.mod_lt _ (by decide)
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hLt (by decide))]
      exact hLt
  | i64 =>
      change HMod.hMod (HMod.hMod (HShiftRight.hShiftRight x.toNat 0)
        (Nat.pow 2 64)) (Nat.pow 2 128) < Nat.pow 2 64
      have hLt : HMod.hMod (HShiftRight.hShiftRight x.toNat 0) (Nat.pow 2 64) <
          Nat.pow 2 64 :=
        Nat.mod_lt _ (by decide)
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hLt (by decide))]
      exact hLt
  | isize =>
      change HMod.hMod (HMod.hMod (HShiftRight.hShiftRight x.toNat 0)
        (Nat.pow 2 64)) (Nat.pow 2 128) < Nat.pow 2 64
      have hLt : HMod.hMod (HShiftRight.hShiftRight x.toNat 0) (Nat.pow 2 64) <
          Nat.pow 2 64 :=
        Nat.mod_lt _ (by decide)
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hLt (by decide))]
      exact hLt
  | i128 =>
      change HMod.hMod (HMod.hMod (HShiftRight.hShiftRight x.toNat 0)
        (Nat.pow 2 128)) (Nat.pow 2 128) < Nat.pow 2 128
      exact Nat.mod_lt _ (by decide)

private theorem truncateBits_idem (w : IntWidth) (x : BitVec 128) :
    truncateBits w (truncateBits w x) = truncateBits w x := by
  have hLt := truncateBits_toNat_lt w x
  have h128 : ∀ y : BitVec 128, y.toNat < Nat.pow 2 w.bitWidth →
      truncateBits w y = y := by
    intro y hYLt
    cases w with
    | i8 =>
        change BitVec.ofNat 128
          (HMod.hMod (HShiftRight.hShiftRight y.toNat 0) (Nat.pow 2 8)) = y
        have hY8 : y.toNat < Nat.pow 2 8 := hYLt
        rw [Nat.shiftRight_zero, Nat.mod_eq_of_lt hY8, bv_ofNat_toNat]
    | i16 =>
        change BitVec.ofNat 128
          (HMod.hMod (HShiftRight.hShiftRight y.toNat 0) (Nat.pow 2 16)) = y
        have hY16 : y.toNat < Nat.pow 2 16 := hYLt
        rw [Nat.shiftRight_zero, Nat.mod_eq_of_lt hY16, bv_ofNat_toNat]
    | i32 =>
        change BitVec.ofNat 128
          (HMod.hMod (HShiftRight.hShiftRight y.toNat 0) (Nat.pow 2 32)) = y
        have hY32 : y.toNat < Nat.pow 2 32 := hYLt
        rw [Nat.shiftRight_zero, Nat.mod_eq_of_lt hY32, bv_ofNat_toNat]
    | i64 =>
        change BitVec.ofNat 128
          (HMod.hMod (HShiftRight.hShiftRight y.toNat 0) (Nat.pow 2 64)) = y
        have hY64 : y.toNat < Nat.pow 2 64 := hYLt
        rw [Nat.shiftRight_zero, Nat.mod_eq_of_lt hY64, bv_ofNat_toNat]
    | isize =>
        change BitVec.ofNat 128
          (HMod.hMod (HShiftRight.hShiftRight y.toNat 0) (Nat.pow 2 64)) = y
        have hYIs : y.toNat < Nat.pow 2 64 := hYLt
        rw [Nat.shiftRight_zero, Nat.mod_eq_of_lt hYIs, bv_ofNat_toNat]
    | i128 =>
        change BitVec.ofNat 128
          (HMod.hMod (HShiftRight.hShiftRight y.toNat 0) (Nat.pow 2 128)) = y
        have hY128 : y.toNat < Nat.pow 2 128 := hYLt
        rw [Nat.shiftRight_zero, Nat.mod_eq_of_lt hY128, bv_ofNat_toNat]
  exact h128 (truncateBits w x) hLt

private theorem scalarVal_wf_lt {sv : ScalarVal} (hWf : sv.wf = true) :
    sv.bits.toNat < Nat.pow 2 sv.width.bitWidth := by
  unfold ScalarVal.wf at hWf
  have hEq : truncateBits sv.width sv.bits = sv.bits := eq_of_beq hWf
  rw [← hEq]
  exact truncateBits_toNat_lt sv.width sv.bits

private theorem scalarVal_wf_le_max {sv : ScalarVal} (hWf : sv.wf = true) :
    sv.bits.toNat ≤ Nat.pow 2 sv.width.bitWidth - 1 :=
  Nat.le_pred_of_lt (scalarVal_wf_lt hWf)

private theorem scalarVal_wf_truncate (w : IntWidth) (s : Bool)
    (bits : BitVec 128) :
    ({ width := w, signed := s, bits := truncateBits w bits } :
      ScalarVal).wf = true := by
  unfold ScalarVal.wf
  dsimp only
  rw [truncateBits_idem w bits]
  exact bv128_beq_self _

private theorem bang_true_eq_false {b : Bool} (h : b = true) :
    (!b) = false := by
  rw [h]; rfl

private theorem list_map_map {α β γ : Type} (g : β → γ) (f : α → β) :
    ∀ xs : List α, (xs.map f).map g = xs.map (fun x => g (f x))
  | [] => rfl
  | _ :: xs => congrArg (fun tl => _ :: tl) (list_map_map g f xs)

private theorem list_map_drop {α β : Type} (f : α → β) :
    ∀ (xs : List α) (n : Nat), (xs.map f).drop n = (xs.drop n).map f
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, n + 1 => list_map_drop f xs n

private theorem list_map_take {α β : Type} (f : α → β) :
    ∀ (xs : List α) (n : Nat), (xs.map f).take n = (xs.take n).map f
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, n + 1 => congrArg (fun tl => _ :: tl) (list_map_take f xs n)

private theorem list_drop_of_le {α : Type} :
    ∀ (xs : List α) (n : Nat), xs.length ≤ n → xs.drop n = []
  | [], 0, _ => rfl
  | [], _ + 1, _ => rfl
  | _ :: _, 0, h => by cases h
  | _ :: xs, n + 1, h => list_drop_of_le xs n (Nat.le_of_succ_le_succ h)

private theorem nat_list_nonempty_zero_lt :
    ∀ ds : List Nat, (!ds.isEmpty) = true → Nat.blt 0 ds.length = true
  | [], h => by cases h
  | _ :: _, _ => rfl

private theorem findDiscrVariantAux_lt (bits : BitVec 128) :
    ∀ (idx : Nat) (ds : List Nat) (v : Nat),
      findDiscrVariantAux idx bits ds = some v → v < idx + ds.length
  | _, [], _, h => by cases h
  | idx, d :: ds, v, h => by
      dsimp only [findDiscrVariantAux] at h
      cases hEq : (BitVec.ofNat 128 d == bits) with
      | true =>
          rw [hEq] at h
          cases h
          exact Nat.lt_add_of_pos_right (Nat.succ_pos _)
      | false =>
          rw [hEq] at h
          have hSub := findDiscrVariantAux_lt bits (idx + 1) ds v h
          rw [Nat.add_assoc, Nat.add_comm 1 ds.length] at hSub
          exact hSub

private theorem evalConstLit_checkVal (mty : MirTy) (lit : ConstLit) (v : Val)
    (h : evalConstLit mty lit = .ok v) :
    checkVal v mty = true := by
  cases mty with
  | int w s =>
      cases lit with
      | zeroSized | rodataBytes _ | rodataRef _ _ _ _ => cases h
      | scalar bits =>
          dsimp only [evalConstLit] at h
          cases hNe : (truncateBits w bits != bits) with
          | true => rw [hNe] at h; cases h
          | false =>
              rw [hNe] at h
              cases h
              dsimp only [checkVal, Val.ty?]
              rw [ite_cond_true (scalarVal_wf_truncate w s bits)]
              dsimp only [MirTy.beq]
              rw [intWidth_beq_self, beq_self_eq_true]
              rfl
  | bool =>
      cases lit with
      | zeroSized | rodataBytes _ | rodataRef _ _ _ _ => cases h
      | scalar bits =>
          dsimp only [evalConstLit] at h
          cases hNe : (truncateBits .i8 bits != bits) with
          | true => rw [hNe] at h; cases h
          | false =>
              rw [hNe] at h
              cases hB0 : (UInt8.ofNat (truncateBits .i8 bits).toNat == 0) with
              | true => rw [hB0] at h; cases h; rfl
              | false =>
                  rw [hB0] at h
                  cases hB1 : (UInt8.ofNat (truncateBits .i8 bits).toNat == 1) with
                  | true => rw [hB1] at h; cases h; rfl
                  | false => rw [hB1] at h; cases h
  | unit =>
      cases lit with
      | scalar _ | rodataBytes _ | rodataRef _ _ _ _ => cases h
      | zeroSized => cases h; rfl
  | char =>
      cases lit with
      | zeroSized | rodataBytes _ | rodataRef _ _ _ _ => cases h
      | scalar bits =>
          dsimp only [evalConstLit] at h
          cases hNe : (truncateBits .i32 bits != bits) with
          | true => rw [hNe] at h; cases h
          | false =>
              rw [hNe] at h
              cases hUni : isUnicodeScalar bits.toNat with
              | false => rw [hUni] at h; cases h
              | true => rw [hUni] at h; cases h; rfl
  | ordering =>
      cases lit with
      | zeroSized | rodataBytes _ | rodataRef _ _ _ _ => cases h
      | scalar bits =>
          dsimp only [evalConstLit] at h
          cases hNe : (truncateBits .i8 bits != bits) with
          | true => rw [hNe] at h; cases h
          | false =>
              rw [hNe] at h
              cases hOrd : orderingOfTagBits bits.toNat with
              | none => rw [hOrd] at h; cases h
              | some ord => rw [hOrd] at h; cases h; rfl
  | enum ety =>
      cases lit with
      | rodataBytes _ | rodataRef _ _ _ _ => cases h
      | zeroSized =>
          dsimp only [evalConstLit] at h
          cases hZst : isZstEnumTy ety with
          | false => rw [hZst] at h; cases h
          | true =>
              rw [hZst] at h
              cases h
              unfold isZstEnumTy at hZst
              cases hTag : ety.tagRepr with
              | scalar _ _ => rw [hTag] at hZst; cases hZst
              | zeroSized =>
                  rw [hTag] at hZst
                  dsimp only at hZst
                  have hNonEmpty : (!ety.discriminants.isEmpty) = true := by
                    unfold enumAdmitted at hZst
                    exact bool_and_left (bool_and_left (bool_and_left
                      (bool_and_left hZst)))
                  dsimp only [checkVal, Val.ty?]
                  rw [hZst, nat_list_nonempty_zero_lt ety.discriminants hNonEmpty]
                  exact enumTy_beq_self ety
      | scalar bits =>
          dsimp only [evalConstLit] at h
          cases hTag : ety.tagRepr with
          | zeroSized => rw [hTag] at h; cases h
          | scalar tagW tagS =>
              rw [hTag] at h
              dsimp only at h
              cases hBad : (!enumAdmitted ety || truncateBits tagW bits != bits) with
              | true => rw [ite_cond_true hBad] at h; cases h
              | false =>
                  rw [ite_cond_false hBad] at h
                  have hAdm : enumAdmitted ety = true :=
                    not_bool_eq_false (bool_or_eq_false_left hBad)
                  cases hFind : findDiscrVariant?
                      (tagBitsToDiscrBits tagW tagS ety.discrWidth bits)
                      ety.discriminants with
                  | none => rw [hFind] at h; cases h
                  | some idx =>
                      rw [hFind] at h
                      cases h
                      have hLt : idx < ety.discriminants.length :=
                        Nat.zero_add ety.discriminants.length ▸
                          findDiscrVariantAux_lt _ 0 ety.discriminants idx hFind
                      dsimp only [checkVal, Val.ty?]
                      rw [hAdm, Nat.blt_eq.mpr hLt]
                      exact enumTy_beq_self ety
  | never | tuple _ | ref _ _ | rawPtr _ _ | slice _ | str | rangeTo _ | rangeFrom _
  | array _ _ | unsupported | option _ | range _ | box _ | vec _ =>
      cases lit <;> cases h

private theorem evalIntToIntCast_checkVal (v : Val) (castTy : MirTy) (res : Val)
    (h : evalIntToIntCast v castTy = .ok res) :
    checkVal res castTy = true := by
  unfold evalIntToIntCast at h
  cases hBits : intLikeBits v with
  | none => rw [hBits] at h; cases h
  | some bits =>
      rw [hBits] at h
      cases castTy with
      | int w s =>
          cases h
          dsimp only [checkVal, Val.ty?]
          rw [ite_cond_true (scalarVal_wf_truncate w s (BitVec.ofNat 128 bits))]
          dsimp only [MirTy.beq]
          rw [intWidth_beq_self, beq_self_eq_true]
          rfl
      | char =>
          dsimp only at h
          cases hBle : Nat.ble bits 255 with
          | false => rw [ite_cond_false hBle] at h; cases h
          | true => rw [ite_cond_true hBle] at h; cases h; rfl
      | bool | unit | never | ordering | enum _ | tuple _
      | ref _ _ | rawPtr _ _ | slice _ | str | rangeTo _ | rangeFrom _
      | array _ _ | unsupported | option _ | range _ | box _ | vec _ => cases h

mutual
theorem toClosedMirTy?_isClosed :
    ∀ {ty : OpenMirTy} {mty : MirTy},
      OpenMirTy.toClosedMirTy? ty = some mty → OpenMirTy.isClosed ty = true
  | .bool, _, _ | .int _ _, _, _ | .unit, _, _ | .never, _, _
  | .char, _, _ | .ordering, _, _ | .enum _, _, _ => rfl
  | .slice _, _, h | .array _ _, _, h | .adt _ _, _, h
  | .param _, _, h | .assocProj _ _ _ _, _, h | .unsupported, _, h => by
      cases h
  | .ref _ p, _, h | .rawPtr _ p, _, h => by
      dsimp only [OpenMirTy.toClosedMirTy?] at h
      cases hP : OpenMirTy.toClosedMirTy? p with
      | none => rw [hP] at h; cases h
      | some _ =>
          dsimp only [OpenMirTy.isClosed]
          exact toClosedMirTy?_isClosed hP
  | .tuple fs, _, h => by
      dsimp only [OpenMirTy.toClosedMirTy?] at h
      cases hFs : OpenMirTy.toClosedMirTyList? fs with
      | none => rw [hFs] at h; cases h
      | some _ => exact toClosedMirTyList?_isClosed hFs

theorem toClosedMirTyList?_isClosed :
      ∀ {fs : List OpenMirTy} {cs : List MirTy},
        OpenMirTy.toClosedMirTyList? fs = some cs →
        OpenMirTy.isClosedList fs = true
    | [], _, _ => rfl
    | x :: xs, cs, h => by
        dsimp only [OpenMirTy.toClosedMirTyList?] at h
        cases hx : OpenMirTy.toClosedMirTy? x with
        | none => rw [hx] at h; cases h
        | some cx =>
            rw [hx] at h
            cases hxs : OpenMirTy.toClosedMirTyList? xs with
            | none => rw [hxs] at h; cases h
            | some cxs =>
                exact bool_and_eq_true (toClosedMirTy?_isClosed hx)
                  (toClosedMirTyList?_isClosed hxs)
end

theorem toClosedMirTy?_substAndNormalize_eq (reg : TraitRegistry)
    (σ : List OpenMirTy) {ty : OpenMirTy} {mty : MirTy}
    (h : OpenMirTy.toClosedMirTy? ty = some mty) :
    OpenMirTy.substAndNormalize reg normFuel σ ty = ty := by
  have hc := toClosedMirTy?_isClosed h
  unfold OpenMirTy.substAndNormalize
  rw [openMirTy_subst_isClosed σ ty hc,
    normalizeOpenTy_isClosed reg normFuel ty hc]

theorem toClosedMirTy?_eraseOpenTy {ty : OpenMirTy} {mty : MirTy}
    (h : OpenMirTy.toClosedMirTy? ty = some mty) :
    eraseOpenTy ty = mty := by
  unfold eraseOpenTy
  rw [h]

theorem toClosedMirTy?_erase_subst (reg : TraitRegistry) (σ : List OpenMirTy)
    {ty : OpenMirTy} {mty : MirTy}
    (h : OpenMirTy.toClosedMirTy? ty = some mty) :
    eraseOpenTy (OpenMirTy.substAndNormalize reg normFuel σ ty) = mty := by
  rw [toClosedMirTy?_substAndNormalize_eq reg σ h]
  exact toClosedMirTy?_eraseOpenTy h

private theorem toDay1List?_map_eraseOpenTy (reg : TraitRegistry)
    (σ : List OpenMirTy) :
    ∀ {tys : List OpenMirTy} {mtys : List MirTy},
      OpenMirTy.toClosedMirTyList? tys = some mtys →
      List.map eraseOpenTy
          (List.map (OpenMirTy.substAndNormalize reg normFuel σ) tys) =
        mtys
  | [], mtys, h => by cases h; rfl
  | x :: xs, mtys, h => by
      dsimp only [OpenMirTy.toClosedMirTyList?] at h
      cases hx : OpenMirTy.toClosedMirTy? x with
      | none => rw [hx] at h; cases h
      | some cx =>
          rw [hx] at h
          cases hxs : OpenMirTy.toClosedMirTyList? xs with
          | none => rw [hxs] at h; cases h
          | some cxs =>
              rw [hxs] at h
              cases h
              dsimp only [List.map]
              rw [toClosedMirTy?_erase_subst reg σ hx,
                toDay1List?_map_eraseOpenTy reg σ hxs]

private theorem toDay1?_erase_projElem (reg : TraitRegistry)
    (σ : List OpenMirTy) {e : OpenProjectionElem} {de : ProjectionElem}
    (h : OpenProjectionElem.toDay1? e = some de) :
    eraseOpenProjectionElem (OpenProjectionElem.subst reg normFuel σ e) = de := by
  cases e with
  | deref => cases h; rfl
  | unsupported => cases h; rfl
  | field idx ty =>
      dsimp only [OpenProjectionElem.toDay1?] at h
      cases hTy : OpenMirTy.toClosedMirTy? ty with
      | none => rw [hTy] at h; cases h
      | some mty =>
          rw [hTy] at h
          cases h
          dsimp only [OpenProjectionElem.subst, eraseOpenProjectionElem]
          rw [toClosedMirTy?_erase_subst reg σ hTy]

private theorem toDay1List?_erase_projElem (reg : TraitRegistry)
    (σ : List OpenMirTy) :
    ∀ {es : List OpenProjectionElem} {des : List ProjectionElem},
      OpenProjectionElem.toDay1List? es = some des →
      List.map eraseOpenProjectionElem
          (List.map (OpenProjectionElem.subst reg normFuel σ) es) =
        des
  | [], des, h => by cases h; rfl
  | e :: es, des, h => by
      dsimp only [OpenProjectionElem.toDay1List?] at h
      cases he : OpenProjectionElem.toDay1? e with
      | none => rw [he] at h; cases h
      | some de =>
          rw [he] at h
          cases hes : OpenProjectionElem.toDay1List? es with
          | none => rw [hes] at h; cases h
          | some ds =>
              rw [hes] at h
              cases h
              dsimp only [List.map]
              rw [toDay1?_erase_projElem reg σ he,
                toDay1List?_erase_projElem reg σ hes]

private theorem toDay1?_erase_place (reg : TraitRegistry)
    (σ : List OpenMirTy) {p : OpenPlace} {dp : Place}
    (h : OpenPlace.toDay1? p = some dp) :
    eraseOpenPlace (OpenPlace.subst reg normFuel σ p) = dp := by
  dsimp only [OpenPlace.toDay1?] at h
  cases hPs : OpenProjectionElem.toDay1List? p.projection with
  | none => rw [hPs] at h; cases h
  | some ps =>
      rw [hPs] at h
      cases h
      dsimp only [OpenPlace.subst, eraseOpenPlace]
      rw [toDay1List?_erase_projElem reg σ hPs]

private theorem toDay1?_erase_operand (reg : TraitRegistry)
    (σ : List OpenMirTy) {op : OpenOperand} {dop : Operand}
    (h : OpenOperand.toDay1? op = some dop) :
    eraseOpenOperand (OpenOperand.subst reg normFuel σ op) = dop := by
  cases op with
  | copy p =>
      dsimp only [OpenOperand.toDay1?] at h
      cases hp : OpenPlace.toDay1? p with
      | none => rw [hp] at h; cases h
      | some dp =>
          rw [hp] at h; cases h
          exact congrArg Operand.copy (toDay1?_erase_place reg σ hp)
  | move p =>
      dsimp only [OpenOperand.toDay1?] at h
      cases hp : OpenPlace.toDay1? p with
      | none => rw [hp] at h; cases h
      | some dp =>
          rw [hp] at h; cases h
          exact congrArg Operand.move (toDay1?_erase_place reg σ hp)
  | constant c =>
      dsimp only [OpenOperand.toDay1?] at h
      cases hTy : OpenMirTy.toClosedMirTy? c.ty with
      | none => rw [hTy] at h; cases h
      | some mty =>
          rw [hTy] at h; cases h
          dsimp only [OpenOperand.subst, eraseOpenOperand]
          rw [toClosedMirTy?_erase_subst reg σ hTy]

private theorem toDay1List?_erase_operand (reg : TraitRegistry)
    (σ : List OpenMirTy) :
    ∀ {ops : List OpenOperand} {dops : List Operand},
      OpenOperand.toDay1List? ops = some dops →
      List.map eraseOpenOperand
          (List.map (OpenOperand.subst reg normFuel σ) ops) =
        dops
  | [], dops, h => by cases h; rfl
  | x :: xs, dops, h => by
      dsimp only [OpenOperand.toDay1List?] at h
      cases hx : OpenOperand.toDay1? x with
      | none => rw [hx] at h; cases h
      | some dx =>
          rw [hx] at h
          cases hxs : OpenOperand.toDay1List? xs with
          | none => rw [hxs] at h; cases h
          | some dxs =>
              rw [hxs] at h; cases h
              dsimp only [List.map]
              rw [toDay1?_erase_operand reg σ hx,
                toDay1List?_erase_operand reg σ hxs]

private theorem toDay1?_erase_rvalue (reg : TraitRegistry)
    (σ : List OpenMirTy) {rv : OpenRvalue} {drv : Rvalue}
    (h : OpenRvalue.toDay1? rv = some drv) :
    eraseOpenRvalue (OpenRvalue.subst reg normFuel σ rv) = drv := by
  cases rv with
  | use op =>
      dsimp only [OpenRvalue.toDay1?] at h
      cases hop : OpenOperand.toDay1? op with
      | none => rw [hop] at h; cases h
      | some dop =>
          rw [hop] at h; cases h
          exact congrArg Rvalue.use (toDay1?_erase_operand reg σ hop)
  | binaryOp op l r =>
      dsimp only [OpenRvalue.toDay1?] at h
      cases hl : OpenOperand.toDay1? l with
      | none => rw [hl] at h; cases h
      | some dl =>
          rw [hl] at h
          cases hr : OpenOperand.toDay1? r with
          | none => rw [hr] at h; cases h
          | some dr =>
              rw [hr] at h; cases h
              dsimp only [OpenRvalue.subst, eraseOpenRvalue]
              rw [toDay1?_erase_operand reg σ hl,
                toDay1?_erase_operand reg σ hr]
  | unaryOp op opnd =>
      dsimp only [OpenRvalue.toDay1?] at h
      cases hop : OpenOperand.toDay1? opnd with
      | none => rw [hop] at h; cases h
      | some dop =>
          rw [hop] at h; cases h
          exact congrArg (Rvalue.unaryOp op) (toDay1?_erase_operand reg σ hop)
  | cast k opnd ty =>
      dsimp only [OpenRvalue.toDay1?] at h
      cases hop : OpenOperand.toDay1? opnd with
      | none => rw [hop] at h; cases h
      | some dop =>
          rw [hop] at h
          cases hTy : OpenMirTy.toClosedMirTy? ty with
          | none => rw [hTy] at h; cases h
          | some mty =>
              rw [hTy] at h; cases h
              dsimp only [OpenRvalue.subst, eraseOpenRvalue]
              rw [toDay1?_erase_operand reg σ hop,
                toClosedMirTy?_erase_subst reg σ hTy]
  | discriminant p =>
      dsimp only [OpenRvalue.toDay1?] at h
      cases hp : OpenPlace.toDay1? p with
      | none => rw [hp] at h; cases h
      | some dp =>
          rw [hp] at h; cases h
          exact congrArg Rvalue.discriminant (toDay1?_erase_place reg σ hp)
  | ref m p =>
      dsimp only [OpenRvalue.toDay1?] at h
      cases hp : OpenPlace.toDay1? p with
      | none => rw [hp] at h; cases h
      | some dp =>
          rw [hp] at h; cases h
          exact congrArg (Rvalue.ref m) (toDay1?_erase_place reg σ hp)
  | addressOf m p =>
      dsimp only [OpenRvalue.toDay1?] at h
      cases hp : OpenPlace.toDay1? p with
      | none => rw [hp] at h; cases h
      | some dp =>
          rw [hp] at h; cases h
          exact congrArg (Rvalue.addressOf m) (toDay1?_erase_place reg σ hp)
  | aggregateTuple fs =>
      dsimp only [OpenRvalue.toDay1?] at h
      cases hfs : OpenOperand.toDay1List? fs with
      | none => rw [hfs] at h; cases h
      | some dfs =>
          rw [hfs] at h; cases h
          exact congrArg Rvalue.aggregateTuple
            (toDay1List?_erase_operand reg σ hfs)
  | unsupported => cases h; rfl

private theorem toDay1?_erase_stmt (reg : TraitRegistry) (σ : List OpenMirTy)
    {st : OpenStatementKind} {dst : StatementKind}
    (h : OpenStatementKind.toDay1? st = some dst) :
    eraseOpenStatementKind (OpenStatementKind.subst reg normFuel σ st) =
      dst := by
  cases st with
  | storageLive l => cases h; rfl
  | storageDead l => cases h; rfl
  | nop => cases h; rfl
  | unsupported => cases h; rfl
  | assign p rv =>
      dsimp only [OpenStatementKind.toDay1?] at h
      cases hp : OpenPlace.toDay1? p with
      | none => rw [hp] at h; cases h
      | some dp =>
          rw [hp] at h
          cases hrv : OpenRvalue.toDay1? rv with
          | none => rw [hrv] at h; cases h
          | some drv =>
              rw [hrv] at h; cases h
              dsimp only [OpenStatementKind.subst, eraseOpenStatementKind]
              rw [toDay1?_erase_place reg σ hp,
                toDay1?_erase_rvalue reg σ hrv]

private theorem toDay1List?_erase_stmt (reg : TraitRegistry)
    (σ : List OpenMirTy) :
    ∀ {sts : List OpenStatementKind} {dsts : List StatementKind},
      OpenStatementKind.toDay1List? sts = some dsts →
      List.map eraseOpenStatementKind
          (List.map (OpenStatementKind.subst reg normFuel σ) sts) =
        dsts
  | [], dsts, h => by cases h; rfl
  | s :: ss, dsts, h => by
      dsimp only [OpenStatementKind.toDay1List?] at h
      cases hs : OpenStatementKind.toDay1? s with
      | none => rw [hs] at h; cases h
      | some ds =>
          rw [hs] at h
          cases hss : OpenStatementKind.toDay1List? ss with
          | none => rw [hss] at h; cases h
          | some dss =>
              rw [hss] at h; cases h
              dsimp only [List.map]
              rw [toDay1?_erase_stmt reg σ hs,
                toDay1List?_erase_stmt reg σ hss]

private theorem toDay1?_erase_term (reg : TraitRegistry) (σ : List OpenMirTy)
    {tm : OpenTerminatorKind} {dtm : TerminatorKind}
    (h : OpenTerminatorKind.toDay1? tm = some dtm) :
    eraseOpenTerminatorKind (OpenTerminatorKind.subst reg normFuel σ tm) =
      dtm := by
  cases tm with
  | goto t => cases h; rfl
  | return_ => cases h; rfl
  | unreachable => cases h; rfl
  | unwindResume => cases h; rfl
  | unsupported => cases h; rfl
  | traitCall _ _ _ _ _ _ _ _ => cases h
  | switchInt d tgts =>
      dsimp only [OpenTerminatorKind.toDay1?] at h
      cases hd : OpenOperand.toDay1? d with
      | none => rw [hd] at h; cases h
      | some dd =>
          rw [hd] at h; cases h
          dsimp only [OpenTerminatorKind.subst, eraseOpenTerminatorKind]
          rw [toDay1?_erase_operand reg σ hd]
  | assert cond exp msg tgt uw =>
      dsimp only [OpenTerminatorKind.toDay1?] at h
      cases hc : OpenOperand.toDay1? cond with
      | none => rw [hc] at h; cases h
      | some dc =>
          rw [hc] at h; cases h
          dsimp only [OpenTerminatorKind.subst, eraseOpenTerminatorKind]
          rw [toDay1?_erase_operand reg σ hc]
  | call _ _ _ _ _ _ =>
      dsimp only [OpenTerminatorKind.toDay1?] at h
      cases h

private theorem toDay1?_erase_bb (reg : TraitRegistry) (σ : List OpenMirTy)
    {bb : OpenBasicBlock} {dbb : BasicBlock}
    (h : OpenBasicBlock.toDay1? bb = some dbb) :
    eraseOpenBasicBlock (OpenBasicBlock.subst reg normFuel σ bb) = dbb := by
  dsimp only [OpenBasicBlock.toDay1?] at h
  cases hs : OpenStatementKind.toDay1List? bb.statements with
  | none => rw [hs] at h; cases h
  | some dsts =>
      rw [hs] at h
      cases ht : OpenTerminatorKind.toDay1? bb.terminator with
      | none => rw [ht] at h; cases h
      | some dtm =>
          rw [ht] at h; cases h
          dsimp only [OpenBasicBlock.subst, eraseOpenBasicBlock]
          rw [toDay1List?_erase_stmt reg σ hs, toDay1?_erase_term reg σ ht]

private theorem toDay1List?_erase_bb (reg : TraitRegistry) (σ : List OpenMirTy) :
    ∀ {bbs : List OpenBasicBlock} {dbbs : List BasicBlock},
      OpenBasicBlock.toDay1List? bbs = some dbbs →
      List.map eraseOpenBasicBlock
          (List.map (OpenBasicBlock.subst reg normFuel σ) bbs) =
        dbbs
  | [], dbbs, h => by cases h; rfl
  | b :: bs, dbbs, h => by
      dsimp only [OpenBasicBlock.toDay1List?] at h
      cases hb : OpenBasicBlock.toDay1? b with
      | none => rw [hb] at h; cases h
      | some db =>
          rw [hb] at h
          cases hbs : OpenBasicBlock.toDay1List? bs with
          | none => rw [hbs] at h; cases h
          | some dbs =>
              rw [hbs] at h; cases h
              dsimp only [List.map]
              rw [toDay1?_erase_bb reg σ hb, toDay1List?_erase_bb reg σ hbs]

theorem day1OfBodySome_eq (reg : TraitRegistry) (σ : List OpenMirTy)
    {ob : OpenBody} {db : Body} (h : OpenBody.toDay1? ob = some db) :
    eraseOpenBody reg σ ob = db := by
  dsimp only [OpenBody.toDay1?] at h
  cases hLoc : OpenMirTy.toClosedMirTyList? ob.locals with
  | none => rw [hLoc] at h; cases h
  | some dLoc =>
      rw [hLoc] at h
      cases hBbs : OpenBasicBlock.toDay1List? ob.basicBlocks with
      | none => rw [hBbs] at h; cases h
      | some dBbs =>
          rw [hBbs] at h; cases h
          dsimp only [eraseOpenBody, OpenBody.subst]
          rw [toDay1List?_map_eraseOpenTy reg σ hLoc,
            toDay1List?_erase_bb reg σ hBbs]

private theorem toDay1List?_erase_bodies (reg : TraitRegistry)
    (σ : List OpenMirTy) :
    ∀ {obs : List OpenBody} {dbs : List Body},
      OpenProgram.toDay1List? obs = some dbs →
      List.map (eraseOpenBody reg σ) obs = dbs
  | [], dbs, h => by cases h; rfl
  | b :: bs, dbs, h => by
      dsimp only [OpenProgram.toDay1List?] at h
      cases hb : OpenBody.toDay1? b with
      | none => rw [hb] at h; cases h
      | some db =>
          rw [hb] at h
          cases hbs : OpenProgram.toDay1List? bs with
          | none => rw [hbs] at h; cases h
          | some dbs' =>
              rw [hbs] at h; cases h
              dsimp only [List.map]
              rw [day1OfBodySome_eq reg σ hb,
                toDay1List?_erase_bodies reg σ hbs]

theorem day1OfProgSome_eq (prog : OpenProgram) (σ : List OpenMirTy)
    (defId : DefId) {day1P : Program}
    (h : OpenProgram.toDay1? (entryOpenProgForBody prog defId) = some day1P) :
    day1P = entryProgForBody (eraseOpenProgram σ prog) defId := by
  dsimp only [OpenProgram.toDay1?, entryOpenProgForBody] at h
  cases hBs : OpenProgram.toDay1List? prog.bodies with
  | none => rw [hBs] at h; cases h
  | some dbs =>
      rw [hBs] at h; cases h
      dsimp only [entryProgForBody, eraseOpenProgram]
      rw [toDay1List?_erase_bodies prog.traitRegistry σ hBs]

private theorem toDay1List?_getElem? :
    ∀ {obs : List OpenBody} {dbs : List Body} {i : Nat} {ob : OpenBody},
      OpenProgram.toDay1List? obs = some dbs →
      openListGet? obs i = some ob →
      ∃ db : Body,
        Trusted.MirSemantics.getElem? dbs i = some db ∧
        OpenBody.toDay1? ob = some db
  | [], _, _, _, _, hGet => by cases hGet
  | b :: bs, dbs, i, ob, hList, hGet => by
      dsimp only [OpenProgram.toDay1List?] at hList
      cases hb : OpenBody.toDay1? b with
      | none => rw [hb] at hList; cases hList
      | some db =>
          rw [hb] at hList
          cases hbs : OpenProgram.toDay1List? bs with
          | none => rw [hbs] at hList; cases hList
          | some dbs' =>
              rw [hbs] at hList; cases hList
              cases i with
              | zero =>
                  cases hGet
                  exact ⟨db, rfl, hb⟩
              | succ j =>
                  dsimp only [Trusted.MirSemantics.getElem?]
                  exact toDay1List?_getElem? hbs hGet

private theorem openBodyToDay1_noTraitCall {ob : OpenBody} {db : Body}
    (h : OpenBody.toDay1? ob = some db) {bIdx : Nat} {bb : OpenBasicBlock}
    (hBb : openListGet? ob.basicBlocks bIdx = some bb) :
    match bb.terminator with
    | .traitCall _ _ _ _ _ _ _ _ => False
    | _ => True := by
  dsimp only [OpenBody.toDay1?] at h
  cases hLoc : OpenMirTy.toClosedMirTyList? ob.locals with
  | none => rw [hLoc] at h; cases h
  | some dLoc =>
      rw [hLoc] at h
      cases hBbs : OpenBasicBlock.toDay1List? ob.basicBlocks with
      | none => rw [hBbs] at h; cases h
      | some dBbs =>
          rw [hBbs] at h
          have hAux : ∀ {bbs : List OpenBasicBlock} {dbbs : List BasicBlock}
              {k : Nat} {b : OpenBasicBlock},
              OpenBasicBlock.toDay1List? bbs = some dbbs →
              openListGet? bbs k = some b →
              ∃ dtm : TerminatorKind,
                OpenTerminatorKind.toDay1? b.terminator = some dtm := by
            intro bbs
            induction bbs with
            | nil => intro _ _ _ _ hG; cases hG
            | cons x xs ih =>
                intro dbbs k b hL hG
                dsimp only [OpenBasicBlock.toDay1List?] at hL
                cases hx : OpenBasicBlock.toDay1? x with
                | none => rw [hx] at hL; cases hL
                | some dx =>
                    rw [hx] at hL
                    cases hxs : OpenBasicBlock.toDay1List? xs with
                    | none => rw [hxs] at hL; cases hL
                    | some dxs =>
                        rw [hxs] at hL; cases hL
                        cases k with
                        | zero =>
                            cases hG
                            dsimp only [OpenBasicBlock.toDay1?] at hx
                            cases hs' : OpenStatementKind.toDay1List?
                                x.statements with
                            | none => rw [hs'] at hx; cases hx
                            | some _ =>
                                rw [hs'] at hx
                                cases ht' : OpenTerminatorKind.toDay1?
                                    x.terminator with
                                | none => rw [ht'] at hx; cases hx
                                | some dtm => exact ⟨dtm, rfl⟩
                        | succ j => exact ih hxs hG
          let ⟨dtm, hTm⟩ := hAux hBbs hBb
          cases hTm' : bb.terminator with
          | traitCall _ _ _ _ _ _ _ _ =>
              rw [hTm'] at hTm; cases hTm
          | goto _ | switchInt _ _ | return_ | unreachable
          | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ _
          | unsupported => exact True.intro

private theorem openState_toState_ofState (s : State) :
    OpenState.toState (OpenState.ofState s) = s := by
  cases s with
  | mk frames callerMem mem =>
      dsimp only [OpenState.ofState, OpenState.toState]
      have hFrames :
          List.map OpenFrameState.toFrameState
              (List.map OpenFrameState.ofFrameState frames) = frames := by
        induction frames with
        | nil => rfl
        | cons f fs ih =>
            dsimp only [List.map]
            have hf : OpenFrameState.toFrameState
                (OpenFrameState.ofFrameState f) = f := by
              cases f; rfl
            rw [hf, ih]
      rw [hFrames]

/-- In a call-free program, Day-1 `evalStep` keeps a single frame with no
pinned `sysrootOp?` in that shape. -/
private theorem evalStep_singleFrame (p : Program) (s s' : State)
    (hSingle : ∃ f : FrameState, s.frames = [f] ∧ f.sysrootOp? = none)
    (hAll : p.bodies.all (fun b => !bodyHasAnyCall b) = true)
    (hEv : evalStep p 0 s = .step s') :
    ∃ f' : FrameState, s'.frames = [f'] ∧ f'.sysrootOp? = none := by
  let ⟨f, hFs, hSys⟩ := hSingle
  cases s with
  | mk frames cm mem =>
      dsimp only at hFs
      subst hFs
      let ⟨df', hNext, _, hSys'⟩ := evalStep_single_preserves_defId p f mem cm
        s' (activeFrameBody_noCall p f hAll) hEv
      exact ⟨df', hNext, hSys'.trans hSys⟩

private theorem openStep_day1Some_iff (prog : OpenProgram) (env : OpenExecEnv)
    (wcs : List WhereClause) (day1P : Program)
    (hDay1 : OpenProgram.toDay1? prog = some day1P)
    (s : State)
    (hSingle : ∃ f : FrameState, s.frames = [f] ∧ f.sysrootOp? = none)
    (res : StepResult State TerminalOut) :
    OpenStep prog env wcs (OpenState.ofState s) (liftStepResult res) ↔
      evalStep day1P 0 s = res := by
  let ⟨f, hFs, hSys⟩ := hSingle
  have hDet : openEvalDetStep prog env (OpenState.ofState s) =
      liftStepResult (evalStep day1P 0 s) := by
    unfold openEvalDetStep openEvalDetStepAux
    have hOF : (OpenState.ofState s).frames =
        [OpenFrameState.ofFrameState f] := by
      dsimp only [OpenState.ofState]
      rw [hFs]
      rfl
    rw [hDay1, hOF]
    dsimp only
    rw [openState_toState_ofState s]
  dsimp only [OpenState.ofState] at hDet
  rw [hFs] at hDet
  dsimp only [List.map, OpenFrameState.ofFrameState] at hDet
  have hOfInj : ∀ {s₁ s₂ : State},
      OpenState.ofState s₁ = OpenState.ofState s₂ → s₁ = s₂ := by
    intro s₁ s₂ hEq
    have hT := congrArg OpenState.toState hEq
    rw [openState_toState_ofState, openState_toState_ofState] at hT
    exact hT
  have hDetEq : ∀ r, (liftStepResult res = liftStepResult r ↔ res = r) := by
    intro r
    cases res <;> cases r <;> constructor <;> intro h
    · exact congrArg StepResult.step (hOfInj (StepResult.step.inj h))
    · rw [h]
    · cases h
    · cases h
    · cases h
    · cases h
    · cases h
    · cases h
    · exact congrArg StepResult.done (StepResult.done.inj h)
    · rw [h]
    · cases h
    · cases h
    · cases h
    · cases h
    · cases h
    · cases h
    · exact congrArg StepResult.fault (StepResult.fault.inj h)
    · rw [h]
  have hFrames : OpenStep prog env wcs (OpenState.ofState s)
      (liftStepResult res) ↔
      liftStepResult res = liftStepResult (evalStep day1P 0 s) := by
    unfold OpenStep OpenStepOnFrames OpenState.ofState
    rw [hFs]
    dsimp only [List.map, OpenFrameState.ofFrameState, OpenStepOnBodyOpt]
    cases hGet : openListGet? prog.bodies f.defId with
    | none =>
        dsimp only [OpenProgram.toDay1?] at hDay1
        cases hBs : OpenProgram.toDay1List? prog.bodies with
        | none => rw [hBs] at hDay1; cases hDay1
        | some dbs =>
            rw [hBs] at hDay1; cases hDay1
            have hNone : Trusted.MirSemantics.getElem? dbs f.defId = none := by
              have hAux : ∀ {obs : List OpenBody} {dbs' : List Body} {k : Nat},
                  OpenProgram.toDay1List? obs = some dbs' →
                  openListGet? obs k = none →
                  Trusted.MirSemantics.getElem? dbs' k = none := by
                intro obs
                induction obs with
                | nil => intro dbs' k hL _; cases hL; cases k <;> rfl
                | cons x xs ih =>
                    intro dbs' k hL hG
                    dsimp only [OpenProgram.toDay1List?] at hL
                    cases hx : OpenBody.toDay1? x with
                    | none => rw [hx] at hL; cases hL
                    | some dx =>
                        rw [hx] at hL
                        cases hxs : OpenProgram.toDay1List? xs with
                        | none => rw [hxs] at hL; cases hL
                        | some dxs =>
                            rw [hxs] at hL; cases hL
                            cases k with
                            | zero => cases hG
                            | succ j =>
                                dsimp only [Trusted.MirSemantics.getElem?]
                                exact ih hxs hG
              exact hAux hBs hGet
            have hEvNone : evalStep
                ({ bodies := dbs
                 , entryDefId := prog.entryDefId
                 , pointerWidthBits := prog.pointerWidthBits
                 , mirProfileVersion := prog.mirProfileVersion
                 , scope := prog.scope } : Program)
                0 s = .fault .unsupported := by
              unfold evalStep
              rw [hFs]
              dsimp only [activeFrameBody]
              rw [hSys]
              dsimp only
              rw [hNone]
            rw [hEvNone]
            rfl
    | some ob =>
        dsimp only [OpenStepOnBlockOpt]
        cases hBb : openListGet? ob.basicBlocks f.blockIdx with
        | none =>
            dsimp only [OpenProgram.toDay1?] at hDay1
            cases hBs : OpenProgram.toDay1List? prog.bodies with
            | none => rw [hBs] at hDay1; cases hDay1
            | some dbs =>
                rw [hBs] at hDay1; cases hDay1
                let ⟨db, hGetD, hObD⟩ := toDay1List?_getElem? hBs hGet
                have hBbNone :
                    Trusted.MirSemantics.getElem? db.basicBlocks f.blockIdx =
                      none := by
                  dsimp only [OpenBody.toDay1?] at hObD
                  cases hLoc : OpenMirTy.toClosedMirTyList? ob.locals with
                  | none => rw [hLoc] at hObD; cases hObD
                  | some _ =>
                      rw [hLoc] at hObD
                      cases hBbs : OpenBasicBlock.toDay1List? ob.basicBlocks with
                      | none => rw [hBbs] at hObD; cases hObD
                      | some dbbs =>
                          rw [hBbs] at hObD; cases hObD
                          have hAux : ∀ {bs : List OpenBasicBlock}
                              {dbs' : List BasicBlock} {k : Nat},
                              OpenBasicBlock.toDay1List? bs = some dbs' →
                              openListGet? bs k = none →
                              Trusted.MirSemantics.getElem? dbs' k = none := by
                            intro bs
                            induction bs with
                            | nil => intro dbs' k hL _; cases hL; cases k <;> rfl
                            | cons x xs ih =>
                                intro dbs' k hL hG
                                dsimp only [OpenBasicBlock.toDay1List?] at hL
                                cases hx : OpenBasicBlock.toDay1? x with
                                | none => rw [hx] at hL; cases hL
                                | some dx =>
                                    rw [hx] at hL
                                    cases hxs : OpenBasicBlock.toDay1List? xs with
                                    | none => rw [hxs] at hL; cases hL
                                    | some dxs =>
                                        rw [hxs] at hL; cases hL
                                        cases k with
                                        | zero => cases hG
                                        | succ j =>
                                            dsimp only [Trusted.MirSemantics.getElem?]
                                            exact ih hxs hG
                          exact hAux hBbs hBb
                have hEvNone : evalStep
                    ({ bodies := dbs
                     , entryDefId := prog.entryDefId
                     , pointerWidthBits := prog.pointerWidthBits
                     , mirProfileVersion := prog.mirProfileVersion
                     , scope := prog.scope } : Program)
                    0 s = .fault .unsupported := by
                  unfold evalStep
                  rw [hFs]
                  dsimp only [activeFrameBody]
                  rw [hSys]
                  dsimp only
                  rw [hGetD]
                  dsimp only
                  rw [hBbNone]
                rw [hEvNone]
                rfl
        | some bb =>
            dsimp only [OpenStepOnStmtEnd]
            cases hEnd : Nat.beq f.stmtIdx bb.statements.length with
            | false => dsimp only; rw [hDet]
            | true =>
                dsimp only
                dsimp only [OpenProgram.toDay1?] at hDay1
                cases hBs : OpenProgram.toDay1List? prog.bodies with
                | none => rw [hBs] at hDay1; cases hDay1
                | some _ =>
                    rw [hBs] at hDay1; cases hDay1
                    let ⟨_, _, hObD⟩ := toDay1List?_getElem? hBs hGet
                    have hNoT := openBodyToDay1_noTraitCall hObD hBb
                    cases hTm : bb.terminator with
                    | traitCall _ _ _ _ _ _ _ _ => rw [hTm] at hNoT; cases hNoT
                    | goto _ | switchInt _ _ | return_ | unreachable
                    | unwindResume | assert _ _ _ _ _
                    | call _ _ _ _ _ _ | unsupported =>
                        dsimp only [OpenStepOnTerm]
                        rw [hDet]
  exact ⟨fun h => ((hDetEq (evalStep day1P 0 s)).mp (hFrames.mp h)).symm,
    fun h => hFrames.mpr ((hDetEq (evalStep day1P 0 s)).mpr h.symm)⟩

private theorem openReaches_snoc (prog : OpenProgram) (env : OpenExecEnv)
    (wcs : List WhereClause) {s₁ s₂ s₃ : OpenState}
    (hR : OpenReaches prog env wcs s₁ s₂)
    (hS : OpenStep prog env wcs s₂ (.step s₃)) :
    OpenReaches prog env wcs s₁ s₃ := by
  induction hR with
  | refl _ => exact .step hS (.refl _)
  | step hFirst _ ih => exact .step hFirst (ih hS)

private theorem openWellFormed_day1Some_to_wellFormed (prog : OpenProgram)
    (env : OpenExecEnv) (wcs : List WhereClause) (q : Query) (day1P : Program)
    (hDay1 : OpenProgram.toDay1? prog = some day1P)
    (hOWf : OpenWellFormed prog env wcs q) :
    WellFormed day1P q := by
  have hInitEq : openInitState prog env q =
      match initState day1P q with
      | .ok s => .ok (OpenState.ofState s)
      | .error k => .error k := by
    unfold openInitState openInitStateAux
    rw [hDay1]
    rfl
  have hAll := toDay1?_noCall prog day1P hDay1
  have hLiftReach : ∀ {s₀ s : State},
      (∃ f : FrameState, s₀.frames = [f] ∧ f.sysrootOp? = none) →
      Reaches day1P s₀ s →
      OpenReaches prog env wcs (OpenState.ofState s₀) (OpenState.ofState s) ∧
        (∃ f : FrameState, s.frames = [f] ∧ f.sysrootOp? = none) := by
    intro s₀ s hF0 hReach
    induction hReach with
    | refl => exact ⟨.refl _, hF0⟩
    | tail _ hStep ih =>
        let ⟨_, _, hEv⟩ := hStep
        let ⟨hOR, hFs1⟩ := ih
        exact ⟨openReaches_snoc prog env wcs hOR
            ((openStep_day1Some_iff prog env wcs day1P hDay1 _ hFs1
              (.step _)).mpr hEv),
          evalStep_singleFrame day1P _ _ hFs1 hAll hEv⟩
  have hInitSingle : ∀ {s₀ : State},
      initState day1P q = .ok s₀ →
        ∃ f : FrameState, s₀.frames = [f] ∧ f.sysrootOp? = none := by
    intro s₀ hI
    unfold initState at hI
    cases hHdr : (!Nat.beq day1P.pointerWidthBits 64 ||
        !Nat.beq day1P.mirProfileVersion 1) with
    | true => rw [ite_cond_true hHdr] at hI; cases hI
    | false =>
        rw [ite_cond_false hHdr] at hI
        cases hCm : (!q.callerMem.allocations.isEmpty) with
        | true => rw [ite_cond_true hCm] at hI; cases hI
        | false =>
            rw [ite_cond_false hCm] at hI
            dsimp only at hI
            cases hB : Trusted.MirSemantics.getElem? day1P.bodies
                day1P.entryDefId with
            | none => rw [hB] at hI; cases hI
            | some body =>
                rw [hB] at hI
                dsimp only at hI
                cases hE : body.basicBlocks.isEmpty with
                | true => rw [hE] at hI; cases hI
                | false =>
                    rw [ite_cond_false hE] at hI
                    cases hArg : (!Nat.blt body.argumentCount
                        body.locals.length) with
                    | true => rw [ite_cond_true hArg] at hI; cases hI
                    | false =>
                        rw [ite_cond_false hArg] at hI
                        cases hSto : (!storageAnnotationsInBounds body) with
                        | true => rw [ite_cond_true hSto] at hI; cases hI
                        | false =>
                            rw [ite_cond_false hSto] at hI
                            cases hDis : (!discriminantTypesValid body) with
                            | true => rw [ite_cond_true hDis] at hI; cases hI
                            | false =>
                                rw [ite_cond_false hDis] at hI
                                cases hCas : (!castTypesValid body) with
                                | true => rw [ite_cond_true hCas] at hI; cases hI
                                | false =>
                                    rw [ite_cond_false hCas] at hI
                                    cases hAct : (!assertConditionTypesValid body) with
                                    | true => rw [ite_cond_true hAct] at hI; cases hI
                                    | false =>
                                        rw [ite_cond_false hAct] at hI
                                        cases hSup : (!body.locals.all
                                            isSupportedScalarOrUnitTy) with
                                        | true =>
                                            rw [ite_cond_true hSup] at hI; cases hI
                                        | false =>
                                            rw [ite_cond_false hSup] at hI
                                            have hI := (ite_err_ok hI).2
                                            have hI := (ite_err_ok hI).2
                                            cases hChk : (!checkArgsMatch q.args
                                                ((body.locals.drop 1).take
                                                  body.argumentCount)) with
                                            | true =>
                                                rw [ite_cond_true hChk] at hI
                                                cases hI
                                            | false =>
                                                rw [ite_cond_false hChk] at hI
                                                cases hI
                                                exact ⟨_, rfl, rfl⟩
  constructor
  · let ⟨os₀, hOInit, _⟩ := hOWf.1
    rw [hInitEq] at hOInit
    cases hDInit : initState day1P q with
    | error k => rw [hDInit] at hOInit; cases hOInit
    | ok s₀ => exact ⟨s₀, rfl, fun _ _ => ⟨0, rfl⟩⟩
  · intro k hFault
    unfold ReachesResult at hFault
    cases hDInit : initState day1P q with
    | error k' =>
        let ⟨os₀, hOInit, _⟩ := hOWf.1
        rw [hInitEq, hDInit] at hOInit
        cases hOInit
    | ok s₀ =>
        rw [hDInit] at hFault
        let ⟨s, hReach, _, _, hEv⟩ := hFault
        have hOInit : openInitState prog env q = .ok (OpenState.ofState s₀) := by
          rw [hInitEq, hDInit]
        let ⟨hOReach, hFsS⟩ := hLiftReach (hInitSingle hDInit) hReach
        have hOStep :=
          (openStep_day1Some_iff prog env wcs day1P hDay1 s hFsS
            (.fault k)).mpr hEv
        exact hOWf.2 (OpenState.ofState s₀) hOInit (OpenState.ofState s) k hOReach
          hOStep

private theorem checkScalarRoles_intRoles (sv : ScalarVal) (w : IntWidth)
    (hWf : sv.wf = true) (hW : sv.width = w) :
    checkScalarRoles sv (intRoles w) = true := by
  have hLe : Nat.ble sv.bits.toNat (Nat.pow 2 w.bitWidth - 1) = true := by
    rw [← hW]
    exact nat_ble_true (scalarVal_wf_le_max hWf)
  cases w with
  | i8 | i16 | i32 | i64 | isize | i128 =>
      dsimp only [intRoles, IntWidth.byteSize, repeatItem, checkScalarRoles]
      rw [hWf, hW, intWidth_beq_self, byteRolesBeq_self, hLe]
      rfl

private theorem checkVal_shape {v : Val} {mty : MirTy}
    (hChk : checkVal v mty = true) :
    (∃ b, mty = .bool ∧ v = .bool b) ∨
    (mty = .unit ∧ v = .unit) ∨
    (∃ c, mty = .char ∧ v = .char c) ∨
    (∃ ord, mty = .ordering ∧ v = .ordering ord) ∨
    (∃ w s sv, mty = .int w s ∧ v = .scalar sv ∧
      sv.wf = true ∧ sv.width = w ∧ sv.signed = s) ∨
    (∃ ety idx, mty = .enum ety ∧ v = .enumVal ety idx ∧
      enumAdmitted ety = true ∧ idx < ety.discriminants.length) ∨
    (∃ w s sv b, mty = .tuple [.int w s, .bool] ∧
      v = .tuple [.scalar sv, .bool b] ∧
      sv.wf = true ∧ sv.width = w ∧ sv.signed = s) := by
  cases v with
  | bool b =>
      dsimp only [checkVal, Val.ty?] at hChk
      cases mty with
      | bool => exact .inl ⟨b, rfl, rfl⟩
      | _ => cases hChk
  | unit =>
      dsimp only [checkVal, Val.ty?] at hChk
      cases mty with
      | unit => exact .inr (.inl ⟨rfl, rfl⟩)
      | _ => cases hChk
  | char c =>
      dsimp only [checkVal, Val.ty?] at hChk
      cases mty with
      | char => exact .inr (.inr (.inl ⟨c, rfl, rfl⟩))
      | _ => cases hChk
  | ordering ord =>
      dsimp only [checkVal, Val.ty?] at hChk
      cases mty with
      | ordering => exact .inr (.inr (.inr (.inl ⟨ord, rfl, rfl⟩)))
      | _ => cases hChk
  | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | bytes _ | array _
  | optionVal _ | range _ _ | boxPtr _ _ | vec _ _ _ =>
      dsimp only [checkVal, Val.ty?] at hChk
      cases hChk
  | scalar sv =>
      dsimp only [checkVal, Val.ty?] at hChk
      cases hWf : sv.wf with
      | false => rw [ite_cond_false hWf] at hChk; cases hChk
      | true =>
          rw [ite_cond_true hWf] at hChk
          dsimp only at hChk
          cases mty with
          | int w s =>
              dsimp only [MirTy.beq] at hChk
              exact .inr (.inr (.inr (.inr (.inl ⟨w, s, sv, rfl, rfl, hWf,
                intWidth_beq_eq (bool_and_left hChk),
                eq_of_beq (bool_and_right hChk)⟩))))
          | _ => cases hChk
  | enumVal ety idx =>
      dsimp only [checkVal, Val.ty?] at hChk
      cases hOK : (enumAdmitted ety && Nat.blt idx ety.discriminants.length)
          with
      | false => rw [ite_cond_false hOK] at hChk; cases hChk
      | true =>
          rw [ite_cond_true hOK] at hChk
          dsimp only at hChk
          cases mty with
          | enum ety' =>
              have hEq := enumTy_beq_eq hChk
              subst hEq
              exact .inr (.inr (.inr (.inr (.inr (.inl ⟨ety, idx, rfl, rfl,
                bool_and_left hOK, Nat.blt_eq.mp (bool_and_right hOK)⟩)))))
          | _ => cases hChk
  | tuple fs =>
      cases fs with
      | nil => dsimp only [checkVal, Val.ty?] at hChk; cases hChk
      | cons v1 vs1 =>
          cases v1 with
          | bool _ | unit | char _ | ordering _ | enumVal _ _ | ptr _
          | slicePtr _ _ | rangeTo _ | rangeFrom _ | tuple _ | bytes _
          | array _ | optionVal _ | range _ _ | boxPtr _ _ | vec _ _ _ =>
              dsimp only [checkVal, Val.ty?] at hChk; cases hChk
          | scalar sv =>
              cases vs1 with
              | nil => dsimp only [checkVal, Val.ty?] at hChk; cases hChk
              | cons v2 vs2 =>
                  cases v2 with
                  | scalar _ | unit | char _ | ordering _ | enumVal _ _ | ptr _
                  | slicePtr _ _ | rangeTo _ | rangeFrom _ | tuple _
                  | bytes _ | array _ | optionVal _ | range _ _ | boxPtr _ _
                  | vec _ _ _ =>
                      dsimp only [checkVal, Val.ty?] at hChk; cases hChk
                  | bool b =>
                      cases vs2 with
                      | cons _ _ =>
                          dsimp only [checkVal, Val.ty?] at hChk; cases hChk
                      | nil =>
                          dsimp only [checkVal, Val.ty?] at hChk
                          cases hWf : sv.wf with
                          | false => rw [ite_cond_false hWf] at hChk; cases hChk
                          | true =>
                              rw [ite_cond_true hWf] at hChk
                              dsimp only at hChk
                              cases mty with
                              | tuple ms =>
                                  cases ms with
                                  | nil => cases hChk
                                  | cons m1 ms1 =>
                                      cases ms1 with
                                      | nil =>
                                          dsimp only [MirTy.beq, MirTy.beqList]
                                            at hChk
                                          cases (bool_and_right hChk)
                                      | cons m2 ms2 =>
                                          cases ms2 with
                                          | cons _ _ =>
                                              dsimp only [MirTy.beq,
                                                MirTy.beqList] at hChk
                                              cases (bool_and_right
                                                (bool_and_right hChk))
                                          | nil =>
                                              cases m1 with
                                              | int w s =>
                                                  cases m2 with
                                                  | bool =>
                                                      dsimp only [MirTy.beq,
                                                        MirTy.beqList] at hChk
                                                      exact .inr (.inr (.inr
                                                        (.inr (.inr (.inr
                                                          ⟨w, s, sv, b, rfl,
                                                            rfl, hWf,
                                                            intWidth_beq_eq
                                                              (bool_and_left
                                                                (bool_and_left
                                                                  hChk)),
                                                            eq_of_beq
                                                              (bool_and_right
                                                                (bool_and_left
                                                                  hChk))⟩)))))
                                                  | _ =>
                                                      have h2 := bool_and_left
                                                        (bool_and_right hChk)
                                                      cases h2
                                              | _ => cases hChk
                              | _ => cases hChk

private theorem toClosedMirTy?_eq_int {ty : OpenMirTy} {w : IntWidth}
    {s : Bool} (h : OpenMirTy.toClosedMirTy? ty = some (.int w s)) :
    ty = .int w s := by
  cases ty with
  | int _ _ => cases h; rfl
  | ref _ p | rawPtr _ p =>
      dsimp only [OpenMirTy.toClosedMirTy?] at h
      cases hp : OpenMirTy.toClosedMirTy? p <;> rw [hp] at h <;> cases h
  | tuple fs =>
      dsimp only [OpenMirTy.toClosedMirTy?] at h
      cases hf : OpenMirTy.toClosedMirTyList? fs <;> rw [hf] at h <;> cases h
  | _ => cases h

private theorem toClosedMirTy?_eq_bool {ty : OpenMirTy}
    (h : OpenMirTy.toClosedMirTy? ty = some .bool) : ty = .bool := by
  cases ty with
  | bool => rfl
  | ref _ p | rawPtr _ p =>
      dsimp only [OpenMirTy.toClosedMirTy?] at h
      cases hp : OpenMirTy.toClosedMirTy? p <;> rw [hp] at h <;> cases h
  | tuple fs =>
      dsimp only [OpenMirTy.toClosedMirTy?] at h
      cases hf : OpenMirTy.toClosedMirTyList? fs <;> rw [hf] at h <;> cases h
  | _ => cases h

theorem checkVal_implies_checkValAgainstSpec :
    ∀ (sub : OpenMirTy) (mty : MirTy) (sp : TypeLayoutSpec) (v : Val)
      (baseClosed : TypeSpecEnv),
      OpenMirTy.toClosedMirTy? sub = some mty →
      isSupportedScalarOrUnitTy mty = true →
      evalNormOpenTySpec baseClosed sub = some sp →
      checkVal v mty = true →
      checkValAgainstSpec v sp = true := by
  intro sub mty sp v baseClosed hCl hSupp hEval hChk
  cases sub with
  | slice _ | array _ _ | adt _ _ | param _ | assocProj _ _ _ _
  | unsupported =>
      cases hCl
  | ref _ p | rawPtr _ p =>
      dsimp only [OpenMirTy.toClosedMirTy?] at hCl
      cases hp : OpenMirTy.toClosedMirTy? p <;> rw [hp] at hCl <;> cases hCl
      cases hSupp
  | bool =>
      cases hCl; cases hEval
      cases checkVal_shape hChk with
      | inl hB => let ⟨_, _, hv⟩ := hB; rw [hv]; rfl
      | inr hR =>
          cases hR with
          | inl h => cases h.1
          | inr h => cases h with
            | inl h => let ⟨_, hm, _⟩ := h; cases hm
            | inr h => cases h with
              | inl h => let ⟨_, hm, _⟩ := h; cases hm
              | inr h => cases h with
                | inl h => let ⟨_, _, _, hm, _⟩ := h; cases hm
                | inr h => cases h with
                  | inl h => let ⟨_, _, hm, _⟩ := h; cases hm
                  | inr h => let ⟨_, _, _, _, hm, _⟩ := h; cases hm
  | unit =>
      cases hCl; cases hEval
      cases checkVal_shape hChk with
      | inl h => let ⟨_, hm, _⟩ := h; cases hm
      | inr hR =>
          cases hR with
          | inl h => rw [h.2]; rfl
          | inr h => cases h with
            | inl h => let ⟨_, hm, _⟩ := h; cases hm
            | inr h => cases h with
              | inl h => let ⟨_, hm, _⟩ := h; cases hm
              | inr h => cases h with
                | inl h => let ⟨_, _, _, hm, _⟩ := h; cases hm
                | inr h => cases h with
                  | inl h => let ⟨_, _, hm, _⟩ := h; cases hm
                  | inr h => let ⟨_, _, _, _, hm, _⟩ := h; cases hm
  | never =>
      cases hCl; cases hEval
      cases checkVal_shape hChk with
      | inl h => let ⟨_, hm, _⟩ := h; cases hm
      | inr hR =>
          cases hR with
          | inl h => cases h.1
          | inr h => cases h with
            | inl h => let ⟨_, hm, _⟩ := h; cases hm
            | inr h => cases h with
              | inl h => let ⟨_, hm, _⟩ := h; cases hm
              | inr h => cases h with
                | inl h => let ⟨_, _, _, hm, _⟩ := h; cases hm
                | inr h => cases h with
                  | inl h => let ⟨_, _, hm, _⟩ := h; cases hm
                  | inr h => let ⟨_, _, _, _, hm, _⟩ := h; cases hm
  | char =>
      cases hCl; cases hEval
      cases checkVal_shape hChk with
      | inl h => let ⟨_, hm, _⟩ := h; cases hm
      | inr hR =>
          cases hR with
          | inl h => cases h.1
          | inr h => cases h with
            | inl h =>
                let ⟨c, _, hv⟩ := h
                rw [hv]
                dsimp only [checkValAgainstSpec, charTypeLayoutSpec]
                rw [char_isUnicodeScalar c]
                rfl
            | inr h => cases h with
              | inl h => let ⟨_, hm, _⟩ := h; cases hm
              | inr h => cases h with
                | inl h => let ⟨_, _, _, hm, _⟩ := h; cases hm
                | inr h => cases h with
                  | inl h => let ⟨_, _, hm, _⟩ := h; cases hm
                  | inr h => let ⟨_, _, _, _, hm, _⟩ := h; cases hm
  | ordering =>
      cases hCl; cases hEval
      cases checkVal_shape hChk with
      | inl h => let ⟨_, hm, _⟩ := h; cases hm
      | inr hR =>
          cases hR with
          | inl h => cases h.1
          | inr h => cases h with
            | inl h => let ⟨_, hm, _⟩ := h; cases hm
            | inr h => cases h with
              | inl h => let ⟨_, _, hv⟩ := h; rw [hv]; rfl
              | inr h => cases h with
                | inl h => let ⟨_, _, _, hm, _⟩ := h; cases hm
                | inr h => cases h with
                  | inl h => let ⟨_, _, hm, _⟩ := h; cases hm
                  | inr h => let ⟨_, _, _, _, hm, _⟩ := h; cases hm
  | int w s =>
      cases hCl; cases hEval
      cases checkVal_shape hChk with
      | inl h => let ⟨_, hm, _⟩ := h; cases hm
      | inr hR =>
          cases hR with
          | inl h => cases h.1
          | inr h => cases h with
            | inl h => let ⟨_, hm, _⟩ := h; cases hm
            | inr h => cases h with
              | inl h => let ⟨_, hm, _⟩ := h; cases hm
              | inr h => cases h with
                | inl h =>
                    let ⟨w', s', sv, hm, hv, hWf, hW, _⟩ := h
                    cases hm
                    rw [hv]
                    dsimp only [checkValAgainstSpec, intTypeLayoutSpec]
                    exact checkScalarRoles_intRoles sv w hWf hW
                | inr h => cases h with
                  | inl h => let ⟨_, _, hm, _⟩ := h; cases hm
                  | inr h => let ⟨_, _, _, _, hm, _⟩ := h; cases hm
  | enum ety =>
      cases hCl
      dsimp only [evalNormOpenTySpec] at hEval
      cases checkVal_shape hChk with
      | inl h => let ⟨_, hm, _⟩ := h; cases hm
      | inr hR =>
          cases hR with
          | inl h => cases h.1
          | inr h => cases h with
            | inl h => let ⟨_, hm, _⟩ := h; cases hm
            | inr h => cases h with
              | inl h => let ⟨_, hm, _⟩ := h; cases hm
              | inr h => cases h with
                | inl h => let ⟨_, _, _, hm, _⟩ := h; cases hm
                | inr h => cases h with
                  | inl h =>
                      let ⟨ety', idx, hm, hv, hAdm, hIdxLt⟩ := h
                      cases hm
                      rw [hv]
                      have hIdx := Nat.blt_eq.mpr hIdxLt
                      unfold enumTypeLayoutSpec at hEval
                      rw [ite_not_true hAdm] at hEval
                      cases hTag : ety.tagRepr with
                      | zeroSized =>
                          rw [hTag] at hEval
                          cases hEval
                          dsimp only [checkValAgainstSpec]
                          rw [hAdm, hIdx]
                          unfold enumTypeLayoutSpec
                          rw [ite_not_true hAdm, hTag]
                          dsimp only
                          rw [enumTy_beq_self]
                          rfl
                      | scalar tagW tagS =>
                          rw [hTag] at hEval
                          cases hEval
                          dsimp only [checkValAgainstSpec]
                          rw [hAdm, hIdx]
                          unfold enumTypeLayoutSpec
                          rw [ite_not_true hAdm, hTag]
                          dsimp only
                          rw [enumTy_beq_self,
                            nat_beq_self (intLayout tagW).size,
                            byteRolesBeq_self]
                          rfl
                  | inr h => let ⟨_, _, _, _, hm, _⟩ := h; cases hm
  | tuple fs =>
      cases fs with
      | nil => cases hCl; cases hSupp
      | cons a rest =>
          dsimp only [OpenMirTy.toClosedMirTy?,
            OpenMirTy.toClosedMirTyList?] at hCl
          cases ha : OpenMirTy.toClosedMirTy? a with
          | none => rw [ha] at hCl; cases hCl
          | some ca =>
              rw [ha] at hCl
              cases rest with
              | nil =>
                  dsimp only [OpenMirTy.toClosedMirTyList?] at hCl
                  cases hCl
                  simp only [isSupportedScalarOrUnitTy, isOverflowPairTy] at hSupp
                  cases hSupp
              | cons b0 tl =>
                  dsimp only [OpenMirTy.toClosedMirTyList?] at hCl
                  cases hb : OpenMirTy.toClosedMirTy? b0 with
                  | none => rw [hb] at hCl; cases hCl
                  | some cb =>
                      rw [hb] at hCl
                      cases tl with
                      | cons c cs =>
                          dsimp only [OpenMirTy.toClosedMirTyList?] at hCl
                          cases hc : OpenMirTy.toClosedMirTy? c with
                          | none => rw [hc] at hCl; cases hCl
                          | some _ =>
                              rw [hc] at hCl
                              cases hcs : OpenMirTy.toClosedMirTyList? cs with
                              | none => rw [hcs] at hCl; cases hCl
                              | some _ =>
                                  rw [hcs] at hCl
                                  cases hCl
                                  simp only [isSupportedScalarOrUnitTy,
                                    isOverflowPairTy] at hSupp
                                  cases hSupp
                      | nil =>
                          cases hCl
                          cases ca with
                          | bool | unit | never | char | ordering | enum _
                          | tuple _ | ref _ _ | rawPtr _ _ | slice _ | str
                          | rangeTo _ | rangeFrom _ | array _ _
                          | unsupported | option _ | range _ | box _ | vec _ =>
                              cases hSupp
                          | int w s =>
                              cases cb with
                              | int _ _ | unit | never | char | ordering
                              | enum _ | tuple _ | ref _ _ | rawPtr _ _
                              | slice _ | str | rangeTo _ | rangeFrom _
                              | array _ _ | unsupported | option _ | range _
                              | box _ | vec _ =>
                                  cases hSupp
                              | bool =>
                                  have haEq := toClosedMirTy?_eq_int ha
                                  have hbEq := toClosedMirTy?_eq_bool hb
                                  subst haEq; subst hbEq
                                  cases hEval
                                  cases checkVal_shape hChk with
                                  | inl h => let ⟨_, hm, _⟩ := h; cases hm
                                  | inr hR =>
                                      cases hR with
                                      | inl h => cases h.1
                                      | inr h => cases h with
                                        | inl h => let ⟨_, hm, _⟩ := h; cases hm
                                        | inr h => cases h with
                                          | inl h =>
                                              let ⟨_, hm, _⟩ := h; cases hm
                                          | inr h => cases h with
                                            | inl h =>
                                                let ⟨_, _, _, hm, _⟩ := h
                                                cases hm
                                            | inr h => cases h with
                                              | inl h =>
                                                  let ⟨_, _, hm, _⟩ := h
                                                  cases hm
                                              | inr h =>
                                                  let ⟨w', s', sv, b, hm, hv,
                                                    hWf, hW, _⟩ := h
                                                  cases hm; rw [hv]
                                                  dsimp only [
                                                    checkValAgainstSpec,
                                                    overflowPairTypeLayoutSpec]
                                                  rw [hWf, hW,
                                                    nat_beq_self
                                                      (overflowPairLayout
                                                        w).size,
                                                    byteRolesBeq_self]
                                                  rfl

private theorem openListGet?_replicate_true (n i : Nat)
    (inv : List AllocByte → Prop)
    (h : openListGet? (List.replicate n (fun _ : List AllocByte => True)) i =
      some inv) :
    inv = (fun _ : List AllocByte => True) := by
  induction n generalizing i with
  | zero => cases h
  | succ k ih =>
      cases i with
      | zero => cases h; rfl
      | succ j => exact ih j h

private theorem argsSatisfyParamInvs_replicate_true (prog : OpenProgram)
    (env : OpenExecEnv) (ts : TypeSpecEnv) (n : Nat) :
    ∀ (args : List Val) (tys : List OpenMirTy),
      args.length = tys.length →
      argsSatisfyParamInvs prog
        { env with typeSpecs := { ts with
            paramInvs := List.replicate n (fun _ => True) } }
        args tys
  | [], [], _ => True.intro
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | v :: vs, t :: ts', h => by
      have hTail := argsSatisfyParamInvs_replicate_true prog env ts n vs ts'
        (Nat.succ.inj h)
      refine ⟨?_, hTail⟩
      dsimp only
      cases hN : normalizeOpenTy prog.traitRegistry normFuel t with
      | param i =>
          cases v with
          | bytes bs =>
              dsimp only
              cases hGet : openListGet?
                  (List.replicate n (fun _ : List AllocByte => True)) i with
              | none => exact True.intro
              | some inv =>
                  rw [openListGet?_replicate_true n i inv hGet]
                  exact True.intro
          | bool _ | scalar _ | unit | char _ | ordering _
          | enumVal _ _ | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _
          | tuple _ | array _ | optionVal _ | range _ _ | vec _ _ _
          | boxPtr _ _ => exact True.intro
      | bool | int _ _ | unit | never | char | ordering | enum _ | tuple _
      | slice _ | array _ _ | adt _ _ | ref _ _ | rawPtr _ _
      | assocProj _ _ _ _ | unsupported =>
          cases v <;> exact True.intro

private theorem checkVal_erased_to_checkOpenVal (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env : OpenExecEnv) (σ : List OpenMirTy) (paramSpecs : List TypeLayoutSpec)
    (paramInvs : List (List AllocByte → Prop))
    (hLenEq : paramSpecs.length = σ.length)
    (hMap : ∀ (i : Nat) (ty : OpenMirTy), openListGet? σ i = some ty →
      ∃ sp : TypeLayoutSpec, openListGet? paramSpecs i = some sp ∧
        evalOpenTySpec prog.traitRegistry normFuel
          { env.typeSpecs with paramSpecs := [], paramInvs := [] } ty =
          some sp ∧
        OpenMirTy.isClosed ty = true)
    (ty : OpenMirTy) (mty : MirTy) (sp : TypeLayoutSpec) (v : Val)
    (hClSub : OpenMirTy.toClosedMirTy?
      (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ ty) = some mty)
    (hSupp : isSupportedScalarOrUnitTy mty = true)
    (hEval : evalOpenTySpec prog.traitRegistry normFuel
      (substTypeSpecEnv env.typeSpecs paramSpecs paramInvs
        (instAssocSpecs prog.traitRegistry env.typeSpecs σ)) ty = some sp)
    (hChk : checkVal v mty = true) :
    checkOpenVal prog
      { env with typeSpecs := (substTypeSpecEnv env.typeSpecs paramSpecs
          paramInvs (instAssocSpecs prog.traitRegistry env.typeSpecs σ)) }
      v ty = true := by
  let env' : OpenExecEnv :=
    { env with typeSpecs := (substTypeSpecEnv env.typeSpecs paramSpecs
        paramInvs (instAssocSpecs prog.traitRegistry env.typeSpecs σ)) }
  let baseClosed : TypeSpecEnv :=
    { env.typeSpecs with paramSpecs := [], paramInvs := [] }
  have hSubEval :
      evalOpenTySpec prog.traitRegistry normFuel baseClosed
        (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ ty) =
        some sp :=
    evalOpenTySpec_subst_param_some prog hRegWf env σ paramSpecs paramInvs
      hLenEq hMap ty sp hEval
  have hSubClosed : OpenMirTy.isClosed
      (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ ty) = true :=
    toClosedMirTy?_isClosed hClSub
  have hNormEval :
      evalNormOpenTySpec baseClosed
        (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ ty) =
        some sp := by
    unfold evalOpenTySpec at hSubEval
    rw [normalizeOpenTy_isClosed prog.traitRegistry
      normFuel _ hSubClosed] at hSubEval
    exact hSubEval
  have hAg := checkVal_implies_checkValAgainstSpec
    (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ ty) mty sp v
    baseClosed hClSub hSupp hNormEval hChk
  unfold checkOpenVal
  cases hTyCl : OpenMirTy.toClosedMirTy? ty with
  | some mty0 =>
      have hEq : OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ ty =
          ty := toClosedMirTy?_substAndNormalize_eq prog.traitRegistry σ hTyCl
      rw [hEq, hTyCl] at hClSub
      cases hClSub
      dsimp only
      rw [hSupp]
      exact hChk
  | none =>
      dsimp only [checkOpenValOnSpec]
      rw [hEval]
      exact hAg

private theorem erasedTy_local_props (prog : OpenProgram)
    (env' : OpenExecEnv) (σ : List OpenMirTy) (ob : OpenBody)
    (erasedOb : Body)
    (hObEq : OpenBody.toDay1? (OpenBody.subst prog.traitRegistry normFuel σ ob) =
      some erasedOb)
    (hAdm : openLocalsAdmitted prog env' ob.locals)
    (hSupp : erasedOb.locals.all isSupportedScalarOrUnitTy = true) :
    ∀ (i : Nat) (ty : OpenMirTy),
      openListGet? ob.locals i = some ty →
      ∃ (mty : MirTy) (sp : TypeLayoutSpec),
        OpenMirTy.toClosedMirTy?
          (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ ty) =
          some mty ∧
        Trusted.MirSemantics.getElem? erasedOb.locals i = some mty ∧
        isSupportedScalarOrUnitTy mty = true ∧
        evalOpenTySpec prog.traitRegistry normFuel env'.typeSpecs ty = some sp ∧
        WellFormedTypeLayoutSpec sp ∧
        sp.isSized = true := by
  dsimp only [OpenBody.toDay1?, OpenBody.subst] at hObEq
  cases hLoc : OpenMirTy.toClosedMirTyList?
      (ob.locals.map (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ))
      with
  | none => rw [hLoc] at hObEq; cases hObEq
  | some dLoc =>
      rw [hLoc] at hObEq
      cases hBbs : OpenBasicBlock.toDay1List? _ with
      | none => rw [hBbs] at hObEq; cases hObEq
      | some _ =>
          rw [hBbs] at hObEq
          cases hObEq
          dsimp only at hSupp
          have hAux : ∀ (tys : List OpenMirTy) (mtys : List MirTy) (k : Nat)
              (ty : OpenMirTy),
              OpenMirTy.toClosedMirTyList?
                (tys.map (OpenMirTy.substAndNormalize prog.traitRegistry
                  normFuel σ)) = some mtys →
              openLocalsAdmitted prog env' tys →
              mtys.all isSupportedScalarOrUnitTy = true →
              openListGet? tys k = some ty →
              ∃ (mty : MirTy) (sp : TypeLayoutSpec),
                OpenMirTy.toClosedMirTy?
                  (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ ty)
                  = some mty ∧
                Trusted.MirSemantics.getElem? mtys k = some mty ∧
                isSupportedScalarOrUnitTy mty = true ∧
                evalOpenTySpec prog.traitRegistry normFuel env'.typeSpecs ty =
                  some sp ∧
                WellFormedTypeLayoutSpec sp ∧
                sp.isSized = true := by
            intro tys
            induction tys with
            | nil => intro _ _ _ _ _ _ hG; cases hG
            | cons x xs ih =>
                intro mtys k ty hL hA hS hG
                dsimp only [List.map, OpenMirTy.toClosedMirTyList?] at hL
                cases hx : OpenMirTy.toClosedMirTy?
                    (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ
                      x) with
                | none => rw [hx] at hL; cases hL
                | some cx =>
                    rw [hx] at hL
                    cases hxs : OpenMirTy.toClosedMirTyList?
                        (xs.map (OpenMirTy.substAndNormalize prog.traitRegistry
                          normFuel σ)) with
                    | none => rw [hxs] at hL; cases hL
                    | some cxs =>
                        rw [hxs] at hL; cases hL
                        dsimp only [List.all] at hS
                        cases k with
                        | zero =>
                            cases hG
                            exact ⟨cx, by
                              let ⟨sp, _, hEv, hWf, hSz⟩ := hA.1
                              exact ⟨sp, hx, rfl, bool_and_left hS, hEv, hWf,
                                hSz⟩⟩
                        | succ j =>
                            exact ih cxs j ty hxs hA.2 (bool_and_right hS) hG
          intro i ty hG
          exact hAux ob.locals dLoc i ty hLoc hAdm hSupp hG

private theorem erasedOb_locals_eq_map (prog : OpenProgram) (σ : List OpenMirTy)
    (ob : OpenBody) (erasedOb : Body)
    (hObEq : OpenBody.toDay1? (OpenBody.subst prog.traitRegistry normFuel σ ob) =
      some erasedOb) :
    erasedOb.locals =
      ob.locals.map (fun ty =>
        eraseOpenTy
          (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ ty)) ∧
    erasedOb.argumentCount = ob.argumentCount ∧
    erasedOb.basicBlocks =
      (ob.basicBlocks.map (OpenBasicBlock.subst prog.traitRegistry normFuel σ)).map
        eraseOpenBasicBlock := by
  dsimp only [OpenBody.toDay1?, OpenBody.subst] at hObEq
  cases hLoc : OpenMirTy.toClosedMirTyList?
      (ob.locals.map (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ))
      with
  | none => rw [hLoc] at hObEq; cases hObEq
  | some dLoc =>
      rw [hLoc] at hObEq
      cases hBbs : OpenBasicBlock.toDay1List?
          (ob.basicBlocks.map (OpenBasicBlock.subst prog.traitRegistry normFuel σ))
          with
      | none => rw [hBbs] at hObEq; cases hObEq
      | some dBbs =>
          rw [hBbs] at hObEq; cases hObEq
          have hMapLoc : ∀ {xs : List OpenMirTy} {cs : List MirTy},
              OpenMirTy.toClosedMirTyList? xs = some cs →
              cs = xs.map eraseOpenTy := by
            intro xs
            induction xs with
            | nil => intro cs h; cases h; rfl
            | cons x xs ih =>
                intro cs h
                dsimp only [OpenMirTy.toClosedMirTyList?] at h
                cases hx : OpenMirTy.toClosedMirTy? x with
                | none => rw [hx] at h; cases h
                | some cx =>
                    rw [hx] at h
                    cases hxs : OpenMirTy.toClosedMirTyList? xs with
                    | none => rw [hxs] at h; cases h
                    | some cxs =>
                        rw [hxs] at h; cases h
                        dsimp only [List.map]
                        rw [← toClosedMirTy?_eraseOpenTy hx, ih hxs]
          have hMapBbs : ∀ {xs : List OpenBasicBlock} {ds : List BasicBlock},
              OpenBasicBlock.toDay1List? xs = some ds →
              ds = xs.map eraseOpenBasicBlock := by
            intro xs
            induction xs with
            | nil => intro ds h; cases h; rfl
            | cons x xs ih =>
                intro ds h
                dsimp only [OpenBasicBlock.toDay1List?] at h
                cases hx : OpenBasicBlock.toDay1? x with
                | none => rw [hx] at h; cases h
                | some dx =>
                    rw [hx] at h
                    cases hxs : OpenBasicBlock.toDay1List? xs with
                    | none => rw [hxs] at h; cases h
                    | some dxs =>
                        rw [hxs] at h; cases h
                        dsimp only [List.map]
                        have hSub : ∀ {b : OpenBasicBlock} {db : BasicBlock},
                            OpenBasicBlock.toDay1? b = some db →
                            db = eraseOpenBasicBlock b := by
                          intro b db hb
                          have h1 : ∀ {e : OpenProjectionElem} {de : ProjectionElem},
                              OpenProjectionElem.toDay1? e = some de →
                              de = eraseOpenProjectionElem e := by
                            intro e de he
                            cases e with
                            | deref => cases he; rfl
                            | unsupported => cases he; rfl
                            | field _ ty =>
                                dsimp only [OpenProjectionElem.toDay1?] at he
                                cases ht : OpenMirTy.toClosedMirTy? ty with
                                | none => rw [ht] at he; cases he
                                | some _ =>
                                    rw [ht] at he; cases he
                                    dsimp only [eraseOpenProjectionElem]
                                    rw [toClosedMirTy?_eraseOpenTy ht]
                          have h2 : ∀ {es : List OpenProjectionElem}
                              {des : List ProjectionElem},
                              OpenProjectionElem.toDay1List? es = some des →
                              des = es.map eraseOpenProjectionElem := by
                            intro es
                            induction es with
                            | nil => intro des he; cases he; rfl
                            | cons e es' ih' =>
                                intro des he
                                dsimp only [OpenProjectionElem.toDay1List?] at he
                                cases hE : OpenProjectionElem.toDay1? e with
                                | none => rw [hE] at he; cases he
                                | some dE =>
                                    rw [hE] at he
                                    cases hEs : OpenProjectionElem.toDay1List? es' with
                                    | none => rw [hEs] at he; cases he
                                    | some dEs =>
                                        rw [hEs] at he; cases he
                                        dsimp only [List.map]
                                        rw [← h1 hE, ih' hEs]
                          have h3 : ∀ {p : OpenPlace} {dp : Place},
                              OpenPlace.toDay1? p = some dp →
                              dp = eraseOpenPlace p := by
                            intro p dp hp
                            dsimp only [OpenPlace.toDay1?] at hp
                            cases hPs : OpenProjectionElem.toDay1List? p.projection with
                            | none => rw [hPs] at hp; cases hp
                            | some ps =>
                                rw [hPs] at hp; cases hp
                                dsimp only [eraseOpenPlace]
                                rw [h2 hPs]
                          have h4 : ∀ {op : OpenOperand} {dop : Operand},
                              OpenOperand.toDay1? op = some dop →
                              dop = eraseOpenOperand op := by
                            intro op dop hop
                            cases op with
                            | copy p =>
                                dsimp only [OpenOperand.toDay1?] at hop
                                cases hp : OpenPlace.toDay1? p with
                                | none => rw [hp] at hop; cases hop
                                | some dp =>
                                    rw [hp] at hop; cases hop
                                    exact congrArg Operand.copy (h3 hp)
                            | move p =>
                                dsimp only [OpenOperand.toDay1?] at hop
                                cases hp : OpenPlace.toDay1? p with
                                | none => rw [hp] at hop; cases hop
                                | some dp =>
                                    rw [hp] at hop; cases hop
                                    exact congrArg Operand.move (h3 hp)
                            | constant c =>
                                dsimp only [OpenOperand.toDay1?] at hop
                                cases ht : OpenMirTy.toClosedMirTy? c.ty with
                                | none => rw [ht] at hop; cases hop
                                | some _ =>
                                    rw [ht] at hop; cases hop
                                    dsimp only [eraseOpenOperand]
                                    rw [toClosedMirTy?_eraseOpenTy ht]
                          have h5 : ∀ {ops : List OpenOperand} {dops : List Operand},
                              OpenOperand.toDay1List? ops = some dops →
                              dops = ops.map eraseOpenOperand := by
                            intro ops
                            induction ops with
                            | nil => intro dops ho; cases ho; rfl
                            | cons o os ih' =>
                                intro dops ho
                                dsimp only [OpenOperand.toDay1List?] at ho
                                cases hO : OpenOperand.toDay1? o with
                                | none => rw [hO] at ho; cases ho
                                | some dO =>
                                    rw [hO] at ho
                                    cases hOs : OpenOperand.toDay1List? os with
                                    | none => rw [hOs] at ho; cases ho
                                    | some dOs =>
                                        rw [hOs] at ho; cases ho
                                        dsimp only [List.map]
                                        rw [← h4 hO, ih' hOs]
                          have h6 : ∀ {rv : OpenRvalue} {drv : Rvalue},
                              OpenRvalue.toDay1? rv = some drv →
                              drv = eraseOpenRvalue rv := by
                            intro rv drv hrv
                            cases rv with
                            | use op =>
                                dsimp only [OpenRvalue.toDay1?] at hrv
                                cases ho : OpenOperand.toDay1? op with
                                | none => rw [ho] at hrv; cases hrv
                                | some do_ =>
                                    rw [ho] at hrv; cases hrv
                                    exact congrArg Rvalue.use (h4 ho)
                            | binaryOp op l r =>
                                dsimp only [OpenRvalue.toDay1?] at hrv
                                cases hl : OpenOperand.toDay1? l with
                                | none => rw [hl] at hrv; cases hrv
                                | some dl =>
                                    rw [hl] at hrv
                                    cases hr : OpenOperand.toDay1? r with
                                    | none => rw [hr] at hrv; cases hrv
                                    | some dr =>
                                        rw [hr] at hrv; cases hrv
                                        dsimp only [eraseOpenRvalue]
                                        rw [h4 hl, h4 hr]
                            | unaryOp op opnd =>
                                dsimp only [OpenRvalue.toDay1?] at hrv
                                cases ho : OpenOperand.toDay1? opnd with
                                | none => rw [ho] at hrv; cases hrv
                                | some do_ =>
                                    rw [ho] at hrv; cases hrv
                                    exact congrArg (Rvalue.unaryOp op) (h4 ho)
                            | cast k opnd ty =>
                                dsimp only [OpenRvalue.toDay1?] at hrv
                                cases ho : OpenOperand.toDay1? opnd with
                                | none => rw [ho] at hrv; cases hrv
                                | some do_ =>
                                    rw [ho] at hrv
                                    cases ht : OpenMirTy.toClosedMirTy? ty with
                                    | none => rw [ht] at hrv; cases hrv
                                    | some _ =>
                                        rw [ht] at hrv; cases hrv
                                        dsimp only [eraseOpenRvalue]
                                        rw [h4 ho, toClosedMirTy?_eraseOpenTy ht]
                            | discriminant p =>
                                dsimp only [OpenRvalue.toDay1?] at hrv
                                cases hp : OpenPlace.toDay1? p with
                                | none => rw [hp] at hrv; cases hrv
                                | some dp =>
                                    rw [hp] at hrv; cases hrv
                                    exact congrArg Rvalue.discriminant (h3 hp)
                            | ref m p =>
                                dsimp only [OpenRvalue.toDay1?] at hrv
                                cases hp : OpenPlace.toDay1? p with
                                | none => rw [hp] at hrv; cases hrv
                                | some dp =>
                                    rw [hp] at hrv; cases hrv
                                    exact congrArg (Rvalue.ref m) (h3 hp)
                            | addressOf m p =>
                                dsimp only [OpenRvalue.toDay1?] at hrv
                                cases hp : OpenPlace.toDay1? p with
                                | none => rw [hp] at hrv; cases hrv
                                | some dp =>
                                    rw [hp] at hrv; cases hrv
                                    exact congrArg (Rvalue.addressOf m) (h3 hp)
                            | aggregateTuple fs =>
                                dsimp only [OpenRvalue.toDay1?] at hrv
                                cases hfs : OpenOperand.toDay1List? fs with
                                | none => rw [hfs] at hrv; cases hrv
                                | some dfs =>
                                    rw [hfs] at hrv; cases hrv
                                    exact congrArg Rvalue.aggregateTuple (h5 hfs)
                            | unsupported => cases hrv; rfl
                          have h7 : ∀ {st : OpenStatementKind} {dst : StatementKind},
                              OpenStatementKind.toDay1? st = some dst →
                              dst = eraseOpenStatementKind st := by
                            intro st dst hst
                            cases st with
                            | storageLive _ | storageDead _ | nop | unsupported =>
                                cases hst; rfl
                            | assign dst' rv' =>
                                dsimp only [OpenStatementKind.toDay1?] at hst
                                cases hp : OpenPlace.toDay1? dst' with
                                | none => rw [hp] at hst; cases hst
                                | some dp =>
                                    rw [hp] at hst
                                    cases hrv : OpenRvalue.toDay1? rv' with
                                    | none => rw [hrv] at hst; cases hst
                                    | some drv =>
                                        rw [hrv] at hst; cases hst
                                        dsimp only [eraseOpenStatementKind]
                                        rw [h3 hp, h6 hrv]
                          have h8 : ∀ {sts : List OpenStatementKind}
                              {dsts : List StatementKind},
                              OpenStatementKind.toDay1List? sts = some dsts →
                              dsts = sts.map eraseOpenStatementKind := by
                            intro sts
                            induction sts with
                            | nil => intro dsts hs'; cases hs'; rfl
                            | cons s ss ih' =>
                                intro dsts hs'
                                dsimp only [OpenStatementKind.toDay1List?] at hs'
                                cases hS : OpenStatementKind.toDay1? s with
                                | none => rw [hS] at hs'; cases hs'
                                | some dS =>
                                    rw [hS] at hs'
                                    cases hSs : OpenStatementKind.toDay1List? ss with
                                    | none => rw [hSs] at hs'; cases hs'
                                    | some dSs =>
                                        rw [hSs] at hs'; cases hs'
                                        dsimp only [List.map]
                                        rw [← h7 hS, ih' hSs]
                          have h9 : ∀ {tm : OpenTerminatorKind} {dtm : TerminatorKind},
                              OpenTerminatorKind.toDay1? tm = some dtm →
                              dtm = eraseOpenTerminatorKind tm := by
                            intro tm dtm htm
                            cases tm with
                            | goto _ | return_ | unreachable | unwindResume
                            | unsupported => cases htm; rfl
                            | traitCall _ _ _ _ _ _ _ _ => cases htm
                            | switchInt d tgts =>
                                dsimp only [OpenTerminatorKind.toDay1?] at htm
                                cases hd : OpenOperand.toDay1? d with
                                | none => rw [hd] at htm; cases htm
                                | some dd =>
                                    rw [hd] at htm; cases htm
                                    dsimp only [eraseOpenTerminatorKind]
                                    rw [h4 hd]
                            | assert cond exp msg tgt uw =>
                                dsimp only [OpenTerminatorKind.toDay1?] at htm
                                cases hc : OpenOperand.toDay1? cond with
                                | none => rw [hc] at htm; cases htm
                                | some dc =>
                                    rw [hc] at htm; cases htm
                                    dsimp only [eraseOpenTerminatorKind]
                                    rw [h4 hc]
                            | call _ _ _ _ _ _ =>
                                dsimp only [OpenTerminatorKind.toDay1?] at htm
                                cases htm
                          dsimp only [OpenBasicBlock.toDay1?] at hb
                          cases hSts : OpenStatementKind.toDay1List? b.statements with
                          | none => rw [hSts] at hb; cases hb
                          | some dSts =>
                              rw [hSts] at hb
                              cases hTm : OpenTerminatorKind.toDay1? b.terminator with
                              | none => rw [hTm] at hb; cases hb
                              | some dTm =>
                                  rw [hTm] at hb; cases hb
                                  dsimp only [eraseOpenBasicBlock]
                                  rw [h8 hSts, h9 hTm]
                        rw [← hSub hx, ih hxs]
          refine ⟨?_, rfl, hMapBbs hBbs⟩
          rw [hMapLoc hLoc, list_map_map]

private theorem list_drop_take_mem {α : Type} :
    ∀ (xs : List α) (d t : Nat) (x : α),
      x ∈ (xs.drop d).take t → x ∈ xs := by
  intro xs d t x hMem
  have hDrop : ∀ (ys : List α) (k : Nat) (y : α),
      y ∈ ys.drop k → y ∈ ys := by
    intro ys
    induction ys with
    | nil => intro k y h; cases k <;> cases h
    | cons a as ih =>
        intro k y h
        cases k with
        | zero => exact h
        | succ j => exact List.Mem.tail a (ih j y h)
  have hTake : ∀ (ys : List α) (k : Nat) (y : α),
      y ∈ ys.take k → y ∈ ys := by
    intro ys
    induction ys with
    | nil => intro k y h; cases k <;> cases h
    | cons a as ih =>
        intro k y h
        cases k with
        | zero => cases h
        | succ j =>
            cases h with
            | head _ => exact List.Mem.head _
            | tail _ ht => exact List.Mem.tail a (ih j y ht)
  exact hDrop xs d x (hTake (xs.drop d) t x hMem)

private theorem validEntryArgs_to_validOpenEntryArgs (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env : OpenExecEnv) (σ : List OpenMirTy) (paramSpecs : List TypeLayoutSpec)
    (hLenEq : paramSpecs.length = σ.length)
    (hMap : ∀ (i : Nat) (ty : OpenMirTy), openListGet? σ i = some ty →
      ∃ sp : TypeLayoutSpec, openListGet? paramSpecs i = some sp ∧
        evalOpenTySpec prog.traitRegistry normFuel
          { env.typeSpecs with paramSpecs := [], paramInvs := [] } ty =
          some sp ∧
        OpenMirTy.isClosed ty = true)
    (ob : OpenBody) (erasedOb : Body)
    (hObEq : OpenBody.toDay1? (OpenBody.subst prog.traitRegistry normFuel σ ob) =
      some erasedOb)
    (hAdm : openLocalsAdmitted prog
      { env with typeSpecs := (substTypeSpecEnv env.typeSpecs paramSpecs
          (List.replicate paramSpecs.length (fun _ => True))
          (instAssocSpecs prog.traitRegistry env.typeSpecs σ)) }
      ob.locals)
    (hSupp : erasedOb.locals.all isSupportedScalarOrUnitTy = true)
    (args : List Val) (hValid : ValidEntryArgs erasedOb args) :
    ValidOpenEntryArgs prog
      { env with typeSpecs := (substTypeSpecEnv env.typeSpecs paramSpecs
          (List.replicate paramSpecs.length (fun _ => True))
          (instAssocSpecs prog.traitRegistry env.typeSpecs σ)) }
      ob args := by
  let paramInvs := List.replicate paramSpecs.length (fun _ : List AllocByte => True)
  let env' : OpenExecEnv :=
    { env with typeSpecs := (substTypeSpecEnv env.typeSpecs paramSpecs
        paramInvs (instAssocSpecs prog.traitRegistry env.typeSpecs σ)) }
  have hParts := erasedOb_locals_eq_map prog σ ob erasedOb hObEq
  have hDropMap :
      (erasedOb.locals.drop 1).take erasedOb.argumentCount =
        ((ob.locals.drop 1).take ob.argumentCount).map (fun ty =>
          eraseOpenTy
            (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ ty)) := by
    rw [hParts.1, hParts.2.1, list_map_drop, list_map_take]
  have hPerMem : ∀ ty : OpenMirTy, ty ∈ ob.locals →
      ∃ (mty : MirTy) (sp : TypeLayoutSpec),
        OpenMirTy.toClosedMirTy?
          (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ ty) =
          some mty ∧
        isSupportedScalarOrUnitTy mty = true ∧
        evalOpenTySpec prog.traitRegistry normFuel env'.typeSpecs ty = some sp := by
    intro ty hMem
    have hFind : ∀ (xs : List OpenMirTy), ty ∈ xs →
        ∃ k, openListGet? xs k = some ty := by
      intro xs hm
      induction xs with
      | nil => cases hm
      | cons a as ih =>
          cases hm with
          | head _ => exact ⟨0, rfl⟩
          | tail _ ht => let ⟨j, hj⟩ := ih ht; exact ⟨j + 1, hj⟩
    let ⟨i, hi⟩ := hFind ob.locals hMem
    let ⟨mty, sp, hCl, _, hSup, hEv, _, _⟩ :=
      erasedTy_local_props prog env' σ ob erasedOb hObEq hAdm hSupp i ty hi
    exact ⟨mty, sp, hCl, hSup, hEv⟩
  have hChk : checkOpenArgsMatch prog env' args
      ((ob.locals.drop 1).take ob.argumentCount) = true := by
    unfold ValidEntryArgs at hValid
    rw [hDropMap] at hValid
    have hAux : ∀ (vs : List Val) (tys : List OpenMirTy),
        (∀ t, t ∈ tys → t ∈ ob.locals) →
        checkArgsMatch vs (tys.map (fun ty =>
          eraseOpenTy
            (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ ty))) =
          true →
        checkOpenArgsMatch prog env' vs tys = true := by
      intro vs
      induction vs with
      | nil =>
          intro tys _ hA
          cases tys with
          | nil => rfl
          | cons _ _ => cases hA
      | cons v vs ih =>
          intro tys hSub hA
          cases tys with
          | nil => cases hA
          | cons t ts =>
              dsimp only [List.map, checkArgsMatch] at hA
              dsimp only [checkOpenArgsMatch]
              have hv := bool_and_left hA
              have hvs := bool_and_right hA
              let ⟨mty, sp, hCl, hSup, hEv⟩ :=
                hPerMem t (hSub t (List.Mem.head ts))
              rw [toClosedMirTy?_eraseOpenTy hCl] at hv
              have hv' := checkVal_erased_to_checkOpenVal prog hRegWf env σ
                paramSpecs paramInvs hLenEq hMap t mty sp v hCl hSup hEv hv
              exact bool_and_eq_true hv'
                (ih ts (fun u hu => hSub u (List.Mem.tail t hu)) hvs)
    exact hAux args ((ob.locals.drop 1).take ob.argumentCount)
      (fun t ht => list_drop_take_mem ob.locals 1 ob.argumentCount t ht)
      hValid
  have hLenArgs : args.length = ((ob.locals.drop 1).take ob.argumentCount).length := by
    have hAuxLen : ∀ (vs : List Val) (ts : List MirTy),
        checkArgsMatch vs ts = true → vs.length = ts.length := by
      intro vs
      induction vs with
      | nil => intro ts h; cases ts with | nil => rfl | cons _ _ => cases h
      | cons _ _ ih =>
          intro ts h
          cases ts with
          | nil => cases h
          | cons _ ts' =>
              dsimp only [checkArgsMatch] at h
              exact congrArg Nat.succ (ih ts' (bool_and_right h))
    unfold ValidEntryArgs at hValid
    rw [hParts.1, hParts.2.1, list_map_drop, list_map_take] at hValid
    have hEq := hAuxLen args _ hValid
    rw [length_map_eq] at hEq
    exact hEq
  have hTsEq :
      { (substTypeSpecEnv env.typeSpecs paramSpecs
          (List.replicate paramSpecs.length (fun _ => True))
          (instAssocSpecs prog.traitRegistry env.typeSpecs σ)) with
        paramInvs := List.replicate paramSpecs.length (fun _ => True) } =
      substTypeSpecEnv env.typeSpecs paramSpecs
        (List.replicate paramSpecs.length (fun _ => True))
        (instAssocSpecs prog.traitRegistry env.typeSpecs σ) := rfl
  refine ⟨hChk, ?_⟩
  rw [← hTsEq]
  exact argsSatisfyParamInvs_replicate_true prog env
    (substTypeSpecEnv env.typeSpecs paramSpecs
      (List.replicate paramSpecs.length (fun _ => True))
      (instAssocSpecs prog.traitRegistry env.typeSpecs σ))
    paramSpecs.length args ((ob.locals.drop 1).take ob.argumentCount) hLenArgs

noncomputable def erasedTy (prog : OpenProgram) (σ : List OpenMirTy)
    (ty : OpenMirTy) : MirTy :=
  eraseOpenTy (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ ty)

private theorem erasedTy_def (prog : OpenProgram) (σ : List OpenMirTy)
    (ty : OpenMirTy) :
    eraseOpenTy (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ ty) =
      erasedTy prog σ ty := by
  unfold erasedTy; rfl

private theorem map_substAndNormalize_eq_erasedTy (prog : OpenProgram)
    (σ : List OpenMirTy) (tys : List OpenMirTy) :
    tys.map (fun ty =>
      eraseOpenTy
        (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ ty)) =
      tys.map (erasedTy prog σ) := by
  unfold erasedTy; rfl

def ValRel (mty : MirTy) (vd vo : Val) : Prop :=
  checkVal vd mty = true ∧
  (vd = vo ∨
   (mty = .unit ∧ vd = .unit ∧ vo = .bytes []) ∨
   (∃ ety : EnumTy, mty = .enum ety ∧ isZstEnumTy ety = true ∧
     vd = .enumVal ety 0 ∧ vo = .bytes []))

def SlotRel (mty : MirTy) (sd so : LocalSlot) : Prop :=
  (sd = .dead ∧ so = .dead) ∨
  (sd = .immediate none ∧ so = .immediate none) ∨
  (∃ vd vo : Val, sd = .immediate (some vd) ∧ so = .immediate (some vo) ∧
    ValRel mty vd vo) ∨
  (sd = liveUninitSlot mty ∧
    (mty = .unit ∨ ∃ ety : EnumTy, mty = .enum ety ∧ isZstEnumTy ety = true) ∧
    so = .immediate none)

def LocalsRel (prog : OpenProgram) (σ : List OpenMirTy) :
    List OpenMirTy → List LocalSlot → List LocalSlot → Prop
  | [], [], [] => True
  | ty :: tys, sd :: sds, so :: sos =>
      SlotRel (erasedTy prog σ ty) sd so ∧ LocalsRel prog σ tys sds sos
  | _, _, _ => False

def StateRel (prog : OpenProgram) (σ : List OpenMirTy)
    (defId : DefId) (ob : OpenBody) (ds : State) (os : OpenState) : Prop :=
  ∃ (df : FrameState) (of_ : OpenFrameState),
    ds.frames = [df] ∧
    os.frames = [of_] ∧
    df.defId = defId ∧
    of_.defId = defId ∧
    df.blockIdx = of_.blockIdx ∧
    df.stmtIdx = of_.stmtIdx ∧
    of_.retDst = none ∧
    ds.callerMem = ⟨[]⟩ ∧
    os.callerMem = ⟨[]⟩ ∧
    ds.mem = entryMemory ∧
    os.mem = MemoryState.empty ∧
    LocalsRel prog σ ob.locals df.locals of_.locals

private theorem openLiveUninitSlot_slotRel (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (σ : List OpenMirTy) (ty : OpenMirTy) :
    SlotRel (erasedTy prog σ ty) (liveUninitSlot (erasedTy prog σ ty))
      (openLiveUninitSlot prog ty) := by
  unfold openLiveUninitSlot erasedTy
  cases hCl : OpenMirTy.toClosedMirTy?
      (normalizeOpenTy prog.traitRegistry normFuel ty) with
  | some m₀ =>
      have hSub : OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ ty =
          normalizeOpenTy prog.traitRegistry normFuel ty := by
        rw [← substAndNormalize_normalize_eq prog.traitRegistry hRegWf σ ty]
        exact toClosedMirTy?_substAndNormalize_eq prog.traitRegistry σ hCl
      rw [hSub]
      dsimp only [eraseOpenTy]
      rw [hCl]
      cases m₀ with
      | unit =>
          exact .inr (.inr (.inl ⟨.unit, .unit, rfl, rfl, ⟨rfl, .inl rfl⟩⟩))
      | enum ety =>
          cases hZ : isZstEnumTy ety with
          | false =>
              dsimp only [liveUninitSlot]
              rw [hZ]
              exact .inr (.inl ⟨rfl, rfl⟩)
          | true =>
              dsimp only [liveUninitSlot]
              rw [hZ]
              have hChk : checkVal (.enumVal ety 0) (.enum ety) = true := by
                unfold isZstEnumTy at hZ
                cases hTag : ety.tagRepr with
                | scalar _ _ => rw [hTag] at hZ; cases hZ
                | zeroSized =>
                    rw [hTag] at hZ
                    have hAdm : enumAdmitted ety = true := by
                      rw [← hZ]
                    have hNE : (!ety.discriminants.isEmpty) = true := by
                      unfold enumAdmitted at hAdm
                      exact bool_and_left (bool_and_left (bool_and_left
                        (bool_and_left hAdm)))
                    dsimp only [checkVal, Val.ty?]
                    rw [hAdm, nat_list_nonempty_zero_lt ety.discriminants hNE]
                    exact enumTy_beq_self ety
              exact .inr (.inr (.inl ⟨.enumVal ety 0, .enumVal ety 0, rfl, rfl,
                ⟨hChk, .inl rfl⟩⟩))
      | bool | int _ _ | never | char | ordering | tuple _ | ref _ _
      | rawPtr _ _ | slice _ | str | rangeTo _ | rangeFrom _ | array _ _
      | unsupported | option _ | range _ | box _ | vec _ =>
          exact .inr (.inl ⟨rfl, rfl⟩)
  | none =>
      cases hM : eraseOpenTy
          (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ ty) with
      | unit =>
          exact .inr (.inr (.inr ⟨rfl, .inl rfl, rfl⟩))
      | enum ety =>
          cases hZ : isZstEnumTy ety with
          | true =>
              refine .inr (.inr (.inr ⟨?_, .inr ⟨ety, rfl, hZ⟩, rfl⟩))
              rfl
          | false =>
              refine .inr (.inl ⟨?_, rfl⟩)
              dsimp only [liveUninitSlot]; rw [ite_cond_false hZ]
      | bool | int _ _ | never | char | ordering | tuple _ | ref _ _
      | rawPtr _ _ | slice _ | str | rangeTo _ | rangeFrom _ | array _ _
      | unsupported | option _ | range _ | box _ | vec _ =>
          exact .inr (.inl ⟨rfl, rfl⟩)

private theorem localsRel_getElem? (prog : OpenProgram) (σ : List OpenMirTy) :
    ∀ {tys : List OpenMirTy} {sds sos : List LocalSlot} (lid : Nat),
      LocalsRel prog σ tys sds sos →
      (openListGet? tys lid = none ∧
       Trusted.MirSemantics.getElem? sds lid = none ∧
       Trusted.MirSemantics.getElem? sos lid = none) ∨
      (∃ (ty : OpenMirTy) (sd so : LocalSlot),
        openListGet? tys lid = some ty ∧
        Trusted.MirSemantics.getElem? sds lid = some sd ∧
        Trusted.MirSemantics.getElem? sos lid = some so ∧
        SlotRel (erasedTy prog σ ty) sd so)
  | [], [], [], _, _ => .inl ⟨rfl, rfl, rfl⟩
  | [], [], _ :: _, _, h => by cases h
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h
  | _ :: _, _ :: _, [], _, h => by cases h
  | ty :: tys, sd :: sds, so :: sos, lid, h => by
      cases lid with
      | zero => exact .inr ⟨ty, sd, so, rfl, rfl, rfl, h.1⟩
      | succ j => exact localsRel_getElem? prog σ j h.2

private theorem localsRel_setElem? (prog : OpenProgram) (σ : List OpenMirTy) :
    ∀ {tys : List OpenMirTy} {sds sos : List LocalSlot} (lid : Nat)
      {ty : OpenMirTy} {sd' so' : LocalSlot},
      LocalsRel prog σ tys sds sos →
      openListGet? tys lid = some ty →
      SlotRel (erasedTy prog σ ty) sd' so' →
      ∃ sds' sos',
        setElem? sds lid sd' = some sds' ∧
        setElem? sos lid so' = some sos' ∧
        LocalsRel prog σ tys sds' sos' := by
  intro tys sds sos lid
  induction lid generalizing tys sds sos with
  | zero =>
      intro ty sd' so' hRel hGet hSlot
      cases tys with
      | nil => cases hGet
      | cons ty0 tys' =>
          cases sds with
          | nil => cases hRel
          | cons sd0 sds' =>
              cases sos with
              | nil => cases hRel
              | cons so0 sos' =>
                  cases hGet
                  exact ⟨sd' :: sds', so' :: sos', rfl, rfl, ⟨hSlot, hRel.2⟩⟩
  | succ j ih =>
      intro ty sd' so' hRel hGet hSlot
      cases tys with
      | nil => cases hGet
      | cons ty0 tys' =>
          cases sds with
          | nil => cases hRel
          | cons sd0 sds' =>
              cases sos with
              | nil => cases hRel
              | cons so0 sos' =>
                  let ⟨sds'', sos'', hs1, hs2, hTail⟩ :=
                    ih hRel.2 hGet hSlot
                  dsimp only [setElem?]
                  rw [hs1, hs2]
                  exact ⟨sd0 :: sds'', so0 :: sos'', rfl, rfl, ⟨hRel.1, hTail⟩⟩

private theorem hasStorageAnnotation_eq_open (prog : OpenProgram)
    (σ : List OpenMirTy) (ob : OpenBody) (erasedOb : Body)
    (hObEq : OpenBody.toDay1? (OpenBody.subst prog.traitRegistry normFuel σ ob) =
      some erasedOb) (idx : Nat) :
    hasStorageAnnotation erasedOb idx = openHasStorageAnnotation ob idx := by
  have hBbs := (erasedOb_locals_eq_map prog σ ob erasedOb hObEq).2.2
  unfold hasStorageAnnotation openHasStorageAnnotation
  rw [hBbs]
  have hAux : ∀ bbs : List OpenBasicBlock,
      ((bbs.map (OpenBasicBlock.subst prog.traitRegistry normFuel σ)).map
        eraseOpenBasicBlock).any
        (fun bb => bb.statements.any (stmtHasStorageMarker idx)) =
      bbs.any (fun bb => bb.statements.any (fun st =>
        match st with
        | .storageLive id | .storageDead id => Nat.beq id idx
        | _ => false)) := by
    intro bbs
    induction bbs with
    | nil => rfl
    | cons b bs ih =>
        dsimp only [List.map, List.any, OpenBasicBlock.subst,
          eraseOpenBasicBlock]
        have hStmts :
            ((b.statements.map
              (OpenStatementKind.subst prog.traitRegistry normFuel σ)).map
                eraseOpenStatementKind).any (stmtHasStorageMarker idx) =
            b.statements.any (fun st =>
              match st with
              | .storageLive id | .storageDead id => Nat.beq id idx
              | _ => false) := by
          induction b.statements with
          | nil => rfl
          | cons s ss ihs =>
              dsimp only [List.map, List.any]
              have hHead : stmtHasStorageMarker idx (eraseOpenStatementKind
                  (OpenStatementKind.subst prog.traitRegistry normFuel σ s)) =
                  match s with
                  | .storageLive id | .storageDead id => Nat.beq id idx
                  | _ => false := by
                cases s <;> rfl
              rw [hHead, ihs]
        rw [hStmts, ih]
  exact hAux ob.basicBlocks

private theorem list_drop_cons_getElem? {α : Type} :
    ∀ (xs : List α) (j : Nat) (v : α) (vs : List α),
      xs.drop j = v :: vs →
      Trusted.MirSemantics.getElem? xs j = some v ∧ xs.drop (j + 1) = vs
  | [], j, v, vs, h => by cases j <;> cases h
  | x :: xs, 0, v, vs, h => by cases h; exact ⟨rfl, rfl⟩
  | _ :: xs, j + 1, v, vs, h => list_drop_cons_getElem? xs j v vs h

private theorem list_drop_nil_length_le {α : Type} :
    ∀ (xs : List α) (j : Nat), xs.drop j = [] → xs.length ≤ j
  | [], _, _ => Nat.zero_le _
  | _ :: xs, 0, h => by cases h
  | _ :: xs, j + 1, h =>
      Nat.succ_le_succ (list_drop_nil_length_le xs j h)

private theorem initLocals_rel_aux (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (σ : List OpenMirTy) (ob : OpenBody) (erasedOb : Body)
    (hObEq : OpenBody.toDay1? (OpenBody.subst prog.traitRegistry normFuel σ ob) =
      some erasedOb)
    (args : List Val) (hLenArgs : args.length = erasedOb.argumentCount) :
    ∀ (j : Nat) (tys : List OpenMirTy) (vs : List Val)
      (osLocs : List LocalSlot),
      vs = args.drop j →
      checkArgsMatch vs ((tys.map (erasedTy prog σ)).take vs.length) = true →
      initOpenLocalsBuild prog ob (j + 1) tys vs = some osLocs →
      LocalsRel prog σ tys
        (initLocalsLoop erasedOb args (j + 1) (tys.map (erasedTy prog σ)))
        osLocs := by
  intro j tys
  induction tys generalizing j with
  | nil =>
      intro vs osLocs _ _ hInit
      cases vs with
      | nil => cases hInit; exact True.intro
      | cons _ _ => cases hInit
  | cons ty restTys ih =>
      intro vs osLocs hDrop hChk hInit
      cases vs with
      | nil =>
          have hLe : erasedOb.argumentCount ≤ j := by
            rw [← hLenArgs]
            exact list_drop_nil_length_le args j hDrop.symm
          have hNotLe : Nat.ble (j + 1) erasedOb.argumentCount = false :=
            nat_ble_false (Nat.lt_succ_of_le hLe)
          dsimp only [initOpenLocalsBuild] at hInit
          cases hRest : initOpenLocalsBuild prog ob (j + 2) restTys [] with
          | none => rw [hRest] at hInit; cases hInit
          | some osRest =>
              rw [hRest] at hInit; cases hInit
              dsimp only [List.map, initLocalsLoop]
              rw [ite_cond_false (nat_beq_succ_zero j), ite_cond_false hNotLe,
                hasStorageAnnotation_eq_open prog σ ob erasedOb hObEq (j + 1)]
              have hDrop' := hDrop.symm
              have hAll : args.drop (j + 1) = [] := by
                have hLen : args.length ≤ j + 1 :=
                  Nat.le_trans (list_drop_nil_length_le args j hDrop')
                    (Nat.le_succ j)
                exact list_drop_of_le args (j + 1) hLen
              have hTail := ih (j + 1) [] osRest hAll.symm rfl hRest
              cases openHasStorageAnnotation ob (j + 1) with
              | true =>
                  rw [ite_cond_true (rfl : (true : Bool) = true)]
                  exact ⟨.inl ⟨rfl, rfl⟩, hTail⟩
              | false =>
                  rw [ite_cond_false (rfl : (false : Bool) = false),
                    ite_cond_false (rfl : (false : Bool) = false)]
                  dsimp only [LocalsRel]
                  constructor
                  · exact openLiveUninitSlot_slotRel prog hRegWf σ ty
                  · exact hTail
      | cons v vs' =>
          have hStep := list_drop_cons_getElem? args j v vs' hDrop.symm
          have hJlt : j < args.length := by
            have hAux : ∀ {xs : List Val} {k : Nat} {w : Val},
                Trusted.MirSemantics.getElem? xs k = some w → k < xs.length := by
              intro xs
              induction xs with
              | nil => intro k w hg; cases hg
              | cons _ _ ihx =>
                  intro k w hg
                  cases k with
                  | zero => exact Nat.succ_pos _
                  | succ m => exact Nat.succ_lt_succ (ihx hg)
            exact hAux hStep.1
          have hBle : Nat.ble (j + 1) erasedOb.argumentCount = true :=
            nat_ble_true (by rw [← hLenArgs]; exact hJlt)
          dsimp only [initOpenLocalsBuild] at hInit
          cases hRest : initOpenLocalsBuild prog ob (j + 2) restTys vs' with
          | none => rw [hRest] at hInit; cases hInit
          | some osRest =>
              rw [hRest] at hInit; cases hInit
              dsimp only [List.map, List.take, checkArgsMatch] at hChk
              have hChkV := bool_and_left hChk
              have hChkVs := bool_and_right hChk
              dsimp only [List.map, initLocalsLoop]
              rw [ite_cond_false (nat_beq_succ_zero j), ite_cond_true hBle]
              rw [show j + 1 - 1 = j from rfl, hStep.1]
              refine ⟨.inr (.inr (.inl ⟨v, v, rfl, rfl, hChkV, .inl rfl⟩)), ?_⟩
              exact ih (j + 1) vs' osRest hStep.2.symm hChkVs hRest

private theorem openLiveUninitSlot_eq_of_traitRegistry (p1 p2 : OpenProgram)
    (hReg : p1.traitRegistry = p2.traitRegistry) (ty : OpenMirTy) :
    openLiveUninitSlot p1 ty = openLiveUninitSlot p2 ty := by
  unfold openLiveUninitSlot
  simp only [hReg]

private theorem openLiveUninitSlot_entryOpenProgForBody (prog : OpenProgram)
    (defId : DefId) (ty : OpenMirTy) :
    openLiveUninitSlot (entryOpenProgForBody prog defId) ty =
      openLiveUninitSlot prog ty :=
  openLiveUninitSlot_eq_of_traitRegistry (entryOpenProgForBody prog defId) prog
    rfl ty

private theorem checkOpenVal_eq_of_traitRegistry (p1 p2 : OpenProgram)
    (hReg : p1.traitRegistry = p2.traitRegistry) (env : OpenExecEnv)
    (v : Val) (ty : OpenMirTy) :
    checkOpenVal p1 env v ty = checkOpenVal p2 env v ty := by
  unfold checkOpenVal; rw [hReg]

private theorem checkOpenArgsMatch_eq_of_traitRegistry (p1 p2 : OpenProgram)
    (hReg : p1.traitRegistry = p2.traitRegistry) (env : OpenExecEnv) :
    ∀ vs tys, checkOpenArgsMatch p1 env vs tys = checkOpenArgsMatch p2 env vs tys
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | _ :: _, _ :: _ => by
      dsimp only [checkOpenArgsMatch]
      rw [checkOpenVal_eq_of_traitRegistry p1 p2 hReg,
        checkOpenArgsMatch_eq_of_traitRegistry p1 p2 hReg]

private theorem initOpenLocalsBuild_eq_of_traitRegistry (p1 p2 : OpenProgram)
    (hReg : p1.traitRegistry = p2.traitRegistry) (ob : OpenBody) :
    ∀ (idx : Nat) (tys : List OpenMirTy) (vs : List Val),
      initOpenLocalsBuild p1 ob idx tys vs =
        initOpenLocalsBuild p2 ob idx tys vs
  | _, [], [] => rfl
  | _, [], _ :: _ => rfl
  | 0, ty :: restTys, vs => by
      dsimp only [initOpenLocalsBuild]
      rw [openLiveUninitSlot_eq_of_traitRegistry p1 p2 hReg,
        initOpenLocalsBuild_eq_of_traitRegistry p1 p2 hReg ob 1 restTys vs]
  | idx + 1, _ :: restTys, _ :: vs => by
      dsimp only [initOpenLocalsBuild]
      rw [initOpenLocalsBuild_eq_of_traitRegistry p1 p2 hReg ob (idx + 2)
        restTys vs]
  | idx + 1, ty :: restTys, [] => by
      dsimp only [initOpenLocalsBuild]
      rw [openLiveUninitSlot_eq_of_traitRegistry p1 p2 hReg,
        initOpenLocalsBuild_eq_of_traitRegistry p1 p2 hReg ob (idx + 2)
        restTys []]

private theorem init_sim (prog : OpenProgram) (env' : OpenExecEnv)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (σ : List OpenMirTy) (defId : DefId) (ob : OpenBody) (erasedOb : Body)
    (hGetOpen : openListGet? prog.bodies defId = some ob)
    (hGetErased : Trusted.MirSemantics.getElem?
      (eraseOpenProgram σ prog).bodies defId = some erasedOb)
    (_hErasedDef : erasedOb = eraseOpenBody prog.traitRegistry σ ob)
    (hObEq : OpenBody.toDay1? (OpenBody.subst prog.traitRegistry normFuel σ ob) =
      some erasedOb)
    (hDay1Adm : BodyStaticAdmitted (eraseOpenProgram σ prog) erasedOb = true)
    (hNone : OpenProgram.toDay1? (entryOpenProgForBody prog defId) = none)
    (args : List Val) (hValid : ValidEntryArgs erasedOb args)
    (os₀ : OpenState)
    (hOInit : openInitState (entryOpenProgForBody prog defId) env'
      { args := args } = .ok os₀) :
    ∃ ds₀ : State,
      initState (entryProgForBody (eraseOpenProgram σ prog) defId)
        { args := args } = .ok ds₀ ∧
      StateRel prog σ defId ob ds₀ os₀ := by
  have hParts := erasedOb_locals_eq_map prog σ ob erasedOb hObEq
  unfold BodyStaticAdmitted singleBodyStaticAdmitted at hDay1Adm
  have hAllCall := bool_and_right hDay1Adm
  have h0 := bool_and_left hDay1Adm
  have hCallsAdm := bool_and_right h0
  have hS0 := bool_and_left h0
  have hSupp := bool_and_right hS0
  have hA0 := bool_and_left hS0
  have hAct := bool_and_right hA0
  have h1 := bool_and_left hA0
  have hCast := bool_and_right h1
  have h2 := bool_and_left h1
  have hDiscr := bool_and_right h2
  have h3 := bool_and_left h2
  have hSto := bool_and_right h3
  have h4 := bool_and_left h3
  have hArgLt := bool_and_right h4
  have h5 := bool_and_left h4
  have hBbsNE := bool_and_right h5
  have h6 := bool_and_left h5
  have hIdNE := bool_and_right h6
  have h7 := bool_and_left h6
  have hVer := bool_and_right h7
  have hPtr := bool_and_left h7
  have hErasedP : Trusted.MirSemantics.getElem?
      (entryProgForBody (eraseOpenProgram σ prog) defId).bodies defId =
      some erasedOb := hGetErased
  have hP64 : (entryProgForBody (eraseOpenProgram σ prog) defId).pointerWidthBits =
      (eraseOpenProgram σ prog).pointerWidthBits := rfl
  have hPV1 : (entryProgForBody (eraseOpenProgram σ prog) defId).mirProfileVersion =
      (eraseOpenProgram σ prog).mirProfileVersion := rfl
  have hChkArgs : checkArgsMatch args
      ((erasedOb.locals.drop 1).take erasedOb.argumentCount) = true := hValid
  have hInitDs :
      initState (entryProgForBody (eraseOpenProgram σ prog) defId)
        { args := args } =
      .ok
        { frames :=
            [{ defId := defId
             , blockIdx := 0
             , stmtIdx := 0
             , locals := initLocalsLoop erasedOb args 0 erasedOb.locals }]
        , callerMem := ⟨[]⟩
        , mem := entryMemory } := by
    let dp := entryProgForBody (eraseOpenProgram σ prog) defId
    have hHdrD : (!Nat.beq dp.pointerWidthBits 64 ||
        !Nat.beq dp.mirProfileVersion 1) = false := by
      dsimp only [dp]
      rw [hP64, hPV1, bang_true_eq_false hPtr, bang_true_eq_false hVer]
      rfl
    have hCmD : (!({ args := args } : Query).callerMem.allocations.isEmpty) =
        false := rfl
    have hE : erasedOb.basicBlocks.isEmpty = false := not_bool_eq_true hBbsNE
    have hEntryD :
        (entryProgForBody (eraseOpenProgram σ prog) defId).entryDefId =
          defId := rfl
    have hCallsAdmE : callsAdmitted
        (entryProgForBody (eraseOpenProgram σ prog) defId) erasedOb = true :=
      hCallsAdm
    have hAllCallE : allCallBodiesStaticAdmitted
        (entryProgForBody (eraseOpenProgram σ prog) defId) erasedOb = true :=
      hAllCall
    unfold initState
    rw [ite_cond_false hHdrD, ite_cond_false hCmD, hEntryD, hErasedP]
    dsimp only
    rw [ite_cond_false hE, ite_not_true hArgLt, ite_not_true hSto,
      ite_not_true hDiscr, ite_not_true hCast, ite_not_true hAct,
      ite_not_true hSupp, ite_not_true hCallsAdmE, ite_not_true hAllCallE,
      ite_not_true hChkArgs]
  unfold openInitState openInitStateAux at hOInit
  rw [hNone] at hOInit
  dsimp only at hOInit
  have hCmO : (!({ args := args } : Query).callerMem.allocations.isEmpty) =
      false := rfl
  rw [ite_cond_false hCmO] at hOInit
  have hGetEP : openListGet? (entryOpenProgForBody prog defId).bodies
      (entryOpenProgForBody prog defId).entryDefId = some ob := hGetOpen
  rw [hGetEP] at hOInit
  dsimp only at hOInit
  cases hHdr : (!Nat.beq (entryOpenProgForBody prog defId).pointerWidthBits 64 ||
      !Nat.beq (entryOpenProgForBody prog defId).mirProfileVersion 1 ||
      ob.basicBlocks.isEmpty ||
      !Nat.blt ob.argumentCount ob.locals.length) with
  | true => rw [ite_cond_true hHdr] at hOInit; cases hOInit
  | false =>
      rw [ite_cond_false hHdr] at hOInit
      cases hLocInit : initOpenLocals (entryOpenProgForBody prog defId) env'
          ob args with
      | none => rw [hLocInit] at hOInit; cases hOInit
      | some osLocs =>
          rw [hLocInit] at hOInit
          cases hOInit
          dsimp only [initOpenLocals] at hLocInit
          rw [checkOpenArgsMatch_eq_of_traitRegistry
              (entryOpenProgForBody prog defId) prog rfl,
            initOpenLocalsBuild_eq_of_traitRegistry
              (entryOpenProgForBody prog defId) prog rfl] at hLocInit
          cases hGuards : (!Nat.beq args.length ob.argumentCount ||
              !Nat.beq ((ob.locals.drop 1).take ob.argumentCount).length
                ob.argumentCount ||
              !Nat.blt ob.argumentCount ob.locals.length ||
              !checkOpenArgsMatch prog env' args
                ((ob.locals.drop 1).take ob.argumentCount)) with
          | true => rw [ite_cond_true hGuards] at hLocInit; cases hLocInit
          | false =>
              rw [ite_cond_false hGuards] at hLocInit
              have hLenArgs : args.length = erasedOb.argumentCount := by
                have hg1 := bool_or_eq_false_left
                  (bool_or_eq_false_left (bool_or_eq_false_left hGuards))
                rw [hParts.2.1]
                exact nat_beq_eq (not_bool_eq_false hg1)
              cases hObs : ob.locals with
              | nil =>
                  rw [hParts.1, hParts.2.1, hObs] at hArgLt
                  cases hArgLt
              | cons ty0 restTys =>
                  rw [hObs] at hLocInit
                  dsimp only [initOpenLocalsBuild] at hLocInit
                  cases hRestOs : initOpenLocalsBuild prog ob 1 restTys args with
                  | none => rw [hRestOs] at hLocInit; cases hLocInit
                  | some restOs =>
                      rw [hRestOs] at hLocInit; cases hLocInit
                      have hDropTake :
                          ((erasedOb.locals.drop 1).take erasedOb.argumentCount)
                            =
                          (restTys.map (erasedTy prog σ)).take args.length := by
                        rw [hParts.1, map_substAndNormalize_eq_erasedTy, hObs,
                          hLenArgs]
                        rfl
                      rw [hDropTake] at hChkArgs
                      have hTailRel := initLocals_rel_aux prog hRegWf σ ob
                        erasedOb hObEq args hLenArgs 0 restTys args restOs
                        rfl hChkArgs hRestOs
                      have hZeroRel := openLiveUninitSlot_slotRel prog hRegWf σ
                        ty0
                      have hLocalsEq :
                          initLocalsLoop erasedOb args 0 erasedOb.locals =
                            liveUninitSlot (erasedTy prog σ ty0) ::
                              initLocalsLoop erasedOb args 1
                                (restTys.map (erasedTy prog σ)) := by
                        rw [hParts.1, map_substAndNormalize_eq_erasedTy, hObs]
                        dsimp only [List.map, initLocalsLoop]
                        rw [ite_cond_true (rfl : Nat.beq 0 0 = true)]
                      refine ⟨_, hInitDs, ?_⟩
                      refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                        rfl, rfl, ?_⟩
                      rw [hLocalsEq, hObs]
                      exact ⟨hZeroRel, hTailRel⟩

private theorem valRel_prim_eq {mty : MirTy} {vd vo : Val}
    (hP : isPrimitiveReadableTy mty = true) (hR : ValRel mty vd vo) :
    vd = vo := by
  cases hR.2 with
  | inl hEq => exact hEq
  | inr hRest =>
      cases hRest with
      | inl hU =>
          let ⟨hU1, _, _⟩ := hU
          subst hU1; cases hP
      | inr hE => let ⟨_, hEq, _, _, _⟩ := hE; subst hEq; cases hP

private theorem isIntLikeTy_to_prim {mty : MirTy}
    (hI : isIntLikeTy mty = true) : isPrimitiveReadableTy mty = true := by
  cases mty <;> cases hI <;> rfl

private theorem valRel_zeroSized_const (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env : OpenExecEnv) (σ : List OpenMirTy) (paramSpecs : List TypeLayoutSpec)
    (hLenEq : paramSpecs.length = σ.length)
    (hMap : ∀ (i : Nat) (ty : OpenMirTy), openListGet? σ i = some ty →
      ∃ sp : TypeLayoutSpec, openListGet? paramSpecs i = some sp ∧
        evalOpenTySpec prog.traitRegistry normFuel
          { env.typeSpecs with paramSpecs := [], paramInvs := [] } ty =
          some sp ∧
        OpenMirTy.isClosed ty = true)
    (dstTy : OpenMirTy) (dstMty : MirTy) (sp : TypeLayoutSpec)
    (hCl : OpenMirTy.toClosedMirTy?
      (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ dstTy) =
      some dstMty)
    (hSupp : isSupportedScalarOrUnitTy dstMty = true)
    (hEval : evalOpenTySpec prog.traitRegistry normFuel
      (substTypeSpecEnv env.typeSpecs paramSpecs
        (List.replicate paramSpecs.length (fun _ => True))
        (instAssocSpecs prog.traitRegistry env.typeSpecs σ)) dstTy = some sp)
    (hInhab : sp.inhabited = true)
    (hSz : ((sp.sizeForMeta .none).getD 1) = 0) :
    ∃ vd : Val,
      evalConstLit dstMty .zeroSized = .ok vd ∧
      ValRel dstMty vd (.bytes []) := by
  let paramInvs := List.replicate paramSpecs.length (fun _ : List AllocByte => True)
  let baseClosed : TypeSpecEnv :=
    { env.typeSpecs with paramSpecs := [], paramInvs := [] }
  have hSubEval :
      evalOpenTySpec prog.traitRegistry normFuel baseClosed
        (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ dstTy) =
        some sp :=
    evalOpenTySpec_subst_param_some prog hRegWf env σ paramSpecs paramInvs
      hLenEq hMap dstTy sp hEval
  have hSubClosed : OpenMirTy.isClosed
      (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ dstTy) = true :=
    toClosedMirTy?_isClosed hCl
  have hNormEval :
      evalNormOpenTySpec baseClosed
        (OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ dstTy) =
        some sp := by
    unfold evalOpenTySpec at hSubEval
    rw [normalizeOpenTy_isClosed prog.traitRegistry
      normFuel _ hSubClosed] at hSubEval
    exact hSubEval
  cases hSub : OpenMirTy.substAndNormalize prog.traitRegistry normFuel σ dstTy
      with
  | unit =>
      rw [hSub] at hCl
      cases hCl
      exact ⟨.unit, rfl, ⟨rfl, .inr (.inl ⟨rfl, rfl, rfl⟩)⟩⟩
  | enum ety =>
      rw [hSub] at hCl hNormEval
      cases hCl
      dsimp only [evalNormOpenTySpec] at hNormEval
      unfold enumTypeLayoutSpec at hNormEval
      cases hAdm : enumAdmitted ety with
      | false => rw [hAdm] at hNormEval; cases hNormEval
      | true =>
          rw [hAdm] at hNormEval
          cases hTag : ety.tagRepr with
          | zeroSized =>
              rw [hTag] at hNormEval
              cases hNormEval
              have hZst : isZstEnumTy ety = true := by
                unfold isZstEnumTy; rw [hTag]; exact hAdm
              have hNE : (!ety.discriminants.isEmpty) = true := by
                unfold enumAdmitted at hAdm
                exact bool_and_left (bool_and_left (bool_and_left
                  (bool_and_left hAdm)))
              have hChk : checkVal (.enumVal ety 0) (.enum ety) = true := by
                dsimp only [checkVal, Val.ty?]
                rw [hAdm, nat_list_nonempty_zero_lt ety.discriminants hNE]
                exact enumTy_beq_self ety
              refine ⟨.enumVal ety 0, ?_,
                ⟨hChk, .inr (.inr ⟨ety, rfl, hZst, rfl, rfl⟩)⟩⟩
              dsimp only [evalConstLit]
              rw [ite_cond_true hZst]
          | scalar tagW tagS =>
              rw [hTag] at hNormEval
              cases hNormEval
              cases tagW <;> cases hSz
  | bool =>
      rw [hSub] at hNormEval; cases hNormEval; cases hSz
  | int w _ =>
      rw [hSub] at hNormEval; cases hNormEval
      cases w <;> cases hSz
  | char =>
      rw [hSub] at hNormEval; cases hNormEval; cases hSz
  | ordering =>
      rw [hSub] at hNormEval; cases hNormEval; cases hSz
  | never =>
      rw [hSub] at hNormEval; cases hNormEval
      cases hInhab
  | slice _ | array _ _ | adt _ _ | param _ | assocProj _ _ _ _
  | unsupported =>
      rw [hSub] at hCl; cases hCl
  | ref _ p =>
      rw [hSub] at hCl
      dsimp only [OpenMirTy.toClosedMirTy?] at hCl
      cases hp : OpenMirTy.toClosedMirTy? p with
      | none => rw [hp] at hCl; cases hCl
      | some _ => rw [hp] at hCl; cases hCl; cases hSupp
  | rawPtr _ p =>
      rw [hSub] at hCl
      dsimp only [OpenMirTy.toClosedMirTy?] at hCl
      cases hp : OpenMirTy.toClosedMirTy? p with
      | none => rw [hp] at hCl; cases hCl
      | some _ => rw [hp] at hCl; cases hCl; cases hSupp
  | tuple fs =>
      rw [hSub] at hCl
      dsimp only [OpenMirTy.toClosedMirTy?] at hCl
      cases hFs : OpenMirTy.toClosedMirTyList? fs with
      | none => rw [hFs] at hCl; cases hCl
      | some cs =>
          rw [hFs] at hCl; cases hCl
          cases fs with
          | nil => cases hFs; cases hSupp
          | cons a rest =>
              cases rest with
              | nil =>
                  dsimp only [OpenMirTy.toClosedMirTyList?] at hFs
                  cases ha : OpenMirTy.toClosedMirTy? a with
                  | none => rw [ha] at hFs; cases hFs
                  | some _ =>
                      rw [ha] at hFs; cases hFs
                      simp only [isSupportedScalarOrUnitTy,
                        isOverflowPairTy] at hSupp
                      cases hSupp
              | cons b tl =>
                  cases tl with
                  | cons c ds =>
                      dsimp only [OpenMirTy.toClosedMirTyList?] at hFs
                      cases ha : OpenMirTy.toClosedMirTy? a with
                      | none => rw [ha] at hFs; cases hFs
                      | some _ =>
                          rw [ha] at hFs
                          cases hb : OpenMirTy.toClosedMirTy? b with
                          | none => rw [hb] at hFs; cases hFs
                          | some _ =>
                              rw [hb] at hFs
                              cases hc : OpenMirTy.toClosedMirTy? c with
                              | none => rw [hc] at hFs; cases hFs
                              | some _ =>
                                  rw [hc] at hFs
                                  cases hds : OpenMirTy.toClosedMirTyList? ds
                                      with
                                  | none => rw [hds] at hFs; cases hFs
                                  | some _ =>
                                      rw [hds] at hFs; cases hFs
                                      simp only [isSupportedScalarOrUnitTy,
                                        isOverflowPairTy] at hSupp
                                      cases hSupp
                  | nil =>
                      dsimp only [OpenMirTy.toClosedMirTyList?] at hFs
                      cases ha : OpenMirTy.toClosedMirTy? a with
                      | none => rw [ha] at hFs; cases hFs
                      | some ca =>
                          rw [ha] at hFs
                          cases hb : OpenMirTy.toClosedMirTy? b with
                          | none => rw [hb] at hFs; cases hFs
                          | some cb =>
                              rw [hb] at hFs; cases hFs
                              have hPair : ∃ w s, ca = .int w s ∧ cb = .bool := by
                                cases ca <;> cases cb <;>
                                  first
                                  | exact ⟨_, _, rfl, rfl⟩
                                  | (unfold isSupportedScalarOrUnitTy
                                        isOverflowPairTy at hSupp;
                                      cases hSupp)
                              let ⟨w, s, hCa, hCb⟩ := hPair
                              subst hCa; subst hCb
                              have haEq := toClosedMirTy?_eq_int ha
                              have hbEq := toClosedMirTy?_eq_bool hb
                              subst haEq; subst hbEq
                              rw [hSub] at hNormEval
                              cases hNormEval
                              cases w <;> cases hSz

private theorem list_isEmpty_eq_nil {α : Type} :
    ∀ {xs : List α}, xs.isEmpty = true → xs = []
  | [], _ => rfl
  | _ :: _, h => by cases h

private theorem evalOpenOperand_sim (prog : OpenProgram) (env : OpenExecEnv)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (σ : List OpenMirTy) (ob : OpenBody) (dfLocs : List LocalSlot)
    (of_ : OpenFrameState) (tyOk : MirTy → Bool)
    (hRel : LocalsRel prog σ ob.locals dfLocs of_.locals)
    (op : OpenOperand) (vo : Val) (srcTy : OpenMirTy) (of₁ : OpenFrameState)
    (hEval : evalOpenOperand prog env ob of_ op = .ok (vo, srcTy, of₁)) :
    of₁.defId = of_.defId ∧
    of₁.blockIdx = of_.blockIdx ∧
    of₁.stmtIdx = of_.stmtIdx ∧
    of₁.retDst = of_.retDst ∧
    match op with
    | .copy p | .move p =>
        p.projection = [] ∧
        openListGet? ob.locals p.localId = some srcTy ∧
        ∃ (vd : Val) (dfLocs' : List LocalSlot),
          evalOperandToSlot (ob.locals.map (erasedTy prog σ)) dfLocs entryMemory
            tyOk (eraseOpenOperand (OpenOperand.subst prog.traitRegistry normFuel σ op)) =
            .ok (erasedTy prog σ srcTy, some vd, dfLocs', entryMemory) ∧
          ValRel (erasedTy prog σ srcTy) vd vo ∧
          LocalsRel prog σ ob.locals dfLocs' of₁.locals
    | .constant c =>
        srcTy = c.ty ∧
        of₁ = of_ ∧
        ((∃ mc : MirTy,
            OpenMirTy.toClosedMirTy? c.ty = some mc ∧
            erasedTy prog σ c.ty = mc ∧
            evalConstLit mc c.lit = .ok vo ∧
            evalOperandToSlot (ob.locals.map (erasedTy prog σ)) dfLocs
              entryMemory tyOk
              (eraseOpenOperand
                (OpenOperand.subst prog.traitRegistry normFuel σ op)) =
              .ok (mc, some vo, dfLocs, entryMemory) ∧
            ValRel mc vo vo) ∨
         (OpenMirTy.toClosedMirTy? c.ty = none ∧
          c.lit = .zeroSized ∧
          vo = .bytes [] ∧
          ∃ sp : TypeLayoutSpec,
            evalOpenTySpec prog.traitRegistry normFuel env.typeSpecs c.ty =
              some sp ∧
            sp.inhabited = true ∧
            ((sp.sizeForMeta .none).getD 1) = 0)) := by
  cases op with
  | copy p =>
      dsimp only [evalOpenOperand] at hEval
      cases hL : openListGet? ob.locals p.localId with
      | none => rw [hL] at hEval; cases hEval
      | some ty =>
          rw [hL] at hEval
          cases hF : Trusted.MirSemantics.getElem? of_.locals p.localId with
          | none => rw [hF] at hEval; cases hEval
          | some so =>
              rw [hF] at hEval
              cases so with
              | dead | partialTuple _ | indirect _ => cases hEval
              | immediate optVal =>
                  cases hEmp : p.projection.isEmpty with
                  | false => simp only [hEmp] at hEval; cases hEval
                  | true =>
                      simp only [hEmp] at hEval
                      cases optVal with
                      | none => cases hEval
                      | some vo' =>
                          cases hEval
                          have hProjNil : p.projection = [] :=
                            list_isEmpty_eq_nil hEmp
                          cases localsRel_getElem? prog σ p.localId hRel with
                          | inl hNone =>
                              let ⟨hN1, _, _⟩ := hNone
                              rw [hL] at hN1; cases hN1
                          | inr hSome =>
                              let ⟨ty', sd, so', hG1, hG2, hG3, hSlot⟩ := hSome
                              have hTyEq : ty' = srcTy :=
                                Option.some.inj (hG1.symm.trans hL)
                              subst hTyEq
                              rw [hF] at hG3; cases hG3
                              cases hSlot with
                              | inl hC => cases hC.2
                              | inr hS1 =>
                                  cases hS1 with
                                  | inl hC => cases hC.2
                                  | inr hS2 =>
                                      cases hS2 with
                                      | inr hC => cases hC.2.2
                                      | inl hImm =>
                                          let ⟨vd, vo'', hSd, hSo, hVRel⟩ := hImm
                                          cases hSo
                                          refine ⟨rfl, rfl, rfl, rfl, hProjNil, hL,
                                            vd, dfLocs, ?_, hVRel, hRel⟩
                                          dsimp only [OpenOperand.subst,
                                            eraseOpenOperand, OpenPlace.subst,
                                            eraseOpenPlace, List.map,
                                            evalOperandToSlot]
                                          rw [hProjNil]
                                          dsimp only [List.map, List.isEmpty]
                                          rw [mirGetElem?_map,
                                            getElem?_eq_openListGet?, hL]
                                          dsimp only [Option.map]
                                          rw [hG2, hSd]
                                          dsimp only
                                          rw [ite_cond_false
                                            (rfl : (!true) = false)]
  | move p =>
      dsimp only [evalOpenOperand] at hEval
      cases hL : openListGet? ob.locals p.localId with
      | none => rw [hL] at hEval; cases hEval
      | some ty =>
          rw [hL] at hEval
          cases hF : Trusted.MirSemantics.getElem? of_.locals p.localId with
          | none => rw [hF] at hEval; cases hEval
          | some so =>
              rw [hF] at hEval
              cases so with
              | dead | partialTuple _ | indirect _ => cases hEval
              | immediate optVal =>
                  cases hEmp : p.projection.isEmpty with
                  | false => simp only [hEmp] at hEval; cases hEval
                  | true =>
                      simp only [hEmp] at hEval
                      cases optVal with
                      | none => cases hEval
                      | some vo' =>
                          cases hSetO : setElem? of_.locals p.localId
                              (openLiveUninitSlot prog ty) with
                          | none => rw [hSetO] at hEval; cases hEval
                          | some ls' =>
                              rw [hSetO] at hEval
                              cases hEval
                              have hProjNil : p.projection = [] :=
                                list_isEmpty_eq_nil hEmp
                              cases localsRel_getElem? prog σ p.localId hRel with
                              | inl hNone =>
                                  let ⟨hN1, _, _⟩ := hNone
                                  rw [hL] at hN1; cases hN1
                              | inr hSome =>
                                  let ⟨ty', sd, so', hG1, hG2, hG3, hSlot⟩ := hSome
                                  have hTyEq : ty' = srcTy :=
                                    Option.some.inj (hG1.symm.trans hL)
                                  subst hTyEq
                                  rw [hF] at hG3; cases hG3
                                  cases hSlot with
                                  | inl hC => cases hC.2
                                  | inr hS1 =>
                                      cases hS1 with
                                      | inl hC => cases hC.2
                                      | inr hS2 =>
                                          cases hS2 with
                                          | inr hC => cases hC.2.2
                                          | inl hImm =>
                                              let ⟨vd, vo'', hSd, hSo, hVRel⟩ :=
                                                hImm
                                              cases hSo
                                              let ⟨dfLocs', ofLocs', hSetD,
                                                hSetO', hRel'⟩ :=
                                                localsRel_setElem? prog σ p.localId
                                                  hRel hL
                                                  (openLiveUninitSlot_slotRel
                                                    prog hRegWf σ ty')
                                              rw [hSetO] at hSetO'; cases hSetO'
                                              refine ⟨rfl, rfl, rfl, rfl, hProjNil,
                                                hL, vd, dfLocs', ?_, hVRel, hRel'⟩
                                              dsimp only [OpenOperand.subst,
                                                eraseOpenOperand, OpenPlace.subst,
                                                eraseOpenPlace, List.map,
                                                evalOperandToSlot]
                                              rw [hProjNil]
                                              dsimp only [List.map, List.isEmpty]
                                              rw [mirGetElem?_map,
                                                getElem?_eq_openListGet?, hL]
                                              dsimp only [Option.map]
                                              rw [hG2, hSd]
                                              dsimp only
                                              rw [ite_cond_false
                                                (rfl : (!true) = false)]
                                              rw [hSetD]
  | constant c =>
      dsimp only [evalOpenOperand] at hEval
      cases hCl : OpenMirTy.toClosedMirTy? c.ty with
      | some mc =>
          rw [hCl] at hEval
          dsimp only at hEval
          cases hLit : evalConstLit mc c.lit with
          | error k => rw [hLit] at hEval; cases hEval
          | ok v =>
              rw [hLit] at hEval; cases hEval
              have hEr : erasedTy prog σ c.ty = mc :=
                toClosedMirTy?_erase_subst prog.traitRegistry σ hCl
              have hChk := evalConstLit_checkVal mc c.lit vo hLit
              refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, .inl ⟨mc, hCl, hEr, hLit,
                ?_, hChk, .inl rfl⟩⟩
              dsimp only [OpenOperand.subst, eraseOpenOperand, evalOperandToSlot]
              rw [erasedTy_def, hEr, hLit]
      | none =>
          rw [hCl] at hEval
          cases hLit : c.lit with
          | scalar _ | rodataBytes _ | rodataRef _ _ _ _ =>
              rw [hLit] at hEval; cases hEval
          | zeroSized =>
              rw [hLit] at hEval
              cases hEv : evalOpenTySpec prog.traitRegistry normFuel
                  env.typeSpecs c.ty with
              | none => rw [hEv] at hEval; cases hEval
              | some sp =>
                  rw [hEv] at hEval
                  dsimp only at hEval
                  have hF : ∀ a : Bool, (a && false) = false := fun a => by
                    cases a <;> rfl
                  have hT : ∀ a : Bool, (a && true) = a := fun a => by
                    cases a <;> rfl
                  cases hRoles : sp.rolesForMeta .none with
                  | none =>
                      rw [hRoles] at hEval; dsimp only at hEval
                      rw [hF] at hEval
                      rw [ite_cond_false (rfl : (false : Bool) = false)] at hEval
                      cases hEval
                  | some rs =>
                      cases rs with
                      | cons _ _ =>
                          rw [hRoles] at hEval; dsimp only at hEval
                          rw [hF] at hEval
                          rw [ite_cond_false (rfl : (false : Bool) = false)]
                            at hEval
                          cases hEval
                      | nil =>
                          rw [hRoles] at hEval; dsimp only at hEval
                          rw [hT] at hEval
                          cases hSz : sp.isSized with
                          | false =>
                              rw [hSz] at hEval
                              rw [show (false && sp.inhabited &&
                                  Nat.beq ((sp.sizeForMeta .none).getD 1) 0) =
                                  false from rfl] at hEval
                              rw [ite_cond_false (rfl : (false : Bool) = false)]
                                at hEval
                              cases hEval
                          | true =>
                              rw [hSz] at hEval
                              cases hIn : sp.inhabited with
                              | false =>
                                  rw [hIn] at hEval
                                  rw [show (true && false &&
                                      Nat.beq ((sp.sizeForMeta .none).getD 1)
                                        0) = false from rfl] at hEval
                                  rw [ite_cond_false
                                    (rfl : (false : Bool) = false)] at hEval
                                  cases hEval
                              | true =>
                                  rw [hIn] at hEval
                                  cases hZ : Nat.beq
                                      ((sp.sizeForMeta .none).getD 1) 0 with
                                  | false =>
                                      rw [hZ] at hEval
                                      rw [show (true && true && false) = false
                                        from rfl] at hEval
                                      rw [ite_cond_false
                                        (rfl : (false : Bool) = false)] at hEval
                                      cases hEval
                                  | true =>
                                      rw [hZ] at hEval
                                      rw [show (true && true && true) = true
                                        from rfl] at hEval
                                      rw [ite_cond_true
                                        (rfl : (true : Bool) = true)] at hEval
                                      cases hEval
                                      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl,
                                        .inr ⟨hCl, hLit, rfl, sp, hEv, hIn,
                                          nat_beq_eq hZ⟩⟩

private theorem evalOpenOperand_prim_sim (prog : OpenProgram)
    (env : OpenExecEnv) (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (σ : List OpenMirTy) (ob : OpenBody) (dfLocs : List LocalSlot)
    (of_ : OpenFrameState) (hRel : LocalsRel prog σ ob.locals dfLocs of_.locals)
    (op : OpenOperand) (vo : Val) (srcTy : OpenMirTy) (of₁ : OpenFrameState)
    (mty : MirTy) (tyOk : MirTy → Bool)
    (hEval : evalOpenOperand prog env ob of_ op = .ok (vo, srcTy, of₁))
    (hCl : OpenMirTy.toClosedMirTy? srcTy = some mty)
    (hPrim : isPrimitiveReadableTy mty = true) :
    of₁.defId = of_.defId ∧
    of₁.blockIdx = of_.blockIdx ∧
    of₁.stmtIdx = of_.stmtIdx ∧
    of₁.retDst = of_.retDst ∧
    ∃ dfLocs' : List LocalSlot,
      evalOperandToSlot (ob.locals.map (erasedTy prog σ)) dfLocs entryMemory
        tyOk (eraseOpenOperand (OpenOperand.subst prog.traitRegistry normFuel σ op)) =
        .ok (mty, some vo, dfLocs', entryMemory) ∧
      LocalsRel prog σ ob.locals dfLocs' of₁.locals := by
  have hSim := evalOpenOperand_sim prog env hRegWf σ ob dfLocs of_ tyOk hRel
    op vo srcTy of₁ hEval
  cases op with
  | copy p | move p =>
      let ⟨_, _, vd, dfLocs', hSlot, hVRel, hRel'⟩ := hSim.2.2.2.2
      have hEr : erasedTy prog σ srcTy = mty :=
        toClosedMirTy?_erase_subst prog.traitRegistry σ hCl
      rw [hEr] at hSlot hVRel
      have hEq := valRel_prim_eq hPrim hVRel
      subst hEq
      exact ⟨hSim.1, hSim.2.1, hSim.2.2.1, hSim.2.2.2.1, dfLocs', hSlot, hRel'⟩
  | constant c =>
      let ⟨hSrc, hOf1, hBranch⟩ := hSim.2.2.2.2
      subst hSrc; subst hOf1
      cases hBranch with
      | inl hBr =>
          let ⟨mc, hCl', hEr, _, hSlot, _⟩ := hBr
          rw [hCl] at hCl'; cases hCl'
          exact ⟨hSim.1, hSim.2.1, hSim.2.2.1, hSim.2.2.2.1, dfLocs, hSlot, hRel⟩
      | inr hBr =>
          let ⟨hBr1, _⟩ := hBr
          rw [hCl] at hBr1; cases hBr1

private theorem writePlace_sim (prog : OpenProgram) (env : OpenExecEnv)
    (σ : List OpenMirTy) (ob : OpenBody) (dfLocs : List LocalSlot)
    (of_ : OpenFrameState) (dst : OpenPlace) (dstTy : OpenMirTy)
    (vd vo : Val) (of' : OpenFrameState)
    (hRel : LocalsRel prog σ ob.locals dfLocs of_.locals)
    (hL : openListGet? ob.locals dst.localId = some dstTy)
    (hW : writeOpenPlace prog env ob of_ dst vo = .ok of')
    (hVRel : ValRel (erasedTy prog σ dstTy) vd vo) :
    of'.defId = of_.defId ∧
    of'.blockIdx = of_.blockIdx ∧
    of'.stmtIdx = of_.stmtIdx ∧
    of'.retDst = of_.retDst ∧
    ∃ dfLocs' : List LocalSlot,
      writePlace dfLocs entryMemory dst.localId (erasedTy prog σ dstTy) vd =
        .ok (dfLocs', entryMemory) ∧
      LocalsRel prog σ ob.locals dfLocs' of'.locals := by
  unfold writeOpenPlace at hW
  cases hEmp : dst.projection.isEmpty with
  | false => simp only [hEmp] at hW; cases hW
  | true =>
      simp only [hEmp] at hW
      rw [hL] at hW
      cases hChkO : checkOpenVal prog env vo dstTy with
      | false => simp only [hChkO] at hW; cases hW
      | true =>
          simp only [hChkO] at hW
          cases hF : Trusted.MirSemantics.getElem? of_.locals dst.localId with
          | none => rw [hF] at hW; cases hW
          | some so =>
              rw [hF] at hW
              cases so with
              | dead | partialTuple _ | indirect _ => cases hW
              | immediate _ =>
                  cases hSetO : setElem? of_.locals dst.localId
                      (.immediate (some vo)) with
                  | none => rw [hSetO] at hW; cases hW
                  | some ls' =>
                      rw [hSetO] at hW; cases hW
                      cases localsRel_getElem? prog σ dst.localId hRel with
                      | inl hNone =>
                          let ⟨hN1, _, _⟩ := hNone
                          rw [hL] at hN1; cases hN1
                      | inr hSome =>
                          let ⟨ty', sd, so', hG1, hG2, hG3, hSlot⟩ := hSome
                          rw [hL] at hG1; cases hG1
                          rw [hF] at hG3; cases hG3
                          have hNotDead : ∃ optD, sd = .immediate optD := by
                            cases hSlot with
                            | inl hC => cases hC.2
                            | inr hS1 =>
                                cases hS1 with
                                | inl hS => exact ⟨none, hS.1⟩
                                | inr hS2 =>
                                    cases hS2 with
                                    | inl hImm =>
                                        let ⟨vd', _, hSd', _⟩ := hImm
                                        exact ⟨some vd', hSd'⟩
                                    | inr hZst =>
                                        cases hZst.2.1 with
                                        | inl hU =>
                                            exact ⟨some .unit, by
                                              rw [hU] at hZst; exact hZst.1⟩
                                        | inr hE =>
                                            let ⟨ety, hE', hZ'⟩ := hE
                                            refine ⟨some (.enumVal ety 0), ?_⟩
                                            have hS := hZst.1
                                            rw [hE'] at hS
                                            dsimp only [liveUninitSlot] at hS
                                            rw [hZ'] at hS
                                            exact hS
                          let ⟨optD, hSdImm⟩ := hNotDead
                          let ⟨dfLocs', ofLocs', hSetD, hSetO', hRel'⟩ :=
                            localsRel_setElem? prog σ dst.localId hRel hL
                              (.inr (.inr (.inl ⟨vd, vo, rfl, rfl, hVRel⟩)))
                          rw [hSetO] at hSetO'; cases hSetO'
                          refine ⟨rfl, rfl, rfl, rfl, dfLocs', ?_, hRel'⟩
                          unfold writePlace
                          rw [ite_not_true hVRel.1, hG2, hSdImm]
                          dsimp only
                          rw [hSetD]

private theorem evalOpenOperand_entryOpenProgForBody (prog : OpenProgram)
    (defId : DefId) (env : OpenExecEnv) (ob : OpenBody)
    (frame : OpenFrameState) (op : OpenOperand) :
    evalOpenOperand (entryOpenProgForBody prog defId) env ob frame op =
      evalOpenOperand prog env ob frame op := by
  cases op with
  | copy _ | constant _ => unfold evalOpenOperand entryOpenProgForBody; rfl
  | move _ =>
      unfold evalOpenOperand
      simp only [openLiveUninitSlot_entryOpenProgForBody]

private theorem writeOpenPlace_entryOpenProgForBody (prog : OpenProgram)
    (defId : DefId) (env : OpenExecEnv) (ob : OpenBody)
    (frame : OpenFrameState) (dst : OpenPlace) (v : Val) :
    writeOpenPlace (entryOpenProgForBody prog defId) env ob frame dst v =
      writeOpenPlace prog env ob frame dst v := by
  unfold writeOpenPlace
  simp only [checkOpenVal_eq_of_traitRegistry (entryOpenProgForBody prog defId)
    prog rfl]

private theorem openStep_eq_det_none (prog : OpenProgram) (env : OpenExecEnv)
    (wcs : List WhereClause) (defId : DefId) (ob : OpenBody)
    (hNone : OpenProgram.toDay1? (entryOpenProgForBody prog defId) = none)
    (hGet : openListGet? prog.bodies defId = some ob)
    (hErasable : openBodyIsDay1Erasable ob = true)
    (os : OpenState) (of_ : OpenFrameState) (bb : OpenBasicBlock)
    (hFr : os.frames = [of_]) (hDef : of_.defId = defId)
    (hBb : openListGet? ob.basicBlocks of_.blockIdx = some bb) :
    ∀ res, OpenStep (entryOpenProgForBody prog defId) env wcs os res ↔
      res = openEvalDetStep (entryOpenProgForBody prog defId) env os := by
  intro res
  have _ := hNone
  unfold OpenStep OpenStepOnFrames
  rw [hFr]
  dsimp only [OpenStepOnBodyOpt, entryOpenProgForBody]
  rw [hDef, hGet]
  dsimp only [OpenStepOnBlockOpt]
  rw [hBb]
  dsimp only [OpenStepOnStmtEnd]
  cases Nat.beq of_.stmtIdx bb.statements.length with
  | false => rfl
  | true =>
      have hTermPure : openTermIsDay1Pure bb.terminator = true := by
        unfold openBodyIsDay1Erasable at hErasable
        rw [← getElem?_eq_openListGet?] at hBb
        exact all_getElem?_eq_true
          (p := fun b => openTermIsDay1Pure b.terminator) hErasable hBb
      cases hTm : bb.terminator with
      | traitCall _ _ _ _ _ _ _ _ | call _ _ _ _ _ _
      | assert _ _ _ _ _ | unwindResume =>
          rw [hTm] at hTermPure; cases hTermPure
      | goto _ | switchInt _ _ | return_ | unreachable
      | unsupported => dsimp only; rfl

private theorem deallocateLocal_empty {mem : MemoryState} {slot : LocalSlot}
    (hNotInd : ∀ mp, slot ≠ .indirect mp) :
    deallocateLocal mem slot = .ok mem := by
  cases slot with
  | dead | partialTuple _ | immediate _ => rfl
  | indirect mp => exact False.elim (hNotInd mp rfl)

private theorem slotRel_not_indirect {mty : MirTy} {sd so : LocalSlot}
    (h : SlotRel mty sd so) :
    (∀ mp, sd ≠ .indirect mp) ∧ (∀ mp, so ≠ .indirect mp) := by
  constructor <;> intro mp hEq
  · subst hEq
    cases h with
    | inl hC => cases hC.1
    | inr hS1 =>
        cases hS1 with
        | inl hC => cases hC.1
        | inr hS2 =>
            cases hS2 with
            | inl hImm => let ⟨_, _, hEq1, _⟩ := hImm; cases hEq1
            | inr hZst =>
                cases hZst.2.1 with
                | inl hU =>
                    have hC := hZst.1
                    rw [hU] at hC; cases hC
                | inr hE =>
                    let ⟨_, hE', hZ'⟩ := hE
                    have hC := hZst.1
                    rw [hE'] at hC
                    dsimp only [liveUninitSlot] at hC
                    rw [hZ'] at hC
                    cases hC
  · subst hEq
    cases h with
    | inl hC => cases hC.2
    | inr hS1 =>
        cases hS1 with
        | inl hC => cases hC.2
        | inr hS2 =>
            cases hS2 with
            | inl hImm => let ⟨_, _, _, hEq2, _⟩ := hImm; cases hEq2
            | inr hZst => cases hZst.2.2

private theorem openStep_term_sim (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env : OpenExecEnv) (σ : List OpenMirTy) (defId : DefId) (ob : OpenBody)
    (erasedOb : Body) (hObEq : OpenBody.toDay1?
      (OpenBody.subst prog.traitRegistry normFuel σ ob) = some erasedOb)
    (hGet : openListGet? prog.bodies defId = some ob)
    (hErasable : openBodyIsDay1Erasable ob = true)
    (hNone : OpenProgram.toDay1? (entryOpenProgForBody prog defId) = none)
    (hArgLt : Nat.blt ob.argumentCount ob.locals.length = true)
    (ds : State) (os : OpenState) (df : FrameState) (of_ : OpenFrameState)
    (bb : OpenBasicBlock)
    (_hDF : ds.frames = [df]) (hOF : os.frames = [of_])
    (hDDef : df.defId = defId) (hODef : of_.defId = defId)
    (_hBlk : df.blockIdx = of_.blockIdx) (_hStmtIdx : df.stmtIdx = of_.stmtIdx)
    (hRet : of_.retDst = none) (_hDCM : ds.callerMem = ⟨[]⟩)
    (hOCM : os.callerMem = ⟨[]⟩) (_hDMem : ds.mem = entryMemory)
    (hOMem : os.mem = MemoryState.empty)
    (hLRel : LocalsRel prog σ ob.locals df.locals of_.locals)
    (hBb : openListGet? ob.basicBlocks of_.blockIdx = some bb)
    (hAtEnd : Nat.beq of_.stmtIdx bb.statements.length = true)
    (hNoFault : ∀ k, openEvalDetStep (entryOpenProgForBody prog defId) env os ≠
      .fault k) :
    (∀ k, evalTerminator erasedOb
        (eraseOpenBasicBlock (OpenBasicBlock.subst prog.traitRegistry normFuel σ bb))
        df entryMemory ⟨[]⟩ ≠ .fault k) ∧
    (∀ ds', evalTerminator erasedOb
        (eraseOpenBasicBlock (OpenBasicBlock.subst prog.traitRegistry normFuel σ bb))
        df entryMemory ⟨[]⟩ = .step ds' →
      ∃ os',
        openEvalDetStep (entryOpenProgForBody prog defId) env os = .step os' ∧
        StateRel prog σ defId ob ds' os') := by
  have hParts := erasedOb_locals_eq_map prog σ ob erasedOb hObEq
  have hDet : openEvalDetStep (entryOpenProgForBody prog defId) env os =
      match bb.terminator with
      | .goto tgt =>
          .step { os with frames := [{ of_ with blockIdx := tgt, stmtIdx := 0 }] }
      | .return_ =>
          if bb.cleanup then .fault .unsupported
          else match Trusted.MirSemantics.getElem? of_.locals 0 with
            | some (.immediate (some retV)) => .done (.returned ⟨retV, os.callerMem⟩)
            | some (.immediate none) | some .dead => .fault .undefined
            | _ => .fault .unsupported
      | .unreachable => .fault .undefined
      | .switchInt discr tgts =>
          match evalOpenOperand (entryOpenProgForBody prog defId) env ob of_
              discr with
          | .error k => .fault k
          | .ok (v, discrTy, f₁) =>
              match OpenMirTy.toClosedMirTy? discrTy with
              | none => .fault .unsupported
              | some mTy =>
                  if !isPrimitiveReadableTy mTy then .fault .unsupported
                  else
                    let tgtRes : Except FaultKind BasicBlockId :=
                      match v with
                      | .scalar sv =>
                          evalSwitchBranches sv.width sv.bits tgts.otherwise
                            tgts.branches
                      | .bool b =>
                          evalBoolSwitchBranches b tgts.otherwise tgts.branches
                      | .char c =>
                          evalCharSwitchBranches c tgts.otherwise tgts.branches
                      | _ =>
                          match tgts.branches with
                          | [] => .ok tgts.otherwise
                          | _ :: _ => .error .unsupported
                    match tgtRes with
                    | .error k => .fault k
                    | .ok tgt =>
                        .step { os with frames :=
                          [{ f₁ with blockIdx := tgt, stmtIdx := 0 }] }
      | .unwindResume =>
          if !bb.cleanup then .fault .unsupported
          else .done (.unwound os.callerMem)
      | .assert cond exp _ tgt uw =>
          match evalOpenOperand (entryOpenProgForBody prog defId) env ob of_
              cond with
          | .error k => .fault k
          | .ok (v, _, f₁) =>
              match v with
              | .bool b =>
                  if b == exp then
                    .step { os with frames :=
                      [{ f₁ with blockIdx := tgt, stmtIdx := 0 }] }
                  else openUnwindWith os os.callerMem [] uw (some f₁)
              | _ => .fault .unsupported
      | .call _ _ _ _ _ _ | .traitCall _ _ _ _ _ _ _ _
      | .unsupported => .fault .unsupported := by
    unfold openEvalDetStep openEvalDetStepAux
    rw [hNone, hOF]
    dsimp only [entryOpenProgForBody]
    rw [hODef, hGet]
    dsimp only
    rw [hBb]
    dsimp only
    have hNoneStmt : openListGet? bb.statements of_.stmtIdx = none := by
      have hEqIdx := nat_beq_eq hAtEnd
      have hAux : ∀ {α : Type} (xs : List α), openListGet? xs xs.length = none := by
        intro α xs
        induction xs with
        | nil => rfl
        | cons _ _ ih => exact ih
      rw [hEqIdx]
      exact hAux bb.statements
    rw [hNoneStmt]
    dsimp only
    rw [ite_not_true hAtEnd]
    cases bb.terminator with
    | switchInt discr tgts =>
        dsimp only
        cases hOp' : evalOpenOperand (entryOpenProgForBody prog defId) env ob
            of_ discr with
        | error _ =>
            have hOp'' := hOp'
            dsimp only [entryOpenProgForBody] at hOp''
            rw [hOp'']
        | ok res =>
            have hOp'' := hOp'
            dsimp only [entryOpenProgForBody] at hOp''
            rw [hOp'']
            cases res with
            | mk v res' =>
                cases res' with
                | mk discrTy _ =>
            dsimp only
            cases hCl' : OpenMirTy.toClosedMirTy? discrTy with
            | none => rfl
            | some mTy => rfl
    | _ => rfl
  rw [hDet] at hNoFault
  have hTermPure : openTermIsDay1Pure bb.terminator = true := by
    unfold openBodyIsDay1Erasable at hErasable
    rw [← getElem?_eq_openListGet?] at hBb
    exact all_getElem?_eq_true
      (p := fun b => openTermIsDay1Pure b.terminator) hErasable hBb
  cases hTm : bb.terminator with
  | traitCall _ _ _ _ _ _ _ _ | call _ _ _ _ _ _ | assert _ _ _ _ _
  | unwindResume =>
      rw [hTm] at hTermPure; cases hTermPure
  | unsupported =>
      rw [hTm] at hNoFault
      exact False.elim (hNoFault .unsupported rfl)
  | unreachable =>
      rw [hTm] at hNoFault
      exact False.elim (hNoFault .undefined rfl)
  | goto tgt =>
      rw [hTm] at hDet
      dsimp only [OpenBasicBlock.subst, OpenTerminatorKind.subst,
        eraseOpenBasicBlock, eraseOpenTerminatorKind, evalTerminator, jumpToBlock]
      rw [hTm]
      dsimp only
      constructor
      · intro k hF; cases hF
      · intro ds' hS
        cases hS
        refine ⟨{ os with frames := [{ of_ with blockIdx := tgt, stmtIdx := 0 }] },
          ?_, ?_⟩
        · rw [hDet]
        · exact ⟨{ df with blockIdx := tgt, stmtIdx := 0 },
            { of_ with blockIdx := tgt, stmtIdx := 0 }, rfl, rfl, hDDef, hODef,
            rfl, rfl, hRet, rfl, hOCM, rfl, hOMem, hLRel⟩
  | return_ =>
      rw [hTm] at hNoFault
      cases hCln : bb.cleanup with
      | true =>
          dsimp only at hNoFault
          rw [ite_cond_true hCln] at hNoFault
          exact False.elim (hNoFault .unsupported rfl)
      | false =>
          dsimp only at hNoFault
          rw [ite_cond_false hCln] at hNoFault
          cases localsRel_getElem? prog σ 0 hLRel with
          | inl hNone =>
              cases hObs : ob.locals with
              | nil => rw [hObs] at hArgLt; cases hArgLt
              | cons _ _ => rw [hObs] at hNone; cases hNone.1
          | inr hSome =>
              let ⟨ty0, sd0, so0, hG0, hSD0, hSO0, hSlot0⟩ := hSome
              rw [hSO0] at hNoFault
              cases so0 with
              | dead => exact False.elim (hNoFault .undefined rfl)
              | partialTuple _ =>
                  cases hSlot0 with
                  | inl hC => cases hC.2
                  | inr hS1 =>
                      cases hS1 with
                      | inl hC => cases hC.2
                      | inr hS2 =>
                          cases hS2 with
                          | inl hImm =>
                              let ⟨_, _, _, hSo, _⟩ := hImm; cases hSo
                          | inr hZst => cases hZst.2.2
              | indirect mp =>
                  exact False.elim ((slotRel_not_indirect hSlot0).2 mp rfl)
              | immediate optVo =>
                  cases optVo with
                  | none => exact False.elim (hNoFault .undefined rfl)
                  | some retVo =>
                      cases hSlot0 with
                      | inl hC => cases hC.2
                      | inr hS1 =>
                          cases hS1 with
                          | inl hC => cases hC.2
                          | inr hS2 =>
                              cases hS2 with
                              | inr hC => cases hC.2.2
                              | inl hImm =>
                                  let ⟨retVd, _, hSD, _, _⟩ := hImm
                                  rw [hSD] at hSD0
                                  dsimp only [OpenBasicBlock.subst,
                                    OpenTerminatorKind.subst, eraseOpenBasicBlock,
                                    eraseOpenTerminatorKind, evalTerminator]
                                  rw [hTm]
                                  dsimp only
                                  rw [ite_cond_false hCln, hSD0]
                                  exact ⟨(fun k hF => by cases hF),
                                    fun ds' hS => by cases hS⟩
  | switchInt discr tgts =>
      rw [hTm] at hDet hNoFault
      dsimp only at hNoFault
      cases hOp : evalOpenOperand (entryOpenProgForBody prog defId) env ob of_
          discr with
      | error k =>
          rw [hOp] at hNoFault
          exact False.elim (hNoFault k rfl)
      | ok resOp =>
          cases resOp with
          | mk v resOp' =>
              cases resOp' with
              | mk discrTy f₁ =>
          rw [hOp] at hNoFault
          dsimp only at hNoFault
          cases hCl : OpenMirTy.toClosedMirTy? discrTy with
          | none =>
              rw [hCl] at hNoFault
              exact False.elim (hNoFault .unsupported rfl)
          | some mTy =>
              rw [hCl] at hNoFault
              dsimp only at hNoFault
              cases hPrim : isPrimitiveReadableTy mTy with
              | false =>
                  rw [ite_not_false hPrim] at hNoFault
                  exact False.elim (hNoFault .unsupported rfl)
              | true =>
                  rw [ite_not_true hPrim] at hNoFault
                  have hOp' : evalOpenOperand prog env ob of_ discr =
                      .ok (v, discrTy, f₁) := by
                    rw [← evalOpenOperand_entryOpenProgForBody prog defId]
                    exact hOp
                  have hOpSim := evalOpenOperand_prim_sim
                    prog env hRegWf σ ob df.locals
                    of_ hLRel discr v discrTy f₁ mTy isPrimitiveReadableTy hOp'
                    hCl hPrim
                  let ⟨h1, h2, h3, h4, dfLocs₁, hSlotSim, hRel₁⟩ := hOpSim
                  have hPrimEv :
                      evalPrimitiveOperand erasedOb.locals df.locals entryMemory
                        (eraseOpenOperand
                          (OpenOperand.subst prog.traitRegistry normFuel σ
                            discr)) =
                        .ok (v, dfLocs₁, entryMemory) := by
                    unfold evalPrimitiveOperand
                    rw [hParts.1, map_substAndNormalize_eq_erasedTy]
                    change (match evalOperandToSlot
                        (ob.locals.map (erasedTy prog σ)) df.locals entryMemory
                        isPrimitiveReadableTy
                        (eraseOpenOperand
                          (OpenOperand.subst prog.traitRegistry normFuel σ
                            discr)) with
                      | .error k => .error k
                      | .ok (ty, optVal, locals', mem') =>
                        if !isPrimitiveReadableTy ty then .error .unsupported
                        else match optVal with
                          | some v' => .ok (v', locals', mem')
                          | none => .error .undefined) =
                      Except.ok (v, dfLocs₁, entryMemory)
                    rw [hSlotSim]
                    dsimp only
                    rw [ite_not_true hPrim]
                  have finishSwitch :
                      ∀ (tgtRes : Except FaultKind BasicBlockId),
                        let openRes : StepResult OpenState TerminalOut :=
                          match tgtRes with
                          | .error k => .fault k
                          | .ok tgt => .step { os with frames :=
                              [{ f₁ with blockIdx := tgt, stmtIdx := 0 }] }
                        let closedRes : StepResult State TerminalOut :=
                          match tgtRes with
                          | .error k => .fault k
                          | .ok target => .step {
                              frames := [{
                                df with
                                locals := dfLocs₁,
                                blockIdx := target,
                                stmtIdx := 0 }],
                              mem := entryMemory }
                        openRes =
                          openEvalDetStep (entryOpenProgForBody prog defId)
                            env os →
                        (∀ k, openRes ≠ StepResult.fault k) →
                        (∀ k, closedRes ≠ StepResult.fault k) ∧
                        (∀ ds', closedRes = StepResult.step ds' →
                           ∃ os', openEvalDetStep
                             (entryOpenProgForBody prog defId) env os =
                             StepResult.step os' ∧
                             StateRel prog σ defId ob ds' os') := by
                    intro tgtRes openRes closedRes hDetT hNoFT
                    cases tgtRes with
                    | error k =>
                        dsimp only [openRes] at hNoFT
                        exact False.elim (hNoFT k rfl)
                    | ok tgt =>
                        dsimp only [closedRes]
                        refine ⟨(fun k hk => by cases hk), fun ds' hS => ?_⟩
                        cases hS
                        exact ⟨_, hDetT.symm, ⟨{
                            df with
                            locals := dfLocs₁,
                            blockIdx := tgt,
                            stmtIdx := 0 },
                          { f₁ with blockIdx := tgt, stmtIdx := 0 }, rfl, rfl,
                          hDDef, h1.trans hODef, rfl, rfl, h4.trans hRet,
                          rfl, hOCM, rfl, hOMem, hRel₁⟩⟩
                  dsimp only at hDet
                  rw [hOp] at hDet
                  dsimp only at hDet
                  rw [hCl] at hDet
                  dsimp only at hDet
                  rw [ite_not_true hPrim] at hDet
                  dsimp only [OpenBasicBlock.subst, OpenTerminatorKind.subst,
                    eraseOpenBasicBlock, eraseOpenTerminatorKind,
                    evalTerminator, jumpToBlock]
                  rw [hTm]
                  dsimp only
                  rw [hPrimEv]
                  dsimp only
                  cases v <;>
                    exact finishSwitch _
                      (by rw [hDet] <;> first | rfl | (dsimp only; rfl))
                      hNoFault

private theorem mutability_beq_self :
    ∀ m : Mutability, Mutability.beq m m = true
  | .shared | .mut => rfl

mutual
  private theorem mirTy_beq_self : ∀ m : MirTy, MirTy.beq m m = true
    | .bool | .unit | .never | .char | .ordering | .str | .unsupported => rfl
    | .int w s => by
        dsimp only [MirTy.beq]
        rw [intWidth_beq_self w, beq_self_eq_true s]
        rfl
    | .enum ety => enumTy_beq_self ety
    | .tuple fs => mirTyList_beq_self fs
    | .ref m p | .rawPtr m p => by
        dsimp only [MirTy.beq]
        rw [mutability_beq_self m, mirTy_beq_self p]
        rfl
    | .slice e | .rangeTo e | .rangeFrom e | .range e | .option e | .vec e
    | .box e =>
        mirTy_beq_self e
    | .array e n => by
        dsimp only [MirTy.beq]
        rw [nat_beq_self n, mirTy_beq_self e]
        rfl

  private theorem mirTyList_beq_self :
      ∀ fs : List MirTy, MirTy.beqList fs fs = true
    | [] => rfl
    | x :: xs => by
        dsimp only [MirTy.beqList]
        rw [mirTy_beq_self x, mirTyList_beq_self xs]
        rfl
end

private theorem erasedTy_of_normClosed (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (σ : List OpenMirTy) {ty : OpenMirTy} {m : MirTy}
    (hCl : OpenMirTy.toClosedMirTy? (normalizeOpenTy prog.traitRegistry normFuel ty) =
      some m) :
    erasedTy prog σ ty = m := by
  unfold erasedTy
  rw [← substAndNormalize_normalize_eq prog.traitRegistry hRegWf σ ty]
  exact toClosedMirTy?_erase_subst prog.traitRegistry σ hCl

private theorem openStep_assign_sim (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env : OpenExecEnv) (σ : List OpenMirTy) (paramSpecs : List TypeLayoutSpec)
    (hLenEq : paramSpecs.length = σ.length)
    (hMap : ∀ (i : Nat) (ty : OpenMirTy), openListGet? σ i = some ty →
      ∃ sp : TypeLayoutSpec, openListGet? paramSpecs i = some sp ∧
        evalOpenTySpec prog.traitRegistry normFuel
          { env.typeSpecs with paramSpecs := [], paramInvs := [] } ty =
          some sp ∧
        OpenMirTy.isClosed ty = true)
    (defId : DefId) (ob : OpenBody) (erasedOb : Body)
    (hObEq : OpenBody.toDay1? (OpenBody.subst prog.traitRegistry normFuel σ ob) =
      some erasedOb)
    (hAdm : openLocalsAdmitted prog
      { env with typeSpecs := (substTypeSpecEnv env.typeSpecs paramSpecs
          (List.replicate paramSpecs.length (fun _ => True))
          (instAssocSpecs prog.traitRegistry env.typeSpecs σ)) } ob.locals)
    (hSupp : erasedOb.locals.all isSupportedScalarOrUnitTy = true)
    (hGet : openListGet? prog.bodies defId = some ob)
    (hNone : OpenProgram.toDay1? (entryOpenProgForBody prog defId) = none)
    (ds : State) (os : OpenState) (df : FrameState) (of_ : OpenFrameState)
    (bb : OpenBasicBlock) (dst : OpenPlace) (rv : OpenRvalue)
    (_hDF : ds.frames = [df]) (hOF : os.frames = [of_])
    (hDDef : df.defId = defId) (hODef : of_.defId = defId)
    (hBlk : df.blockIdx = of_.blockIdx) (hStmtIdx : df.stmtIdx = of_.stmtIdx)
    (hRet : of_.retDst = none) (_hDCM : ds.callerMem = ⟨[]⟩)
    (hOCM : os.callerMem = ⟨[]⟩) (_hDMem : ds.mem = entryMemory)
    (hOMem : os.mem = MemoryState.empty)
    (hLRel : LocalsRel prog σ ob.locals df.locals of_.locals)
    (hBb : openListGet? ob.basicBlocks of_.blockIdx = some bb)
    (hStmt : openListGet? bb.statements of_.stmtIdx = some (.assign dst rv))
    (hNoFault : ∀ k, openEvalDetStep (entryOpenProgForBody prog defId)
      { env with typeSpecs := (substTypeSpecEnv env.typeSpecs paramSpecs
          (List.replicate paramSpecs.length (fun _ => True))
          (instAssocSpecs prog.traitRegistry env.typeSpecs σ)) } os ≠ .fault k) :
    let env' : OpenExecEnv :=
      { env with typeSpecs := (substTypeSpecEnv env.typeSpecs paramSpecs
          (List.replicate paramSpecs.length (fun _ => True))
          (instAssocSpecs prog.traitRegistry env.typeSpecs σ)) }
    (∀ k, evalStatement erasedOb df entryMemory ⟨[]⟩
        (eraseOpenStatementKind
          (OpenStatementKind.subst prog.traitRegistry normFuel σ
            (.assign dst rv))) ≠ .fault k) ∧
    (∀ ds', evalStatement erasedOb df entryMemory ⟨[]⟩
        (eraseOpenStatementKind
          (OpenStatementKind.subst prog.traitRegistry normFuel σ
            (.assign dst rv))) = .step ds' →
      ∃ os',
        openEvalDetStep (entryOpenProgForBody prog defId) env' os = .step os' ∧
        StateRel prog σ defId ob ds' os') := by
  intro env'
  have hParts := erasedOb_locals_eq_map prog σ ob erasedOb hObEq
  have hDet : openEvalDetStep (entryOpenProgForBody prog defId) env' os =
      if !dst.projection.isEmpty then .fault .unsupported
      else match openListGet? ob.locals dst.localId with
      | none => .fault .unsupported
      | some dstTy =>
          let dstN := normalizeOpenTy prog.traitRegistry normFuel dstTy
          (fun rv' : OpenRvalue =>
          match rv' with
          | .use op =>
              match evalOpenOperand (entryOpenProgForBody prog defId) env' ob of_
                  op with
              | .error k => .fault k
              | .ok (v, srcTy, f₁) =>
                  let srcN := normalizeOpenTy prog.traitRegistry normFuel srcTy
                  if !OpenMirTy.beq srcN dstN then .fault .unsupported
                  else match writeOpenPlace (entryOpenProgForBody prog defId)
                      env' ob f₁ dst v with
                    | .error k => .fault k
                    | .ok f₂ =>
                        .step { os with frames :=
                          { f₂ with stmtIdx := of_.stmtIdx + 1 } :: [] }
          | .binaryOp op lhs rhs =>
              match evalOpenOperand (entryOpenProgForBody prog defId) env' ob of_
                  lhs with
              | .error k => .fault k
              | .ok (vl, srcL, f₁) =>
                  match evalOpenOperand (entryOpenProgForBody prog defId) env' ob
                      f₁ rhs with
                  | .error k => .fault k
                  | .ok (vr, srcR, f₂) =>
                      match OpenMirTy.toClosedMirTy? srcL,
                            OpenMirTy.toClosedMirTy? srcR,
                            OpenMirTy.toClosedMirTy? dstN,
                            evalBinOp op vl vr with
                      | some ml, some mr, some mDst, .ok resV =>
                          if !isPrimitiveReadableTy ml ||
                             !isPrimitiveReadableTy mr || !checkVal resV mDst
                          then .fault .unsupported
                          else match writeOpenPlace
                              (entryOpenProgForBody prog defId) env' ob f₂ dst
                              resV with
                            | .error k => .fault k
                            | .ok f₃ =>
                                .step { os with frames :=
                                  { f₃ with stmtIdx := of_.stmtIdx + 1 } :: [] }
                      | _, _, _, .error k => .fault k
                      | _, _, _, _ => .fault .unsupported
          | .unaryOp op opnd =>
              match evalOpenOperand (entryOpenProgForBody prog defId) env' ob of_
                  opnd with
              | .error k => .fault k
              | .ok (v, srcTy, f₁) =>
                  match OpenMirTy.toClosedMirTy? srcTy,
                        OpenMirTy.toClosedMirTy? dstN, evalUnOp op v with
                  | some mSrc, some mDst, .ok resV =>
                      if !isPrimitiveReadableTy mSrc || !checkVal resV mDst
                      then .fault .unsupported
                      else match writeOpenPlace
                          (entryOpenProgForBody prog defId) env' ob f₁ dst resV
                          with
                        | .error k => .fault k
                        | .ok f₂ =>
                            .step { os with frames :=
                              { f₂ with stmtIdx := of_.stmtIdx + 1 } :: [] }
                  | _, _, .error k => .fault k
                  | _, _, _ => .fault .unsupported
          | .cast .intToInt opnd castTy =>
              let castN := normalizeOpenTy prog.traitRegistry normFuel castTy
              if !OpenMirTy.beq castN dstN then .fault .unsupported
              else match evalOpenOperand (entryOpenProgForBody prog defId) env'
                      ob of_ opnd, OpenMirTy.toClosedMirTy? castN with
                | .ok (v, srcTy, f₁), some mCast =>
                    match OpenMirTy.toClosedMirTy? srcTy with
                    | some mSrc =>
                        if !isIntLikeTy mSrc then .fault .unsupported
                        else match evalIntToIntCast v mCast with
                          | .error k => .fault k
                          | .ok resV =>
                              match writeOpenPlace
                                  (entryOpenProgForBody prog defId) env' ob f₁
                                  dst resV with
                              | .error k => .fault k
                              | .ok f₂ =>
                                  .step { os with frames :=
                                    { f₂ with stmtIdx := of_.stmtIdx + 1 } :: [] }
                    | none => .fault .unsupported
                | .error k, _ => .fault k
                | _, none => .fault .unsupported
          | _ => .fault .unsupported) rv := by
    unfold openEvalDetStep openEvalDetStepAux
    rw [hNone, hOF]
    dsimp only [entryOpenProgForBody]
    rw [hODef, hGet]
    dsimp only
    rw [hBb]
    dsimp only
    rw [hStmt]
    rfl
  rw [hDet] at hNoFault
  dsimp only at hNoFault
  cases hEmp : dst.projection.isEmpty with
  | false =>
      rw [ite_not_false hEmp] at hNoFault
      exact False.elim (hNoFault .unsupported rfl)
  | true =>
      have hProjNil : dst.projection = [] := list_isEmpty_eq_nil hEmp
      rw [ite_not_true hEmp] at hNoFault
      cases hDst : openListGet? ob.locals dst.localId with
      | none =>
          rw [hDst] at hNoFault
          exact False.elim (hNoFault .unsupported rfl)
      | some dstTy =>
          rw [hDst] at hNoFault
          dsimp only at hNoFault
          have hDstD : Trusted.MirSemantics.getElem? erasedOb.locals dst.localId =
              some (erasedTy prog σ dstTy) := by
            rw [hParts.1, mirGetElem?_map, getElem?_eq_openListGet?, hDst]
            rfl
          cases rv with
          | discriminant _ | ref _ _ | addressOf _ _ | aggregateTuple _
          | unsupported =>
              exact False.elim (hNoFault .unsupported rfl)
          | use op =>
              dsimp only at hNoFault
              cases hOp : evalOpenOperand (entryOpenProgForBody prog defId) env'
                  ob of_ op with
              | error k => rw [hOp] at hNoFault; exact False.elim (hNoFault k rfl)
              | ok resOp =>
                  cases resOp with
                  | mk vo resOp' =>
                      cases resOp' with
                      | mk srcTy f₁ =>
                  rw [hOp] at hNoFault
                  dsimp only at hNoFault
                  cases hBeq : OpenMirTy.beq
                      (normalizeOpenTy prog.traitRegistry normFuel srcTy)
                      (normalizeOpenTy prog.traitRegistry normFuel dstTy) with
                  | false =>
                      rw [ite_not_false hBeq] at hNoFault
                      exact False.elim (hNoFault .unsupported rfl)
                  | true =>
                      rw [ite_not_true hBeq] at hNoFault
                      have hNormEq := openMirTy_beq_eq hBeq
                      have hErEq : erasedTy prog σ srcTy =
                          erasedTy prog σ dstTy := by
                        unfold erasedTy
                        rw [← substAndNormalize_normalize_eq prog.traitRegistry
                            hRegWf σ srcTy,
                          ← substAndNormalize_normalize_eq prog.traitRegistry
                            hRegWf σ dstTy, hNormEq]
                      cases hW : writeOpenPlace (entryOpenProgForBody prog defId)
                          env' ob f₁ dst vo with
                      | error k =>
                          rw [hW] at hNoFault
                          exact False.elim (hNoFault k rfl)
                      | ok f₂ =>
                          have hOp' : evalOpenOperand prog env' ob of_ op =
                              .ok (vo, srcTy, f₁) := by
                            rw [← evalOpenOperand_entryOpenProgForBody prog defId]
                            exact hOp
                          have hOpSim := evalOpenOperand_sim
                            prog env' hRegWf σ ob
                            df.locals of_ (fun s => MirTy.beq s
                              (erasedTy prog σ dstTy)) hLRel op vo srcTy f₁ hOp'
                          let ⟨hf1, hf2, hf3, hf4, hOpBody⟩ := hOpSim
                          cases op with
                          | copy p =>
                              let ⟨_, _, vd, dfLocs₁, hSlotSim, hVRel, hRel₁⟩ :=
                                hOpBody
                              rw [hErEq] at hSlotSim hVRel
                              have hW' : writeOpenPlace prog env' ob f₁ dst vo =
                                  .ok f₂ := by
                                rw [← writeOpenPlace_entryOpenProgForBody prog defId]
                                exact hW
                              have hWSim := writePlace_sim
                                prog env' σ ob
                                dfLocs₁ f₁ dst dstTy vd vo f₂ hRel₁ hDst hW' hVRel
                              let ⟨hw1, hw2, hw3, hw4, dfLocs₂, hWPlace, hRel₂⟩ :=
                                hWSim
                              have hStmtD : evalStatement erasedOb df entryMemory
                                  ⟨[]⟩ (eraseOpenStatementKind
                                    (OpenStatementKind.subst prog.traitRegistry
                                      normFuel σ (.assign dst (.use (.copy p))))) =
                                  .step {
                                    frames := [{ df with
                                      stmtIdx := df.stmtIdx + 1,
                                      locals := dfLocs₂ }]
                                    callerMem := ⟨[]⟩
                                    mem := entryMemory } := by
                                dsimp only [OpenStatementKind.subst,
                                  eraseOpenStatementKind, OpenPlace.subst,
                                  eraseOpenPlace, OpenRvalue.subst,
                                  eraseOpenRvalue, evalStatement]
                                rw [hProjNil]
                                dsimp only [List.map, List.isEmpty]
                                rw [ite_cond_false (rfl : (!true) = false), hDstD]
                                dsimp only [evalRvalue]
                                rw [hParts.1, map_substAndNormalize_eq_erasedTy,
                                  hSlotSim]
                                dsimp only
                                rw [ite_not_true (mirTy_beq_self _)]
                                dsimp only
                                rw [hWPlace]
                              rw [hStmtD]
                              refine ⟨(fun k hk => by cases hk), fun ds' hS => ?_⟩
                              cases hS
                              refine ⟨{ os with frames :=
                                [{ f₂ with stmtIdx := of_.stmtIdx + 1 }] }, ?_, ?_⟩
                              · rw [hDet, ite_not_true hEmp, hDst]
                                dsimp only
                                rw [hOp]
                                dsimp only
                                rw [ite_not_true hBeq, hW]
                              · exact ⟨{ df with
                                      stmtIdx := df.stmtIdx + 1,
                                      locals := dfLocs₂ },
                                  { f₂ with stmtIdx := of_.stmtIdx + 1 },
                                  rfl, rfl, hDDef, hw1.trans (hf1.trans hODef),
                                  by dsimp only; rw [hBlk, hw2, hf2],
                                  by dsimp only; rw [hStmtIdx],
                                  hw4.trans (hf4.trans hRet), rfl, hOCM, rfl,
                                  hOMem, hRel₂⟩
                          | move p =>
                              let ⟨_, _, vd, dfLocs₁, hSlotSim, hVRel, hRel₁⟩ :=
                                hOpBody
                              rw [hErEq] at hSlotSim hVRel
                              have hW' : writeOpenPlace prog env' ob f₁ dst vo =
                                  .ok f₂ := by
                                rw [← writeOpenPlace_entryOpenProgForBody prog defId]
                                exact hW
                              have hWSim := writePlace_sim
                                prog env' σ ob
                                dfLocs₁ f₁ dst dstTy vd vo f₂ hRel₁ hDst hW' hVRel
                              let ⟨hw1, hw2, hw3, hw4, dfLocs₂, hWPlace, hRel₂⟩ :=
                                hWSim
                              have hStmtD : evalStatement erasedOb df entryMemory
                                  ⟨[]⟩ (eraseOpenStatementKind
                                    (OpenStatementKind.subst prog.traitRegistry
                                      normFuel σ (.assign dst (.use (.move p))))) =
                                  .step {
                                    frames := [{ df with
                                      stmtIdx := df.stmtIdx + 1,
                                      locals := dfLocs₂ }]
                                    callerMem := ⟨[]⟩
                                    mem := entryMemory } := by
                                dsimp only [OpenStatementKind.subst,
                                  eraseOpenStatementKind, OpenPlace.subst,
                                  eraseOpenPlace, OpenRvalue.subst,
                                  eraseOpenRvalue, evalStatement]
                                rw [hProjNil]
                                dsimp only [List.map, List.isEmpty]
                                rw [ite_cond_false (rfl : (!true) = false), hDstD]
                                dsimp only [evalRvalue]
                                rw [hParts.1, map_substAndNormalize_eq_erasedTy,
                                  hSlotSim]
                                dsimp only
                                rw [ite_not_true (mirTy_beq_self _)]
                                dsimp only
                                rw [hWPlace]
                              rw [hStmtD]
                              refine ⟨(fun k hk => by cases hk), fun ds' hS => ?_⟩
                              cases hS
                              refine ⟨{ os with frames :=
                                [{ f₂ with stmtIdx := of_.stmtIdx + 1 }] }, ?_, ?_⟩
                              · rw [hDet, ite_not_true hEmp, hDst]
                                dsimp only
                                rw [hOp]
                                dsimp only
                                rw [ite_not_true hBeq, hW]
                              · exact ⟨{ df with
                                      stmtIdx := df.stmtIdx + 1,
                                      locals := dfLocs₂ },
                                  { f₂ with stmtIdx := of_.stmtIdx + 1 },
                                  rfl, rfl, hDDef, hw1.trans (hf1.trans hODef),
                                  by dsimp only; rw [hBlk, hw2, hf2],
                                  by dsimp only; rw [hStmtIdx],
                                  hw4.trans (hf4.trans hRet), rfl, hOCM, rfl,
                                  hOMem, hRel₂⟩
                          | constant c =>
                              let ⟨hSrcC, hF1Eq, hBr⟩ := hOpBody
                              subst hSrcC; subst hF1Eq
                              cases hBr with
                              | inl hBrL =>
                                let ⟨mc, hCl, hErC, hLit, hSlotSim, hVRel⟩ := hBrL
                                have hDstMc : erasedTy prog σ dstTy = mc :=
                                  hErEq.symm.trans hErC
                                rw [← hDstMc] at hSlotSim hVRel
                                have hW' : writeOpenPlace prog env' ob f₁ dst
                                    vo = .ok f₂ := by
                                  rw [← writeOpenPlace_entryOpenProgForBody prog defId]
                                  exact hW
                                have hWSim := writePlace_sim
                                  prog env' σ ob
                                  df.locals f₁ dst dstTy vo vo f₂ hLRel hDst hW'
                                  hVRel
                                let ⟨hw1, hw2, hw3, hw4, dfLocs₂, hWPlace, hRel₂⟩ :=
                                  hWSim
                                have hStmtD : evalStatement erasedOb df entryMemory
                                    ⟨[]⟩ (eraseOpenStatementKind
                                      (OpenStatementKind.subst prog.traitRegistry
                                        normFuel σ
                                        (.assign dst (.use (.constant c))))) =
                                    .step {
                                      frames := [{ df with
                                        stmtIdx := df.stmtIdx + 1,
                                        locals := dfLocs₂ }]
                                      callerMem := ⟨[]⟩
                                      mem := entryMemory } := by
                                  dsimp only [OpenStatementKind.subst,
                                    eraseOpenStatementKind, OpenPlace.subst,
                                    eraseOpenPlace, OpenRvalue.subst,
                                    eraseOpenRvalue, evalStatement]
                                  rw [hProjNil]
                                  dsimp only [List.map, List.isEmpty]
                                  rw [ite_cond_false (rfl : (!true) = false),
                                    hDstD]
                                  dsimp only [evalRvalue]
                                  rw [hParts.1,
                                    map_substAndNormalize_eq_erasedTy, hSlotSim]
                                  dsimp only
                                  rw [ite_not_true (mirTy_beq_self _)]
                                  dsimp only
                                  rw [hWPlace]
                                rw [hStmtD]
                                refine ⟨(fun k hk => by cases hk),
                                  fun ds' hS => ?_⟩
                                cases hS
                                refine ⟨{ os with frames :=
                                  [{ f₂ with stmtIdx := f₁.stmtIdx + 1 }] }, ?_, ?_⟩
                                · rw [hDet, ite_not_true hEmp, hDst]
                                  dsimp only
                                  rw [hOp]
                                  dsimp only
                                  rw [ite_not_true hBeq, hW]
                                · exact ⟨{ df with
                                        stmtIdx := df.stmtIdx + 1,
                                        locals := dfLocs₂ },
                                    { f₂ with stmtIdx := f₁.stmtIdx + 1 },
                                    rfl, rfl, hDDef, hw1.trans hODef,
                                    by dsimp only; rw [hBlk, hw2],
                                    by dsimp only; rw [hStmtIdx],
                                    hw4.trans hRet, rfl, hOCM, rfl, hOMem, hRel₂⟩
                              | inr hBrR =>
                                let ⟨hClNone, hLitZ, hVoBytes, sp, hEvC, hInhab,
                                  hSz⟩ := hBrR
                                subst hVoBytes
                                let ⟨dstMty, sp', hClDst, _, hSuppDst, hEvDst, _, _⟩ :=
                                  erasedTy_local_props prog env' σ ob erasedOb
                                    hObEq hAdm hSupp dst.localId dstTy hDst
                                have hSpEq : sp' = sp := by
                                  have hEvCN : evalOpenTySpec prog.traitRegistry
                                      normFuel env'.typeSpecs c.ty =
                                      evalOpenTySpec prog.traitRegistry normFuel
                                        env'.typeSpecs dstTy := by
                                    unfold evalOpenTySpec
                                    rw [hNormEq]
                                  rw [hEvCN, hEvDst] at hEvC
                                  cases hEvC; rfl
                                subst hSpEq
                                have hDstMtyEq : erasedTy prog σ dstTy = dstMty :=
                                  toClosedMirTy?_eraseOpenTy hClDst
                                let ⟨vd, hConstZ, hVRelZ⟩ :=
                                  valRel_zeroSized_const prog hRegWf env σ
                                    paramSpecs hLenEq hMap dstTy dstMty sp'
                                    hClDst hSuppDst hEvDst hInhab hSz
                                rw [← hDstMtyEq] at hVRelZ hConstZ
                                have hW' : writeOpenPlace prog env' ob f₁ dst
                                    (.bytes []) = .ok f₂ := by
                                  rw [← writeOpenPlace_entryOpenProgForBody prog defId]
                                  exact hW
                                have hWSim := writePlace_sim
                                  prog env' σ ob
                                  df.locals f₁ dst dstTy vd (.bytes []) f₂ hLRel
                                  hDst hW' hVRelZ
                                let ⟨hw1, hw2, hw3, hw4, dfLocs₂, hWPlace, hRel₂⟩ :=
                                  hWSim
                                have hStmtD : evalStatement erasedOb df entryMemory
                                    ⟨[]⟩ (eraseOpenStatementKind
                                      (OpenStatementKind.subst prog.traitRegistry
                                        normFuel σ
                                        (.assign dst (.use (.constant c))))) =
                                    .step {
                                      frames := [{ df with
                                        stmtIdx := df.stmtIdx + 1,
                                        locals := dfLocs₂ }]
                                      callerMem := ⟨[]⟩
                                      mem := entryMemory } := by
                                  dsimp only [OpenStatementKind.subst,
                                    eraseOpenStatementKind, OpenPlace.subst,
                                    eraseOpenPlace, OpenRvalue.subst,
                                    eraseOpenRvalue, OpenOperand.subst,
                                    eraseOpenOperand, evalStatement]
                                  rw [hProjNil]
                                  dsimp only [List.map, List.isEmpty]
                                  rw [ite_cond_false (rfl : (!true) = false), hDstD]
                                  dsimp only [evalRvalue, evalOperandToSlot]
                                  rw [erasedTy_def, hLitZ, hErEq, hConstZ]
                                  dsimp only
                                  rw [ite_not_true (mirTy_beq_self _)]
                                  dsimp only
                                  rw [hWPlace]
                                rw [hStmtD]
                                refine ⟨(fun k hk => by cases hk),
                                  fun ds' hS => ?_⟩
                                cases hS
                                refine ⟨{ os with frames :=
                                  [{ f₂ with stmtIdx := f₁.stmtIdx + 1 }] }, ?_, ?_⟩
                                · rw [hDet, ite_not_true hEmp, hDst]
                                  dsimp only
                                  rw [hOp]
                                  dsimp only
                                  rw [ite_not_true hBeq, hW]
                                · exact ⟨{ df with
                                        stmtIdx := df.stmtIdx + 1,
                                        locals := dfLocs₂ },
                                    { f₂ with stmtIdx := f₁.stmtIdx + 1 },
                                    rfl, rfl, hDDef, hw1.trans hODef,
                                    by dsimp only; rw [hBlk, hw2],
                                    by dsimp only; rw [hStmtIdx],
                                    hw4.trans hRet, rfl, hOCM, rfl, hOMem, hRel₂⟩
          | binaryOp op lhs rhs =>
              dsimp only at hNoFault
              cases hLhs : evalOpenOperand (entryOpenProgForBody prog defId) env'
                  ob of_ lhs with
              | error k => rw [hLhs] at hNoFault; exact False.elim (hNoFault k rfl)
              | ok resL =>
                  cases resL with
                  | mk vl resL' =>
                      cases resL' with
                      | mk srcL f₁ =>
                  rw [hLhs] at hNoFault
                  dsimp only at hNoFault
                  cases hRhs : evalOpenOperand
                      (entryOpenProgForBody prog defId) env' ob f₁ rhs
                      with
                  | error k =>
                      rw [hRhs] at hNoFault
                      exact False.elim (hNoFault k rfl)
                  | ok resR =>
                      cases resR with
                      | mk vr resR' =>
                          cases resR' with
                          | mk srcR f₂ =>
                      rw [hRhs] at hNoFault
                      dsimp only at hNoFault
                      cases hBin : evalBinOp op vl vr with
                      | error k =>
                          rw [hBin] at hNoFault
                          cases hClL : OpenMirTy.toClosedMirTy? srcL <;>
                          cases hClR : OpenMirTy.toClosedMirTy? srcR <;>
                          cases hClD : OpenMirTy.toClosedMirTy?
                              (normalizeOpenTy prog.traitRegistry normFuel
                                dstTy) <;>
                          exact False.elim (by
                            rw [hClL, hClR, hClD] at hNoFault
                            exact hNoFault k rfl)
                      | ok resV =>
                          rw [hBin] at hNoFault
                          cases hClL : OpenMirTy.toClosedMirTy? srcL with
                          | none =>
                              rw [hClL] at hNoFault
                              exact False.elim (hNoFault .unsupported rfl)
                          | some ml =>
                              rw [hClL] at hNoFault
                              cases hClR : OpenMirTy.toClosedMirTy? srcR with
                              | none =>
                                  rw [hClR] at hNoFault
                                  exact False.elim (hNoFault .unsupported rfl)
                              | some mr =>
                                  rw [hClR] at hNoFault
                                  cases hClD : OpenMirTy.toClosedMirTy?
                                      (normalizeOpenTy prog.traitRegistry normFuel
                                        dstTy) with
                                  | none =>
                                      rw [hClD] at hNoFault
                                      exact False.elim
                                        (hNoFault .unsupported rfl)
                                  | some mDst =>
                                      rw [hClD] at hNoFault
                                      dsimp only at hNoFault
                                      cases hBad : (!isPrimitiveReadableTy ml ||
                                          !isPrimitiveReadableTy mr ||
                                          !checkVal resV mDst) with
                                      | true =>
                                          rw [ite_cond_true hBad] at hNoFault
                                          exact False.elim
                                            (hNoFault .unsupported rfl)
                                      | false =>
                                          rw [ite_cond_false hBad] at hNoFault
                                          have hPrimL : isPrimitiveReadableTy ml =
                                              true :=
                                            not_bool_eq_false (bool_or_eq_false_left
                                              (bool_or_eq_false_left hBad))
                                          have hPrimR : isPrimitiveReadableTy mr =
                                              true :=
                                            not_bool_eq_false
                                              (bool_or_eq_false_right
                                                (bool_or_eq_false_left hBad))
                                          have hChkRes : checkVal resV mDst =
                                              true :=
                                            not_bool_eq_false
                                              (bool_or_eq_false_right hBad)
                                          cases hW : writeOpenPlace
                                              (entryOpenProgForBody prog defId)
                                              env' ob f₂ dst resV with
                                          | error k =>
                                              rw [hW] at hNoFault
                                              exact False.elim (hNoFault k rfl)
                                          | ok f₃ =>
                                              have hLhs' : evalOpenOperand prog env' ob
                                                  of_ lhs =
                                                  .ok (vl, srcL, f₁) := by
                                                rw [← evalOpenOperand_entryOpenProgForBody prog defId]
                                                exact hLhs
                                              have hRhs' : evalOpenOperand prog env' ob
                                                  f₁ rhs =
                                                  .ok (vr, srcR, f₂) := by
                                                rw [← evalOpenOperand_entryOpenProgForBody prog defId]
                                                exact hRhs
                                              have hW' : writeOpenPlace prog env' ob
                                                  f₂ dst resV = .ok f₃ := by
                                                rw [← writeOpenPlace_entryOpenProgForBody prog defId]
                                                exact hW
                                              have hLSim := evalOpenOperand_prim_sim
                                                prog
                                                env' hRegWf σ ob df.locals of_
                                                hLRel lhs vl srcL f₁ ml
                                                isPrimitiveReadableTy hLhs' hClL
                                                hPrimL
                                              let ⟨hl1, hl2, _, hl4, dfLocs₁,
                                                hSlotL, hRel₁⟩ := hLSim
                                              have hRSim := evalOpenOperand_prim_sim
                                                prog
                                                env' hRegWf σ ob dfLocs₁ f₁
                                                hRel₁ rhs vr srcR f₂ mr
                                                isPrimitiveReadableTy hRhs' hClR
                                                hPrimR
                                              let ⟨hr1, hr2, _, hr4, dfLocs₂,
                                                hSlotR, hRel₂⟩ := hRSim
                                              have hErD : erasedTy prog σ dstTy =
                                                  mDst :=
                                                erasedTy_of_normClosed prog hRegWf
                                                  σ hClD
                                              have hVRes : ValRel
                                                  (erasedTy prog σ dstTy) resV
                                                  resV := by
                                                rw [hErD]; exact ⟨hChkRes, .inl rfl⟩
                                              have hWSim := writePlace_sim
                                                prog
                                                env' σ ob dfLocs₂ f₂ dst dstTy
                                                resV resV f₃ hRel₂ hDst hW' hVRes
                                              let ⟨hw1, hw2, _, hw4, dfLocs₃,
                                                hWPlace, hRel₃⟩ := hWSim
                                              have hStmtD : evalStatement erasedOb
                                                  df entryMemory ⟨[]⟩
                                                  (eraseOpenStatementKind
                                                    (OpenStatementKind.subst
                                                      prog.traitRegistry normFuel σ
                                                      (.assign dst
                                                        (.binaryOp op lhs rhs)))) =
                                                  .step {
                                                    frames := [{ df with
                                                      stmtIdx := df.stmtIdx + 1
                                                      locals := dfLocs₃ }]
                                                    callerMem := ⟨[]⟩
                                                    mem := entryMemory } := by
                                                dsimp only [OpenStatementKind.subst,
                                                  eraseOpenStatementKind,
                                                  OpenPlace.subst, eraseOpenPlace,
                                                  OpenRvalue.subst,
                                                  eraseOpenRvalue, evalStatement]
                                                rw [hProjNil]
                                                dsimp only [List.map, List.isEmpty]
                                                rw [ite_cond_false
                                                  (rfl : (!true) = false), hDstD]
                                                dsimp only [evalRvalue,
                                                  evalPrimitiveOperand]
                                                rw [hParts.1,
                                                  map_substAndNormalize_eq_erasedTy,
                                                  hSlotL]
                                                dsimp only
                                                rw [ite_not_true hPrimL]
                                                dsimp only
                                                rw [hSlotR]
                                                dsimp only
                                                rw [ite_not_true hPrimR]
                                                dsimp only
                                                rw [hBin]
                                                dsimp only
                                                rw [hWPlace]
                                              rw [hStmtD]
                                              refine ⟨(fun k hk => by cases hk),
                                                fun ds' hS => ?_⟩
                                              cases hS
                                              refine ⟨{ os with frames := [{ f₃ with
                                                  stmtIdx := of_.stmtIdx + 1 }] },
                                                ?_, ?_⟩
                                              · rw [hDet, ite_not_true hEmp, hDst]
                                                dsimp only
                                                rw [hLhs]
                                                dsimp only
                                                rw [hRhs]
                                                dsimp only
                                                rw [hClL, hClR, hClD, hBin]
                                                dsimp only
                                                rw [ite_cond_false hBad]
                                                rw [hW]
                                              · exact ⟨{ df with
                                                    stmtIdx := df.stmtIdx + 1,
                                                    locals := dfLocs₃ },
                                                  { f₃ with
                                                    stmtIdx := of_.stmtIdx + 1 },
                                                  rfl, rfl, hDDef,
                                                  hw1.trans (hr1.trans
                                                    (hl1.trans hODef)),
                                                  by dsimp only; rw [hBlk, hw2, hr2, hl2],
                                                  by dsimp only; rw [hStmtIdx],
                                                  hw4.trans (hr4.trans
                                                    (hl4.trans hRet)),
                                                  rfl, hOCM, rfl, hOMem, hRel₃⟩
          | unaryOp op opnd =>
              dsimp only at hNoFault
              cases hOpnd : evalOpenOperand (entryOpenProgForBody prog defId) env'
                  ob of_ opnd with
              | error k => rw [hOpnd] at hNoFault; exact False.elim (hNoFault k rfl)
              | ok resOp =>
                  cases resOp with
                  | mk v resOp' =>
                      cases resOp' with
                      | mk srcTy f₁ =>
                  rw [hOpnd] at hNoFault
                  dsimp only at hNoFault
                  cases hUn : evalUnOp op v with
                  | error k =>
                      rw [hUn] at hNoFault
                      cases hClS : OpenMirTy.toClosedMirTy? srcTy <;>
                      cases hClD : OpenMirTy.toClosedMirTy?
                          (normalizeOpenTy prog.traitRegistry normFuel dstTy) <;>
                      exact False.elim (by
                        rw [hClS, hClD] at hNoFault
                        exact hNoFault k rfl)
                  | ok resV =>
                      rw [hUn] at hNoFault
                      cases hClS : OpenMirTy.toClosedMirTy? srcTy with
                      | none =>
                          rw [hClS] at hNoFault
                          exact False.elim (hNoFault .unsupported rfl)
                      | some mSrc =>
                          rw [hClS] at hNoFault
                          cases hClD : OpenMirTy.toClosedMirTy?
                              (normalizeOpenTy prog.traitRegistry normFuel dstTy) with
                          | none =>
                              rw [hClD] at hNoFault
                              exact False.elim (hNoFault .unsupported rfl)
                          | some mDst =>
                              rw [hClD] at hNoFault
                              dsimp only at hNoFault
                              cases hBad : (!isPrimitiveReadableTy mSrc ||
                                  !checkVal resV mDst) with
                              | true =>
                                  rw [ite_cond_true hBad] at hNoFault
                                  exact False.elim (hNoFault .unsupported rfl)
                              | false =>
                                  rw [ite_cond_false hBad] at hNoFault
                                  have hPrimS : isPrimitiveReadableTy mSrc = true :=
                                    not_bool_eq_false (bool_or_eq_false_left hBad)
                                  have hChkRes : checkVal resV mDst = true :=
                                    not_bool_eq_false (bool_or_eq_false_right hBad)
                                  cases hW : writeOpenPlace
                                      (entryOpenProgForBody prog defId) env' ob f₁
                                      dst resV with
                                  | error k =>
                                      rw [hW] at hNoFault
                                      exact False.elim (hNoFault k rfl)
                                  | ok f₂ =>
                                      have hOpnd' : evalOpenOperand prog env' ob
                                          of_ opnd = .ok (v, srcTy, f₁) := by
                                        rw [← evalOpenOperand_entryOpenProgForBody prog defId]
                                        exact hOpnd
                                      have hW' : writeOpenPlace prog env' ob f₁
                                          dst resV = .ok f₂ := by
                                        rw [← writeOpenPlace_entryOpenProgForBody prog defId]
                                        exact hW
                                      have hSim := evalOpenOperand_prim_sim
                                        prog env'
                                        hRegWf σ ob df.locals of_ hLRel opnd v
                                        srcTy f₁ mSrc isPrimitiveReadableTy hOpnd'
                                        hClS hPrimS
                                      let ⟨hs1, hs2, _, hs4, dfLocs₁, hSlotS,
                                        hRel₁⟩ := hSim
                                      have hErD : erasedTy prog σ dstTy = mDst :=
                                        erasedTy_of_normClosed prog hRegWf σ hClD
                                      have hVRes : ValRel
                                          (erasedTy prog σ dstTy) resV resV := by
                                        rw [hErD]; exact ⟨hChkRes, .inl rfl⟩
                                      have hWSim := writePlace_sim
                                        prog env' σ
                                        ob dfLocs₁ f₁ dst dstTy resV resV f₂ hRel₁
                                        hDst hW' hVRes
                                      let ⟨hw1, hw2, _, hw4, dfLocs₂, hWPlace,
                                        hRel₂⟩ := hWSim
                                      have hStmtD : evalStatement erasedOb df
                                          entryMemory ⟨[]⟩
                                          (eraseOpenStatementKind
                                            (OpenStatementKind.subst
                                              prog.traitRegistry normFuel σ
                                              (.assign dst
                                                (.unaryOp op opnd)))) =
                                          .step {
                                            frames := [{ df with
                                              stmtIdx := df.stmtIdx + 1
                                              locals := dfLocs₂ }]
                                            callerMem := ⟨[]⟩
                                            mem := entryMemory } := by
                                        dsimp only [OpenStatementKind.subst,
                                          eraseOpenStatementKind, OpenPlace.subst,
                                          eraseOpenPlace, OpenRvalue.subst,
                                          eraseOpenRvalue, evalStatement]
                                        rw [hProjNil]
                                        dsimp only [List.map, List.isEmpty]
                                        rw [ite_cond_false
                                          (rfl : (!true) = false), hDstD]
                                        dsimp only [evalRvalue,
                                          evalPrimitiveOperand]
                                        rw [hParts.1,
                                          map_substAndNormalize_eq_erasedTy,
                                          hSlotS]
                                        dsimp only
                                        rw [ite_not_true hPrimS]
                                        dsimp only
                                        rw [hUn]
                                        dsimp only
                                        rw [hWPlace]
                                      rw [hStmtD]
                                      refine ⟨(fun k hk => by cases hk),
                                        fun ds' hS => ?_⟩
                                      cases hS
                                      refine ⟨{ os with frames := [{ f₂ with
                                          stmtIdx := of_.stmtIdx + 1 }] }, ?_, ?_⟩
                                      · rw [hDet, ite_not_true hEmp, hDst]
                                        dsimp only
                                        rw [hOpnd]
                                        dsimp only
                                        rw [hClS, hClD, hUn]
                                        dsimp only
                                        rw [ite_cond_false hBad]
                                        rw [hW]
                                      · exact ⟨{ df with
                                            stmtIdx := df.stmtIdx + 1,
                                            locals := dfLocs₂ },
                                          { f₂ with stmtIdx := of_.stmtIdx + 1 },
                                          rfl, rfl, hDDef,
                                          hw1.trans (hs1.trans hODef),
                                          by dsimp only; rw [hBlk, hw2, hs2],
                                          by dsimp only; rw [hStmtIdx],
                                          hw4.trans (hs4.trans hRet), rfl, hOCM,
                                          rfl, hOMem, hRel₂⟩
          | cast kind opnd castTy =>
              cases kind with
              | unsupported | ptrToPtr | intToPtr | unsize | boxAsRef =>
                  exact False.elim (hNoFault .unsupported rfl)
              | intToInt =>
                  dsimp only at hNoFault
                  cases hBeq : OpenMirTy.beq
                      (normalizeOpenTy prog.traitRegistry normFuel castTy)
                      (normalizeOpenTy prog.traitRegistry normFuel dstTy) with
                  | false =>
                      rw [ite_not_false hBeq] at hNoFault
                      exact False.elim (hNoFault .unsupported rfl)
                  | true =>
                      rw [ite_not_true hBeq] at hNoFault
                      have hCastEq := openMirTy_beq_eq hBeq
                      cases hOpnd : evalOpenOperand
                          (entryOpenProgForBody prog defId) env' ob of_ opnd
                          with
                      | error k =>
                          rw [hOpnd] at hNoFault
                          exact False.elim (hNoFault k rfl)
                      | ok resOp =>
                          cases resOp with
                          | mk v resOp' =>
                              cases resOp' with
                              | mk srcTy f₁ =>
                          rw [hOpnd] at hNoFault
                          cases hClC : OpenMirTy.toClosedMirTy?
                              (normalizeOpenTy prog.traitRegistry normFuel castTy)
                              with
                          | none =>
                              rw [hClC] at hNoFault
                              exact False.elim (hNoFault .unsupported rfl)
                          | some mCast =>
                              rw [hClC] at hNoFault
                              dsimp only at hNoFault
                              cases hClS : OpenMirTy.toClosedMirTy? srcTy with
                              | none =>
                                  rw [hClS] at hNoFault
                                  exact False.elim (hNoFault .unsupported rfl)
                              | some mSrc =>
                                  rw [hClS] at hNoFault
                                  dsimp only at hNoFault
                                  cases hInt : isIntLikeTy mSrc with
                                  | false =>
                                      rw [ite_not_false hInt] at hNoFault
                                      exact False.elim
                                        (hNoFault .unsupported rfl)
                                  | true =>
                                      rw [ite_not_true hInt] at hNoFault
                                      cases hCast : evalIntToIntCast v mCast with
                                      | error k =>
                                          rw [hCast] at hNoFault
                                          exact False.elim (hNoFault k rfl)
                                      | ok resV =>
                                          rw [hCast] at hNoFault
                                          dsimp only at hNoFault
                                          cases hW : writeOpenPlace
                                              (entryOpenProgForBody prog defId)
                                              env' ob f₁ dst resV with
                                          | error k =>
                                              rw [hW] at hNoFault
                                              exact False.elim (hNoFault k rfl)
                                          | ok f₂ =>
                                              have hOpnd' : evalOpenOperand prog
                                                  env' ob of_ opnd =
                                                  .ok (v, srcTy, f₁) := by
                                                rw [← evalOpenOperand_entryOpenProgForBody prog defId]
                                                exact hOpnd
                                              have hW' : writeOpenPlace prog env'
                                                  ob f₁ dst resV = .ok f₂ := by
                                                rw [← writeOpenPlace_entryOpenProgForBody prog defId]
                                                exact hW
                                              have hSim := evalOpenOperand_prim_sim
                                                prog
                                                env' hRegWf σ ob df.locals of_
                                                hLRel opnd v srcTy f₁ mSrc
                                                isIntLikeTy hOpnd' hClS
                                                (isIntLikeTy_to_prim hInt)
                                              let ⟨hs1, hs2, _, hs4, dfLocs₁,
                                                hSlotS, hRel₁⟩ := hSim
                                              have hErC : erasedTy prog σ castTy =
                                                  mCast :=
                                                erasedTy_of_normClosed prog hRegWf
                                                  σ hClC
                                              have hClD : OpenMirTy.toClosedMirTy?
                                                  (normalizeOpenTy prog.traitRegistry
                                                    normFuel dstTy) =
                                                  some mCast := by
                                                rw [← hCastEq]; exact hClC
                                              have hErD : erasedTy prog σ dstTy =
                                                  mCast :=
                                                erasedTy_of_normClosed prog hRegWf
                                                  σ hClD
                                              have hChkRes :=
                                                evalIntToIntCast_checkVal v mCast
                                                  resV hCast
                                              have hVRes : ValRel
                                                  (erasedTy prog σ dstTy) resV
                                                  resV := by
                                                rw [hErD]; exact ⟨hChkRes, .inl rfl⟩
                                              have hWSim := writePlace_sim
                                                prog
                                                env' σ ob dfLocs₁ f₁ dst dstTy
                                                resV resV f₂ hRel₁ hDst hW' hVRes
                                              let ⟨hw1, hw2, _, hw4, dfLocs₂,
                                                hWPlace, hRel₂⟩ := hWSim
                                              have hStmtD : evalStatement erasedOb
                                                  df entryMemory ⟨[]⟩
                                                  (eraseOpenStatementKind
                                                    (OpenStatementKind.subst
                                                      prog.traitRegistry normFuel σ
                                                      (.assign dst
                                                        (.cast .intToInt opnd
                                                          castTy)))) =
                                                  .step {
                                                    frames := [{ df with
                                                      stmtIdx := df.stmtIdx + 1
                                                      locals := dfLocs₂ }]
                                                    callerMem := ⟨[]⟩
                                                    mem := entryMemory } := by
                                                dsimp only [OpenStatementKind.subst,
                                                  eraseOpenStatementKind,
                                                  OpenPlace.subst, eraseOpenPlace,
                                                  OpenRvalue.subst,
                                                  eraseOpenRvalue, evalStatement]
                                                rw [hProjNil]
                                                dsimp only [List.map, List.isEmpty]
                                                rw [ite_cond_false
                                                  (rfl : (!true) = false), hDstD]
                                                dsimp only [evalRvalue]
                                                rw [hParts.1,
                                                  map_substAndNormalize_eq_erasedTy,
                                                  hSlotS]
                                                dsimp only
                                                rw [ite_not_true hInt]
                                                unfold erasedTy at hErC
                                                rw [hErC, hCast]
                                                dsimp only
                                                rw [hWPlace]
                                              rw [hStmtD]
                                              refine ⟨(fun k hk => by cases hk),
                                                fun ds' hS => ?_⟩
                                              cases hS
                                              refine ⟨{ os with frames := [{ f₂ with
                                                  stmtIdx := of_.stmtIdx + 1 }] },
                                                ?_, ?_⟩
                                              · rw [hDet, ite_not_true hEmp, hDst]
                                                dsimp only
                                                rw [ite_not_true hBeq]
                                                rw [hOpnd, hClC]
                                                dsimp only
                                                rw [hClS]
                                                dsimp only
                                                rw [ite_not_true hInt]
                                                rw [hCast]
                                                dsimp only
                                                rw [hW]
                                              · exact ⟨{ df with
                                                    stmtIdx := df.stmtIdx + 1,
                                                    locals := dfLocs₂ },
                                                  { f₂ with
                                                    stmtIdx := of_.stmtIdx + 1 },
                                                  rfl, rfl, hDDef,
                                                  hw1.trans (hs1.trans hODef),
                                                  by dsimp only; rw [hBlk, hw2, hs2],
                                                  by dsimp only; rw [hStmtIdx],
                                                  hw4.trans (hs4.trans hRet), rfl,
                                                  hOCM, rfl, hOMem, hRel₂⟩

private theorem openStep_sim (prog : OpenProgram)
    (hRegWf : TraitRegistryWf prog.traitRegistry = true)
    (env : OpenExecEnv) (σ : List OpenMirTy) (paramSpecs : List TypeLayoutSpec)
    (hLenEq : paramSpecs.length = σ.length)
    (hMap : ∀ (i : Nat) (ty : OpenMirTy), openListGet? σ i = some ty →
      ∃ sp : TypeLayoutSpec, openListGet? paramSpecs i = some sp ∧
        evalOpenTySpec prog.traitRegistry normFuel
          { env.typeSpecs with paramSpecs := [], paramInvs := [] } ty =
          some sp ∧
        OpenMirTy.isClosed ty = true)
    (defId : DefId) (ob : OpenBody) (erasedOb : Body)
    (hObEq : OpenBody.toDay1? (OpenBody.subst prog.traitRegistry normFuel σ ob) =
      some erasedOb)
    (hAdm : openLocalsAdmitted prog
      { env with typeSpecs := (substTypeSpecEnv env.typeSpecs paramSpecs
          (List.replicate paramSpecs.length (fun _ => True))
          (instAssocSpecs prog.traitRegistry env.typeSpecs σ)) } ob.locals)
    (hSupp : erasedOb.locals.all isSupportedScalarOrUnitTy = true)
    (hGet : openListGet? prog.bodies defId = some ob)
    (hGetErased : Trusted.MirSemantics.getElem?
      (eraseOpenProgram σ prog).bodies defId = some erasedOb)
    (hErasable : openBodyIsDay1Erasable ob = true)
    (hArgLt : Nat.blt ob.argumentCount ob.locals.length = true)
    (hNone : OpenProgram.toDay1? (entryOpenProgForBody prog defId) = none)
    (ds : State) (os : OpenState)
    (hRel : StateRel prog σ defId ob ds os)
    (hNoFault : ∀ k, ¬ OpenStep (entryOpenProgForBody prog defId)
      { env with typeSpecs := (substTypeSpecEnv env.typeSpecs paramSpecs
          (List.replicate paramSpecs.length (fun _ => True))
          (instAssocSpecs prog.traitRegistry env.typeSpecs σ)) }
      ob.sig.whereClauses os (.fault k))
    (hDSys : ∃ f : FrameState, ds.frames = [f] ∧ f.sysrootOp? = none) :
    (∀ k, evalStep (entryProgForBody (eraseOpenProgram σ prog) defId) 0 ds ≠
      .fault k) ∧
    (∀ ds', evalStep (entryProgForBody (eraseOpenProgram σ prog) defId) 0 ds =
      .step ds' →
      ∃ os',
        OpenStep (entryOpenProgForBody prog defId)
          { env with typeSpecs := (substTypeSpecEnv env.typeSpecs paramSpecs
              (List.replicate paramSpecs.length (fun _ => True))
              (instAssocSpecs prog.traitRegistry env.typeSpecs σ)) }
          ob.sig.whereClauses os (.step os') ∧
        StateRel prog σ defId ob ds' os') := by
  let env' : OpenExecEnv :=
    { env with typeSpecs := (substTypeSpecEnv env.typeSpecs paramSpecs
        (List.replicate paramSpecs.length (fun _ => True))
        (instAssocSpecs prog.traitRegistry env.typeSpecs σ)) }
  let ⟨df, of_, hDF, hOF, hDDef, hODef, hBlk, hStmtIdx, hRet,
    hDCM, hOCM, hDMem, hOMem, hLRel⟩ := hRel
  have hDfSys : df.sysrootOp? = none := by
    let ⟨f0, hF0, hS0⟩ := hDSys
    rw [hDF] at hF0
    injection hF0 with hEq _
    rw [hEq]
    exact hS0
  have hParts := erasedOb_locals_eq_map prog σ ob erasedOb hObEq
  cases hBb : openListGet? ob.basicBlocks of_.blockIdx with
  | none =>
      have hOFault : OpenStep (entryOpenProgForBody prog defId) env'
          ob.sig.whereClauses os (.fault .unsupported) := by
        unfold OpenStep OpenStepOnFrames
        rw [hOF]
        dsimp only [OpenStepOnBodyOpt, entryOpenProgForBody]
        rw [hODef, hGet]
        dsimp only [OpenStepOnBlockOpt]
        rw [hBb]
      exact False.elim (hNoFault .unsupported hOFault)
  | some bb =>
      have hStepIff := openStep_eq_det_none prog env' ob.sig.whereClauses defId
        ob hNone hGet hErasable os of_ bb hOF hODef hBb
      have hNoFaultDet : ∀ k, openEvalDetStep (entryOpenProgForBody prog defId)
          env' os ≠ .fault k := by
        intro k hk
        exact hNoFault k ((hStepIff (.fault k)).mpr hk.symm)
      have hBbD : Trusted.MirSemantics.getElem? erasedOb.basicBlocks df.blockIdx =
          some (eraseOpenBasicBlock
            (OpenBasicBlock.subst prog.traitRegistry normFuel σ bb)) := by
        rw [hParts.2.2, mirGetElem?_map, mirGetElem?_map,
          getElem?_eq_openListGet?, hBlk, hBb]
        rfl
      have hStmtsLen : (eraseOpenBasicBlock
          (OpenBasicBlock.subst prog.traitRegistry normFuel σ bb)).statements.length
          = bb.statements.length := by
        dsimp only [eraseOpenBasicBlock, OpenBasicBlock.subst]
        rw [length_map_eq, length_map_eq]
      cases hStmt : openListGet? bb.statements of_.stmtIdx with
      | none =>
          cases hAtEnd : Nat.beq of_.stmtIdx bb.statements.length with
          | false =>
              have hDetF : openEvalDetStep (entryOpenProgForBody prog defId)
                  env' os = .fault .unsupported := by
                unfold openEvalDetStep openEvalDetStepAux
                rw [hNone, hOF]
                dsimp only
                rw [hODef]
                dsimp only [entryOpenProgForBody]
                rw [hGet]
                dsimp only
                rw [hBb]
                dsimp only
                rw [hStmt]
                dsimp only
                rw [ite_not_false hAtEnd]
              exact False.elim (hNoFaultDet .unsupported hDetF)
          | true =>
              have hTermSim := openStep_term_sim prog hRegWf env' σ defId ob
                erasedOb hObEq hGet hErasable hNone hArgLt ds os df of_ bb hDF
                hOF hDDef hODef hBlk hStmtIdx hRet hDCM hOCM hDMem hOMem hLRel
                hBb hAtEnd hNoFaultDet
              have hStmtD : Trusted.MirSemantics.getElem?
                  (eraseOpenBasicBlock
                    (OpenBasicBlock.subst prog.traitRegistry normFuel σ bb)).statements
                  df.stmtIdx = none := by
                dsimp only [eraseOpenBasicBlock, OpenBasicBlock.subst]
                rw [mirGetElem?_map, mirGetElem?_map, getElem?_eq_openListGet?,
                  hStmtIdx, hStmt]
                rfl
              have hEvStep : evalStep
                  (entryProgForBody (eraseOpenProgram σ prog) defId) 0 ds =
                  evalTerminator erasedOb
                    (eraseOpenBasicBlock
                      (OpenBasicBlock.subst prog.traitRegistry normFuel σ bb))
                    df entryMemory ⟨[]⟩ := by
                unfold evalStep
                rw [hDF]
                dsimp only [activeFrameBody]
                rw [hDfSys]
                dsimp only
                rw [hDDef]
                dsimp only [entryProgForBody]
                rw [hGetErased]
                dsimp only
                rw [hBbD]
                dsimp only
                rw [hStmtD, hStmtsLen, hStmtIdx, ite_cond_true hAtEnd, hDMem,
                  hDCM]
                have hNoT := basicBlocks_noCall_term
                  (openBody_toDay1_noCall _ erasedOb hObEq) hBbD
                cases hTm : (eraseOpenBasicBlock (OpenBasicBlock.subst
                    prog.traitRegistry normFuel σ bb)).terminator <;>
                  first
                  | rfl
                  | (rw [hTm] at hNoT; cases hNoT)
              rw [hEvStep]
              refine ⟨hTermSim.1, fun ds' hS => ?_⟩
              let ⟨os', hDetS, hRel'⟩ := hTermSim.2 ds' hS
              exact ⟨os', (hStepIff (.step os')).mpr hDetS.symm, hRel'⟩
      | some stmt =>
          have hStmtD : Trusted.MirSemantics.getElem?
              (eraseOpenBasicBlock
                (OpenBasicBlock.subst prog.traitRegistry normFuel σ bb)).statements
              df.stmtIdx = some (eraseOpenStatementKind
                (OpenStatementKind.subst prog.traitRegistry normFuel σ stmt)) := by
            dsimp only [eraseOpenBasicBlock, OpenBasicBlock.subst]
            rw [mirGetElem?_map, mirGetElem?_map, getElem?_eq_openListGet?,
              hStmtIdx, hStmt]
            rfl
          have hEvStep : evalStep
              (entryProgForBody (eraseOpenProgram σ prog) defId) 0 ds =
              evalStatement erasedOb df entryMemory ⟨[]⟩
                (eraseOpenStatementKind
                  (OpenStatementKind.subst prog.traitRegistry normFuel σ stmt)) := by
            unfold evalStep
            rw [hDF]
            dsimp only [activeFrameBody]
            rw [hDfSys]
            dsimp only
            rw [hDDef]
            dsimp only [entryProgForBody]
            rw [hGetErased]
            dsimp only
            rw [hBbD]
            dsimp only
            rw [hStmtD, hDMem, hDCM]
            rfl
          rw [hEvStep]
          cases stmt with
          | nop =>
              have hDetNop : openEvalDetStep (entryOpenProgForBody prog defId)
                  env' os = .step { os with frames :=
                    [{ of_ with stmtIdx := of_.stmtIdx + 1 }] } := by
                unfold openEvalDetStep openEvalDetStepAux
                rw [hNone, hOF]
                dsimp only
                rw [hODef]
                dsimp only [entryOpenProgForBody]
                rw [hGet]
                dsimp only
                rw [hBb]
                dsimp only
                rw [hStmt]
              dsimp only [OpenStatementKind.subst, eraseOpenStatementKind,
                evalStatement]
              refine ⟨(fun k hk => by cases hk), fun ds' hS => ?_⟩
              cases hS
              exact ⟨_, (hStepIff (.step _)).mpr hDetNop.symm,
                ⟨{ df with stmtIdx := df.stmtIdx + 1 },
                  { of_ with stmtIdx := of_.stmtIdx + 1 }, rfl, rfl, hDDef, hODef,
                  hBlk, by dsimp only; rw [hStmtIdx], hRet, rfl, hOCM, rfl, hOMem,
                  hLRel⟩⟩
          | unsupported =>
              have hDetU : openEvalDetStep (entryOpenProgForBody prog defId)
                  env' os = .fault .unsupported := by
                unfold openEvalDetStep openEvalDetStepAux
                rw [hNone, hOF]
                dsimp only
                rw [hODef]
                dsimp only [entryOpenProgForBody]
                rw [hGet]
                dsimp only
                rw [hBb]
                dsimp only
                rw [hStmt]
              exact False.elim (hNoFaultDet .unsupported hDetU)
          | storageLive lid =>
              have hGetEP :
                  openListGet? (entryOpenProgForBody prog defId).bodies
                    of_.defId = some ob := hODef.symm ▸ hGet
              have hDetSL : openEvalDetStep (entryOpenProgForBody prog defId)
                  env' os =
                  match openListGet? ob.locals lid,
                        Trusted.MirSemantics.getElem? of_.locals lid with
                  | some ty, some old =>
                      match setElem? of_.locals lid
                              (openLiveUninitSlot prog ty) with
                      | some ls' =>
                          match deallocateLocal os.mem old with
                          | .error k => .fault k
                          | .ok mem' =>
                              .step { os with
                                frames := [{ of_ with
                                  stmtIdx := of_.stmtIdx + 1, locals := ls' }]
                                mem := mem' }
                      | none => .fault .unsupported
                  | _, _ => .fault .unsupported := by
                unfold openEvalDetStep openEvalDetStepAux
                rw [hNone, hOF]
                dsimp only
                rw [hGetEP]
                dsimp only
                rw [hBb]
                dsimp only
                rw [hStmt]
                dsimp only
                simp only [openLiveUninitSlot_entryOpenProgForBody]
                cases openListGet? ob.locals lid with
                | none => rfl
                | some ty =>
                    cases Trusted.MirSemantics.getElem? of_.locals lid with
                    | none => rfl
                    | some old =>
                        cases setElem? of_.locals lid
                            (openLiveUninitSlot prog ty) with
                        | none => rfl
                        | some ls' =>
                            cases deallocateLocal os.mem old <;> rfl
              rw [hDetSL] at hNoFaultDet
              cases localsRel_getElem? prog σ lid hLRel with
              | inl hNone =>
                  rw [hNone.1] at hNoFaultDet
                  exact False.elim (hNoFaultDet .unsupported rfl)
              | inr hSome =>
                  let ⟨ty, sd, so, hG1, hG2, hG3, hSlot⟩ := hSome
                  let ⟨dfLocs', ofLocs', hSetD, hSetO, hRel'⟩ :=
                    localsRel_setElem? prog σ lid hLRel hG1
                      (openLiveUninitSlot_slotRel prog hRegWf σ ty)
                  have hDeallocD : deallocateLocal entryMemory sd =
                      .ok entryMemory :=
                    deallocateLocal_empty (slotRel_not_indirect hSlot).1
                  have hDeallocO : deallocateLocal os.mem so = .ok os.mem :=
                    deallocateLocal_empty (slotRel_not_indirect hSlot).2
                  have hDetStep : openEvalDetStep (entryOpenProgForBody prog defId)
                      env' os = .step { os with
                        frames := [{ of_ with
                          stmtIdx := of_.stmtIdx + 1, locals := ofLocs' }] } := by
                    rw [hDetSL, hG1, hG3]
                    dsimp only
                    rw [hSetO]
                    dsimp only
                    rw [hDeallocO]
                  have hGD : Trusted.MirSemantics.getElem? erasedOb.locals lid =
                      some (erasedTy prog σ ty) := by
                    rw [hParts.1, mirGetElem?_map, getElem?_eq_openListGet?, hG1]
                    rfl
                  dsimp only [OpenStatementKind.subst, eraseOpenStatementKind,
                    evalStatement]
                  rw [hGD, hG2]
                  dsimp only
                  rw [hSetD]
                  dsimp only
                  rw [hDeallocD]
                  refine ⟨(fun k hk => by cases hk), fun ds' hS => ?_⟩
                  cases hS
                  exact ⟨_, (hStepIff (.step _)).mpr hDetStep.symm,
                    ⟨{ df with stmtIdx := df.stmtIdx + 1, locals := dfLocs' },
                      { of_ with stmtIdx := of_.stmtIdx + 1, locals := ofLocs' },
                      rfl, rfl, hDDef, hODef, hBlk, by dsimp only; rw [hStmtIdx],
                      hRet, rfl, hOCM, rfl, hOMem, hRel'⟩⟩
          | storageDead lid =>
              have hGetEP :
                  openListGet? (entryOpenProgForBody prog defId).bodies
                    of_.defId = some ob := hODef.symm ▸ hGet
              have hDetSD : openEvalDetStep (entryOpenProgForBody prog defId)
                  env' os =
                  if Nat.beq lid 0 then .fault .unsupported
                  else match Trusted.MirSemantics.getElem? of_.locals lid with
                    | none => .fault .unsupported
                    | some old =>
                        match setElem? of_.locals lid .dead with
                        | some ls' =>
                            match deallocateLocal os.mem old with
                            | .error k => .fault k
                            | .ok mem' =>
                                .step { os with
                                  frames := [{ of_ with
                                    stmtIdx := of_.stmtIdx + 1, locals := ls' }]
                                  mem := mem' }
                        | none => .fault .unsupported := by
                unfold openEvalDetStep openEvalDetStepAux
                rw [hNone, hOF]
                dsimp only
                rw [hGetEP]
                dsimp only
                rw [hBb]
                dsimp only
                rw [hStmt]
                dsimp only
                cases Nat.beq lid 0 with
                | true => rfl
                | false =>
                    cases Trusted.MirSemantics.getElem? of_.locals lid with
                    | none => rfl
                    | some old =>
                        cases setElem? of_.locals lid .dead with
                        | none => rfl
                        | some ls' =>
                            cases deallocateLocal os.mem old <;> rfl
              rw [hDetSD] at hNoFaultDet
              cases hZero : Nat.beq lid 0 with
              | true =>
                  rw [ite_cond_true hZero] at hNoFaultDet
                  exact False.elim (hNoFaultDet .unsupported rfl)
              | false =>
                  rw [ite_cond_false hZero] at hNoFaultDet
                  cases localsRel_getElem? prog σ lid hLRel with
                  | inl hNone =>
                      rw [hNone.2.2] at hNoFaultDet
                      exact False.elim (hNoFaultDet .unsupported rfl)
                  | inr hSome =>
                      let ⟨ty, sd, so, hG1, hG2, hG3, hSlot⟩ := hSome
                      let ⟨dfLocs', ofLocs', hSetD, hSetO, hRel'⟩ :=
                        localsRel_setElem? prog σ lid hLRel hG1 (.inl ⟨rfl, rfl⟩)
                      have hDeallocD : deallocateLocal entryMemory sd =
                          .ok entryMemory :=
                        deallocateLocal_empty (slotRel_not_indirect hSlot).1
                      have hDeallocO : deallocateLocal os.mem so = .ok os.mem :=
                        deallocateLocal_empty (slotRel_not_indirect hSlot).2
                      have hDetStep :
                          openEvalDetStep (entryOpenProgForBody prog defId) env'
                            os = .step { os with
                              frames := [{ of_ with
                                stmtIdx := of_.stmtIdx + 1, locals := ofLocs' }] } := by
                        rw [hDetSD, ite_cond_false hZero, hG3]
                        dsimp only
                        rw [hSetO]
                        dsimp only
                        rw [hDeallocO]
                      dsimp only [OpenStatementKind.subst, eraseOpenStatementKind,
                        evalStatement]
                      rw [ite_cond_false hZero, hG2]
                      dsimp only
                      rw [hSetD]
                      dsimp only
                      rw [hDeallocD]
                      refine ⟨(fun k hk => by cases hk), fun ds' hS => ?_⟩
                      cases hS
                      exact ⟨_, (hStepIff (.step _)).mpr hDetStep.symm,
                        ⟨{ df with stmtIdx := df.stmtIdx + 1, locals := dfLocs' },
                          { of_ with stmtIdx := of_.stmtIdx + 1, locals := ofLocs' },
                          rfl, rfl, hDDef, hODef, hBlk, by dsimp only; rw [hStmtIdx],
                          hRet, rfl, hOCM, rfl, hOMem, hRel'⟩⟩
          | assign dst rv =>
              have hAs := openStep_assign_sim prog hRegWf env σ paramSpecs
                hLenEq hMap defId ob erasedOb hObEq hAdm hSupp hGet hNone ds os
                df of_ bb dst rv hDF hOF hDDef hODef hBlk hStmtIdx hRet hDCM hOCM
                hDMem hOMem hLRel hBb hStmt hNoFaultDet
              refine ⟨hAs.1, fun ds' hS => ?_⟩
              let ⟨os', hDetS, hRel'⟩ := hAs.2 ds' hS
              exact ⟨os', (hStepIff (.step os')).mpr hDetS.symm, hRel'⟩

/-- Day-1 `initState` builds one entry frame at `p.entryDefId` with no pinned
`sysrootOp?`. -/
private theorem initState_singleFrame (p : Program) (q : Query) (s : State)
    (h : initState p q = .ok s) :
    ∃ f : FrameState, s.frames = [f] ∧ f.defId = p.entryDefId ∧
      f.sysrootOp? = none := by
  unfold initState at h
  have h := (ite_err_ok h).2
  have h := (ite_err_ok h).2
  cases hB : Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
  | none =>
      rw [hB] at h
      dsimp only at h
      cases h
  | some body =>
      rw [hB] at h
      dsimp only at h
      have h := (ite_err_ok h).2
      have h := (ite_err_ok h).2
      have h := (ite_err_ok h).2
      have h := (ite_err_ok h).2
      have h := (ite_err_ok h).2
      have h := (ite_err_ok h).2
      have h := (ite_err_ok h).2
      have h := (ite_err_ok h).2
      have h := (ite_err_ok h).2
      have h := (ite_err_ok h).2
      cases h
      exact ⟨_, rfl, rfl, rfl⟩

/-- Day-1 executions of a call-free entry body stay in one frame at `defId`
with no pinned `sysrootOp?`. -/
private theorem reaches_singleFrame_noSysroot (p : Program) (defId : DefId)
    (body : Body)
    (hGet : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hNo : bodyHasAnyCall body = false) {s₀ s : State}
    (h0 : ∃ f : FrameState, s₀.frames = [f] ∧ f.defId = defId ∧
      f.sysrootOp? = none)
    (hR : Reaches p s₀ s) :
    ∃ f : FrameState, s.frames = [f] ∧ f.defId = defId ∧
      f.sysrootOp? = none := by
  induction hR with
  | refl => exact h0
  | tail _ hStep ih =>
      let ⟨f, hFs, hD, hS⟩ := ih
      let ⟨_, _, hEv⟩ := hStep
      have hNoCall : ∀ b, activeFrameBody p f = some b →
          bodyHasAnyCall b = false := by
        intro b hb
        unfold activeFrameBody at hb
        rw [hS] at hb
        dsimp only at hb
        rw [hD, hGet] at hb
        injection hb with hb
        subst hb
        exact hNo
      have key : ∀ (m s' : State), m.frames = [f] →
          evalStep p 0 m = .step s' →
          ∃ f' : FrameState, s'.frames = [f'] ∧ f'.defId = defId ∧
            f'.sysrootOp? = none := by
        intro m s' hF hE
        cases m with
        | mk fr cm mem =>
            dsimp only at hF
            subst hF
            let ⟨f', hN, hD', hS'⟩ :=
              evalStep_single_preserves_defId p f mem cm s' hNoCall hE
            exact ⟨f', hN, hD'.trans hD, hS'.trans hS⟩
      exact key _ _ hFs hEv

/-- End-to-end closed-instantiation erasure soundness: proving
`OpenInstantiationErasureClaim eraseOpenBody eraseOpenProgram` via genuine
Day-1 `evalStep` <-> `OpenStep` lockstep simulation with zero trust-bypassing
axioms or caller-supplied `wellFormedTransfer` hypotheses. -/
theorem ClosedInstantiationTransfer :
    OpenInstantiationErasureClaim eraseOpenBody eraseOpenProgram := by
  intro prog env defId ob σ safetyPre concretePre hParam hLen hWfSubst
    hWhereDisch hBounded hObEq hObErasable hGetErased hDay1Adm hPre
  let ⟨paramSpecs', hPsLen, hPsWf', hEvSubst, hMap⟩ :=
    substSpecs_of_allSubstTypesWellFormed prog env σ hWfSubst
  let hMap' : ∀ (i : Nat) (ty : OpenMirTy), openListGet? σ i = some ty →
      ∃ sp : TypeLayoutSpec, openListGet? paramSpecs' i = some sp ∧
        evalOpenTySpec prog.traitRegistry normFuel
          { env.typeSpecs with paramSpecs := [], paramInvs := [] } ty =
          some sp ∧
        OpenMirTy.isClosed ty = true :=
    fun i ty hG =>
      let ⟨sp, hs, he, _, hc⟩ := hMap i ty hG
      ⟨sp, hs, he, hc⟩
  let erasedOb := eraseOpenBody prog.traitRegistry σ ob
  refine ⟨hGetErased, hDay1Adm, fun args hValidEntry hConcretePre => ?_⟩
  let assocSpecFn := instAssocSpecs prog.traitRegistry env.typeSpecs σ
  let env' : OpenExecEnv := instOpenExecEnv prog env σ paramSpecs'
  have hRegWf : TraitRegistryWf prog.traitRegistry = true := hParam.2.1
  have hAdm' : OpenBodyStaticAdmitted prog env' ob :=
    (hParam.2.2.2 paramSpecs'
      (List.replicate paramSpecs'.length (fun _ => True))
      assocSpecFn (Eq.trans hPsLen hLen) hPsWf'
      (replicate_true_paramInvsWf paramSpecs' hPsWf')
      (allWhereParamsSem_of_discharged prog hRegWf env σ paramSpecs' hPsLen
        hMap ob.sig.whereClauses hBounded hWhereDisch)).1
  have hWfs' :=
    (hParam.2.2.2 paramSpecs'
      (List.replicate paramSpecs'.length (fun _ => True))
      assocSpecFn (Eq.trans hPsLen hLen) hPsWf'
      (replicate_true_paramInvsWf paramSpecs' hPsWf')
      (allWhereParamsSem_of_discharged prog hRegWf env σ paramSpecs' hPsLen
        hMap ob.sig.whereClauses hBounded hWhereDisch)).2
  have hSupp : erasedOb.locals.all isSupportedScalarOrUnitTy = true := by
    unfold BodyStaticAdmitted singleBodyStaticAdmitted at hDay1Adm
    exact bool_and_right (bool_and_left (bool_and_left hDay1Adm))
  have hValidOpen : ValidOpenEntryArgs prog env' ob args :=
    validEntryArgs_to_validOpenEntryArgs prog hRegWf env σ paramSpecs' hPsLen
      hMap' ob erasedOb hObEq hAdm'.2.2.2.2.2.2.2.2.2 hSupp args hValidEntry
  have hOWf : OpenWellFormed (entryOpenProgForBody prog defId) env'
      ob.sig.whereClauses { args := args } :=
    hWfs' args hValidOpen (fun hUnsafe =>
      hPre hUnsafe args paramSpecs' hEvSubst hValidEntry (hConcretePre hUnsafe))
  cases hDay1 : OpenProgram.toDay1? (entryOpenProgForBody prog defId) with
  | some day1P =>
      have hDay1Eq := day1OfProgSome_eq prog σ defId hDay1
      rw [← hDay1Eq]
      exact openWellFormed_day1Some_to_wellFormed (entryOpenProgForBody prog defId)
        env' ob.sig.whereClauses { args := args } day1P hDay1 hOWf
  | none =>
      let ⟨os₀, hOInit, hOProg⟩ := hOWf.1
      let ⟨ds₀, hDInit, hInitRel⟩ := init_sim prog env' hRegWf σ defId ob
        erasedOb hParam.1 hGetErased rfl hObEq hDay1Adm hDay1 args hValidEntry
        os₀ hOInit
      have hErasedNoCall : bodyHasAnyCall erasedOb = false :=
        openBody_toDay1_noCall _ erasedOb hObEq
      have hSingleAt : ∀ s : State,
          Reaches (entryProgForBody (eraseOpenProgram σ prog) defId) ds₀ s →
          ∃ f : FrameState, s.frames = [f] ∧ f.sysrootOp? = none := by
        intro s hR
        let ⟨f, hFs, _, hS⟩ := reaches_singleFrame_noSysroot
          (entryProgForBody (eraseOpenProgram σ prog) defId) defId erasedOb
          hGetErased hErasedNoCall (initState_singleFrame _ _ ds₀ hDInit) hR
        exact ⟨f, hFs, hS⟩
      have hReachRel : ∀ s : State,
          Reaches (entryProgForBody (eraseOpenProgram σ prog) defId) ds₀ s →
          ∃ os : OpenState,
            OpenReaches (entryOpenProgForBody prog defId) env'
              ob.sig.whereClauses os₀ os ∧
            StateRel prog σ defId ob s os := by
        intro s hReach
        induction hReach with
        | refl => exact ⟨os₀, .refl os₀, hInitRel⟩
        | tail hR1 hStep ih =>
            let ⟨os1, hOReach1, hRel1⟩ := ih
            let ⟨_, _, hEv⟩ := hStep
            have hSys1 := hSingleAt _ hR1
            have hNoFault1 : ∀ k, ¬ OpenStep (entryOpenProgForBody prog defId)
                env' ob.sig.whereClauses os1 (.fault k) :=
              fun k => hOWf.2 os₀ hOInit os1 k hOReach1
            have hArgLt : Nat.blt ob.argumentCount ob.locals.length = true := by
              have hParts := erasedOb_locals_eq_map prog σ ob erasedOb hObEq
              unfold BodyStaticAdmitted singleBodyStaticAdmitted at hDay1Adm
              have hAL := bool_and_right (bool_and_left (bool_and_left
                (bool_and_left (bool_and_left (bool_and_left
                  (bool_and_left (bool_and_left hDay1Adm)))))))
              rw [hParts.1, hParts.2.1, length_map_eq] at hAL
              exact hAL
            have hStepSim := openStep_sim prog hRegWf env σ paramSpecs' hPsLen
              hMap' defId ob erasedOb hObEq hAdm'.2.2.2.2.2.2.2.2.2 hSupp
              hParam.1 hGetErased hObErasable hArgLt hDay1 _ os1 hRel1 hNoFault1
              hSys1
            let ⟨os2, hOStep, hRel2⟩ := hStepSim.2 _ hEv
            exact ⟨os2, openReaches_snoc (entryOpenProgForBody prog defId) env'
              ob.sig.whereClauses hOReach1 hOStep, hRel2⟩
      constructor
      · exact ⟨ds₀, hDInit, fun _ _ => ⟨0, rfl⟩⟩
      · intro k hFault
        unfold ReachesResult at hFault
        rw [hDInit] at hFault
        let ⟨s, hReach, _, _, hEv⟩ := hFault
        let ⟨os, hOReach, hRelS⟩ := hReachRel s hReach
        have hNoFaultS : ∀ k', ¬ OpenStep (entryOpenProgForBody prog defId)
            env' ob.sig.whereClauses os (.fault k') :=
          fun k' => hOWf.2 os₀ hOInit os k' hOReach
        have hArgLt : Nat.blt ob.argumentCount ob.locals.length = true := by
          have hParts := erasedOb_locals_eq_map prog σ ob erasedOb hObEq
          unfold BodyStaticAdmitted singleBodyStaticAdmitted at hDay1Adm
          have hAL := bool_and_right (bool_and_left (bool_and_left
            (bool_and_left (bool_and_left (bool_and_left
              (bool_and_left (bool_and_left hDay1Adm)))))))
          rw [hParts.1, hParts.2.1, length_map_eq] at hAL
          exact hAL
        have hStepSim := openStep_sim prog hRegWf env σ paramSpecs' hPsLen hMap'
          defId ob erasedOb hObEq hAdm'.2.2.2.2.2.2.2.2.2 hSupp hParam.1
          hGetErased hObErasable hArgLt hDay1 s os hRelS hNoFaultS
          (hSingleAt s hReach)
        exact hStepSim.1 k hEv

end Anneal.Generic

end
