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
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Trusted.MirAst.Types
public import Trusted.MirAst.Places
public import Trusted.MirAst.Rvalues
public import Trusted.MirAst.Statements
public import Trusted.MirAst.Terminators
public import Trusted.MirAst.Body

@[expose] public section

namespace Anneal.Generic

open Trusted.MirAst

/-!
# Open Generic MIR AST and Trait Registry (`Anneal.Generic.Syntax`)

Zero-TCB `theory/` syntax extensions for reasoning about object-free
trait-bounded Rust functions in `Anneal.Generic.OpenSemantics` and erasing
Day-1-erasable entry bodies (`openBodyIsDay1Erasable`, excluding `.traitCall`,
`.call`, `.assert`, and `.unwindResume`) to closed Day-1 `BodyVerified`: type
parameter indices (`TyParamId`), trait definition identifiers (`TraitDefId`),
associated item indices (`AssocItemIdx`), open MIR types (`OpenMirTy`),
where-clauses (`WhereClause`), function and trait-method signatures
(`FnSigSpec`, `TraitMethodSig`), trait impl coherence keys and bindings
(`ImplKey`, `ImplBinding`, `TraitRegistry`), and open MIR bodies (`OpenBody`,
`OpenProgram`).

All definitions live in `Type 0` inside `Anneal.Generic` (`0`-TCB `theory/`),
carry `noncomputable` on value definitions so Lean generates zero auxiliary
`._unsafe_rec` symbols, and avoid `deriving` clauses.
-/

/-- Positional generic type parameter index (`rustc_middle::ty::ParamTy`
with `pub index: u32, pub name: Symbol` in
`compiler/rustc_middle/src/ty/sty.rs`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`). -/
abbrev TyParamId := Nat

/-- Identifier for a Rust trait definition (`rustc_span::def_id::DefId` of a
trait item in the captured crate unit; `compiler/rustc_span/src/def_id.rs`,
`rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`). -/
abbrev TraitDefId := Nat

/-- Ordinal index of an associated item (associated type or trait method)
within a trait definition. -/
abbrev AssocItemIdx := Nat

/-- Nominal identifier for an algebraic data type (`rustc_middle::ty::AdtDef`
identifier; `compiler/rustc_middle/src/ty/adt.rs`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`). -/
abbrev AdtDefId := Nat

/-- Open MIR type syntax extending closed `MirTy` with positional type
parameters (`.param`), associated-type projections (`.assocProj`), slices
(`.slice`), fixed arrays (`.array`), and nominal ADTs (`.adt`).

Corresponds to `rustc_middle::ty::TyKind` (aliased from
`rustc_type_ir::TyKind` in `compiler/rustc_middle/src/ty/sty.rs` and
`compiler/rustc_type_ir/src/ty_kind.rs`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), specifically variants
`Param(I::ParamTy)`, `Alias(AliasTy<I>)`, `Slice(I::Ty)`,
`Array(I::Ty, I::Const)`, and `Adt(I::AdtDef, I::GenericArgs)`.

In object-free bounded generics, trait objects (`Dynamic`), closures, and
higher-ranked binders remain unmodeled and lower fail-closed to `.unsupported`.
-/
inductive OpenMirTy where
  | bool
  | int (width : IntWidth) (signed : Bool)
  | unit
  | never
  | char
  | ordering
  | enum (ty : EnumTy)
  | tuple (fields : List OpenMirTy)
  | slice (elem : OpenMirTy)
  | array (elem : OpenMirTy) (len : Nat)
  | adt (id : AdtDefId) (args : List OpenMirTy)
  | ref (mutability : Mutability) (pointee : OpenMirTy)
  | rawPtr (mutability : Mutability) (pointee : OpenMirTy)
  | param (id : TyParamId)
  | assocProj (selfTy : OpenMirTy) (traitId : TraitDefId)
      (traitArgs : List OpenMirTy) (assocIdx : AssocItemIdx)
  | unsupported

/-- Look up element `idx` in a list without importing `Trusted.MirModel`. -/
noncomputable def openListGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => openListGet? xs n

mutual
  /-- Explicit structural equality on `OpenMirTy`. -/
  noncomputable def OpenMirTy.beq : OpenMirTy → OpenMirTy → Bool
    | .bool, .bool => true
    | .int w₁ s₁, .int w₂ s₂ => IntWidth.beq w₁ w₂ && (s₁ == s₂)
    | .unit, .unit => true
    | .never, .never => true
    | .char, .char => true
    | .ordering, .ordering => true
    | .enum e₁, .enum e₂ => EnumTy.beq e₁ e₂
    | .tuple fs₁, .tuple fs₂ => OpenMirTy.beqList fs₁ fs₂
    | .slice e₁, .slice e₂ => OpenMirTy.beq e₁ e₂
    | .array e₁ n₁, .array e₂ n₂ => OpenMirTy.beq e₁ e₂ && Nat.beq n₁ n₂
    | .adt id₁ as₁, .adt id₂ as₂ => Nat.beq id₁ id₂ && OpenMirTy.beqList as₁ as₂
    | .ref m₁ p₁, .ref m₂ p₂ => Mutability.beq m₁ m₂ && OpenMirTy.beq p₁ p₂
    | .rawPtr m₁ p₁, .rawPtr m₂ p₂ =>
        Mutability.beq m₁ m₂ && OpenMirTy.beq p₁ p₂
    | .param id₁, .param id₂ => Nat.beq id₁ id₂
    | .assocProj s₁ tr₁ as₁ i₁, .assocProj s₂ tr₂ as₂ i₂ =>
        OpenMirTy.beq s₁ s₂ &&
        Nat.beq tr₁ tr₂ &&
        OpenMirTy.beqList as₁ as₂ &&
        Nat.beq i₁ i₂
    | .unsupported, .unsupported => true
    | _, _ => false

  /-- Elementwise structural equality on `List OpenMirTy`. -/
  noncomputable def OpenMirTy.beqList : List OpenMirTy → List OpenMirTy → Bool
    | [], [] => true
    | x :: xs, y :: ys => OpenMirTy.beq x y && OpenMirTy.beqList xs ys
    | _, _ => false
end

mutual
  /-- Whether an `OpenMirTy` contains zero uninstantiated type parameters
  (`.param`) and zero unnormalized associated-type projections (`.assocProj`).
  -/
  noncomputable def OpenMirTy.isClosed : OpenMirTy → Bool
    | .bool | .int _ _ | .unit | .never | .char | .ordering
    | .enum _ => true
    | .tuple fs => OpenMirTy.isClosedList fs
    | .slice e => OpenMirTy.isClosed e
    | .array e _ => OpenMirTy.isClosed e
    | .adt _ args => OpenMirTy.isClosedList args
    | .ref _ p => OpenMirTy.isClosed p
    | .rawPtr _ p => OpenMirTy.isClosed p
    | .param _ | .assocProj _ _ _ _ | .unsupported => false

  /-- Elementwise closedness on `List OpenMirTy`. -/
  noncomputable def OpenMirTy.isClosedList : List OpenMirTy → Bool
    | [] => true
    | x :: xs => OpenMirTy.isClosed x && OpenMirTy.isClosedList xs
end

mutual
  /-- Project an `OpenMirTy` back to closed `MirTy` when it lies in the
  Day-1 closed fragment (no `.param`, `.assocProj`, `.slice`, `.array`, `.adt`,
  or `.unsupported`). -/
  noncomputable def OpenMirTy.toClosedMirTy? : OpenMirTy → Option MirTy
    | .bool => some .bool
    | .int w s => some (.int w s)
    | .unit => some .unit
    | .never => some .never
    | .char => some .char
    | .ordering => some .ordering
    | .enum ty => some (.enum ty)
    | .tuple fs =>
        match OpenMirTy.toClosedMirTyList? fs with
        | some cs => some (.tuple cs)
        | none => none
    | .ref m p =>
        match OpenMirTy.toClosedMirTy? p with
        | some cp => some (.ref m cp)
        | none => none
    | .rawPtr m p =>
        match OpenMirTy.toClosedMirTy? p with
        | some cp => some (.rawPtr m cp)
        | none => none
    | .slice _ | .array _ _ | .adt _ _ | .param _ | .assocProj _ _ _ _
    | .unsupported => none

  /-- Elementwise projection of `List OpenMirTy` to `Option (List MirTy)`. -/
  noncomputable def OpenMirTy.toClosedMirTyList? :
      List OpenMirTy → Option (List MirTy)
    | [] => some []
    | x :: xs =>
        match OpenMirTy.toClosedMirTy? x, OpenMirTy.toClosedMirTyList? xs with
        | some cx, some cxs => some (cx :: cxs)
        | _, _ => none
end

mutual
  /-- Positional substitution `σ` applied to an `OpenMirTy`. An out-of-range
  parameter index stays `.param id` so partial substitutions remain well-defined
  and fail closed under `isClosed`. -/
  noncomputable def OpenMirTy.subst (σ : List OpenMirTy) : OpenMirTy → OpenMirTy
    | .bool => .bool
    | .int w s => .int w s
    | .unit => .unit
    | .never => .never
    | .char => .char
    | .ordering => .ordering
    | .enum ty => .enum ty
    | .tuple fs => .tuple (OpenMirTy.substList σ fs)
    | .slice e => .slice (OpenMirTy.subst σ e)
    | .array e len => .array (OpenMirTy.subst σ e) len
    | .adt id args => .adt id (OpenMirTy.substList σ args)
    | .ref m p => .ref m (OpenMirTy.subst σ p)
    | .rawPtr m p => .rawPtr m (OpenMirTy.subst σ p)
    | .param id =>
        match openListGet? σ id with
        | some repl => repl
        | none => .param id
    | .assocProj selfTy tr args idx =>
        .assocProj (OpenMirTy.subst σ selfTy) tr
          (OpenMirTy.substList σ args) idx
    | .unsupported => .unsupported

  /-- Elementwise substitution on `List OpenMirTy`. -/
  noncomputable def OpenMirTy.substList
      (σ : List OpenMirTy) : List OpenMirTy → List OpenMirTy
    | [] => []
    | x :: xs => OpenMirTy.subst σ x :: OpenMirTy.substList σ xs
end

/-- Trait and structural constraints on generic items (`PredicateKind`
aliased in `compiler/rustc_middle/src/ty/predicate.rs` from
`compiler/rustc_type_ir/src/predicate_kind.rs`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, covering object-free trait
bounds, `Sized` bounds, and associated-type equalities). -/
inductive WhereClause where
  | traitBound (selfTy : OpenMirTy) (traitId : TraitDefId)
      (args : List OpenMirTy)
  | isSized (ty : OpenMirTy)
  | typeEq (lhs rhs : OpenMirTy)

/-- Explicit structural equality on `WhereClause`. -/
noncomputable def WhereClause.beq : WhereClause → WhereClause → Bool
  | .traitBound s₁ tr₁ as₁, .traitBound s₂ tr₂ as₂ =>
      OpenMirTy.beq s₁ s₂ && Nat.beq tr₁ tr₂ && OpenMirTy.beqList as₁ as₂
  | .isSized t₁, .isSized t₂ => OpenMirTy.beq t₁ t₂
  | .typeEq l₁ r₁, .typeEq l₂ r₂ => OpenMirTy.beq l₁ l₂ && OpenMirTy.beq r₁ r₂
  | _, _ => false

/-- Signature of a trait method item, parameterized over `Self` (`.param 0`)
and any trait parameters (`.param 1..`). -/
structure TraitMethodSig where
  methodIdx : AssocItemIdx
  argTys : List OpenMirTy
  retTy : OpenMirTy
  whereClauses : List WhereClause := []
  isUnsafe : Bool := false

/-- Open generic function signature carrying positional parameter count,
argument/return types, and required `WhereClause` obligations. -/
structure FnSigSpec where
  tyParamCount : Nat
  argTys : List OpenMirTy
  retTy : OpenMirTy
  whereClauses : List WhereClause := []

/-- Grounded trait-implementation lookup key `(selfTy, traitId, args)` for
dictionary resolution in `TraitRegistry` (matching `TraitRef`, aliased in
`compiler/rustc_middle/src/ty/predicate.rs` from
`compiler/rustc_type_ir/src/predicate.rs`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`). -/
structure ImplKey where
  selfTy : OpenMirTy
  traitId : TraitDefId
  args : List OpenMirTy

/-- Explicit structural equality on `ImplKey`. -/
noncomputable def ImplKey.beq (a b : ImplKey) : Bool :=
  OpenMirTy.beq a.selfTy b.selfTy &&
    Nat.beq a.traitId b.traitId &&
    OpenMirTy.beqList a.args b.args

/-- Binding of one associated type (`type Assoc = rhsTy;`) inside an `impl`. -/
structure AssocTypeBinding where
  assocIdx : AssocItemIdx
  rhsTy : OpenMirTy

/-- Concrete implementation data registered for an `ImplKey` in a program's
`TraitRegistry`: optional impl type-parameter count, impl where-clauses,
associated-type definitions, and concrete method `DefId` mapping. -/
structure ImplBinding where
  implTyParamCount : Nat := 0
  whereClauses : List WhereClause := []
  assocTypes : List AssocTypeBinding := []
  methodDefIds : List (AssocItemIdx × DefId) := []

/-- Map from canonical `(selfTy, traitId, args)` keys to concrete trait
implementation bindings. Coherence (`TraitRegistryWf`) forbids duplicate
overlapping keys so dictionary resolution is deterministic. -/
abbrev TraitRegistry := List (ImplKey × ImplBinding)

/-- Look up the first binding whose `ImplKey` matches `key`. -/
noncomputable def lookupImpl :
    TraitRegistry → ImplKey → Option ImplBinding
  | [], _ => none
  | (k, b) :: rest, key =>
      if ImplKey.beq k key then some b else lookupImpl rest key

/-- Look up an associated type binding by ordinal `assocIdx`. -/
noncomputable def lookupAssocType :
    List AssocTypeBinding → AssocItemIdx → Option OpenMirTy
  | [], _ => none
  | b :: rest, idx =>
      if Nat.beq b.assocIdx idx then some b.rhsTy else lookupAssocType rest idx

/-- Look up the concrete callee `DefId` for a trait method index inside an
`ImplBinding`. -/
noncomputable def lookupImplMethod :
    List (AssocItemIdx × DefId) → AssocItemIdx → Option DefId
  | [], _ => none
  | (m, d) :: rest, idx =>
      if Nat.beq m idx then some d else lookupImplMethod rest idx

/-- Resolve a trait associated-type projection `(selfTy as Trait<args>)::Assoc`
against `reg`. -/
noncomputable def resolveAssocType (reg : TraitRegistry) (selfTy : OpenMirTy)
    (traitId : TraitDefId) (args : List OpenMirTy) (idx : AssocItemIdx) :
    Option OpenMirTy :=
  match lookupImpl reg ⟨selfTy, traitId, args⟩ with
  | some binding => lookupAssocType binding.assocTypes idx
  | none => none

mutual
  /-- Single bottom-up normalization pass rewriting closed `.assocProj` nodes
  resolved in `reg`. -/
  noncomputable def normalizeOpenTyStep (reg : TraitRegistry) :
      OpenMirTy → OpenMirTy
    | .bool => .bool
    | .int w s => .int w s
    | .unit => .unit
    | .never => .never
    | .char => .char
    | .ordering => .ordering
    | .enum ty => .enum ty
    | .tuple fs => .tuple (normalizeOpenTyStepList reg fs)
    | .slice e => .slice (normalizeOpenTyStep reg e)
    | .array e len => .array (normalizeOpenTyStep reg e) len
    | .adt id args => .adt id (normalizeOpenTyStepList reg args)
    | .ref m p => .ref m (normalizeOpenTyStep reg p)
    | .rawPtr m p => .rawPtr m (normalizeOpenTyStep reg p)
    | .param id => .param id
    | .assocProj selfTy tr args idx =>
        let selfN := normalizeOpenTyStep reg selfTy
        let argsN := normalizeOpenTyStepList reg args
        match resolveAssocType reg selfN tr argsN idx with
        | some rhs => rhs
        | none => .assocProj selfN tr argsN idx
    | .unsupported => .unsupported

  /-- Elementwise single normalization pass on `List OpenMirTy`. -/
  noncomputable def normalizeOpenTyStepList (reg : TraitRegistry) :
      List OpenMirTy → List OpenMirTy
    | [] => []
    | x :: xs => normalizeOpenTyStep reg x :: normalizeOpenTyStepList reg xs
end

/-- Bounded multi-step normalization of associated-type projections against
`reg`. Using explicit `fuel` guarantees structural termination in `Type 0`
without `partial`. -/
noncomputable def normalizeOpenTy (reg : TraitRegistry) :
    Nat → OpenMirTy → OpenMirTy
  | 0, ty => ty
  | fuel + 1, ty => normalizeOpenTy reg fuel (normalizeOpenTyStep reg ty)

/-- Substitute `σ` and normalize associated projections up to `fuel` steps. -/
noncomputable def OpenMirTy.substAndNormalize (reg : TraitRegistry) (fuel : Nat)
    (σ : List OpenMirTy) (ty : OpenMirTy) : OpenMirTy :=
  normalizeOpenTy reg fuel (OpenMirTy.subst σ ty)

/-- Substitute `σ` into a `WhereClause` and normalize embedded types. -/
noncomputable def WhereClause.substAndNormalize (reg : TraitRegistry)
    (fuel : Nat) (σ : List OpenMirTy) : WhereClause → WhereClause
  | .traitBound selfTy tr args =>
      .traitBound (OpenMirTy.substAndNormalize reg fuel σ selfTy) tr
        (args.map (OpenMirTy.substAndNormalize reg fuel σ))
  | .isSized ty => .isSized (OpenMirTy.substAndNormalize reg fuel σ ty)
  | .typeEq lhs rhs =>
      .typeEq (OpenMirTy.substAndNormalize reg fuel σ lhs)
        (OpenMirTy.substAndNormalize reg fuel σ rhs)

/-- Open MIR place projection element carrying `OpenMirTy` in field
projections. -/
inductive OpenProjectionElem where
  | deref
  | field (fieldIdx : FieldIdx) (ty : OpenMirTy)
  | unsupported

/-- Open MIR place (`localId` plus open projections). -/
structure OpenPlace where
  localId : LocalId
  projection : List OpenProjectionElem := []

/-- Open MIR typed constant operand. -/
structure OpenConstOperand where
  ty : OpenMirTy
  lit : ConstLit

/-- Open MIR operand (`copy`, `move`, `constant`). -/
inductive OpenOperand where
  | copy (place : OpenPlace)
  | move (place : OpenPlace)
  | constant (c : OpenConstOperand)

/-- Open MIR right-hand-side expression carrying `OpenMirTy` in `.cast`. -/
inductive OpenRvalue where
  | use (op : OpenOperand)
  | binaryOp (op : BinOp) (lhs rhs : OpenOperand)
  | unaryOp (op : UnOp) (opnd : OpenOperand)
  | cast (kind : CastKind) (opnd : OpenOperand) (ty : OpenMirTy)
  | discriminant (place : OpenPlace)
  | ref (mutability : Mutability) (place : OpenPlace)
  | addressOf (mutability : Mutability) (place : OpenPlace)
  | aggregateTuple (fields : List OpenOperand)
  | unsupported

/-- Open MIR statement inside an `OpenBasicBlock`. -/
inductive OpenStatementKind where
  | assign (dst : OpenPlace) (rvalue : OpenRvalue)
  | storageLive (localId : LocalId)
  | storageDead (localId : LocalId)
  | nop
  | unsupported

/-- Open MIR terminator extending `TerminatorKind` with generic direct calls
(`.call` carrying `substs : List OpenMirTy`) and trait-method calls
(`.traitCall`). -/
inductive OpenTerminatorKind where
  | goto (target : BasicBlockId)
  | switchInt (discr : OpenOperand) (targets : SwitchTargets)
  | return_
  | unreachable
  | unwindResume
  | assert (cond : OpenOperand) (expected : Bool) (msg : AssertKind)
      (target : BasicBlockId) (unwind : UnwindAction)
  | call (callee : DefId) (substs : List OpenMirTy)
      (args : List OpenOperand) (dst : OpenPlace)
      (target : Option BasicBlockId) (unwind : UnwindAction)
  | traitCall (selfTy : OpenMirTy) (traitId : TraitDefId)
      (traitArgs : List OpenMirTy) (methodIdx : AssocItemIdx)
      (args : List OpenOperand) (dst : OpenPlace)
      (target : Option BasicBlockId) (unwind : UnwindAction)
  | unsupported

/-- Basic block in an open generic MIR body. -/
structure OpenBasicBlock where
  statements : List OpenStatementKind
  terminator : OpenTerminatorKind
  cleanup : Bool := false

/-- Open generic MIR function body combining `FnSigSpec` with open local
declarations and open basic blocks. -/
structure OpenBody where
  sig : FnSigSpec
  argumentCount : Nat
  locals : List OpenMirTy
  basicBlocks : List OpenBasicBlock
  isUnsafe : Bool := false
  identity : String := ""

/-- Open generic MIR verification unit carrying bodies and the trait impl
coherence registry. Mirrors `Trusted.MirAst.Program` by omitting defaults on
`pointerWidthBits`, `mirProfileVersion`, and `scope` so target layout, profile
version, and verification scope must be supplied explicitly. -/
structure OpenProgram where
  bodies : List OpenBody
  entryDefId : DefId := 0
  traitRegistry : TraitRegistry := []
  pointerWidthBits : Nat
  mirProfileVersion : Nat
  scope : VerificationScope

/-- Substitute and normalize an `OpenProjectionElem`. -/
noncomputable def OpenProjectionElem.subst (reg : TraitRegistry) (fuel : Nat)
    (σ : List OpenMirTy) : OpenProjectionElem → OpenProjectionElem
  | .deref => .deref
  | .field idx ty => .field idx (OpenMirTy.substAndNormalize reg fuel σ ty)
  | .unsupported => .unsupported

/-- Substitute and normalize an `OpenPlace`. -/
noncomputable def OpenPlace.subst (reg : TraitRegistry) (fuel : Nat)
    (σ : List OpenMirTy) (p : OpenPlace) : OpenPlace :=
  { localId := p.localId
  , projection := p.projection.map (OpenProjectionElem.subst reg fuel σ) }

/-- Substitute and normalize an `OpenOperand`. -/
noncomputable def OpenOperand.subst (reg : TraitRegistry) (fuel : Nat)
    (σ : List OpenMirTy) : OpenOperand → OpenOperand
  | .copy p => .copy (OpenPlace.subst reg fuel σ p)
  | .move p => .move (OpenPlace.subst reg fuel σ p)
  | .constant c =>
      .constant { ty := OpenMirTy.substAndNormalize reg fuel σ c.ty
                , lit := c.lit }

/-- Substitute and normalize an `OpenRvalue`. -/
noncomputable def OpenRvalue.subst (reg : TraitRegistry) (fuel : Nat)
    (σ : List OpenMirTy) : OpenRvalue → OpenRvalue
  | .use op => .use (OpenOperand.subst reg fuel σ op)
  | .binaryOp op lhs rhs =>
      .binaryOp op (OpenOperand.subst reg fuel σ lhs)
        (OpenOperand.subst reg fuel σ rhs)
  | .unaryOp op opnd => .unaryOp op (OpenOperand.subst reg fuel σ opnd)
  | .cast kind opnd ty =>
      .cast kind (OpenOperand.subst reg fuel σ opnd)
        (OpenMirTy.substAndNormalize reg fuel σ ty)
  | .discriminant p => .discriminant (OpenPlace.subst reg fuel σ p)
  | .ref m p => .ref m (OpenPlace.subst reg fuel σ p)
  | .addressOf m p => .addressOf m (OpenPlace.subst reg fuel σ p)
  | .aggregateTuple fs =>
      .aggregateTuple (fs.map (OpenOperand.subst reg fuel σ))
  | .unsupported => .unsupported

/-- Substitute and normalize an `OpenStatementKind`. -/
noncomputable def OpenStatementKind.subst (reg : TraitRegistry) (fuel : Nat)
    (σ : List OpenMirTy) : OpenStatementKind → OpenStatementKind
  | .assign dst rv =>
      .assign (OpenPlace.subst reg fuel σ dst) (OpenRvalue.subst reg fuel σ rv)
  | .storageLive l => .storageLive l
  | .storageDead l => .storageDead l
  | .nop => .nop
  | .unsupported => .unsupported

/-- Substitute and normalize an `OpenTerminatorKind`. -/
noncomputable def OpenTerminatorKind.subst (reg : TraitRegistry) (fuel : Nat)
    (σ : List OpenMirTy) : OpenTerminatorKind → OpenTerminatorKind
  | .goto t => .goto t
  | .switchInt d tgts =>
      .switchInt (OpenOperand.subst reg fuel σ d) tgts
  | .return_ => .return_
  | .unreachable => .unreachable
  | .unwindResume => .unwindResume
  | .assert cond exp msg tgt uw =>
      .assert (OpenOperand.subst reg fuel σ cond) exp msg tgt uw
  | .call callee substs args dst tgt uw =>
      .call callee (substs.map (OpenMirTy.substAndNormalize reg fuel σ))
        (args.map (OpenOperand.subst reg fuel σ))
        (OpenPlace.subst reg fuel σ dst) tgt uw
  | .traitCall selfTy tr trArgs mIdx args dst tgt uw =>
      .traitCall (OpenMirTy.substAndNormalize reg fuel σ selfTy) tr
        (trArgs.map (OpenMirTy.substAndNormalize reg fuel σ)) mIdx
        (args.map (OpenOperand.subst reg fuel σ))
        (OpenPlace.subst reg fuel σ dst) tgt uw
  | .unsupported => .unsupported

/-- Substitute and normalize an `OpenBasicBlock`. -/
noncomputable def OpenBasicBlock.subst (reg : TraitRegistry) (fuel : Nat)
    (σ : List OpenMirTy) (bb : OpenBasicBlock) : OpenBasicBlock :=
  { statements := bb.statements.map (OpenStatementKind.subst reg fuel σ)
  , terminator := OpenTerminatorKind.subst reg fuel σ bb.terminator
  , cleanup := bb.cleanup }

/-- Instantiate an `OpenBody` at ground type substitution `σ` and projection
normalization fuel `fuel` against `reg`. -/
noncomputable def OpenBody.subst (reg : TraitRegistry) (fuel : Nat)
    (σ : List OpenMirTy) (ob : OpenBody) : OpenBody :=
  { sig := { tyParamCount := 0
           , argTys := ob.sig.argTys.map
               (OpenMirTy.substAndNormalize reg fuel σ)
           , retTy := OpenMirTy.substAndNormalize reg fuel σ ob.sig.retTy
           , whereClauses := ob.sig.whereClauses.map
               (WhereClause.substAndNormalize reg fuel σ) }
  , argumentCount := ob.argumentCount
  , locals := ob.locals.map (OpenMirTy.substAndNormalize reg fuel σ)
  , basicBlocks := ob.basicBlocks.map (OpenBasicBlock.subst reg fuel σ)
  , isUnsafe := ob.isUnsafe
  , identity := ob.identity }

end Anneal.Generic

end
