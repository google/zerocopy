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
public import Init.Data.Nat.Div.Basic
public import Init.Data.List.Basic
public import Init.Control.Except
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics.Ops
public import Trusted.MirSemantics.Enum
public import Trusted.MirSemantics.Layout
public import Trusted.MirSemantics.Memory
public import Trusted.MirSemantics.Bytes
public import Trusted.MirSemantics.State
public import Trusted.MirSemantics.Step
public import Trusted.MirSemantics.Boundary
public import Anneal.Generic.Syntax
public import Anneal.Generic.TypeSpec

@[expose] public section

namespace Anneal.Generic

open Trusted.MirAst Trusted.MirSemantics

/-!
# Trait Contracts & Open Operational Semantics (`Anneal.Generic.OpenSemantics`)

Zero-TCB `theory/` assume-guarantee trait contracts (`TraitMethodSpec`,
`TraitContract`), trait registry coherence (`TraitRegistryWf`), where-clause
discharge (`WhereClauseParamSem`, `AllWhereDischarged`), open MIR operational
rules (`OpenState`, `AssumeGuaranteeTraitCall`, `OpenStep`, `OpenWellFormed`),
the parametric verification judgment (`ParametricBodyVerified`), and the erasure
claim signature (`OpenInstantiationErasureClaim`).

All modules under `Anneal.Generic` live in `anneal/theory/` (`0` TCB lines in
`anneal/trusted/`) and feed closed Day-1 `Trusted.MirSemantics.BodyVerified`
proofs for Day-1-erasable entry bodies (`openBodyIsDay1Erasable`) via
`Anneal.Generic.ClosedInstantiationTransfer`.

## Known modeling gaps (must be closed before promotion to trusted)

Before promoting any open-generic AST, layout, or operational definition into
`anneal/trusted/`, the following known modeling gaps must be closed:

1. **Unwind propagation and guard-mutation coverage (`openUnwindWith`)**:
   - In `.continue_`, `openUnwindWith` currently inspects `restFrames` without
     first consulting `callerFrame?`'s `retDst`, and returns
     `.fault .unsupported` rather than `.done (.unwound cm)` when unwinding out
     of a concrete callee into a root entry frame whose `retDst = none`.
   - Undefined-behavior guards in `OpenSemantics` are not yet cataloged in
     `ci/check_guard_mutation.py`.
2. **Trait-contract caller memory and impl `where`-clause scope
   (`SatisfiesTraitSemDepth`, `AssumeGuaranteeTraitCall`)**:
   - `SatisfiesTraitSemDepth` checks `mspec.pre` and `mspec.post` at empty
     `CallerMemory` (`⟨[]⟩`), whereas `AssumeGuaranteeTraitCall` invokes method
     contracts at arbitrary `s.callerMem` and updates `s.callerMem := cm'`.
   - `SatisfiesTraitSemDepth` passes `calleeBody.sig.whereClauses` as
     `assumedWhere` without verifying that those clauses follow from
     `binding.whereClauses` and `mspec.sig.whereClauses` (and `openMirTyNoParam`
     admits parameter-free `.assocProj` nodes that fail `OpenMirTy.isClosed`).
3. **Reference, raw-pointer, and slice validity (`pointerTypeLayoutSpec`,
   `sliceTypeLayoutSpec`, `checkPtrRoles`, `openInitStateAux`)**:
   - `pointerTypeLayoutSpec` and `sliceTypeLayoutSpec` hardcode
     `inhabited := true` without gating on `pointeeSpec.inhabited` or non-empty
     `elemSpec.inhabited`.
   - `pointerTypeLayoutSpec` uses an unscaled `[0, isizeMax]` metadata range for
     unsized pointees rather than scaling reference slice lengths by `elemSz` or
     permitting raw `*const [T]` lengths above `isize::MAX`.
   - `checkPtrRoles` accepts thin `Val.ptr` (which carries no slice length
     metadata) for 16-byte wide pointers and does not check backing allocations
     against `openInitStateAux`'s empty `callerMem`.
4. **Projection normalization before `toClosedMirTy?`, whole-program `toDay1?`
   dispatch, and fault precedence (`checkOpenVal`, `evalOpenOperand`,
   `openInitStateAux`, `openEvalDetStepAux`)**:
   - `checkOpenVal`, `evalOpenOperand` (`.constant`), and `openEvalDetStepAux`
     (`.binaryOp`, `.unaryOp`, `.cast`, `.switchInt`) inspect
     `OpenMirTy.toClosedMirTy?` without first normalizing associated-type
     projections via `normalizeOpenTy`.
   - `openInitStateAux` and `openEvalDetStepAux` branch on whole-program
     `OpenProgram.toDay1? prog`, allowing uncalled generic sibling bodies in
     `prog.bodies` to alter closed-body stepping, initial memory
     (`MemoryState.empty` vs. `entryMemory`), and operand-vs-type fault
     precedence.
5. **Parameter invariants across non-`.bytes` values and `?Sized` metadata
   (`argsSatisfyParamInvs`, `WhereClauseParamSem`, `AllParamInvsWf`)**:
   - `argsSatisfyParamInvs` enforces `env.typeSpecs.paramInvs` only when an
     entry value at `.param i` is represented as `Val.bytes bs`, returning
     `True` on native scalar, boolean, char, unit, pointer, and tuple `Val`
     representations accepted by `checkValAgainstSpec`.
   - `WhereClauseParamSem` (for `.param i`) and `AllParamInvsWf` quantify
     `LangValid` and inhabitation only at `PtrMeta.none` / `sp.isSized = true`,
     making `typeInv` and `paramInvs` checks vacuous for unsized (`?Sized`)
     parameter instantiations.
6. **Concrete trait-callee static admission (`concreteTraitCallStep`)**:
   - Closed `.traitCall` dispatch checks `tyParamCount = 0`, `openBodyNoParam`,
     `openSigMatchesLocals`, and non-empty `basicBlocks` on `calleeBody`, rather
     than full `OpenBodyStaticAdmitted`.
7. **Closed-reference / raw-pointer admission boundary and closed-`Self`
   trait-bound vacuity (`openClosedTySupported`, `SatisfiesTraitSem`,
   `AllWhereDischarged`, `ParametricBodyVerified`)**:
   - `openClosedTySupported` inspects only types convertible via
     `OpenMirTy.toClosedMirTy?`, rejecting closed Day-1-convertible `.ref`,
     `.rawPtr`, non-overflow `.tuple`, and unadmitted `.enum` types (e.g.,
     `&u64`, `*const bool`) across static admission (`openLocalsAdmitted`,
     `OpenBodyStructureValid`, `SatisfiesTraitSemDepth`, and `WhereClauseSem`).
     `SatisfiesTraitSem` and `AllWhereDischarged` therefore refuse `&self` and
     `&mut self` trait `impl`s whose instantiated signatures or callee locals
     mention a closed Day-1-convertible reference or raw pointer (such as
     `impl ByteSource for u64`), whereas by-value-receiver scalar trait `impl`s
     are inhabited (see `Anneal.Generic.Canaries`).
   - Closed references and raw pointers to non-Day-1 pointees (`.adt`, `.slice`,
     or `.array`, such as `&[u8]` or `&MemSlice`) yield
     `OpenMirTy.toClosedMirTy? = none`, so `openClosedTySupported` admits them
     (used by parametric canaries such as `hash_block`). Consequently, a closed
     `&self`/`&mut self` `impl` on a non-Day-1 `Self` type (e.g.,
     `impl ByteSource for MemSlice`) remains admissible in
     `OpenBodyStaticAdmitted`, `SatisfiesTraitSem`, and `AllWhereDischarged`,
     running with empty `CallerMemory` (`⟨[]⟩`) and unbacked `Val.ptr` values
     (whose dereference faults `.unsupported` in `OpenSemantics`). Closing this
     requires integrating Profile v2 `CallerMemory` support before promotion to
     `anneal/trusted/`.
   - When a body's `sig.whereClauses` contains a closed-`Self` (and
     closed-arguments) `.traitBound` whose `SatisfiesTraitSem` obligation is
     unrefinable, `WhereClauseParamSem` reduces to `False`, so the
     `AllWhereParamsSem` implication in `ParametricBodyVerified` holds vacuously
     (while `OpenBodyStructureValid` still holds unconditionally). This vacuity
     is not exploitable at closed instantiation because both
     `ClosedOpenInstantiationTransfer` and `ClosedInstantiationTransfer`
     independently require `AllWhereDischarged`.
8. **Pinned upstream `rustc` and Rust Reference quotes**:
   - Promoting any declaration into `anneal/trusted/lean/` requires adding
     pinned verbatim upstream quotes for all modeled `rustc` and Rust Reference
     rules.
-/

/-- Abstract semantic specification for one method of a trait, parameterized
over the trait's type parameter layouts (`paramSpecs`) and resolved associated
type layouts (`assocSpecs`). -/
structure TraitMethodSpec where
  sig : TraitMethodSig
  pre : List TypeLayoutSpec → List TypeLayoutSpec → List Val →
    CallerMemory → Prop
  post : List TypeLayoutSpec → List TypeLayoutSpec → List Val →
    CallerMemory → TerminalOut → Prop

/-- Look up a `TraitMethodSpec` by `AssocItemIdx`. -/
noncomputable def lookupMethodSpec :
    List TraitMethodSpec → AssocItemIdx → Option TraitMethodSpec
  | [], _ => none
  | m :: rest, idx =>
      if Nat.beq m.sig.methodIdx idx then some m
      else lookupMethodSpec rest idx

/-- Semantic contract associated with a Rust trait (`TraitDefId`): parameter
count, associated type count, method pre/post contracts, and a type safety
invariant enforced on implementing types. -/
structure TraitContract where
  traitId : TraitDefId
  tyParamCount : Nat
  assocTypeCount : Nat
  methodSpecs : List TraitMethodSpec
  typeInv : TypeLayoutSpec → List AllocByte → Prop := fun _ _ => True

/-- Semantic environment interpreting traits and open/ADT types during
parametric verification. -/
structure OpenExecEnv where
  traitContracts : TraitDefId → Option TraitContract
  typeSpecs : TypeSpecEnv := emptyTypeSpecEnv

/-- Normalization fuel used when normalizing associated-type projections. -/
noncomputable def normFuel : Nat := 16

/-- Whether `key` matches any `ImplKey` already present in `reg`. -/
noncomputable def implKeyInRegistry (key : ImplKey) : TraitRegistry → Bool
  | [] => false
  | (k, _) :: rest => ImplKey.beq k key || implKeyInRegistry key rest

/-- Coherence invariant on `TraitRegistry`: no two entries share an `ImplKey`
(preventing duplicate-impl dictionary spoofing). Matches Rust trait coherence
(`compiler/rustc_middle/src/traits/specialization_graph.rs`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`:

> "This implicitly checks for overlapping impls"
). -/
noncomputable def TraitRegistryPairwiseDistinct : TraitRegistry → Bool
  | [] => true
  | (k, _) :: rest =>
      !implKeyInRegistry k rest && TraitRegistryPairwiseDistinct rest

/-- Whether an `assocIdx` already appears in a list of `AssocTypeBinding`s. -/
noncomputable def assocIdxInBindings (idx : AssocItemIdx) :
    List AssocTypeBinding → Bool
  | [] => false
  | b :: rest => Nat.beq b.assocIdx idx || assocIdxInBindings idx rest

/-- Every associated-type binding within an `ImplBinding` uses a distinct
`assocIdx` and a closed acyclic RHS `OpenMirTy` (`OpenMirTy.isClosed` forbids
`.param`, `.assocProj`, and `.unsupported`). -/
noncomputable def assocTypesWf : List AssocTypeBinding → Bool
  | [] => true
  | b :: rest =>
      !assocIdxInBindings b.assocIdx rest &&
      OpenMirTy.isClosed b.rhsTy &&
      assocTypesWf rest

/-- Whether a `methodIdx` already appears in `methodDefIds`. -/
noncomputable def methodIdxInBindings (idx : AssocItemIdx) :
    List (AssocItemIdx × DefId) → Bool
  | [] => false
  | (m, _) :: rest => Nat.beq m idx || methodIdxInBindings idx rest

/-- Every method binding within an `ImplBinding` uses a distinct `AssocItemIdx`.
-/
noncomputable def methodBindingsDistinct : List (AssocItemIdx × DefId) → Bool
  | [] => true
  | (m, _) :: rest =>
      !methodIdxInBindings m rest && methodBindingsDistinct rest

/-- Whether a `WhereClause` contains zero open parameters, projections, or
`.unsupported` constructors. -/
noncomputable def WhereClause.isClosed : WhereClause → Bool
  | .traitBound selfTy _ args =>
      OpenMirTy.isClosed selfTy && OpenMirTy.isClosedList args
  | .isSized ty => OpenMirTy.isClosed ty
  | .typeEq lhs rhs => OpenMirTy.isClosed lhs && OpenMirTy.isClosed rhs

/-- Elementwise closedness on `List WhereClause`. -/
noncomputable def WhereClause.isClosedList : List WhereClause → Bool
  | [] => true
  | w :: rest => WhereClause.isClosed w && WhereClause.isClosedList rest

/-- Every `ImplKey` and `ImplBinding` in `reg` uses closed self/argument/RHS
types, zero impl type parameters, closed impl where-clauses, and pairwise
distinct intra-binding associated items and methods. -/
noncomputable def ImplRegistryEntriesWf : TraitRegistry → Bool
  | [] => true
  | (k, b) :: rest =>
      OpenMirTy.isClosed k.selfTy &&
      OpenMirTy.isClosedList k.args &&
      Nat.beq b.implTyParamCount 0 &&
      WhereClause.isClosedList b.whereClauses &&
      assocTypesWf b.assocTypes &&
      methodBindingsDistinct b.methodDefIds &&
      ImplRegistryEntriesWf rest

/-- Combined well-formedness gate for a program's `TraitRegistry`. -/
noncomputable def TraitRegistryWf (reg : TraitRegistry) : Bool :=
  TraitRegistryPairwiseDistinct reg && ImplRegistryEntriesWf reg

/-- Check whether `wc` appears syntactically (up to `WhereClause.beq`) in an
assumed where-clause list. -/
noncomputable def whereClauseInList (wc : WhereClause) :
    List WhereClause → Bool
  | [] => false
  | w :: rest => WhereClause.beq w wc || whereClauseInList wc rest

/-- Check that every element of `wcs` appears in `assumedWhere`. -/
noncomputable def allWhereInList (assumedWhere : List WhereClause) :
    List WhereClause → Bool
  | [] => true
  | w :: rest =>
      whereClauseInList w assumedWhere && allWhereInList assumedWhere rest

/-- Convert an `OpenProjectionElem` to a closed `ProjectionElem` if its field
type lies in the Day-1 `MirTy` fragment. -/
noncomputable def OpenProjectionElem.toDay1? :
    OpenProjectionElem → Option ProjectionElem
  | .deref => some .deref
  | .field idx ty =>
      match OpenMirTy.toClosedMirTy? ty with
      | some mty => some (.field idx mty)
      | none => none
  | .unsupported => some .unsupported

/-- Convert a list of `OpenProjectionElem` to `List ProjectionElem`. -/
noncomputable def OpenProjectionElem.toDay1List? :
    List OpenProjectionElem → Option (List ProjectionElem)
  | [] => some []
  | p :: rest =>
      match OpenProjectionElem.toDay1? p,
            OpenProjectionElem.toDay1List? rest with
      | some dp, some drest => some (dp :: drest)
      | _, _ => none

/-- Convert an `OpenPlace` to a Day-1 `Place` if all field projections lie in
Day-1 `MirTy`. -/
noncomputable def OpenPlace.toDay1? (p : OpenPlace) : Option Place :=
  match OpenProjectionElem.toDay1List? p.projection with
  | some ps => some { localId := p.localId, projection := ps }
  | none => none

/-- Convert an `OpenOperand` to a Day-1 `Operand` if its embedded types lie in
Day-1 `MirTy`. -/
noncomputable def OpenOperand.toDay1? : OpenOperand → Option Operand
  | .copy p =>
      match OpenPlace.toDay1? p with
      | some dp => some (.copy dp)
      | none => none
  | .move p =>
      match OpenPlace.toDay1? p with
      | some dp => some (.move dp)
      | none => none
  | .constant c =>
      match OpenMirTy.toClosedMirTy? c.ty with
      | some mty => some (.constant { ty := mty, lit := c.lit })
      | none => none

/-- Convert a list of `OpenOperand` to `List Operand`. -/
noncomputable def OpenOperand.toDay1List? :
    List OpenOperand → Option (List Operand)
  | [] => some []
  | x :: xs =>
      match OpenOperand.toDay1? x, OpenOperand.toDay1List? xs with
      | some dx, some dxs => some (dx :: dxs)
      | _, _ => none

/-- Convert an `OpenRvalue` to a Day-1 `Rvalue` if its embedded types lie in
Day-1 `MirTy`. -/
noncomputable def OpenRvalue.toDay1? : OpenRvalue → Option Rvalue
  | .use op =>
      match OpenOperand.toDay1? op with
      | some dop => some (.use dop)
      | none => none
  | .binaryOp op lhs rhs =>
      match OpenOperand.toDay1? lhs, OpenOperand.toDay1? rhs with
      | some l, some r => some (.binaryOp op l r)
      | _, _ => none
  | .unaryOp op opnd =>
      match OpenOperand.toDay1? opnd with
      | some o => some (.unaryOp op o)
      | none => none
  | .cast kind opnd ty =>
      match OpenOperand.toDay1? opnd, OpenMirTy.toClosedMirTy? ty with
      | some o, some mty => some (.cast kind o mty)
      | _, _ => none
  | .discriminant p =>
      match OpenPlace.toDay1? p with
      | some dp => some (.discriminant dp)
      | none => none
  | .ref m p =>
      match OpenPlace.toDay1? p with
      | some dp => some (.ref m dp)
      | none => none
  | .addressOf m p =>
      match OpenPlace.toDay1? p with
      | some dp => some (.addressOf m dp)
      | none => none
  | .aggregateTuple fs =>
      match OpenOperand.toDay1List? fs with
      | some dfs => some (.aggregateTuple dfs)
      | none => none
  | .unsupported => some .unsupported

/-- Convert an `OpenStatementKind` to a Day-1 `StatementKind`. -/
noncomputable def OpenStatementKind.toDay1? :
    OpenStatementKind → Option StatementKind
  | .assign dst rv =>
      match OpenPlace.toDay1? dst, OpenRvalue.toDay1? rv with
      | some d, some r => some (.assign d r)
      | _, _ => none
  | .storageLive l => some (.storageLive l)
  | .storageDead l => some (.storageDead l)
  | .nop => some .nop
  | .unsupported => some .unsupported

/-- Convert a list of `OpenStatementKind` to `List StatementKind`. -/
noncomputable def OpenStatementKind.toDay1List? :
    List OpenStatementKind → Option (List StatementKind)
  | [] => some []
  | s :: rest =>
      match OpenStatementKind.toDay1? s, OpenStatementKind.toDay1List? rest with
      | some ds, some drest => some (ds :: drest)
      | _, _ => none

/-- Convert an `OpenTerminatorKind` to a Day-1 `TerminatorKind`. `.traitCall`
and generic `.call` with non-empty substitutions have no Day-1 equivalent and
return `none`. -/
noncomputable def OpenTerminatorKind.toDay1? :
    OpenTerminatorKind → Option TerminatorKind
  | .goto t => some (.goto t)
  | .switchInt d tgts =>
      match OpenOperand.toDay1? d with
      | some dd => some (.switchInt dd tgts)
      | none => none
  | .return_ => some .return_
  | .unreachable => some .unreachable
  | .unwindResume => some .unwindResume
  | .assert cond exp msg tgt uw =>
      match OpenOperand.toDay1? cond with
      | some dc => some (.assert dc exp msg tgt uw)
      | none => none
  | .call callee substs args dst tgt uw =>
      match substs with
      | [] =>
          match OpenOperand.toDay1List? args, OpenPlace.toDay1? dst with
          | some dargs, some ddst => some (.call callee dargs ddst tgt uw)
          | _, _ => none
      | _ :: _ => none
  | .traitCall _ _ _ _ _ _ _ _ => none
  | .unsupported => some .unsupported

/-- Convert an `OpenBasicBlock` to a Day-1 `BasicBlock`. -/
noncomputable def OpenBasicBlock.toDay1? (bb : OpenBasicBlock) :
    Option BasicBlock :=
  match OpenStatementKind.toDay1List? bb.statements,
        OpenTerminatorKind.toDay1? bb.terminator with
  | some stmts, some term =>
      some { statements := stmts, terminator := term, cleanup := bb.cleanup }
  | _, _ => none

/-- Convert a list of `OpenBasicBlock` to `List BasicBlock`. -/
noncomputable def OpenBasicBlock.toDay1List? :
    List OpenBasicBlock → Option (List BasicBlock)
  | [] => some []
  | b :: rest =>
      match OpenBasicBlock.toDay1? b, OpenBasicBlock.toDay1List? rest with
      | some db, some drest => some (db :: drest)
      | _, _ => none

/-- Convert an `OpenBody` to a Day-1 `Body` when all locals, statements, and
terminators lie in the Day-1 closed fragment. -/
noncomputable def OpenBody.toDay1? (ob : OpenBody) : Option Body :=
  match OpenMirTy.toClosedMirTyList? ob.locals,
        OpenBasicBlock.toDay1List? ob.basicBlocks with
  | some dLocals, some dBlocks =>
      some
        { argumentCount := ob.argumentCount
        , locals := dLocals
        , basicBlocks := dBlocks
        , isUnsafe := ob.isUnsafe
        , identity := ob.identity }
  | _, _ => none

/-- Convert an `OpenProgram` to a Day-1 `Program` when every body converts via
`OpenBody.toDay1?`. -/
noncomputable def OpenProgram.toDay1List? : List OpenBody → Option (List Body)
  | [] => some []
  | b :: rest =>
      match OpenBody.toDay1? b, OpenProgram.toDay1List? rest with
      | some db, some drest => some (db :: drest)
      | _, _ => none

/-- Convert an `OpenProgram` to a Day-1 `Program` if every body converts. -/
noncomputable def OpenProgram.toDay1? (prog : OpenProgram) : Option Program :=
  match OpenProgram.toDay1List? prog.bodies with
  | some bs =>
      some
        { bodies := bs
        , entryDefId := prog.entryDefId
        , pointerWidthBits := prog.pointerWidthBits
        , mirProfileVersion := prog.mirProfileVersion
        , scope := prog.scope }
  | none => none

/-- Execution frame for open generic MIR evaluation, recording caller return
destination and unwind target for nested monomorphic trait calls. -/
structure OpenFrameState where
  defId : DefId
  blockIdx : BasicBlockId
  stmtIdx : Nat
  locals : List LocalSlot
  retDst : Option (OpenPlace × Option BasicBlockId × UnwindAction) := none

/-- Execution state for open generic MIR evaluation (`frames`, `callerMem`,
and stack `mem`). -/
structure OpenState where
  frames : List OpenFrameState
  callerMem : CallerMemory := ⟨[]⟩
  mem : MemoryState

/-- Project a single `OpenFrameState` to Day-1 `FrameState`. -/
noncomputable def OpenFrameState.toFrameState (f : OpenFrameState) :
    FrameState :=
  { defId := f.defId
  , blockIdx := f.blockIdx
  , stmtIdx := f.stmtIdx
  , locals := f.locals }

/-- Lift a Day-1 `FrameState` to `OpenFrameState`. -/
noncomputable def OpenFrameState.ofFrameState (f : FrameState) :
    OpenFrameState :=
  { defId := f.defId
  , blockIdx := f.blockIdx
  , stmtIdx := f.stmtIdx
  , locals := f.locals
  , retDst := none }

/-- Project an `OpenState` to Day-1 `State`. -/
noncomputable def OpenState.toState (s : OpenState) : State :=
  { frames := s.frames.map OpenFrameState.toFrameState
  , callerMem := s.callerMem
  , mem := s.mem }

/-- Lift a Day-1 `State` to `OpenState`. -/
noncomputable def OpenState.ofState (s : State) : OpenState :=
  { frames := s.frames.map OpenFrameState.ofFrameState
  , callerMem := s.callerMem
  , mem := s.mem }

/-- Lift a Day-1 `StepResult State TerminalOut` to
`StepResult OpenState TerminalOut`. -/
noncomputable def liftStepResult :
    StepResult State TerminalOut → StepResult OpenState TerminalOut
  | .step next => .step (OpenState.ofState next)
  | .done out => .done out
  | .fault kind => .fault kind

/-- Check whether `roles` is a `ByteRole` list equal to `expected`. -/
noncomputable def byteRolesBeq : List ByteRole → List ByteRole → Bool
  | [], [] => true
  | r₁ :: rs₁, r₂ :: rs₂ => ByteRole.beq r₁ r₂ && byteRolesBeq rs₁ rs₂
  | _, _ => false

/-- Check whether a scalar `sv` fits `roles` consisting of `sv.width.byteSize`
`.intRange min max sv.width` roles with `min ≤ sv.bits.toNat ≤ max`. -/
noncomputable def checkScalarRoles (sv : ScalarVal) : List ByteRole → Bool
  | [] => false
  | .valueByte (.intRange min max w) :: rest =>
      let n := w.byteSize
      let expected := repeatItem (.valueByte (.intRange min max w)) n
      sv.wf &&
      IntWidth.beq sv.width w &&
      byteRolesBeq (.valueByte (.intRange min max w) :: rest) expected &&
      Nat.ble min sv.bits.toNat &&
      Nat.ble sv.bits.toNat max
  | _ => false

/-- Check whether pointer `p` fits `roles` for a thin (8-byte) or wide
slice (16-byte) reference or raw pointer, enforcing `allocId.isSome` and
offset alignment when `isRef = true`. -/
noncomputable def checkPtrRoles (p : PtrVal) (roles : List ByteRole) : Bool :=
  if !IntWidth.beq p.width .isize then
    false
  else
    match takeSplit? 8 roles with
    | some (hd8, tl) =>
        match hd8 with
        | .valueByte (.refPtr align isRef) :: _ =>
            allRolesMatchExact (.valueByte (.refPtr align isRef)) hd8 &&
            (if isRef then
               p.allocId.isSome &&
               Nat.beq (Nat.mod p.offsetBytes.toNat (Nat.pow 2 align)) 0
             else
               true) &&
            match tl with
            | [] => true
            | _ :: _ =>
                Nat.beq tl.length 8 &&
                allRolesMatchExact (.valueByte (.intRange 0 isizeMax .isize)) tl
        | _ => false
    | none => false

/-- Check a `Val` strictly against an evaluated `TypeLayoutSpec`. Rejects all
values when `spec.inhabited = false`, validates `.bytes` via `LangValidBool`
(using slice element count rather than byte length for unsized slices), and
enforces exact role/tag matching for `.bool`, `.ordering`, `.char`, `.unit`,
`.enumVal`, `.scalar`, `.ptr`, and `.tuple`. -/
noncomputable def checkValAgainstSpec (v : Val) (spec : TypeLayoutSpec) :
    Bool :=
  if !spec.inhabited then
    false
  else
    match v with
    | .bytes bs =>
        if spec.isSized then
          LangValidBool spec .none bs
        else
          match spec.sizeForMeta (.sliceLen 1) with
          | none => false
          | some 0 => bs.isEmpty && LangValidBool spec (.sliceLen 0) []
          | some elemSz =>
              let elemCount := Nat.div bs.length elemSz
              Nat.beq (elemSz * elemCount) bs.length &&
              LangValidBool spec (.sliceLen elemCount) bs
    | .bool _ =>
        spec.isSized &&
        spec.enumTy?.isNone &&
        match spec.rolesForMeta .none with
        | some rs => byteRolesBeq rs [.valueByte .boolByte]
        | none => false
    | .ordering _ =>
        spec.isSized &&
        spec.enumTy?.isNone &&
        match spec.rolesForMeta .none with
        | some rs => byteRolesBeq rs [.valueByte .orderingByte]
        | none => false
    | .char c =>
        spec.isSized &&
        spec.enumTy?.isNone &&
        isUnicodeScalar c.toNat &&
        match spec.rolesForMeta .none with
        | some rs => byteRolesBeq rs charRoles
        | none => false
    | .unit =>
        spec.isSized &&
        spec.enumTy?.isNone &&
        match spec.sizeForMeta .none, spec.rolesForMeta .none with
        | some 0, some [] => true
        | _, _ => false
    | .enumVal ety varIdx =>
        spec.isSized &&
        enumAdmitted ety &&
        Nat.blt varIdx ety.discriminants.length &&
        match spec.enumTy?, enumTypeLayoutSpec ety with
        | some ety', some eSpec =>
            EnumTy.beq ety ety' &&
            match spec.sizeForMeta .none, eSpec.sizeForMeta .none,
                  spec.rolesForMeta .none, eSpec.rolesForMeta .none with
            | some s₁, some s₂, some r₁, some r₂ =>
                Nat.beq s₁ s₂ && byteRolesBeq r₁ r₂
            | _, _, _, _ => false
        | _, _ => false
    | .scalar sv =>
        spec.isSized &&
        spec.enumTy?.isNone &&
        match spec.rolesForMeta .none with
        | some rs => checkScalarRoles sv rs
        | none => false
    | .ptr p =>
        spec.isSized &&
        spec.enumTy?.isNone &&
        match spec.rolesForMeta .none with
        | some rs => checkPtrRoles p rs
        | none => false
    | .tuple [.scalar sv, .bool _] =>
        spec.isSized &&
        sv.wf &&
        spec.enumTy?.isNone &&
        let opSpec := overflowPairTypeLayoutSpec sv.width
        match spec.sizeForMeta .none, opSpec.sizeForMeta .none,
              spec.rolesForMeta .none, opSpec.rolesForMeta .none with
        | some s₁, some s₂, some r₁, some r₂ =>
            Nat.beq s₁ s₂ && byteRolesBeq r₁ r₂
        | _, _, _, _ => false
    | .tuple _ | .slicePtr _ _ | .rangeTo _ | .rangeFrom _ => false

/-- Check a `Val` against an optional `TypeLayoutSpec`. -/
noncomputable def checkOpenValOnSpec (v : Val) :
    Option TypeLayoutSpec → Bool
  | none => false
  | some spec => checkValAgainstSpec v spec

/-- Whether `ty` avoids closed Day-1 `MirTy` forms outside
`isSupportedScalarOrUnitTy` (rejecting closed Day-1 `.ref`, `.rawPtr`,
non-overflow `.tuple`, and unadmitted `.enum` types that Day-1 `initState` /
`evalStep` and `OpenSemantics` with empty `CallerMemory` cannot faithfully
execute). -/
noncomputable def openClosedTySupported (reg : TraitRegistry)
    (ty : OpenMirTy) : Bool :=
  match OpenMirTy.toClosedMirTy? (normalizeOpenTy reg normFuel ty) with
  | some mty => isSupportedScalarOrUnitTy mty
  | none => true

/-- Check whether `v` is valid at open type `ty` under `env`. Supports Day-1
closed scalar/enum/overflow-pair values (`checkVal` when
`isSupportedScalarOrUnitTy` holds) and reference/pointer/slice/array/ADT/open
values whose `evalOpenTySpec` succeeds with a `TypeLayoutSpec`. -/
noncomputable def checkOpenVal (prog : OpenProgram) (env : OpenExecEnv)
    (v : Val) (ty : OpenMirTy) : Bool :=
  match OpenMirTy.toClosedMirTy? ty with
  | some mty =>
      if isSupportedScalarOrUnitTy mty then checkVal v mty
      else checkOpenValOnSpec v
        (evalOpenTySpec prog.traitRegistry normFuel env.typeSpecs ty)
  | none =>
      checkOpenValOnSpec v
        (evalOpenTySpec prog.traitRegistry normFuel env.typeSpecs ty)

/-- Check argument list matching against open parameter types. -/
noncomputable def checkOpenArgsMatch (prog : OpenProgram) (env : OpenExecEnv) :
    List Val → List OpenMirTy → Bool
  | [], [] => true
  | v :: vs, t :: ts =>
      checkOpenVal prog env v t && checkOpenArgsMatch prog env vs ts
  | _, _ => false

/-- Check that every byte-slice value passed for a type parameter `.param i`
satisfies the corresponding invariant in `env.typeSpecs.paramInvs`. -/
def argsSatisfyParamInvs (prog : OpenProgram)
    (env : OpenExecEnv) :
    List Val → List OpenMirTy → Prop
  | [], [] => True
  | v :: vs, t :: ts =>
      let headOk : Prop :=
        match normalizeOpenTy prog.traitRegistry normFuel t, v with
        | .param i, .bytes bs =>
            match openListGet? env.typeSpecs.paramInvs i with
            | some inv => inv bs
            | none => True
        | _, _ => True
      headOk ∧ argsSatisfyParamInvs prog env vs ts
  | _, _ => False

/-- Check whether any basic block in `ob` has a `StorageLive`/`StorageDead`
marker for `localId`. -/
noncomputable def openHasStorageAnnotation (ob : OpenBody)
    (localId : LocalId) : Bool :=
  ob.basicBlocks.any (fun bb =>
    bb.statements.any (fun st =>
      match st with
      | .storageLive id | .storageDead id => Nat.beq id localId
      | _ => false))

/-- Initial live slot value for `ty` in open execution (preserving inhabited ZST
unit and ZST enum values matching `liveUninitSlot` in
`Trusted.MirSemantics.Enum`). -/
noncomputable def openLiveUninitSlot (prog : OpenProgram) (ty : OpenMirTy) :
    LocalSlot :=
  match OpenMirTy.toClosedMirTy?
      (normalizeOpenTy prog.traitRegistry normFuel ty) with
  | some mty => liveUninitSlot mty
  | none => .immediate none

/-- Recursive slot initializer for `initOpenLocals`: keeps `_0` live
(`openLiveUninitSlot`) regardless of storage markers and initializes
unannotated locals above `argumentCount` via `openLiveUninitSlot`, matching
`initLocalsLoop` in `Trusted.MirSemantics.State`. -/
noncomputable def initOpenLocalsBuild (prog : OpenProgram) (ob : OpenBody) :
    Nat → List OpenMirTy → List Val → Option (List LocalSlot)
  | _, [], [] => some []
  | 0, ty :: restTys, vs =>
      let slot := openLiveUninitSlot prog ty
      match initOpenLocalsBuild prog ob 1 restTys vs with
      | some rest => some (slot :: rest)
      | none => none
  | idx + 1, _ :: restTys, v :: vs =>
      match initOpenLocalsBuild prog ob (idx + 2) restTys vs with
      | some rest => some (.immediate (some v) :: rest)
      | none => none
  | idx + 1, ty :: restTys, [] =>
      let slot :=
        if openHasStorageAnnotation ob (idx + 1) then
          .dead
        else
          openLiveUninitSlot prog ty
      match initOpenLocalsBuild prog ob (idx + 2) restTys [] with
      | some rest => some (slot :: rest)
      | none => none
  | _, [], _ :: _ => none

/-- Build initial local slots for `ob` and entry `args` (mirroring
`Trusted.MirSemantics.initState`). -/
noncomputable def initOpenLocals (prog : OpenProgram) (env : OpenExecEnv)
    (ob : OpenBody) (args : List Val) : Option (List LocalSlot) :=
  let paramTys := (ob.locals.drop 1).take ob.argumentCount
  if !Nat.beq args.length ob.argumentCount ||
     !Nat.beq paramTys.length ob.argumentCount ||
     !Nat.blt ob.argumentCount ob.locals.length ||
     !checkOpenArgsMatch prog env args paramTys then
    none
  else
    initOpenLocalsBuild prog ob 0 ob.locals args

/-- Helper for `openInitState` parameterized by `OpenProgram.toDay1? prog`. -/
noncomputable def openInitStateAux (prog : OpenProgram) (env : OpenExecEnv)
    (q : Query) : Option Program → Except FaultKind OpenState
  | some day1Prog =>
      match initState day1Prog q with
      | .ok s => .ok (OpenState.ofState s)
      | .error k => .error k
  | none =>
      if !q.callerMem.allocations.isEmpty then
        .error .unsupported
      else
        match openListGet? prog.bodies prog.entryDefId with
        | none => .error .unsupported
        | some body =>
            if !Nat.beq prog.pointerWidthBits 64 ||
               !Nat.beq prog.mirProfileVersion 1 ||
               body.basicBlocks.isEmpty ||
               !Nat.blt body.argumentCount body.locals.length then
              .error .unsupported
            else
              match initOpenLocals prog env body q.args with
              | none => .error .unsupported
              | some locals =>
                  .ok
                    { frames :=
                        [{ defId := prog.entryDefId
                         , blockIdx := 0
                         , stmtIdx := 0
                         , locals := locals
                         , retDst := none }]
                    , callerMem := ⟨[]⟩
                    , mem := MemoryState.empty }

/-- Initialize an `OpenState` for `(prog, env, q)`. If `OpenProgram.toDay1?`
succeeds on `prog`, delegates directly to Day-1 `initState`. -/
noncomputable def openInitState (prog : OpenProgram) (env : OpenExecEnv)
    (q : Query) : Except FaultKind OpenState :=
  openInitStateAux prog env q (OpenProgram.toDay1? prog)

/-- Evaluate an `OpenOperand` to `(val, ty, frame')`, checking local bounds
and `.dead` liveness before inspecting projections (matching
`eval_place_to_op` in `compiler/rustc_const_eval/src/interpret/operand.rs`,
`rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) and preserving
ZST values on `.move` via `openLiveUninitSlot`. -/
noncomputable def evalOpenOperand (prog : OpenProgram) (env : OpenExecEnv)
    (ob : OpenBody) (frame : OpenFrameState) :
    OpenOperand → Except FaultKind (Val × OpenMirTy × OpenFrameState)
  | .copy p =>
      match openListGet? ob.locals p.localId,
            Trusted.MirSemantics.getElem? frame.locals p.localId with
      | some _, some .dead => .error .undefined
      | some ty, some (.immediate optVal) =>
          if !p.projection.isEmpty then
            .error .unsupported
          else
            match optVal with
            | some v => .ok (v, ty, frame)
            | none => .error .undefined
      | _, _ => .error .unsupported
  | .move p =>
      match openListGet? ob.locals p.localId,
            Trusted.MirSemantics.getElem? frame.locals p.localId with
      | some _, some .dead => .error .undefined
      | some ty, some (.immediate optVal) =>
          if !p.projection.isEmpty then
            .error .unsupported
          else
            match optVal with
            | some v =>
                match setElem? frame.locals p.localId
                        (openLiveUninitSlot prog ty) with
                | some ls' => .ok (v, ty, { frame with locals := ls' })
                | none => .error .unsupported
            | none => .error .undefined
      | _, _ => .error .unsupported
  | .constant c =>
      match OpenMirTy.toClosedMirTy? c.ty with
      | some mty =>
          match evalConstLit mty c.lit with
          | .ok v => .ok (v, c.ty, frame)
          | .error k => .error k
      | none =>
          match c.lit, evalOpenTySpec
                  prog.traitRegistry normFuel env.typeSpecs c.ty with
          | .zeroSized, some sp =>
              if sp.isSized && sp.inhabited &&
                 Nat.beq ((sp.sizeForMeta .none).getD 1) 0 &&
                 match sp.rolesForMeta .none with | some [] => true | _ => false
              then
                .ok (.bytes [], c.ty, frame)
              else
                .error .unsupported
          | _, _ => .error .unsupported

/-- Evaluate a list of `OpenOperand` left-to-right. -/
noncomputable def evalOpenOperands (prog : OpenProgram) (env : OpenExecEnv)
    (ob : OpenBody) (frame : OpenFrameState) :
    List OpenOperand → Except FaultKind (List Val × OpenFrameState)
  | [] => .ok ([], frame)
  | op :: ops =>
      match evalOpenOperand prog env ob frame op with
      | .error k => .error k
      | .ok (v, _, f₁) =>
          match evalOpenOperands prog env ob f₁ ops with
          | .error k => .error k
          | .ok (vs, f₂) => .ok (v :: vs, f₂)

/-- Write a `Val` to an unprojected `OpenPlace` in `frame`, verifying `dst`
bounds, projection emptiness, `checkOpenVal` at `dstTy`, and local liveness.
Matches `eval_rvalue_into_place` (`interpret/step.rs`) and
`write_immediate_no_validate` (`interpret/place.rs`) under
`compiler/rustc_const_eval/src/interpret/` (`rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`). -/
noncomputable def writeOpenPlace (prog : OpenProgram) (env : OpenExecEnv)
    (ob : OpenBody) (frame : OpenFrameState) (dst : OpenPlace)
    (v : Val) : Except FaultKind OpenFrameState :=
  if !dst.projection.isEmpty then
    .error .unsupported
  else
    match openListGet? ob.locals dst.localId with
    | none => .error .unsupported
    | some dstTy =>
        if !checkOpenVal prog env v dstTy then
          .error .unsupported
        else
          match Trusted.MirSemantics.getElem? frame.locals dst.localId with
          | none => .error .unsupported
          | some .dead => .error .undefined
          | some (.immediate _) =>
              match setElem? frame.locals dst.localId (.immediate (some v)) with
              | some ls' => .ok { frame with locals := ls' }
              | none => .error .unsupported
          | some (.indirect _) => .error .unsupported
          | some (.partialTuple _) => .error .unsupported

/-- Resolve the `count` associated-type layout specifications for
`(selfTy as Trait<args>)::0..(count - 1)` in `env.typeSpecs`. -/
noncomputable def resolveTraitAssocSpecsAux (prog : OpenProgram)
    (env : OpenExecEnv) (selfTy : OpenMirTy) (tr : TraitDefId)
    (args : List OpenMirTy) (idx : Nat) :
    Nat → Option (List TypeLayoutSpec)
  | 0 => some []
  | rem + 1 =>
      match evalOpenTySpec prog.traitRegistry normFuel env.typeSpecs
              (.assocProj selfTy tr args idx),
            resolveTraitAssocSpecsAux prog env selfTy tr args (idx + 1) rem with
      | some sp, some rest => some (sp :: rest)
      | _, _ => none

/-- Resolve all `assocCount` associated-type specs for a trait bound. -/
noncomputable def resolveTraitAssocSpecs (prog : OpenProgram)
    (env : OpenExecEnv) (selfTy : OpenMirTy) (tr : TraitDefId)
    (args : List OpenMirTy) (assocCount : Nat) :
    Option (List TypeLayoutSpec) :=
  resolveTraitAssocSpecsAux prog env selfTy tr args 0 assocCount

/-- Propagate an unwind from `restFrames` using `uw` (when `restFrames` is empty
under `.continue_`, terminates `.done (.unwound cm)`; `.terminate` fails closed
with `.fault .unsupported` since `TerminalOut` has no abort variant). -/
noncomputable def openUnwindWith (s : OpenState) (cm : CallerMemory)
    (restFrames : List OpenFrameState) (uw : UnwindAction)
    (callerFrame? : Option OpenFrameState := none) :
    StepResult OpenState TerminalOut :=
  match uw with
  | .continue_ =>
      match restFrames with
      | [] => .done (.unwound cm)
      | caller :: tail =>
          match caller.retDst with
          | some (_, _, callerUw) =>
              openUnwindWith { s with callerMem := cm } cm tail callerUw none
          | none => .fault .unsupported
  | .unreachable => .fault .undefined
  | .terminate => .fault .unsupported
  | .cleanup blk =>
      match callerFrame? with
      | some f =>
          .step
            { frames := { f with blockIdx := blk, stmtIdx := 0 } :: restFrames
            , callerMem := cm
            , mem := s.mem }
      | none =>
          match restFrames with
          | caller :: tail =>
              .step
                { frames :=
                    { caller with blockIdx := blk, stmtIdx := 0 } :: tail
                , callerMem := cm
                , mem := s.mem }
          | [] => .fault .unsupported

mutual
  /-- Whether `OpenMirTy` contains zero `.param` nodes. -/
  noncomputable def openMirTyNoParam : OpenMirTy → Bool
    | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
    | .unsupported => true
    | .param _ => false
    | .slice e | .array e _ | .ref _ e | .rawPtr _ e => openMirTyNoParam e
    | .tuple fs | .adt _ fs => openMirTyListNoParam fs
    | .assocProj s _ args _ =>
        openMirTyNoParam s && openMirTyListNoParam args

  /-- Elementwise `.param`-absence check on `List OpenMirTy`. -/
  noncomputable def openMirTyListNoParam : List OpenMirTy → Bool
    | [] => true
    | x :: xs => openMirTyNoParam x && openMirTyListNoParam xs
end

/-- Whether `OpenPlace` contains zero `.param` nodes. -/
noncomputable def openPlaceNoParam (p : OpenPlace) : Bool :=
  p.projection.all fun
    | .deref | .unsupported => true
    | .field _ ty => openMirTyNoParam ty

/-- Whether `OpenOperand` contains zero `.param` nodes. -/
noncomputable def openOperandNoParam : OpenOperand → Bool
  | .copy p | .move p => openPlaceNoParam p
  | .constant c => openMirTyNoParam c.ty

/-- Whether `OpenRvalue` contains zero `.param` nodes. -/
noncomputable def openRvalueNoParam : OpenRvalue → Bool
  | .use op | .unaryOp _ op => openOperandNoParam op
  | .binaryOp _ lhs rhs => openOperandNoParam lhs && openOperandNoParam rhs
  | .cast _ op ty => openOperandNoParam op && openMirTyNoParam ty
  | .discriminant p | .ref _ p | .addressOf _ p => openPlaceNoParam p
  | .aggregateTuple fs => fs.all openOperandNoParam
  | .unsupported => true

/-- Whether `OpenStatementKind` contains zero `.param` nodes. -/
noncomputable def openStmtNoParam : OpenStatementKind → Bool
  | .assign dst rv => openPlaceNoParam dst && openRvalueNoParam rv
  | .storageLive _ | .storageDead _ | .nop | .unsupported => true

/-- Whether `OpenTerminatorKind` contains zero `.param` nodes. -/
noncomputable def openTermNoParam : OpenTerminatorKind → Bool
  | .goto _ | .return_ | .unreachable | .unwindResume | .unsupported => true
  | .switchInt op _ | .assert op _ _ _ _ => openOperandNoParam op
  | .call _ substs args dst _ _ =>
      openMirTyListNoParam substs && args.all openOperandNoParam &&
      openPlaceNoParam dst
  | .traitCall selfTy _ trArgs _ args dst _ _ =>
      openMirTyNoParam selfTy && openMirTyListNoParam trArgs &&
      args.all openOperandNoParam && openPlaceNoParam dst

/-- Whether `WhereClause` contains zero `.param` nodes. -/
noncomputable def openWhereNoParam : WhereClause → Bool
  | .traitBound selfTy _ args =>
      openMirTyNoParam selfTy && openMirTyListNoParam args
  | .isSized ty => openMirTyNoParam ty
  | .typeEq l r => openMirTyNoParam l && openMirTyNoParam r

mutual
  /-- Whether every `.param id` in an `OpenMirTy` satisfies `id < bound`. -/
  noncomputable def openMirTyParamsLt (bound : Nat) : OpenMirTy → Bool
    | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
    | .unsupported => true
    | .param id => Nat.blt id bound
    | .slice e | .array e _ | .ref _ e | .rawPtr _ e =>
        openMirTyParamsLt bound e
    | .tuple fs | .adt _ fs => openMirTyListParamsLt bound fs
    | .assocProj s _ args _ =>
        openMirTyParamsLt bound s && openMirTyListParamsLt bound args

  /-- Elementwise `.param`-bound check on `List OpenMirTy`. -/
  noncomputable def openMirTyListParamsLt (bound : Nat) :
      List OpenMirTy → Bool
    | [] => true
    | x :: xs => openMirTyParamsLt bound x && openMirTyListParamsLt bound xs
end

/-- Whether every `.param id` in a `WhereClause` satisfies `id < bound`. -/
noncomputable def openWhereParamsLt (bound : Nat) : WhereClause → Bool
  | .traitBound selfTy _ args =>
      openMirTyParamsLt bound selfTy && openMirTyListParamsLt bound args
  | .isSized ty => openMirTyParamsLt bound ty
  | .typeEq l r =>
      openMirTyParamsLt bound l && openMirTyParamsLt bound r

/-- Whether every `.param id` in `sig.{argTys, retTy, whereClauses}`
satisfies `id < bound`. -/
noncomputable def traitMethodSigParamsLt (bound : Nat)
    (sig : TraitMethodSig) : Bool :=
  openMirTyListParamsLt bound sig.argTys &&
  openMirTyParamsLt bound sig.retTy &&
  sig.whereClauses.all (openWhereParamsLt bound)

/-- Whether an `OpenBody` contains zero `.param` nodes (as required for
monomorphic trait-impl methods with `sig.tyParamCount = 0`). -/
noncomputable def openBodyNoParam (ob : OpenBody) : Bool :=
  openMirTyListNoParam ob.locals &&
  openMirTyListNoParam ob.sig.argTys &&
  openMirTyNoParam ob.sig.retTy &&
  ob.sig.whereClauses.all openWhereNoParam &&
  ob.basicBlocks.all fun bb =>
    bb.statements.all openStmtNoParam && openTermNoParam bb.terminator

/-- Assume-guarantee transition relation for an open `.traitCall` whose
receiver/arguments are not yet closed. Passes `[selfSpec] ++ traitArgSpecs` and
resolved `assocSpecs` to `mspec.{pre,post}`, checks `mspec.sig.whereClauses`,
validates argument and return types (`checkOpenArgsMatch` / `checkOpenVal`),
and faults `.undefined` if `mspec.post` violates return-type validity. -/
def AssumeGuaranteeTraitCall (prog : OpenProgram)
    (env : OpenExecEnv) (assumedWhere : List WhereClause)
    (s : OpenState) (ob : OpenBody) (frame : OpenFrameState)
    (restFrames : List OpenFrameState) (selfTy : OpenMirTy) (tr : TraitDefId)
    (traitArgs : List OpenMirTy) (methodIdx : AssocItemIdx)
    (args : List OpenOperand) (dst : OpenPlace) (target : Option BasicBlockId)
    (unwind : UnwindAction) (res : StepResult OpenState TerminalOut) : Prop :=
  let selfN := normalizeOpenTy prog.traitRegistry normFuel selfTy
  let argsN := traitArgs.map (normalizeOpenTy prog.traitRegistry normFuel)
  let bound := WhereClause.traitBound selfN tr argsN
  if !whereClauseInList bound assumedWhere then
    res = .fault .unsupported
  else
    match env.traitContracts tr with
    | none => res = .fault .unsupported
    | some contract =>
        if !Nat.beq argsN.length contract.tyParamCount then
          res = .fault .unsupported
        else
          match lookupMethodSpec contract.methodSpecs methodIdx with
          | none => res = .fault .unsupported
          | some mspec =>
              let substList := selfN :: argsN
              let normSubst :=
                OpenMirTy.substAndNormalize prog.traitRegistry normFuel
                  substList
              let instArgTys := mspec.sig.argTys.map normSubst
              let instRetTy := normSubst mspec.sig.retTy
              let instWcs := mspec.sig.whereClauses.map (fun wc =>
                match wc with
                | .traitBound st tr' as' =>
                    .traitBound (normSubst st) tr' (as'.map normSubst)
                | .isSized t => .isSized (normSubst t)
                | .typeEq l r => .typeEq (normSubst l) (normSubst r))
              if !traitMethodSigParamsLt substList.length mspec.sig ||
                 !allWhereInList assumedWhere instWcs then
                res = .fault .unsupported
              else
                match openListGet? ob.locals dst.localId with
                | none => res = .fault .unsupported
                | some dstTy =>
                    let dstN :=
                      normalizeOpenTy prog.traitRegistry normFuel dstTy
                    if !OpenMirTy.beq dstN instRetTy ||
                       (openMirTyNoParam selfN &&
                        openMirTyListNoParam argsN &&
                        (!openMirTyListNoParam instArgTys ||
                         !openMirTyNoParam instRetTy ||
                         !instWcs.all openWhereNoParam)) then
                      res = .fault .unsupported
                    else
                      match evalOpenTySpec prog.traitRegistry normFuel
                              env.typeSpecs selfN,
                            evalNormOpenTySpecList env.typeSpecs argsN,
                            resolveTraitAssocSpecs prog env selfN tr argsN
                              contract.assocTypeCount with
                      | some selfSpec, some argSpecs, some assocSpecs =>
                          match evalOpenOperands prog env ob frame args with
                          | .error k => res = .fault k
                          | .ok (argVals, frame₁) =>
                              if !checkOpenArgsMatch prog env argVals
                                    instArgTys then
                                res = .fault .unsupported
                              else
                                let specArgs := selfSpec :: argSpecs
                                (¬ mspec.pre specArgs assocSpecs argVals
                                      s.callerMem ∧
                                  res = .fault .undefined) ∨
                                (mspec.pre specArgs assocSpecs argVals
                                    s.callerMem ∧
                                  ∃ out : TerminalOut,
                                    mspec.post specArgs assocSpecs argVals
                                      s.callerMem out ∧
                                    match out with
                                    | .returned ⟨retVal, cm'⟩ =>
                                        if !checkOpenVal prog env retVal
                                              instRetTy then
                                          res = .fault .undefined
                                        else
                                          match target with
                                          | none => res = .fault .undefined
                                          | some nextBlk =>
                                              match writeOpenPlace prog env ob
                                                      frame₁ dst retVal with
                                              | .error k => res = .fault k
                                              | .ok frame₂ =>
                                                  let nextFrame :
                                                      OpenFrameState :=
                                                    { frame₂ with
                                                      blockIdx := nextBlk
                                                      stmtIdx := 0 }
                                                  res = .step
                                                    { frames :=
                                                        nextFrame :: restFrames
                                                    , callerMem := cm'
                                                    , mem := s.mem }
                                    | .unwound cm' =>
                                        res = openUnwindWith s cm' restFrames
                                          unwind (some frame₁))
                      | _, _, _ => res = .fault .unsupported

/-- Helper for `openEvalDetStep` parameterized by `OpenProgram.toDay1? prog`.
When `toDay1? prog` is `some day1Prog`, delegates directly to Day-1 `evalStep`;
when `none`, evaluates open statements and non-call terminators (`StorageDead 0`
and `.ref`/`.addressOf` fault `.unsupported`, `Assign` enforces normalized type
equality, `.switchInt` requires closed primitive discriminant types, and
`.assert`, `.unwindResume`, and nested `retDst` frames step via
`openUnwindWith` rather than faulting `.unsupported` as in Day-1 `Step.lean`).
-/
noncomputable def openEvalDetStepAux (prog : OpenProgram) (env : OpenExecEnv)
    (s : OpenState) : Option Program → StepResult OpenState TerminalOut
  | some day1Prog => liftStepResult (evalStep day1Prog 0 (OpenState.toState s))
  | none =>
      match s.frames with
      | frame :: restFrames =>
          match openListGet? prog.bodies frame.defId with
          | none => .fault .unsupported
          | some ob =>
              match openListGet? ob.basicBlocks frame.blockIdx with
              | none => .fault .unsupported
              | some bb =>
                  match openListGet? bb.statements frame.stmtIdx with
                  | some stmt =>
                      match stmt with
                      | .nop =>
                          .step
                            { s with
                              frames :=
                                { frame with stmtIdx := frame.stmtIdx + 1 } ::
                                restFrames }
                      | .storageLive lid =>
                          match openListGet? ob.locals lid,
                                Trusted.MirSemantics.getElem? frame.locals lid
                              with
                          | some ty, some old =>
                              match setElem? frame.locals lid
                                      (openLiveUninitSlot prog ty) with
                              | some ls' =>
                                  match deallocateLocal s.mem old with
                                  | .error k => .fault k
                                  | .ok mem' =>
                                      .step
                                        { s with
                                          frames :=
                                            { frame with
                                              stmtIdx := frame.stmtIdx + 1
                                              locals := ls' } :: restFrames
                                          mem := mem' }
                              | none => .fault .unsupported
                          | _, _ => .fault .unsupported
                      | .storageDead lid =>
                          if Nat.beq lid 0 then
                            .fault .unsupported
                          else
                            match Trusted.MirSemantics.getElem? frame.locals lid
                                with
                            | none => .fault .unsupported
                            | some old =>
                                match setElem? frame.locals lid .dead with
                                | some ls' =>
                                    match deallocateLocal s.mem old with
                                    | .error k => .fault k
                                    | .ok mem' =>
                                        .step
                                          { s with
                                            frames :=
                                              { frame with
                                                stmtIdx := frame.stmtIdx + 1
                                                locals := ls' } :: restFrames
                                            mem := mem' }
                                | none => .fault .unsupported
                      | .assign dst rv =>
                          if !dst.projection.isEmpty then
                            .fault .unsupported
                          else
                            match openListGet? ob.locals dst.localId with
                            | none => .fault .unsupported
                            | some dstTy =>
                                let dstN :=
                                  normalizeOpenTy prog.traitRegistry normFuel
                                    dstTy
                                match rv with
                                | .use op =>
                                    match evalOpenOperand prog env ob frame
                                            op with
                                    | .error k => .fault k
                                    | .ok (v, srcTy, f₁) =>
                                        let srcN :=
                                          normalizeOpenTy prog.traitRegistry
                                            normFuel srcTy
                                        if !OpenMirTy.beq srcN dstN then
                                          .fault .unsupported
                                        else
                                          match writeOpenPlace prog env ob f₁
                                                  dst v with
                                          | .error k => .fault k
                                          | .ok f₂ =>
                                              .step
                                                { s with
                                                  frames :=
                                                    { f₂ with
                                                      stmtIdx :=
                                                        frame.stmtIdx + 1 } ::
                                                    restFrames }
                                | .binaryOp op lhs rhs =>
                                    match evalOpenOperand prog env ob frame
                                            lhs with
                                    | .error k => .fault k
                                    | .ok (vl, srcL, f₁) =>
                                        match evalOpenOperand prog env ob f₁
                                                rhs with
                                        | .error k => .fault k
                                        | .ok (vr, srcR, f₂) =>
                                            match OpenMirTy.toClosedMirTy? srcL,
                                                  OpenMirTy.toClosedMirTy? srcR,
                                                  OpenMirTy.toClosedMirTy? dstN,
                                                  evalBinOp op vl vr with
                                            | some ml, some mr, some mDst,
                                              .ok resV =>
                                                if !isPrimitiveReadableTy ml ||
                                                   !isPrimitiveReadableTy mr ||
                                                   !checkVal resV mDst
                                                then
                                                  .fault .unsupported
                                                else
                                                  match writeOpenPlace prog env
                                                          ob f₂ dst resV with
                                                  | .error k => .fault k
                                                  | .ok f₃ =>
                                                      .step
                                                        { s with
                                                          frames :=
                                                            { f₃ with
                                                              stmtIdx :=
                                                                frame.stmtIdx +
                                                                  1 } ::
                                                            restFrames }
                                            | _, _, _, .error k => .fault k
                                            | _, _, _, _ => .fault .unsupported
                                | .unaryOp op opnd =>
                                    match evalOpenOperand prog env ob frame
                                            opnd with
                                    | .error k => .fault k
                                    | .ok (v, srcTy, f₁) =>
                                        match OpenMirTy.toClosedMirTy? srcTy,
                                              OpenMirTy.toClosedMirTy? dstN,
                                              evalUnOp op v with
                                        | some mSrc, some mDst, .ok resV =>
                                            if !isPrimitiveReadableTy mSrc ||
                                               !checkVal resV mDst then
                                              .fault .unsupported
                                            else
                                              match writeOpenPlace prog env ob
                                                      f₁ dst resV with
                                              | .error k => .fault k
                                              | .ok f₂ =>
                                                  .step
                                                    { s with
                                                      frames :=
                                                        { f₂ with
                                                          stmtIdx :=
                                                            frame.stmtIdx + 1 }
                                                        :: restFrames }
                                        | _, _, .error k => .fault k
                                        | _, _, _ => .fault .unsupported
                                | .cast .intToInt opnd castTy =>
                                    let castN :=
                                      normalizeOpenTy prog.traitRegistry
                                        normFuel castTy
                                    if !OpenMirTy.beq castN dstN then
                                      .fault .unsupported
                                    else
                                      match evalOpenOperand prog env ob frame
                                              opnd,
                                            OpenMirTy.toClosedMirTy? castN with
                                      | .ok (v, srcTy, f₁), some mCast =>
                                          match OpenMirTy.toClosedMirTy?
                                                  srcTy with
                                          | some mSrc =>
                                              if !isIntLikeTy mSrc then
                                                .fault .unsupported
                                              else
                                                match evalIntToIntCast v
                                                        mCast with
                                                | .error k => .fault k
                                                | .ok resV =>
                                                    match writeOpenPlace prog
                                                            env ob f₁ dst
                                                            resV with
                                                    | .error k => .fault k
                                                    | .ok f₂ =>
                                                        .step
                                                          { s with
                                                            frames :=
                                                              { f₂ with
                                                                stmtIdx :=
                                                                  frame.stmtIdx
                                                                    + 1 } ::
                                                              restFrames }
                                          | none => .fault .unsupported
                                      | .error k, _ => .fault k
                                      | _, none => .fault .unsupported
                                | _ => .fault .unsupported
                      | .unsupported => .fault .unsupported
                  | none =>
                      if !Nat.beq frame.stmtIdx bb.statements.length then
                        .fault .unsupported
                      else
                        match bb.terminator with
                        | .goto tgt =>
                            .step
                              { s with
                                frames :=
                                  { frame with blockIdx := tgt, stmtIdx := 0 }
                                  :: restFrames }
                        | .return_ =>
                            if bb.cleanup then
                              .fault .unsupported
                            else
                              match Trusted.MirSemantics.getElem? frame.locals 0
                                  with
                              | some (.immediate (some retV)) =>
                                  match restFrames with
                                  | [] => .done (.returned ⟨retV, s.callerMem⟩)
                                  | caller :: tail =>
                                      match frame.retDst with
                                      | some (dst, some retBlk, _) =>
                                          match openListGet? prog.bodies
                                                  caller.defId with
                                          | some callerBody =>
                                              match writeOpenPlace prog env
                                                      callerBody caller dst
                                                      retV with
                                              | .error k => .fault k
                                              | .ok caller' =>
                                                  .step
                                                    { s with
                                                      frames :=
                                                        { caller' with
                                                          blockIdx := retBlk
                                                          stmtIdx := 0 } ::
                                                        tail }
                                          | none => .fault .unsupported
                                      | some (_, none, _) => .fault .undefined
                                      | none => .fault .unsupported
                              | some (.immediate none) | some .dead =>
                                  .fault .undefined
                              | _ => .fault .unsupported
                        | .unreachable => .fault .undefined
                        | .unwindResume =>
                            if !bb.cleanup then
                              .fault .unsupported
                            else
                              match restFrames with
                              | [] => .done (.unwound s.callerMem)
                              | _ =>
                                  match frame.retDst with
                                  | some (_, _, uw) =>
                                      openUnwindWith s s.callerMem restFrames uw
                                        none
                                  | none => .fault .unsupported
                        | .switchInt discr tgts =>
                            match evalOpenOperand prog env ob frame discr with
                            | .error k => .fault k
                            | .ok (v, discrTy, f₁) =>
                                match OpenMirTy.toClosedMirTy? discrTy with
                                | none => .fault .unsupported
                                | some mTy =>
                                    if !isPrimitiveReadableTy mTy then
                                      .fault .unsupported
                                    else
                                      let tgtRes :
                                          Except FaultKind BasicBlockId :=
                                        match v with
                                        | .scalar sv =>
                                            evalSwitchBranches sv.width sv.bits
                                              tgts.otherwise tgts.branches
                                        | .bool b =>
                                            evalBoolSwitchBranches b
                                              tgts.otherwise tgts.branches
                                        | .char c =>
                                            evalCharSwitchBranches c
                                              tgts.otherwise tgts.branches
                                        | _ =>
                                            match tgts.branches with
                                            | [] => .ok tgts.otherwise
                                            | _ :: _ => .error .unsupported
                                      match tgtRes with
                                      | .error k => .fault k
                                      | .ok tgt =>
                                          .step
                                            { s with
                                              frames :=
                                                { f₁ with
                                                  blockIdx := tgt
                                                  stmtIdx := 0 } ::
                                                restFrames }
                        | .assert cond exp _ tgt uw =>
                            match evalOpenOperand prog env ob frame cond with
                            | .error k => .fault k
                            | .ok (v, _, f₁) =>
                                match v with
                                | .bool b =>
                                    if b == exp then
                                      .step
                                        { s with
                                          frames :=
                                            { f₁ with
                                              blockIdx := tgt
                                              stmtIdx := 0 } :: restFrames }
                                    else
                                      openUnwindWith s s.callerMem restFrames uw
                                        (some f₁)
                                | _ => .fault .unsupported
                        | .call _ _ _ _ _ _ => .fault .unsupported
                        | .traitCall _ _ _ _ _ _ _ _ => .fault .unsupported
                        | .unsupported => .fault .unsupported
      | [] => .fault .unsupported

/-- Deterministic step relation for open statements and non-trait terminators.
When `OpenProgram.toDay1? prog = some day1Prog`, delegates directly to
`Trusted.MirSemantics.evalStep day1Prog 0`. -/
noncomputable def openEvalDetStep (prog : OpenProgram) (env : OpenExecEnv)
    (s : OpenState) : StepResult OpenState TerminalOut :=
  openEvalDetStepAux prog env s (OpenProgram.toDay1? prog)

/-- Check that every `StorageLive` and `StorageDead` marker in `ob` refers to
an in-bounds local index `< ob.locals.length`. -/
noncomputable def openStorageAnnotationsInBounds (ob : OpenBody) : Bool :=
  let n := ob.locals.length
  ob.basicBlocks.all (fun bb =>
    bb.statements.all (fun st =>
      match st with
      | .storageLive id | .storageDead id => Nat.blt id n
      | _ => true))

/-- Check that `Discriminant` assignments in `ob` target compatible integer
locals. -/
noncomputable def openDiscriminantTypesValid (prog : OpenProgram)
    (ob : OpenBody) : Bool :=
  ob.basicBlocks.all (fun bb =>
    bb.statements.all (fun st =>
      match st with
      | .assign dst (.discriminant src) =>
          if dst.projection.isEmpty && src.projection.isEmpty then
            match openListGet? ob.locals src.localId,
                  openListGet? ob.locals dst.localId with
            | some srcTy, some dstTy =>
                match OpenMirTy.toClosedMirTy?
                        (normalizeOpenTy prog.traitRegistry normFuel srcTy),
                      OpenMirTy.toClosedMirTy?
                        (normalizeOpenTy prog.traitRegistry normFuel dstTy) with
                | some (.enum ety), some mDst =>
                    if enumAdmitted ety then
                      MirTy.beq mDst (.int ety.discrWidth ety.discrSigned)
                    else
                      true
                | some .ordering, some mDst => MirTy.beq mDst (.int .i8 true)
                | _, _ => true
            | _, _ => true
          else
            true
      | _ => true))

/-- Check that `Cast(.intToInt, _, castTy)` destinations in `ob` agree with
`castTy` after projection normalization. -/
noncomputable def openCastTypesValid (prog : OpenProgram) (ob : OpenBody) :
    Bool :=
  ob.basicBlocks.all (fun bb =>
    bb.statements.all (fun st =>
      match st with
      | .assign dst (.cast .intToInt _ castTy) =>
          if dst.projection.isEmpty then
            match openListGet? ob.locals dst.localId with
            | some dstTy =>
                OpenMirTy.beq
                  (normalizeOpenTy prog.traitRegistry normFuel dstTy)
                  (normalizeOpenTy prog.traitRegistry normFuel castTy)
            | none => true
          else
            true
      | _ => true))

/-- Check pairwise normalized equality on two `List OpenMirTy`s. -/
noncomputable def openTyListsNormEq (reg : TraitRegistry) :
    List OpenMirTy → List OpenMirTy → Bool
  | [], [] => true
  | t₁ :: ts₁, t₂ :: ts₂ =>
      OpenMirTy.beq (normalizeOpenTy reg normFuel t₁)
        (normalizeOpenTy reg normFuel t₂) &&
      openTyListsNormEq reg ts₁ ts₂
  | _, _ => false

/-- Check that `ob.sig` (`argTys`, `retTy`, parameter count) agrees with
`ob.locals` and `ob.argumentCount`. -/
noncomputable def openSigMatchesLocals (prog : OpenProgram) (ob : OpenBody) :
    Bool :=
  Nat.beq ob.argumentCount ob.sig.argTys.length &&
  Nat.blt ob.argumentCount ob.locals.length &&
  match openListGet? ob.locals 0 with
  | none => false
  | some retLocalTy =>
      OpenMirTy.beq (normalizeOpenTy prog.traitRegistry normFuel retLocalTy)
        (normalizeOpenTy prog.traitRegistry normFuel ob.sig.retTy) &&
      openTyListsNormEq prog.traitRegistry
        ((ob.locals.drop 1).take ob.argumentCount) ob.sig.argTys

/-- Check that every local type in `ob` avoids closed unsupported Day-1 forms
(`openClosedTySupported`) and evaluates to a sized, well-formed
`TypeLayoutSpec` under `env.typeSpecs` (unsized locals cannot be immediate in
Rust MIR). -/
def openLocalsAdmitted (prog : OpenProgram) (env : OpenExecEnv) :
    List OpenMirTy → Prop
  | [] => True
  | t :: ts =>
      (∃ sp : TypeLayoutSpec,
        openClosedTySupported prog.traitRegistry t = true ∧
        evalOpenTySpec prog.traitRegistry normFuel env.typeSpecs t = some sp ∧
        WellFormedTypeLayoutSpec sp ∧
        sp.isSized = true) ∧
      openLocalsAdmitted prog env ts

/-- Environment-independent structural static admissibility checks for an open
generic body `ob` (hoisted outside `AllWhereParamsSem` in
`ParametricBodyVerified` so malformed or closed-unsupported bodies with
unsatisfiable `where`-clauses cannot pass vacuously). -/
def OpenBodyStructureValid (prog : OpenProgram) (ob : OpenBody) : Prop :=
  prog.pointerWidthBits = 64 ∧
  prog.mirProfileVersion = 1 ∧
  !stringIsEmpty ob.identity = true ∧
  !ob.basicBlocks.isEmpty = true ∧
  openSigMatchesLocals prog ob = true ∧
  openStorageAnnotationsInBounds ob = true ∧
  openDiscriminantTypesValid prog ob = true ∧
  openCastTypesValid prog ob = true ∧
  TraitRegistryWf prog.traitRegistry = true ∧
  ob.locals.all (openClosedTySupported prog.traitRegistry) = true

/-- Static admissibility judgment for an open generic body `ob`, checking target
word size, profile version, non-empty identity/blocks, `sig`/`locals`,
storage/discriminant/cast invariants, `TraitRegistryWf`, and admitted local
layout specifications. -/
def OpenBodyStaticAdmitted (prog : OpenProgram)
    (env : OpenExecEnv) (ob : OpenBody) : Prop :=
  prog.pointerWidthBits = 64 ∧
  prog.mirProfileVersion = 1 ∧
  !stringIsEmpty ob.identity = true ∧
  !ob.basicBlocks.isEmpty = true ∧
  openSigMatchesLocals prog ob = true ∧
  openStorageAnnotationsInBounds ob = true ∧
  openDiscriminantTypesValid prog ob = true ∧
  openCastTypesValid prog ob = true ∧
  TraitRegistryWf prog.traitRegistry = true ∧
  openLocalsAdmitted prog env ob.locals

/-- Concrete monomorphic trait-call execution: looks up `ImplKey` in coherent
`prog.traitRegistry`, validates unprojected destination `dst` and normalized
return type equality against `calleeBody.sig.retTy`, and pushes a fresh frame
for `calleeBody` (failing closed `.fault .unsupported` on any registry, method,
admission, destination, return-type, or argument mismatch, never falling back
to `AssumeGuaranteeTraitCall`). -/
noncomputable def concreteTraitCallStep (prog : OpenProgram) (env : OpenExecEnv)
    (s : OpenState) (ob : OpenBody) (frame : OpenFrameState)
    (restFrames : List OpenFrameState) (selfN : OpenMirTy) (tr : TraitDefId)
    (argsN : List OpenMirTy) (mIdx : AssocItemIdx) (args : List OpenOperand)
    (dst : OpenPlace) (tgt : Option BasicBlockId) (uw : UnwindAction) :
    StepResult OpenState TerminalOut :=
  if !TraitRegistryWf prog.traitRegistry then
    .fault .unsupported
  else
    match lookupImpl prog.traitRegistry ⟨selfN, tr, argsN⟩ with
    | none => .fault .unsupported
    | some binding =>
        if !Nat.beq binding.implTyParamCount 0 then
          .fault .unsupported
        else
          match lookupImplMethod binding.methodDefIds mIdx with
          | none => .fault .unsupported
          | some calleeId =>
              match openListGet? prog.bodies calleeId with
              | none => .fault .unsupported
              | some calleeBody =>
                  if !Nat.beq calleeBody.sig.tyParamCount 0 ||
                     !openBodyNoParam calleeBody ||
                     !openSigMatchesLocals prog calleeBody ||
                     calleeBody.basicBlocks.isEmpty then
                    .fault .unsupported
                  else if !dst.projection.isEmpty then
                    .fault .unsupported
                  else
                    match openListGet? ob.locals dst.localId with
                    | none => .fault .unsupported
                    | some dstTy =>
                        let dstN :=
                          normalizeOpenTy prog.traitRegistry normFuel dstTy
                        let calleeRetN :=
                          normalizeOpenTy prog.traitRegistry normFuel
                            calleeBody.sig.retTy
                        if !OpenMirTy.beq dstN calleeRetN then
                          .fault .unsupported
                        else
                          match evalOpenOperands prog env ob frame args with
                          | .error k => .fault k
                          | .ok (argVals, frame₁) =>
                              match initOpenLocals prog env calleeBody argVals
                                with
                              | none => .fault .unsupported
                              | some calleeLocals =>
                                  let calleeFrame : OpenFrameState :=
                                    { defId := calleeId
                                    , blockIdx := 0
                                    , stmtIdx := 0
                                    , locals := calleeLocals
                                    , retDst := some (dst, tgt, uw) }
                                  .step
                                    { s with
                                      frames :=
                                        calleeFrame :: frame₁ :: restFrames }

/-- Terminator dispatch helper for `OpenStep`. Closed `.traitCall`s execute
`concreteTraitCallStep` (never falling back to `AssumeGuaranteeTraitCall`);
open `.traitCall`s execute `AssumeGuaranteeTraitCall`. -/
def OpenStepOnTerm (prog : OpenProgram) (env : OpenExecEnv)
    (assumedWhere : List WhereClause) (s : OpenState) (ob : OpenBody)
    (frame : OpenFrameState) (restFrames : List OpenFrameState)
    (res : StepResult OpenState TerminalOut) : OpenTerminatorKind → Prop
  | .traitCall selfTy tr trArgs mIdx args dst tgt uw =>
      let selfN := normalizeOpenTy prog.traitRegistry normFuel selfTy
      let argsN := trArgs.map (normalizeOpenTy prog.traitRegistry normFuel)
      if OpenMirTy.isClosed selfN && OpenMirTy.isClosedList argsN then
        res = concreteTraitCallStep prog env s ob frame restFrames selfN tr
          argsN mIdx args dst tgt uw
      else
        AssumeGuaranteeTraitCall prog env assumedWhere
          s ob frame restFrames selfTy tr trArgs mIdx args dst tgt uw res
  | .goto _ | .switchInt _ _ | .return_ | .unreachable | .unwindResume
  | .assert _ _ _ _ _ | .call _ _ _ _ _ _ | .unsupported =>
      res = openEvalDetStep prog env s

/-- Statement-end guard helper for `OpenStep`. -/
def OpenStepOnStmtEnd (prog : OpenProgram) (env : OpenExecEnv)
    (assumedWhere : List WhereClause) (s : OpenState) (ob : OpenBody)
    (frame : OpenFrameState) (restFrames : List OpenFrameState)
    (bb : OpenBasicBlock) (res : StepResult OpenState TerminalOut) :
    Bool → Prop
  | true =>
      OpenStepOnTerm prog env assumedWhere s ob frame restFrames res
        bb.terminator
  | false => res = openEvalDetStep prog env s

/-- Basic-block lookup helper for `OpenStep`. -/
def OpenStepOnBlockOpt (prog : OpenProgram) (env : OpenExecEnv)
    (assumedWhere : List WhereClause) (s : OpenState) (ob : OpenBody)
    (frame : OpenFrameState) (restFrames : List OpenFrameState)
    (res : StepResult OpenState TerminalOut) :
    Option OpenBasicBlock → Prop
  | none => res = .fault .unsupported
  | some bb =>
      OpenStepOnStmtEnd prog env assumedWhere s ob frame restFrames bb res
        (Nat.beq frame.stmtIdx bb.statements.length)

/-- Body lookup helper for `OpenStep`. -/
def OpenStepOnBodyOpt (prog : OpenProgram) (env : OpenExecEnv)
    (assumedWhere : List WhereClause) (s : OpenState)
    (frame : OpenFrameState) (restFrames : List OpenFrameState)
    (res : StepResult OpenState TerminalOut) : Option OpenBody → Prop
  | none => res = .fault .unsupported
  | some ob =>
      OpenStepOnBlockOpt prog env assumedWhere s ob frame restFrames res
        (openListGet? ob.basicBlocks frame.blockIdx)

/-- Frame-list dispatch helper for `OpenStep`. -/
def OpenStepOnFrames (prog : OpenProgram) (env : OpenExecEnv)
    (assumedWhere : List WhereClause) (s : OpenState)
    (res : StepResult OpenState TerminalOut) : List OpenFrameState → Prop
  | frame :: restFrames =>
      OpenStepOnBodyOpt prog env assumedWhere s frame restFrames res
        (openListGet? prog.bodies frame.defId)
  | [] => res = .fault .unsupported

/-- Relational small-step transition `OpenStep` for open generic MIR bodies.
-/
def OpenStep (prog : OpenProgram) (env : OpenExecEnv)
    (assumedWhere : List WhereClause) (s : OpenState)
    (res : StepResult OpenState TerminalOut) : Prop :=
  OpenStepOnFrames prog env assumedWhere s res s.frames

/-- Multi-step reachability under `OpenStep`. -/
inductive OpenReaches (prog : OpenProgram) (env : OpenExecEnv)
    (assumedWhere : List WhereClause) : OpenState → OpenState → Prop where
  | refl (s : OpenState) : OpenReaches prog env assumedWhere s s
  | step {s₁ s₂ s₃ : OpenState} :
      OpenStep prog env assumedWhere s₁ (.step s₂) →
      OpenReaches prog env assumedWhere s₂ s₃ →
      OpenReaches prog env assumedWhere s₁ s₃

/-- Fault-freedom and step-progress safety invariant for an open generic query
`q`. Requiring `∃ res, OpenStep ... s res` at every reachable state forbids
vacuous deadlocks on unsatisfiable postconditions. -/
def OpenWellFormed (prog : OpenProgram) (env : OpenExecEnv)
    (assumedWhere : List WhereClause) (q : Query) : Prop :=
  (∃ s₀ : OpenState, openInitState prog env q = .ok s₀ ∧
    ∀ s : OpenState, OpenReaches prog env assumedWhere s₀ s →
      ∃ res : StepResult OpenState TerminalOut,
        OpenStep prog env assumedWhere s res) ∧
  ∀ s₀ : OpenState, openInitState prog env q = .ok s₀ →
    ∀ s : OpenState, ∀ k : FaultKind,
      OpenReaches prog env assumedWhere s₀ s →
      ¬ OpenStep prog env assumedWhere s (.fault k)

/-- Observable terminal behavior of `(prog, env, assumedWhere, q)` under
`OpenStep`. -/
def OpenBehavior (prog : OpenProgram) (env : OpenExecEnv)
    (assumedWhere : List WhereClause) (q : Query) (out : TerminalOut) : Prop :=
  ∃ s₀ s : OpenState,
    openInitState prog env q = .ok s₀ ∧
    OpenReaches prog env assumedWhere s₀ s ∧
    OpenStep prog env assumedWhere s (.done out)

/-- Override `entryDefId` on `prog`. -/
noncomputable def entryOpenProgForBody (prog : OpenProgram) (defId : DefId) :
    OpenProgram :=
  { prog with entryDefId := defId }

/-- Check that every element of `σ` is closed, lies in the supported closed
fragment when Day-1-convertible (`openClosedTySupported`), and evaluates to a
well-formed `TypeLayoutSpec` in `env.typeSpecs`. -/
def AllSubstTypesWellFormed (prog : OpenProgram)
    (env : OpenExecEnv) (σ : List OpenMirTy) : Prop :=
  ∀ ty : OpenMirTy, ty ∈ σ →
    OpenMirTy.isClosed ty = true ∧
    openClosedTySupported prog.traitRegistry ty = true ∧
    ∃ spec : TypeLayoutSpec,
      evalOpenTySpec prog.traitRegistry normFuel env.typeSpecs ty = some spec ∧
      WellFormedTypeLayoutSpec spec

/-- Check that every type-parameter invariant `inv ∈ paramInvs` matches
`paramSpecs.length` and is inhabited whenever the corresponding
`TypeLayoutSpec` is sized and inhabited (preventing vacuous invariant
quantification). -/
def AllParamInvsWf :
    List TypeLayoutSpec → List (List AllocByte → Prop) → Prop
  | [], [] => True
  | sp :: sps, inv :: invs =>
      (sp.inhabited = true → sp.isSized = true →
        ∃ bs : List AllocByte, LangValid sp .none bs ∧ inv bs) ∧
      AllParamInvsWf sps invs
  | _, _ => False

/-- Maximum nesting depth when checking concrete `impl` `whereClauses` in
`SatisfiesTraitSem`. -/
noncomputable def traitCheckDepth : Nat := 8

/-- Core trait-contract satisfaction predicate at bounded `impl`-`where` fuel
`depth` (`0` returns `False` unconditionally as the structural fuel base case).
Checks `TraitRegistryWf`, closed `argsN`, `contract.typeInv`, associated-type
specs, `binding.whereClauses`, and behavioral refinement of every concrete
`calleeBody` against `mspec.{pre,post}`. -/
def SatisfiesTraitSemDepth (prog : OpenProgram)
    (env : OpenExecEnv) :
    Nat → OpenMirTy → TraitDefId → List OpenMirTy → TraitContract → Prop
  | 0, _, _, _, _ => False
  | depth + 1, selfTy, traitId, traitArgs, contract =>
      let envClosed : OpenExecEnv :=
        { env with
          typeSpecs :=
            { env.typeSpecs with paramSpecs := [], paramInvs := [] } }
      let selfN := normalizeOpenTy prog.traitRegistry normFuel selfTy
      let argsN := traitArgs.map (normalizeOpenTy prog.traitRegistry normFuel)
      TraitRegistryWf prog.traitRegistry = true ∧
      env.traitContracts traitId = some contract ∧
      OpenMirTy.isClosed selfN = true ∧
      openClosedTySupported prog.traitRegistry selfN = true ∧
      argsN.length = contract.tyParamCount ∧
      AllSubstTypesWellFormed prog envClosed argsN ∧
      (∃ selfSpec : TypeLayoutSpec,
        evalOpenTySpec prog.traitRegistry normFuel envClosed.typeSpecs selfN =
          some selfSpec ∧
        WellFormedTypeLayoutSpec selfSpec ∧
        ∀ m : PtrMeta, ∀ bs : List AllocByte,
          LangValid selfSpec m bs → contract.typeInv selfSpec bs) ∧
      ∃ binding : ImplBinding,
        lookupImpl prog.traitRegistry ⟨selfN, traitId, argsN⟩ = some binding ∧
        binding.implTyParamCount = 0 ∧
        (∀ wc : WhereClause, wc ∈ binding.whereClauses →
          match wc with
          | .traitBound wSelf wTr wArgs =>
              ∃ wContract : TraitContract,
                envClosed.traitContracts wTr = some wContract ∧
                SatisfiesTraitSemDepth prog envClosed depth wSelf wTr wArgs
                  wContract
          | .isSized ty =>
              openClosedTySupported prog.traitRegistry ty = true ∧
              ∃ sp : TypeLayoutSpec,
                evalOpenTySpec prog.traitRegistry normFuel envClosed.typeSpecs
                    ty =
                  some sp ∧
                WellFormedTypeLayoutSpec sp ∧
                sp.isSized = true
          | .typeEq lhs rhs =>
              openClosedTySupported prog.traitRegistry lhs = true ∧
              OpenMirTy.beq
                (normalizeOpenTy prog.traitRegistry normFuel lhs)
                (normalizeOpenTy prog.traitRegistry normFuel rhs) = true ∧
              ∃ sp : TypeLayoutSpec,
                evalOpenTySpec prog.traitRegistry normFuel envClosed.typeSpecs
                    lhs =
                  some sp ∧
                evalOpenTySpec prog.traitRegistry normFuel envClosed.typeSpecs
                    rhs =
                  some sp ∧
                WellFormedTypeLayoutSpec sp) ∧
        (∃ assocSpecs : List TypeLayoutSpec,
          resolveTraitAssocSpecs prog envClosed selfN traitId argsN
            contract.assocTypeCount = some assocSpecs ∧
          AllParamSpecsWf assocSpecs ∧
          (∀ idx : AssocItemIdx, idx < contract.assocTypeCount →
            ∃ rhsTy : OpenMirTy, ∃ rhsSpec : TypeLayoutSpec,
              lookupAssocType binding.assocTypes idx = some rhsTy ∧
              OpenMirTy.isClosed rhsTy = true ∧
              evalOpenTySpec prog.traitRegistry normFuel envClosed.typeSpecs
                  rhsTy =
                some rhsSpec ∧
              WellFormedTypeLayoutSpec rhsSpec) ∧
          (∃ selfSpec : TypeLayoutSpec, ∃ argSpecs : List TypeLayoutSpec,
            evalOpenTySpec prog.traitRegistry normFuel envClosed.typeSpecs
                selfN =
              some selfSpec ∧
            evalNormOpenTySpecList envClosed.typeSpecs argsN = some argSpecs ∧
            ∀ mspec : TraitMethodSpec,
              mspec ∈ contract.methodSpecs →
                ∃ calleeId : DefId, ∃ calleeBody : OpenBody,
                  lookupImplMethod binding.methodDefIds mspec.sig.methodIdx =
                    some calleeId ∧
                  openListGet? prog.bodies calleeId = some calleeBody ∧
                  calleeBody.sig.tyParamCount = 0 ∧
                  openBodyNoParam calleeBody = true ∧
                  calleeBody.isUnsafe = mspec.sig.isUnsafe ∧
                  OpenBodyStaticAdmitted prog envClosed calleeBody ∧
                  let normSubst :=
                    OpenMirTy.substAndNormalize prog.traitRegistry normFuel
                      (selfN :: argsN)
                  let instArgTys := mspec.sig.argTys.map normSubst
                  let instRetTy := normSubst mspec.sig.retTy
                  calleeBody.argumentCount = instArgTys.length ∧
                  OpenMirTy.beq
                    (normalizeOpenTy prog.traitRegistry normFuel
                      calleeBody.sig.retTy)
                    instRetTy = true ∧
                  openTyListsNormEq prog.traitRegistry calleeBody.sig.argTys
                    instArgTys = true ∧
                  ∀ argVals : List Val,
                    checkOpenArgsMatch prog envClosed argVals instArgTys =
                      true →
                    mspec.pre (selfSpec :: argSpecs) assocSpecs argVals ⟨[]⟩ →
                    OpenWellFormed (entryOpenProgForBody prog calleeId)
                      envClosed calleeBody.sig.whereClauses
                      { args := argVals } ∧
                    ∀ out : TerminalOut,
                      OpenBehavior (entryOpenProgForBody prog calleeId)
                        envClosed calleeBody.sig.whereClauses
                        { args := argVals } out →
                      mspec.post (selfSpec :: argSpecs) assocSpecs argVals ⟨[]⟩
                        out))

/-- Top-level concrete trait satisfaction at `traitCheckDepth`. -/
def SatisfiesTraitSem (prog : OpenProgram) (env : OpenExecEnv)
    (selfTy : OpenMirTy) (traitId : TraitDefId) (traitArgs : List OpenMirTy)
    (contract : TraitContract) : Prop :=
  SatisfiesTraitSemDepth prog env traitCheckDepth selfTy traitId traitArgs
    contract

/-- Grounded semantic truth of a closed `WhereClause` against `prog` (evaluated
under `envClosed` with empty `paramSpecs`/`paramInvs`). For `.typeEq`, requires
both syntactic equality of normalized `OpenMirTy`s (`OpenMirTy.beq`) and a
well-formed `TypeLayoutSpec`. -/
def WhereClauseSem (prog : OpenProgram) (env : OpenExecEnv) :
    WhereClause → Prop
  | wc =>
      let envClosed : OpenExecEnv :=
        { env with
          typeSpecs :=
            { env.typeSpecs with paramSpecs := [], paramInvs := [] } }
      match wc with
      | .traitBound selfTy tr args =>
          ∃ contract : TraitContract,
            envClosed.traitContracts tr = some contract ∧
            SatisfiesTraitSem prog envClosed selfTy tr args contract
      | .isSized ty =>
          openClosedTySupported prog.traitRegistry ty = true ∧
          ∃ sp : TypeLayoutSpec,
            evalOpenTySpec prog.traitRegistry normFuel envClosed.typeSpecs ty =
              some sp ∧
            WellFormedTypeLayoutSpec sp ∧
            sp.isSized = true
      | .typeEq lhs rhs =>
          openClosedTySupported prog.traitRegistry lhs = true ∧
          OpenMirTy.beq
            (normalizeOpenTy prog.traitRegistry normFuel lhs)
            (normalizeOpenTy prog.traitRegistry normFuel rhs) = true ∧
          ∃ sp : TypeLayoutSpec,
            evalOpenTySpec prog.traitRegistry normFuel envClosed.typeSpecs lhs =
              some sp ∧
            evalOpenTySpec prog.traitRegistry normFuel envClosed.typeSpecs rhs =
              some sp ∧
            WellFormedTypeLayoutSpec sp

/-- Every clause in `wcs` holds semantically after substituting `σ` and
normalizing associated projections. -/
def AllWhereDischarged (prog : OpenProgram) (env : OpenExecEnv)
    (σ : List OpenMirTy) (wcs : List WhereClause) : Prop :=
  ∀ wc : WhereClause, wc ∈ wcs →
    WhereClauseSem prog env
      (WhereClause.substAndNormalize prog.traitRegistry normFuel σ wc)

/-- Parametric semantic truth of an assumed `WhereClause` at a type-layout
instantiation `(env.typeSpecs.paramSpecs, paramInvs, assocSpecs)`. When the
target of `.traitBound` is closed, falls back to full concrete
`SatisfiesTraitSem`; when open, checks contract existence, parameter arity,
well-formed `self`/`args` specs, associated-type layout specs in `assocSpecs`,
and `paramInvs` soundness against `contract.typeInv`.

Note: on open `.typeEq lhs rhs` (such as `<B as ByteSource>::Out = u64` prior
to substitution `σ`), `lhs` is an unnormalized `.assocProj (.param _)` whose
syntactic `OpenMirTy` differs from `rhs`, so parametric `.typeEq` constrains
`evalOpenTySpec` layout agreement via `env.typeSpecs.assocSpecs`, while closed
instantiation (`WhereClauseSem` / `SatisfiesTraitSemDepth`) enforces syntactic
`OpenMirTy.beq` after projection normalization. -/
def WhereClauseParamSem (prog : OpenProgram) (env : OpenExecEnv) :
    WhereClause → Prop
  | .isSized ty =>
      ∃ sp : TypeLayoutSpec,
        evalOpenTySpec prog.traitRegistry normFuel env.typeSpecs ty = some sp ∧
        WellFormedTypeLayoutSpec sp ∧
        sp.isSized = true
  | .typeEq lhs rhs =>
      ∃ sp : TypeLayoutSpec,
        evalOpenTySpec prog.traitRegistry normFuel env.typeSpecs lhs = some sp ∧
        evalOpenTySpec prog.traitRegistry normFuel env.typeSpecs rhs = some sp ∧
        WellFormedTypeLayoutSpec sp
  | .traitBound selfTy tr args =>
      let selfN := normalizeOpenTy prog.traitRegistry normFuel selfTy
      let argsN := args.map (normalizeOpenTy prog.traitRegistry normFuel)
      ∃ contract : TraitContract,
        env.traitContracts tr = some contract ∧
        argsN.length = contract.tyParamCount ∧
        (∀ a : OpenMirTy, a ∈ argsN →
          ∃ aSp : TypeLayoutSpec,
            evalOpenTySpec prog.traitRegistry normFuel env.typeSpecs a =
              some aSp ∧
            WellFormedTypeLayoutSpec aSp) ∧
        (∃ selfSpec : TypeLayoutSpec,
          evalOpenTySpec prog.traitRegistry normFuel env.typeSpecs selfN =
            some selfSpec ∧
          WellFormedTypeLayoutSpec selfSpec ∧
          (match selfN with
           | .param i =>
               match openListGet? env.typeSpecs.paramInvs i with
               | some inv =>
                   ∀ bs : List AllocByte,
                     LangValid selfSpec .none bs →
                     inv bs →
                     contract.typeInv selfSpec bs
               | none => False
           | _ =>
               ∀ m : PtrMeta, ∀ bs : List AllocByte,
                 LangValid selfSpec m bs → contract.typeInv selfSpec bs)) ∧
        (∃ assocSpecs : List TypeLayoutSpec,
          resolveTraitAssocSpecs prog env selfN tr argsN
            contract.assocTypeCount = some assocSpecs ∧
          AllParamSpecsWf assocSpecs) ∧
        (OpenMirTy.isClosed selfN = true →
          OpenMirTy.isClosedList argsN = true →
          SatisfiesTraitSem prog env selfN tr argsN contract)

/-- All `WhereClause` obligations in `wcs` hold semantically at parametric
instantiation `env`. -/
def AllWhereParamsSem (prog : OpenProgram) (env : OpenExecEnv) :
    List WhereClause → Prop
  | [] => True
  | wc :: rest =>
      WhereClauseParamSem prog env wc ∧ AllWhereParamsSem prog env rest

/-- Valid entry arguments predicate for an open body `ob`, checking both
`checkOpenArgsMatch` and parameter safety invariants `paramInvs`. -/
def ValidOpenEntryArgs (prog : OpenProgram) (env : OpenExecEnv)
    (ob : OpenBody) (args : List Val) : Prop :=
  let paramTys := (ob.locals.drop 1).take ob.argumentCount
  checkOpenArgsMatch prog env args paramTys = true ∧
  argsSatisfyParamInvs prog env args paramTys

/-- Top-level parametric verification judgment for a generic MIR body `ob`:
enforces environment-independent `OpenBodyStructureValid` unconditionally, and
quantifies over EVERY `(paramSpecs, paramInvs, assocSpecs)` matching
`ob.sig.tyParamCount`, `AllParamSpecsWf`, `AllParamInvsWf`, and
`AllWhereParamsSem ... ob.sig.whereClauses`, requiring `OpenBodyStaticAdmitted`
and `OpenWellFormed` across all `ValidOpenEntryArgs`. -/
def ParametricBodyVerified (prog : OpenProgram)
    (env : OpenExecEnv) (defId : DefId) (ob : OpenBody)
    (safetyPre : OpenExecEnv → List Val → Prop) : Prop :=
  openListGet? prog.bodies defId = some ob ∧
  TraitRegistryWf prog.traitRegistry = true ∧
  OpenBodyStructureValid prog ob ∧
  ∀ paramSpecs : List TypeLayoutSpec,
    ∀ paramInvs : List (List AllocByte → Prop),
      ∀ assocSpecs : OpenMirTy → TraitDefId → List OpenMirTy →
          AssocItemIdx → Option TypeLayoutSpec,
        paramSpecs.length = ob.sig.tyParamCount →
        AllParamSpecsWf paramSpecs →
        AllParamInvsWf paramSpecs paramInvs →
        let env' : OpenExecEnv :=
          { env with
            typeSpecs := substTypeSpecEnv env.typeSpecs
              paramSpecs paramInvs assocSpecs }
        AllWhereParamsSem prog env' ob.sig.whereClauses →
        OpenBodyStaticAdmitted prog env' ob ∧
        ∀ args : List Val,
          ValidOpenEntryArgs prog env' ob args →
          (ob.isUnsafe = true → safetyPre env' args) →
          OpenWellFormed (entryOpenProgForBody prog defId) env'
            ob.sig.whereClauses { args := args }

/-- Substituted `OpenProgram` formed by instantiating every body in `prog` at
`σ` (including normalizing substituted types and `sig.whereClauses` via
`OpenBody.subst`). -/
noncomputable def substOpenProgram (σ : List OpenMirTy) (prog : OpenProgram) :
    OpenProgram :=
  { prog with
    bodies := prog.bodies.map (OpenBody.subst prog.traitRegistry normFuel σ) }

/-- Whether an `OpenTerminatorKind` is a non-call, non-traitCall terminator
that executes identically in Day-1 `evalTerminator` (`Step.lean`). -/
noncomputable def openTermIsDay1Pure : OpenTerminatorKind → Bool
  | .goto _ | .switchInt _ _ | .return_ | .unreachable
  | .unsupported => true
  | .unwindResume | .assert _ _ _ _ _
  | .call _ _ _ _ _ _ | .traitCall _ _ _ _ _ _ _ _ => false

/-- Whether an `OpenBody` contains only terminators with faithful Day-1
execution semantics. -/
noncomputable def openBodyIsDay1Erasable (ob : OpenBody) : Bool :=
  ob.basicBlocks.all (fun bb => openTermIsDay1Pure bb.terminator)

mutual
  /-- Projection nesting depth bound on `OpenMirTy`. -/
  noncomputable def OpenMirTy.assocDepth : OpenMirTy → Nat
    | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
    | .param _ | .unsupported => 0
    | .slice e | .array e _ | .ref _ e | .rawPtr _ e => OpenMirTy.assocDepth e
    | .tuple fs | .adt _ fs => OpenMirTy.assocDepthList fs
    | .assocProj s _ args _ =>
        Nat.max (OpenMirTy.assocDepth s) (OpenMirTy.assocDepthList args) + 1

  /-- Elementwise projection nesting depth bound on `List OpenMirTy`. -/
  noncomputable def OpenMirTy.assocDepthList : List OpenMirTy → Nat
    | [] => 0
    | x :: xs => Nat.max (OpenMirTy.assocDepth x) (OpenMirTy.assocDepthList xs)
end

mutual
  /-- Whether every `.tuple` inside `OpenMirTy` is a closed Day-1 overflow pair
  `[.int w s, .bool]` so `evalNormOpenTySpec` never drops an open tuple
  asymmetrically prior to substitution. -/
  noncomputable def openTyNoOpenTuple : OpenMirTy → Bool
    | .bool | .int _ _ | .unit | .never | .char | .ordering | .enum _
    | .param _ | .unsupported => true
    | .tuple [.int _ _, .bool] => true
    | .tuple _ => false
    | .slice e | .array e _ | .ref _ e | .rawPtr _ e => openTyNoOpenTuple e
    | .adt _ args => openTyListNoOpenTuple args
    | .assocProj s _ args _ =>
        openTyNoOpenTuple s && openTyListNoOpenTuple args

  /-- Elementwise open-tuple absence check on `List OpenMirTy`. -/
  noncomputable def openTyListNoOpenTuple : List OpenMirTy → Bool
    | [] => true
    | x :: xs => openTyNoOpenTuple x && openTyListNoOpenTuple xs
end

/-- Whether every associated-type projection in `wcs` has nesting depth at most
`bound` and contains no non-closed `.tuple`s. -/
noncomputable def openWhereClausesBounded (bound : Nat) :
    List WhereClause → Bool
  | [] => true
  | wc :: rest =>
      let ok :=
        match wc with
        | .traitBound selfTy _ args =>
            Nat.ble (OpenMirTy.assocDepth selfTy) bound &&
            Nat.ble (OpenMirTy.assocDepthList args) bound &&
            openTyNoOpenTuple selfTy && openTyListNoOpenTuple args
        | .isSized ty =>
            Nat.ble (OpenMirTy.assocDepth ty) bound &&
            openTyNoOpenTuple ty
        | .typeEq l r =>
            Nat.ble (OpenMirTy.assocDepth l) bound &&
            Nat.ble (OpenMirTy.assocDepth r) bound &&
            openTyNoOpenTuple l && openTyNoOpenTuple r
      ok && openWhereClausesBounded bound rest

/-- Instantiated associated-type resolver mapping
`(selfTy as Trait<args>)::idx`: preserves `base.assocSpecs` verbatim on
parameter-free queries, and substitutes `σ` and evaluates in closed `base`
whenever open `.param` nodes appear. -/
noncomputable def instAssocSpecs (reg : TraitRegistry)
    (base : TypeSpecEnv) (σ : List OpenMirTy) :
    OpenMirTy → TraitDefId → List OpenMirTy → AssocItemIdx →
      Option TypeLayoutSpec :=
  fun selfTy tr args idx =>
    if openMirTyNoParam selfTy && openMirTyListNoParam args then
      base.assocSpecs selfTy tr args idx
    else
      let baseClosed : TypeSpecEnv :=
        { base with paramSpecs := [], paramInvs := [] }
      let selfSub := OpenMirTy.substAndNormalize reg normFuel σ selfTy
      let argsSub := args.map (OpenMirTy.substAndNormalize reg normFuel σ)
      evalOpenTySpec reg normFuel baseClosed (.assocProj selfSub tr argsSub idx)

/-- The `OpenExecEnv` instantiated at closed substitution `σ` using resolved
`paramSpecs`, trivial `paramInvs`, and `instAssocSpecs`. -/
noncomputable def instOpenExecEnv (prog : OpenProgram) (env : OpenExecEnv)
    (σ : List OpenMirTy) (paramSpecs : List TypeLayoutSpec) : OpenExecEnv :=
  { env with
    typeSpecs :=
      substTypeSpecEnv env.typeSpecs paramSpecs
        (List.replicate paramSpecs.length (fun _ => True))
        (instAssocSpecs prog.traitRegistry env.typeSpecs σ) }

/-- Claim specification for `Anneal.Generic.Erasure`: given any monomorphizing
erasure pair `(eraseBody, eraseProg)` satisfying Day-1 substitution agreement on
`ob`, `ParametricBodyVerified` paired with `AllSubstTypesWellFormed`,
`AllWhereDischarged`, and `BodyStaticAdmitted` yields genuine Day-1
`Trusted.MirSemantics.BodyVerified` with `safetyPre` required only at the
`σ`-instantiated environment `instOpenExecEnv prog env σ paramSpecs`. -/
def OpenInstantiationErasureClaim
    (eraseBody : TraitRegistry → List OpenMirTy → OpenBody → Body)
    (eraseProg : List OpenMirTy → OpenProgram → Program) : Prop :=
  ∀ (prog : OpenProgram) (env : OpenExecEnv) (defId : DefId) (ob : OpenBody)
    (σ : List OpenMirTy) (safetyPre : OpenExecEnv → List Val → Prop)
    (concretePre : List Val → Prop),
    ParametricBodyVerified prog env defId ob safetyPre →
    σ.length = ob.sig.tyParamCount →
    AllSubstTypesWellFormed prog env σ →
    AllWhereDischarged prog env σ ob.sig.whereClauses →
    openWhereClausesBounded normFuel ob.sig.whereClauses = true →
    OpenBody.toDay1? (OpenBody.subst prog.traitRegistry normFuel σ ob) =
      some (eraseBody prog.traitRegistry σ ob) →
    openBodyIsDay1Erasable ob = true →
    Trusted.MirSemantics.getElem? (eraseProg σ prog).bodies defId =
      some (eraseBody prog.traitRegistry σ ob) →
    BodyStaticAdmitted (eraseProg σ prog)
      (eraseBody prog.traitRegistry σ ob) = true →
    ((eraseBody prog.traitRegistry σ ob).isUnsafe = true →
      ∀ args : List Val, ∀ paramSpecs : List TypeLayoutSpec,
        evalNormOpenTySpecList env.typeSpecs
          (σ.map (normalizeOpenTy prog.traitRegistry normFuel)) =
            some paramSpecs →
        ValidEntryArgs (eraseBody prog.traitRegistry σ ob) args →
        concretePre args →
        safetyPre (instOpenExecEnv prog env σ paramSpecs) args) →
    BodyVerified (eraseProg σ prog) defId
      (eraseBody prog.traitRegistry σ ob) concretePre

end Anneal.Generic

end
