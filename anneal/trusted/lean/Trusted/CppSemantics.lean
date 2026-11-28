-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:refinement
module
prelude
public import Init.NotationExtra
public import Init.Data.List.Basic
public import Trusted.Framework
public import Trusted.CppAst
public import Trusted.CppSemantics.State
public import Trusted.CppSemantics.Memory
public import Trusted.CppSemantics.Eval
public import Trusted.CppSemantics.Step

@[expose] public section

namespace Trusted.CppSemantics

open Trusted.CppAst Trusted.Framework

/-!
# Rung-0 C11 ExecutionModel Instance (`Trusted.CppSemantics`)

Plugs Rung-0 C11 small-step semantics directly into
`Trusted.Framework.ExecutionModel` (`CppProfileRung0`) with
`OracleGrade.unbridged "cpp_rung0_c11"`, `defaultCppDownstreamGaps`, and the
model-pinned root obligation `CppEnvelopeTheorem`.
-/

/-- Canonical downstream compilation and hardware execution stages outside a
Pass-1 C11 AST proof. -/
@[reducible] def defaultCppDownstreamGaps : List DisclosedGap :=
  [ .unverifiedDownstream "clang_opt",
    .unverifiedDownstream "llvm_codegen",
    .unverifiedDownstream "linker",
    .unverifiedDownstream "microarch_timing" ]

/-- Project `CppTerminalOut` into `Trusted.Framework.TerminalOutcome`. -/
noncomputable def mapCppTerminalOut :
    CppTerminalOut → TerminalOutcome CppVal CppMemory
  | .returned out => .returned out.ret out.mem
  | .unwound mem  => .unwound mem
  | .aborted mem  => .aborted mem

/-- Lift `CppBehavior` to `TerminalOutcome CppVal CppMemory`. -/
@[reducible] def CppProduces (prog : CppProgram) (q : CppQuery)
    (res : TerminalOutcome CppVal CppMemory) : Prop :=
  ∃ out : CppTerminalOut, CppBehavior prog q out ∧ mapCppTerminalOut out = res

/-- Check whether `id` is absent from `seen`. -/
noncomputable def strNotSeen (id : String) : List String → Bool
  | [] => true
  | x :: rest => !(id == x) && strNotSeen id rest

/-- Check that every body has a non-empty, pairwise-distinct `identity`. -/
noncomputable def cppBodiesUniqueAux (seen : List String) :
    List CppBody → Bool
  | [] => true
  | b :: rest =>
    !(b.identity == "") &&
      strNotSeen b.identity seen &&
      cppBodiesUniqueAux (b.identity :: seen) rest

/-- Pairwise-distinct non-empty body identity check for `CppProgram`. -/
noncomputable def cppBodiesHaveUniqueIdentities (bodies : List CppBody) :
    Bool :=
  cppBodiesUniqueAux [] bodies

/-- Check that every record has a non-empty `recordId` distinct from those
in `seen` and the other records. -/
noncomputable def cppRecordsUniqueAux (seen : List String) :
    List CppRecordDef → Bool
  | [] => true
  | r :: rest =>
    !(r.recordId == "") && strNotSeen r.recordId seen &&
      cppRecordsUniqueAux (r.recordId :: seen) rest

/-- `true` iff no field type of any record contains a `restrict` pointer. -/
noncomputable def cppRecordsNoRestrict : List CppRecordDef → Bool
  | [] => true
  | r :: rest =>
    CppTy.noRestrictList (r.fields.map CppFieldDecl.ty) &&
      cppRecordsNoRestrict rest

/-- Check that `locals` match `sig.params` starting at local `1`. -/
noncomputable def paramLocalsMatch :
    List CppLocalDecl → List CppTy → Bool
  | _, [] => true
  | [], _ :: _ => false
  | d :: ds, t :: ts =>
    d.isParam && CppTy.beq d.ty t && paramLocalsMatch ds ts

/-- `true` iff every call in `blocks` stores its result, if any, into a whole
local (C11 §6.5.16p3 leaves a projected destination unsequenced with the
call). -/
noncomputable def cppBlocksAdmitted : List CppBlock → Bool
  | [] => true
  | b :: rest =>
    (match b.term with
     | .call _ _ (some (p, _)) _ => p.projs.isEmpty
     | _ => true) && cppBlocksAdmitted rest

/-- Static admission check on a `CppBody`. `restrict`-qualified pointers are
not admitted anywhere in its signature or locals: the semantics does not
model C11 §6.7.3.1 based-on aliasing. -/
noncomputable def cppBodyAdmitted (_p : CppProgram) (b : CppBody) : Bool :=
  !(b.identity == "") &&
    CppTy.noRestrictList b.sig.params && CppTy.noRestrict b.sig.ret &&
    CppTy.noRestrictList (b.locals.map CppLocalDecl.ty) &&
    if b.isExternal then
      true
    else
      !b.blocks.isEmpty &&
        Nat.blt b.entryBlock b.blocks.length &&
        cppBlocksAdmitted b.blocks &&
        match b.locals with
        | [] => false
        | retDecl :: rest =>
          CppTy.beq retDecl.ty b.sig.ret &&
            paramLocalsMatch rest b.sig.params

/-- Check that no record in `records` is a `union`. C lets a program read a
union member other than the one last stored, reinterpreting its bytes, while
C++ makes that read undefined. The semantics tracks no active member and so
cannot tell the two apart; programs declaring a union are not admitted. -/
noncomputable def cppNoUnions : List CppRecordDef → Bool
  | [] => true
  | r :: rest => !r.isUnion && cppNoUnions rest

/-- Static admission check on a `CppProgram` against expected `policy` and
record layout table `records` (which `CppProfileRung0` also uses for entry
and return validity, so it must be exactly `p.records`). Strict-aliasing
programs are not admitted: integer types record only their width, so the
model cannot tell `long` from `long long` as C11 §6.5p7 requires. -/
noncomputable def cppProgramAdmitted (policy : CppLangPolicy)
    (records : List CppRecordDef) (p : CppProgram) : Bool :=
  CppLangPolicy.beq p.policy policy &&
    Nat.beq p.policy.pointerWidthBits 64 &&
    p.policy.exceptionsOff &&
    p.policy.littleEndian &&
    !p.policy.strictAliasing &&
    CppRecordDef.beqList p.records records &&
    cppRecordsUniqueAux [] p.records &&
    cppRecordsNoRestrict p.records &&
    cppNoUnions p.records &&
    !p.bodies.isEmpty &&
    Nat.blt p.entryDefId p.bodies.length

/-- Entry domain predicate for Rung-0 C11 functions. -/
def CppEntryDom (policy : CppLangPolicy)
    (records : List CppRecordDef) (body : CppBody) (q : CppQuery) : Prop :=
  validCppMemory q.mem = true ∧
    checkCppArgs policy records q.args body.sig.params = true ∧
    refArgsOk policy records q.mem body.sig.paramNonNull body.sig.params
      q.args = true ∧
    argsLiveInMem policy records q.mem q.args body.sig.params = true

/-- Return validity predicate for Rung-0 C11 functions. -/
def CppReturnValid (policy : CppLangPolicy)
    (records : List CppRecordDef) (body : CppBody) (ret : CppVal)
    (mem : CppMemory) : Prop :=
  validCppMemory mem = true ∧
    checkCppVal policy records ret body.sig.ret = true ∧
    valLiveInMem policy records mem ret body.sig.ret = true

/-- Override `entryDefId` to execute body `defId` as the root function. -/
noncomputable def cppExecForBody (p : CppProgram) (defId : Nat) : CppProgram :=
  { p with entryDefId := defId }

/-- Rung-0 C11 `ExecutionModel` parameterized by `policy` and the `records`
layout table, which admission requires to equal the program's own. Unbridged
until a Pass-2 correspondence to a reference C semantics lands
(`OracleGrade.unbridged "cpp_rung0_c11"`). -/
@[reducible] noncomputable def CppProfileRung0 (policy : CppLangPolicy)
    (records : List CppRecordDef) :
    ExecutionModel CppProgram CppBody CppSignature CppQuery CppVal CppMemory :=
  { profileId := "cpp_rung0_c11"
    oracleGrade := .unbridged "cpp_rung0_c11"
    programAdmitted := cppProgramAdmitted policy records
    bodyAdmitted := cppBodyAdmitted
    isPartialScope := CppProgram.isPartial
    bodyAt := fun p defId => cppGetElem? p.bodies defId
    uniqueIdentities := fun p => cppBodiesHaveUniqueIdentities p.bodies
    bodyIdentity := CppBody.identity
    bodyIsUnsafe := fun _ => true
    bodyIsExternal := CppBody.isExternal
    bodyMatchesSig := fun b sig => CppSignature.beq b.sig sig
    modelGaps := defaultCppDownstreamGaps
    requiredGaps := fun _ => []
    claimShapeGaps := fun _ => []
    entryDom := CppEntryDom policy records
    returnValid := CppReturnValid policy records
    memValid := fun m => validCppMemory m = true
    execForBody := cppExecForBody
    wellFormed := CppWellFormed
    produces := CppProduces
    diverges := CppDiverges
    faultsUB := CppFaultsUB }

/-- C11 verified contract entry alias. -/
abbrev CppVerifiedEntry :=
  VerifiedEntry CppSignature CppQuery CppVal CppMemory

/-- C11 external callee stub alias. -/
abbrev CppAssumedStub :=
  AssumedStub CppSignature CppQuery CppVal CppMemory

/-- C11 existential UB refutation entry alias. -/
abbrev CppRefutationEntry :=
  RefutationEntry CppSignature CppQuery

/-- Model-pinned structured Rung-0 C11 verification obligation, fixing
`ExecutionModel` to `CppProfileRung0 policy records` inside `Trusted.*`. -/
@[reducible] def CppEnvelopeTheorem
    (policy : CppLangPolicy)
    (program : CppProgram)
    (entries : List CppVerifiedEntry)
    (stubs : List CppAssumedStub)
    (refutations : List CppRefutationEntry)
    (claimShapes : List ClaimShape)
    (gaps : List DisclosedGap)
    (records : List CppRecordDef) : Prop :=
  EnvelopeTheorem
    (mkEnvelope (CppProfileRung0 policy records) program entries stubs
      refutations claimShapes gaps)

end Trusted.CppSemantics

end
