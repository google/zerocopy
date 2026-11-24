-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Expected
import Anneal.MirWp
import Anneal.MirSymExec

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp
open Anneal.MirSymExec (SymScalar SymVal SymEnv symRun symEntry)

/-!
Both `<usize as PointerMetadata>` bodies are run once, symbolically, by the
bundled `Anneal.MirSymExec` executor on a free `usize` argument. The kernel
evaluates `symRun` on each captured body, so no local, block or statement
index appears here, and the single symbolic run covers all `2^64` inputs.
-/

private theorem body0_adm :
    BodyStaticAdmitted Captured.program Captured.body_0 = true := rfl

private theorem body1_adm :
    BodyStaticAdmitted Captured.program Captured.body_1 = true := rfl

/-- The free `usize` argument: symbolic variable `0`. -/
private noncomputable def usizeArg : SymVal := .scalar (.var 0 .isize false)

/-- Valuation binding every symbolic variable to `v`. -/
private def envOf (v : Val) : SymEnv := fun _ => v

private theorem body0_run :
    symRun Captured.body_0 4 (symEntry Captured.body_0 [usizeArg]) =
      .ret usizeArg := rfl

private theorem body1_run :
    symRun Captured.body_1 4 (symEntry Captured.body_1 [usizeArg]) =
      .ret usizeArg := rfl

private theorem usizeArg_eval {v : Val}
    (hv : checkVal v (.int .isize false) = true) :
    usizeArg.eval (envOf v) = v :=
  Anneal.MirSymExec.symScalar_var_eval (env := envOf v) hv

private theorem usize_valid (n : Spec.UsizeWord) :
    checkVal (Spec.usizeVal n) (.int .isize false) = true := by
  refine checkVal_scalar_of_toNat_lt ?_
  change Nat.mod n.toNat (Nat.pow 2 128) < intWidthModulus .isize
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) n.isLt

/-- Every valid entry argument list is an instance of `[usizeArg]`. -/
private theorem cover (body : Body)
    (hTys : (body.locals.drop 1).take body.argumentCount = [.int .isize false])
    (args : List Val) (valid : ValidEntryArgs body args) :
    ∃ env : SymEnv, [usizeArg].map (SymVal.eval env) = args := by
  have hMatch : checkArgsMatch args [.int .isize false] = true := by
    unfold ValidEntryArgs at valid
    rw [hTys] at valid
    exact valid
  let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
  have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
  subst hEq; subst hNil
  exact ⟨envOf v, congrArg (fun x => [x]) (usizeArg_eval hv)⟩

private theorem body0_safe_verified :
    BodyVerified Captured.program 0 Captured.body_0
      (Spec.specs.safety Captured.body_0.identity) :=
  Anneal.MirSymExec.symRun_bodyVerified_pre rfl body0_adm body0_run
    (fun args valid _ => cover Captured.body_0 rfl args valid)

private theorem body1_safe_verified :
    BodyVerified Captured.program 1 Captured.body_1
      (Spec.specs.safety Captured.body_1.identity) :=
  Anneal.MirSymExec.symRun_bodyVerified_pre rfl body1_adm body1_run
    (fun args valid _ => cover Captured.body_1 rfl args valid)

private theorem total_of_run {defId : DefId} {body : Body}
    (hBody : Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (hAdm : BodyStaticAdmitted Captured.program body = true)
    (hTys : (body.locals.drop 1).take body.argumentCount = [.int .isize false])
    (hRun : symRun body 4 (symEntry body [usizeArg]) = .ret usizeArg)
    (n : Spec.UsizeWord) :
    Spec.ReturnsTotal Captured.program defId [Spec.usizeVal n] (Spec.usizeVal n) := by
  have hv := usize_valid n
  have hEval : [usizeArg].map (SymVal.eval (envOf (Spec.usizeVal n))) =
      [Spec.usizeVal n] :=
    congrArg (fun x => [x]) (usizeArg_eval hv)
  have hArgs : ValidEntryArgs body
      ([usizeArg].map (SymVal.eval (envOf (Spec.usizeVal n)))) := by
    rw [hEval]
    unfold ValidEntryArgs
    rw [hTys]
    exact checkArgsMatch_cons_iff.mpr ⟨_, [], rfl, hv, rfl⟩
  have h := Anneal.MirSymExec.symRun_entry_behavior hBody hAdm
    (envOf (Spec.usizeVal n)) hArgs hRun
  rw [hEval, usizeArg_eval hv] at h
  exact ⟨h.2.2.2.2, h.2.2.2.1, h.2.2.1⟩

private theorem body0_total (n : Spec.UsizeWord) :
    Spec.ReturnsTotal Captured.program 0 [Spec.usizeVal n] (Spec.usizeVal n) :=
  total_of_run rfl body0_adm rfl body0_run n

private theorem body1_total (m : Spec.UsizeWord) :
    Spec.ReturnsTotal Captured.program 1 [Spec.usizeVal m] (Spec.usizeVal m) :=
  total_of_run rfl body1_adm rfl body1_run m

public theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · have hAll : BodiesVerified Captured.program Spec.specs 0 Captured.program.bodies :=
      ⟨body0_safe_verified, body1_safe_verified, True.intro⟩
    intro defId body found
    have hSub := bodiesVerified_getElem hAll defId body found
    rw [Nat.zero_add] at hSub
    exact hSub
  · refine ⟨rfl, 0, Captured.body_0, 1, Captured.body_1,
      rfl, rfl, rfl, rfl, rfl, rfl,
      body0_total, body1_total,
      (fun n => ⟨n, body0_total n, body1_total n⟩),
      (fun m => ⟨m, body1_total m, body0_total m⟩)⟩

end Proof
