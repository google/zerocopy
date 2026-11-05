-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.MirSemantics
import Anneal.MirLemmas

open Trusted Anneal

/-- Constructs an entry `MirState` with local `1` initialized to `argVal` and
uniform 8-byte `tySizes`. -/
def mkState1 (argVal : MirVal) : MirState := {
  locals := updateLocal (fun _ => none) 1 (some argVal)
  block := 0
  stmtIdx := 0
  tySizes := fun _ => 8
}

/-- Concrete kernel execution oracle for `idCopyBody` on `42 : usize` via
`ExecNormal` and higher-order unification on `StepResult.silent`. -/
theorem exec_id_42 :
    ExecNormal [] [] idCopyBody (mkState1 (.usize 42))
      (fun r => r.value = .usize 42) := by
  exact .step rfl (.normal rfl rfl)

/-- Concrete kernel execution oracle for `allocPassthroughBody` on `42 : usize`
across 4 `evalMirStep` transitions. -/
theorem exec_alloc_passthrough_42 :
    ExecNormal [] [] allocPassthroughBody (mkState1 (.usize 42))
      (fun r => r.value = .usize 42) := by
  exact .step rfl (.step rfl (.step rfl (.step rfl (.normal rfl rfl))))

/-- Concrete kernel execution oracle for `makeNonZeroBody` on the `0 : usize`
branch (9 `evalMirStep` transitions, returning `NonZeroUsize(1)`). -/
theorem exec_make_nonzero_0 :
    ExecNormal [nonZeroAdtDecl 0] [] makeNonZeroBody (mkState1 (.usize 0))
      (fun r => r.value = .adt 0 (.usize 1)) := by
  exact .step rfl (.step rfl (.step rfl (.step rfl (.step rfl
    (.step rfl (.step rfl (.step rfl (.step rfl (.normal rfl rfl)))))))))

/-- Concrete kernel execution oracle for `makeNonZeroBody` on the non-zero
`42 : usize` branch (12 `evalMirStep` transitions, returning
`NonZeroUsize(42)`). -/
theorem exec_make_nonzero_42 :
    ExecNormal [nonZeroAdtDecl 0] [] makeNonZeroBody (mkState1 (.usize 42))
      (fun r => r.value = .adt 0 (.usize 42)) := by
  exact .step rfl (.step rfl (.step rfl (.step rfl (.step rfl
    (.step rfl (.step rfl (.step rfl (.step rfl (.step rfl
      (.step rfl (.step rfl (.normal rfl rfl))))))))))))

/-- Negative TCB policy canary verifying that `defaultTrustPolicy` rejects
`TCBItem.fnVerified` waivers. Kills mutant `M8` (`MirSemantics.lean:1169`). -/
theorem canary_defaultTrustPolicy_rejects_fnVerified_waiver
    (fnName : String) (bodyId : BodyId) :
    ¬ defaultTrustPolicy.isAllowed (.fnVerified fnName bodyId) := by
  intro h
  exact h
