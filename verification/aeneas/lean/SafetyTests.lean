/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import SpecsSyntax
public import Zerocopy.Funs
@[expose] public section
open Aeneas Aeneas.Std AeneasSpecs
namespace SafetyTests

-- Sequencing cannot convert forbidden execution into either a value or
-- divergence. In particular, discarding a callee's result is still sequencing.
theorem forbidden_bind {α β : Type} (next : α → Result β) :
    (Result.fail .undef >>= next) = Result.fail .undef := bind_fail .undef next

theorem total_rejects_forbidden {α : Type} (post : α → Prop) :
    ¬ WP.spec (.fail .undef) post := by simp

theorem partial_rejects_forbidden {α : Type} (post : α → Prop) :
    ¬ WP.dspec (.fail .undef) post := by simp

-- Every oversized copy is forbidden, rather than success with truncated
-- output or a recoverable None. The caller proves this branch unreachable.
theorem copy_rejects_oversize (src dst : Slice U8)
    (oversize : dst.val.length < src.val.length) :
    util.copy_unchecked src dst = .fail .undef := by
  simp [util.copy_unchecked, Zerocopy.forbiddenExecution, Nat.not_le.mpr oversize]

theorem offset_copy_rejects_oversize (src dst : Slice U8) (start : Usize)
    (inside : start.val ≤ dst.val.length)
    (oversize : dst.val.length - start.val < src.val.length) :
    util.copy_unchecked_at src dst start = .fail .undef := by
  simp [util.copy_unchecked_at, Zerocopy.forbiddenExecution, inside,
    Nat.not_le.mpr oversize]

-- This is the model of an unsafe producer with an invalid bit pattern. These
-- examples execute no Rust UB: they examine its forbidden abstract outcome.
noncomputable def badBool : Result Bool := util.transmute_unchecked Bool (2#u8)

theorem bad_bool_forbidden : badBool = .fail .undef := by
  simp [badBool, util.transmute_unchecked, Zerocopy.forbiddenExecution, UScalar.val]

noncomputable def discardCall : Result Unit := do let _ ← badBool; Result.ok ()
noncomputable def failThenDiverge : Result Unit := do let _ ← badBool; Result.div
def diverge : Result Unit := .div
spec discarded for discardCall with 0 type parameters
  ensures _ => True
partial spec beforeDivergence for failThenDiverge with 0 type parameters
  ensures _ => True

example : ¬discarded := by simp [discarded, discardCall, bad_bool_forbidden]
example : ¬beforeDivergence := by simp [beforeDivergence, failThenDiverge, bad_bool_forbidden]

-- Even a contract that says nothing about the output must prove its execution
-- judgment. Partial contracts permit divergence, but never preceding UB.
partial spec diverges for diverge with 0 type parameters
  ensures _ => True
example : diverges := WP.dspec.div _

end SafetyTests
