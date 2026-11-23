-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import InitialCache
import SymExec

namespace ProductionPaths

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Endianness
  ProductionReduction SymExec

/-!
Each concrete `(flag, width)` control choice runs the captured body over a
free input word. The kernel evaluates `symRun` on `sourceBody` itself, so no
local, block or statement index, and no state vector, appears here. Nothing
here assumes a result; `ProductionEndpoints` fixes the expected words.
-/

/-- Entry arguments with a concrete flag and width and a symbolic value. -/
noncomputable def sArgs (flag : Bool) (width : Nat) : List SVal :=
  [.conc (.bool flag), .conc (dataWidthVal width), .word .input]

/-- Step budget; a run stops at its first return, so slack costs nothing. -/
def fuel : Nat := 4096

/-- The word the source returns on one control path, if supported. -/
noncomputable def pathWord (flag : Bool) (width : Nat) : Option Sym :=
  (symRun sourceBody fuel (sEntry sourceBody (sArgs flag width))).bind
    SVal.sym?

theorem path_sound {flag : Bool} {width : Nat} {s : Sym}
    {endian : TargetEndian} (h : pathWord flag width = some s) (value : Word) :
    Safe endian sourceBody (endianArgs flag width value) ∧
      Returns endian sourceBody (endianArgs flag width value)
        (u64Val (s.eval value)) := by
  obtain ⟨v, hr, hs⟩ := Option.bind_eq_some_iff.mp h
  have run := symRun_entry (endian := endian) value hr
  rw [SVal.sym?_sound value hs] at run
  exact run

end ProductionPaths
