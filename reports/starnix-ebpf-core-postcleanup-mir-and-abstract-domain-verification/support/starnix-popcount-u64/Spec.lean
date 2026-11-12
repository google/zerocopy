-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.Mvp

namespace Spec

open Trusted.Mvp

/-- Structural-recursion model of Kernighan's bit-counting loop (`x &= x - 1`). -/
def kernighanSteps : Nat → Word → Word → Word
  | 0, _, count => count
  | fuel + 1, x, count =>
      if x != 0 then kernighanSteps fuel (x &&& (x - 1)) (count + 1)
      else count

/-- Exact functional specification of `verifier::popcount_u64(x)`. -/
def popcountSpec (x : Word) : Word :=
  kernighanSteps (x.toNat + 1) x 0

/-- Every 64-bit input `x` executes safely, terminates, and returns `popcountSpec x`,
    which satisfies the canonical Kernighan recurrence (`popcountSpec 0 = 0` and
    `x != 0 → popcountSpec x = popcountSpec (x &&& (x - 1)) + 1`). -/
def exactPopcount (body : Body) : Prop :=
  (∀ x : Word, Safe body [x] ∧ Returns body [x] (popcountSpec x)) ∧
  popcountSpec 0 = 0 ∧
  (∀ x : Word, (x != 0) = true → popcountSpec x = popcountSpec (x &&& (x - 1)) + 1)

def specs : Specs :=
  { safety := fun _ _ => True
    property := fun program => ∃ body, program.bodies = [body] ∧
      exactPopcount body }

end Spec
