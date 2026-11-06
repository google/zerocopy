-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Trusted
import Init.Omega

namespace GoodTheory

macro "solve_linear" : tactic => `(tactic| omega)

def stepDown (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => stepDown k
termination_by n

theorem targetSpec_gt (n : Nat) : Trusted.targetSpec n > n := by
  unfold Trusted.targetSpec
  solve_linear

end GoodTheory
