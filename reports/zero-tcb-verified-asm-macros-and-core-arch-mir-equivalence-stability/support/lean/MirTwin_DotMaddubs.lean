-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Omega
import AsmMirBase
import IsaLemmas

namespace LockedObligations

open AsmMirBase IsaLemmas

private theorem dotMirLoopAcc_sum (mem8 : Nat → UInt8) (uBase sBase : Nat) :
    ∀ (k : Nat), ymmSum8Mod32 (dotMirLoopAcc mem8 uBase sBase (2 * k)) =
      dotBlocks64Spec mem8 uBase sBase k
  | 0 => rfl
  | k + 1 => by
    have e2 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [e2]
    dsimp only [dotMirLoopAcc, dotBlocks64Spec]
    rw [ymmSum8_vpaddd256, ymmSum8_vpaddd256, dotMirLoopAcc_sum mem8 uBase sBase k]
    have o0 : 32 * (2 * k) = 64 * k := by omega
    have o1 : 32 * (2 * k + 1) = 64 * k + 32 := by omega
    rw [o0, o1, Nat.mod_add_mod]

theorem verify_dot_maddubs_mir_twin (mem8 : Nat → UInt8) (uBase sBase blocks64 : Nat) :
    dotAvx2MirTwin mem8 uBase sBase blocks64 = dotBlocks64Spec mem8 uBase sBase blocks64 := by
  unfold dotAvx2MirTwin
  have hred := horizontal_reduce_256 (dotMirLoopAcc mem8 uBase sBase (2 * blocks64))
  dsimp only at hred
  rw [hred]
  exact dotMirLoopAcc_sum mem8 uBase sBase blocks64

end LockedObligations
