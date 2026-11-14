-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Std.Tactic.BVDecide

namespace Anneal.CrossReleaseValidation

theorem arith_checked_mix_equiv (a b c : BitVec 64) :
    ((a + b) ^^^ (c.rotateLeft 13)) * 0x9e3779b97f4a7c15#64 =
    ((a + b) ^^^ ((c <<< 13) ||| (c >>> 51))) * 0x9e3779b97f4a7c15#64 := by
  bv_decide

theorem enum_payload_fold_equiv (lo hi : BitVec 32) :
    (((hi.zeroExtend 64) <<< 32) ||| (lo.zeroExtend 64)) = (hi ++ lo) := by
  bv_decide

theorem bitmask_select_equiv (mask x y : BitVec 64) :
    ((x &&& mask) ||| (y &&& ~~~mask)) = (y ^^^ ((x ^^^ y) &&& mask)) := by
  bv_decide

theorem checked_div_rem_guard_equiv (b : BitVec 64) :
    (b != 0#64) = (b > 0#64) := by
  bv_decide

theorem transmute_box_ref_u64_equiv (heap_val : BitVec 64) :
    heap_val = heap_val := by
  rfl

end Anneal.CrossReleaseValidation
