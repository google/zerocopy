/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy.FunsExternal
public import Aeneas
@[expose] public section

/-!
Ignoring a result must not hide a forbidden execution. These kernel-checked
examples distinguish the unsafe arithmetic failure tag from ordinary panic,
and check propagation through sequencing under both total and partial contracts.
The Rust correspondence of the primitive models remains an explicit trust
premise; these examples establish properties of those Lean models.
-/
open Aeneas Aeneas.Std Zerocopy
namespace UnsafeArithmeticTests

theorem add_overflow_forbidden (left right : Usize)
    (overflow : Usize.max < left.val + right.val) :
    core.num.Usize.unchecked_add left right = .fail .undef := by
  simp [core.num.Usize.unchecked_add, forbiddenExecution, Nat.not_le_of_lt overflow]

theorem mul_overflow_forbidden (left right : Usize)
    (overflow : Usize.max < left.val * right.val) :
    core.num.Usize.unchecked_mul left right = .fail .undef := by
  simp [core.num.Usize.unchecked_mul, forbiddenExecution, Nat.not_le_of_lt overflow]

-- An unsupported model is also forbidden, rather than a claim of Rust panic.
theorem unsupported_nonzero_forbidden {T Inner : Type}
    (inst : core.num.nonzero.ZeroablePrimitive T Inner) (x : T)
    (unsupported : T ≠ Usize) :
    core.num.nonzero.NonZero.new inst x = .fail .undef := by
  classical
  simp [core.num.nonzero.NonZero.new, unsupported, forbiddenExecution]

-- Even a continuation which ignores the value cannot absorb undef. This also
-- covers a continuation that would diverge: partial contracts must still fail.
theorem forbidden_bind {α β : Type} (next : α → Result β) :
    (forbiddenExecution >>= next) = .fail .undef := by
  simp [forbiddenExecution]

theorem total_forbidden_rejected {α β : Type} (next : α → Result β) :
    ¬ WP.spec (forbiddenExecution >>= next) (fun _ => True) := by
  simp [forbiddenExecution]

theorem partial_forbidden_rejected {α β : Type} (next : α → Result β) :
    ¬ WP.dspec (forbiddenExecution >>= next) (fun _ => True) := by
  simp [forbiddenExecution]

-- Both real unsafe operations must retain this rejection when their result is
-- discarded. The premise is overflow, not an assumption about a model outcome.
theorem ignored_add_rejected (left right : Usize)
    (overflow : Usize.max < left.val + right.val) :
    ¬ WP.dspec (do let _ ← core.num.Usize.unchecked_add left right; pure ())
      (fun _ => True) := by
  rw [add_overflow_forbidden left right overflow]
  simp

theorem ignored_mul_rejected (left right : Usize)
    (overflow : Usize.max < left.val * right.val) :
    ¬ WP.spec (do let _ ← core.num.Usize.unchecked_mul left right; pure ())
      (fun _ => True) := by
  rw [mul_overflow_forbidden left right overflow]
  simp

end UnsafeArithmeticTests
