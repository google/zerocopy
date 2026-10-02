/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Proofs.Util
@[expose] public section

/-!
The Rust assertions are the application promise. These lemmas connect the
extracted remainder calculations to the already proved bitwise helpers. The
canonical theorem establishes successful execution of the entire harness,
including both assertions, for every accepted input.
-/
open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.Raw

theorem arithmetic_checks (len : Usize) (align : NonZeroUsize) :
    util.checks.check_arithmetic len align ⦃ _ => True ⦄ := by
  unfold util.checks.check_arithmetic
  simp only [core.num.nonzero.NonZero.get, bind_ok]
  step as ⟨pow2, hp⟩
  split
  · rename_i enabled
    have power : align.val.val.isPowerOfTwo := by
      exact Eq.mp hp enabled
    have positive := Nat.pos_of_isPowerOfTwo power
    step as ⟨remainder, hr⟩
    step as ⟨gap, hg⟩
    step as ⟨padding, hpadding⟩
    step with padding_lt_alignment len align power as ⟨actual, _, exactPadding, _⟩
    step
    step with round_down_spec len align power as ⟨rounded, _, exactRounded, _⟩
    step as ⟨expected, hexpected⟩
    · rw [hr]
      exact Nat.mod_le _ _
    · step
  · simp only [WP.spec_ok]

end Zerocopy.Proofs.Raw

namespace Zerocopy.Proofs

theorem arithmetic_checks_spec : Specs.arithmetic_checks_spec := by
  intro len align _ _ _ _
  apply WP.spec_mono (Raw.arithmetic_checks len align)
  intro result _
  exact ⟨(), rfl, trivial⟩

end Zerocopy.Proofs
