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
open Aeneas Aeneas.Std AeneasSpecs Zerocopy
namespace NonZeroSafetyTests

-- These are model executions, not attempts to execute undefined Rust.
noncomputable def zeroConstructor :=
  core.num.nonzero.NonZero.new_unchecked
    Zerocopy.Usize.Insts.CoreNumNonzeroZeroablePrimitiveNonZeroUsizeInner (0#usize)

theorem zero_forbidden : zeroConstructor = .fail .undef := by
  simp [zeroConstructor, core.num.nonzero.NonZero.new_unchecked,
    Zerocopy.forbiddenExecution]

example : ¬ WP.spec zeroConstructor (fun _ => True) := by simp [zero_forbidden]
example : ¬ WP.dspec zeroConstructor (fun _ => True) := by simp [zero_forbidden]

noncomputable def discardZero : Result Unit := do let _ ← zeroConstructor; .ok ()
noncomputable def zeroBeforeDivergence : Result Unit := do let _ ← zeroConstructor; .div
spec discarded for discardZero with 0 type parameters
  ensures _ => True
partial spec beforeDivergence for zeroBeforeDivergence with 0 type parameters
  ensures _ => True

example : ¬discarded := by simp [discarded, discardZero, zero_forbidden]
example : ¬beforeDivergence := by
  simp [beforeDivergence, zeroBeforeDivergence, zero_forbidden]

theorem unsupported_carrier_forbidden {T Inner : Type}
    (inst : core.num.nonzero.ZeroablePrimitive T Inner) (x : T) (unsupported : T ≠ Usize) :
    core.num.nonzero.NonZero.new_unchecked inst x = .fail .undef := by
  simp [core.num.nonzero.NonZero.new_unchecked, unsupported, Zerocopy.forbiddenExecution]

-- A native dictionary alone supplies no alignment proposition. Without its
-- law, an alignment-two model reaches a forbidden zero constructor. The
-- premise here is a counterfactual model value, not an extra Rust assumption.
theorem missing_law_forbidden (T : Type) (dictionary : Zerocopy.Unaligned T) (x : Usize)
    (alignment : Zerocopy.RustLayout.align T = 2#usize) :
    Zerocopy.trait_checks.divide_by_unaligned dictionary x = .fail .undef := by
  have half : (1#usize / 2#usize : Result Usize) = .ok (0#usize) := by
    obtain ⟨result, call, numeric⟩ :=
      UScalar.div_spec (1#usize) (y := 2#usize) (by scalar_tac)
    have zero : result = 0#usize := by
      apply UScalar.eq_of_val_eq
      simpa using numeric
    simpa only [zero] using call
  simp [Zerocopy.trait_checks.divide_by_unaligned, core.mem.align_of, alignment,
    half, core.num.nonzero.NonZero.new_unchecked, Zerocopy.forbiddenExecution]

example (T : Type) (dictionary : Zerocopy.Unaligned T) (x : Usize)
    (alignment : Zerocopy.RustLayout.align T = 2#usize) :
    ¬ WP.spec (Zerocopy.trait_checks.divide_by_unaligned dictionary x) (fun _ => True) := by
  simp [missing_law_forbidden T dictionary x alignment]

example (T : Type) (dictionary : Zerocopy.Unaligned T) (x : Usize)
    (alignment : Zerocopy.RustLayout.align T = 2#usize) :
    ¬ WP.dspec (Zerocopy.trait_checks.divide_by_unaligned dictionary x) (fun _ => True) := by
  simp [missing_law_forbidden T dictionary x alignment]

end NonZeroSafetyTests
