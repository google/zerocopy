/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Aeneas
public section
open Aeneas Aeneas.Std

namespace AeneasContracts

/-- An indexed Rust loop refines a mathematical prefix computation. The
caller proves one body step: continue advances the index by one, while done
occurs at the length. This rule supplies the index bounds and termination
measure, and carries an arbitrary representation invariant. -/
theorem indexed_loop_spec {State Model : Type}
    (length : Nat) (view : State → Model) (prefixValue : Nat → Model)
    (valid : State → Prop)
    (body : State × Usize → Result (ControlFlow (State × Usize) State))
    (hbody : ∀ state i, i.val ≤ length → view state = prefixValue i.val → valid state →
      body (state, i) ⦃ r => match r with
        | .cont (next, j) => i.val < length ∧ j.val = i.val + 1 ∧
          view next = prefixValue j.val ∧ valid next
        | .done out => i.val = length ∧ view out = prefixValue i.val ∧ valid out ⦄)
    (state : State) (i : Usize)
    (hi : i.val ≤ length) (hv : view state = prefixValue i.val) (hc : valid state) :
    loop body (state, i) ⦃ out => view out = prefixValue length ∧ valid out ⦄ := by
  apply loop.spec_decr_nat
    (fun s : State × Usize => length - s.2.val)
    (fun s => s.2.val ≤ length ∧ view s.1 = prefixValue s.2.val ∧ valid s.1)
  · rintro ⟨state, i⟩ ⟨hi, hv, hc⟩
    apply WP.spec_mono (hbody state i hi hv hc)
    intro r hr
    cases r with
    | done out =>
      obtain ⟨hend, hv, hc⟩ := hr
      exact ⟨hend ▸ hv, hc⟩
    | cont s =>
      rcases s with ⟨next, j⟩
      obtain ⟨hlt, hj, hv, hc⟩ := hr
      exact ⟨⟨by scalar_tac, hv, hc⟩, by scalar_tac⟩
  · exact ⟨hi, hv, hc⟩

end AeneasContracts
