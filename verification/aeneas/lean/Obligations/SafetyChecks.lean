/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy
@[expose] public section
open Aeneas Aeneas.Std
namespace Zerocopy.Obligations

-- The independent expectations describe all inputs, including rejected bytes
-- and insufficient destinations. They are propositions, not trusted axioms.
def checked_bool_spec_contract (byte : U8) (run : Result (Option Bool)) : Prop :=
  run ⦃ out => out = if byte.val < 2 then some (decide (byte.val = 1)) else none ⦄

def checked_bool_spec : Prop :=
  ∀ byte, checked_bool_spec_contract byte (util.safety_checks.checked_bool byte)

def checked_copy_spec_contract (src dst : Slice U8)
    (run : Result (Bool × Slice U8)) : Prop :=
  run ⦃ out => out.1 = decide (src.val.length ≤ dst.val.length) ∧
    out.2.val = if src.val.length ≤ dst.val.length
      then src.val ++ dst.val.drop src.val.length else dst.val ⦄

def checked_copy_spec : Prop :=
  ∀ src dst, checked_copy_spec_contract src dst (util.safety_checks.checked_copy src dst)

end Zerocopy.Obligations
