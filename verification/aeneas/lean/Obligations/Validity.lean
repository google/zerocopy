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

-- These expectations retain all raw candidate values. A decoder rejecting bad
-- candidates at the INPUT would conceal precisely the cases being validated.
def bool_encoding_spec_contract (byte : U8) (run : Result Bool) : Prop :=
  run ⦃ out => out = decide (byte.val = 0 ∨ byte.val = 1) ⦄
def bool_encoding_spec : Prop :=
  ∀ byte, bool_encoding_spec_contract byte (util.validity.bool_encoding byte)

def nonzero_encoding_spec_contract (n : Usize) (run : Result Bool) : Prop :=
  run ⦃ out => out = decide (n.val ≠ 0) ⦄
def nonzero_encoding_spec : Prop :=
  ∀ n, nonzero_encoding_spec_contract n (util.validity.nonzero_encoding n)

def checked_nonzero_spec_contract (n : Usize)
    (run : Result (Option (core.num.nonzero.NonZero Usize
      core.num.niche_types.NonZeroUsizeInner))) : Prop :=
  run ⦃ out => match out with
    | none => n.val = 0
    | some value => value.val = n ∧ 0 < value.val.val ⦄
def checked_nonzero_spec : Prop :=
  ∀ n, checked_nonzero_spec_contract n (util.safety_checks.checked_nonzero n)

def checked_bool_pair_spec_contract (bytes : Aeneas.Std.Array U8 2#usize)
    (run : Result (Option (Aeneas.Std.Array Bool 2#usize))) : Prop :=
  run ⦃ out => match out with
    | none => ∃ byte ∈ bytes.val, 2 ≤ byte.val
    | some values => values.val = bytes.val.map (fun byte => decide (byte.val = 1)) ∧
        ∀ byte ∈ bytes.val, byte.val < 2 ⦄
def checked_bool_pair_spec : Prop :=
  ∀ bytes, checked_bool_pair_spec_contract bytes (util.safety_checks.checked_bool_pair bytes)

def bool_slice_valid_spec_contract (bytes : Slice U8) (run : Result Bool) : Prop :=
  run ⦃ out => out = decide (∀ byte ∈ bytes.val, byte.val < 2) ⦄
def bool_slice_valid_spec : Prop :=
  ∀ bytes, bool_slice_valid_spec_contract bytes (util.safety_checks.bool_slice_valid bytes)

end Zerocopy.Obligations
