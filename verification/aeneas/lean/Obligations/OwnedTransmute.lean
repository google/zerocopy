/- Copyright 2026 The Fuchsia Authors
SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT -/

module
public import Obligations.Byteorder
@[expose] public section
open Aeneas Aeneas.Std
namespace Zerocopy.Obligations

-- Retain the independent positional digit expectations used for numerical
-- byteorder. These expectations inspect arbitrary outcomes, not executions.
def owned_transmute_to_bytes_spec_contract (value : U32)
    (run : Result (Aeneas.Std.Array U8 4#usize)) : Prop :=
  write_u32_le_spec_contract value run

def owned_transmute_to_bytes_spec : Prop :=
  ∀ value, owned_transmute_to_bytes_spec_contract value (util.owned_transmute.to_bytes value)

def owned_transmute_from_bytes_spec_contract (bytes : Aeneas.Std.Array U8 4#usize)
    (run : Result U32) : Prop := read_u32_le_spec_contract bytes run

def owned_transmute_from_bytes_spec : Prop :=
  ∀ bytes, owned_transmute_from_bytes_spec_contract bytes (util.owned_transmute.from_bytes bytes)

def owned_transmute_bool_spec_contract (byte : U8) (run : Result (Option Bool)) : Prop :=
  run ⦃ output => match output with
    | none => 2 ≤ byte.val
    | some value => byte.val < 2 ∧ value = decide (byte.val = 1) ⦄

def owned_transmute_bool_spec : Prop :=
  ∀ byte, owned_transmute_bool_spec_contract byte (util.owned_transmute.checked_bool byte)

def owned_transmute_round_trip_checks_spec_contract (_value : U32) (run : Result Unit) : Prop :=
  run ⦃ _ => True ⦄

def owned_transmute_round_trip_checks_spec : Prop :=
  ∀ value, owned_transmute_round_trip_checks_spec_contract value
    (util.owned_transmute.round_trip_checks value)

end Zerocopy.Obligations
