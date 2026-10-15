/- Copyright 2026 The Fuchsia Authors
SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT -/

module
public import RequiredModelContracts.Byteorder
public import Obligations.OwnedTransmute
@[expose] public section
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

-- These bridges reuse positional digit expectations, not implementation
-- correctness. Every provided hypothesis is about the same arbitrary run.
@[contract_simps] theorem required_owned_transmute_to_bytes (value : U32)
    (run : Result (Aeneas.Std.Array U8 4#usize))
    (provided : Specs.owned_transmute_to_bytes_spec_contract value run) :
    Obligations.owned_transmute_to_bytes_spec_contract value run := by
  exact required_write_u32_le value run provided

@[contract_simps] theorem required_owned_transmute_from_bytes (bytes : Aeneas.Std.Array U8 4#usize)
    (run : Result U32) (provided : Specs.owned_transmute_from_bytes_spec_contract bytes run) :
    Obligations.owned_transmute_from_bytes_spec_contract bytes run := by
  exact required_read_u32_le bytes run provided

@[contract_simps] theorem required_owned_transmute_bool (byte : U8)
    (run : Result (Option Bool)) (provided : Specs.owned_transmute_bool_spec_contract byte run) :
    Obligations.owned_transmute_bool_spec_contract byte run := by
  apply WP.spec_mono (provided (unsignedWord byte) rfl)
  rintro output ⟨value, decoded, facts⟩
  have identityDecode : RustModel.decode output = some output := by
    cases output <;> rfl
  have same : value = output := Option.some.inj (decoded.symm.trans identityDecode)
  subst value
  cases output <;> exact facts

@[contract_simps] theorem required_owned_transmute_round_trip_checks (value : U32)
    (run : Result Unit) (provided : Specs.owned_transmute_round_trip_checks_spec_contract value run) :
    Obligations.owned_transmute_round_trip_checks_spec_contract value run := by
  apply WP.spec_mono (provided (unsignedWord value) rfl)
  rintro _ ⟨_, _, _⟩
  trivial

end Zerocopy.Proofs
