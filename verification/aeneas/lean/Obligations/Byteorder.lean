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

/- These byteorder expectations retain the raw input domain. Readers must
return the positional base-256 value; writers must return every numeric byte,
including zeros. They deliberately use explicit digit arithmetic rather than
invoking the authored specification's shared decoder or encoder. -/

def read_u16_le_spec_contract (bytes : Aeneas.Std.Array U8 2#usize)
    (run : Result (U16)) : Prop :=
  run ⦃ output => output.val = bytes.val[0]!.val + 256 * (bytes.val[1]!.val) ⦄

def read_u16_le_spec : Prop :=
  ∀ (bytes : Aeneas.Std.Array U8 2#usize), read_u16_le_spec_contract bytes
    (byteorder.verification.read_u16_le bytes)

def write_u16_le_spec_contract (n : U16)
    (run : Result (Aeneas.Std.Array U8 2#usize)) : Prop :=
  run ⦃ output => output.val.map UScalar.val = [n.val % 256, n.val / 256 % 256] ⦄

def write_u16_le_spec : Prop :=
  ∀ (n : U16), write_u16_le_spec_contract n
    (byteorder.verification.write_u16_le n)

def set_u16_le_spec_contract (_bytes : Aeneas.Std.Array U8 2#usize) (n : U16)
    (run : Result (U16)) : Prop :=
  run ⦃ output => output = n ⦄

def set_u16_le_spec : Prop :=
  ∀ (bytes : Aeneas.Std.Array U8 2#usize) (n : U16), set_u16_le_spec_contract bytes n
    (byteorder.verification.set_u16_le bytes n)

def read_u16_be_spec_contract (bytes : Aeneas.Std.Array U8 2#usize)
    (run : Result (U16)) : Prop :=
  run ⦃ output => output.val = bytes.val[1]!.val + 256 * (bytes.val[0]!.val) ⦄

def read_u16_be_spec : Prop :=
  ∀ (bytes : Aeneas.Std.Array U8 2#usize), read_u16_be_spec_contract bytes
    (byteorder.verification.read_u16_be bytes)

def write_u16_be_spec_contract (n : U16)
    (run : Result (Aeneas.Std.Array U8 2#usize)) : Prop :=
  run ⦃ output => output.val.map UScalar.val = [n.val / 256 % 256, n.val % 256] ⦄

def write_u16_be_spec : Prop :=
  ∀ (n : U16), write_u16_be_spec_contract n
    (byteorder.verification.write_u16_be n)

def set_u16_be_spec_contract (_bytes : Aeneas.Std.Array U8 2#usize) (n : U16)
    (run : Result (U16)) : Prop :=
  run ⦃ output => output = n ⦄

def set_u16_be_spec : Prop :=
  ∀ (bytes : Aeneas.Std.Array U8 2#usize) (n : U16), set_u16_be_spec_contract bytes n
    (byteorder.verification.set_u16_be bytes n)

def read_u32_le_spec_contract (bytes : Aeneas.Std.Array U8 4#usize)
    (run : Result (U32)) : Prop :=
  run ⦃ output => output.val = bytes.val[0]!.val + 256 * (bytes.val[1]!.val + 256 * (bytes.val[2]!.val + 256 * (bytes.val[3]!.val))) ⦄

def read_u32_le_spec : Prop :=
  ∀ (bytes : Aeneas.Std.Array U8 4#usize), read_u32_le_spec_contract bytes
    (byteorder.verification.read_u32_le bytes)

def write_u32_le_spec_contract (n : U32)
    (run : Result (Aeneas.Std.Array U8 4#usize)) : Prop :=
  run ⦃ output => output.val.map UScalar.val = [n.val % 256, n.val / 256 % 256, n.val / 65536 % 256, n.val / 16777216 % 256] ⦄

def write_u32_le_spec : Prop :=
  ∀ (n : U32), write_u32_le_spec_contract n
    (byteorder.verification.write_u32_le n)

def set_u32_le_spec_contract (_bytes : Aeneas.Std.Array U8 4#usize) (n : U32)
    (run : Result (U32)) : Prop :=
  run ⦃ output => output = n ⦄

def set_u32_le_spec : Prop :=
  ∀ (bytes : Aeneas.Std.Array U8 4#usize) (n : U32), set_u32_le_spec_contract bytes n
    (byteorder.verification.set_u32_le bytes n)

def read_u32_be_spec_contract (bytes : Aeneas.Std.Array U8 4#usize)
    (run : Result (U32)) : Prop :=
  run ⦃ output => output.val = bytes.val[3]!.val + 256 * (bytes.val[2]!.val + 256 * (bytes.val[1]!.val + 256 * (bytes.val[0]!.val))) ⦄

def read_u32_be_spec : Prop :=
  ∀ (bytes : Aeneas.Std.Array U8 4#usize), read_u32_be_spec_contract bytes
    (byteorder.verification.read_u32_be bytes)

def write_u32_be_spec_contract (n : U32)
    (run : Result (Aeneas.Std.Array U8 4#usize)) : Prop :=
  run ⦃ output => output.val.map UScalar.val = [n.val / 16777216 % 256, n.val / 65536 % 256, n.val / 256 % 256, n.val % 256] ⦄

def write_u32_be_spec : Prop :=
  ∀ (n : U32), write_u32_be_spec_contract n
    (byteorder.verification.write_u32_be n)

def set_u32_be_spec_contract (_bytes : Aeneas.Std.Array U8 4#usize) (n : U32)
    (run : Result (U32)) : Prop :=
  run ⦃ output => output = n ⦄

def set_u32_be_spec : Prop :=
  ∀ (bytes : Aeneas.Std.Array U8 4#usize) (n : U32), set_u32_be_spec_contract bytes n
    (byteorder.verification.set_u32_be bytes n)

end Zerocopy.Obligations
