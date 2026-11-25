-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import GuardRefuteWf

/-!
# Negative Refutations for `Trusted.MirSemantics.Bytes` Validity Guards

Each theorem exercises one scalar-validity or uninitialized-byte UB guard in
`Trusted/MirSemantics/Bytes.lean` (`evalConstLit` for `bool`, `char`,
`Ordering`, and fieldless `enum`, plus `initBytes?` on indirect memory reads).
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

/-- Guard `bytes_invalid_bool_value`: a 1-byte `bool` scalar whose value is
`2` (neither `0` nor `1`) faults with `.undefined`. -/
theorem refute_bytes_invalid_bool_value :
    ReachesResult (mkConstRetProg .bool 2) queryEmpty (.fault .undefined) ∧
    ¬ WellFormed (mkConstRetProg .bool 2) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `bytes_invalid_char_surrogate`: a `char` constant holding surrogate
code point `0xD800` faults with `.undefined` rather than passing through
`Char.ofNat`. -/
theorem refute_bytes_invalid_char_surrogate :
    ReachesResult (mkConstRetProg .char 0xd800) queryEmpty
      (.fault .undefined) ∧
    ¬ WellFormed (mkConstRetProg .char 0xd800) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `bytes_invalid_ordering_tag`: a `core::cmp::Ordering` constant with
tag `2` (outside `{-1_i8, 0, 1}`) faults with `.undefined`. -/
theorem refute_bytes_invalid_ordering_tag :
    ReachesResult (mkConstRetProg .ordering 2) queryEmpty
      (.fault .undefined) ∧
    ¬ WellFormed (mkConstRetProg .ordering 2) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `bytes_invalid_enum_tag`: a `ReprU8 { A = 10, B = 20 }` constant
with tag `1` faults with `.undefined`. -/
theorem refute_bytes_invalid_enum_tag :
    ReachesResult (mkConstRetProg (.enum reprU8EnumTy) 1) queryEmpty
      (.fault .undefined) ∧
    ¬ WellFormed (mkConstRetProg (.enum reprU8EnumTy) 1) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program `StorageLive(_1: u32); _0 = copy _1; return`, used to test indirect
uninitialized-byte reads after `forceAllocation`. -/
noncomputable def progIndirectUninitRead : Program :=
  mkSingleBlockProg 0 [u32Ty, u32Ty]
    [.storageLive 1, .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]

/-- Guard `bytes_uninit_memory_read`: reading uninitialized bytes from an
indirect stack allocation via `initBytes?` / `decodeVal` / `loadIndirect`
faults with `.undefined`. -/
theorem refute_bytes_uninit_memory_read :
    (match initState progIndirectUninitRead queryEmpty with
     | .ok s₀ =>
       match evalStep progIndirectUninitRead 0 s₀ with
       | .step s₁ =>
         match forceAllocation progIndirectUninitRead s₁ 1 with
         | .ok (s₂, _) =>
           evalStep progIndirectUninitRead 0 s₂ = .fault .undefined
         | .error _ => False
       | _ => False
     | .error _ => False) :=
  rfl

/-- Guard `bytes_int_scalar_width_check`: `evalConstLit` rejects a `u8`
scalar literal exceeding 8 bits (`256`) with `.unsupported`. -/
theorem refute_bytes_int_scalar_width_check :
    ReachesResult (mkConstRetProg u8Ty 256) queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed (mkConstRetProg u8Ty 256) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `bytes_bool_scalar_width_check`: `evalConstLit` rejects a `bool`
scalar literal `0x100` exceeding 1 byte with `.unsupported` instead of reading
its zero low byte as `false`. -/
theorem refute_bytes_bool_scalar_width_check :
    ReachesResult (mkConstRetProg .bool 0x100) queryEmpty
      (.fault .unsupported) ∧
    ¬ WellFormed (mkConstRetProg .bool 0x100) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `bytes_char_scalar_width_check`: `evalConstLit` rejects a `char`
scalar literal exceeding 32 bits (`0x100000041`) with `.unsupported` rather than
reclassifying it as `.undefined`. -/
theorem refute_bytes_char_scalar_width_check :
    ReachesResult (mkConstRetProg .char 0x100000041) queryEmpty
      (.fault .unsupported) :=
  reachesResult_of_execFault (fuel := 1) rfl

/-- Guard `bytes_enum_tag_width_check`: `evalConstLit` rejects an enum tag
literal `0x10a` exceeding its 8-bit `tagW` width with `.unsupported` rather
than truncating it to valid tag `10`. -/
theorem refute_bytes_enum_tag_width_check :
    ReachesResult (mkConstRetProg (.enum reprU8EnumTy) 0x10a) queryEmpty
      (.fault .unsupported) ∧
    ¬ WellFormed (mkConstRetProg (.enum reprU8EnumTy) 0x10a) queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `bytes_decode_length_mismatch`: `decodeVal` rejects a byte slice
whose length differs from `layoutOfTy ty` with `.unsupported`. -/
theorem refute_bytes_decode_length_mismatch :
    decodeVal .little u32Ty [.init 0 none, .init 0 none] =
      .error .unsupported :=
  rfl

end GuardMutation
