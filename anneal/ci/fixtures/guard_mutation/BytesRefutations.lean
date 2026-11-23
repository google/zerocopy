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

/-- Little-endian program that allocates `_1 : u32` in memory and stores
`0x01020304` into `_1`. -/
noncomputable def progStoreIndirectLe : Program :=
  mkSingleBlockProg 0 [u32Ty, u32Ty]
    [.storageLive 1,
     .assign ⟨1, []⟩
       (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0x01020304)⟩))]

/-- Big-endian program with the same body as `progStoreIndirectLe`. -/
noncomputable def progStoreIndirectBe : Program :=
  { progStoreIndirectLe with targetEndian := .big }

/-- Guard `bytes_decode_endian_little`: `decodeUInt .little` decodes
`[4, 3, 2, 1]` as `0x01020304` rather than reversing bytes as big-endian. -/
theorem refute_bytes_decode_endian_little :
    decodeUInt .little [4, 3, 2, 1] = 0x01020304 :=
  rfl

/-- Guard `bytes_decode_endian_big`: `decodeUInt .big` decodes `[1, 2, 3, 4]`
as `0x01020304` rather than reading little-endian byte order. -/
theorem refute_bytes_decode_endian_big :
    decodeUInt .big [1, 2, 3, 4] = 0x01020304 :=
  rfl

/-- Guard `step_endian_propagates_little`: `evalStep` threads
`p.targetEndian = .little` into `evalStatement` and `storeIndirect`, storing
`[0x04, 0x03, 0x02, 0x01]` for `0x01020304u32`. -/
theorem refute_step_endian_propagates_little :
    (match initState progStoreIndirectLe queryEmpty with
     | .ok s₀ =>
       match evalStep progStoreIndirectLe 0 s₀ with
       | .step s₁ =>
         match forceAllocation progStoreIndirectLe s₁ 1 with
         | .ok (s₂, place) =>
           match evalStep progStoreIndirectLe 0 s₂ with
           | .step s₃ =>
             readBytes s₃.mem place 4 2 =
               .ok [.init 4 none, .init 3 none, .init 2 none, .init 1 none]
           | _ => False
         | .error _ => False
       | _ => False
     | .error _ => False) :=
  rfl

/-- Guard `step_endian_propagates_big`: `evalStep` threads
`p.targetEndian = .big` into `evalStatement` and `storeIndirect`, storing
`[0x01, 0x02, 0x03, 0x04]` for `0x01020304u32`. -/
theorem refute_step_endian_propagates_big :
    (match initState progStoreIndirectBe queryEmpty with
     | .ok s₀ =>
       match evalStep progStoreIndirectBe 0 s₀ with
       | .step s₁ =>
         match forceAllocation progStoreIndirectBe s₁ 1 with
         | .ok (s₂, place) =>
           match evalStep progStoreIndirectBe 0 s₂ with
           | .step s₃ =>
             readBytes s₃.mem place 4 2 =
               .ok [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
           | _ => False
         | .error _ => False
       | _ => False
     | .error _ => False) :=
  rfl

end GuardMutation
