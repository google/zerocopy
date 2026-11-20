/- Probe B3: which data-structure primitives does the KERNEL reduce (decide +kernel)?
   Each line is an independent `example`; failures are reported as errors. -/
import Std.Data.HashMap
import Std.Data.ExtHashMap
import Std.Data.ExtDHashMap

-- Platform word size: `System.Platform.numBits` is defined via an opaque `getNumBits`.
example : System.Platform.numBits = 64 := by decide +kernel
-- USize arithmetic depends on numBits
example : (5 : USize).toNat = 5 := by decide +kernel
-- UInt64 arithmetic (UInt64 is a structure over BitVec 64)
example : (0xFFFFFFFFFFFFFFFF : UInt64) + 1 = 0 := by decide +kernel
-- hashing a Nat (used by HashMap)
example : hash (5 : Nat) = 5 := by decide +kernel
-- Std.HashMap lookup after insert
example : ((∅ : Std.HashMap Nat Nat).insert 1 2).get? 1 = some 2 := by decide +kernel
-- Std.ExtHashMap (quotient) lookup after insert
example : ((∅ : Std.ExtHashMap Nat Nat).insert 1 2).get? 1 = some 2 := by decide +kernel
-- Array (List-backed in the kernel) set/get
example : ((Array.replicate 32 (0 : Nat)).set! 7 9)[7]! = 9 := by decide +kernel
-- BitVec 64 multiply / udiv / sdiv / umod literals (Nat GMP acceleration)
example : (0x123456789abcdef#64 * 0xfedcba987654321#64) = 0x22236d88fe5618cf#64 := by decide +kernel
example : (0xffffffffffffffff#64 / 7#64) = 0x2492492492492492#64 := by decide +kernel
example : (BitVec.sdiv (-7#64) 2#64) = -3#64 := by decide +kernel
-- String literal equality (used e.g. by Sail error messages)
example : "abc" ++ "d" = "abcd" := by decide +kernel
