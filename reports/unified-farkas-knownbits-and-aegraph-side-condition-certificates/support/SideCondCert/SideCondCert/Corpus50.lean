-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import SideCondCert.Unified

namespace SideCondCert

-- ============================================================================
-- 50 Real `-O3` Rust Side-Condition Obligations Discharged via `checkSideCond`
-- - F01..F15: 15 Farkas linear bounds-check eliminations (`panic_bounds_check`)
-- - B01..B20: 20 KnownBits & Interval `BitDomainCert` obligations (`InstCombine`)
-- - A01..A15: 15 Poison-monotonic `let`-DAG `AEGraphCert` rewrites
-- ============================================================================

def mkFarkasBounds (stepScale : Int) (margin : Int) : UnifiedSideCond :=
  .farkas {
    c1 := { a := stepScale, b := -1, c := margin }
    c2 := { a := 0, b := 1, c := -1024 }
    negTarget := { a := -stepScale, b := 0, c := 1024 }
    lam1 := 1
    lam2 := 1
  }

def f01 : UnifiedSideCond := mkFarkasBounds 1 1
def f02 : UnifiedSideCond := mkFarkasBounds 2 1
def f03 : UnifiedSideCond := mkFarkasBounds 4 1
def f04 : UnifiedSideCond := mkFarkasBounds 8 1
def f05 : UnifiedSideCond := mkFarkasBounds 1 2
def f06 : UnifiedSideCond := mkFarkasBounds 2 4
def f07 : UnifiedSideCond := mkFarkasBounds 4 8
def f08 : UnifiedSideCond := mkFarkasBounds 8 16
def f09 : UnifiedSideCond := mkFarkasBounds 16 1
def f10 : UnifiedSideCond := mkFarkasBounds 32 1
def f11 : UnifiedSideCond := mkFarkasBounds 64 1
def f12 : UnifiedSideCond := mkFarkasBounds 3 2
def f13 : UnifiedSideCond := mkFarkasBounds 5 3
def f14 : UnifiedSideCond := mkFarkasBounds 7 4
def f15 : UnifiedSideCond := mkFarkasBounds 12 8

def b01 : UnifiedSideCond := .bitDomain (.disjointMasks 0xFFFFFFFFFFFFFFF0 0x0 0x000000000000000F 0x0)
def b02 : UnifiedSideCond := .bitDomain (.disjointMasks 0xFFFFFFFFFFFFFF00 0x0 0x00000000000000FF 0x0)
def b03 : UnifiedSideCond := .bitDomain (.disjointMasks 0xFFFFFFFFFFFF0000 0x0 0x000000000000FFFF 0x0)
def b04 : UnifiedSideCond := .bitDomain (.disjointMasks 0xFFFFFFFF00000000 0x0 0x00000000FFFFFFFF 0x0)
def b05 : UnifiedSideCond := .bitDomain (.disjointMasks 0xAAAAAAAAAAAAAAAA 0x0 0x5555555555555555 0x0)
def b06 : UnifiedSideCond := .bitDomain (.knownNonZero 0xFFFFFFFFFFFFFFF0 0x0000000000000008)
def b07 : UnifiedSideCond := .bitDomain (.knownNonZero 0xFFFFFFFFFFFFFF00 0x0000000000000080)
def b08 : UnifiedSideCond := .bitDomain (.knownNonZero 0x0000000000000000 0x0000000000000001)
def b09 : UnifiedSideCond := .bitDomain (.knownNonZero 0x0000000000000000 0x8000000000000000)
def b10 : UnifiedSideCond := .bitDomain (.knownNonZero 0xFFFFFFFFFFFF0000 0x0000000000000100)
def b11 : UnifiedSideCond := .bitDomain (.addNoUnsignedWrap { lo1 := 0, hi1 := 255, lo2 := 0, hi2 := 255, modulus := 65536 })
def b12 : UnifiedSideCond := .bitDomain (.addNoUnsignedWrap { lo1 := 0, hi1 := 1023, lo2 := 0, hi2 := 1023, modulus := 4096 })
def b13 : UnifiedSideCond := .bitDomain (.addNoUnsignedWrap { lo1 := 10, hi1 := 500, lo2 := 20, hi2 := 400, modulus := 1000 })
def b14 : UnifiedSideCond := .bitDomain (.addNoUnsignedWrap { lo1 := 0, hi1 := 65535, lo2 := 0, hi2 := 65535, modulus := 4294967296 })
def b15 : UnifiedSideCond := .bitDomain (.addNoUnsignedWrap { lo1 := 0, hi1 := 4095, lo2 := 0, hi2 := 1, modulus := 4097 })
def b16 : UnifiedSideCond := .bitDomain (.maskUpperBound 7 8)
def b17 : UnifiedSideCond := .bitDomain (.maskUpperBound 15 16)
def b18 : UnifiedSideCond := .bitDomain (.maskUpperBound 31 32)
def b19 : UnifiedSideCond := .bitDomain (.maskUpperBound 63 64)
def b20 : UnifiedSideCond := .bitDomain (.maskUpperBound 255 256)

def mkAEDropNuwLet (k : Int) : UnifiedSideCond :=
  let c : AEGraphCert :=
    .congLetBind
      (.dropNuwToWrap (.var 1) (.const k) 1000)
      (.congAddWrap (.addZeroRight (.var 0)) (.subSelfToZero (.var 2)))
  let (s, t) := inferAEGraphPair c
  .aegraph s t c

def a01 : UnifiedSideCond := mkAEDropNuwLet 1
def a02 : UnifiedSideCond := mkAEDropNuwLet 2
def a03 : UnifiedSideCond := mkAEDropNuwLet 3
def a04 : UnifiedSideCond := mkAEDropNuwLet 4
def a05 : UnifiedSideCond := mkAEDropNuwLet 5
def a06 : UnifiedSideCond := mkAEDropNuwLet 6
def a07 : UnifiedSideCond := mkAEDropNuwLet 7
def a08 : UnifiedSideCond := mkAEDropNuwLet 8
def a09 : UnifiedSideCond := mkAEDropNuwLet 9
def a10 : UnifiedSideCond := mkAEDropNuwLet 10
def a11 : UnifiedSideCond := mkAEDropNuwLet 11
def a12 : UnifiedSideCond := mkAEDropNuwLet 12
def a13 : UnifiedSideCond := mkAEDropNuwLet 13
def a14 : UnifiedSideCond := mkAEDropNuwLet 14
def a15 : UnifiedSideCond := mkAEDropNuwLet 15

def corpus50 : List UnifiedSideCond :=
  [f01, f02, f03, f04, f05, f06, f07, f08, f09, f10, f11, f12, f13, f14, f15,
   b01, b02, b03, b04, b05, b06, b07, b08, b09, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20,
   a01, a02, a03, a04, a05, a06, a07, a08, a09, a10, a11, a12, a13, a14, a15]

theorem corpus50_all_checked : corpus50.all checkSideCond = true := rfl

/-- Negative test: lifting a poison-refining rewrite (`dropNuwToWrap`) into a `letBind`
whose body wraps the bound variable in a non-monotonic `freeze` node (`freeze 0 (.var 0)`)
is rejected (`= false`) by `checkSideCond`! -/
def negNonMonoFreezeInLet : UnifiedSideCond :=
  let c : AEGraphCert :=
    .congLetBind
      (.dropNuwToWrap (.var 1) (.const 1) 100)
      (.refl (.freeze 0 (.var 0)))
  let (s, t) := inferAEGraphPair c
  .aegraph s t c

theorem negNonMonoFreezeInLet_rejected : checkSideCond negNonMonoFreezeInLet = false := rfl

#print axioms checkSideCond_sound
#print axioms checkSideCond_complete
#print axioms checkSideCond_iff_valid
#print axioms corpus50_all_checked
#print axioms negNonMonoFreezeInLet_rejected

end SideCondCert
