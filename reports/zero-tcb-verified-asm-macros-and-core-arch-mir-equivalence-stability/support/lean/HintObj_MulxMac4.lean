-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import AsmMirBase
import UntrustedHints

namespace UntrustedHints

-- Auto-emitted by `asm_verified!` + ELF `.o` symbol byte-offset extractor (0 manual LOC)
def mulxMac4Cert : DualCarryMac4Cert :=
  { p0 := 0,   p1 := 2,   p2 := 4,   p3 := 9,   p4 := 15,
    p5 := 18,  p6 := 24,  p7 := 30,  p8 := 37,  p9 := 41,
    p10 := 47, p11 := 53, p12 := 60, p13 := 64, p14 := 70,
    p15 := 76, p16 := 83, p17 := 87, p18 := 93, p19 := 99 }

end UntrustedHints

namespace LockedObligations

open AsmMirBase

theorem verify_mulx_mac4_obj (s : X86State)
    (hrip : s.rip = 0) (hnh : s.halted = false) (hnf : s.fault = false) (hymm : s.ymmDirty = false)
    (hrdi : s.gpr .rdi + 24 < W64) (hrsi : s.gpr .rsi + 24 < W64)
    (hdisj : s.gpr .rdi + 32 ≤ s.gpr .rsi ∨ s.gpr .rsi + 32 ≤ s.gpr .rdi) :
    let sf := run mulxObjBytes 20 s
    let rdi := s.gpr .rdi
    let rsi := s.gpr .rsi
    sf.halted = true ∧
    sf.fault = false ∧
    sf.cf = false ∧
    sf.of_ = false ∧
    sf.gpr .rsp = s.gpr .rsp ∧
    sf.gpr .rbx = s.gpr .rbx ∧
    val5Limbs (readMem64 sf rdi) (readMem64 sf (rdi + 8))
              (readMem64 sf (rdi + 16)) (readMem64 sf (rdi + 24)) (sf.gpr .rax) =
      mac4RefVal (readMem64 s rdi) (readMem64 s (rdi + 8))
                 (readMem64 s (rdi + 16)) (readMem64 s (rdi + 24))
                 (readMem64 s rsi) (readMem64 s (rsi + 8))
                 (readMem64 s (rsi + 16)) (readMem64 s (rsi + 24))
                 (s.gpr .rdx % W64) :=
  UntrustedHints.checkDualCarryMac4Cert_sound
    (code := mulxObjBytes) (c := UntrustedHints.mulxMac4Cert)
    s rfl hrip hnh hnf hymm hrdi hrsi hdisj

end LockedObligations
