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
def dotUnroll2Cert : SimdDotUnroll2Cert :=
  { p0 := 0,   p1 := 4,   p2 := 8,   p3 := 11,  p4 := 13,  p5 := 17,  p6 := 22,  p7 := 26,
    p8 := 28,  p9 := 33,  p10 := 38, p11 := 43, p12 := 47, p13 := 51, p14 := 57, p15 := 63,
    p16 := 68, p17 := 72, p18 := 76, p19 := 80, p20 := 83,
    p21 := 85, p22 := 89, p23 := 95, p24 := 99, p25 := 104, p26 := 108, p27 := 113, p28 := 117,
    p29 := 121, p30 := 124 }

end UntrustedHints

namespace LockedObligations

open AsmMirBase

theorem verify_dot_maddubs_obj (s : X86State)
    (hrip : s.rip = 0) (hnh : s.halted = false) (hnf : s.fault = false)
    (hblk : 64 * (s.gpr .rdx % W64) < W64) :
    let blocks := s.gpr .rdx % W64
    let sf := run dotObjBytes (18 + 13 * blocks) s
    sf.halted = true ∧
    sf.fault = false ∧
    sf.ymmDirty = false ∧
    sf.gpr .rsp = s.gpr .rsp ∧
    sf.mem64 = s.mem64 ∧
    sf.mem8 = s.mem8 ∧
    sf.gpr .rax = dotBlocks64Spec s.mem8 (s.gpr .rdi) (s.gpr .rsi) blocks :=
  UntrustedHints.checkSimdDotUnroll2Cert_sound
    (code := dotObjBytes) (c := UntrustedHints.dotUnroll2Cert)
    s rfl hrip hnh hnf hblk

end LockedObligations
