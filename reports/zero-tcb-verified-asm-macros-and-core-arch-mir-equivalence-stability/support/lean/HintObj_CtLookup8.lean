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
def ctLookup8Cert : CtLinearScan8Cert :=
  { p0 := 0,   p1 := 2,   p2 := 5,   p3 := 9,   p4 := 13,  p5 := 17,  p6 := 21,
    p7 := 25,  p8 := 29,  p9 := 33,  p10 := 37, p11 := 41, p12 := 45, p13 := 49,
    p14 := 53, p15 := 57, p16 := 61, p17 := 65, p18 := 69, p19 := 73, p20 := 77,
    p21 := 81, p22 := 85, p23 := 89, p24 := 93, p25 := 97 }

end UntrustedHints

namespace LockedObligations

open AsmMirBase

theorem verify_ct_lookup8_obj (s : X86State)
    (hrip : s.rip = 0) (hnh : s.halted = false) (hnf : s.fault = false) (hymm : s.ymmDirty = false) :
    let sf := run ctObjBytes 26 s
    sf.halted = true ∧
    sf.fault = false ∧
    sf.gpr .rsp = s.gpr .rsp ∧
    sf.mem64 = s.mem64 ∧
    sf.gpr .rax = lookup8Spec s (s.gpr .rdi) (s.gpr .rsi % W64) := by
  have h := UntrustedHints.checkCtLinearScan8Cert_exec
    (code := ctObjBytes) (c := UntrustedHints.ctLookup8Cert)
    s rfl hrip hnh hnf hymm
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem verify_ct_lookup8_2safety (s1 s2 : X86State)
    (hrip1 : s1.rip = 0) (hnh1 : s1.halted = false) (hnf1 : s1.fault = false) (hymm1 : s1.ymmDirty = false)
    (hrip2 : s2.rip = 0) (hnh2 : s2.halted = false) (hnf2 : s2.fault = false) (hymm2 : s2.ymmDirty = false)
    (hpub : s1.gpr .rdi = s2.gpr .rdi) (hleak : s1.leak = s2.leak) :
    (run ctObjBytes 26 s1).leak = (run ctObjBytes 26 s2).leak :=
  UntrustedHints.checkCtLinearScan8Cert_2safety
    (code := ctObjBytes) (c := UntrustedHints.ctLookup8Cert)
    s1 s2 rfl hrip1 hnh1 hnf1 hymm1 hrip2 hnh2 hnf2 hymm2 hpub hleak

end LockedObligations
