-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import RegAllocCert.Completeness

namespace RegAllocCert

/-- Canonical allocation map for the benchmark corpus:
- Virtual registers `0..10` map to physical GPRs `0..10` (`%rax..%r10`);
- Physical GPR `11` (`%r11`) is reserved as `reservedScratch` for parallel-move cycle breaking
  and caller-saved call clobbers;
- Virtual registers `v ≥ 11` spill to disjoint 8-byte stack frame slots `[8*(v-11), 8*(v-10))`. -/
def stdAlloc (v : VReg) : Loc :=
  if v < 11 then
    .preg { bank := .gpr, idx := v }
  else
    .spill { offset := (v - 11) * 8, sizeBytes := 8 }

def scratchR11 : PReg := { bank := .gpr, idx := 11 }
def calleeRbx  : PReg := { bank := .gpr, idx := 3 }
def calleeR12  : PReg := { bank := .gpr, idx := 12 }
def calleeR13  : PReg := { bank := .gpr, idx := 13 }

theorem stdAlloc_valid : ValidAllocMap stdAlloc scratchR11 := by
  constructor
  · intro v1 v2 h_eq
    dsimp [stdAlloc] at h_eq
    by_cases h1 : v1 < 11 <;> by_cases h2 : v2 < 11 <;> simp only [h1, h2, ↓reduceIte] at h_eq
    · injection h_eq with hp
      injection hp
    · contradiction
    · contradiction
    · injection h_eq with hs
      injection hs with h_off _
      have h_sub : v1 - 11 = v2 - 11 := Nat.eq_of_mul_eq_mul_right (by decide) h_off
      have h1' : 11 ≤ v1 := Nat.not_lt.mp h1
      have h2' : 11 ≤ v2 := Nat.not_lt.mp h2
      calc v1 = (v1 - 11) + 11 := (Nat.sub_add_cancel h1').symm
        _ = (v2 - 11) + 11 := by rw [h_sub]
        _ = v2 := Nat.sub_add_cancel h2'
  · intro v
    dsimp [stdAlloc, scratchR11]
    by_cases h1 : v < 11 <;> simp only [h1, ↓reduceIte]
    · intro h_c
      injection h_c with hp
      injection hp with _ h_idx
      subst h_idx
      exact absurd h1 (by decide)
    · intro h_c
      contradiction

-- ============================================================================
-- Ten Kernel-Verified `-O3` Function Lowerings (`fnT01` .. `fnT10`)
-- ============================================================================

/-- `T01` (`T07_regalloc_with_spills`): Spill-slot round-trips (`v11`, `v12`), call clobbering
`%r11`, and 2-register parallel-move cycle resolved via `%r11`. -/
def certT01 : RegAllocCertBundle :=
  { alloc := stdAlloc
    reservedScratch := scratchR11
    spillSlots := [{ offset := 0, sizeBytes := 8 }, { offset := 8, sizeBytes := 8 }]
    bodyCert :=
      .seq (.copyVReg 11 0)
      (.seq (.constI 12 42)
      (.seq (.callClobber 1 11 10 scratchR11)
      (.seq (.binOp .add 2 1 12)
            (.parSwap2 1 2 (.viaScratch scratchR11))))) }

def fnT01_SSA : SSAFunc := { argVReg := 0, retVReg := 1, body := (inferInstPair stdAlloc certT01.bodyCert).1 }
def fnT01_Mach : MachFunc :=
  { frameSize := 32
    calleeSaved := [(calleeRbx, { offset := 16, sizeBytes := 8 }), (calleeR12, { offset := 24, sizeBytes := 8 })]
    argLoc := stdAlloc 0, retLoc := stdAlloc 1
    body := (inferInstPair stdAlloc certT01.bodyCert).2
    epilogueRestores := [(calleeRbx, { offset := 16, sizeBytes := 8 }), (calleeR12, { offset := 24, sizeBytes := 8 })] }

theorem fnT01_checked : checkRegAllocCert fnT01_SSA fnT01_Mach certT01 = true := rfl
theorem fnT01_refines (st : SSAState) (ms : MachState) (h : stateSim stdAlloc st ms) (x : Int) :
    refines (evalSSAFunc fnT01_SSA st x) (evalMachFunc fnT01_Mach ms x) :=
  checkRegAllocCert_sound fnT01_SSA fnT01_Mach certT01 stdAlloc_valid fnT01_checked st ms h x

/-- `T02`: 3-way register rotation cycle (`v0 := v1; v1 := v2; v2 := v0`) on a split loop
backedge resolved via scratch register `%r11`, plus bounds panic check. -/
def certT02 : RegAllocCertBundle :=
  { alloc := stdAlloc
    reservedScratch := scratchR11
    spillSlots := [{ offset := 0, sizeBytes := 8 }]
    bodyCert :=
      .seq (.constI 1 100)
      (.seq (.constI 2 200)
      (.seq (.parRotate3 0 1 2 scratchR11)
            (.assertBoundsPanic 0 500))) }

def fnT02_SSA : SSAFunc := { argVReg := 0, retVReg := 0, body := (inferInstPair stdAlloc certT02.bodyCert).1 }
def fnT02_Mach : MachFunc :=
  { frameSize := 16, calleeSaved := [(calleeRbx, { offset := 8, sizeBytes := 8 })]
    argLoc := stdAlloc 0, retLoc := stdAlloc 0
    body := (inferInstPair stdAlloc certT02.bodyCert).2
    epilogueRestores := [(calleeRbx, { offset := 8, sizeBytes := 8 })] }

theorem fnT02_checked : checkRegAllocCert fnT02_SSA fnT02_Mach certT02 = true := rfl
theorem fnT02_refines (st : SSAState) (ms : MachState) (h : stateSim stdAlloc st ms) (x : Int) :
    refines (evalSSAFunc fnT02_SSA st x) (evalMachFunc fnT02_Mach ms x) :=
  checkRegAllocCert_sound fnT02_SSA fnT02_Mach certT02 stdAlloc_valid fnT02_checked st ms h x

/-- `T03`: High-pressure 68-VReg kernel (`v64..v67` spilled to frame offsets `424..456`),
combining `viaXchg` 2-cycle swap with spilled reload arithmetic. -/
def certT03 : RegAllocCertBundle :=
  { alloc := stdAlloc
    reservedScratch := scratchR11
    spillSlots := [{ offset := 424, sizeBytes := 8 }, { offset := 432, sizeBytes := 8 },
                   { offset := 440, sizeBytes := 8 }, { offset := 448, sizeBytes := 8 }]
    bodyCert :=
      .seq (.copyVReg 64 0)
      (.seq (.constI 65 17)
      (.seq (.binOp .mul 66 64 65)
      (.seq (.copyVReg 3 66)
      (.seq (.constI 4 99)
            (.parSwap2 3 4 .viaXchg))))) }

def fnT03_SSA : SSAFunc := { argVReg := 0, retVReg := 4, body := (inferInstPair stdAlloc certT03.bodyCert).1 }
def fnT03_Mach : MachFunc :=
  { frameSize := 464, calleeSaved := [(calleeR13, { offset := 456, sizeBytes := 8 })]
    argLoc := stdAlloc 0, retLoc := stdAlloc 4
    body := (inferInstPair stdAlloc certT03.bodyCert).2
    epilogueRestores := [(calleeR13, { offset := 456, sizeBytes := 8 })] }

theorem fnT03_checked : checkRegAllocCert fnT03_SSA fnT03_Mach certT03 = true := rfl
theorem fnT03_refines (st : SSAState) (ms : MachState) (h : stateSim stdAlloc st ms) (x : Int) :
    refines (evalSSAFunc fnT03_SSA st x) (evalMachFunc fnT03_Mach ms x) :=
  checkRegAllocCert_sound fnT03_SSA fnT03_Mach certT03 stdAlloc_valid fnT03_checked st ms h x

/-- `T04`: Back-to-back calls with live-across-call values spilled (`v13`, `v14`) and restored. -/
def certT04 : RegAllocCertBundle :=
  { alloc := stdAlloc
    reservedScratch := scratchR11
    spillSlots := [{ offset := 16, sizeBytes := 8 }, { offset := 24, sizeBytes := 8 }]
    bodyCert :=
      .seq (.copyVReg 13 0)
      (.seq (.callClobber 1 0 5 scratchR11)
      (.seq (.copyVReg 14 1)
      (.seq (.callClobber 2 13 11 scratchR11)
            (.binOp .add 3 14 2)))) }

def fnT04_SSA : SSAFunc := { argVReg := 0, retVReg := 3, body := (inferInstPair stdAlloc certT04.bodyCert).1 }
def fnT04_Mach : MachFunc :=
  { frameSize := 48, calleeSaved := [(calleeRbx, { offset := 32, sizeBytes := 8 })]
    argLoc := stdAlloc 0, retLoc := stdAlloc 3
    body := (inferInstPair stdAlloc certT04.bodyCert).2
    epilogueRestores := [(calleeRbx, { offset := 32, sizeBytes := 8 })] }

theorem fnT04_checked : checkRegAllocCert fnT04_SSA fnT04_Mach certT04 = true := rfl
theorem fnT04_refines (st : SSAState) (ms : MachState) (h : stateSim stdAlloc st ms) (x : Int) :
    refines (evalSSAFunc fnT04_SSA st x) (evalMachFunc fnT04_Mach ms x) :=
  checkRegAllocCert_sound fnT04_SSA fnT04_Mach certT04 stdAlloc_valid fnT04_checked st ms h x

/-- `T05`: Diamond CFG join with simultaneous 2-cycle (`v1 ↔ v2`) and 3-cycle (`v3 → v4 → v5 → v3`). -/
def certT05 : RegAllocCertBundle :=
  { alloc := stdAlloc
    reservedScratch := scratchR11
    spillSlots := []
    bodyCert :=
      .seq (.copyVReg 1 0)
      (.seq (.constI 2 10)
      (.seq (.constI 3 20)
      (.seq (.constI 4 30)
      (.seq (.constI 5 40)
      (.seq (.parSwap2 1 2 .viaXchg)
      (.seq (.parRotate3 3 4 5 scratchR11)
            (.binOp .add 6 1 3))))))) }

def fnT05_SSA : SSAFunc := { argVReg := 0, retVReg := 6, body := (inferInstPair stdAlloc certT05.bodyCert).1 }
def fnT05_Mach : MachFunc :=
  { frameSize := 16, calleeSaved := [], argLoc := stdAlloc 0, retLoc := stdAlloc 6
    body := (inferInstPair stdAlloc certT05.bodyCert).2, epilogueRestores := [] }

theorem fnT05_checked : checkRegAllocCert fnT05_SSA fnT05_Mach certT05 = true := rfl
theorem fnT05_refines (st : SSAState) (ms : MachState) (h : stateSim stdAlloc st ms) (x : Int) :
    refines (evalSSAFunc fnT05_SSA st x) (evalMachFunc fnT05_Mach ms x) :=
  checkRegAllocCert_sound fnT05_SSA fnT05_Mach certT05 stdAlloc_valid fnT05_checked st ms h x

/-- `T06`: Checked UB guard (`assumeNonNegUB`) + bitwise XOR/AND hash mixing with spill slots. -/
def certT06 : RegAllocCertBundle :=
  { alloc := stdAlloc
    reservedScratch := scratchR11
    spillSlots := [{ offset := 0, sizeBytes := 8 }]
    bodyCert :=
      .seq (.assumeNonNegUB 0)
      (.seq (.constI 11 255)
      (.seq (.binOp .bitAnd 1 0 11)
      (.seq (.constI 2 85)
            (.binOp .bitXor 3 1 2)))) }

def fnT06_SSA : SSAFunc := { argVReg := 0, retVReg := 3, body := (inferInstPair stdAlloc certT06.bodyCert).1 }
def fnT06_Mach : MachFunc :=
  { frameSize := 16, calleeSaved := [], argLoc := stdAlloc 0, retLoc := stdAlloc 3
    body := (inferInstPair stdAlloc certT06.bodyCert).2, epilogueRestores := [] }

theorem fnT06_checked : checkRegAllocCert fnT06_SSA fnT06_Mach certT06 = true := rfl
theorem fnT06_refines (st : SSAState) (ms : MachState) (h : stateSim stdAlloc st ms) (x : Int) :
    refines (evalSSAFunc fnT06_SSA st x) (evalMachFunc fnT06_Mach ms x) :=
  checkRegAllocCert_sound fnT06_SSA fnT06_Mach certT06 stdAlloc_valid fnT06_checked st ms h x

/-- `T07`: Spill-to-spill parallel swap (`v15 ↔ v16` in stack frame `[32, 48)`) broken via `%r11`. -/
def certT07 : RegAllocCertBundle :=
  { alloc := stdAlloc
    reservedScratch := scratchR11
    spillSlots := [{ offset := 32, sizeBytes := 8 }, { offset := 40, sizeBytes := 8 }]
    bodyCert :=
      .seq (.copyVReg 15 0)
      (.seq (.constI 16 77)
      (.seq (.parSwap2 15 16 (.viaScratch scratchR11))
            (.binOp .sub 1 15 16))) }

def fnT07_SSA : SSAFunc := { argVReg := 0, retVReg := 1, body := (inferInstPair stdAlloc certT07.bodyCert).1 }
def fnT07_Mach : MachFunc :=
  { frameSize := 64, calleeSaved := [], argLoc := stdAlloc 0, retLoc := stdAlloc 1
    body := (inferInstPair stdAlloc certT07.bodyCert).2, epilogueRestores := [] }

theorem fnT07_checked : checkRegAllocCert fnT07_SSA fnT07_Mach certT07 = true := rfl
theorem fnT07_refines (st : SSAState) (ms : MachState) (h : stateSim stdAlloc st ms) (x : Int) :
    refines (evalSSAFunc fnT07_SSA st x) (evalMachFunc fnT07_Mach ms x) :=
  checkRegAllocCert_sound fnT07_SSA fnT07_Mach certT07 stdAlloc_valid fnT07_checked st ms h x

/-- `T08`: Mixed GPR-to-spill 3-way rotation (`v2 → v17 → v18 → v2`) across split loop header. -/
def certT08 : RegAllocCertBundle :=
  { alloc := stdAlloc
    reservedScratch := scratchR11
    spillSlots := [{ offset := 48, sizeBytes := 8 }, { offset := 56, sizeBytes := 8 }]
    bodyCert :=
      .seq (.copyVReg 2 0)
      (.seq (.constI 17 300)
      (.seq (.constI 18 400)
      (.seq (.parRotate3 2 17 18 scratchR11)
            (.binOp .add 3 2 17)))) }

def fnT08_SSA : SSAFunc := { argVReg := 0, retVReg := 3, body := (inferInstPair stdAlloc certT08.bodyCert).1 }
def fnT08_Mach : MachFunc :=
  { frameSize := 80, calleeSaved := [], argLoc := stdAlloc 0, retLoc := stdAlloc 3
    body := (inferInstPair stdAlloc certT08.bodyCert).2, epilogueRestores := [] }

theorem fnT08_checked : checkRegAllocCert fnT08_SSA fnT08_Mach certT08 = true := rfl
theorem fnT08_refines (st : SSAState) (ms : MachState) (h : stateSim stdAlloc st ms) (x : Int) :
    refines (evalSSAFunc fnT08_SSA st x) (evalMachFunc fnT08_Mach ms x) :=
  checkRegAllocCert_sound fnT08_SSA fnT08_Mach certT08 stdAlloc_valid fnT08_checked st ms h x

/-- `T09`: Chained slice bounds checks (`assertBoundsPanic`) with live-range split reload. -/
def certT09 : RegAllocCertBundle :=
  { alloc := stdAlloc
    reservedScratch := scratchR11
    spillSlots := [{ offset := 64, sizeBytes := 8 }]
    bodyCert :=
      .seq (.assertBoundsPanic 0 1024)
      (.seq (.copyVReg 19 0)
      (.seq (.constI 1 4)
      (.seq (.binOp .mul 2 19 1)
            (.assertBoundsPanic 2 4096)))) }

def fnT09_SSA : SSAFunc := { argVReg := 0, retVReg := 2, body := (inferInstPair stdAlloc certT09.bodyCert).1 }
def fnT09_Mach : MachFunc :=
  { frameSize := 80, calleeSaved := [], argLoc := stdAlloc 0, retLoc := stdAlloc 2
    body := (inferInstPair stdAlloc certT09.bodyCert).2, epilogueRestores := [] }

theorem fnT09_checked : checkRegAllocCert fnT09_SSA fnT09_Mach certT09 = true := rfl
theorem fnT09_refines (st : SSAState) (ms : MachState) (h : stateSim stdAlloc st ms) (x : Int) :
    refines (evalSSAFunc fnT09_SSA st x) (evalMachFunc fnT09_Mach ms x) :=
  checkRegAllocCert_sound fnT09_SSA fnT09_Mach certT09 stdAlloc_valid fnT09_checked st ms h x

/-- `T10`: Full SysV x86-64 callee-save frame (`%rbx, %r12, %r13`), call clobber, and 80-VReg spill. -/
def certT10 : RegAllocCertBundle :=
  { alloc := stdAlloc
    reservedScratch := scratchR11
    spillSlots := [{ offset := 552, sizeBytes := 8 }]
    bodyCert :=
      .seq (.copyVReg 80 0)
      (.seq (.callClobber 4 80 1 scratchR11)
      (.seq (.parSwap2 4 80 (.viaScratch scratchR11))
            (.binOp .add 5 4 80))) }

def fnT10_SSA : SSAFunc := { argVReg := 0, retVReg := 5, body := (inferInstPair stdAlloc certT10.bodyCert).1 }
def fnT10_Mach : MachFunc :=
  { frameSize := 600
    calleeSaved := [(calleeRbx, { offset := 560, sizeBytes := 8 }),
                    (calleeR12, { offset := 568, sizeBytes := 8 }),
                    (calleeR13, { offset := 576, sizeBytes := 8 })]
    argLoc := stdAlloc 0, retLoc := stdAlloc 5
    body := (inferInstPair stdAlloc certT10.bodyCert).2
    epilogueRestores := [(calleeRbx, { offset := 560, sizeBytes := 8 }),
                         (calleeR12, { offset := 568, sizeBytes := 8 }),
                         (calleeR13, { offset := 576, sizeBytes := 8 })] }

theorem fnT10_checked : checkRegAllocCert fnT10_SSA fnT10_Mach certT10 = true := rfl
theorem fnT10_refines (st : SSAState) (ms : MachState) (h : stateSim stdAlloc st ms) (x : Int) :
    refines (evalSSAFunc fnT10_SSA st x) (evalMachFunc fnT10_Mach ms x) :=
  checkRegAllocCert_sound fnT10_SSA fnT10_Mach certT10 stdAlloc_valid fnT10_checked st ms h x

-- ============================================================================
-- Five Negative Bug Injections Rejected by `checkRegAllocCert` (`= false` by `rfl`)
-- ============================================================================

def bug1_ClobberLiveReg : RegAllocCertBundle :=
  { certT01 with
    bodyCert :=
      .seq (.copyVReg 11 0)
      (.seq (.constI 12 42)
      (.seq (.callClobber 1 11 10 { bank := .gpr, idx := 0 })
      (.seq (.binOp .add 2 1 12)
            (.parSwap2 1 2 (.viaScratch scratchR11))))) }

theorem bug1_rejected : checkRegAllocCert fnT01_SSA fnT01_Mach bug1_ClobberLiveReg = false := rfl

def bug2_OverlappingSpills : RegAllocCertBundle :=
  { certT01 with
    spillSlots := [{ offset := 0, sizeBytes := 8 }, { offset := 4, sizeBytes := 4 }] }

theorem bug2_rejected : checkRegAllocCert fnT01_SSA fnT01_Mach bug2_OverlappingSpills = false := rfl

def bug3_BadCycleScratch : RegAllocCertBundle :=
  { certT01 with
    bodyCert :=
      .seq (.copyVReg 11 0)
      (.seq (.constI 12 42)
      (.seq (.callClobber 1 11 10 scratchR11)
      (.seq (.binOp .add 2 1 12)
            (.parSwap2 1 2 (.viaScratch { bank := .gpr, idx := 1 }))))) }

theorem bug3_rejected : checkRegAllocCert fnT01_SSA fnT01_Mach bug3_BadCycleScratch = false := rfl

def bug4_MachFuncMissingCalleeRestore : MachFunc :=
  { fnT01_Mach with
    epilogueRestores := [(calleeRbx, { offset := 16, sizeBytes := 8 })] }

theorem bug4_rejected :
    checkRegAllocCert fnT01_SSA bug4_MachFuncMissingCalleeRestore certT01 = false := rfl

def bug5_MachFuncMissingReload : MachFunc :=
  { fnT01_Mach with
    body :=
      .seq (.moveLoc (stdAlloc 11) (stdAlloc 0))
      (.seq (.constLoc (stdAlloc 12) 42)
      (.seq (.callClobberLoc (stdAlloc 1) (stdAlloc 11) 10 scratchR11)
      (.seq (.binOpLoc .add (stdAlloc 2) (stdAlloc 1) (.preg calleeRbx))
            (.swap2Loc (stdAlloc 1) (stdAlloc 2) (.viaScratch scratchR11))))) }

theorem bug5_rejected :
    checkRegAllocCert fnT01_SSA bug5_MachFuncMissingReload certT01 = false := rfl

#print axioms checkRegAllocCert_sound
#print axioms checkRegAllocCert_complete
#print axioms checkRegAllocCert_iff_valid
#print axioms fnT01_refines
#print axioms fnT10_refines
#print axioms bug1_rejected
#print axioms bug5_rejected

end RegAllocCert
