prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Int.Basic
import Init.Data.List.Basic
import DemonicIsaModel

/-!
# Kernel-Checked Refutations for 12 Synthesized SIMD / `asm!` Counterexamples

Generated from bundled `CaDiCaL 2.1.2` (`exit 10`) + coupled SAT-assumption shrinking
and constructive `F2BasisSimd` unit-basis search. Every refutation theorem states its
claim strictly over `DemonicIsaModel.TotalMirAsmEquiv` or `DemonicIsaModel.CtLeakEquiv`
(`type_hints == 0`), proved by pure kernel reduction (`rfl`) with zero `sorry` and
zero native axioms, plus formal separation of Class I real code bugs from Class II
unreachable loop-invariant counterexamples.
-/

namespace RefuteSimdAsm12

open DemonicIsaModel

theorem refute_total_fault {In Out : Type}
    {pre : In → Bool} {mirSpec : In → Out}
    {asmExec : In → DemonicEnv → IsaOutcome Out}
    (x : In) (d : DemonicEnv) (fk : FaultKind)
    (hpre : pre x = true)
    (hd : ValidDemonic d = true)
    (hfault : asmExec x d = .fault fk) :
    ¬ TotalMirAsmEquiv pre mirSpec asmExec := by
  intro heq
  have h := heq x d hpre hd
  rw [hfault] at h
  nomatch h

theorem refute_total_mismatch {In Out : Type} [DecidableEq Out]
    {pre : In → Bool} {mirSpec : In → Out}
    {asmExec : In → DemonicEnv → IsaOutcome Out}
    (x : In) (d : DemonicEnv)
    (hpre : pre x = true)
    (hd : ValidDemonic d = true)
    (hne : decide (asmExec x d = .ok (mirSpec x)) = false) :
    ¬ TotalMirAsmEquiv pre mirSpec asmExec := by
  intro heq
  have h := heq x d hpre hd
  exact absurd h (of_decide_eq_false hne)

theorem refute_ct_2safety_leak {Pub Sec Out : Type}
    {k : CtKernel Pub Sec Out}
    (p : Pub) (s1 s2 : Sec)
    (hp1 : k.pre p s1 = true)
    (hp2 : k.pre p s2 = true)
    (hleak : decide ((k.exec p s1).2 = (k.exec p s2).2) = false) :
    ¬ CtLeakEquiv k := by
  intro hct
  have hl := hct.2 p s1 s2 hp1 hp2
  exact absurd hl (of_decide_eq_false hleak)

def defaultDemonic : DemonicEnv := ⟨0, [], 0, false⟩

-- Bug 1: `vpmaddubsw` signed `i16` saturation (`u0=255, u1=254, s0=64, s1=65`)
theorem refute_bug01_vpmaddubsw_sat :
    ¬ TotalMirAsmEquiv maddubsPre maddubsMirSpec maddubsAsmBuggy :=
  refute_total_mismatch ⟨255, 254, 64, 65⟩ defaultDemonic rfl rfl rfl

-- Also verify canonical boundary `255 * (64 + 65) = 32,895 > 32,767`:
theorem refute_bug01b_vpmaddubsw_canonical_32895 :
    ¬ TotalMirAsmEquiv maddubsPre maddubsMirSpec maddubsAsmBuggy :=
  refute_total_mismatch ⟨255, 255, 64, 65⟩ defaultDemonic rfl rfl rfl

-- Bug 2: SWAR `count_zero_bytes` Mycroft cross-byte borrow bleed (`x = 0x100`, weight 1!)
theorem refute_bug02_swar_borrow_bleed :
    ¬ TotalMirAsmEquiv swarCountPre swarCountMirSpec swarCountAsmBuggy :=
  refute_total_mismatch 256 defaultDemonic rfl rfl rfl

-- Bug 3: `bsf` vs `tzcnt` undefined destination on zero (`x = 0, bsfUndefDst = 0`)
theorem refute_bug03_bsf_zero_undef_dst :
    ¬ TotalMirAsmEquiv bsfPre bsfMirSpec bsfAsmBuggy :=
  refute_total_mismatch 0 ⟨0, [], 0, false⟩ rfl rfl rfl

-- Bug 4: Branching on `ZF` immediately after `imul` (`a = 0, b = 0, imulUndefZf = false`)
theorem refute_bug04_imul_zf_undef_branch :
    ¬ TotalMirAsmEquiv imulZfPre imulZfMirSpec imulZfAsmBuggy :=
  refute_total_mismatch ⟨0, 0⟩ ⟨0, [], 0, false⟩ rfl rfl rfl

-- Bug 5: Unguarded `vmovdqu` crossing `PROT_NONE` page (`len = 0, pageMisalign = 4065`)
theorem refute_bug05_vmovdqu_cross_page :
    ¬ TotalMirAsmEquiv vmovdquHeadPre vmovdquHeadMirSpec vmovdquHeadAsmBuggy :=
  refute_total_fault [] ⟨4065, [], 0, false⟩
    (.unmappedPageCross 4065 32 0) rfl rfl rfl

-- Bug 6: Off-by-one shift mask reading 1 demonic slack byte (`len = 1, slack0 = 1`)
theorem refute_bug06_off_by_one_tail_mask_slack :
    ¬ TotalMirAsmEquiv tailMaskPre tailMaskMirSpec tailMaskAsmBuggy :=
  refute_total_mismatch [0] ⟨0, [1], 0, false⟩ rfl rfl rfl

-- Bug 7: Optimistic `vpmovmskb` fast-path is functionally exact on both witnesses yet fails 2-safety!
theorem bug07_functional_on_witness_pair :
    (ctVpmovmskbKernel.exec [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]).1 = ctVpmovmskbKernel.spec [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ∧
    (ctVpmovmskbKernel.exec [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]).1 = ctVpmovmskbKernel.spec [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] :=
  ⟨rfl, rfl⟩

theorem refute_bug07_ct_vpmovmskb_leak :
    ¬ CtLeakEquiv ctVpmovmskbKernel :=
  refute_ct_2safety_leak [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] rfl rfl rfl

-- Bug 8: 64-bit `pclmulqdq` CRC-64 fold polynomial bit-flip via F2 unit-basis (`h = 0, l = 1`)
theorem refute_bug08_pclmulqdq_crc64_bitflip :
    ¬ TotalMirAsmEquiv clmulFoldPre clmulFoldMirSpec clmulFoldAsmBuggy :=
  refute_total_mismatch ⟨0, 1⟩ defaultDemonic rfl rfl rfl

-- Bug 9: `mulx` + `adcx`/`adox` carry-flag swap (`t0=0, t1=0, a0=1229782938247303442, a1=1229782938247303441, b=15`)
theorem refute_bug09_adcx_adox_carry_swap :
    ¬ TotalMirAsmEquiv adxMac2Pre adxMac2MirSpec adxMac2AsmBuggy :=
  refute_total_mismatch ⟨0, 0, 1229782938247303442, 1229782938247303441, 15⟩ defaultDemonic rfl rfl rfl

-- Bug 10: `vpshufb` control-byte bit-7 zeroing (`lut0 = 1, idx0 = 128`)
theorem refute_bug10_vpshufb_bit7_zeroing :
    ¬ TotalMirAsmEquiv pshufbPre pshufbMirSpec pshufbAsmBuggy :=
  refute_total_mismatch ⟨1, 128⟩ defaultDemonic rfl rfl rfl

-- Bug 11a: `vminss` signed-zero operand swap (`a = 0x80000000, b = 0x0`)
theorem refute_bug11_vminss_signed_zero_swap :
    ¬ TotalMirAsmEquiv f32Pre vminssMirSpec vminssAsmBuggy :=
  refute_total_mismatch ⟨2147483648, 0⟩ defaultDemonic rfl rfl rfl

-- Bug 11b: `vminss` quiet/signaling NaN operand swap (`a = 0x7f800001, b = 0x0`)
theorem refute_bug11b_vminss_nan_swap :
    ¬ TotalMirAsmEquiv f32Pre vminssMirSpec vminssAsmBuggy :=
  refute_total_mismatch ⟨2139095041, 0⟩ defaultDemonic rfl rfl rfl

-- Bug 12: BMI2 `bzhi` count `>= 64` saturation vs modular shift (`x = 1, n = 64`)
theorem refute_bug12_bzhi_ge64_vs_shift :
    ¬ TotalMirAsmEquiv bzhiPre bzhiMirSpec bzhiAsmBuggy :=
  refute_total_mismatch ⟨1, 64⟩ defaultDemonic rfl rfl rfl

-- ============================================================================
-- Formal Class II vs Class I Separation:
-- `candidateInvCoincidental` fails `StepInductive` at CaDiCaL witness `⟨64, 96, 2⟩`,
-- yet `triageHealthyExec` satisfies `TotalMirAsmEquiv` across its entire bounded domain!
-- ============================================================================

theorem triage_classII_noninductive_yet_program_correct :
    (¬ StepInductive candidateInvCoincidental triageLoopGuard triageLoopStep) ∧
    TotalMirAsmEquiv triageHealthyPre triageHealthySpec triageHealthyExec :=
  And.intro
    (fun hind => Bool.noConfusion (hind ⟨64, 96, 2⟩ rfl rfl))
    (fun blocks _d hpre _hd => by
      cases blocks with
      | zero => rfl
      | succ b1 =>
        cases b1 with
        | zero => rfl
        | succ b2 =>
          cases b2 with
          | zero => rfl
          | succ b3 =>
            cases b3 with
            | zero => rfl
            | succ b4 =>
              cases b4 with
              | zero => rfl
              | succ b5 =>
                cases b5 with
                | zero => rfl
                | succ b6 =>
                  cases b6 with
                  | zero => rfl
                  | succ b7 =>
                    cases b7 with
                    | zero => rfl
                    | succ b8 =>
                      cases b8 with
                      | zero => rfl
                      | succ _ => exact Bool.noConfusion hpre)

end RefuteSimdAsm12
