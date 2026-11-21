/-!
# Kernel-checked restatement of Wheeler's DDC Proof #1 and Proof #2

Abstract first-order model following chapter 5 (sections 5.6 and 5.7) of
D. A. Wheeler, "Fully Countering Trusting Trust through Diverse
Double-Compiling" (PhD dissertation, George Mason University, 2009;
arXiv:1004.5534). The original proofs were found by prover9; this file restates
the same assumptions and goals and has them checked by the Lean 4 kernel.

Scope: executables, sources, languages, environments and environment effects
are opaque types, and `compile`, `exactlyCorrespond`, `accuratelyTranslates`
are uninterpreted. This is a model of the DDC *argument*. It is not a model of
`rustc`, `mrustc`, TinyCC, or any other real compiler, and it proves nothing
about whether the assumptions hold for a real toolchain.

Names follow the dissertation: `cT` trusted compiler executable, `sP` parent
compiler source, `sA` source of the compiler under test, `cA` executable of the
compiler under test, `cP` putative parent executable, `e1`/`e2`/`eA`/`eArun`
environments.

Checked with: Lean (version 4.34.1), no `sorry`, no `axiom`, no `partial`,
no `native_decide`.
-/

namespace DdcModel

/-- Vocabulary of Proof #1 (dissertation section 5.6). `Data` is the sort of
executables; the first-order original is unsorted. -/
structure Sig where
  Data : Type
  Src : Type
  Lang : Type
  Env : Type
  Eff : Type
  /-- `compile Source Compiler EnvEffects RunOn Target` -/
  compile : Src → Data → Eff → Env → Env → Data
  /-- `exactlyCorrespond Executable Source Lang RunOn` -/
  exactlyCorrespond : Data → Src → Lang → Env → Prop
  /-- `accuratelyTranslates Compiler Lang Source EnvEffects RunOn Target` -/
  accuratelyTranslates : Data → Lang → Src → Eff → Env → Env → Prop

/-- The three assumptions of Proof #1 that are not definitions of `stage1` and
`stage2`: `cT_compiles_sP`, `sP_compiles_sA`, `define_exactly_correspond`. -/
structure Proof1Assumptions (S : Sig) (cT : S.Data) (sP sA : S.Src)
    (lsP lsA : S.Lang) (e1 e2 eArun : S.Env) : Prop where
  /-- 5.6.4: the trusted compiler accurately translates the parent source. -/
  cT_compiles_sP : ∀ eff : S.Eff, S.accuratelyTranslates cT lsP sP eff e1 e2
  /-- 5.6.6: the parent source, once accurately compiled, accurately
  translates the source of the compiler under test. -/
  sP_compiles_sA :
    ∀ (g : S.Data) (effMakeP effP : S.Eff) (execEnv targetEnv : S.Env),
      S.accuratelyTranslates g lsP sP effMakeP execEnv targetEnv →
      S.accuratelyTranslates (S.compile sP g effMakeP execEnv targetEnv)
        lsA sA effP targetEnv eArun
  /-- 5.6.8: output of an accurate translation exactly corresponds to its
  source. -/
  define_exactly_correspond :
    ∀ (c : S.Data) (l : S.Lang) (s : S.Src) (eff : S.Eff)
      (execEnv targetEnv : S.Env),
      S.accuratelyTranslates c l s eff execEnv targetEnv →
      S.exactlyCorrespond (S.compile s c eff execEnv targetEnv) s l targetEnv

/-- Proof #1, goal `source_corresponds_to_executable` (5.6.10):
`(stage2 = cA) -> exactly_correspond(cA, sA, lsA, eArun)`. -/
theorem source_corresponds_to_executable (S : Sig)
    (cT cA stage1 stage2 : S.Data) (sP sA : S.Src) (lsP lsA : S.Lang)
    (e1 e2 eArun : S.Env) (e1effects e2effects : S.Eff)
    (definition_stage1 : stage1 = S.compile sP cT e1effects e1 e2)
    (definition_stage2 : stage2 = S.compile sA stage1 e2effects e2 eArun)
    (A : Proof1Assumptions S cT sP sA lsP lsA e1 e2 eArun) :
    stage2 = cA → S.exactlyCorrespond cA sA lsA eArun := by
  intro h
  rw [← h, definition_stage2, definition_stage1]
  exact A.define_exactly_correspond _ _ _ _ _ _
    (A.sP_compiles_sA cT e1effects e2effects e1 e2 (A.cT_compiles_sP e1effects))

/-- Vocabulary added by Proof #2 (dissertation section 5.7): `run`,
`converttext`, `extract`, `retarget`, `portable_and_deterministic`. -/
structure Sig2 extends Sig where
  /-- `run Executable Input EnvEffects Environment` -/
  run : Data → Src → Eff → Env → Data
  /-- `converttext Data Environment1 Environment2` -/
  converttext : Data → Env → Env → Data
  /-- `extract Data` -/
  extract : Data → Data
  /-- `retarget Source Target` -/
  retarget : Src → Env → Src
  /-- `portable_and_deterministic Source Language Input` -/
  portableAndDeterministic : Src → Lang → Src → Prop

/-- Proof #2, goal `always_equal` (5.7.13): `cA = stage2`. The nine
hypotheses are the nine assumptions listed in 5.7. -/
theorem always_equal (S : Sig2)
    (cT cP cA stage1 stage2 : S.Data) (sP sA : S.Src) (lsP : S.Lang)
    (e1 e2 eA eArun : S.Env) (e1effects e2effects eAeffects : S.Eff)
    (definition_stage1 : stage1 = S.compile sP cT e1effects e1 e2)
    (definition_stage2 : stage2 = S.compile sA stage1 e2effects e2 eArun)
    (define_exactly_correspond :
      ∀ (c : S.Data) (l : S.Lang) (s : S.Src) (eff : S.Eff)
        (execEnv targetEnv : S.Env),
        S.accuratelyTranslates c l s eff execEnv targetEnv →
        S.exactlyCorrespond (S.compile s c eff execEnv targetEnv) s l targetEnv)
    (cT_compiles_sP : ∀ eff : S.Eff, S.accuratelyTranslates cT lsP sP eff e1 e2)
    (definition_cA : cA = S.compile sA cP eAeffects eA eArun)
    (cP_corresponds_to_sP : S.exactlyCorrespond cP sP lsP eA)
    (define_compile :
      ∀ (s : S.Src) (c : S.Data) (eff : S.Eff) (runOn target : S.Env),
        S.compile s c eff runOn target =
          S.extract (S.converttext (S.run c (S.retarget s target) eff runOn)
            runOn target))
    (sP_portable_and_deterministic :
      S.portableAndDeterministic sP lsP (S.retarget sA eArun))
    (define_determinism :
      ∀ (s : S.Src) (l : S.Lang) (input : S.Src) (x1 x2 : S.Data)
        (env1 env2 target : S.Env) (eff1 eff2 : S.Eff),
        S.portableAndDeterministic s l input →
        S.exactlyCorrespond x1 s l env1 →
        S.exactlyCorrespond x2 s l env2 →
        S.converttext (S.run x1 input eff1 env1) env1 target =
          S.converttext (S.run x2 input eff2 env2) env2 target) :
    cA = stage2 := by
  have hstage1 : S.exactlyCorrespond stage1 sP lsP e2 := by
    rw [definition_stage1]
    exact define_exactly_correspond _ _ _ _ _ _ (cT_compiles_sP e1effects)
  have hrun :=
    define_determinism sP lsP (S.retarget sA eArun) cP stage1 eA e2 eArun
      eAeffects e2effects sP_portable_and_deterministic cP_corresponds_to_sP
      hstage1
  rw [definition_cA, definition_stage2, define_compile, define_compile, hrun]

/-! ## Non-vacuity: the Proof #1 assumptions are jointly satisfiable -/

/-- Degenerate one-point model in which every assumption holds. -/
def trivialSig : Sig where
  Data := Unit
  Src := Unit
  Lang := Unit
  Env := Unit
  Eff := Unit
  compile := fun _ _ _ _ _ => ()
  exactlyCorrespond := fun _ _ _ _ => True
  accuratelyTranslates := fun _ _ _ _ _ _ => True

theorem proof1_assumptions_satisfiable :
    Proof1Assumptions trivialSig () () () () () () () () :=
  { cT_compiles_sP := fun _ => True.intro
    sP_compiles_sA := fun _ _ _ _ _ _ => True.intro
    define_exactly_correspond := fun _ _ _ _ _ _ _ => True.intro }

/-! ## Necessity of the trusted-compiler assumption

A two-point "taint" model. `true` is an executable that corresponds to its
source; `false` is one carrying a self-propagating payload. `compile` returns
the taint of the compiler that ran, which is Thompson's attack in its simplest
form: a subverted compiler emits a subverted compiler regardless of the source
it is given. -/

/-- Taint model: output of a compilation inherits the taint of the compiler. -/
def taintSig : Sig where
  Data := Bool
  Src := Unit
  Lang := Unit
  Env := Unit
  Eff := Unit
  compile := fun _ c _ _ _ => c
  exactlyCorrespond := fun d _ _ _ => d = true
  accuratelyTranslates := fun c _ _ _ _ _ => c = true

/-- In the taint model `sP_compiles_sA` and `define_exactly_correspond` hold
for every choice of constants. -/
theorem taint_sP_compiles_sA :
    ∀ (g : taintSig.Data) (effMakeP effP : taintSig.Eff)
      (execEnv targetEnv : taintSig.Env),
      taintSig.accuratelyTranslates g () () effMakeP execEnv targetEnv →
      taintSig.accuratelyTranslates
        (taintSig.compile () g effMakeP execEnv targetEnv) () () effP targetEnv () :=
  fun _ _ _ _ _ h => h

theorem taint_define_exactly_correspond :
    ∀ (c : taintSig.Data) (l : taintSig.Lang) (s : taintSig.Src)
      (eff : taintSig.Eff) (execEnv targetEnv : taintSig.Env),
      taintSig.accuratelyTranslates c l s eff execEnv targetEnv →
      taintSig.exactlyCorrespond
        (taintSig.compile s c eff execEnv targetEnv) s l targetEnv :=
  fun _ _ _ _ _ _ h => h

/-- If the "trusted" compiler `cT` carries the same payload as the compiler
under test, the DDC comparison succeeds (`stage2 = cA`) while `cA` does not
correspond to its source. Every Proof #1 hypothesis except `cT_compiles_sP`
holds in this model, so that assumption cannot be dropped. -/
theorem ddc_passes_but_unsound_when_cT_shares_payload :
    ∃ (cT cA stage1 stage2 : taintSig.Data),
      stage1 = taintSig.compile () cT () () () ∧
      stage2 = taintSig.compile () stage1 () () () ∧
      stage2 = cA ∧
      ¬ taintSig.exactlyCorrespond cA () () () :=
  ⟨false, false, false, false, rfl, rfl, rfl, Bool.false_ne_true⟩

/-- With an untainted `cT`, the same model detects a tainted `cA`: the DDC
result differs from `cA`. -/
theorem ddc_detects_tainted_cA_with_clean_cT :
    ∀ (stage1 stage2 : taintSig.Data),
      stage1 = taintSig.compile () true () () () →
      stage2 = taintSig.compile () stage1 () () () →
      stage2 ≠ false := by
  intro stage1 stage2 h1 h2
  rw [h2, h1]
  exact fun h => Bool.false_ne_true h.symm

end DdcModel

#print axioms DdcModel.source_corresponds_to_executable
#print axioms DdcModel.always_equal
#print axioms DdcModel.proof1_assumptions_satisfiable
#print axioms DdcModel.taint_sP_compiles_sA
#print axioms DdcModel.taint_define_exactly_correspond
#print axioms DdcModel.ddc_passes_but_unsound_when_cT_shares_payload
#print axioms DdcModel.ddc_detects_tainted_cA_with_clean_cT
