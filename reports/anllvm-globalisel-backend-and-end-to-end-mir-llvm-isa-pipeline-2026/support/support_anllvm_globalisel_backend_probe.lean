/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

/-!
# Probe: Adapting LLVM's `GlobalISel` Backend Pipeline (`AnLLVM -> AnMachineIR -> PostRA -> ISA`)

This standalone Lean 4.34.1 mechanization models the five-stage backend lowering
pipeline for Anneal's verified port of LLVM (`llc` 21.1.8):

1. **Unified `AnMachineIR` Representation (`MachineFunction`)**:
   Models `llvm/CodeGen/MachineFunction.h`, `llvm/CodeGenTypes/LowLevelType.h`,
   and `llvm/CodeGen/GlobalISel/GenericMachineInstrs.h`. Both `GenericOpcode`
   (`G_ADD`, `G_SUB`, `G_MUL`, `G_SHL_IMM`, `G_ZEXT`, `G_TRUNC`, `G_LOAD`,
   `G_STORE`, `G_PTR_ADD`, `G_ICMP`, `G_UADDO`, `G_UADDE`, `G_MERGE_VALUES`,
   `G_UNMERGE_VALUES`, `G_SELECT`) and `TargetOpcode` (`ADD64_FLAGS`,
   `ADDC64_FLAGS`, `CMP64_FLAGS`, `CSET64`, `CSEL64`, `ADD_SHIFTED`, `LDR64`,
   `STR64`) inhabit the same `MachineFunction` type so that `IRTranslator`,
   `Legalizer`, `RegBankSelect`, and `InstructionSelect` are homogeneous
   `AnMachineLang -> AnMachineLang` refinements.
2. **Stage 1 (`IRTranslator`)**:
   Lowers `AnLLVM` instructions and ABI argument/return marshaling directly into
   `GenericOpcode` `AnMachineIR` without constructing an intermediate
   `SelectionDAG` (`irTranslator_compiles`).
3. **Stage 2 (`Legalizer` + `RegBankSelect`)**:
   Legalizes 128-bit `s128` addition into 64-bit `G_UNMERGE_VALUES`, `G_UADDO`
   (producing an explicit SSA carry virtual register `vflag : VReg`),
   `G_UADDE` (consuming `vflag`), and `G_MERGE_VALUES`, and legalizes narrow
   `s8` addition via 32-bit promotion and masking
   (`legalizer_s128_and_s8_compiles`).
4. **Stage 3 (`InstructionSelect`)**:
   Models TableGen `GlobalISelEmitter` pattern selection lowering `GenericOpcode`
   into `TargetOpcode` (`G_PTR_ADD(base, G_SHL_IMM(idx, 3)) -> ADD_SHIFTED`,
   `G_UADDO / G_UADDE -> ADD64_FLAGS / ADDC64_FLAGS`) while preserving explicit
   SSA flag virtual registers (`instructionSelect_compiles`).
5. **Stage 4 (`UnifiedRegAllocAndFlagChecker`)**:
   Validates the combined transition from `MachineSSA` to `PostRA MachineIR`
   (`PHIElimination + TwoAddressInstructionPass + RegisterCoalescer +
   RegAllocGreedy + VirtRegRewriter`) in one hop via a forward symbolic
   certificate checker (`checkPostRaMachine_sound`), and proves a negative
   canary (`canary_intervening_flag_clobber_between_uaddo_and_uadde_rejected`)
   showing that any flag-clobbering instruction inserted between `ADD64_FLAGS`
   and `ADDC64_FLAGS` is rejected.
6. **Stage 5 (`PrologEpilogAndMcEncode`)**:
   Lowers `PostRA MachineIR` stack spill slots and callee-saved register saves
   into explicit `[SP + offset]` frame addressing and `MCInst` encodings, and
   composes all five stages via `PassCompiler.comp`
   (`anllvmBackendPipeline_verified`).
-/

namespace Anneal.BackendProbe

/-!
## Section 1: Anneal `Trusted.Refinement` and `BB-8` (`PassCompiler`, `CertChecker`) Foundation

We begin with the core behavioral refinement definitions from
`Trusted/Refinement.lean` and the proof-gated compiler / certificate-checker
combinators from `Theory/BuildingBlocks.lean` (`BB-8`).
-/

/-- Reflexive, transitive refinement preorder `b₁ ≤ b₂`. -/
class Preorder (B : Type u) extends LE B where
  le_refl  : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

/-- Partial behavior gated by a safety proposition `defined : Prop`. -/
structure Partial (B : Type u) where
  defined : Prop
  val     : defined → B

instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ :=
    ∃ (f : p₂.defined → p₁.defined),
      ∀ (h₂ : p₂.defined), p₁.val (f h₂) ≤ p₂.val h₂
  le_refl p := ⟨id, fun h => Preorder.le_refl (p.val h)⟩
  le_trans := by
    intro a b c ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩
    exact ⟨fun hc => f₁ (f₂ hc),
      fun hc => Preorder.le_trans (hf₁ (f₂ hc)) (hf₂ hc)⟩

/-- Query-indexed nondeterministic partial behavior. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- Deterministic total evaluator lifted into `Behavior Query Out`. -/
def Behavior.ofTotal {Query Out : Type} (eval : Query → Out) :
    Behavior Query Out :=
  fun q => {
    defined := True
    val     := fun _ o => o = eval q
  }

/-- Partial deterministic evaluator (`Option Out`, where `none` denotes UB)
lifted into `Behavior Query Out`. -/
def Behavior.ofOption {Query Out : Type} (eval : Query → Option Out) :
    Behavior Query Out :=
  fun q => {
    defined := ∃ res, eval q = some res
    val     := fun _ o => eval q = some o
  }

/-- Language parameterized by a shared semantic observation type `SemObs`. -/
structure Language (SemObs : Type) where
  Prog  : Type
  Query : Type
  Out   : Type
  obs   : Out → SemObs
  sem   : Prog → Behavior Query Out

/-- Identity-observation language constructor. -/
abbrev Language.mkSimple (Prog Query Out : Type)
    (sem : Prog → Behavior Query Out) : Language Out where
  Prog  := Prog
  Query := Query
  Out   := Out
  obs   := id
  sem   := sem

/-- Cross-language behavior codec preserving `SemObs` across `decodeOut`. -/
structure BehaviorCodec {SemObs : Type} (L₁ L₂ : Language SemObs) where
  encodeQuery : L₁.Query → L₂.Query
  decodeQuery : L₂.Query → L₁.Query
  encodeOut   : L₁.Out → L₂.Out
  decodeOut   : L₂.Out → Option L₁.Out
  decodeQuery_encodeQuery : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁
  decodeOut_encodeOut     : ∀ o₁, decodeOut (encodeOut o₁) = some o₁
  obs_decodeOut           : ∀ o₂ o₁, decodeOut o₂ = some o₁ → L₂.obs o₂ = L₁.obs o₁

/-- Canonical identity codec between two `Language.mkSimple` languages sharing
the same `Query` and `Out` types. -/
def mkSimpleCodec {Q O : Type} {P₁ P₂ : Type}
    (sem₁ : P₁ → Behavior Q O) (sem₂ : P₂ → Behavior Q O) :
    BehaviorCodec (Language.mkSimple P₁ Q O sem₁)
                  (Language.mkSimple P₂ Q O sem₂) where
  encodeQuery q := q
  decodeQuery q := q
  encodeOut o   := o
  decodeOut o   := some o
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl
  obs_decodeOut _ _ h       := Option.some.inj h

/-- Lifts a source behavior `b : Behavior L₁.Query L₁.Out` across `c`. -/
def BehaviorCodec.toMorphism {SemObs : Type} {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂) (b : Behavior L₁.Query L₁.Out) :
    Behavior L₂.Query L₂.Out :=
  fun q₂ => {
    defined := (b (c.decodeQuery q₂)).defined
    val     := fun h o₂ =>
      ∃ o₁, c.decodeOut o₂ = some o₁ ∧ (b (c.decodeQuery q₂)).val h o₁
  }

/-- Sequential composition of behavior codecs. -/
def BehaviorCodec.comp {SemObs : Type} {L₁ L₂ L₃ : Language SemObs}
    (c₁₂ : BehaviorCodec L₁ L₂) (c₂₃ : BehaviorCodec L₂ L₃) :
    BehaviorCodec L₁ L₃ where
  encodeQuery q₁ := c₂₃.encodeQuery (c₁₂.encodeQuery q₁)
  decodeQuery q₃ := c₁₂.decodeQuery (c₂₃.decodeQuery q₃)
  encodeOut o₁   := c₂₃.encodeOut (c₁₂.encodeOut o₁)
  decodeOut o₃   := (c₂₃.decodeOut o₃).bind c₁₂.decodeOut
  decodeQuery_encodeQuery q₁ := by
    rw [c₂₃.decodeQuery_encodeQuery, c₁₂.decodeQuery_encodeQuery]
  decodeOut_encodeOut o₁ := by
    simp [c₂₃.decodeOut_encodeOut, c₁₂.decodeOut_encodeOut]
  obs_decodeOut o₃ o₁ h := by
    cases h₂ : c₂₃.decodeOut o₃ with
    | none =>
      rw [h₂] at h
      contradiction
    | some o₂ =>
      rw [h₂] at h
      simp only [Option.bind] at h
      have hObs₂₃ := c₂₃.obs_decodeOut o₃ o₂ h₂
      have hObs₁₂ := c₁₂.obs_decodeOut o₂ o₁ h
      exact Eq.trans hObs₂₃ hObs₁₂

/-- Downward compilation relation `L_tgt.sem t ≤ c.toMorphism (L_src.sem s)`. -/
abbrev Compiles {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ c.toMorphism (L_src.sem s)

/-- Sufficient condition for `Compiles` between `Behavior.ofOption` languages
sharing the same `Query` and `Out` types via `mkSimpleCodec`. -/
theorem compiles_of_eval_eq {Q O : Type}
    {P₁ P₂ : Type} {eval₁ : P₁ → Q → Option O} {eval₂ : P₂ → Q → Option O}
    (s : P₁) (t : P₂)
    (hEq : ∀ q res, eval₁ s q = some res → eval₂ t q = some res) :
    Compiles (Language.mkSimple P₁ Q O (fun p => Behavior.ofOption (eval₁ p)))
             (Language.mkSimple P₂ Q O (fun p => Behavior.ofOption (eval₂ p)))
             (mkSimpleCodec (fun p => Behavior.ofOption (eval₁ p))
                            (fun p => Behavior.ofOption (eval₂ p)))
             s t := by
  intro q
  refine ⟨fun ⟨res, h₁⟩ => ⟨res, hEq q res h₁⟩, ?_⟩
  intro ⟨res, h₁⟩ o h₂
  refine ⟨o, rfl, ?_⟩
  change eval₁ s q = some res at h₁
  change eval₂ t q = some o at h₂
  change eval₁ s q = some o
  have h₂' := hEq q res h₁
  have hEqO : res = o := Option.some.inj (h₂'.symm.trans h₂)
  exact hEqO ▸ h₁

/-- Transitivity of `Compiles` across sequential `BehaviorCodec.comp`. -/
theorem Compiles.trans {SemObs : Type} {L₁ L₂ L₃ : Language SemObs}
    {c₁₂ : BehaviorCodec L₁ L₂} {c₂₃ : BehaviorCodec L₂ L₃}
    {p₁ : L₁.Prog} {p₂ : L₂.Prog} {p₃ : L₃.Prog}
    (h₁₂ : Compiles L₁ L₂ c₁₂ p₁ p₂)
    (h₂₃ : Compiles L₂ L₃ c₂₃ p₂ p₃) :
    Compiles L₁ L₃ (BehaviorCodec.comp c₁₂ c₂₃) p₁ p₃ := by
  intro q₃
  rcases h₁₂ (c₂₃.decodeQuery q₃) with ⟨f₁₂, hf₁₂⟩
  rcases h₂₃ q₃ with ⟨f₂₃, hf₂₃⟩
  refine ⟨fun h₁ => f₂₃ (f₁₂ h₁), ?_⟩
  intro h₁ o₃ ho₃
  rcases hf₂₃ (f₁₂ h₁) o₃ ho₃ with ⟨o₂, hDec₂₃, ho₂⟩
  rcases hf₁₂ h₁ o₂ ho₂ with ⟨o₁, hDec₁₂, ho₁⟩
  refine ⟨o₁, ?_, ho₁⟩
  simp [BehaviorCodec.comp, hDec₂₃, hDec₁₂]

/-- `BB-8` proof-gated compiler pass (`PassCompiler`). -/
structure PassCompiler {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) where
  compile : L_src.Prog → Option L_tgt.Prog
  sound   : ∀ s t, compile s = some t → Compiles L_src L_tgt c s t

/-- Sequential composition of `PassCompiler` stages (`BB-8`). -/
def PassCompiler.comp {SemObs : Type} {L₁ L₂ L₃ : Language SemObs}
    {c₁₂ : BehaviorCodec L₁ L₂} {c₂₃ : BehaviorCodec L₂ L₃}
    (P₁₂ : PassCompiler L₁ L₂ c₁₂) (P₂₃ : PassCompiler L₂ L₃ c₂₃) :
    PassCompiler L₁ L₃ (BehaviorCodec.comp c₁₂ c₂₃) where
  compile s := (P₁₂.compile s).bind P₂₃.compile
  sound s t h := by
    cases h₁ : P₁₂.compile s with
    | none =>
      rw [h₁] at h
      contradiction
    | some m =>
      rw [h₁] at h
      simp only [Option.bind] at h
      exact Compiles.trans (P₁₂.sound s m h₁) (P₂₃.sound m t h)

/-- `BB-8` translation-validation certificate checker (`CertChecker`).
Validates an untrusted target program produced by an external pass pipeline
(such as `PHIElimination + TwoAddress + Coalescer + RegAllocGreedy`). -/
structure CertChecker {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) where
  check : L_src.Prog → L_tgt.Prog → Bool
  sound : ∀ s t, check s t = true → Compiles L_src L_tgt c s t

/-- Combines an untrusted oracle `oracle : L_src.Prog → Option L_tgt.Prog`
with a verified `CertChecker` to produce a sound `PassCompiler` with zero trust
in `oracle`. -/
def CertChecker.toPassCompiler {SemObs : Type} {L_src L_tgt : Language SemObs}
    {c : BehaviorCodec L_src L_tgt}
    (checker : CertChecker L_src L_tgt c)
    (oracle : L_src.Prog → Option L_tgt.Prog) :
    PassCompiler L_src L_tgt c where
  compile s :=
    match oracle s with
    | none => none
    | some t => if checker.check s t then some t else none
  sound s t h := by
    cases hOr : oracle s with
    | none =>
      rw [hOr] at h
      contradiction
    | some t' =>
      rw [hOr] at h
      simp only at h
      split at h
      · rename_i hChk
        injection h with hEq
        subst hEq
        exact checker.sound s t' hChk
      · contradiction

/-!
## Section 2: Shared Semantic Domain (`AbiQuery`, `AbiOut`, `LowLevelType`, `MVal`)

To compare `AnLLVM`, `AnMachineIR` (`GlobalISel`), `PostRA MachineIR`, and
`FramedISA` along a single compositional chain, all four languages share a
common ABI query (`AbiQuery`) and ABI observation (`AbiOut`):
- Six 64-bit ABI argument registers (`arg0`..`arg5`, modeling `$x0`..`$x5` on
  AArch64, `$a0`..`$a5` on RISC-V, or `$rdi, $rsi, $rdx, $rcx, $r8, $r9` on
  x86-64), plus an initial 64-bit word-addressed heap memory `heap : List Nat`
  and initial callee-saved register state `calleeSaved : Nat`.
- Two 64-bit ABI return registers (`retLo`, `retHi`), final `heap : List Nat`,
  and preserved `calleeSaved : Nat`.
-/

/-- 64-bit word modulus $2^{64}$ used to model modular 64-bit arithmetic and
carry generation (`G_UADDO` / `G_UADDE`) constructively over `Nat`. -/
def word64Mod : Nat := 18446744073709551616

/-- 32-bit word modulus $2^{32}$. -/
def word32Mod : Nat := 4294967296

/-- 8-bit byte modulus $2^8$. -/
def word8Mod : Nat := 256

/-- ABI entry state shared across `AnLLVM`, `AnMachineIR`, `PostRA`, and `ISA`. -/
structure AbiQuery where
  arg0        : Nat
  arg1        : Nat
  arg2        : Nat
  arg3        : Nat
  arg4        : Nat
  arg5        : Nat
  heap        : List Nat
  calleeSaved : Nat
  deriving DecidableEq, Repr

/-- ABI exit observation: return pair `(retLo, retHi)`, final `heap`, and
callee-saved register value `calleeSaved`. -/
structure AbiOut where
  retLo       : Nat
  retHi       : Nat
  heap        : List Nat
  calleeSaved : Nat
  deriving DecidableEq, Repr

/-- `LLT` (`LowLevelType`) from `llvm/CodeGenTypes/LowLevelType.h:40-100`.
In GlobalISel, virtual registers are typed by `LLT` rather than `SelectionDAG`'s
`MVT`/`EVT` + `MVT::Other` (`Chain`) + `MVT::Glue`. -/
inductive LowLevelType where
  | s1   -- 1-bit scalar or explicit carry/condition flag (`LLT::scalar(1)`)
  | s8   -- 8-bit scalar (`LLT::scalar(8)`)
  | s32  -- 32-bit scalar (`LLT::scalar(32)`)
  | s64  -- 64-bit scalar (`LLT::scalar(64)`)
  | s128 -- 128-bit wide scalar (`LLT::scalar(128)`)
  | p0   -- 64-bit pointer in address space 0 (`LLT::pointer(0, 64)`)
  deriving DecidableEq, Repr

/-- Machine values inhabiting `AnLLVM` and `AnMachineIR` virtual registers. -/
inductive MVal where
  | v1   (b : Bool)
  | v8   (n : Nat)
  | v32  (n : Nat)
  | v64  (n : Nat)
  | v128 (lo hi : Nat)
  | ptr  (wordIdx : Nat)
  deriving DecidableEq, Repr

/-- Extracts the `LowLevelType` of an `MVal`. -/
def MVal.llt : MVal → LowLevelType
  | .v1 _     => .s1
  | .v8 _     => .s8
  | .v32 _    => .s32
  | .v64 _    => .s64
  | .v128 _ _ => .s128
  | .ptr _    => .p0

/-- Integer comparison predicates matching `CmpInst::Predicate` in `G_ICMP`. -/
inductive IntPred where
  | eq
  | ult
  | ugt
  deriving DecidableEq, Repr

/-- Evaluates an `IntPred` on two natural numbers. -/
def IntPred.eval : IntPred → Nat → Nat → Bool
  | .eq,  a, b => decide (a = b)
  | .ult, a, b => decide (a < b)
  | .ugt, a, b => decide (a > b)

/-- Safe list lookup for word-addressed heap memory. -/
def heapLoad (heap : List Nat) (idx : Nat) : Option Nat :=
  heap[idx]?

/-- Safe list update for word-addressed heap memory (returns `none` if out of
bounds). -/
def heapStore (heap : List Nat) (idx : Nat) (val : Nat) : Option (List Nat) :=
  if idx < heap.length then
    some (heap.set idx (val % word64Mod))
  else
    none

/-!
## Section 3: Source Language `AnLlvmLang` (`AnLLVM` SSA Subset)

We model an `AnLLVM` function body operating over typed SSA variables (`VReg :=
Nat`) with 128-bit integer addition (`add128`), 8-bit addition (`add8`),
zero-extension (`zext8To64`, `zext64To128`), pointer indexing (`gep64`),
memory loads/stores (`load64`, `store64`), comparisons (`icmp64`), and
conditional selection (`select64`).
-/

abbrev VReg := Nat

/-- `AnLLVM` instructions prior to `IRTranslator`. -/
inductive AnLlvmInstr where
  | arg128      (dst : VReg) (loArgIdx hiArgIdx : Nat)
  | arg64       (dst : VReg) (argIdx : Nat)
  | arg8        (dst : VReg) (argIdx : Nat)
  | argPtr      (dst : VReg) (argIdx : Nat)
  | const64     (dst : VReg) (imm : Nat)
  | add128      (dst lhs rhs : VReg)
  | add64       (dst lhs rhs : VReg)
  | add8        (dst lhs rhs : VReg)
  | zext8To64   (dst src : VReg)
  | zext64To128 (dst src : VReg)
  | gep64       (dst base idx : VReg)
  | load64      (dst ptrReg : VReg)
  | store64     (valReg ptrReg : VReg)
  | icmp64      (dst : VReg) (pred : IntPred) (lhs rhs : VReg)
  | select64    (dst cond tVal fVal : VReg)
  deriving DecidableEq, Repr

/-- Return convention of an `AnLLVM` function. -/
inductive AnLlvmRet where
  | ret128 (src : VReg)
  | ret64  (src : VReg)
  deriving DecidableEq, Repr

/-- An `AnLLVM` function consists of a straight-line or if-converted SSA body
and a return descriptor. -/
structure AnLlvmProg where
  body : List AnLlvmInstr
  ret  : AnLlvmRet
  deriving DecidableEq, Repr

/-- Looks up an ABI argument index `0..5` from `AbiQuery`. -/
def AbiQuery.getArg (q : AbiQuery) : Nat → Nat
  | 0 => q.arg0 % word64Mod
  | 1 => q.arg1 % word64Mod
  | 2 => q.arg2 % word64Mod
  | 3 => q.arg3 % word64Mod
  | 4 => q.arg4 % word64Mod
  | _ => q.arg5 % word64Mod

/-- Total functional environment mapping `VReg` to `Option MVal`. -/
abbrev VRegEnv := List (VReg × MVal)

def envGet {α : Type} (env : List (VReg × α)) (r : VReg) : Option α :=
  match env with
  | [] => none
  | (k, v) :: rest => if k = r then some v else envGet rest r

def envSet {α : Type} (env : List (VReg × α)) (r : VReg) (v : α) :
    List (VReg × α) :=
  (r, v) :: env

@[simp]
theorem envGet_envSet_same {α : Type} (env : List (VReg × α)) (r : VReg) (v : α) :
    envGet (envSet env r v) r = some v := by
  simp [envGet, envSet]

@[simp]
theorem envGet_envSet_ne {α : Type} (env : List (VReg × α)) (r₁ r₂ : VReg) (v : α)
    (hNe : r₁ ≠ r₂) :
    envGet (envSet env r₁ v) r₂ = envGet env r₂ := by
  simp [envGet, envSet, hNe]

/-- Unsigned 64-bit addition with carry-in `cin`, returning `(sumLo, carryOut)`.
This is the shared semantic core of 128-bit `add128`, `G_UADDO` / `G_UADDE`,
and `ADD64_FLAGS` / `ADDC64_FLAGS`. -/
def add64WithCarry (a b : Nat) (cin : Bool) : Nat × Bool :=
  let cNat := if cin then 1 else 0
  let total := (a % word64Mod) + (b % word64Mod) + cNat
  (total % word64Mod, decide (total ≥ word64Mod))

/-- Evaluates a single `AnLlvmInstr`. -/
def evalAnLlvmInstr (q : AbiQuery) (env : VRegEnv) (heap : List Nat)
    (inst : AnLlvmInstr) : Option (VRegEnv × List Nat) :=
  match inst with
  | .arg128 dst loIdx hiIdx =>
    some (envSet env dst (.v128 (q.getArg loIdx) (q.getArg hiIdx)), heap)
  | .arg64 dst idx =>
    some (envSet env dst (.v64 (q.getArg idx)), heap)
  | .arg8 dst idx =>
    some (envSet env dst (.v8 ((q.getArg idx) % word8Mod)), heap)
  | .argPtr dst idx =>
    some (envSet env dst (.ptr (q.getArg idx)), heap)
  | .const64 dst imm =>
    some (envSet env dst (.v64 (imm % word64Mod)), heap)
  | .add128 dst lhs rhs =>
    match envGet env lhs, envGet env rhs with
    | some (.v128 aLo aHi), some (.v128 bLo bHi) =>
      let (lo, c0) := add64WithCarry aLo bLo false
      let (hi, _)  := add64WithCarry aHi bHi c0
      some (envSet env dst (.v128 lo hi), heap)
    | _, _ => none
  | .add64 dst lhs rhs =>
    match envGet env lhs, envGet env rhs with
    | some (.v64 a), some (.v64 b) =>
      let (lo, _) := add64WithCarry a b false
      some (envSet env dst (.v64 lo), heap)
    | _, _ => none
  | .add8 dst lhs rhs =>
    match envGet env lhs, envGet env rhs with
    | some (.v8 a), some (.v8 b) =>
      some (envSet env dst (.v8 ((a + b) % word8Mod)), heap)
    | _, _ => none
  | .zext8To64 dst src =>
    match envGet env src with
    | some (.v8 a) => some (envSet env dst (.v64 (a % word8Mod)), heap)
    | _ => none
  | .zext64To128 dst src =>
    match envGet env src with
    | some (.v64 a) => some (envSet env dst (.v128 (a % word64Mod) 0), heap)
    | _ => none
  | .gep64 dst base idx =>
    match envGet env base, envGet env idx with
    | some (.ptr b), some (.v64 i) =>
      let byteOff := ((i * 8) % word64Mod)
      some (envSet env dst (.ptr (b + byteOff / 8)), heap)
    | _, _ => none
  | .load64 dst ptrReg =>
    match envGet env ptrReg with
    | some (.ptr idx) =>
      match heapLoad heap idx with
      | some v => some (envSet env dst (.v64 (v % word64Mod)), heap)
      | none => none
    | _ => none
  | .store64 valReg ptrReg =>
    match envGet env valReg, envGet env ptrReg with
    | some (.v64 v), some (.ptr idx) =>
      match heapStore heap idx v with
      | some heap' => some (env, heap')
      | none => none
    | _, _ => none
  | .icmp64 dst pred lhs rhs =>
    match envGet env lhs, envGet env rhs with
    | some (.v64 a), some (.v64 b) =>
      some (envSet env dst (.v1 (pred.eval a b)), heap)
    | _, _ => none
  | .select64 dst cond tVal fVal =>
    match envGet env cond, envGet env tVal, envGet env fVal with
    | some (.v1 c), some (.v64 tv), some (.v64 fv) =>
      some (envSet env dst (.v64 (if c then tv else fv)), heap)
    | _, _, _ => none

/-- Evaluates a list of `AnLlvmInstr`s. -/
def evalAnLlvmBody (q : AbiQuery) (env : VRegEnv) (heap : List Nat) :
    List AnLlvmInstr → Option (VRegEnv × List Nat)
  | [] => some (env, heap)
  | i :: rest =>
    match evalAnLlvmInstr q env heap i with
    | some (env', heap') => evalAnLlvmBody q env' heap' rest
    | none => none

/-- Evaluates an `AnLlvmProg` on an `AbiQuery`. -/
def evalAnLlvmProg (p : AnLlvmProg) (q : AbiQuery) : Option AbiOut :=
  match evalAnLlvmBody q [] q.heap p.body with
  | none => none
  | some (env, heap') =>
    match p.ret with
    | .ret128 src =>
      match envGet env src with
      | some (.v128 lo hi) =>
        some { retLo := lo, retHi := hi, heap := heap', calleeSaved := q.calleeSaved }
      | _ => none
    | .ret64 src =>
      match envGet env src with
      | some (.v64 lo) =>
        some { retLo := lo, retHi := 0, heap := heap', calleeSaved := q.calleeSaved }
      | _ => none

/-- `AnLlvmLang` packaged as an Anneal `Language AbiOut`. -/
abbrev AnLlvmLang : Language AbiOut :=
  Language.mkSimple AnLlvmProg AbiQuery AbiOut
    (fun p => Behavior.ofOption (evalAnLlvmProg p))

/-!
## Section 4: Unified `AnMachineIR` (`GlobalISel` Generic + Target SSA IR)

In LLVM's `GlobalISel` (`llvm/CodeGen/GlobalISel/`), `IRTranslator`, `Legalizer`,
`RegBankSelect`, and `InstructionSelect` all mutate a single `MachineFunction`
representation (`llvm/CodeGen/MachineFunction.h:187-201`).

We improve on upstream LLVM's `MachineInstr` in one critical way for formal
verification: **target flag-setting and flag-consuming instructions in
`AnMachineIR` (`ADD64_FLAGS`, `ADDC64_FLAGS`, `CMP64_FLAGS`, `CSEL64`) take and
produce explicit SSA flag virtual registers (`vflag : VReg`) throughout
`MachineSSA`**, rather than switching prematurely to `implicit-def $nzcv` /
`implicit-def $eflags` during `InstructionSelect`.
-/

/-- Register banks assigned by `RegBankSelect`
(`llvm/CodeGen/GlobalISel/RegBankSelect.h`). -/
inductive RegBank where
  | unassigned
  | gpr
  | flag
  deriving DecidableEq, Repr

/-- `MachineFunctionProperties` (`llvm/CodeGen/MachineFunction.h:187-201`). -/
structure MachineFunctionProperties where
  isSSA           : Bool
  legalized       : Bool
  regBankSelected : Bool
  selected        : Bool
  noVRegs         : Bool
  deriving DecidableEq, Repr

/-- Unified `AnMachineInstr` covering both pre-ISel `GenericOpcode` (`G_*`,
`llvm/Support/TargetOpcodes.def:255-755`) and post-ISel `TargetOpcode`
(AArch64/x86-64/RISC-V target instructions with explicit SSA flag registers). -/
inductive AnMachineInstr where
  -- ABI entry copy pseudo-instructions
  | COPY_FROM_ABI_GPR (dst : VReg) (bank : RegBank) (ty : LowLevelType) (argIdx : Nat)
  -- Pre-ISel Generic MachineIR (`GenericOpcode`)
  | G_CONSTANT       (dst : VReg) (bank : RegBank) (ty : LowLevelType) (imm : Nat)
  | G_ADD            (dst : VReg) (bank : RegBank) (ty : LowLevelType) (lhs rhs : VReg)
  | G_MUL_IMM        (dst : VReg) (bank : RegBank) (ty : LowLevelType) (src : VReg) (imm : Nat)
  | G_SHL_IMM        (dst : VReg) (bank : RegBank) (ty : LowLevelType) (src : VReg) (shift : Nat)
  | G_TRUNC64_TO_8   (dst : VReg) (bank : RegBank) (src : VReg)
  | G_ZEXT8_TO_64    (dst : VReg) (bank : RegBank) (src : VReg)
  | G_ZEXT64_TO_128  (dst : VReg) (bank : RegBank) (src : VReg)
  | G_MERGE_VALUES   (dst : VReg) (bank : RegBank) (lo hi : VReg)
  | G_UNMERGE_VALUES (dstLo dstHi : VReg) (bank : RegBank) (src : VReg)
  | G_UADDO          (dst vflagOut : VReg) (bank : RegBank) (lhs rhs : VReg)
  | G_UADDE          (dst vflagOut : VReg) (bank : RegBank) (lhs rhs vflagIn : VReg)
  | G_PTR_ADD        (dst : VReg) (bank : RegBank) (base offset : VReg)
  | G_LOAD64         (dst : VReg) (bank : RegBank) (ptrReg : VReg)
  | G_STORE64        (valReg ptrReg : VReg)
  | G_ICMP64         (dst : VReg) (bank : RegBank) (pred : IntPred) (lhs rhs : VReg)
  | G_SELECT64       (dst : VReg) (bank : RegBank) (cond tVal fVal : VReg)
  -- Post-ISel Target MachineIR (`TargetOpcode`) with explicit SSA `vflag`
  | MOV_IMM64        (dst : VReg) (imm : Nat)
  | ADD64            (dst lhs rhs : VReg)
  | ADD8_MASK        (dst lhs rhs : VReg)
  | ZEXT8_TO_64      (dst src : VReg)
  | ADD64_FLAGS      (dst vflagOut lhs rhs : VReg)
  | ADDC64_FLAGS     (dst vflagOut lhs rhs vflagIn : VReg)
  | ADD_SHIFTED_PTR  (dst base idx : VReg) (shift : Nat)
  | LDR64            (dst ptrReg : VReg)
  | STR64            (valReg ptrReg : VReg)
  | CMP64_FLAGS      (vflagOut : VReg) (pred : IntPred) (lhs rhs : VReg)
  | CSEL64           (dst vflagIn tVal fVal : VReg)
  deriving DecidableEq, Repr

/-- Return instruction of a `MachineFunction`. -/
inductive AnMachineRet where
  | G_RET128  (src : VReg)
  | G_RET64   (src : VReg)
  | RET_PAIR  (loReg hiReg : VReg)
  | RET_SINGLE (loReg : VReg)
  deriving DecidableEq, Repr

/-- Unified `MachineFunction` (`AnMachineIR`) used across all four `GlobalISel`
stages (`IRTranslator`, `Legalizer`, `RegBankSelect`, `InstructionSelect`). -/
structure MachineFunction where
  props : MachineFunctionProperties
  body  : List AnMachineInstr
  ret   : AnMachineRet
  deriving DecidableEq, Repr

/-- Operational semantics of a single `AnMachineInstr`. -/
def evalAnMachineInstr (q : AbiQuery) (env : VRegEnv) (heap : List Nat)
    (inst : AnMachineInstr) : Option (VRegEnv × List Nat) :=
  match inst with
  | .COPY_FROM_ABI_GPR dst _ ty argIdx =>
    let raw := q.getArg argIdx
    let v := match ty with
      | .s1   => MVal.v1 (decide (raw % 2 = 1))
      | .s8   => MVal.v8 (raw % word8Mod)
      | .s32  => MVal.v32 (raw % word32Mod)
      | .s64  => MVal.v64 raw
      | .s128 => MVal.v128 raw 0
      | .p0   => MVal.ptr raw
    some (envSet env dst v, heap)
  | .G_CONSTANT dst _ ty imm =>
    let v := match ty with
      | .s1   => MVal.v1 (decide (imm % 2 = 1))
      | .s8   => MVal.v8 (imm % word8Mod)
      | .s32  => MVal.v32 (imm % word32Mod)
      | .s64  => MVal.v64 (imm % word64Mod)
      | .s128 => MVal.v128 (imm % word64Mod) 0
      | .p0   => MVal.ptr (imm % word64Mod)
    some (envSet env dst v, heap)
  | .G_ADD dst _ ty lhs rhs =>
    match ty, envGet env lhs, envGet env rhs with
    | .s128, some (.v128 aLo aHi), some (.v128 bLo bHi) =>
      let (lo, c0) := add64WithCarry aLo bLo false
      let (hi, _)  := add64WithCarry aHi bHi c0
      some (envSet env dst (.v128 lo hi), heap)
    | .s64, some (.v64 a), some (.v64 b) =>
      let (lo, _) := add64WithCarry a b false
      some (envSet env dst (.v64 lo), heap)
    | .s8, some (.v8 a), some (.v8 b) =>
      some (envSet env dst (.v8 ((a + b) % word8Mod)), heap)
    | _, _, _ => none
  | .G_MUL_IMM dst _ .s64 src imm =>
    match envGet env src with
    | some (.v64 a) => some (envSet env dst (.v64 ((a * imm) % word64Mod)), heap)
    | _ => none
  | .G_MUL_IMM _ _ _ _ _ => none
  | .G_SHL_IMM dst _ .s64 src shift =>
    match envGet env src with
    | some (.v64 a) => some (envSet env dst (.v64 ((a * (2 ^ shift)) % word64Mod)), heap)
    | _ => none
  | .G_SHL_IMM _ _ _ _ _ => none
  | .G_TRUNC64_TO_8 dst _ src =>
    match envGet env src with
    | some (.v64 a) => some (envSet env dst (.v8 (a % word8Mod)), heap)
    | _ => none
  | .G_ZEXT8_TO_64 dst _ src =>
    match envGet env src with
    | some (.v8 a) => some (envSet env dst (.v64 (a % word8Mod)), heap)
    | _ => none
  | .G_ZEXT64_TO_128 dst _ src =>
    match envGet env src with
    | some (.v64 a) => some (envSet env dst (.v128 (a % word64Mod) 0), heap)
    | _ => none
  | .G_MERGE_VALUES dst _ lo hi =>
    match envGet env lo, envGet env hi with
    | some (.v64 l), some (.v64 h) =>
      some (envSet env dst (.v128 (l % word64Mod) (h % word64Mod)), heap)
    | _, _ => none
  | .G_UNMERGE_VALUES dstLo dstHi _ src =>
    match envGet env src with
    | some (.v128 l h) =>
      some (envSet (envSet env dstLo (.v64 l)) dstHi (.v64 h), heap)
    | _ => none
  | .G_UADDO dst vflagOut _ lhs rhs =>
    match envGet env lhs, envGet env rhs with
    | some (.v64 a), some (.v64 b) =>
      let (lo, carry) := add64WithCarry a b false
      some (envSet (envSet env dst (.v64 lo)) vflagOut (.v1 carry), heap)
    | _, _ => none
  | .G_UADDE dst vflagOut _ lhs rhs vflagIn =>
    match envGet env lhs, envGet env rhs, envGet env vflagIn with
    | some (.v64 a), some (.v64 b), some (.v1 cin) =>
      let (lo, carry) := add64WithCarry a b cin
      some (envSet (envSet env dst (.v64 lo)) vflagOut (.v1 carry), heap)
    | _, _, _ => none
  | .G_PTR_ADD dst _ base offset =>
    match envGet env base, envGet env offset with
    | some (.ptr b), some (.v64 byteOff) =>
      some (envSet env dst (.ptr (b + (byteOff % word64Mod) / 8)), heap)
    | _, _ => none
  | .G_LOAD64 dst _ ptrReg =>
    match envGet env ptrReg with
    | some (.ptr idx) =>
      match heapLoad heap idx with
      | some v => some (envSet env dst (.v64 (v % word64Mod)), heap)
      | none => none
    | _ => none
  | .G_STORE64 valReg ptrReg =>
    match envGet env valReg, envGet env ptrReg with
    | some (.v64 v), some (.ptr idx) =>
      match heapStore heap idx v with
      | some heap' => some (env, heap')
      | none => none
    | _, _ => none
  | .G_ICMP64 dst _ pred lhs rhs =>
    match envGet env lhs, envGet env rhs with
    | some (.v64 a), some (.v64 b) =>
      some (envSet env dst (.v1 (pred.eval a b)), heap)
    | _, _ => none
  | .G_SELECT64 dst _ cond tVal fVal =>
    match envGet env cond, envGet env tVal, envGet env fVal with
    | some (.v1 c), some (.v64 tv), some (.v64 fv) =>
      some (envSet env dst (.v64 (if c then tv else fv)), heap)
    | _, _, _ => none
  -- Post-ISel `TargetOpcode` instructions
  | .MOV_IMM64 dst imm =>
    some (envSet env dst (.v64 (imm % word64Mod)), heap)
  | .ADD64 dst lhs rhs =>
    match envGet env lhs, envGet env rhs with
    | some (.v64 a), some (.v64 b) =>
      let (lo, _) := add64WithCarry a b false
      some (envSet env dst (.v64 lo), heap)
    | _, _ => none
  | .ADD8_MASK dst lhs rhs =>
    match envGet env lhs, envGet env rhs with
    | some (.v8 a), some (.v8 b) =>
      some (envSet env dst (.v8 ((a + b) % word8Mod)), heap)
    | _, _ => none
  | .ZEXT8_TO_64 dst src =>
    match envGet env src with
    | some (.v8 a) => some (envSet env dst (.v64 (a % word8Mod)), heap)
    | _ => none
  | .ADD64_FLAGS dst vflagOut lhs rhs =>
    match envGet env lhs, envGet env rhs with
    | some (.v64 a), some (.v64 b) =>
      let (lo, carry) := add64WithCarry a b false
      some (envSet (envSet env dst (.v64 lo)) vflagOut (.v1 carry), heap)
    | _, _ => none
  | .ADDC64_FLAGS dst vflagOut lhs rhs vflagIn =>
    match envGet env lhs, envGet env rhs, envGet env vflagIn with
    | some (.v64 a), some (.v64 b), some (.v1 cin) =>
      let (lo, carry) := add64WithCarry a b cin
      some (envSet (envSet env dst (.v64 lo)) vflagOut (.v1 carry), heap)
    | _, _, _ => none
  | .ADD_SHIFTED_PTR dst base idx shift =>
    match envGet env base, envGet env idx with
    | some (.ptr b), some (.v64 i) =>
      let byteOff := (i * (2 ^ shift)) % word64Mod
      some (envSet env dst (.ptr (b + byteOff / 8)), heap)
    | _, _ => none
  | .LDR64 dst ptrReg =>
    match envGet env ptrReg with
    | some (.ptr idx) =>
      match heapLoad heap idx with
      | some v => some (envSet env dst (.v64 (v % word64Mod)), heap)
      | none => none
    | _ => none
  | .STR64 valReg ptrReg =>
    match envGet env valReg, envGet env ptrReg with
    | some (.v64 v), some (.ptr idx) =>
      match heapStore heap idx v with
      | some heap' => some (env, heap')
      | none => none
    | _, _ => none
  | .CMP64_FLAGS vflagOut pred lhs rhs =>
    match envGet env lhs, envGet env rhs with
    | some (.v64 a), some (.v64 b) =>
      some (envSet env vflagOut (.v1 (pred.eval a b)), heap)
    | _, _ => none
  | .CSEL64 dst vflagIn tVal fVal =>
    match envGet env vflagIn, envGet env tVal, envGet env fVal with
    | some (.v1 c), some (.v64 tv), some (.v64 fv) =>
      some (envSet env dst (.v64 (if c then tv else fv)), heap)
    | _, _, _ => none

/-- Evaluates a sequence of `AnMachineInstr`s. -/
def evalAnMachineBody (q : AbiQuery) (env : VRegEnv) (heap : List Nat) :
    List AnMachineInstr → Option (VRegEnv × List Nat)
  | [] => some (env, heap)
  | i :: rest =>
    match evalAnMachineInstr q env heap i with
    | some (env', heap') => evalAnMachineBody q env' heap' rest
    | none => none

@[simp]
theorem evalAnMachineBody_append (q : AbiQuery) (env : VRegEnv) (heap : List Nat)
    (xs ys : List AnMachineInstr) :
    evalAnMachineBody q env heap (xs ++ ys) =
      match evalAnMachineBody q env heap xs with
      | some (env', heap') => evalAnMachineBody q env' heap' ys
      | none => none := by
  induction xs generalizing env heap with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.cons_append, evalAnMachineBody]
    cases evalAnMachineInstr q env heap x with
    | none => rfl
    | some pair => exact ih pair.1 pair.2

/-- Evaluates a `MachineFunction` on an `AbiQuery`. -/
def evalMachineFunction (mf : MachineFunction) (q : AbiQuery) : Option AbiOut :=
  match evalAnMachineBody q [] q.heap mf.body with
  | none => none
  | some (env, heap') =>
    match mf.ret with
    | .G_RET128 src =>
      match envGet env src with
      | some (.v128 lo hi) =>
        some { retLo := lo, retHi := hi, heap := heap', calleeSaved := q.calleeSaved }
      | _ => none
    | .G_RET64 src =>
      match envGet env src with
      | some (.v64 lo) =>
        some { retLo := lo, retHi := 0, heap := heap', calleeSaved := q.calleeSaved }
      | _ => none
    | .RET_PAIR loReg hiReg =>
      match envGet env loReg, envGet env hiReg with
      | some (.v64 lo), some (.v64 hi) =>
        some { retLo := lo, retHi := hi, heap := heap', calleeSaved := q.calleeSaved }
      | _, _ => none
    | .RET_SINGLE loReg =>
      match envGet env loReg with
      | some (.v64 lo) =>
        some { retLo := lo, retHi := 0, heap := heap', calleeSaved := q.calleeSaved }
      | _ => none

/-- `AnMachineLang` packaged as an Anneal `Language AbiOut`. -/
abbrev AnMachineLang : Language AbiOut :=
  Language.mkSimple MachineFunction AbiQuery AbiOut
    (fun mf => Behavior.ofOption (evalMachineFunction mf))

/-- Identity codec between `AnLlvmLang` and `AnMachineLang`. -/
def llvmToMachineCodec : BehaviorCodec AnLlvmLang AnMachineLang :=
  mkSimpleCodec (fun p => Behavior.ofOption (evalAnLlvmProg p))
                (fun mf => Behavior.ofOption (evalMachineFunction mf))

/-- Identity codec on `AnMachineLang` for `GlobalISel` in-place passes
(`Legalizer`, `RegBankSelect`, `InstructionSelect`). -/
def machineIdCodec : BehaviorCodec AnMachineLang AnMachineLang :=
  mkSimpleCodec (fun mf => Behavior.ofOption (evalMachineFunction mf))
                (fun mf => Behavior.ofOption (evalMachineFunction mf))

/-!
## Section 5: Stage 1 — `IRTranslator` (`AnLlvmLang -> AnMachineLang`)

`IRTranslator` (`llvm/CodeGen/GlobalISel/IRTranslator.h`) lowers `AnLLVM`
instructions directly into `GenericOpcode` `AnMachineInstr`s inside a
`MachineFunction` with `props.isSSA = true`.

Unlike `SelectionDAGBuilder`, which converts each basic block into an auxiliary
graph of `SDNode`s with `MVT::Other` (`Chain`) and `MVT::Glue` edges,
`IRTranslator` is a direct 1-to-1 structural homomorphic translation from
`AnLlvmInstr` to `AnMachineInstr`.
-/

/-- Translates a single `AnLlvmInstr` into `GenericOpcode` `AnMachineInstr`s.
For `arg128`, we use reserved scratch virtual registers `1000 + dst` and
`2000 + dst` to model `IRTranslator`'s `COPY $x0; COPY $x1; G_MERGE_VALUES`. -/
def translateLlvmInstr : AnLlvmInstr → List AnMachineInstr
  | .arg128 dst loIdx hiIdx =>
    let loTmp := 1000 + dst
    let hiTmp := 2000 + dst
    [ .COPY_FROM_ABI_GPR loTmp .unassigned .s64 loIdx
    , .COPY_FROM_ABI_GPR hiTmp .unassigned .s64 hiIdx
    , .G_MERGE_VALUES dst .unassigned loTmp hiTmp ]
  | .arg64 dst idx =>
    [ .COPY_FROM_ABI_GPR dst .unassigned .s64 idx ]
  | .arg8 dst idx =>
    [ .COPY_FROM_ABI_GPR dst .unassigned .s8 idx ]
  | .argPtr dst idx =>
    [ .COPY_FROM_ABI_GPR dst .unassigned .p0 idx ]
  | .const64 dst imm =>
    [ .G_CONSTANT dst .unassigned .s64 imm ]
  | .add128 dst lhs rhs =>
    [ .G_ADD dst .unassigned .s128 lhs rhs ]
  | .add64 dst lhs rhs =>
    [ .G_ADD dst .unassigned .s64 lhs rhs ]
  | .add8 dst lhs rhs =>
    [ .G_ADD dst .unassigned .s8 lhs rhs ]
  | .zext8To64 dst src =>
    [ .G_ZEXT8_TO_64 dst .unassigned src ]
  | .zext64To128 dst src =>
    [ .G_ZEXT64_TO_128 dst .unassigned src ]
  | .gep64 dst base idx =>
    let offReg := 3000 + dst
    [ .G_MUL_IMM offReg .unassigned .s64 idx 8
    , .G_PTR_ADD dst .unassigned base offReg ]
  | .load64 dst ptrReg =>
    [ .G_LOAD64 dst .unassigned ptrReg ]
  | .store64 valReg ptrReg =>
    [ .G_STORE64 valReg ptrReg ]
  | .icmp64 dst pred lhs rhs =>
    [ .G_ICMP64 dst .unassigned pred lhs rhs ]
  | .select64 dst cond tVal fVal =>
    [ .G_SELECT64 dst .unassigned cond tVal fVal ]

/-- Translates a list of `AnLlvmInstr`s. -/
def translateLlvmBody : List AnLlvmInstr → List AnMachineInstr
  | [] => []
  | i :: rest => translateLlvmInstr i ++ translateLlvmBody rest

/-- Translates an `AnLlvmRet` into an `AnMachineRet`. -/
def translateLlvmRet : AnLlvmRet → AnMachineRet
  | .ret128 src => .G_RET128 src
  | .ret64 src  => .G_RET64 src

/-- Full `IRTranslator` pass (`AnLlvmProg → MachineFunction`). -/
def irTranslatorPass (p : AnLlvmProg) : MachineFunction := {
  props := {
    isSSA           := true
    legalized       := false
    regBankSelected := false
    selected        := false
    noVRegs         := false
  }
  body  := translateLlvmBody p.body
  ret   := translateLlvmRet p.ret
}

/-!
### Representative Benchmark Programs (`add_u128_and_u8` and `gep_load_select`)

We define the two benchmark programs from our `llc` 21.1.8 empirical study:
1. `llvmAddU128AndU8`: 128-bit addition combined with narrow 8-bit addition and
   zero-extension (`add i128`, `add i8`, `zext i8 to i64`, `zext i64 to i128`).
2. `llvmGepLoadSelect`: pointer array indexing (`getelementptr i64`), 64-bit
   memory load (`load i64`), unsigned comparison (`icmp ugt`), and conditional
   select (`select i1`).
-/

def llvmAddU128AndU8 : AnLlvmProg := {
  body := [
    .arg128 0 0 1,      -- %0 = (arg0, arg1) : i128
    .arg128 1 2 3,      -- %1 = (arg2, arg3) : i128
    .arg8 2 4,          -- %2 = trunc arg4 : i8
    .arg8 3 5,          -- %3 = trunc arg5 : i8
    .add128 10 0 1,     -- %10 = add i128 %0, %1
    .add8 11 2 3,       -- %11 = add i8 %2, %3
    .zext8To64 12 11,   -- %12 = zext i8 %11 to i64
    .zext64To128 13 12, -- %13 = zext i64 %12 to i128
    .add128 14 10 13    -- %14 = add i128 %10, %13
  ]
  ret := .ret128 14
}

def llvmGepLoadSelect : AnLlvmProg := {
  body := [
    .argPtr 0 0,            -- %0 = base : ptr
    .arg64 1 1,             -- %1 = idx : i64
    .arg64 3 3,             -- %3 = fallback : i64
    .gep64 7 0 1,           -- %7 = getelementptr i64, ptr %0, i64 %1
    .load64 9 7,            -- %9 = load i64, ptr %7
    .icmp64 10 .ugt 9 3,    -- %10 = icmp ugt i64 %9, %3
    .select64 11 10 9 3     -- %11 = select i1 %10, i64 %9, i64 %3
  ]
  ret := .ret64 11
}

/-- Pointwise equivalence between `evalAnLlvmProg` and `evalMachineFunction ∘
irTranslatorPass` on `llvmAddU128AndU8` for all `AbiQuery` inputs. -/
theorem irTranslator_addU128AndU8_eval_eq (q : AbiQuery) :
    evalMachineFunction (irTranslatorPass llvmAddU128AndU8) q =
      evalAnLlvmProg llvmAddU128AndU8 q := by
  simp [llvmAddU128AndU8, irTranslatorPass, translateLlvmBody, translateLlvmInstr,
        translateLlvmRet, evalMachineFunction, evalAnMachineBody,
        evalAnMachineInstr, evalAnLlvmProg, evalAnLlvmBody, evalAnLlvmInstr,
        envGet, envSet, AbiQuery.getArg]

/-- Modulo idempotence `(a % word64Mod) % word64Mod = a % word64Mod`. -/
@[simp]
theorem mod_word64Mod_idem (a : Nat) :
    (a % word64Mod) % word64Mod = a % word64Mod :=
  Nat.mod_mod_of_dvd a (Nat.dvd_refl word64Mod)

/-- Pointwise equivalence between `evalAnLlvmProg` and `evalMachineFunction ∘
irTranslatorPass` on `llvmGepLoadSelect` for all `AbiQuery` inputs (including
out-of-bounds memory accesses where both sides evaluate to `none`). -/
theorem irTranslator_gepLoadSelect_eval_eq (q : AbiQuery) :
    evalMachineFunction (irTranslatorPass llvmGepLoadSelect) q =
      evalAnLlvmProg llvmGepLoadSelect q := by
  simp [llvmGepLoadSelect, irTranslatorPass, translateLlvmBody,
        translateLlvmInstr, translateLlvmRet, evalMachineFunction,
        evalAnMachineBody, evalAnMachineInstr, evalAnLlvmProg,
        evalAnLlvmBody, evalAnLlvmInstr, envGet, envSet]
  cases heapLoad q.heap (q.getArg 0 + q.getArg 1 * 8 % word64Mod / 8) <;>
    simp [envGet]

/-- Stage 1 (`IRTranslator`) `Compiles` theorem on `llvmAddU128AndU8`. -/
theorem irTranslator_addU128AndU8_compiles :
    Compiles AnLlvmLang AnMachineLang llvmToMachineCodec
      llvmAddU128AndU8 (irTranslatorPass llvmAddU128AndU8) := by
  apply compiles_of_eval_eq
  intro q res h
  rw [irTranslator_addU128AndU8_eval_eq]
  exact h

/-- Stage 1 (`IRTranslator`) `Compiles` theorem on `llvmGepLoadSelect`. -/
theorem irTranslator_gepLoadSelect_compiles :
    Compiles AnLlvmLang AnMachineLang llvmToMachineCodec
      llvmGepLoadSelect (irTranslatorPass llvmGepLoadSelect) := by
  apply compiles_of_eval_eq
  intro q res h
  rw [irTranslator_gepLoadSelect_eval_eq]
  exact h

/-!
## Section 6: Stage 2 — `Legalizer`, `ArtifactCombiner`, and `RegBankSelect`

In LLVM's `GlobalISel`, `LegalizerPass` (`llvm/CodeGen/GlobalISel/LegalizerHelper.h`
and `llvm/CodeGen/GlobalISel/LegalizationArtifactCombiner.h`) runs two phases in
tandem before `RegBankSelect` (`llvm/CodeGen/GlobalISel/RegBankSelect.h`):
1. `LegalizerHelper`:
   - `narrowScalar` splits 128-bit `G_ADD s128` into:
     a. `G_UNMERGE_VALUES` of the two `s128` operands into `(aLo, aHi)` and
        `(bLo, bHi)`,
     b. `G_UADDO dstLo vflag aLo bLo` (computing the low 64-bit sum and an
        **explicit SSA carry virtual register `vflag : s1`**),
     c. `G_UADDE dstHi vflag2 aHi bHi vflag` (computing the high 64-bit sum
        using `vflag`), and
     d. `G_MERGE_VALUES dst dstLo dstHi`.
   - `lower` rewrites `G_ZEXT64_TO_128 dst src` into `G_CONSTANT zero 0` +
     `G_MERGE_VALUES dst src zero`, and rewrites `G_MUL_IMM dst s64 src 8` into
     `G_SHL_IMM dst s64 src 3`.
2. `LegalizationArtifactCombiner::tryCombineUnmergeValues`
   (`llvm/CodeGen/GlobalISel/LegalizationArtifactCombiner.h:1064-1270`):
   folds every `G_UNMERGE_VALUES (dstLo, dstHi) src` with its producer
   `G_MERGE_VALUES src lo hi` by substituting `(dstLo ↦ lo, dstHi ↦ hi)` and
   erasing both artifact instructions.
3. `RegBankSelect` (`llvm/CodeGen/GlobalISel/RegBankSelect.h`): assigns `.gpr`
   to integer/pointer virtual registers and `.flag` to carry/predicate virtual
   registers.
-/

/-- Legalizes and assigns register banks for a single `AnMachineInstr`. -/
def legalizeAndBankInstr : AnMachineInstr → List AnMachineInstr
  | .COPY_FROM_ABI_GPR dst _ ty argIdx =>
    [ .COPY_FROM_ABI_GPR dst .gpr ty argIdx ]
  | .G_CONSTANT dst _ ty imm =>
    [ .G_CONSTANT dst .gpr ty imm ]
  | .G_ADD dst _ .s128 lhs rhs =>
    let aLo   := 4000 + dst
    let aHi   := 4100 + dst
    let bLo   := 4200 + dst
    let bHi   := 4300 + dst
    let sumLo := 4400 + dst
    let sumHi := 4500 + dst
    let cFlag := 4600 + dst
    let cOut2 := 4700 + dst
    [ .G_UNMERGE_VALUES aLo aHi .gpr lhs
    , .G_UNMERGE_VALUES bLo bHi .gpr rhs
    , .G_UADDO sumLo cFlag .gpr aLo bLo
    , .G_UADDE sumHi cOut2 .gpr aHi bHi cFlag
    , .G_MERGE_VALUES dst .gpr sumLo sumHi ]
  | .G_ADD dst _ ty lhs rhs =>
    [ .G_ADD dst .gpr ty lhs rhs ]
  | .G_MUL_IMM dst _ .s64 src 8 =>
    [ .G_SHL_IMM dst .gpr .s64 src 3 ]
  | .G_MUL_IMM dst _ ty src imm =>
    [ .G_MUL_IMM dst .gpr ty src imm ]
  | .G_SHL_IMM dst _ ty src shift =>
    [ .G_SHL_IMM dst .gpr ty src shift ]
  | .G_TRUNC64_TO_8 dst _ src =>
    [ .G_TRUNC64_TO_8 dst .gpr src ]
  | .G_ZEXT8_TO_64 dst _ src =>
    [ .G_ZEXT8_TO_64 dst .gpr src ]
  | .G_ZEXT64_TO_128 dst _ src =>
    let zeroReg := 4800 + dst
    [ .G_CONSTANT zeroReg .gpr .s64 0
    , .G_MERGE_VALUES dst .gpr src zeroReg ]
  | .G_MERGE_VALUES dst _ lo hi =>
    [ .G_MERGE_VALUES dst .gpr lo hi ]
  | .G_UNMERGE_VALUES dstLo dstHi _ src =>
    [ .G_UNMERGE_VALUES dstLo dstHi .gpr src ]
  | .G_UADDO dst vflagOut _ lhs rhs =>
    [ .G_UADDO dst vflagOut .gpr lhs rhs ]
  | .G_UADDE dst vflagOut _ lhs rhs vflagIn =>
    [ .G_UADDE dst vflagOut .gpr lhs rhs vflagIn ]
  | .G_PTR_ADD dst _ base offset =>
    [ .G_PTR_ADD dst .gpr base offset ]
  | .G_LOAD64 dst _ ptrReg =>
    [ .G_LOAD64 dst .gpr ptrReg ]
  | .G_STORE64 valReg ptrReg =>
    [ .G_STORE64 valReg ptrReg ]
  | .G_ICMP64 dst _ pred lhs rhs =>
    [ .G_ICMP64 dst .flag pred lhs rhs ]
  | .G_SELECT64 dst _ cond tVal fVal =>
    [ .G_SELECT64 dst .gpr cond tVal fVal ]
  | other => [ other ]

/-- Legalizes a list of `AnMachineInstr`s. -/
def legalizeAndBankBody : List AnMachineInstr → List AnMachineInstr
  | [] => []
  | i :: rest => legalizeAndBankInstr i ++ legalizeAndBankBody rest

/-- Looks up a substituted `VReg` in `subst`. -/
def substVReg (subst : List (VReg × VReg)) (v : VReg) : VReg :=
  match envGet subst v with
  | some v' => v'
  | none    => v

/-- Models `LegalizationArtifactCombiner::tryCombineUnmergeValues`
(`llvm/CodeGen/GlobalISel/LegalizationArtifactCombiner.h:1064-1270`): folds
`G_UNMERGE_VALUES` with its producer `G_MERGE_VALUES` and substitutes the
unmerged 64-bit virtual registers into subsequent instructions. -/
def combineArtifactsBody (merges : List (VReg × (VReg × VReg)))
    (subst : List (VReg × VReg)) :
    List AnMachineInstr → List AnMachineInstr × List (VReg × (VReg × VReg)) × List (VReg × VReg)
  | [] => ([], merges, subst)
  | inst :: rest =>
    match inst with
    | .G_MERGE_VALUES dst _ lo hi =>
      let lo' := substVReg subst lo
      let hi' := substVReg subst hi
      combineArtifactsBody (envSet merges dst (lo', hi')) subst rest
    | .G_UNMERGE_VALUES dstLo dstHi _ src =>
      match envGet merges (substVReg subst src) with
      | some (lo, hi) =>
        let subst' := envSet (envSet subst dstLo lo) dstHi hi
        combineArtifactsBody merges subst' rest
      | none =>
        let (rest', m', s') := combineArtifactsBody merges subst rest
        (.G_UNMERGE_VALUES dstLo dstHi .gpr (substVReg subst src) :: rest', m', s')
    | .G_UADDO dst vflagOut bank lhs rhs =>
      let i' := AnMachineInstr.G_UADDO dst vflagOut bank (substVReg subst lhs) (substVReg subst rhs)
      let (rest', m', s') := combineArtifactsBody merges subst rest
      (i' :: rest', m', s')
    | .G_UADDE dst vflagOut bank lhs rhs vflagIn =>
      let i' := AnMachineInstr.G_UADDE dst vflagOut bank
                  (substVReg subst lhs) (substVReg subst rhs) (substVReg subst vflagIn)
      let (rest', m', s') := combineArtifactsBody merges subst rest
      (i' :: rest', m', s')
    | .G_ADD dst bank ty lhs rhs =>
      let i' := AnMachineInstr.G_ADD dst bank ty (substVReg subst lhs) (substVReg subst rhs)
      let (rest', m', s') := combineArtifactsBody merges subst rest
      (i' :: rest', m', s')
    | .G_ZEXT8_TO_64 dst bank src =>
      let i' := AnMachineInstr.G_ZEXT8_TO_64 dst bank (substVReg subst src)
      let (rest', m', s') := combineArtifactsBody merges subst rest
      (i' :: rest', m', s')
    | .G_SHL_IMM dst bank ty src shift =>
      let i' := AnMachineInstr.G_SHL_IMM dst bank ty (substVReg subst src) shift
      let (rest', m', s') := combineArtifactsBody merges subst rest
      (i' :: rest', m', s')
    | .G_PTR_ADD dst bank base offset =>
      let i' := AnMachineInstr.G_PTR_ADD dst bank (substVReg subst base) (substVReg subst offset)
      let (rest', m', s') := combineArtifactsBody merges subst rest
      (i' :: rest', m', s')
    | .G_LOAD64 dst bank ptrReg =>
      let i' := AnMachineInstr.G_LOAD64 dst bank (substVReg subst ptrReg)
      let (rest', m', s') := combineArtifactsBody merges subst rest
      (i' :: rest', m', s')
    | .G_STORE64 valReg ptrReg =>
      let i' := AnMachineInstr.G_STORE64 (substVReg subst valReg) (substVReg subst ptrReg)
      let (rest', m', s') := combineArtifactsBody merges subst rest
      (i' :: rest', m', s')
    | .G_ICMP64 dst bank pred lhs rhs =>
      let i' := AnMachineInstr.G_ICMP64 dst bank pred (substVReg subst lhs) (substVReg subst rhs)
      let (rest', m', s') := combineArtifactsBody merges subst rest
      (i' :: rest', m', s')
    | .G_SELECT64 dst bank cond tVal fVal =>
      let i' := AnMachineInstr.G_SELECT64 dst bank (substVReg subst cond)
                  (substVReg subst tVal) (substVReg subst fVal)
      let (rest', m', s') := combineArtifactsBody merges subst rest
      (i' :: rest', m', s')
    | other =>
      let (rest', m', s') := combineArtifactsBody merges subst rest
      (other :: rest', m', s')

/-- Full `Legalizer` + `LegalizationArtifactCombiner` + `RegBankSelect` pass on
`MachineFunction`. -/
def legalizeMachineFunction (mf : MachineFunction) : MachineFunction :=
  let expanded := legalizeAndBankBody mf.body
  let (combinedBody, merges, subst) := combineArtifactsBody [] [] expanded
  let ret' := match mf.ret with
    | .G_RET128 src =>
      match envGet merges (substVReg subst src) with
      | some (lo, hi) => .RET_PAIR lo hi
      | none          => .G_RET128 (substVReg subst src)
    | .G_RET64 src => .RET_SINGLE (substVReg subst src)
    | .RET_PAIR lo hi => .RET_PAIR (substVReg subst lo) (substVReg subst hi)
    | .RET_SINGLE lo  => .RET_SINGLE (substVReg subst lo)
  { props := { mf.props with legalized := true, regBankSelected := true }
    body  := combinedBody
    ret   := ret' }

/-- Key arithmetic lemma: `2 ^ 3 = 8`, so `G_MUL_IMM idx 8` and
`G_SHL_IMM idx 3` produce the exact same 64-bit byte offset. -/
@[simp]
theorem two_pow_three_eq_eight : (2 ^ 3 : Nat) = 8 := rfl

/-- `add64WithCarry` produces a low 64-bit word that is already reduced modulo
`word64Mod`. -/
@[simp]
theorem add64WithCarry_fst_mod (a b : Nat) (cin : Bool) :
    (add64WithCarry a b cin).1 % word64Mod = (add64WithCarry a b cin).1 := by
  simp [add64WithCarry]

/-- `AbiQuery.getArg` is already reduced modulo `word64Mod`. -/
@[simp]
theorem getArg_mod_word64Mod (q : AbiQuery) (idx : Nat) :
    (q.getArg idx) % word64Mod = q.getArg idx := by
  cases idx with
  | zero => simp [AbiQuery.getArg]
  | succ n =>
    cases n with
    | zero => simp [AbiQuery.getArg]
    | succ n2 =>
      cases n2 with
      | zero => simp [AbiQuery.getArg]
      | succ n3 =>
        cases n3 with
        | zero => simp [AbiQuery.getArg]
        | succ n4 =>
          cases n4 with
          | zero => simp [AbiQuery.getArg]
          | succ _ => simp [AbiQuery.getArg]

/-- Any 8-bit value `a % word8Mod` is strictly less than `word64Mod`, so
`(a % word8Mod) % word64Mod = a % word8Mod`. -/
@[simp]
theorem mod_word8Mod_mod_word64Mod (a : Nat) :
    (a % word8Mod) % word64Mod = a % word8Mod := by
  have hLt8 : a % word8Mod < word8Mod := Nat.mod_lt a (by decide)
  have hLt64 : a % word8Mod < word64Mod :=
    Nat.lt_trans hLt8 (by decide : word8Mod < word64Mod)
  exact Nat.mod_eq_of_lt hLt64

/-- Pointwise equivalence of `legalizeMachineFunction` on `llvmAddU128AndU8`:
proves that splitting `s128` `G_ADD` into `G_UNMERGE_VALUES` + `G_UADDO` +
`G_UADDE` + `G_MERGE_VALUES` and running `LegalizationArtifactCombiner`
preserves exact 128-bit addition semantics. -/
theorem legalizer_addU128AndU8_eval_eq (q : AbiQuery) :
    evalMachineFunction (legalizeMachineFunction (irTranslatorPass llvmAddU128AndU8)) q =
      evalMachineFunction (irTranslatorPass llvmAddU128AndU8) q := by
  simp [llvmAddU128AndU8, irTranslatorPass, translateLlvmBody, translateLlvmInstr,
        translateLlvmRet, legalizeMachineFunction, legalizeAndBankBody,
        legalizeAndBankInstr, combineArtifactsBody, substVReg,
        evalMachineFunction, evalAnMachineBody, evalAnMachineInstr, envGet, envSet]

/-- Pointwise equivalence of `legalizeMachineFunction` on `llvmGepLoadSelect`. -/
theorem legalizer_gepLoadSelect_eval_eq (q : AbiQuery) :
    evalMachineFunction (legalizeMachineFunction (irTranslatorPass llvmGepLoadSelect)) q =
      evalMachineFunction (irTranslatorPass llvmGepLoadSelect) q := by
  simp only [llvmGepLoadSelect, irTranslatorPass, translateLlvmBody,
             translateLlvmInstr, translateLlvmRet, legalizeMachineFunction,
             legalizeAndBankBody, legalizeAndBankInstr, combineArtifactsBody,
             substVReg, List.cons_append, List.nil_append, evalMachineFunction,
             evalAnMachineBody, evalAnMachineInstr, envGet, envSet,
             two_pow_three_eq_eight]

/-- Stage 2 (`Legalizer` + `RegBankSelect`) `Compiles` theorem on
`llvmAddU128AndU8` and `llvmGepLoadSelect`. -/
theorem legalizer_s128_and_s8_compiles :
    Compiles AnMachineLang AnMachineLang machineIdCodec
      (irTranslatorPass llvmAddU128AndU8)
      (legalizeMachineFunction (irTranslatorPass llvmAddU128AndU8)) ∧
    Compiles AnMachineLang AnMachineLang machineIdCodec
      (irTranslatorPass llvmGepLoadSelect)
      (legalizeMachineFunction (irTranslatorPass llvmGepLoadSelect)) := by
  constructor
  · apply compiles_of_eval_eq
    intro q res h
    rw [legalizer_addU128AndU8_eval_eq]
    exact h
  · apply compiles_of_eval_eq
    intro q res h
    rw [legalizer_gepLoadSelect_eval_eq]
    exact h

/-!
## Section 7: Stage 3 — `InstructionSelect` (`AnMachineLang -> AnMachineLang`)

In LLVM's `GlobalISel`, `InstructionSelect`
(`llvm/CodeGen/GlobalISel/InstructionSelector.h` and `GIMatchTableExecutor.h`)
executes TableGen-generated pattern matchers over the legalized, bank-selected
`MachineFunction`:
- Multi-instruction addressing-mode pattern (`GIM_RecordInsn` + `GIM_CheckOpcode`):
  rewrites `G_SHL_IMM offReg .gpr .s64 idx shift` followed by
  `G_PTR_ADD dst .gpr base offReg` into a single `ADD_SHIFTED_PTR dst base idx shift`.
- Carry-chain patterns:
  rewrites `G_UADDO dst vflag .gpr lhs rhs` into `ADD64_FLAGS dst vflag lhs rhs`,
  and `G_UADDE dst vflagOut .gpr lhs rhs vflagIn` into
  `ADDC64_FLAGS dst vflagOut lhs rhs vflagIn`.
- Compare-and-select patterns:
  rewrites `G_ICMP64 vflag .flag pred lhs rhs` into
  `CMP64_FLAGS vflag pred lhs rhs`, and `G_SELECT64 dst .gpr vflag tVal fVal`
  into `CSEL64 dst vflag tVal fVal`.
-/

/-- Single-instruction TableGen selection rule. -/
def selectSingleInstr : AnMachineInstr → AnMachineInstr
  | .G_CONSTANT dst _ .s64 imm           => .MOV_IMM64 dst imm
  | .G_ADD dst _ .s64 lhs rhs            => .ADD64 dst lhs rhs
  | .G_ADD dst _ .s8 lhs rhs             => .ADD8_MASK dst lhs rhs
  | .G_ZEXT8_TO_64 dst _ src             => .ZEXT8_TO_64 dst src
  | .G_UADDO dst vflag _ lhs rhs         => .ADD64_FLAGS dst vflag lhs rhs
  | .G_UADDE dst vflagOut _ lhs rhs vfIn => .ADDC64_FLAGS dst vflagOut lhs rhs vfIn
  | .G_LOAD64 dst _ ptrReg               => .LDR64 dst ptrReg
  | .G_STORE64 valReg ptrReg             => .STR64 valReg ptrReg
  | .G_ICMP64 vflag _ pred lhs rhs       => .CMP64_FLAGS vflag pred lhs rhs
  | .G_SELECT64 dst _ cond tVal fVal     => .CSEL64 dst cond tVal fVal
  | other                                => other

/-- Peephole / tree pattern matcher modeling `GIMatchTableExecutor`: matches
adjacent `(G_SHL_IMM off idx shift, G_PTR_ADD dst base off)` into a single
`ADD_SHIFTED_PTR dst base idx shift` instruction via primitive structural
recursion with a 1-instruction lookahead buffer `prevShl`. -/
def selectBodyAux (prevShl : Option (VReg × VReg × Nat)) :
    List AnMachineInstr → List AnMachineInstr
  | [] =>
    match prevShl with
    | none => []
    | some (offReg, idx, shift) => [ .G_SHL_IMM offReg .gpr .s64 idx shift ]
  | inst :: rest =>
    match prevShl with
    | none =>
      match inst with
      | .G_SHL_IMM offReg _ _ idx shift =>
        selectBodyAux (some (offReg, idx, shift)) rest
      | other =>
        selectSingleInstr other :: selectBodyAux none rest
    | some (offReg, idx, shift) =>
      match inst with
      | .G_PTR_ADD dst _ base offReg' =>
        if offReg == offReg' then
          .ADD_SHIFTED_PTR dst base idx shift :: selectBodyAux none rest
        else
          .G_SHL_IMM offReg .gpr .s64 idx shift ::
          .G_PTR_ADD dst .gpr base offReg' ::
          selectBodyAux none rest
      | .G_SHL_IMM offReg2 _ _ idx2 shift2 =>
        .G_SHL_IMM offReg .gpr .s64 idx shift ::
        selectBodyAux (some (offReg2, idx2, shift2)) rest
      | other =>
        .G_SHL_IMM offReg .gpr .s64 idx shift ::
        selectSingleInstr other ::
        selectBodyAux none rest

def selectBody (body : List AnMachineInstr) : List AnMachineInstr :=
  selectBodyAux none body

/-- Full `InstructionSelect` pass on `MachineFunction`. -/
def instructionSelectPass (mf : MachineFunction) : MachineFunction := {
  props := { mf.props with selected := true }
  body  := selectBody mf.body
  ret   := mf.ret
}

/-- Mirrors `llvm::isPreISelGenericOpcode` (`llvm/CodeGen/TargetOpcodes.h:34-38`):
checks that an `AnMachineInstr` is a selected target instruction (`TargetOpcode`
or ABI entry pseudo) and not a pre-ISel `G_*` generic opcode. -/
def isSelectedTargetInstr : AnMachineInstr → Bool
  | .COPY_FROM_ABI_GPR _ _ _ _ => true
  | .MOV_IMM64 _ _             => true
  | .ADD64 _ _ _               => true
  | .ADD8_MASK _ _ _           => true
  | .ZEXT8_TO_64 _ _           => true
  | .ADD64_FLAGS _ _ _ _       => true
  | .ADDC64_FLAGS _ _ _ _ _    => true
  | .ADD_SHIFTED_PTR _ _ _ _   => true
  | .LDR64 _ _                 => true
  | .STR64 _ _                 => true
  | .CMP64_FLAGS _ _ _ _       => true
  | .CSEL64 _ _ _ _            => true
  | _                          => false

/-- Mirrors `MachineVerifier`'s check for `MachineFunctionProperties::Property::Selected`:
every instruction in `mf.body` satisfies `isSelectedTargetInstr`. -/
def isFullySelected (mf : MachineFunction) : Bool :=
  mf.props.selected && mf.body.all isSelectedTargetInstr

/-- Pointwise equivalence of `instructionSelectPass` on the legalized
`llvmAddU128AndU8` `MachineFunction`. -/
theorem instructionSelect_addU128AndU8_eval_eq (q : AbiQuery) :
    evalMachineFunction
      (instructionSelectPass (legalizeMachineFunction (irTranslatorPass llvmAddU128AndU8))) q =
    evalMachineFunction
      (legalizeMachineFunction (irTranslatorPass llvmAddU128AndU8)) q := by
  have hSel :
      instructionSelectPass (legalizeMachineFunction (irTranslatorPass llvmAddU128AndU8)) =
      { props := { isSSA := true, legalized := true, regBankSelected := true,
                   selected := true, noVRegs := false },
        body := [
          .COPY_FROM_ABI_GPR 1000 .gpr .s64 0,
          .COPY_FROM_ABI_GPR 2000 .gpr .s64 1,
          .COPY_FROM_ABI_GPR 1001 .gpr .s64 2,
          .COPY_FROM_ABI_GPR 2001 .gpr .s64 3,
          .COPY_FROM_ABI_GPR 2 .gpr .s8 4,
          .COPY_FROM_ABI_GPR 3 .gpr .s8 5,
          .ADD64_FLAGS 4410 4610 1000 1001,
          .ADDC64_FLAGS 4510 4710 2000 2001 4610,
          .ADD8_MASK 11 2 3,
          .ZEXT8_TO_64 12 11,
          .MOV_IMM64 4813 0,
          .ADD64_FLAGS 4414 4614 4410 12,
          .ADDC64_FLAGS 4514 4714 4510 4813 4614
        ],
        ret := .RET_PAIR 4414 4514 } := rfl
  rw [hSel]
  simp [llvmAddU128AndU8, irTranslatorPass, translateLlvmBody, translateLlvmInstr,
        translateLlvmRet, legalizeMachineFunction, legalizeAndBankBody,
        legalizeAndBankInstr, combineArtifactsBody, substVReg,
        evalMachineFunction, evalAnMachineBody, evalAnMachineInstr, envGet, envSet]

/-- Pointwise equivalence of `instructionSelectPass` on the legalized
`llvmGepLoadSelect` `MachineFunction` (including the TableGen addressing-mode
pattern `G_PTR_ADD(base, G_SHL_IMM(idx, 3)) -> ADD_SHIFTED_PTR`). -/
theorem instructionSelect_gepLoadSelect_eval_eq (q : AbiQuery) :
    evalMachineFunction
      (instructionSelectPass (legalizeMachineFunction (irTranslatorPass llvmGepLoadSelect))) q =
    evalMachineFunction
      (legalizeMachineFunction (irTranslatorPass llvmGepLoadSelect)) q := by
  have hSel :
      instructionSelectPass (legalizeMachineFunction (irTranslatorPass llvmGepLoadSelect)) =
      { props := { isSSA := true, legalized := true, regBankSelected := true,
                   selected := true, noVRegs := false },
        body := [
          .COPY_FROM_ABI_GPR 0 .gpr .p0 0,
          .COPY_FROM_ABI_GPR 1 .gpr .s64 1,
          .COPY_FROM_ABI_GPR 3 .gpr .s64 3,
          .ADD_SHIFTED_PTR 7 0 1 3,
          .LDR64 9 7,
          .CMP64_FLAGS 10 .ugt 9 3,
          .CSEL64 11 10 9 3
        ],
        ret := .RET_SINGLE 11 } := rfl
  rw [hSel]
  simp [llvmGepLoadSelect, irTranslatorPass, translateLlvmBody,
        translateLlvmInstr, translateLlvmRet, legalizeMachineFunction,
        legalizeAndBankBody, legalizeAndBankInstr, combineArtifactsBody,
        substVReg, evalMachineFunction, evalAnMachineBody,
        evalAnMachineInstr, envGet, envSet]
  cases heapLoad q.heap (q.getArg 0 + q.getArg 1 * 8 % word64Mod / 8) <;> rfl

/-- Stage 3 (`InstructionSelect`) `Compiles` theorem on both benchmark programs. -/
theorem instructionSelect_compiles :
    Compiles AnMachineLang AnMachineLang machineIdCodec
      (legalizeMachineFunction (irTranslatorPass llvmAddU128AndU8))
      (instructionSelectPass (legalizeMachineFunction (irTranslatorPass llvmAddU128AndU8))) ∧
    Compiles AnMachineLang AnMachineLang machineIdCodec
      (legalizeMachineFunction (irTranslatorPass llvmGepLoadSelect))
      (instructionSelectPass (legalizeMachineFunction (irTranslatorPass llvmGepLoadSelect))) := by
  constructor
  · apply compiles_of_eval_eq
    intro q res h
    rw [instructionSelect_addU128AndU8_eval_eq]
    exact h
  · apply compiles_of_eval_eq
    intro q res h
    rw [instructionSelect_gepLoadSelect_eval_eq]
    exact h

/-- Complete 3-stage `GlobalISel` front-to-back SSA pipeline
(`IRTranslator -> Legalizer/ArtifactCombiner/RegBankSelect -> InstructionSelect`)
composed on `AnMachineIR`. -/
def globalISelPass (p : AnLlvmProg) : MachineFunction :=
  instructionSelectPass (legalizeMachineFunction (irTranslatorPass p))

/-- Both benchmark functions exit `globalISelPass` with `isFullySelected = true`
(zero remaining `G_*` generic instructions). -/
theorem globalISelPass_fullySelected :
    isFullySelected (globalISelPass llvmAddU128AndU8) = true ∧
    isFullySelected (globalISelPass llvmGepLoadSelect) = true := by
  exact ⟨rfl, rfl⟩

/-- Constructive `GlobalISel` pass compiler over the supported `AnLLVM` corpus. -/
def compileGlobalISel (p : AnLlvmProg) : Option MachineFunction :=
  if p = llvmAddU128AndU8 then
    some (globalISelPass llvmAddU128AndU8)
  else if p = llvmGepLoadSelect then
    some (globalISelPass llvmGepLoadSelect)
  else
    none

/-- `BB-8` `PassCompiler` for the entire `GlobalISel` (`AnLlvmLang ->
AnMachineLang`) pipeline. -/
def globalISelCompiler : PassCompiler AnLlvmLang AnMachineLang llvmToMachineCodec where
  compile := compileGlobalISel
  sound s t h := by
    unfold compileGlobalISel at h
    split at h
    · rename_i hEq
      subst hEq
      injection h with hT
      subst hT
      apply compiles_of_eval_eq
      intro q res hEval
      rw [globalISelPass, instructionSelect_addU128AndU8_eval_eq,
          legalizer_addU128AndU8_eval_eq, irTranslator_addU128AndU8_eval_eq]
      exact hEval
    · split at h
      · rename_i _ hEq
        subst hEq
        injection h with hT
        subst hT
        apply compiles_of_eval_eq
        intro q res hEval
        rw [globalISelPass, instructionSelect_gepLoadSelect_eval_eq,
            legalizer_gepLoadSelect_eval_eq, irTranslator_gepLoadSelect_eval_eq]
        exact hEval
      · contradiction

/-!
## Section 8: Stage 4 — `PostRA MachineIR` and the Unified `RegAlloc + Flag Liveness` Symbolic Checker

Between `InstructionSelect` (`MachineSSA`) and `PrologEpilogInserter` (`PostRA
MachineIR`), `llc -O2` executes `PHIElimination`, `TwoAddressInstructionPass`,
`RegisterCoalescer`, `MachineScheduler`, `RegAllocGreedy`, and `VirtRegRewriter`.

Rather than verifying those heuristic passes constructively, we validate the
entire transition from `MachineSSA` to `PostRA MachineIR` in **one single hop**
using a forward symbolic certificate checker (`checkPostRaMachine`) that checks:
1. Every physical GPR (`PhysReg`) and stack spill slot (`SpillSlot`) holds the
   value of its tracked `MachineSSA` virtual register `v : VReg`, and
2. Whenever an instruction relies on the hardware condition-code register
   (`physFlag : Bool`, modeling `NZCV`/`EFLAGS`), `physFlag` still holds the
   exact `MachineSSA` flag virtual register `vflag : VReg` and has **not** been
   clobbered by an intervening flag-modifying instruction (such as x86
   `MOV32r0` / `XOR_ZERO_CLOBBER`).
-/

/-- Physical general-purpose registers (`r0`..`r7`). -/
inductive PhysReg where
  | r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7
  deriving DecidableEq, Repr

/-- Abstract stack frame spill slot index (`MO_FrameIndex` in
`llvm/CodeGen/MachineOperand.h:56`). -/
abbrev SpillSlot := Nat

/-- Physical machine instructions after `VirtRegRewriter` (`NoPHIs, NoVRegs`). -/
inductive PostRaInstr where
  | MOV_ABI_ARG       (dst : PhysReg) (ty : LowLevelType) (argIdx : Nat)
  | MOV_REG           (dst src : PhysReg)
  | MOV_IMM64         (dst : PhysReg) (imm : Nat)
  /-- Models x86 `MOV32r0` (`xor eax, eax`), which materializes `0` into `dst`
      but **clobbers `EFLAGS` (`physFlag := some false`)**! -/
  | XOR_ZERO_CLOBBER  (dst : PhysReg)
  | SPILL_STORE       (slot : SpillSlot) (src : PhysReg)
  | SPILL_RELOAD      (dst : PhysReg) (slot : SpillSlot)
  | ADD64_NOFLAGS     (dst lhs rhs : PhysReg)
  | ADD8_NOFLAGS      (dst lhs rhs : PhysReg)
  | ZEXT8_TO_64       (dst src : PhysReg)
  | ADD64_SET_FLAGS   (dst lhs rhs : PhysReg)
  | ADDC64_USE_FLAGS  (dst lhs rhs : PhysReg)
  | ADD_SHIFTED_PTR   (dst base idx : PhysReg) (shift : Nat)
  | LDR64             (dst ptrReg : PhysReg)
  | STR64             (valReg ptrReg : PhysReg)
  | CMP64_SET_FLAGS   (pred : IntPred) (lhs rhs : PhysReg)
  | CSEL64_USE_FLAGS  (dst tVal fVal : PhysReg)
  deriving DecidableEq, Repr

/-- Return convention of `PostRaMachineProg`. -/
inductive PostRaRet where
  | RET_PAIR   (loReg hiReg : PhysReg)
  | RET_SINGLE (loReg : PhysReg)
  deriving DecidableEq, Repr

/-- A `PostRA MachineIR` function (`NoPHIs, NoVRegs`). -/
structure PostRaMachineProg where
  numSpillSlots : Nat
  body          : List PostRaInstr
  ret           : PostRaRet
  deriving DecidableEq, Repr

/-- Concrete execution state of `PostRaMachineProg`. -/
structure PostRaState where
  regs     : PhysReg → Option MVal
  spills   : SpillSlot → Option MVal
  physFlag : Option Bool
  heap     : List Nat

def regSet (regs : PhysReg → Option MVal) (r : PhysReg) (v : MVal) :
    PhysReg → Option MVal :=
  fun r' => if r' = r then some v else regs r'

def spillSet (spills : SpillSlot → Option MVal) (s : SpillSlot) (v : MVal) :
    SpillSlot → Option MVal :=
  fun s' => if s' = s then some v else spills s'

/-- Evaluates a single `PostRaInstr`. Notice how `XOR_ZERO_CLOBBER` sets
`physFlag := some false` (clobbering any live carry flag in `EFLAGS`/`NZCV`). -/
def evalPostRaInstr (q : AbiQuery) (st : PostRaState) (inst : PostRaInstr) :
    Option PostRaState :=
  match inst with
  | .MOV_ABI_ARG dst ty argIdx =>
    let raw := q.getArg argIdx
    let v := match ty with
      | .s1   => MVal.v1 (decide (raw % 2 = 1))
      | .s8   => MVal.v8 (raw % word8Mod)
      | .s32  => MVal.v32 (raw % word32Mod)
      | .s64  => MVal.v64 raw
      | .s128 => MVal.v128 raw 0
      | .p0   => MVal.ptr raw
    some { st with regs := regSet st.regs dst v }
  | .MOV_REG dst src =>
    match st.regs src with
    | some v => some { st with regs := regSet st.regs dst v }
    | none => none
  | .MOV_IMM64 dst imm =>
    some { st with regs := regSet st.regs dst (.v64 (imm % word64Mod)) }
  | .XOR_ZERO_CLOBBER dst =>
    some { st with
      regs     := regSet st.regs dst (.v64 0)
      physFlag := some false }
  | .SPILL_STORE slot src =>
    match st.regs src with
    | some v => some { st with spills := spillSet st.spills slot v }
    | none => none
  | .SPILL_RELOAD dst slot =>
    match st.spills slot with
    | some v => some { st with regs := regSet st.regs dst v }
    | none => none
  | .ADD64_NOFLAGS dst lhs rhs =>
    match st.regs lhs, st.regs rhs with
    | some (.v64 a), some (.v64 b) =>
      let (lo, _) := add64WithCarry a b false
      some { st with regs := regSet st.regs dst (.v64 lo) }
    | _, _ => none
  | .ADD8_NOFLAGS dst lhs rhs =>
    match st.regs lhs, st.regs rhs with
    | some (.v8 a), some (.v8 b) =>
      some { st with regs := regSet st.regs dst (.v8 ((a + b) % word8Mod)) }
    | _, _ => none
  | .ZEXT8_TO_64 dst src =>
    match st.regs src with
    | some (.v8 a) =>
      some { st with regs := regSet st.regs dst (.v64 (a % word8Mod)) }
    | _ => none
  | .ADD64_SET_FLAGS dst lhs rhs =>
    match st.regs lhs, st.regs rhs with
    | some (.v64 a), some (.v64 b) =>
      let (lo, carry) := add64WithCarry a b false
      some { st with
        regs     := regSet st.regs dst (.v64 lo)
        physFlag := some carry }
    | _, _ => none
  | .ADDC64_USE_FLAGS dst lhs rhs =>
    match st.regs lhs, st.regs rhs, st.physFlag with
    | some (.v64 a), some (.v64 b), some cin =>
      let (lo, carry) := add64WithCarry a b cin
      some { st with
        regs     := regSet st.regs dst (.v64 lo)
        physFlag := some carry }
    | _, _, _ => none
  | .ADD_SHIFTED_PTR dst base idx shift =>
    match st.regs base, st.regs idx with
    | some (.ptr b), some (.v64 i) =>
      let byteOff := (i * (2 ^ shift)) % word64Mod
      some { st with regs := regSet st.regs dst (.ptr (b + byteOff / 8)) }
    | _, _ => none
  | .LDR64 dst ptrReg =>
    match st.regs ptrReg with
    | some (.ptr idx) =>
      match heapLoad st.heap idx with
      | some v => some { st with regs := regSet st.regs dst (.v64 (v % word64Mod)) }
      | none => none
    | _ => none
  | .STR64 valReg ptrReg =>
    match st.regs valReg, st.regs ptrReg with
    | some (.v64 v), some (.ptr idx) =>
      match heapStore st.heap idx v with
      | some heap' => some { st with heap := heap' }
      | none => none
    | _, _ => none
  | .CMP64_SET_FLAGS pred lhs rhs =>
    match st.regs lhs, st.regs rhs with
    | some (.v64 a), some (.v64 b) =>
      some { st with physFlag := some (pred.eval a b) }
    | _, _ => none
  | .CSEL64_USE_FLAGS dst tVal fVal =>
    match st.physFlag, st.regs tVal, st.regs fVal with
    | some c, some (.v64 tv), some (.v64 fv) =>
      some { st with regs := regSet st.regs dst (.v64 (if c then tv else fv)) }
    | _, _, _ => none

/-- Evaluates a sequence of `PostRaInstr`s. -/
def evalPostRaBody (q : AbiQuery) (st : PostRaState) :
    List PostRaInstr → Option PostRaState
  | [] => some st
  | i :: rest =>
    match evalPostRaInstr q st i with
    | some st' => evalPostRaBody q st' rest
    | none => none

/-- Initial `PostRaState` on function entry. -/
def initPostRaState (q : AbiQuery) : PostRaState := {
  regs     := fun _ => none
  spills   := fun _ => none
  physFlag := none
  heap     := q.heap
}

/-- Evaluates a `PostRaMachineProg` on an `AbiQuery`. -/
def evalPostRaProg (p : PostRaMachineProg) (q : AbiQuery) : Option AbiOut :=
  match evalPostRaBody q (initPostRaState q) p.body with
  | none => none
  | some st =>
    match p.ret with
    | .RET_PAIR loReg hiReg =>
      match st.regs loReg, st.regs hiReg with
      | some (.v64 lo), some (.v64 hi) =>
        some { retLo := lo, retHi := hi, heap := st.heap, calleeSaved := q.calleeSaved }
      | _, _ => none
    | .RET_SINGLE loReg =>
      match st.regs loReg with
      | some (.v64 lo) =>
        some { retLo := lo, retHi := 0, heap := st.heap, calleeSaved := q.calleeSaved }
      | _ => none

/-- `PostRaMachineLang` packaged as an Anneal `Language AbiOut`. -/
abbrev PostRaMachineLang : Language AbiOut :=
  Language.mkSimple PostRaMachineProg AbiQuery AbiOut
    (fun p => Behavior.ofOption (evalPostRaProg p))

/-- Identity codec between `AnMachineLang` and `PostRaMachineLang`. -/
def machineToPostRaCodec : BehaviorCodec AnMachineLang PostRaMachineLang :=
  mkSimpleCodec (fun mf => Behavior.ofOption (evalMachineFunction mf))
                (fun p => Behavior.ofOption (evalPostRaProg p))

/-!
### Forward Symbolic Register-Allocation and Flag-Liveness Checker

We now define the forward symbolic state `SymRegState` tracking:
- `physToVReg : PhysReg → Option VReg` (which `MachineSSA` virtual register is
  currently held in each physical GPR),
- `spillToVReg : SpillSlot → Option VReg` (which `MachineSSA` virtual register
  is currently stored in each stack spill slot), and
- `flagVReg : Option VReg` (which `MachineSSA` flag virtual register `vflag` is
  currently live in `NZCV`/`EFLAGS`).

Whenever an `AnMachineInstr` defines a virtual register `vDst`,
`symInvalidateVReg` first clears any stale binding to `vDst` across
`physToVReg`, `spillToVReg`, and `flagVReg` before binding the destination
physical register or flag. This guarantees that the simulation invariant
`SymStateRel` holds unconditionally for **any** `MachineFunction` `mf` and
`PostRaMachineProg` `post`.
-/

structure SymRegState where
  physToVReg  : PhysReg → Option VReg
  spillToVReg : SpillSlot → Option VReg
  flagVReg    : Option VReg

def initSymRegState : SymRegState := {
  physToVReg  := fun _ => none
  spillToVReg := fun _ => none
  flagVReg    := none
}

/-- Invalidates any previous physical register, spill slot, or flag mapping to
`vDead` when `vDead` is (re-)defined in `MachineSSA`. -/
def symInvalidateVReg (sym : SymRegState) (vDead : VReg) : SymRegState where
  physToVReg r :=
    match sym.physToVReg r with
    | some v => if v = vDead then none else some v
    | none   => none
  spillToVReg s :=
    match sym.spillToVReg s with
    | some v => if v = vDead then none else some v
    | none   => none
  flagVReg :=
    match sym.flagVReg with
    | some v => if v = vDead then none else some v
    | none   => none

/-- Updates `sym` when a `MachineSSA` instruction defines `vDst` in physical
register `dst`. -/
def symSetPhys (sym : SymRegState) (dst : PhysReg) (vDst : VReg) : SymRegState :=
  let s := symInvalidateVReg sym vDst
  { s with physToVReg := fun r => if r = dst then some vDst else s.physToVReg r }

/-- Updates `sym` when a `MachineSSA` instruction defines `vFlagOut` in the
hardware flag register `NZCV`/`EFLAGS`. -/
def symSetFlag (sym : SymRegState) (vFlagOut : VReg) : SymRegState :=
  let s := symInvalidateVReg sym vFlagOut
  { s with flagVReg := some vFlagOut }

/-- Updates `sym` when a `MachineSSA` instruction defines both `vDst` in `dst`
and `vFlagOut` in the hardware flag register. -/
def symSetPhysAndFlag (sym : SymRegState) (dst : PhysReg) (vDst vFlagOut : VReg) :
    SymRegState :=
  symSetFlag (symSetPhys sym dst vDst) vFlagOut

/-- Updates `sym` for a housekeeping physical copy (`MOV_REG` or `SPILL_RELOAD`)
that copies an already-defined `v` into `dst` without modifying `MachineSSA`
`env`. -/
def symCopyToPhys (sym : SymRegState) (dst : PhysReg) (v : VReg) : SymRegState :=
  { sym with physToVReg := fun r => if r = dst then some v else sym.physToVReg r }

/-- Updates `sym` for a housekeeping spill store (`SPILL_STORE slot src`) that
copies an already-defined `v` into `slot` without modifying `MachineSSA` `env`. -/
def symCopyToSpill (sym : SymRegState) (slot : SpillSlot) (v : VReg) : SymRegState :=
  { sym with spillToVReg := fun s => if s = slot then some v else sym.spillToVReg s }

/-- Symbolic step classification: either a housekeeping move/spill/reload
(`.housekeep sym'`) or a matched `MachineSSA` instruction (`.matched sym'`). -/
inductive SymStepResult where
  | housekeep (sym' : SymRegState)
  | matched   (sym' : SymRegState)

def stepSymRegAlloc (sym : SymRegState) (mi? : Option AnMachineInstr)
    (pi : PostRaInstr) : Option SymStepResult :=
  match pi with
  | .MOV_REG dst src =>
    match sym.physToVReg src with
    | some v => some (.housekeep (symCopyToPhys sym dst v))
    | none   => none
  | .SPILL_STORE slot src =>
    match sym.physToVReg src with
    | some v => some (.housekeep (symCopyToSpill sym slot v))
    | none   => none
  | .SPILL_RELOAD dst slot =>
    match sym.spillToVReg slot with
    | some v => some (.housekeep (symCopyToPhys sym dst v))
    | none   => none
  | .MOV_ABI_ARG dst ty argIdx =>
    match mi? with
    | some (.COPY_FROM_ABI_GPR vDst _ vTy vArgIdx) =>
      if ty = vTy && argIdx = vArgIdx then
        some (.matched (symSetPhys sym dst vDst))
      else none
    | _ => none
  | .MOV_IMM64 dst imm =>
    match mi? with
    | some (.MOV_IMM64 vDst vImm) =>
      if imm = vImm then
        some (.matched (symSetPhys sym dst vDst))
      else none
    | _ => none
  | .XOR_ZERO_CLOBBER dst =>
    match mi? with
    | some (.MOV_IMM64 vDst 0) =>
      -- `XOR_ZERO_CLOBBER` (`MOV32r0` / `xor eax, eax`) materializes `0` into
      -- `dst`, but clobbers `EFLAGS` (`flagVReg := none`)!
      some (.matched { (symSetPhys sym dst vDst) with flagVReg := none })
    | _ => none
  | .ADD64_NOFLAGS dst lhs rhs =>
    match mi? with
    | some (.ADD64 vDst vLhs vRhs) =>
      if sym.physToVReg lhs = some vLhs && sym.physToVReg rhs = some vRhs then
        some (.matched (symSetPhys sym dst vDst))
      else none
    | _ => none
  | .ADD8_NOFLAGS dst lhs rhs =>
    match mi? with
    | some (.ADD8_MASK vDst vLhs vRhs) =>
      if sym.physToVReg lhs = some vLhs && sym.physToVReg rhs = some vRhs then
        some (.matched (symSetPhys sym dst vDst))
      else none
    | _ => none
  | .ZEXT8_TO_64 dst src =>
    match mi? with
    | some (.ZEXT8_TO_64 vDst vSrc) =>
      if sym.physToVReg src = some vSrc then
        some (.matched (symSetPhys sym dst vDst))
      else none
    | _ => none
  | .ADD64_SET_FLAGS dst lhs rhs =>
    match mi? with
    | some (.ADD64_FLAGS vDst vFlagOut vLhs vRhs) =>
      if sym.physToVReg lhs = some vLhs && sym.physToVReg rhs = some vRhs then
        some (.matched (symSetPhysAndFlag sym dst vDst vFlagOut))
      else none
    | _ => none
  | .ADDC64_USE_FLAGS dst lhs rhs =>
    match mi? with
    | some (.ADDC64_FLAGS vDst vFlagOut vLhs vRhs vFlagIn) =>
      if sym.physToVReg lhs = some vLhs &&
         sym.physToVReg rhs = some vRhs &&
         sym.flagVReg = some vFlagIn then
        some (.matched (symSetPhysAndFlag sym dst vDst vFlagOut))
      else none
    | _ => none
  | .ADD_SHIFTED_PTR dst base idx shift =>
    match mi? with
    | some (.ADD_SHIFTED_PTR vDst vBase vIdx vShift) =>
      if sym.physToVReg base = some vBase &&
         sym.physToVReg idx = some vIdx &&
         shift = vShift then
        some (.matched (symSetPhys sym dst vDst))
      else none
    | _ => none
  | .LDR64 dst ptrReg =>
    match mi? with
    | some (.LDR64 vDst vPtr) =>
      if sym.physToVReg ptrReg = some vPtr then
        some (.matched (symSetPhys sym dst vDst))
      else none
    | _ => none
  | .STR64 valReg ptrReg =>
    match mi? with
    | some (.STR64 vVal vPtr) =>
      if sym.physToVReg valReg = some vVal && sym.physToVReg ptrReg = some vPtr then
        some (.matched sym)
      else none
    | _ => none
  | .CMP64_SET_FLAGS pred lhs rhs =>
    match mi? with
    | some (.CMP64_FLAGS vFlagOut vPred vLhs vRhs) =>
      if pred = vPred &&
         sym.physToVReg lhs = some vLhs &&
         sym.physToVReg rhs = some vRhs then
        some (.matched (symSetFlag sym vFlagOut))
      else none
    | _ => none
  | .CSEL64_USE_FLAGS dst tVal fVal =>
    match mi? with
    | some (.CSEL64 vDst vFlagIn vTVal vFVal) =>
      if sym.flagVReg = some vFlagIn &&
         sym.physToVReg tVal = some vTVal &&
         sym.physToVReg fVal = some vFVal then
        some (.matched (symSetPhys sym dst vDst))
      else none
    | _ => none

/-- Runs the symbolic checker over the `PostRaInstr` body against the remaining
`AnMachineInstr` list. -/
def checkPostRaBody (sym : SymRegState) (ssaBody : List AnMachineInstr) :
    List PostRaInstr → Option (SymRegState × List AnMachineInstr)
  | [] => some (sym, ssaBody)
  | pi :: rest =>
    match stepSymRegAlloc sym ssaBody.head? pi with
    | some (.housekeep sym') => checkPostRaBody sym' ssaBody rest
    | some (.matched sym')   => checkPostRaBody sym' ssaBody.tail rest
    | none                   => none

/-- Full boolean certificate checker `checkPostRaMachine` validating a
`PostRaMachineProg` against a selected `MachineFunction`. -/
def checkPostRaMachine (mf : MachineFunction) (post : PostRaMachineProg) : Bool :=
  match checkPostRaBody initSymRegState mf.body post.body with
  | some (sym, []) =>
    match mf.ret, post.ret with
    | .RET_PAIR vLo vHi, .RET_PAIR pLo pHi =>
      decide (sym.physToVReg pLo = some vLo ∧ sym.physToVReg pHi = some vHi)
    | .RET_SINGLE vLo, .RET_SINGLE pLo =>
      decide (sym.physToVReg pLo = some vLo)
    | _, _ => false
  | _ => false

/-!
### Simulation Invariant and General Soundness of `checkPostRaMachine`

We now prove that for **any** `MachineFunction` `mf` and **any**
`PostRaMachineProg` `post` (universally quantified over all programs), if
`checkPostRaMachine mf post = true`, then `post` refines `mf`
(`Compiles AnMachineLang PostRaMachineLang machineToPostRaCodec mf post`).
-/

/-- Simulation relation between the `MachineSSA` state `(env, heap)` and the
`PostRA` physical state `st` under symbolic map `sym`. -/
structure SymStateRel (sym : SymRegState) (env : VRegEnv) (heap : List Nat)
    (st : PostRaState) : Prop where
  heap_eq  : st.heap = heap
  phys_ok  : ∀ r v, sym.physToVReg r = some v →
               ∃ val, envGet env v = some val ∧ st.regs r = some val
  spill_ok : ∀ s v, sym.spillToVReg s = some v →
               ∃ val, envGet env v = some val ∧ st.spills s = some val
  flag_ok  : ∀ vf, sym.flagVReg = some vf →
               ∃ b, envGet env vf = some (.v1 b) ∧ st.physFlag = some b

theorem initSymStateRel (q : AbiQuery) :
    SymStateRel initSymRegState [] q.heap (initPostRaState q) where
  heap_eq  := rfl
  phys_ok  := by intro r v h; contradiction
  spill_ok := by intro s v h; contradiction
  flag_ok  := by intro vf h; contradiction

/-- `symInvalidateVReg` preserves `SymStateRel` when `vDead` is updated in `env`
to `val` without yet modifying `st`. -/
theorem symStateRel_invalidate {sym : SymRegState} {env : VRegEnv}
    {heap : List Nat} {st : PostRaState}
    (hRel : SymStateRel sym env heap st) (vDead : VReg) (val : MVal) :
    SymStateRel (symInvalidateVReg sym vDead) (envSet env vDead val) heap st where
  heap_eq := hRel.heap_eq
  phys_ok := by
    intro r v h
    simp only [symInvalidateVReg] at h
    cases hOld : sym.physToVReg r with
    | none => simp [hOld] at h
    | some v0 =>
      simp only [hOld] at h
      split at h
      · contradiction
      · rename_i hNe
        injection h with hEq
        subst hEq
        obtain ⟨val0, hEnv0, hReg0⟩ := hRel.phys_ok r v0 hOld
        exact ⟨val0, by rw [envGet_envSet_ne _ _ _ _ (Ne.symm hNe)]; exact hEnv0, hReg0⟩
  spill_ok := by
    intro s v h
    simp only [symInvalidateVReg] at h
    cases hOld : sym.spillToVReg s with
    | none => simp [hOld] at h
    | some v0 =>
      simp only [hOld] at h
      split at h
      · contradiction
      · rename_i hNe
        injection h with hEq
        subst hEq
        obtain ⟨val0, hEnv0, hSpill0⟩ := hRel.spill_ok s v0 hOld
        exact ⟨val0, by rw [envGet_envSet_ne _ _ _ _ (Ne.symm hNe)]; exact hEnv0, hSpill0⟩
  flag_ok := by
    intro vf h
    simp only [symInvalidateVReg] at h
    cases hOld : sym.flagVReg with
    | none => simp [hOld] at h
    | some v0 =>
      simp only [hOld] at h
      split at h
      · contradiction
      · rename_i hNe
        injection h with hEq
        subst hEq
        obtain ⟨b0, hEnv0, hFlag0⟩ := hRel.flag_ok v0 hOld
        exact ⟨b0, by rw [envGet_envSet_ne _ _ _ _ (Ne.symm hNe)]; exact hEnv0, hFlag0⟩

/-- `symSetPhys` preserves `SymStateRel` when `vDst` is set to `val` in `env`
and `dst` is set to `val` in `st.regs`. -/
theorem symStateRel_symSetPhys {sym : SymRegState} {env : VRegEnv}
    {heap : List Nat} {st : PostRaState}
    (hRel : SymStateRel sym env heap st)
    (dst : PhysReg) (vDst : VReg) (val : MVal) :
    SymStateRel (symSetPhys sym dst vDst) (envSet env vDst val) heap
      { st with regs := regSet st.regs dst val } := by
  have hInv := symStateRel_invalidate hRel vDst val
  refine ⟨hInv.heap_eq, ?_, hInv.spill_ok, hInv.flag_ok⟩
  intro r v h
  simp only [symSetPhys] at h
  split at h
  · rename_i hEq
    subst hEq
    injection h with hV
    subst hV
    exact ⟨val, by simp [envGet_envSet_same], by simp [regSet]⟩
  · rename_i hNe
    simp only [regSet, hNe, ↓reduceIte]
    exact hInv.phys_ok r v h

/-- `symSetFlag` preserves `SymStateRel` when `vFlagOut` is set to `.v1 b` in
`env` and `st.physFlag` is set to `some b`. -/
theorem symStateRel_symSetFlag {sym : SymRegState} {env : VRegEnv}
    {heap : List Nat} {st : PostRaState}
    (hRel : SymStateRel sym env heap st)
    (vFlagOut : VReg) (b : Bool) :
    SymStateRel (symSetFlag sym vFlagOut) (envSet env vFlagOut (.v1 b)) heap
      { st with physFlag := some b } := by
  have hInv := symStateRel_invalidate hRel vFlagOut (.v1 b)
  refine ⟨hInv.heap_eq, hInv.phys_ok, hInv.spill_ok, ?_⟩
  intro vf h
  simp only [symSetFlag, Option.some.injEq] at h
  subst h
  exact ⟨b, by simp [envGet_envSet_same], rfl⟩

/-- `symSetPhysAndFlag` preserves `SymStateRel` when `vDst` is set to `val` in
`env`, `vFlagOut` is set to `.v1 b` in `env`, `dst` is set to `val` in
`st.regs`, and `st.physFlag` is set to `some b`. -/
theorem symStateRel_symSetPhysAndFlag {sym : SymRegState} {env : VRegEnv}
    {heap : List Nat} {st : PostRaState}
    (hRel : SymStateRel sym env heap st)
    (dst : PhysReg) (vDst vFlagOut : VReg) (val : MVal) (b : Bool) :
    SymStateRel (symSetPhysAndFlag sym dst vDst vFlagOut)
      (envSet (envSet env vDst val) vFlagOut (.v1 b)) heap
      { st with regs := regSet st.regs dst val, physFlag := some b } :=
  symStateRel_symSetFlag (symStateRel_symSetPhys hRel dst vDst val) vFlagOut b

/-- `symCopyToPhys` preserves `SymStateRel` when `envGet env v = some val` and
`dst` is set to `val` in `st.regs`. -/
theorem symStateRel_symCopyToPhys {sym : SymRegState} {env : VRegEnv}
    {heap : List Nat} {st : PostRaState}
    (hRel : SymStateRel sym env heap st)
    (dst : PhysReg) (v : VReg) (val : MVal) (hVal : envGet env v = some val) :
    SymStateRel (symCopyToPhys sym dst v) env heap
      { st with regs := regSet st.regs dst val } where
  heap_eq := hRel.heap_eq
  phys_ok := by
    intro r v' h
    simp only [symCopyToPhys] at h
    split at h
    · rename_i hEq
      subst hEq
      injection h with hV
      subst hV
      exact ⟨val, hVal, by simp [regSet]⟩
    · rename_i hNe
      simp only [regSet, hNe, ↓reduceIte]
      exact hRel.phys_ok r v' h
  spill_ok := hRel.spill_ok
  flag_ok  := hRel.flag_ok

/-- `symCopyToSpill` preserves `SymStateRel` when `envGet env v = some val` and
`slot` is set to `val` in `st.spills`. -/
theorem symStateRel_symCopyToSpill {sym : SymRegState} {env : VRegEnv}
    {heap : List Nat} {st : PostRaState}
    (hRel : SymStateRel sym env heap st)
    (slot : SpillSlot) (v : VReg) (val : MVal) (hVal : envGet env v = some val) :
    SymStateRel (symCopyToSpill sym slot v) env heap
      { st with spills := spillSet st.spills slot val } where
  heap_eq := hRel.heap_eq
  phys_ok := hRel.phys_ok
  spill_ok := by
    intro s v' h
    simp only [symCopyToSpill] at h
    split at h
    · rename_i hEq
      subst hEq
      injection h with hV
      subst hV
      exact ⟨val, hVal, by simp [spillSet]⟩
    · rename_i hNe
      simp only [spillSet, hNe, ↓reduceIte]
      exact hRel.spill_ok s v' h
  flag_ok := hRel.flag_ok

/-- Helper: when `sym.physToVReg r = some v` and `envGet env v = some val`,
`st.regs r = some val`. -/
theorem SymStateRel.reg_eq_of_env {sym : SymRegState} {env : VRegEnv}
    {heap : List Nat} {st : PostRaState}
    (hRel : SymStateRel sym env heap st) {r : PhysReg} {v : VReg} {val : MVal}
    (hSym : sym.physToVReg r = some v) (hEnv : envGet env v = some val) :
    st.regs r = some val := by
  obtain ⟨val', hEnv', hReg'⟩ := hRel.phys_ok r v hSym
  rw [hEnv] at hEnv'
  injection hEnv' with hEq
  subst hEq
  exact hReg'

/-- Helper: when `sym.flagVReg = some vf` and `envGet env vf = some (.v1 b)`,
`st.physFlag = some b`. -/
theorem SymStateRel.flag_eq_of_env {sym : SymRegState} {env : VRegEnv}
    {heap : List Nat} {st : PostRaState}
    (hRel : SymStateRel sym env heap st) {vf : VReg} {b : Bool}
    (hSym : sym.flagVReg = some vf) (hEnv : envGet env vf = some (.v1 b)) :
    st.physFlag = some b := by
  obtain ⟨b', hEnv', hFlag'⟩ := hRel.flag_ok vf hSym
  rw [hEnv] at hEnv'
  injection hEnv' with hVal
  injection hVal with hEq
  subst hEq
  exact hFlag'

/-- Single-step soundness of `stepSymRegAlloc` for housekeeping instructions
(`MOV_REG`, `SPILL_STORE`, `SPILL_RELOAD`). -/
theorem stepSymRegAlloc_housekeep_sound (q : AbiQuery)
    {sym sym' : SymRegState} {env : VRegEnv} {heap : List Nat} {st : PostRaState}
    {mi? : Option AnMachineInstr} {pi : PostRaInstr}
    (hRel : SymStateRel sym env heap st)
    (hStep : stepSymRegAlloc sym mi? pi = some (.housekeep sym')) :
    ∃ st', evalPostRaInstr q st pi = some st' ∧
           SymStateRel sym' env heap st' := by
  cases pi with
  | MOV_REG dst src =>
    simp only [stepSymRegAlloc] at hStep
    cases hSrc : sym.physToVReg src with
    | none => simp [hSrc] at hStep
    | some v =>
      simp only [hSrc, Option.some.injEq, SymStepResult.housekeep.injEq] at hStep
      subst hStep
      obtain ⟨val, hEnv, hReg⟩ := hRel.phys_ok src v hSrc
      exact ⟨{ st with regs := regSet st.regs dst val },
             by simp [evalPostRaInstr, hReg],
             symStateRel_symCopyToPhys hRel dst v val hEnv⟩
  | SPILL_STORE slot src =>
    simp only [stepSymRegAlloc] at hStep
    cases hSrc : sym.physToVReg src with
    | none => simp [hSrc] at hStep
    | some v =>
      simp only [hSrc, Option.some.injEq, SymStepResult.housekeep.injEq] at hStep
      subst hStep
      obtain ⟨val, hEnv, hReg⟩ := hRel.phys_ok src v hSrc
      exact ⟨{ st with spills := spillSet st.spills slot val },
             by simp [evalPostRaInstr, hReg],
             symStateRel_symCopyToSpill hRel slot v val hEnv⟩
  | SPILL_RELOAD dst slot =>
    simp only [stepSymRegAlloc] at hStep
    cases hSlot : sym.spillToVReg slot with
    | none => simp [hSlot] at hStep
    | some v =>
      simp only [hSlot, Option.some.injEq, SymStepResult.housekeep.injEq] at hStep
      subst hStep
      obtain ⟨val, hEnv, hSpill⟩ := hRel.spill_ok slot v hSlot
      exact ⟨{ st with regs := regSet st.regs dst val },
             by simp [evalPostRaInstr, hSpill],
             symStateRel_symCopyToPhys hRel dst v val hEnv⟩
  | MOV_ABI_ARG _ _ _ =>
    simp only [stepSymRegAlloc] at hStep
    cases mi? with
    | none => contradiction
    | some mi => cases mi <;> simp at hStep
  | MOV_IMM64 _ _ =>
    simp only [stepSymRegAlloc] at hStep
    cases mi? with
    | none => contradiction
    | some mi => cases mi <;> simp at hStep
  | XOR_ZERO_CLOBBER _ =>
    simp only [stepSymRegAlloc] at hStep
    cases mi? with
    | none => contradiction
    | some mi =>
      cases mi with
      | MOV_IMM64 _ vImm => cases vImm <;> simp at hStep
      | _ => simp at hStep
  | ADD64_NOFLAGS _ _ _ =>
    simp only [stepSymRegAlloc] at hStep
    cases mi? with
    | none => contradiction
    | some mi => cases mi <;> simp at hStep
  | ADD8_NOFLAGS _ _ _ =>
    simp only [stepSymRegAlloc] at hStep
    cases mi? with
    | none => contradiction
    | some mi => cases mi <;> simp at hStep
  | ZEXT8_TO_64 _ _ =>
    simp only [stepSymRegAlloc] at hStep
    cases mi? with
    | none => contradiction
    | some mi => cases mi <;> simp at hStep
  | ADD64_SET_FLAGS _ _ _ =>
    simp only [stepSymRegAlloc] at hStep
    cases mi? with
    | none => contradiction
    | some mi => cases mi <;> simp at hStep
  | ADDC64_USE_FLAGS _ _ _ =>
    simp only [stepSymRegAlloc] at hStep
    cases mi? with
    | none => contradiction
    | some mi => cases mi <;> simp at hStep
  | ADD_SHIFTED_PTR _ _ _ _ =>
    simp only [stepSymRegAlloc] at hStep
    cases mi? with
    | none => contradiction
    | some mi => cases mi <;> simp at hStep
  | LDR64 _ _ =>
    simp only [stepSymRegAlloc] at hStep
    cases mi? with
    | none => contradiction
    | some mi => cases mi <;> simp at hStep
  | STR64 _ _ =>
    simp only [stepSymRegAlloc] at hStep
    cases mi? with
    | none => contradiction
    | some mi => cases mi <;> simp at hStep
  | CMP64_SET_FLAGS _ _ _ =>
    simp only [stepSymRegAlloc] at hStep
    cases mi? with
    | none => contradiction
    | some mi => cases mi <;> simp at hStep
  | CSEL64_USE_FLAGS _ _ _ =>
    simp only [stepSymRegAlloc] at hStep
    cases mi? with
    | none => contradiction
    | some mi => cases mi <;> simp at hStep

/-- Single-step soundness of `stepSymRegAlloc` for matched `MachineSSA`
instructions. -/
theorem stepSymRegAlloc_matched_sound (q : AbiQuery)
    {sym sym' : SymRegState} {env env' : VRegEnv} {heap heap' : List Nat}
    {st : PostRaState} {mi : AnMachineInstr} {pi : PostRaInstr}
    (hRel : SymStateRel sym env heap st)
    (hStep : stepSymRegAlloc sym (some mi) pi = some (.matched sym'))
    (hEval : evalAnMachineInstr q env heap mi = some (env', heap')) :
    ∃ st', evalPostRaInstr q st pi = some st' ∧
           SymStateRel sym' env' heap' st' := by
  cases pi with
  | MOV_REG dst src =>
    simp only [stepSymRegAlloc] at hStep
    cases h : sym.physToVReg src <;> simp [h] at hStep
  | SPILL_STORE slot src =>
    simp only [stepSymRegAlloc] at hStep
    cases h : sym.physToVReg src <;> simp [h] at hStep
  | SPILL_RELOAD dst slot =>
    simp only [stepSymRegAlloc] at hStep
    cases h : sym.spillToVReg slot <;> simp [h] at hStep
  | MOV_ABI_ARG dst ty argIdx =>
    cases mi with
    | COPY_FROM_ABI_GPR vDst bank vTy vArgIdx =>
      simp only [stepSymRegAlloc, Bool.and_eq_true, decide_eq_true_eq] at hStep
      split at hStep
      · rename_i hCond
        rcases hCond with ⟨rfl, rfl⟩
        injection hStep with hRes
        injection hRes with hSym
        subst hSym
        simp only [evalAnMachineInstr, Option.some.injEq, Prod.mk.injEq] at hEval
        rcases hEval with ⟨hEnv', hHeap'⟩
        subst hEnv'; subst hHeap'
        exact ⟨_, rfl, symStateRel_symSetPhys hRel dst vDst _⟩
      · contradiction
    | _ => simp [stepSymRegAlloc] at hStep
  | MOV_IMM64 dst imm =>
    cases mi with
    | MOV_IMM64 vDst vImm =>
      simp only [stepSymRegAlloc] at hStep
      split at hStep
      · rename_i hEq
        subst hEq
        injection hStep with hRes
        injection hRes with hSym
        subst hSym
        simp only [evalAnMachineInstr, Option.some.injEq, Prod.mk.injEq] at hEval
        rcases hEval with ⟨hEnv', hHeap'⟩
        subst hEnv'; subst hHeap'
        exact ⟨_, rfl, symStateRel_symSetPhys hRel dst vDst _⟩
      · contradiction
    | _ => simp [stepSymRegAlloc] at hStep
  | XOR_ZERO_CLOBBER dst =>
    cases mi with
    | MOV_IMM64 vDst vImm =>
      cases vImm with
      | zero =>
        simp only [stepSymRegAlloc, Option.some.injEq, SymStepResult.matched.injEq] at hStep
        subst hStep
        simp only [evalAnMachineInstr, Nat.zero_mod, Option.some.injEq, Prod.mk.injEq] at hEval
        rcases hEval with ⟨hEnv', hHeap'⟩
        subst hEnv'; subst hHeap'
        have hSet := symStateRel_symSetPhys hRel dst vDst (.v64 0)
        refine ⟨_, rfl, ⟨hSet.heap_eq, hSet.phys_ok, hSet.spill_ok, ?_⟩⟩
        intro vf hF
        contradiction
      | succ _ => simp [stepSymRegAlloc] at hStep
    | _ => simp [stepSymRegAlloc] at hStep
  | ADD64_NOFLAGS dst lhs rhs =>
    cases mi with
    | ADD64 vDst vLhs vRhs =>
      simp only [stepSymRegAlloc, Bool.and_eq_true, decide_eq_true_eq] at hStep
      split at hStep
      · rename_i hCond
        rcases hCond with ⟨hLhs, hRhs⟩
        injection hStep with hRes
        injection hRes with hSym
        subst hSym
        simp only [evalAnMachineInstr] at hEval
        cases hEL : envGet env vLhs with
        | some valL =>
          cases valL with
          | v64 a =>
            cases hER : envGet env vRhs with
            | some valR =>
              cases valR with
              | v64 b =>
                simp only [hEL, hER, Option.some.injEq, Prod.mk.injEq] at hEval
                rcases hEval with ⟨hEnv', hHeap'⟩
                subst hEnv'; subst hHeap'
                have hRL := hRel.reg_eq_of_env hLhs hEL
                have hRR := hRel.reg_eq_of_env hRhs hER
                exact ⟨_, by simp [evalPostRaInstr, hRL, hRR],
                       symStateRel_symSetPhys hRel dst vDst _⟩
              | _ => simp [hEL, hER] at hEval
            | none => simp [hEL, hER] at hEval
          | _ => simp [hEL] at hEval
        | none => simp [hEL] at hEval
      · contradiction
    | _ => simp [stepSymRegAlloc] at hStep
  | ADD8_NOFLAGS dst lhs rhs =>
    cases mi with
    | ADD8_MASK vDst vLhs vRhs =>
      simp only [stepSymRegAlloc, Bool.and_eq_true, decide_eq_true_eq] at hStep
      split at hStep
      · rename_i hCond
        rcases hCond with ⟨hLhs, hRhs⟩
        injection hStep with hRes
        injection hRes with hSym
        subst hSym
        simp only [evalAnMachineInstr] at hEval
        cases hEL : envGet env vLhs with
        | some valL =>
          cases valL with
          | v8 a =>
            cases hER : envGet env vRhs with
            | some valR =>
              cases valR with
              | v8 b =>
                simp only [hEL, hER, Option.some.injEq, Prod.mk.injEq] at hEval
                rcases hEval with ⟨hEnv', hHeap'⟩
                subst hEnv'; subst hHeap'
                have hRL := hRel.reg_eq_of_env hLhs hEL
                have hRR := hRel.reg_eq_of_env hRhs hER
                exact ⟨_, by simp [evalPostRaInstr, hRL, hRR],
                       symStateRel_symSetPhys hRel dst vDst _⟩
              | _ => simp [hEL, hER] at hEval
            | none => simp [hEL, hER] at hEval
          | _ => simp [hEL] at hEval
        | none => simp [hEL] at hEval
      · contradiction
    | _ => simp [stepSymRegAlloc] at hStep
  | ZEXT8_TO_64 dst src =>
    cases mi with
    | ZEXT8_TO_64 vDst vSrc =>
      simp only [stepSymRegAlloc] at hStep
      split at hStep
      · rename_i hSrc
        injection hStep with hRes
        injection hRes with hSym
        subst hSym
        simp only [evalAnMachineInstr] at hEval
        cases hES : envGet env vSrc with
        | some valS =>
          cases valS with
          | v8 a =>
            simp only [hES, Option.some.injEq, Prod.mk.injEq] at hEval
            rcases hEval with ⟨hEnv', hHeap'⟩
            subst hEnv'; subst hHeap'
            have hRS := hRel.reg_eq_of_env hSrc hES
            exact ⟨_, by simp [evalPostRaInstr, hRS],
                   symStateRel_symSetPhys hRel dst vDst _⟩
          | _ => simp [hES] at hEval
        | none => simp [hES] at hEval
      · contradiction
    | _ => simp [stepSymRegAlloc] at hStep
  | ADD64_SET_FLAGS dst lhs rhs =>
    cases mi with
    | ADD64_FLAGS vDst vFlagOut vLhs vRhs =>
      simp only [stepSymRegAlloc, Bool.and_eq_true, decide_eq_true_eq] at hStep
      split at hStep
      · rename_i hCond
        rcases hCond with ⟨hLhs, hRhs⟩
        injection hStep with hRes
        injection hRes with hSym
        subst hSym
        simp only [evalAnMachineInstr] at hEval
        cases hEL : envGet env vLhs with
        | some valL =>
          cases valL with
          | v64 a =>
            cases hER : envGet env vRhs with
            | some valR =>
              cases valR with
              | v64 b =>
                simp only [hEL, hER, Option.some.injEq, Prod.mk.injEq] at hEval
                rcases hEval with ⟨hEnv', hHeap'⟩
                subst hEnv'; subst hHeap'
                have hRL := hRel.reg_eq_of_env hLhs hEL
                have hRR := hRel.reg_eq_of_env hRhs hER
                exact ⟨_, by simp [evalPostRaInstr, hRL, hRR],
                       symStateRel_symSetPhysAndFlag hRel dst vDst vFlagOut _ _⟩
              | _ => simp [hEL, hER] at hEval
            | none => simp [hEL, hER] at hEval
          | _ => simp [hEL] at hEval
        | none => simp [hEL] at hEval
      · contradiction
    | _ => simp [stepSymRegAlloc] at hStep
  | ADDC64_USE_FLAGS dst lhs rhs =>
    cases mi with
    | ADDC64_FLAGS vDst vFlagOut vLhs vRhs vFlagIn =>
      simp only [stepSymRegAlloc, Bool.and_eq_true, decide_eq_true_eq] at hStep
      split at hStep
      · rename_i hCond
        rcases hCond with ⟨⟨hLhs, hRhs⟩, hFlagIn⟩
        injection hStep with hRes
        injection hRes with hSym
        subst hSym
        simp only [evalAnMachineInstr] at hEval
        cases hEL : envGet env vLhs with
        | some valL =>
          cases valL with
          | v64 a =>
            cases hER : envGet env vRhs with
            | some valR =>
              cases valR with
              | v64 b =>
                cases hEF : envGet env vFlagIn with
                | some valF =>
                  cases valF with
                  | v1 cin =>
                    simp only [hEL, hER, hEF, Option.some.injEq, Prod.mk.injEq] at hEval
                    rcases hEval with ⟨hEnv', hHeap'⟩
                    subst hEnv'; subst hHeap'
                    have hRL := hRel.reg_eq_of_env hLhs hEL
                    have hRR := hRel.reg_eq_of_env hRhs hER
                    have hRF := hRel.flag_eq_of_env hFlagIn hEF
                    exact ⟨_, by simp [evalPostRaInstr, hRL, hRR, hRF],
                           symStateRel_symSetPhysAndFlag hRel dst vDst vFlagOut _ _⟩
                  | _ => simp [hEL, hER, hEF] at hEval
                | none => simp [hEL, hER, hEF] at hEval
              | _ => simp [hEL, hER] at hEval
            | none => simp [hEL, hER] at hEval
          | _ => simp [hEL] at hEval
        | none => simp [hEL] at hEval
      · contradiction
    | _ => simp [stepSymRegAlloc] at hStep
  | ADD_SHIFTED_PTR dst base idx shift =>
    cases mi with
    | ADD_SHIFTED_PTR vDst vBase vIdx vShift =>
      simp only [stepSymRegAlloc, Bool.and_eq_true, decide_eq_true_eq] at hStep
      split at hStep
      · rename_i hCond
        rcases hCond with ⟨⟨hBase, hIdx⟩, rfl⟩
        injection hStep with hRes
        injection hRes with hSym
        subst hSym
        simp only [evalAnMachineInstr] at hEval
        cases hEB : envGet env vBase with
        | some valB =>
          cases valB with
          | ptr b =>
            cases hEI : envGet env vIdx with
            | some valI =>
              cases valI with
              | v64 i =>
                simp only [hEB, hEI, Option.some.injEq, Prod.mk.injEq] at hEval
                rcases hEval with ⟨hEnv', hHeap'⟩
                subst hEnv'; subst hHeap'
                have hRB := hRel.reg_eq_of_env hBase hEB
                have hRI := hRel.reg_eq_of_env hIdx hEI
                exact ⟨_, by simp [evalPostRaInstr, hRB, hRI],
                       symStateRel_symSetPhys hRel dst vDst _⟩
              | _ => simp [hEB, hEI] at hEval
            | none => simp [hEB, hEI] at hEval
          | _ => simp [hEB] at hEval
        | none => simp [hEB] at hEval
      · contradiction
    | _ => simp [stepSymRegAlloc] at hStep
  | LDR64 dst ptrReg =>
    cases mi with
    | LDR64 vDst vPtr =>
      simp only [stepSymRegAlloc] at hStep
      split at hStep
      · rename_i hPtr
        injection hStep with hRes
        injection hRes with hSym
        subst hSym
        simp only [evalAnMachineInstr] at hEval
        cases hEP : envGet env vPtr with
        | some valP =>
          cases valP with
          | ptr idx =>
            cases hLoad : heapLoad heap idx with
            | some v =>
              simp only [hEP, hLoad, Option.some.injEq, Prod.mk.injEq] at hEval
              rcases hEval with ⟨hEnv', hHeap'⟩
              subst hEnv'; subst hHeap'
              have hRP := hRel.reg_eq_of_env hPtr hEP
              exact ⟨_, by simp [evalPostRaInstr, hRP, hRel.heap_eq, hLoad],
                     symStateRel_symSetPhys hRel dst vDst _⟩
            | none => simp [hEP, hLoad] at hEval
          | _ => simp [hEP] at hEval
        | none => simp [hEP] at hEval
      · contradiction
    | _ => simp [stepSymRegAlloc] at hStep
  | STR64 valReg ptrReg =>
    cases mi with
    | STR64 vVal vPtr =>
      simp only [stepSymRegAlloc, Bool.and_eq_true, decide_eq_true_eq] at hStep
      split at hStep
      · rename_i hCond
        rcases hCond with ⟨hVal, hPtr⟩
        injection hStep with hRes
        injection hRes with hSym
        subst hSym
        simp only [evalAnMachineInstr] at hEval
        cases hEV : envGet env vVal with
        | some valV =>
          cases valV with
          | v64 v =>
            cases hEP : envGet env vPtr with
            | some valP =>
              cases valP with
              | ptr idx =>
                cases hStore : heapStore heap idx v with
                | some heap'' =>
                  simp only [hEV, hEP, hStore, Option.some.injEq, Prod.mk.injEq] at hEval
                  rcases hEval with ⟨hEnv', hHeap'⟩
                  subst hEnv'; subst hHeap'
                  have hRV := hRel.reg_eq_of_env hVal hEV
                  have hRP := hRel.reg_eq_of_env hPtr hEP
                  refine ⟨{ st with heap := heap'' },
                          by simp [evalPostRaInstr, hRV, hRP, hRel.heap_eq, hStore],
                          ⟨rfl, hRel.phys_ok, hRel.spill_ok, hRel.flag_ok⟩⟩
                | none => simp [hEV, hEP, hStore] at hEval
              | _ => simp [hEV, hEP] at hEval
            | none => simp [hEV, hEP] at hEval
          | _ => simp [hEV] at hEval
        | none => simp [hEV] at hEval
      · contradiction
    | _ => simp [stepSymRegAlloc] at hStep
  | CMP64_SET_FLAGS pred lhs rhs =>
    cases mi with
    | CMP64_FLAGS vFlagOut vPred vLhs vRhs =>
      simp only [stepSymRegAlloc, Bool.and_eq_true, decide_eq_true_eq] at hStep
      split at hStep
      · rename_i hCond
        rcases hCond with ⟨⟨rfl, hLhs⟩, hRhs⟩
        injection hStep with hRes
        injection hRes with hSym
        subst hSym
        simp only [evalAnMachineInstr] at hEval
        cases hEL : envGet env vLhs with
        | some valL =>
          cases valL with
          | v64 a =>
            cases hER : envGet env vRhs with
            | some valR =>
              cases valR with
              | v64 b =>
                simp only [hEL, hER, Option.some.injEq, Prod.mk.injEq] at hEval
                rcases hEval with ⟨hEnv', hHeap'⟩
                subst hEnv'; subst hHeap'
                have hRL := hRel.reg_eq_of_env hLhs hEL
                have hRR := hRel.reg_eq_of_env hRhs hER
                exact ⟨_, by simp [evalPostRaInstr, hRL, hRR],
                       symStateRel_symSetFlag hRel vFlagOut _⟩
              | _ => simp [hEL, hER] at hEval
            | none => simp [hEL, hER] at hEval
          | _ => simp [hEL] at hEval
        | none => simp [hEL] at hEval
      · contradiction
    | _ => simp [stepSymRegAlloc] at hStep
  | CSEL64_USE_FLAGS dst tVal fVal =>
    cases mi with
    | CSEL64 vDst vFlagIn vTVal vFVal =>
      simp only [stepSymRegAlloc, Bool.and_eq_true, decide_eq_true_eq] at hStep
      split at hStep
      · rename_i hCond
        rcases hCond with ⟨⟨hFlagIn, hTVal⟩, hFVal⟩
        injection hStep with hRes
        injection hRes with hSym
        subst hSym
        simp only [evalAnMachineInstr] at hEval
        cases hEF : envGet env vFlagIn with
        | some valF =>
          cases valF with
          | v1 c =>
            cases hET : envGet env vTVal with
            | some valT =>
              cases valT with
              | v64 tv =>
                cases hEFalse : envGet env vFVal with
                | some valFalse =>
                  cases valFalse with
                  | v64 fv =>
                    simp only [hEF, hET, hEFalse, Option.some.injEq, Prod.mk.injEq] at hEval
                    rcases hEval with ⟨hEnv', hHeap'⟩
                    subst hEnv'; subst hHeap'
                    have hRF := hRel.flag_eq_of_env hFlagIn hEF
                    have hRT := hRel.reg_eq_of_env hTVal hET
                    have hRFalse := hRel.reg_eq_of_env hFVal hEFalse
                    exact ⟨_, by simp [evalPostRaInstr, hRF, hRT, hRFalse],
                           symStateRel_symSetPhys hRel dst vDst _⟩
                  | _ => simp [hEF, hET, hEFalse] at hEval
                | none => simp [hEF, hET, hEFalse] at hEval
              | _ => simp [hEF, hET] at hEval
            | none => simp [hEF, hET] at hEval
          | _ => simp [hEF] at hEval
        | none => simp [hEF] at hEval
      · contradiction
    | _ => simp [stepSymRegAlloc] at hStep

/-- Notice that if `ssaBody = []` (`mi? = none`), `stepSymRegAlloc` never
returns `.matched`. -/
theorem stepSymRegAlloc_none_not_matched {sym sym' : SymRegState}
    {pi : PostRaInstr}
    (hStep : stepSymRegAlloc sym none pi = some (.matched sym')) : False := by
  cases pi with
  | MOV_REG dst src =>
    simp only [stepSymRegAlloc] at hStep
    cases h : sym.physToVReg src <;> simp [h] at hStep
  | SPILL_STORE slot src =>
    simp only [stepSymRegAlloc] at hStep
    cases h : sym.physToVReg src <;> simp [h] at hStep
  | SPILL_RELOAD dst slot =>
    simp only [stepSymRegAlloc] at hStep
    cases h : sym.spillToVReg slot <;> simp [h] at hStep
  | _ => simp [stepSymRegAlloc] at hStep

/-- Multi-step soundness of `checkPostRaBody` by structural induction over the
`PostRaInstr` list `postBody`. -/
theorem checkPostRaBody_sound (q : AbiQuery)
    (postBody : List PostRaInstr) :
    ∀ {sym symFinal : SymRegState} {ssaBody : List AnMachineInstr}
      {env envFinal : VRegEnv} {heap heapFinal : List Nat} {st : PostRaState},
      SymStateRel sym env heap st →
      checkPostRaBody sym ssaBody postBody = some (symFinal, []) →
      evalAnMachineBody q env heap ssaBody = some (envFinal, heapFinal) →
      ∃ stFinal, evalPostRaBody q st postBody = some stFinal ∧
                 SymStateRel symFinal envFinal heapFinal stFinal := by
  induction postBody with
  | nil =>
    intro sym symFinal ssaBody env envFinal heap heapFinal st hRel hCheck hEval
    simp only [checkPostRaBody, Option.some.injEq, Prod.mk.injEq] at hCheck
    rcases hCheck with ⟨rfl, rfl⟩
    simp only [evalAnMachineBody, Option.some.injEq, Prod.mk.injEq] at hEval
    rcases hEval with ⟨rfl, rfl⟩
    exact ⟨st, rfl, hRel⟩
  | cons pi rest ih =>
    intro sym symFinal ssaBody env envFinal heap heapFinal st hRel hCheck hEval
    simp only [checkPostRaBody] at hCheck
    cases hStep : stepSymRegAlloc sym ssaBody.head? pi with
    | none => simp [hStep] at hCheck
    | some res =>
      simp only [hStep] at hCheck
      cases res with
      | housekeep sym' =>
        obtain ⟨st', hPostStep, hRel'⟩ :=
          stepSymRegAlloc_housekeep_sound q hRel hStep
        obtain ⟨stFinal, hPostRest, hRelFinal⟩ :=
          ih hRel' hCheck hEval
        exact ⟨stFinal, by simp [evalPostRaBody, hPostStep, hPostRest], hRelFinal⟩
      | matched sym' =>
        cases ssaBody with
        | nil =>
          exfalso
          exact stepSymRegAlloc_none_not_matched hStep
        | cons mi ssaRest =>
          simp only [List.head?_cons] at hStep
          simp only [List.tail_cons] at hCheck
          simp only [evalAnMachineBody] at hEval
          cases hMiEval : evalAnMachineInstr q env heap mi with
          | none => simp [hMiEval] at hEval
          | some pair =>
            simp only [hMiEval] at hEval
            obtain ⟨st', hPostStep, hRel'⟩ :=
              stepSymRegAlloc_matched_sound q hRel hStep hMiEval
            obtain ⟨stFinal, hPostRest, hRelFinal⟩ :=
              ih hRel' hCheck hEval
            exact ⟨stFinal, by simp [evalPostRaBody, hPostStep, hPostRest], hRelFinal⟩

/-- **General Soundness Theorem (`checkPostRaMachine_sound`)**:
For **any** `MachineFunction` `mf` and **any** `PostRaMachineProg` `post`, if
`checkPostRaMachine mf post = true`, then `post` refines `mf` under
`Trusted.Compiles`! -/
theorem checkPostRaMachine_sound (mf : MachineFunction) (post : PostRaMachineProg)
    (hCheck : checkPostRaMachine mf post = true) :
    Compiles AnMachineLang PostRaMachineLang machineToPostRaCodec mf post := by
  apply compiles_of_eval_eq
  intro q res hEvalMf
  unfold checkPostRaMachine at hCheck
  cases hBodyCheck : checkPostRaBody initSymRegState mf.body post.body with
  | none => simp [hBodyCheck] at hCheck
  | some pair =>
    rcases pair with ⟨symFinal, remSsa⟩
    cases remSsa with
    | cons _ _ => simp [hBodyCheck] at hCheck
    | nil =>
      simp only [hBodyCheck] at hCheck
      unfold evalMachineFunction at hEvalMf
      cases hSsaEval : evalAnMachineBody q [] q.heap mf.body with
      | none => simp [hSsaEval] at hEvalMf
      | some ssaPair =>
        rcases ssaPair with ⟨envFinal, heapFinal⟩
        simp only [hSsaEval] at hEvalMf
        obtain ⟨stFinal, hPostBody, hRelFinal⟩ :=
          checkPostRaBody_sound q post.body (initSymStateRel q) hBodyCheck hSsaEval
        unfold evalPostRaProg
        simp only [hPostBody]
        cases hRetMf : mf.ret with
        | G_RET128 _ => simp [hRetMf] at hCheck
        | G_RET64 _  => simp [hRetMf] at hCheck
        | RET_PAIR vLo vHi =>
          cases hRetPost : post.ret with
          | RET_SINGLE _ => simp [hRetMf, hRetPost] at hCheck
          | RET_PAIR pLo pHi =>
            simp only [hRetMf, hRetPost, decide_eq_true_eq] at hCheck hEvalMf
            rcases hCheck with ⟨hLo, hHi⟩
            cases hELo : envGet envFinal vLo with
            | some valLo =>
              cases valLo with
              | v64 lo =>
                cases hEHi : envGet envFinal vHi with
                | some valHi =>
                  cases valHi with
                  | v64 hi =>
                    simp only [hELo, hEHi, Option.some.injEq] at hEvalMf
                    have hRLo := hRelFinal.reg_eq_of_env hLo hELo
                    have hRHi := hRelFinal.reg_eq_of_env hHi hEHi
                    simp [hRLo, hRHi, hRelFinal.heap_eq, hEvalMf]
                  | _ => simp [hELo, hEHi] at hEvalMf
                | none => simp [hELo, hEHi] at hEvalMf
              | _ => simp [hELo] at hEvalMf
            | none => simp [hELo] at hEvalMf
        | RET_SINGLE vLo =>
          cases hRetPost : post.ret with
          | RET_PAIR _ _ => simp [hRetMf, hRetPost] at hCheck
          | RET_SINGLE pLo =>
            simp only [hRetMf, hRetPost, decide_eq_true_eq] at hCheck hEvalMf
            cases hELo : envGet envFinal vLo with
            | some valLo =>
              cases valLo with
              | v64 lo =>
                simp only [hELo, Option.some.injEq] at hEvalMf
                have hRLo := hRelFinal.reg_eq_of_env hCheck hELo
                simp [hRLo, hRelFinal.heap_eq, hEvalMf]
              | _ => simp [hELo] at hEvalMf
            | none => simp [hELo] at hEvalMf

/-- `BB-8` `CertChecker` packaging `checkPostRaMachine` and its general
soundness proof `checkPostRaMachine_sound`. -/
def regAllocCertChecker :
    CertChecker AnMachineLang PostRaMachineLang machineToPostRaCodec where
  check := checkPostRaMachine
  sound := checkPostRaMachine_sound

/-!
### Concrete `PostRaMachineProg` Lowerings and Negative Flag-Clobber Canary

We now exhibit concrete register-allocated `PostRaMachineProg` lowerings for
both benchmark functions (`llvmAddU128AndU8` and `llvmGepLoadSelect`):
- `postRaAddU128AndU8` exercises stack spilling (`SPILL_STORE 0 .r4` and
  `SPILL_RELOAD .r6 0`), register moves (`MOV_REG`), narrow 8-bit arithmetic,
  and two 128-bit `ADD64_SET_FLAGS` + `ADDC64_USE_FLAGS` carry chains.
- `postRaAddU128ClobberBug` is the negative canary: it replaces `MOV_IMM64 .r7 0`
  with x86-style `XOR_ZERO_CLOBBER .r7` (`xor r7d, r7d`) **between**
  `ADD64_SET_FLAGS` and `ADDC64_USE_FLAGS`, clobbering the live carry flag in
  `EFLAGS`, and we prove that `checkPostRaMachine` rejects it (`= false`).
-/

def postRaAddU128AndU8 : PostRaMachineProg := {
  numSpillSlots := 1
  body := [
    .MOV_ABI_ARG .r0 .s64 0,       -- v1000 (a_lo)
    .MOV_ABI_ARG .r1 .s64 1,       -- v2000 (a_hi)
    .MOV_ABI_ARG .r2 .s64 2,       -- v1001 (b_lo)
    .MOV_ABI_ARG .r3 .s64 3,       -- v2001 (b_hi)
    .MOV_ABI_ARG .r4 .s8 4,        -- v2 (c_u8)
    .SPILL_STORE 0 .r4,            -- spill v2 to stack slot 0
    .MOV_ABI_ARG .r5 .s8 5,        -- v3 (d_u8)
    .ADD64_SET_FLAGS .r0 .r0 .r2,  -- v4410, v4610 = G_UADDO v1000, v1001
    .ADDC64_USE_FLAGS .r1 .r1 .r3, -- v4510, v4710 = G_UADDE v2000, v2001, v4610
    .SPILL_RELOAD .r6 0,           -- reload v2 from stack slot 0 into r6
    .ADD8_NOFLAGS .r6 .r6 .r5,     -- v11 = ADD8_MASK v2, v3
    .ZEXT8_TO_64 .r6 .r6,          -- v12 = ZEXT8_TO_64 v11
    .MOV_IMM64 .r7 0,              -- v4813 = MOV_IMM64 0 (does NOT clobber flags)
    .ADD64_SET_FLAGS .r0 .r0 .r6,  -- v4414, v4614 = ADD64_FLAGS v4410, v12
    .ADDC64_USE_FLAGS .r1 .r1 .r7  -- v4514, v4714 = ADDC64_FLAGS v4510, v4813, v4614
  ]
  ret := .RET_PAIR .r0 .r1
}

def postRaGepLoadSelect : PostRaMachineProg := {
  numSpillSlots := 0
  body := [
    .MOV_ABI_ARG .r0 .p0 0,          -- v0 = base
    .MOV_ABI_ARG .r1 .s64 1,         -- v1 = idx
    .MOV_ABI_ARG .r3 .s64 3,         -- v3 = fallback
    .ADD_SHIFTED_PTR .r2 .r0 .r1 3,  -- v7 = base + (idx << 3)
    .LDR64 .r4 .r2,                  -- v9 = *v7
    .CMP64_SET_FLAGS .ugt .r4 .r3,   -- v10 = (v9 >u v3)
    .CSEL64_USE_FLAGS .r0 .r4 .r3    -- v11 = v10 ? v9 : v3
  ]
  ret := .RET_SINGLE .r0
}

/-- Both `postRaAddU128AndU8` and `postRaGepLoadSelect` are accepted by
`checkPostRaMachine` (`= true`). -/
theorem checkPostRaMachine_benchmarks_accepted :
    checkPostRaMachine (globalISelPass llvmAddU128AndU8) postRaAddU128AndU8 = true ∧
    checkPostRaMachine (globalISelPass llvmGepLoadSelect) postRaGepLoadSelect = true := by
  exact ⟨rfl, rfl⟩

/-- **Negative Canary (`postRaAddU128ClobberBug`)**:
Suppose the register allocator / instruction scheduler rematerializes `0` using
`XOR_ZERO_CLOBBER .r7` (`MOV32r0` / `xor r7d, r7d`) **between**
`ADD64_SET_FLAGS .r0 .r0 .r6` and `ADDC64_USE_FLAGS .r1 .r1 .r7` on an
`MachineSSA` program where `MOV_IMM64 4813 0` was scheduled between `ADD64_FLAGS`
and `ADDC64_FLAGS`. Because `XOR_ZERO_CLOBBER` clobbers `EFLAGS` (`flagVReg :=
none`), `checkPostRaMachine` rejects the lowered program (`= false`)! -/
def mfInterveningZeroBetweenCarry : MachineFunction := {
  props := {
    isSSA           := true
    legalized       := true
    regBankSelected := true
    selected        := true
    noVRegs         := false
  }
  body := [
    .COPY_FROM_ABI_GPR 0 .gpr .s64 0,
    .COPY_FROM_ABI_GPR 1 .gpr .s64 1,
    .COPY_FROM_ABI_GPR 2 .gpr .s64 2,
    .ADD64_FLAGS 10 20 0 2,      -- defines carry flag v20
    .MOV_IMM64 30 0,             -- materializes 0 into v30 while v20 is live!
    .ADDC64_FLAGS 11 21 1 30 20  -- consumes carry flag v20!
  ]
  ret := .RET_PAIR 10 11
}

def postRaInterveningXorClobberBug : PostRaMachineProg := {
  numSpillSlots := 0
  body := [
    .MOV_ABI_ARG .r0 .s64 0,
    .MOV_ABI_ARG .r1 .s64 1,
    .MOV_ABI_ARG .r2 .s64 2,
    .ADD64_SET_FLAGS .r0 .r0 .r2,  -- sets EFLAGS.CF = v20
    .XOR_ZERO_CLOBBER .r3,         -- BUG: `xor r3d, r3d` clobbers EFLAGS.CF!
    .ADDC64_USE_FLAGS .r1 .r1 .r3  -- reads clobbered EFLAGS.CF!
  ]
  ret := .RET_PAIR .r0 .r1
}

def postRaInterveningMovImmSafe : PostRaMachineProg := {
  numSpillSlots := 0
  body := [
    .MOV_ABI_ARG .r0 .s64 0,
    .MOV_ABI_ARG .r1 .s64 1,
    .MOV_ABI_ARG .r2 .s64 2,
    .ADD64_SET_FLAGS .r0 .r0 .r2,  -- sets EFLAGS.CF = v20
    .MOV_IMM64 .r3 0,              -- SAFE: `mov r3, 0` preserves EFLAGS.CF!
    .ADDC64_USE_FLAGS .r1 .r1 .r3  -- reads intact EFLAGS.CF = v20!
  ]
  ret := .RET_PAIR .r0 .r1
}

/-- **Negative & Positive Flag-Liveness Canary Theorem**:
`checkPostRaMachine` rejects `postRaInterveningXorClobberBug` (`= false`) where
`XOR_ZERO_CLOBBER` clobbers the live carry flag between `ADD64_SET_FLAGS` and
`ADDC64_USE_FLAGS`, while accepting `postRaInterveningMovImmSafe` (`= true`)
where `MOV_IMM64` preserves the live carry flag. -/
theorem canary_intervening_flag_clobber_between_uaddo_and_uadde_rejected :
    checkPostRaMachine mfInterveningZeroBetweenCarry postRaInterveningXorClobberBug = false ∧
    checkPostRaMachine mfInterveningZeroBetweenCarry postRaInterveningMovImmSafe = true := by
  exact ⟨rfl, rfl⟩

/--Untrusted register-allocation oracle mapping our selected `MachineFunction`s
to their `PostRaMachineProg` lowerings, gated by `regAllocCertChecker.toPassCompiler`. -/
def untrustedRegAllocOracle (mf : MachineFunction) : Option PostRaMachineProg :=
  if mf = globalISelPass llvmAddU128AndU8 then
    some postRaAddU128AndU8
  else if mf = globalISelPass llvmGepLoadSelect then
    some postRaGepLoadSelect
  else
    none

/-- `BB-8` `PassCompiler` for Stage 4 (`RegAlloc` + `VirtRegRewriter`), obtained
via `regAllocCertChecker.toPassCompiler`. -/
def regAllocCompiler :
    PassCompiler AnMachineLang PostRaMachineLang machineToPostRaCodec :=
  regAllocCertChecker.toPassCompiler untrustedRegAllocOracle

/-!
## Section 9: Stage 5 — `PrologEpilogAndMcEncode` (`PostRaMachineLang -> FramedIsaLang`) and Full 5-Stage Pipeline Composition

In LLVM's backend (`llvm/CodeGen/PrologEpilogInserter.cpp`,
`llvm/CodeGen/TargetFrameLowering.h`, and `llvm/MC/MCCodeEmitter.h`), the final
lowering stage from `PostRA MachineIR` to `FramedIsaLang`:
1. Allocates the stack frame (`ISA_SUB_SP p.numSpillSlots`) on function entry,
2. Replaces abstract `MO_FrameIndex` spill instructions (`SPILL_STORE`,
   `SPILL_RELOAD`) with concrete SP-relative stack memory instructions
   (`ISA_STR_SP`, `ISA_LDR_SP`) via `eliminateFrameIndex`,
3. Encodes every physical `PostRaInstr` into its corresponding `IsaInstr`
   (`MCInst`), and
4. Deallocates the stack frame (`ISA_ADD_SP p.numSpillSlots`) before returning,
   where `ISA_RET` checks that the stack pointer has been restored to its entry
   depth (`spOffset = 0`) and callee-saved registers are intact.
-/

/-- Concrete ISA / `MCInst` instructions with explicit stack-pointer arithmetic
and SP-relative frame memory accesses. -/
inductive IsaInstr where
  | ISA_SUB_SP           (words : Nat)
  | ISA_ADD_SP           (words : Nat)
  | ISA_STR_SP           (spOff : Nat) (src : PhysReg)
  | ISA_LDR_SP           (dst : PhysReg) (spOff : Nat)
  | ISA_MOV_ABI_ARG      (dst : PhysReg) (ty : LowLevelType) (argIdx : Nat)
  | ISA_MOV_REG          (dst src : PhysReg)
  | ISA_MOV_IMM64        (dst : PhysReg) (imm : Nat)
  | ISA_XOR_ZERO_CLOBBER (dst : PhysReg)
  | ISA_ADD64_NOFLAGS    (dst lhs rhs : PhysReg)
  | ISA_ADD8_NOFLAGS     (dst lhs rhs : PhysReg)
  | ISA_ZEXT8_TO_64      (dst src : PhysReg)
  | ISA_ADD64_SET_FLAGS  (dst lhs rhs : PhysReg)
  | ISA_ADDC64_USE_FLAGS (dst lhs rhs : PhysReg)
  | ISA_ADD_SHIFTED_PTR  (dst base idx : PhysReg) (shift : Nat)
  | ISA_LDR64            (dst ptrReg : PhysReg)
  | ISA_STR64            (valReg ptrReg : PhysReg)
  | ISA_CMP64_SET_FLAGS  (pred : IntPred) (lhs rhs : PhysReg)
  | ISA_CSEL64_USE_FLAGS (dst tVal fVal : PhysReg)
  deriving DecidableEq, Repr

/-- Return instruction of `FramedIsaProg`. -/
inductive IsaRet where
  | ISA_RET_PAIR   (loReg hiReg : PhysReg)
  | ISA_RET_SINGLE (loReg : PhysReg)
  deriving DecidableEq, Repr

/-- Complete framed ISA program emitted by `PrologEpilogInserter` + `AsmPrinter`
+ `MCCodeEmitter`. -/
structure FramedIsaProg where
  prologue : List IsaInstr
  body     : List IsaInstr
  epilogue : List IsaInstr
  ret      : IsaRet
  deriving DecidableEq, Repr

/-- Operational state of `FramedIsaLang`. `spOffset` tracks the downward stack
frame allocation depth in 64-bit words relative to `q.initSp`; `ISA_RET` checks
that `spOffset = 0` (balanced stack frame). -/
structure IsaState where
  regs            : PhysReg → Option MVal
  stack           : Nat → Option MVal
  spOffset        : Nat
  physFlag        : Option Bool
  heap            : List Nat
  calleeSavedSnap : Nat

def initIsaState (q : AbiQuery) : IsaState := {
  regs            := fun _ => none
  stack           := fun _ => none
  spOffset        := 0
  physFlag        := none
  heap            := q.heap
  calleeSavedSnap := q.calleeSaved
}

/-- Evaluates a single `IsaInstr`. -/
def evalIsaInstr (q : AbiQuery) (st : IsaState) (inst : IsaInstr) :
    Option IsaState :=
  match inst with
  | .ISA_SUB_SP words =>
    some { st with spOffset := st.spOffset + words }
  | .ISA_ADD_SP words =>
    if words ≤ st.spOffset then
      some { st with spOffset := st.spOffset - words }
    else
      none
  | .ISA_STR_SP spOff src =>
    match st.regs src with
    | some v => some { st with stack := spillSet st.stack spOff v }
    | none   => none
  | .ISA_LDR_SP dst spOff =>
    match st.stack spOff with
    | some v => some { st with regs := regSet st.regs dst v }
    | none   => none
  | .ISA_MOV_ABI_ARG dst ty argIdx =>
    let raw := q.getArg argIdx
    let v := match ty with
      | .s1   => MVal.v1 (decide (raw % 2 = 1))
      | .s8   => MVal.v8 (raw % word8Mod)
      | .s32  => MVal.v32 (raw % word32Mod)
      | .s64  => MVal.v64 raw
      | .s128 => MVal.v128 raw 0
      | .p0   => MVal.ptr raw
    some { st with regs := regSet st.regs dst v }
  | .ISA_MOV_REG dst src =>
    match st.regs src with
    | some v => some { st with regs := regSet st.regs dst v }
    | none   => none
  | .ISA_MOV_IMM64 dst imm =>
    some { st with regs := regSet st.regs dst (.v64 (imm % word64Mod)) }
  | .ISA_XOR_ZERO_CLOBBER dst =>
    some { st with
      regs     := regSet st.regs dst (.v64 0)
      physFlag := some false }
  | .ISA_ADD64_NOFLAGS dst lhs rhs =>
    match st.regs lhs, st.regs rhs with
    | some (.v64 a), some (.v64 b) =>
      let (lo, _) := add64WithCarry a b false
      some { st with regs := regSet st.regs dst (.v64 lo) }
    | _, _ => none
  | .ISA_ADD8_NOFLAGS dst lhs rhs =>
    match st.regs lhs, st.regs rhs with
    | some (.v8 a), some (.v8 b) =>
      some { st with regs := regSet st.regs dst (.v8 ((a + b) % word8Mod)) }
    | _, _ => none
  | .ISA_ZEXT8_TO_64 dst src =>
    match st.regs src with
    | some (.v8 a) =>
      some { st with regs := regSet st.regs dst (.v64 (a % word8Mod)) }
    | _ => none
  | .ISA_ADD64_SET_FLAGS dst lhs rhs =>
    match st.regs lhs, st.regs rhs with
    | some (.v64 a), some (.v64 b) =>
      let (lo, carry) := add64WithCarry a b false
      some { st with
        regs     := regSet st.regs dst (.v64 lo)
        physFlag := some carry }
    | _, _ => none
  | .ISA_ADDC64_USE_FLAGS dst lhs rhs =>
    match st.regs lhs, st.regs rhs, st.physFlag with
    | some (.v64 a), some (.v64 b), some cin =>
      let (lo, carry) := add64WithCarry a b cin
      some { st with
        regs     := regSet st.regs dst (.v64 lo)
        physFlag := some carry }
    | _, _, _ => none
  | .ISA_ADD_SHIFTED_PTR dst base idx shift =>
    match st.regs base, st.regs idx with
    | some (.ptr b), some (.v64 i) =>
      let byteOff := (i * (2 ^ shift)) % word64Mod
      some { st with regs := regSet st.regs dst (.ptr (b + byteOff / 8)) }
    | _, _ => none
  | .ISA_LDR64 dst ptrReg =>
    match st.regs ptrReg with
    | some (.ptr idx) =>
      match heapLoad st.heap idx with
      | some v => some { st with regs := regSet st.regs dst (.v64 (v % word64Mod)) }
      | none   => none
    | _ => none
  | .ISA_STR64 valReg ptrReg =>
    match st.regs valReg, st.regs ptrReg with
    | some (.v64 v), some (.ptr idx) =>
      match heapStore st.heap idx v with
      | some heap' => some { st with heap := heap' }
      | none       => none
    | _, _ => none
  | .ISA_CMP64_SET_FLAGS pred lhs rhs =>
    match st.regs lhs, st.regs rhs with
    | some (.v64 a), some (.v64 b) =>
      some { st with physFlag := some (pred.eval a b) }
    | _, _ => none
  | .ISA_CSEL64_USE_FLAGS dst tVal fVal =>
    match st.physFlag, st.regs tVal, st.regs fVal with
    | some c, some (.v64 tv), some (.v64 fv) =>
      some { st with regs := regSet st.regs dst (.v64 (if c then tv else fv)) }
    | _, _, _ => none

/-- Evaluates a sequence of `IsaInstr`s. -/
def evalIsaBody (q : AbiQuery) (st : IsaState) :
    List IsaInstr → Option IsaState
  | [] => some st
  | i :: rest =>
    match evalIsaInstr q st i with
    | some st' => evalIsaBody q st' rest
    | none     => none

@[simp]
theorem evalIsaBody_append (q : AbiQuery) (st : IsaState)
    (xs ys : List IsaInstr) :
    evalIsaBody q st (xs ++ ys) =
      match evalIsaBody q st xs with
      | some st' => evalIsaBody q st' ys
      | none     => none := by
  induction xs generalizing st with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.cons_append, evalIsaBody]
    cases evalIsaInstr q st x with
    | none     => rfl
    | some st' => exact ih st'

/-- Evaluates a `FramedIsaProg` on an `AbiQuery`. Enforces stack-frame balance
(`st.spOffset = 0`) at function exit. -/
def evalFramedIsaProg (p : FramedIsaProg) (q : AbiQuery) : Option AbiOut :=
  match evalIsaBody q (initIsaState q) (p.prologue ++ p.body ++ p.epilogue) with
  | none => none
  | some st =>
    if st.spOffset = 0 then
      match p.ret with
      | .ISA_RET_PAIR loReg hiReg =>
        match st.regs loReg, st.regs hiReg with
        | some (.v64 lo), some (.v64 hi) =>
          some { retLo := lo, retHi := hi, heap := st.heap,
                 calleeSaved := st.calleeSavedSnap }
        | _, _ => none
      | .ISA_RET_SINGLE loReg =>
        match st.regs loReg with
        | some (.v64 lo) =>
          some { retLo := lo, retHi := 0, heap := st.heap,
                 calleeSaved := st.calleeSavedSnap }
        | _ => none
    else
      none

/-- `FramedIsaLang` packaged as an Anneal `Language AbiOut`. -/
abbrev FramedIsaLang : Language AbiOut :=
  Language.mkSimple FramedIsaProg AbiQuery AbiOut
    (fun p => Behavior.ofOption (evalFramedIsaProg p))

/-- Identity codec between `PostRaMachineLang` and `FramedIsaLang`. -/
def postRaToIsaCodec : BehaviorCodec PostRaMachineLang FramedIsaLang :=
  mkSimpleCodec
    (fun p => Behavior.ofOption (evalPostRaProg p))
    (fun p => Behavior.ofOption (evalFramedIsaProg p))

/-- Lowers a single `PostRaInstr` into an `IsaInstr` (resolving abstract
`SPILL_STORE`/`SPILL_RELOAD` frame indices into `ISA_STR_SP`/`ISA_LDR_SP`). -/
def lowerPostRaInstrToIsa : PostRaInstr → IsaInstr
  | .MOV_ABI_ARG dst ty idx     => .ISA_MOV_ABI_ARG dst ty idx
  | .MOV_REG dst src            => .ISA_MOV_REG dst src
  | .MOV_IMM64 dst imm          => .ISA_MOV_IMM64 dst imm
  | .XOR_ZERO_CLOBBER dst       => .ISA_XOR_ZERO_CLOBBER dst
  | .SPILL_STORE slot src       => .ISA_STR_SP slot src
  | .SPILL_RELOAD dst slot      => .ISA_LDR_SP dst slot
  | .ADD64_NOFLAGS dst lhs rhs  => .ISA_ADD64_NOFLAGS dst lhs rhs
  | .ADD8_NOFLAGS dst lhs rhs   => .ISA_ADD8_NOFLAGS dst lhs rhs
  | .ZEXT8_TO_64 dst src        => .ISA_ZEXT8_TO_64 dst src
  | .ADD64_SET_FLAGS dst l r    => .ISA_ADD64_SET_FLAGS dst l r
  | .ADDC64_USE_FLAGS dst l r   => .ISA_ADDC64_USE_FLAGS dst l r
  | .ADD_SHIFTED_PTR d b i sh   => .ISA_ADD_SHIFTED_PTR d b i sh
  | .LDR64 dst ptrReg           => .ISA_LDR64 dst ptrReg
  | .STR64 valReg ptrReg        => .ISA_STR64 valReg ptrReg
  | .CMP64_SET_FLAGS p l r      => .ISA_CMP64_SET_FLAGS p l r
  | .CSEL64_USE_FLAGS d t f     => .ISA_CSEL64_USE_FLAGS d t f

/-- Lowers `PostRaRet` to `IsaRet`. -/
def lowerPostRaRetToIsa : PostRaRet → IsaRet
  | .RET_PAIR lo hi => .ISA_RET_PAIR lo hi
  | .RET_SINGLE lo  => .ISA_RET_SINGLE lo

/-- Stage 5 pass (`PrologEpilogInserter` + `eliminateFrameIndex` +
`MCCodeEmitter`): wraps the lowered body in a balanced stack-frame prologue
(`[ISA_SUB_SP p.numSpillSlots]`) and epilogue (`[ISA_ADD_SP p.numSpillSlots]`). -/
def prologEpilogAndMcEncode (p : PostRaMachineProg) : FramedIsaProg := {
  prologue := [ .ISA_SUB_SP p.numSpillSlots ]
  body     := p.body.map lowerPostRaInstrToIsa
  epilogue := [ .ISA_ADD_SP p.numSpillSlots ]
  ret      := lowerPostRaRetToIsa p.ret
}

/-- Embedding of a `PostRaState` at stack depth `spOff` into `IsaState`. -/
def embedPostRaState (q : AbiQuery) (spOff : Nat) (st : PostRaState) : IsaState := {
  regs            := st.regs
  stack           := st.spills
  spOffset        := spOff
  physFlag        := st.physFlag
  heap            := st.heap
  calleeSavedSnap := q.calleeSaved
}

/-- Single-step commutation of `lowerPostRaInstrToIsa` with `embedPostRaState`. -/
theorem evalIsaInstr_lowerPostRaInstr (q : AbiQuery) (spOff : Nat)
    (st : PostRaState) (inst : PostRaInstr) :
    evalIsaInstr q (embedPostRaState q spOff st) (lowerPostRaInstrToIsa inst) =
      (evalPostRaInstr q st inst).map (embedPostRaState q spOff) := by
  cases inst with
  | MOV_ABI_ARG dst ty idx => rfl
  | MOV_REG dst src =>
    simp only [lowerPostRaInstrToIsa, evalIsaInstr, evalPostRaInstr, embedPostRaState]
    cases st.regs src <;> rfl
  | MOV_IMM64 dst imm => rfl
  | XOR_ZERO_CLOBBER dst => rfl
  | SPILL_STORE slot src =>
    simp only [lowerPostRaInstrToIsa, evalIsaInstr, evalPostRaInstr, embedPostRaState]
    cases st.regs src <;> rfl
  | SPILL_RELOAD dst slot =>
    simp only [lowerPostRaInstrToIsa, evalIsaInstr, evalPostRaInstr, embedPostRaState]
    cases st.spills slot <;> rfl
  | ADD64_NOFLAGS dst lhs rhs =>
    simp only [lowerPostRaInstrToIsa, evalIsaInstr, evalPostRaInstr, embedPostRaState]
    cases st.regs lhs with
    | none => rfl
    | some vL =>
      cases vL <;> try rfl
      cases st.regs rhs with
      | none => rfl
      | some vR => cases vR <;> rfl
  | ADD8_NOFLAGS dst lhs rhs =>
    simp only [lowerPostRaInstrToIsa, evalIsaInstr, evalPostRaInstr, embedPostRaState]
    cases st.regs lhs with
    | none => rfl
    | some vL =>
      cases vL <;> try rfl
      cases st.regs rhs with
      | none => rfl
      | some vR => cases vR <;> rfl
  | ZEXT8_TO_64 dst src =>
    simp only [lowerPostRaInstrToIsa, evalIsaInstr, evalPostRaInstr, embedPostRaState]
    cases st.regs src with
    | none => rfl
    | some vS => cases vS <;> rfl
  | ADD64_SET_FLAGS dst lhs rhs =>
    simp only [lowerPostRaInstrToIsa, evalIsaInstr, evalPostRaInstr, embedPostRaState]
    cases st.regs lhs with
    | none => rfl
    | some vL =>
      cases vL <;> try rfl
      cases st.regs rhs with
      | none => rfl
      | some vR => cases vR <;> rfl
  | ADDC64_USE_FLAGS dst lhs rhs =>
    simp only [lowerPostRaInstrToIsa, evalIsaInstr, evalPostRaInstr, embedPostRaState]
    cases st.regs lhs with
    | none => rfl
    | some vL =>
      cases vL <;> try rfl
      cases st.regs rhs with
      | none => rfl
      | some vR =>
        cases vR <;> try rfl
        cases st.physFlag <;> rfl
  | ADD_SHIFTED_PTR dst base idx shift =>
    simp only [lowerPostRaInstrToIsa, evalIsaInstr, evalPostRaInstr, embedPostRaState]
    cases st.regs base with
    | none => rfl
    | some vB =>
      cases vB <;> try rfl
      cases st.regs idx with
      | none => rfl
      | some vI => cases vI <;> rfl
  | LDR64 dst ptrReg =>
    simp only [lowerPostRaInstrToIsa, evalIsaInstr, evalPostRaInstr, embedPostRaState]
    cases st.regs ptrReg with
    | none => rfl
    | some vP =>
      cases vP with
      | ptr idx =>
        dsimp only
        cases heapLoad st.heap idx <;> rfl
      | _ => rfl
  | STR64 valReg ptrReg =>
    simp only [lowerPostRaInstrToIsa, evalIsaInstr, evalPostRaInstr, embedPostRaState]
    cases st.regs valReg with
    | none => rfl
    | some vV =>
      cases vV with
      | v64 v =>
        cases st.regs ptrReg with
        | none => rfl
        | some vP =>
          cases vP with
          | ptr idx =>
            dsimp only
            cases heapStore st.heap idx v <;> rfl
          | _ => rfl
      | _ => rfl
  | CMP64_SET_FLAGS pred lhs rhs =>
    simp only [lowerPostRaInstrToIsa, evalIsaInstr, evalPostRaInstr, embedPostRaState]
    cases st.regs lhs with
    | none => rfl
    | some vL =>
      cases vL <;> try rfl
      cases st.regs rhs with
      | none => rfl
      | some vR => cases vR <;> rfl
  | CSEL64_USE_FLAGS dst tVal fVal =>
    simp only [lowerPostRaInstrToIsa, evalIsaInstr, evalPostRaInstr, embedPostRaState]
    cases st.physFlag with
    | none => rfl
    | some c =>
      cases st.regs tVal with
      | none => rfl
      | some vT =>
        cases vT <;> try rfl
        cases st.regs fVal with
        | none => rfl
        | some vF => cases vF <;> rfl

/-- Multi-step commutation of `List.map lowerPostRaInstrToIsa` with
`evalPostRaBody`. -/
theorem evalIsaBody_map_lowerPostRaInstr (q : AbiQuery) (spOff : Nat)
    (st : PostRaState) (body : List PostRaInstr) :
    evalIsaBody q (embedPostRaState q spOff st) (body.map lowerPostRaInstrToIsa) =
      (evalPostRaBody q st body).map (embedPostRaState q spOff) := by
  induction body generalizing st with
  | nil => rfl
  | cons inst rest ih =>
    simp only [List.map_cons, evalIsaBody, evalPostRaBody,
               evalIsaInstr_lowerPostRaInstr]
    cases evalPostRaInstr q st inst with
    | none     => rfl
    | some st' => exact ih st'

/-- Pointwise evaluation equivalence between `evalFramedIsaProg
(prologEpilogAndMcEncode p)` and `evalPostRaProg p` for **all** `PostRaMachineProg`
`p` and **all** `AbiQuery` `q`. -/
theorem prologEpilogAndMcEncode_eval_eq (p : PostRaMachineProg) (q : AbiQuery) :
    evalFramedIsaProg (prologEpilogAndMcEncode p) q = evalPostRaProg p q := by
  unfold evalFramedIsaProg prologEpilogAndMcEncode evalPostRaProg
  simp only [List.append_assoc, evalIsaBody_append, evalIsaBody, evalIsaInstr,
             initIsaState, Nat.zero_add]
  have hInit :
      ({ regs := fun _ => none, stack := fun _ => none, spOffset := p.numSpillSlots,
         physFlag := none, heap := q.heap, calleeSavedSnap := q.calleeSaved } : IsaState) =
      embedPostRaState q p.numSpillSlots (initPostRaState q) := rfl
  rw [hInit, evalIsaBody_map_lowerPostRaInstr]
  cases evalPostRaBody q (initPostRaState q) p.body with
  | none => rfl
  | some stFinal =>
    simp only [Option.map_some, embedPostRaState,
               Nat.le_refl, ↓reduceIte, Nat.sub_self]
    cases p.ret <;> rfl

/-- **General Stage 5 Soundness Theorem (`prologEpilogAndMcEncode_compiles`)**:
For **every** `PostRaMachineProg` `p`, `prologEpilogAndMcEncode p` refines `p`
under `Trusted.Compiles`! -/
theorem prologEpilogAndMcEncode_compiles (p : PostRaMachineProg) :
    Compiles PostRaMachineLang FramedIsaLang postRaToIsaCodec
      p (prologEpilogAndMcEncode p) := by
  apply compiles_of_eval_eq
  intro q res h
  rw [prologEpilogAndMcEncode_eval_eq]
  exact h

/-- `BB-8` `PassCompiler` for Stage 5 (`PrologEpilogInserter` + `MCCodeEmitter`). -/
def prologEpilogMcCompiler :
    PassCompiler PostRaMachineLang FramedIsaLang postRaToIsaCodec where
  compile p := some (prologEpilogAndMcEncode p)
  sound s t h := by
    injection h with hEq
    subst hEq
    exact prologEpilogAndMcEncode_compiles s

/-- **Negative Stack-Frame Canary (`canary_unbalanced_stack_frame_rejected`)**:
If a buggy `PrologEpilogInserter` allocates 2 stack words (`ISA_SUB_SP 2`) in the
prologue but only deallocates 1 stack word (`ISA_ADD_SP 1`) in the epilogue,
`evalFramedIsaProg` rejects the execution at `ISA_RET` (`= none`) for every
`AbiQuery` `q`. -/
def buggyUnbalancedIsaProg : FramedIsaProg := {
  prologue := [ .ISA_SUB_SP 2 ]
  body     := [ .ISA_MOV_IMM64 .r0 42 ]
  epilogue := [ .ISA_ADD_SP 1 ]
  ret      := .ISA_RET_SINGLE .r0
}

theorem canary_unbalanced_stack_frame_rejected (q : AbiQuery) :
    evalFramedIsaProg buggyUnbalancedIsaProg q = none := rfl

/-!
### End-to-End 5-Stage `AnLLVM -> FramedISA` Verified Backend Pipeline

Finally, we compose all 5 backend stages (`IRTranslator`, `Legalizer` +
`ArtifactCombiner` + `RegBankSelect`, `InstructionSelect`, `RegAlloc` +
`VirtRegRewriter`, and `PrologEpilogInserter` + `MCCodeEmitter`) using
`PassCompiler.comp` (`BB-8`) and prove end-to-end semantic preservation from
`AnLlvmLang` to `FramedIsaLang`.
-/

/-- End-to-end composed `BehaviorCodec` from `AnLlvmLang` to `FramedIsaLang`. -/
def anllvmToIsaCodec : BehaviorCodec AnLlvmLang FramedIsaLang :=
  llvmToMachineCodec.comp (machineToPostRaCodec.comp postRaToIsaCodec)

/-- End-to-end `PassCompiler` composing `globalISelCompiler`,
`regAllocCompiler`, and `prologEpilogMcCompiler`. -/
def anllvmBackendCompiler :
    PassCompiler AnLlvmLang FramedIsaLang anllvmToIsaCodec :=
  globalISelCompiler.comp (regAllocCompiler.comp prologEpilogMcCompiler)

/-- Concrete end-to-end `FramedIsaProg` outputs produced by
`anllvmBackendCompiler` on both benchmark programs. -/
def isaAddU128AndU8 : FramedIsaProg :=
  prologEpilogAndMcEncode postRaAddU128AndU8

def isaGepLoadSelect : FramedIsaProg :=
  prologEpilogAndMcEncode postRaGepLoadSelect

/-- `anllvmBackendCompiler.compile` succeeds on both `llvmAddU128AndU8` and
`llvmGepLoadSelect`, producing `isaAddU128AndU8` and `isaGepLoadSelect`. -/
theorem anllvmBackendCompiler_succeeds :
    anllvmBackendCompiler.compile llvmAddU128AndU8 = some isaAddU128AndU8 ∧
    anllvmBackendCompiler.compile llvmGepLoadSelect = some isaGepLoadSelect := by
  exact ⟨rfl, rfl⟩

/-- **Main End-to-End Backend Theorem (`anllvmBackendPipeline_verified`)**:
Both `llvmAddU128AndU8` and `llvmGepLoadSelect` compile through the entire
5-stage `AnLLVM -> GlobalISel -> RegAlloc -> FramedISA` pipeline with
kernel-checked `Trusted.Compiles` behavioral refinement! -/
theorem anllvmBackendPipeline_verified :
    Compiles AnLlvmLang FramedIsaLang anllvmToIsaCodec
      llvmAddU128AndU8 isaAddU128AndU8 ∧
    Compiles AnLlvmLang FramedIsaLang anllvmToIsaCodec
      llvmGepLoadSelect isaGepLoadSelect := by
  exact ⟨anllvmBackendCompiler.sound llvmAddU128AndU8 isaAddU128AndU8 rfl,
         anllvmBackendCompiler.sound llvmGepLoadSelect isaGepLoadSelect rfl⟩

/-!
## Section 10: Axiom Footprint Verification (`#guard_msgs in #print axioms`)

Every theorem in this probe depends exclusively on `propext` and `Quot.sound`
(or no axioms at all for purely definitional theorems), with zero `sorryAx`,
zero `Lean.ofReduceBool`, and zero `Classical.choice`.
-/

/-- info: 'Anneal.BackendProbe.irTranslator_addU128AndU8_compiles' depends on axioms: [propext] -/
#guard_msgs in
#print axioms irTranslator_addU128AndU8_compiles

/-- info: 'Anneal.BackendProbe.irTranslator_gepLoadSelect_compiles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms irTranslator_gepLoadSelect_compiles

/-- info: 'Anneal.BackendProbe.legalizer_s128_and_s8_compiles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms legalizer_s128_and_s8_compiles

/-- info: 'Anneal.BackendProbe.instructionSelect_compiles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms instructionSelect_compiles

/-- info: 'Anneal.BackendProbe.checkPostRaMachine_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkPostRaMachine_sound

/-- info: 'Anneal.BackendProbe.canary_intervening_flag_clobber_between_uaddo_and_uadde_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms canary_intervening_flag_clobber_between_uaddo_and_uadde_rejected

/-- info: 'Anneal.BackendProbe.prologEpilogAndMcEncode_compiles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms prologEpilogAndMcEncode_compiles

/-- info: 'Anneal.BackendProbe.canary_unbalanced_stack_frame_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms canary_unbalanced_stack_frame_rejected

/-- info: 'Anneal.BackendProbe.anllvmBackendPipeline_verified' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms anllvmBackendPipeline_verified

end Anneal.BackendProbe

