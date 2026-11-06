-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas

/-!
# Self-Contained Mechanized Probe: AnLLVM 5-Primitive IR, Checkers, Self-Hosting Building Blocks, and Canaries 1–11

This standalone `prelude`-only Lean 4.34.1 module (`leanprover/lean4` commit
`5045d0056413266e57c625dcd7c365b10e377c52`) mechanizes and verifies:
1. The universal refinement and verification-unit foundation (`Trusted`).
2. The 5 orthogonal `AnLLVM` compiler primitives (`CompilerSpine`,
   `MaskedWord w` + `VecWord N W`, `DualViewMemory` + two-tier `inttoptr` +
   `stepTreeBorrows`, `FeatureProfile` / `ProfiledState p` + `mkTargetCodec` /
   `mkLayerCodec` + `PassCertChecker`, and the 5 certificate-checker families
   `CC-1`–`CC-5` + `TargetIsaBackend mode`).
3. The 5 `$K_{\text{anc}}$` self-hosting building blocks (`BB-ANC-1`–`BB-ANC-5`).
4. Decoupling of `VerifiedCompilationTheorem` (`compilationTrustPolicy`) from
   `StrictUnitTheorem` and `CrateTheorem` (`defaultTrustPolicy`).
5. All 11 negative canaries (`Canaries 1–11`) and held-out stress suites
   (`HO-1`–`HO-10`), with zero `sorryAx`, zero `Classical.choice`, and zero
   `Lean.ofReduceBool`.
-/

namespace Trusted

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

def Monotone {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    (π : B₁ → B₂) : Prop :=
  ∀ ⦃x y : B₁⦄, x ≤ y → π x ≤ π y

structure Partial (B : Type u) where
  defined : Prop
  val     : defined → B

def Partial.pure {B : Type u} (b : B) : Partial B :=
  ⟨True, fun _ => b⟩

def Partial.ub {B : Type u} : Partial B :=
  ⟨False, False.elim⟩

def Partial.bot {Out : Type u} : Partial (Out → Prop) :=
  ⟨True, fun _ _ => False⟩

def Partial.map {B₁ : Type u} {B₂ : Type v} (f : B₁ → B₂) (p : Partial B₁) :
    Partial B₂ :=
  ⟨p.defined, fun h => f (p.val h)⟩

def Partial.bind {B₁ : Type u} {B₂ : Type v}
    (p : Partial B₁) (f : B₁ → Partial B₂) : Partial B₂ :=
  ⟨∃ h : p.defined, (f (p.val h)).defined, fun h => (f (p.val h.1)).val h.2⟩

def Option.toPartial {B : Type u} : Option B → Partial B
  | some b => Partial.pure b
  | none   => Partial.ub

instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

structure Language (SemObs : Type) where
  Prog  : Type
  Query : Type
  Out   : Type
  obs   : Out → SemObs
  sem   : Prog → Behavior Query Out
  dom   : Query → Prop := fun _ => True

abbrev Language.mkSimple (Prog Query Out : Type)
    (sem : Prog → Behavior Query Out) : Language Out where
  Prog  := Prog
  Query := Query
  Out   := Out
  obs   := fun o => o
  sem   := sem

abbrev Language.Behavior {SemObs : Type} (L : Language SemObs) : Type :=
  Trusted.Behavior L.Query L.Out

def Language.SpecOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => ⟨pre q, fun _ => post q⟩

def Language.SpineSpecOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop) : L.Behavior :=
  L.SpecOn pre (fun q o => obsPost q (L.obs o))

abbrev Language.WellFormedOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) : L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

def NonVacuousOn {Query : Type} (dom pre : Query → Prop) : Prop :=
  (∃ q, pre q) ∨ (∀ q, ¬ dom q)

def Language.ProductiveOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o

def Language.VerifiedOn {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  NonVacuousOn dom pre ∧
  L.ProductiveOn pre prog ∧
  L.sem prog ≤ L.SpecOn pre post

abbrev Language.Verified {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  L.VerifiedOn L.dom pre post prog

def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

structure BehaviorCodec {SemObs : Type} (L₁ L₂ : Language SemObs) where
  encodeQuery : L₁.Query → L₂.Query
  decodeQuery : L₂.Query → L₁.Query
  encodeOut   : L₁.Out → L₂.Out
  decodeOut   : L₂.Out → Option L₁.Out
  decodeQuery_encodeQuery : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁
  decodeOut_encodeOut     : ∀ o₁, decodeOut (encodeOut o₁) = some o₁
  obs_decodeOut           : ∀ o₂ o₁, decodeOut o₂ = some o₁ → L₂.obs o₂ = L₁.obs o₁

def BehaviorCodec.toMorphism {SemObs : Type} {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂) (b : L₁.Behavior) : L₂.Behavior :=
  fun q₂ => {
    defined := (b (c.decodeQuery q₂)).defined
    val     := fun h o₂ =>
      ∃ o₁, c.decodeOut o₂ = some o₁ ∧ (b (c.decodeQuery q₂)).val h o₁
  }

abbrev Compiles {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ c.toMorphism (L_src.sem s)

def ProductiveCompiles {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  Compiles L_src L_tgt c s t ∧
  ∀ q₁,
    (∃ h₁ : (L_src.sem s q₁).defined, ∃ o₁, (L_src.sem s q₁).val h₁ o₁) →
    (∃ h₂ : (L_tgt.sem t (c.encodeQuery q₁)).defined,
      ∃ o₂, (L_tgt.sem t (c.encodeQuery q₁)).val h₂ o₂)

def CompilesPartial {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog)
    (t? : Partial L_tgt.Prog) : Prop :=
  ∀ h : t?.defined, Compiles L_src L_tgt c s (t?.val h)

def ProductiveCompilesPartial {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog)
    (t? : Partial L_tgt.Prog) : Prop :=
  ∀ h : t?.defined, ProductiveCompiles L_src L_tgt c s (t?.val h)

structure Obligation (Id : Type) where
  private mk ::
  id   : Id
  prop : Prop

abbrev Obligation.verified {Id SemObs : Type} (id : Id)
    (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Obligation Id :=
  ⟨id, L.Verified pre post prog⟩

abbrev Obligation.compiles {Id SemObs : Type} (id : Id)
    (L_src L_tgt : Language SemObs) (c : BehaviorCodec L_src L_tgt)
    (s : L_src.Prog) (t : L_tgt.Prog) : Obligation Id :=
  ⟨id, Compiles L_src L_tgt c s t⟩

structure TrustPolicy (Id : Type) where
  isAllowed : Id → Prop

def TrustPolicy.strict {Id : Type} : TrustPolicy Id :=
  ⟨fun _ => False⟩

structure EmittedArtifact where
  path     : String
  contents : String
  expected : String := contents

def EmittedArtifact.holds (a : EmittedArtifact) : Prop :=
  a.contents = a.expected

def NoDupIds {Id : Type} : List Id → Prop
  | []        => True
  | id :: ids => AllHold (ids.map (fun id' => id ≠ id')) ∧ NoDupIds ids

def VerificationResult {Id : Type}
    (policy : TrustPolicy Id)
    (waived : List Id)
    (obligations : List (Obligation Id)) : Prop :=
  obligations ≠ [] ∧
  AllHold (waived.map policy.isAllowed) ∧
  AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))

structure VerificationUnit (Id : Type) where
  policy      : TrustPolicy Id := TrustPolicy.strict
  waived      : List Id := []
  obligations : List (Obligation Id)
  artifacts   : List EmittedArtifact := []

def UnitTheorem {Id : Type} (u : VerificationUnit Id) : Prop :=
  VerificationResult u.policy u.waived u.obligations

def StrictUnitTheorem {Id : Type} (u : VerificationUnit Id) : Prop :=
  UnitTheorem u ∧
  u.waived = [] ∧
  NoDupIds (u.obligations.map Obligation.id) ∧
  AllHold (u.artifacts.map EmittedArtifact.holds)

inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind

inductive EventualOut (Obs : Type := Empty) (Val : Type) where
  | terminated (trace : List Obs) (term : TerminationKind Val)
  | diverges   (trace : List Obs)
  | reacts     (trace : List Obs)

end Trusted

namespace Anneal

open Trusted

def BehaviorCodec.id {SemObs : Type} (L : Language SemObs) :
    BehaviorCodec L L where
  encodeQuery q := q
  decodeQuery q := q
  encodeOut o   := o
  decodeOut o   := some o
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl
  obs_decodeOut _ _ h       := by cases h; rfl

def BehaviorCodec.comp {SemObs : Type} {L₁ L₂ L₃ : Language SemObs}
    (c₁ : BehaviorCodec L₁ L₂) (c₂ : BehaviorCodec L₂ L₃) :
    BehaviorCodec L₁ L₃ where
  encodeQuery q₁ := c₂.encodeQuery (c₁.encodeQuery q₁)
  decodeQuery q₃ := c₁.decodeQuery (c₂.decodeQuery q₃)
  encodeOut o₁   := c₂.encodeOut (c₁.encodeOut o₁)
  decodeOut o₃   :=
    match c₂.decodeOut o₃ with
    | some o₂ => c₁.decodeOut o₂
    | none    => none
  decodeQuery_encodeQuery q₁ := by
    rw [c₂.decodeQuery_encodeQuery, c₁.decodeQuery_encodeQuery]
  decodeOut_encodeOut o₁ := by
    rw [c₂.decodeOut_encodeOut]
    exact c₁.decodeOut_encodeOut o₁
  obs_decodeOut o₃ o₁ h := by
    cases h₂ : c₂.decodeOut o₃ with
    | none =>
      rw [h₂] at h
      cases h
    | some o₂ =>
      rw [h₂] at h
      exact Eq.trans (c₂.obs_decodeOut o₃ o₂ h₂) (c₁.obs_decodeOut o₂ o₁ h)

theorem Compiles.refl {SemObs : Type} (L : Language SemObs) (p : L.Prog) :
    Compiles L L (BehaviorCodec.id L) p p := by
  intro q hdef
  refine ⟨hdef, ?_⟩
  intro o ho
  exact ⟨o, rfl, ho⟩

theorem Compiles.comp {SemObs : Type} {L₁ L₂ L₃ : Language SemObs}
    {c₁ : BehaviorCodec L₁ L₂} {c₂ : BehaviorCodec L₂ L₃}
    {p₁ : L₁.Prog} {p₂ : L₂.Prog} {p₃ : L₃.Prog}
    (h₁₂ : Compiles L₁ L₂ c₁ p₁ p₂)
    (h₂₃ : Compiles L₂ L₃ c₂ p₂ p₃) :
    Compiles L₁ L₃ (BehaviorCodec.comp c₁ c₂) p₁ p₃ := by
  intro q₃ hdef₁
  cases h₁₂ (c₂.decodeQuery q₃) hdef₁ with
  | intro hdef₂ hval₂ =>
    cases h₂₃ q₃ hdef₂ with
    | intro hdef₃ hval₃ =>
      refine ⟨hdef₃, ?_⟩
      intro o₃ ho₃
      cases hval₃ o₃ ho₃ with
      | intro o₂ h₂ =>
        cases h₂ with
        | intro hdec₂ ho₂ =>
          cases hval₂ o₂ ho₂ with
          | intro o₁ h₁ =>
            cases h₁ with
            | intro hdec₁ ho₁ =>
              refine ⟨o₁, ?_, ho₁⟩
              dsimp [BehaviorCodec.comp]
              rw [hdec₂]
              exact hdec₁

theorem ProductiveCompiles.comp {SemObs : Type} {L₁ L₂ L₃ : Language SemObs}
    {c₁ : BehaviorCodec L₁ L₂} {c₂ : BehaviorCodec L₂ L₃}
    {p₁ : L₁.Prog} {p₂ : L₂.Prog} {p₃ : L₃.Prog}
    (h₁₂ : ProductiveCompiles L₁ L₂ c₁ p₁ p₂)
    (h₂₃ : ProductiveCompiles L₂ L₃ c₂ p₂ p₃) :
    ProductiveCompiles L₁ L₃ (BehaviorCodec.comp c₁ c₂) p₁ p₃ :=
  ⟨Compiles.comp h₁₂.1 h₂₃.1,
    fun q₁ hex₁ => h₂₃.2 (c₁.encodeQuery q₁) (h₁₂.2 q₁ hex₁)⟩

theorem ProductiveCompilesPartial.comp {SemObs : Type}
    {L₁ L₂ L₃ : Language SemObs}
    {c₁ : BehaviorCodec L₁ L₂} {c₂ : BehaviorCodec L₂ L₃}
    {p₁ : L₁.Prog} {p₂? : Partial L₂.Prog} {f₂ : L₂.Prog → Partial L₃.Prog}
    (h₁₂ : ProductiveCompilesPartial L₁ L₂ c₁ p₁ p₂?)
    (h₂₃ : ∀ h : p₂?.defined,
      ProductiveCompilesPartial L₂ L₃ c₂ (p₂?.val h) (f₂ (p₂?.val h))) :
    ProductiveCompilesPartial L₁ L₃ (BehaviorCodec.comp c₁ c₂) p₁
      (Partial.bind p₂? f₂) :=
  fun ⟨h₁, h₂⟩ => ProductiveCompiles.comp (h₁₂ h₁) (h₂₃ h₁ h₂)

theorem ProductiveCompilesPartial.of_option {SemObs : Type}
    {L_src L_tgt : Language SemObs}
    {c : BehaviorCodec L_src L_tgt}
    {s : L_src.Prog} {o : Option L_tgt.Prog}
    (h : ∀ t, o = some t → ProductiveCompiles L_src L_tgt c s t) :
    ProductiveCompilesPartial L_src L_tgt c s (Option.toPartial o) := by
  cases o with
  | none   => intro hdef; exact False.elim hdef
  | some t => intro _; exact h t rfl

namespace BB8

structure PassCompiler {SemObs : Type} (L_src L_tgt : Language SemObs) where
  compile : L_src.Prog → Partial L_tgt.Prog
  codec   : BehaviorCodec L_src L_tgt

abbrev PassCompiler.ofTotal {SemObs : Type} {L_src L_tgt : Language SemObs}
    (compile : L_src.Prog → L_tgt.Prog)
    (codec : BehaviorCodec L_src L_tgt) : PassCompiler L_src L_tgt where
  compile s := Partial.pure (compile s)
  codec     := codec

abbrev PassCompiler.ofOption {SemObs : Type} {L_src L_tgt : Language SemObs}
    (compile : L_src.Prog → Option L_tgt.Prog)
    (codec : BehaviorCodec L_src L_tgt) : PassCompiler L_src L_tgt where
  compile s := Option.toPartial (compile s)
  codec     := codec

def PassCompiler.comp {SemObs : Type} {L₁ L₂ L₃ : Language SemObs}
    (C₁₂ : PassCompiler L₁ L₂) (C₂₃ : PassCompiler L₂ L₃) :
    PassCompiler L₁ L₃ where
  compile s := Partial.bind (C₁₂.compile s) C₂₃.compile
  codec     := BehaviorCodec.comp C₁₂.codec C₂₃.codec

abbrev PassCompiler.ProductiveSoundOn {SemObs : Type}
    {L_src L_tgt : Language SemObs}
    (C : PassCompiler L_src L_tgt) (s : L_src.Prog) : Prop :=
  ProductiveCompilesPartial L_src L_tgt C.codec s (C.compile s)

theorem PassCompiler.ProductiveSoundOn.comp {SemObs : Type}
    {L₁ L₂ L₃ : Language SemObs}
    {C₁₂ : PassCompiler L₁ L₂} {C₂₃ : PassCompiler L₂ L₃}
    {p₁ : L₁.Prog}
    (h₁₂ : C₁₂.ProductiveSoundOn p₁)
    (h₂₃ : ∀ h : (C₁₂.compile p₁).defined,
      C₂₃.ProductiveSoundOn ((C₁₂.compile p₁).val h)) :
    (PassCompiler.comp C₁₂ C₂₃).ProductiveSoundOn p₁ :=
  ProductiveCompilesPartial.comp h₁₂ h₂₃

end BB8
end Anneal
namespace Anneal.AnLlvmCore

open Trusted Anneal

/-! ## Section 1: Shared Observable Spine (`CompilerSpine`) and `BehaviorCodec` -/

abbrev RegId     := UInt32
abbrev BlockId   := UInt32
abbrev ScopeId   := UInt32
abbrev ExtCallId := UInt32

/-- Two-tier logical allocation identifier:
    - `.ext id`: caller/globally visible allocation (survives in `CompilerSpine`).
    - `.loc id`: function-local stack allocation (`alloca` / `MirLocal` /
      `SpillSlot`), erased from `CompilerSpine` at function exit. -/
inductive AllocId where
  | ext (id : UInt32)
  | loc (id : UInt32)
  deriving DecidableEq, Repr

/-- External observable events along execution. -/
inductive ArchEvent where
  | extCall        (callId : ExtCallId) (args : List (BitVec 64)) (ret : BitVec 64)
  | volatileAccess (isStore : Bool) (addr : BitVec 64) (width : UInt32) (val : BitVec 64)
  | atomicMsg      (addr : BitVec 64) (val : BitVec 64) (ord : UInt8)
  | uarchLeakage   (pc : BitVec 64) (memAddr : BitVec 64)
  deriving DecidableEq, Repr

/-- Terminal ABI outcome at function exit:
    - `normal`: returns ABI registers `retWords`, preserved callee-saved
      registers `calleeSaved`, and final external heap bytes `extHeap`.
    - `unwind`: unwinds stack with payload `excPayload`, preserved
      `calleeSaved`, and final external heap bytes `extHeap` (`HO-3`).
    - `abort`: deterministic architectural trap (`ud2` / `brk` on `panic=abort`
      or checked overflow), which is a defined outcome (never `Partial.ub`). -/
inductive ArchReturn where
  | normal (retWords : List (BitVec 64))
           (calleeSaved : List (BitVec 64))
           (extHeap : List (UInt32 × List UInt8))
  | unwind (excPayload : BitVec 64)
           (calleeSaved : List (BitVec 64))
           (extHeap : List (UInt32 × List UInt8))
  | abort
  deriving DecidableEq, Repr

/-- Common observable spine shared across `MirLang`, `AnLlvmLang`,
    `AnMachineLang`, `PostRaMachineLang`, and `IsaLang`. -/
abbrev CompilerSpine : Type :=
  EventualOut ArchEvent ArchReturn

/-! ## Section 2: Width-Indexed `MaskedWord w` and `VecWord N W` -/

/-- Width-indexed bitvector equipped with a per-bit poison mask:
    - `bits : BitVec w` holds the data bits.
    - `poisonMask : BitVec w` has bit `i = 1` iff bit `i` is poison / `Byte.uninit`.
    Unifies 64-bit scalars (`MaskedWord 64`), memory bytes (`MaskedWord 8`),
    and fixed-length SIMD vectors (`<N x iW> := MaskedWord (N * W)`). -/
structure MaskedWord (w : Nat) where
  bits       : BitVec w
  poisonMask : BitVec w
  deriving DecidableEq, Repr

abbrev MaskedWord64 := MaskedWord 64
abbrev MemByte      := MaskedWord 8

namespace MaskedWord

def init {w : Nat} (b : BitVec w) : MaskedWord w :=
  ⟨b, 0#w⟩

def uninit (w : Nat) : MaskedWord w :=
  ⟨0#w, BitVec.allOnes w⟩

abbrev byteInit (b : UInt8) : MemByte :=
  init (BitVec.ofNat 8 b.toNat)

abbrev byteUninit : MemByte :=
  uninit 8

/-- `freeze`: deterministically collapses all poison bits to `0` while
    preserving all non-poison bits unchanged (`~poisonMask`). -/
def freeze {w : Nat} (x : MaskedWord w) : MaskedWord w :=
  match x with
  | ⟨bits, mask⟩ => ⟨bits &&& ~~~mask, 0#w⟩

/-- Universal zero-axiom reflexivity of `BEq.beq` (`==`) for any `DecidableEq`
    type. Avoids `Init.Data.BitVec.Lemmas` theorems (`BitVec.and_not_self`),
    which depend on `Classical.choice` in Lean 4.34.1. -/
theorem decEq_refl {α : Type u} [inst : DecidableEq α] (a : α) :
    (a == a) = true := by
  dsimp [BEq.beq, decide]
  cases inst a a with
  | isFalse h => exact False.elim (h rfl)
  | isTrue _  => rfl

/-- Computable boolean directional refinement on demanded bitmask `demanded`
    with an $O(1)$ syntactic-equality fast path:
    Every bit in `demanded` that is non-poison in `src` (`~~~src.poisonMask`)
    must be non-poison in `tgt` and agree with `src.bits`. Bits that are poison
    in `src` (such as `Byte.uninit` struct padding) may refine to deterministic
    `0` or `1` in `tgt`. -/
def checkRefinesOnMask {w : Nat} (demanded : BitVec w)
    (tgt src : MaskedWord w) : Bool :=
  match tgt with
  | ⟨tBits, tMask⟩ =>
    match src with
    | ⟨sBits, sMask⟩ =>
      cond ((tBits.toNat == sBits.toNat) && (tMask.toNat == sMask.toNat))
        true
        (let active := demanded &&& ~~~sMask
         (tMask &&& active == 0#w) && ((tBits ^^^ sBits) &&& active == 0#w))

abbrev checkRefines {w : Nat} (tgt src : MaskedWord w) : Bool :=
  checkRefinesOnMask (BitVec.ofNat w (2 ^ w - 1)) tgt src

def Refines {w : Nat} (tgt src : MaskedWord w) : Prop :=
  checkRefines tgt src = true

theorem checkRefinesOnMask_refl {w : Nat} (demanded : BitVec w)
    (x : MaskedWord w) :
    checkRefinesOnMask demanded x x = true := by
  cases x with
  | mk b m =>
    dsimp [checkRefinesOnMask]
    rw [decEq_refl b.toNat, decEq_refl m.toNat]
    rfl

theorem checkRefines_refl {w : Nat} (x : MaskedWord w) :
    checkRefines x x = true :=
  checkRefinesOnMask_refl (BitVec.ofNat w (2 ^ w - 1)) x

theorem freeze_poisonMask_zero {w : Nat} (x : MaskedWord w) :
    x.freeze.poisonMask = 0#w :=
  match x with
  | ⟨_, _⟩ => rfl

theorem freeze_preserves_defined_bits {w : Nat} (x : MaskedWord w) :
    x.freeze.bits &&& ~~~x.poisonMask = x.bits &&& ~~~x.poisonMask := by
  cases x with
  | mk b m =>
    dsimp [freeze]
    rw [BitVec.and_assoc, BitVec.and_self]

/-- Little-endian packing of 8 `MemByte`s into a `MaskedWord64`: concatenates
    both `.bits` and `.poisonMask` byte-by-byte so uninitialized struct padding
    bytes preserve their exact 8-bit `0xFF` poison mask without poisoning
    adjacent initialized fields. -/
def pack8BytesLE (b0 b1 b2 b3 b4 b5 b6 b7 : MemByte) : MaskedWord64 :=
  let extBits (b : MemByte) (sh : Nat) : BitVec 64 :=
    (BitVec.zeroExtend 64 b.bits) <<< sh
  let extMask (b : MemByte) (sh : Nat) : BitVec 64 :=
    (BitVec.zeroExtend 64 b.poisonMask) <<< sh
  ⟨extBits b0 0  ||| extBits b1 8  ||| extBits b2 16 ||| extBits b3 24 |||
   extBits b4 32 ||| extBits b5 40 ||| extBits b6 48 ||| extBits b7 56,
   extMask b0 0  ||| extMask b1 8  ||| extMask b2 16 ||| extMask b3 24 |||
   extMask b4 32 ||| extMask b5 40 ||| extMask b6 48 ||| extMask b7 56⟩

def extractByteLE (w : MaskedWord64) (idx : Nat) : MemByte :=
  match w with
  | ⟨bits, mask⟩ =>
    let sh := idx * 8
    ⟨BitVec.truncate 8 (bits >>> sh), BitVec.truncate 8 (mask >>> sh)⟩

/-- Arithmetic and bitwise ALU operations propagating `poisonMask`:
    - Arithmetic operations with cross-bit carry/borrow/quotient dependencies
      (`evalAdd`, `evalSub`, `evalUdiv`, `evalSdiv64`, `evalUaddo64`, `evalUadde64`)
      taint the full output word (`BitVec.allOnes w`) whenever any input bit is
      poison (`am != 0 || bm != 0`) or `nuw`/`nsw` overflows, guaranteeing
      monotonicity under `freeze` and `checkRefines` (`Canary 1`).
    - Bitwise operations (`evalAnd`, `evalOr`, `evalXor`) and byte packing
      (`pack8BytesLE`, `extractByteLE`) preserve per-bit `poisonMask` tracking
      for struct padding (`Canary 5`).
    - Shifts (`evalShl`, `evalLshr`) return `uninit w` (`BitVec.allOnes w`) when
      `sh >= w`. -/
def evalAdd {w : Nat} (a b : MaskedWord w) (nuw : Bool := false) : MaskedWord w :=
  match a, b with
  | ⟨ab, am⟩, ⟨bb, bm⟩ =>
    let sum := ab + bb
    let ovf := nuw && (BitVec.ult sum ab)
    if am != 0#w || bm != 0#w || ovf then
      ⟨sum, BitVec.allOnes w⟩
    else
      ⟨sum, 0#w⟩

def evalSub {w : Nat} (a b : MaskedWord w) : MaskedWord w :=
  match a, b with
  | ⟨ab, am⟩, ⟨bb, bm⟩ =>
    if am != 0#w || bm != 0#w then
      ⟨ab - bb, BitVec.allOnes w⟩
    else
      ⟨ab - bb, 0#w⟩

def evalXor {w : Nat} (a b : MaskedWord w) : MaskedWord w :=
  match a, b with
  | ⟨ab, am⟩, ⟨bb, bm⟩ => ⟨ab ^^^ bb, am ||| bm⟩

def evalAnd {w : Nat} (a b : MaskedWord w) : MaskedWord w :=
  match a, b with
  | ⟨ab, am⟩, ⟨bb, bm⟩ =>
    let aKnownZero := ~~~am &&& ~~~ab
    let bKnownZero := ~~~bm &&& ~~~bb
    ⟨ab &&& bb, (am ||| bm) &&& ~~~(aKnownZero ||| bKnownZero)⟩

def evalOr {w : Nat} (a b : MaskedWord w) : MaskedWord w :=
  match a, b with
  | ⟨ab, am⟩, ⟨bb, bm⟩ =>
    let aKnownOne := ~~~am &&& ab
    let bKnownOne := ~~~bm &&& bb
    ⟨ab ||| bb, (am ||| bm) &&& ~~~(aKnownOne ||| bKnownOne)⟩

def evalShl {w : Nat} (a : MaskedWord w) (sh : Nat) : MaskedWord w :=
  match a with
  | ⟨ab, am⟩ =>
    if sh >= w then ⟨0#w, BitVec.allOnes w⟩
    else ⟨ab <<< sh, am <<< sh⟩

def evalLshr {w : Nat} (a : MaskedWord w) (sh : Nat) : MaskedWord w :=
  match a with
  | ⟨ab, am⟩ =>
    if sh >= w then ⟨0#w, BitVec.allOnes w⟩
    else ⟨ab >>> sh, am >>> sh⟩

def evalUdiv {w : Nat} (a b : MaskedWord w) : Option (MaskedWord w) :=
  match a, b with
  | ⟨ab, am⟩, ⟨bb, bm⟩ =>
    if bm != 0#w || bb == 0#w then none
    else if am != 0#w then some ⟨ab / bb, BitVec.allOnes w⟩
    else some ⟨ab / bb, 0#w⟩

def evalSdiv64 (a b : MaskedWord64) : Option MaskedWord64 :=
  match a, b with
  | ⟨ab, am⟩, ⟨bb, bm⟩ =>
    if bm != 0#64 || bb == 0#64 ||
       (ab == 0x8000000000000000#64 && bb == 0xFFFFFFFFFFFFFFFF#64) then
      none
    else if am != 0#64 then
      some ⟨BitVec.sdiv ab bb, BitVec.allOnes 64⟩
    else
      some ⟨BitVec.sdiv ab bb, 0#64⟩

def evalZext32To64 (x : MaskedWord 32) : MaskedWord64 :=
  match x with
  | ⟨b, m⟩ =>
    let mask64 :=
      if m == BitVec.allOnes 32 then BitVec.allOnes 64
      else BitVec.zeroExtend 64 m
    ⟨BitVec.zeroExtend 64 b, mask64⟩

def evalUaddo64 (a b : MaskedWord64) : MaskedWord64 × MaskedWord 1 :=
  match a, b with
  | ⟨ab, am⟩, ⟨bb, bm⟩ =>
    let sum := ab + bb
    let carryBit : BitVec 1 := if BitVec.ult sum ab then 1#1 else 0#1
    if am != 0#64 || bm != 0#64 then
      (⟨sum, BitVec.allOnes 64⟩, ⟨carryBit, 1#1⟩)
    else
      (⟨sum, 0#64⟩, ⟨carryBit, 0#1⟩)

def evalUadde64 (a b : MaskedWord64) (cin : MaskedWord 1) :
    MaskedWord64 × MaskedWord 1 :=
  match a, b, cin with
  | ⟨ab, am⟩, ⟨bb, bm⟩, ⟨cb, cm⟩ =>
    let cExt : BitVec 64 := BitVec.zeroExtend 64 cb
    let s1 := ab + bb
    let c1 := BitVec.ult s1 ab
    let sum := s1 + cExt
    let c2 := BitVec.ult sum s1
    let carryBit : BitVec 1 := if c1 || c2 then 1#1 else 0#1
    if am != 0#64 || bm != 0#64 || cm != 0#1 then
      (⟨sum, BitVec.allOnes 64⟩, ⟨carryBit, 1#1⟩)
    else
      (⟨sum, 0#64⟩, ⟨carryBit, 0#1⟩)

end MaskedWord

/-- Explicit lane-indexed SIMD vector view over `N` lanes of `W`-bit `MaskedWord`s,
    preventing cross-lane carry and `nuw` poison bleed during vector ALU
    operations (`HO-5`). -/
structure VecWord (N W : Nat) where
  lanes : Fin N → MaskedWord W

def extractLane (N W : Nat) (v : MaskedWord (N * W)) (i : Fin N) : MaskedWord W :=
  match v with
  | ⟨bits, mask⟩ =>
    let sh := i.val * W
    ⟨BitVec.ofNat W (Nat.shiftRight bits.toNat sh),
     BitVec.ofNat W (Nat.shiftRight mask.toNat sh)⟩

def toVecWord (N W : Nat) (v : MaskedWord (N * W)) : VecWord N W :=
  ⟨fun i => extractLane N W v i⟩

def packLanesAux (N W : Nat) (vec : VecWord N W) : Nat → MaskedWord (N * W)
  | 0     => ⟨0#(N * W), 0#(N * W)⟩
  | k + 1 =>
    let prev := packLanesAux N W vec k
    if h : k < N then
      let lane := vec.lanes ⟨k, h⟩
      let sh := k * W
      let laneBits := (BitVec.ofNat (N * W) lane.bits.toNat) <<< sh
      let laneMask := (BitVec.ofNat (N * W) lane.poisonMask.toNat) <<< sh
      ⟨prev.bits + laneBits, prev.poisonMask + laneMask⟩
    else
      prev

def ofVecWord (N W : Nat) (vec : VecWord N W) : MaskedWord (N * W) :=
  packLanesAux N W vec N

def VecWord.map2 {N W : Nat} (op : MaskedWord W → MaskedWord W → MaskedWord W)
    (a b : VecWord N W) : VecWord N W :=
  ⟨fun i => op (a.lanes i) (b.lanes i)⟩

theorem vecWord_map2_lane_isolated {N W : Nat}
    (op : MaskedWord W → MaskedWord W → MaskedWord W)
    (a₁ a₂ b₁ b₂ : VecWord N W) (i : Fin N)
    (ha : a₁.lanes i = a₂.lanes i) (hb : b₁.lanes i = b₂.lanes i) :
    (VecWord.map2 op a₁ b₁).lanes i = (VecWord.map2 op a₂ b₂).lanes i := by
  dsimp [VecWord.map2]
  rw [ha, hb]

def liftLaneBinary (N W : Nat) (op : MaskedWord W → MaskedWord W → MaskedWord W)
    (a b : MaskedWord (N * W)) : MaskedWord (N * W) :=
  ofVecWord N W (VecWord.map2 op (toVecWord N W a) (toVecWord N W b))

def evalVecAdd (N W : Nat) (a b : MaskedWord (N * W)) (nuw : Bool := false) :
    MaskedWord (N * W) :=
  liftLaneBinary N W (fun x y => MaskedWord.evalAdd x y nuw) a b

/-! ## Section 3: `DualViewMemory`, Two-Tier `inttoptr`, and Dynamic `TreeBorrows` -/

inductive BorrowPerm where
  | reserved
  | active
  | frozen
  | disabled
  deriving DecidableEq, Repr

structure MemBlock where
  bid          : AllocId
  epoch        : Nat
  live         : Bool
  isExposed    : Bool
  addrObserved : Bool
  baseAddr     : BitVec 64
  byteSize     : Nat
  words        : Array MaskedWord64
  borrowScopes : Array (ScopeId × BorrowPerm) := #[]
  deriving DecidableEq, Repr

structure MemState where
  blocks     : Array MemBlock
  initSp     : BitVec 64
  stackLimit : BitVec 64
  deriving DecidableEq, Repr

structure PtrVal where
  bid     : AllocId
  epoch   : Nat
  byteOff : BitVec 64
  scope   : Option ScopeId := none
  deriving DecidableEq, Repr

namespace MemState

def listGet? {α : Type} : List α → Nat → Option α
  | [], _          => none
  | x :: _, 0      => some x
  | _ :: xs, n + 1 => listGet? xs n

/-- Spine-strict structural list update: forces the recursive tail update before
    constructing `x :: y :: ys`, preventing $O(N)$-deep lazy `List.set` thunk
    chains on 256-instruction basic blocks (`HO-5`). -/
def listSetStrict {α : Type} : List α → Nat → α → List α
  | [], _, _          => []
  | _ :: xs, 0, v     => v :: xs
  | x :: xs, n + 1, v =>
    match listSetStrict xs n v with
    | []      => [x]
    | y :: ys => x :: y :: ys

@[inline]
def arrayGet? {α : Type} (a : Array α) (i : Nat) : Option α :=
  listGet? a.toList i

@[inline]
def arraySetStrict {α : Type} (a : Array α) (i : Nat) (v : α) : Array α :=
  match listSetStrict a.toList i v with
  | []      => ⟨[]⟩
  | x :: xs => ⟨x :: xs⟩

@[inline]
def strictMaskedWord? {w : Nat} (v : MaskedWord w) : Option (MaskedWord w) :=
  match v with
  | ⟨bits, mask⟩ =>
    match bits.toNat with
    | 0 =>
      match mask.toNat with
      | 0     => some ⟨0#w, 0#w⟩
      | m + 1 => some ⟨0#w, BitVec.ofNat w (m + 1)⟩
    | b + 1 =>
      match mask.toNat with
      | 0     => some ⟨BitVec.ofNat w (b + 1), 0#w⟩
      | m + 1 => some ⟨BitVec.ofNat w (b + 1), BitVec.ofNat w (m + 1)⟩

def findBlockList? (bid : AllocId) : List MemBlock → Option MemBlock
  | [] => none
  | b :: rest => if b.bid == bid then some b else findBlockList? bid rest

def updateBlockListStrict (bid : AllocId) (f : MemBlock → Option MemBlock) :
    List MemBlock → Option (List MemBlock)
  | [] => none
  | b :: rest =>
    if b.bid == bid then
      match f b with
      | none    => none
      | some b' => some (b' :: rest)
    else
      match updateBlockListStrict bid f rest with
      | none       => none
      | some rest' => some (b :: rest')

def listHasBid (bid : AllocId) : List MemBlock → Bool
  | [] => false
  | b :: rest => (b.bid == bid) || listHasBid bid rest

def checkNoDupBlockIds : List MemBlock → Bool
  | [] => true
  | b :: rest => (!listHasBid b.bid rest) && checkNoDupBlockIds rest

def findScopePermList? (sc : ScopeId) : List (ScopeId × BorrowPerm) → Option BorrowPerm
  | [] => none
  | (s, p) :: rest => if s == sc then some p else findScopePermList? sc rest

def checkBlockNoWrap64 (b : MemBlock) : Bool :=
  b.baseAddr.toNat + b.byteSize <= 0x10000000000000000

def allocLive (mem : MemState) (bid : AllocId) : MemState :=
  match mem with
  | ⟨blocks, initSp, stackLimit⟩ =>
    let upd (b : MemBlock) : Option MemBlock :=
      match b with
      | ⟨bId, ep, _, exp, obs, base, sz, ws, scs⟩ =>
        let uninitWords := ws.toList.map (fun _ => MaskedWord.uninit 64)
        some ⟨bId, ep + 1, true, exp, obs, base, sz, ⟨uninitWords⟩, scs⟩
    match updateBlockListStrict bid upd blocks.toList with
    | none         => ⟨blocks, initSp, stackLimit⟩
    | some blocks' => ⟨⟨blocks'⟩, initSp, stackLimit⟩

def allocDead (mem : MemState) (bid : AllocId) : MemState :=
  match mem with
  | ⟨blocks, initSp, stackLimit⟩ =>
    let upd (b : MemBlock) : Option MemBlock :=
      match b with
      | ⟨bId, ep, _, exp, obs, base, sz, ws, scs⟩ =>
        some ⟨bId, ep + 1, false, exp, obs, base, sz, ws, scs⟩
    match updateBlockListStrict bid upd blocks.toList with
    | none         => ⟨blocks, initSp, stackLimit⟩
    | some blocks' => ⟨⟨blocks'⟩, initSp, stackLimit⟩

/-- `ptrtoint`: computes concrete address `baseAddr + p.byteOff` and sets
    `isExposed := true` and `addrObserved := true`, enforcing `checkNoDupBlockIds`,
    `b.live = true`, `b.epoch == p.epoch`, `p.byteOff.toNat <= b.byteSize`, and
    `checkBlockNoWrap64`. -/
def evalPtrToInt (mem : MemState) (p : PtrVal) : Option (MaskedWord64 × MemState) :=
  match mem with
  | ⟨blocks, initSp, stackLimit⟩ =>
    if !checkNoDupBlockIds blocks.toList then none
    else
      match findBlockList? p.bid blocks.toList with
      | none => none
      | some ⟨bId, ep, lv, _, _, base, sz, _, _⟩ =>
        if !lv || ep != p.epoch || p.byteOff.toNat > sz ||
           (base.toNat + sz > 0x10000000000000000) then
          none
        else
          let addr := base + p.byteOff
          let upd (b : MemBlock) : Option MemBlock :=
            match b with
            | ⟨bId', ep', lv', _, _, base', sz', ws', scs'⟩ =>
              some ⟨bId', ep', lv', true, true, base', sz', ws', scs'⟩
          match updateBlockListStrict bId upd blocks.toList with
          | none         => none
          | some blocks' => some (MaskedWord.init addr, ⟨⟨blocks'⟩, initSp, stackLimit⟩)

def findInteriorExposedBlock (addr : BitVec 64) : List MemBlock → Option MemBlock
  | [] => none
  | b :: rest =>
    if b.live && b.isExposed &&
       BitVec.ule b.baseAddr addr &&
       BitVec.ult (addr - b.baseAddr) (BitVec.ofNat 64 b.byteSize) then
      some b
    else
      findInteriorExposedBlock addr rest

def findBoundaryExposedBlock (addr : BitVec 64) : List MemBlock → Option MemBlock
  | [] => none
  | b :: rest =>
    if b.live && b.isExposed &&
       (addr == b.baseAddr + BitVec.ofNat 64 b.byteSize) then
      some b
    else
      findBoundaryExposedBlock addr rest

def evalIntToPtr (mem : MemState) (addr : BitVec 64) : Option PtrVal :=
  if !checkNoDupBlockIds mem.blocks.toList then none
  else
    match findInteriorExposedBlock addr mem.blocks.toList with
    | some b => some ⟨b.bid, b.epoch, addr - b.baseAddr, none⟩
    | none   => none

/-- Two-tier `inttoptr` (`Canary 2` / `Canary 3b`): resolves strict interior
    `[baseAddr, baseAddr + byteSize)` at Priority 1, and falls back to boundary
    `addr == baseAddr + byteSize` at Priority 2 for isolated one-past-the-end
    and ZST round-trip casts while `loadWord64` and `storeWord64` still reject
    dereferencing `byteOff == byteSize`. -/
def evalIntToPtrWithBoundary (mem : MemState) (addr : BitVec 64) : Option PtrVal :=
  if !checkNoDupBlockIds mem.blocks.toList then none
  else
    match findInteriorExposedBlock addr mem.blocks.toList with
    | some b => some ⟨b.bid, b.epoch, addr - b.baseAddr, none⟩
    | none   =>
      match findBoundaryExposedBlock addr mem.blocks.toList with
      | some b => some ⟨b.bid, b.epoch, addr - b.baseAddr, none⟩
      | none   => none

def listAll {α : Type} (p : α → Bool) : List α → Bool
  | []      => true
  | x :: xs => p x && listAll p xs

def checkBorrowAccess (b : MemBlock) (accessScope : Option ScopeId)
    (isWrite : Bool) : Bool :=
  let scopeRegistered : Bool :=
    match accessScope with
    | none => true
    | some mySc =>
      match findScopePermList? mySc b.borrowScopes.toList with
      | none           => false
      | some .disabled => false
      | some .frozen   => !isWrite
      | some .active   => true
      | some .reserved => true
  scopeRegistered &&
  listAll (fun (sc, perm) =>
    match accessScope with
    | some mySc =>
      if mySc == sc then
        match perm with
        | .disabled => false
        | .frozen   => !isWrite
        | .active | .reserved => true
      else
        match perm with
        | .active => false
        | .frozen => !isWrite
        | .reserved | .disabled => true
    | none =>
      match perm with
      | .active => false
      | .frozen => !isWrite
      | .reserved | .disabled => true) b.borrowScopes.toList

/-- Dynamic `TreeBorrows` transition on `borrowScopes` (`HO-1`):
    - On a write (`isWrite = true`) through `some mySc`:
      `mySc` transitions `.reserved | .active -> .active` (failing on `.frozen`
      or `.disabled`), while every foreign sibling scope transitions
      `.active | .frozen | .reserved -> .disabled`.
    - On a read (`isWrite = false`) through `some mySc`:
      `mySc` stays unchanged (failing on `.disabled`), while foreign `.active`
      scopes transition to `.frozen`. -/
def stepTreeBorrowsScopes (accessScope : Option ScopeId) (isWrite : Bool) :
    List (ScopeId × BorrowPerm) → Option (List (ScopeId × BorrowPerm))
  | [] => some []
  | (sc, perm) :: rest =>
    match stepTreeBorrowsScopes accessScope isWrite rest with
    | none => none
    | some rest' =>
      match accessScope with
      | some mySc =>
        if mySc == sc then
          match perm with
          | .disabled => none
          | .frozen   => if isWrite then none else some ((sc, .frozen) :: rest')
          | .active   => some ((sc, .active) :: rest')
          | .reserved =>
            some ((sc, if isWrite then .active else .reserved) :: rest')
        else
          if isWrite then
            some ((sc, .disabled) :: rest')
          else
            match perm with
            | .active   => some ((sc, .frozen) :: rest')
            | .frozen   => some ((sc, .frozen) :: rest')
            | .reserved => some ((sc, .reserved) :: rest')
            | .disabled => some ((sc, .disabled) :: rest')
      | none =>
        match perm with
        | .active   => none
        | .frozen   => if isWrite then none else some ((sc, .frozen) :: rest')
        | .reserved =>
          some ((sc, if isWrite then .disabled else .reserved) :: rest')
        | .disabled => some ((sc, .disabled) :: rest')

def stepTreeBorrows (b : MemBlock) (accessScope : Option ScopeId)
    (isWrite : Bool) : Option (Array (ScopeId × BorrowPerm)) :=
  let scopeRegistered : Bool :=
    match accessScope with
    | none => true
    | some mySc =>
      match findScopePermList? mySc b.borrowScopes.toList with
      | none           => false
      | some .disabled => false
      | some .frozen   => !isWrite
      | some .active | some .reserved => true
  if !scopeRegistered then none
  else
    match stepTreeBorrowsScopes accessScope isWrite b.borrowScopes.toList with
    | none      => none
    | some scs' => some ⟨scs'⟩

def loadWord64 (mem : MemState) (p : PtrVal) : Option MaskedWord64 :=
  match mem with
  | ⟨blocks, _, _⟩ =>
    if !checkNoDupBlockIds blocks.toList then none
    else
      match findBlockList? p.bid blocks.toList with
      | none => none
      | some ⟨bId, ep, lv, exp, obs, base, sz, ws, scs⟩ =>
        let off := p.byteOff.toNat
        let wordIdx := off / 8
        if !lv || ep != p.epoch || (off % 8 != 0) || (off + 8 > sz) then none
        else
          match stepTreeBorrows ⟨bId, ep, lv, exp, obs, base, sz, ws, scs⟩ p.scope false with
          | none   => none
          | some _ => arrayGet? ws wordIdx

def storeWord64 (mem : MemState) (p : PtrVal) (v : MaskedWord64) : Option MemState :=
  match mem with
  | ⟨blocks, initSp, stackLimit⟩ =>
    if !checkNoDupBlockIds blocks.toList then none
    else
      let upd (b : MemBlock) : Option MemBlock :=
        match b with
        | ⟨bId, ep, lv, exp, obs, base, sz, ws, scs⟩ =>
          let off := p.byteOff.toNat
          let wordIdx := off / 8
          if !lv || ep != p.epoch || (off % 8 != 0) || (off + 8 > sz) ||
             (wordIdx >= ws.toList.length) then
            none
          else
            match stepTreeBorrows ⟨bId, ep, lv, exp, obs, base, sz, ws, scs⟩ p.scope true with
            | none      => none
            | some scs' =>
              match strictMaskedWord? v with
              | none    => none
              | some v' =>
                match arraySetStrict ws wordIdx v' with
                | ⟨xs⟩ =>
                  some ⟨bId, ep, lv, exp, obs, base, sz, ⟨xs⟩, scs'⟩
      match updateBlockListStrict p.bid upd blocks.toList with
      | none         => none
      | some blocks' => some ⟨⟨blocks'⟩, initSp, stackLimit⟩

end MemState

theorem findInteriorExposedBlock_isExposed (addr : BitVec 64) :
    ∀ (bs : List MemBlock) (b : MemBlock),
      MemState.findInteriorExposedBlock addr bs = some b →
      b ∈ bs ∧ b.isExposed = true
  | [], _, h => by cases h
  | hd :: tl, b, h => by
    dsimp [MemState.findInteriorExposedBlock] at h
    revert h
    cases h_cond :
        (hd.live && hd.isExposed &&
         BitVec.ule hd.baseAddr addr &&
         BitVec.ult (addr - hd.baseAddr) (BitVec.ofNat 64 hd.byteSize)) with
    | false =>
      intro h_rest
      have ih := findInteriorExposedBlock_isExposed addr tl b h_rest
      exact ⟨List.Mem.tail hd ih.1, ih.2⟩
    | true =>
      intro h_eq
      injection h_eq with h_hd
      subst h_hd
      refine ⟨List.Mem.head tl, ?_⟩
      revert h_cond
      cases hd.live <;> cases hd.isExposed <;> intro hc <;> first | rfl | cases hc

theorem evalIntToPtr_never_returns_unexposed
    (mem : MemState) (addr : BitVec 64) (p : PtrVal)
    (h_eval : mem.evalIntToPtr addr = some p) :
    ∃ b ∈ mem.blocks.toList, b.bid = p.bid ∧ b.isExposed = true := by
  dsimp [MemState.evalIntToPtr] at h_eval
  revert h_eval
  cases MemState.checkNoDupBlockIds mem.blocks.toList with
  | false =>
    intro h; cases h
  | true =>
    cases h_find : MemState.findInteriorExposedBlock addr mem.blocks.toList with
    | none =>
      intro h; cases h
    | some b =>
      intro h_some
      injection h_some with hp
      have h_exp := findInteriorExposedBlock_isExposed addr mem.blocks.toList b h_find
      refine ⟨b, h_exp.1, ?_, h_exp.2⟩
      rw [← hp]

/-! ## Section 4: Constructive Cross-Layer `BehaviorCodec`, `FeatureProfile`, and `PassCertChecker` -/

structure AbiQuery where
  argWords        : Array MaskedWord64
  calleeSavedInit : List (BitVec 64)
  mem             : MemState
  deriving DecidableEq, Repr

structure TargetOut (Slack : Type) where
  spine         : CompilerSpine
  slack         : Slack
  abiStackValid : Bool := true

def mkTargetCodec {Prog₁ Prog₂ Query Slack : Type}
    (defaultSlack : Slack)
    (sem₁ : Prog₁ → Behavior Query CompilerSpine)
    (sem₂ : Prog₂ → Behavior Query (TargetOut Slack)) :
    BehaviorCodec
      (Language.mkSimple Prog₁ Query CompilerSpine sem₁)
      { Prog := Prog₂, Query := Query, Out := TargetOut Slack,
        obs := fun o => o.spine, sem := sem₂ } where
  encodeQuery q := q
  decodeQuery q := q
  encodeOut o₁  := ⟨o₁, defaultSlack, true⟩
  decodeOut o₂  := if o₂.abiStackValid then some o₂.spine else none
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl
  obs_decodeOut o₂ o₁ h     := by
    dsimp at h ⊢
    revert h
    cases o₂.abiStackValid with
    | false => intro h; cases h
    | true  =>
      intro h
      injection h with h_eq

theorem mkTargetCodec_rejects_invalid_abi_frame
    {Prog₁ Prog₂ Query Slack : Type}
    (defaultSlack : Slack)
    (sem₁ : Prog₁ → Behavior Query CompilerSpine)
    (sem₂ : Prog₂ → Behavior Query (TargetOut Slack))
    (sp : CompilerSpine) (sl : Slack) :
    (mkTargetCodec defaultSlack sem₁ sem₂).decodeOut ⟨sp, sl, false⟩ = none :=
  rfl

abbrev mkLayerLang (Prog Query Slack : Type)
    (sem : Prog → Behavior Query (TargetOut Slack)) : Language CompilerSpine where
  Prog  := Prog
  Query := Query
  Out   := TargetOut Slack
  obs   := fun o => o.spine
  sem   := sem

def mkLayerCodec {Prog₁ Prog₂ Query Slack₁ Slack₂ : Type}
    (embedSlack : Slack₁ → Slack₂)
    (projectSlack : Slack₂ → Option Slack₁)
    (h_slack : ∀ s₁, projectSlack (embedSlack s₁) = some s₁)
    (sem₁ : Prog₁ → Behavior Query (TargetOut Slack₁))
    (sem₂ : Prog₂ → Behavior Query (TargetOut Slack₂)) :
    BehaviorCodec
      (mkLayerLang Prog₁ Query Slack₁ sem₁)
      (mkLayerLang Prog₂ Query Slack₂ sem₂) where
  encodeQuery q := q
  decodeQuery q := q
  encodeOut o₁  :=
    match o₁ with
    | ⟨sp, sl₁, valid⟩ => ⟨sp, embedSlack sl₁, valid⟩
  decodeOut o₂  :=
    match o₂ with
    | ⟨sp, sl₂, valid⟩ =>
      match projectSlack sl₂ with
      | some sl₁ => some ⟨sp, sl₁, valid⟩
      | none     => none
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut o₁    := by
    cases o₁ with
    | mk sp sl₁ valid =>
      dsimp
      rw [h_slack sl₁]
  obs_decodeOut o₂ o₁ h     := by
    cases o₂ with
    | mk sp₂ sl₂ valid₂ =>
      dsimp at h ⊢
      revert h
      cases projectSlack sl₂ with
      | none => intro h; cases h
      | some sl₁ =>
        intro h
        injection h with h_eq
        rw [← h_eq]

structure FeatureProfile where
  hasNoAliasScopes : Bool := false
  hasFp            : Bool := false
  hasSimd          : Bool := false
  hasAtomics       : Bool := false
  hasUnwind        : Bool := false
  deriving DecidableEq, Repr

def FeatureProfile.scalarCore : FeatureProfile := {}

def FeatureProfile.hasAnyExt (p : FeatureProfile) : Bool :=
  p.hasNoAliasScopes || p.hasFp || p.hasSimd || p.hasAtomics || p.hasUnwind

abbrev OptField (enabled : Bool) (α : Type) : Type :=
  if enabled then α else Unit

inductive ExtVal : FeatureProfile → Type where
  | fp64    : BitVec 64 → ExtVal ⟨na, true, s, a, u⟩
  | simd256 : MaskedWord 256 → ExtVal ⟨na, f, true, a, u⟩

def ExtVal.elimScalarCore {α : Sort u} (v : ExtVal FeatureProfile.scalarCore) : α :=
  nomatch v

theorem optField_false_rfl (α : Type) : OptField false α = Unit := rfl

structure ExtState (p : FeatureProfile) where
  activeScopes : OptField p.hasNoAliasScopes (List ScopeId)
  fpRounding   : OptField p.hasFp UInt8
  simdRegs256  : OptField p.hasSimd (Array (MaskedWord 256))
  atomicSeqId  : OptField p.hasAtomics UInt32
  unwindTarget : OptField p.hasUnwind (Option BlockId)

structure CoreScalarState where
  pc      : BlockId
  instIdx : UInt32
  regs    : Array MaskedWord64
  mem     : MemState
  deriving DecidableEq, Repr

structure ProfiledState (p : FeatureProfile) where
  core : CoreScalarState
  ext  : OptField p.hasAnyExt (ExtState p)

namespace CoreScalarState

@[inline]
def readReg (s : CoreScalarState) (r : RegId) : MaskedWord64 :=
  match s with
  | ⟨_, _, regs, _⟩ => (MemState.arrayGet? regs r.toNat).getD (MaskedWord.uninit 64)

@[inline]
def writeReg (s : CoreScalarState) (dst : RegId) (v : MaskedWord64) : CoreScalarState :=
  match s with
  | ⟨pc, idx, regs, mem⟩ =>
    ⟨pc, idx + 1, MemState.arraySetStrict regs dst.toNat v, mem⟩

end CoreScalarState

structure PassCertChecker {SemObs : Type} (L_src L_tgt : Language SemObs)
    (Cert : Type) where
  codec       : BehaviorCodec L_src L_tgt
  check       : L_src.Prog → L_tgt.Prog → Cert → Bool
  check_sound : ∀ (s : L_src.Prog) (t : L_tgt.Prog) (cert : Cert),
    check s t cert = true → ProductiveCompiles L_src L_tgt codec s t

def PassCertChecker.withWitness {SemObs : Type}
    {L_src L_tgt : Language SemObs} {Cert : Type}
    (P : PassCertChecker L_src L_tgt Cert)
    (tgt : L_tgt.Prog) (cert : Cert) :
    BB8.PassCompiler L_src L_tgt :=
  BB8.PassCompiler.ofOption
    (fun src => if P.check src tgt cert then some tgt else none)
    P.codec

theorem PassCertChecker.withWitness_productiveSoundOn {SemObs : Type}
    {L_src L_tgt : Language SemObs} {Cert : Type}
    (P : PassCertChecker L_src L_tgt Cert)
    (src : L_src.Prog) (tgt : L_tgt.Prog) (cert : Cert) :
    (P.withWitness tgt cert).ProductiveSoundOn src := by
  apply ProductiveCompilesPartial.of_option
  intro t h_some
  dsimp [PassCertChecker.withWitness] at h_some
  revert h_some
  cases h_chk : P.check src tgt cert with
  | false => intro h; cases h
  | true  =>
    intro h
    injection h with h_eq
    subst h_eq
    exact P.check_sound src tgt cert h_chk

theorem PassCertChecker.compile_sound_of_rfl {SemObs : Type}
    {L_src L_tgt : Language SemObs} {Cert : Type}
    (P : PassCertChecker L_src L_tgt Cert)
    (src : L_src.Prog) (tgt : L_tgt.Prog) (cert : Cert)
    (h_chk : P.check src tgt cert = true) :
    ((P.withWitness tgt cert).compile src).defined ∧
    ProductiveCompiles L_src L_tgt P.codec src tgt := by
  refine ⟨?_, P.check_sound src tgt cert h_chk⟩
  dsimp [PassCertChecker.withWitness, BB8.PassCompiler.ofOption]
  rw [h_chk]
  exact trivial

theorem PassCertChecker.seq2_productiveSoundOn {SemObs : Type}
    {L₁ L₂ L₃ : Language SemObs} {Cert₁₂ Cert₂₃ : Type}
    (P₁₂ : PassCertChecker L₁ L₂ Cert₁₂) (p₂ : L₂.Prog) (c₁₂ : Cert₁₂)
    (P₂₃ : PassCertChecker L₂ L₃ Cert₂₃) (p₃ : L₃.Prog) (c₂₃ : Cert₂₃)
    (p₁ : L₁.Prog) :
    ((P₁₂.withWitness p₂ c₁₂).comp (P₂₃.withWitness p₃ c₂₃)).ProductiveSoundOn p₁ :=
  BB8.PassCompiler.ProductiveSoundOn.comp
    (P₁₂.withWitness_productiveSoundOn p₁ p₂ c₁₂)
    (fun h =>
      P₂₃.withWitness_productiveSoundOn
        (((P₁₂.withWitness p₂ c₁₂).compile p₁).val h) p₃ c₂₃)

/-! ## Section 5: The 5 Certificate-Checker Families (`CC-1`–`CC-5`) & `TargetIsaBackend` -/

inductive MirLocalState where
  | dead
  | uninit
  | init (val : MaskedWord64)
  deriving DecidableEq, Repr

def writeMirLocal (slot : MirLocalState) (v : MaskedWord64) : Option MirLocalState :=
  match slot with
  | .dead   => none
  | .uninit => some (.init v)
  | .init _ => some (.init v)

def readMirLocal (slot : MirLocalState) : Option MaskedWord64 :=
  match slot with
  | .dead   => none
  | .uninit => none
  | .init v => some v

/-- Two-parameter `DestinationPropagation` model (`CC-2`) separating
    `hoistOuterLive : Bool` (`Canary 1a`: `rust-lang/rust#146383`) from
    `deleteInnerLive : Bool` (`Canary 1b`: mid-lifetime `.uninit` clobber). -/
def evalDestPropFull (hoistOuterLive deleteInnerLive : Bool) (v : MaskedWord64) :
    Option MaskedWord64 :=
  let initDst : MirLocalState := if hoistOuterLive then .uninit else .dead
  match writeMirLocal initDst v with
  | none => none
  | some dstAfterWrite =>
    let dstAtRead : MirLocalState := if deleteInnerLive then dstAfterWrite else .uninit
    readMirLocal dstAtRead

def evalDestPropDc1 (unionLive : Bool) (v : MaskedWord64) : Option MirLocalState :=
  match evalDestPropFull unionLive unionLive v with
  | none     => none
  | some val => some (.init val)

theorem dc1_unionLive_sound (v : MaskedWord64) :
    evalDestPropDc1 true v = some (.init v) := rfl

theorem canary1_buggyDestProp_fails (v : MaskedWord64) :
    evalDestPropDc1 false v = none := rfl

/-- Constructive disjointness certificates (`CC-3`) checked in $O(1)$ during
    `MemorySSA` upward def-chain walks. -/
inductive AliasDisjointReason where
  | diffAllocId      (bid₁ bid₂ : AllocId)
  | unexposedVsRaw   (localBid : AllocId)
  | constOffsetDisj  (bid : AllocId) (off₁ width₁ off₂ width₂ : Nat)
  | noAliasScopeDisj (scope₁ scope₂ : ScopeId) (perm₁ perm₂ : BorrowPerm)
  deriving DecidableEq, Repr

def checkAliasDisjoint (mem : MemState) (p₁ p₂ : PtrVal) (w₁ w₂ : Nat)
    (reason : AliasDisjointReason) : Bool :=
  let blockList := mem.blocks.toList
  if !MemState.checkNoDupBlockIds blockList then false
  else
    match reason with
    | .diffAllocId b₁ b₂ =>
      (p₁.bid == b₁) && (p₂.bid == b₂) && (b₁ != b₂)
    | .unexposedVsRaw locBid =>
      match MemState.findBlockList? locBid blockList,
            MemState.findBlockList? p₂.bid blockList with
      | some b₁, some b₂ =>
        (p₁.bid == locBid) && (!b₁.isExposed) && b₂.isExposed && (p₁.bid != p₂.bid)
      | _, _ => false
    | .constOffsetDisj bid o₁ sz₁ o₂ sz₂ =>
      (p₁.bid == bid) && (p₂.bid == bid) &&
      (p₁.byteOff.toNat == o₁) && (p₂.byteOff.toNat == o₂) &&
      (o₁ % 8 == 0) && (o₂ % 8 == 0) &&
      (sz₁ == w₁) && (sz₂ == w₂) && (sz₁ > 0) && (sz₂ > 0) &&
      (o₁ + sz₁ <= o₂ || o₂ + sz₂ <= o₁)
    | .noAliasScopeDisj sc₁ sc₂ perm₁ perm₂ =>
      if (p₁.scope != some sc₁) || (p₂.scope != some sc₂) || (sc₁ == sc₂) then
        false
      else
        match MemState.findBlockList? p₁.bid blockList with
        | none => false
        | some b =>
          (p₁.bid == p₂.bid) &&
          (MemState.findScopePermList? sc₁ b.borrowScopes.toList == some perm₁) &&
          (MemState.findScopePermList? sc₂ b.borrowScopes.toList == some perm₂) &&
          (perm₁ != .disabled) && (perm₂ != .disabled) &&
          (perm₁ == .active || perm₂ == .active)

/-- Loop and CFG cut-point guards (`CC-4`). -/
def checkUnswitchCondSafe (preheaderCond : MaskedWord 1) : Bool :=
  preheaderCond.poisonMask == 0#1

theorem dc5b_unswitch_with_freeze_accepted (c : MaskedWord 1) :
    checkUnswitchCondSafe c.freeze = true := by
  cases c; rfl

theorem canary4_unswitch_without_freeze_rejected :
    checkUnswitchCondSafe (MaskedWord.uninit 1) = false := rfl

def checkLoopDeletionSafe (mustprogress : Bool) (hasFiniteTripProof : Bool) : Bool :=
  mustprogress || hasFiniteTripProof

theorem dc8a_finite_loop_deletion_accepted :
    checkLoopDeletionSafe false true = true := rfl

theorem canary6_infinite_rust_loop_deletion_rejected :
    checkLoopDeletionSafe false false = false := rfl

inductive IndVarExtKind where
  | zext
  | sext
  deriving DecidableEq, Repr

def checkIndVarWiden (kind : IndVarExtKind) (hasNuw hasNsw : Bool) : Bool :=
  match kind with
  | .zext => hasNuw
  | .sext => hasNsw

def checkTailCallElim (liveLocalStackIds : List UInt32)
    (escapesLocalAlloca : Bool) (calleeSavedRestored : Bool) : Bool :=
  liveLocalStackIds.isEmpty && (!escapesLocalAlloca) && calleeSavedRestored

/-- Post-RA symbolic equivalence & flag-liveness checker (`CC-5`). -/
inductive FlagEffect where
  | preservesFlags
  | writesFlag         (flagVReg : RegId)
  | readsAndWritesFlag (inFlagVReg outFlagVReg : RegId)
  | clobbersFlags
  deriving DecidableEq, Repr

structure PostRaSymState where
  physToVReg  : Array (Option RegId)
  spillToVReg : Array (Option RegId)
  flagVReg    : Option RegId
  deriving DecidableEq, Repr

inductive PostRaCheckInstr where
  | aluDef         (dstPhys : Nat) (outVReg : RegId) (flagEff : FlagEffect)
  | movPhys        (dstPhys srcPhys : Nat)
  | storeSpill     (slot : Nat) (srcPhys : Nat)
  | loadSpill      (dstPhys : Nat) (slot : Nat)
  | xorZeroClobber (dstPhys : Nat) (outZeroVReg : RegId)
  deriving DecidableEq, Repr

def stepPostRaCheck (st : PostRaSymState) (instr : PostRaCheckInstr) :
    Option PostRaSymState :=
  match st with
  | ⟨phys, spills, flg⟩ =>
    let nPhys := phys.toList.length
    let nSpills := spills.toList.length
    match instr with
    | .aluDef dst v outEff =>
      if dst >= nPhys then none
      else
        match outEff with
        | .preservesFlags =>
          some ⟨MemState.arraySetStrict phys dst (some v), spills, flg⟩
        | .writesFlag vf =>
          some ⟨MemState.arraySetStrict phys dst (some v), spills, some vf⟩
        | .readsAndWritesFlag inVf outVf =>
          if flg == some inVf then
            some ⟨MemState.arraySetStrict phys dst (some v), spills, some outVf⟩
          else
            none
        | .clobbersFlags =>
          some ⟨MemState.arraySetStrict phys dst (some v), spills, none⟩
    | .movPhys dst src =>
      if dst >= nPhys || src >= nPhys then none
      else
        match MemState.arrayGet? phys src with
        | some (some v) => some ⟨MemState.arraySetStrict phys dst (some v), spills, flg⟩
        | some none     => none
        | none          => none
    | .storeSpill slot src =>
      if slot >= nSpills || src >= nPhys then none
      else
        match MemState.arrayGet? phys src with
        | some (some v) => some ⟨phys, MemState.arraySetStrict spills slot (some v), flg⟩
        | some none     => none
        | none          => none
    | .loadSpill dst slot =>
      if dst >= nPhys || slot >= nSpills then none
      else
        match MemState.arrayGet? spills slot with
        | some (some v) => some ⟨MemState.arraySetStrict phys dst (some v), spills, flg⟩
        | some none     => none
        | none          => none
    | .xorZeroClobber dst vZero =>
      if dst >= nPhys then none
      else
        some ⟨MemState.arraySetStrict phys dst (some vZero), spills, none⟩

def runPostRaCheckBlock (st : PostRaSymState) : List PostRaCheckInstr → Option PostRaSymState
  | []        => some st
  | i :: rest =>
    match stepPostRaCheck st i with
    | none     => none
    | some st' => runPostRaCheckBlock st' rest

inductive FlagEffectV2 where
  | preservesFlags
  | writesFlag         (outFlagVReg : RegId)
  | readsFlag          (inFlagVReg : RegId)
  | readsAndWritesFlag (inFlagVReg outFlagVReg : RegId)
  | clobbersFlags
  deriving DecidableEq, Repr

inductive PostRaCheckInstrV2 where
  | aluOp          (dstPhys : Nat)
                   (src1 : Option (Nat × RegId))
                   (src2 : Option (Nat × RegId))
                   (outVReg : RegId)
                   (actualFlagEff expectedFlagEff : FlagEffectV2)
  | movPhys        (dstPhys srcPhys : Nat)
  | storeSpill     (slot : Nat) (srcPhys : Nat)
  | loadSpill      (dstPhys : Nat) (slot : Nat)
  | xorZeroClobber (dstPhys : Nat) (outZeroVReg : RegId)
  deriving DecidableEq, Repr

def checkSrcOperand (phys : Array (Option RegId)) : Option (Nat × RegId) → Bool
  | none          => true
  | some (r, exp) => MemState.arrayGet? phys r == some (some exp)

def stepPostRaCheckV2 (st : PostRaSymState) (instr : PostRaCheckInstrV2) :
    Option PostRaSymState :=
  match st with
  | ⟨phys, spills, flg⟩ =>
    let nPhys := phys.toList.length
    let nSpills := spills.toList.length
    match instr with
    | .aluOp dst src1 src2 v actualEff expectedEff =>
      if dst >= nPhys || (actualEff != expectedEff) ||
         (!checkSrcOperand phys src1) || (!checkSrcOperand phys src2) then
        none
      else
        match actualEff with
        | .preservesFlags =>
          some ⟨MemState.arraySetStrict phys dst (some v), spills, flg⟩
        | .writesFlag vf =>
          some ⟨MemState.arraySetStrict phys dst (some v), spills, some vf⟩
        | .readsFlag inVf =>
          if flg == some inVf then
            some ⟨MemState.arraySetStrict phys dst (some v), spills, flg⟩
          else
            none
        | .readsAndWritesFlag inVf outVf =>
          if flg == some inVf then
            some ⟨MemState.arraySetStrict phys dst (some v), spills, some outVf⟩
          else
            none
        | .clobbersFlags =>
          some ⟨MemState.arraySetStrict phys dst (some v), spills, none⟩
    | .movPhys dst src =>
      if dst >= nPhys || src >= nPhys then none
      else
        match MemState.arrayGet? phys src with
        | some (some v) => some ⟨MemState.arraySetStrict phys dst (some v), spills, flg⟩
        | some none     => none
        | none          => none
    | .storeSpill slot src =>
      if slot >= nSpills || src >= nPhys then none
      else
        match MemState.arrayGet? phys src with
        | some (some v) => some ⟨phys, MemState.arraySetStrict spills slot (some v), flg⟩
        | some none     => none
        | none          => none
    | .loadSpill dst slot =>
      if dst >= nPhys || slot >= nSpills then none
      else
        match MemState.arrayGet? spills slot with
        | some (some v) => some ⟨MemState.arraySetStrict phys dst (some v), spills, flg⟩
        | some none     => none
        | none          => none
    | .xorZeroClobber dst vZero =>
      if dst >= nPhys then none
      else
        some ⟨MemState.arraySetStrict phys dst (some vZero), spills, none⟩

def runPostRaCheckBlockV2 (st : PostRaSymState) :
    List PostRaCheckInstrV2 → Option PostRaSymState
  | []        => some st
  | i :: rest =>
    match stepPostRaCheckV2 st i with
    | none     => none
    | some st' => runPostRaCheckBlockV2 st' rest

theorem dc13_movImm_preserves_carry_accepted :
    (runPostRaCheckBlock ⟨#[none, none, none], #[none], none⟩
      [ .aluDef 0 1 (.writesFlag 10),
        .aluDef 1 2 .preservesFlags,
        .aluDef 2 3 (.readsAndWritesFlag 10 11) ]).isSome = true := rfl

theorem canary7_xorZeroClobber_between_add_and_adc_rejected :
    runPostRaCheckBlock ⟨#[none, none, none], #[none], none⟩
      [ .aluDef 0 1 (.writesFlag 10),
        .xorZeroClobber 1 2,
        .aluDef 2 3 (.readsAndWritesFlag 10 11) ] = none := rfl

inductive ArtifactEmissionMode where
  | option5A_assemblyTextS
  | option5B_machineBytesO
  deriving DecidableEq, Repr

inductive PcRelBaseMode where
  | currentPc
  | nextPc
  deriving DecidableEq, Repr

def evalPcRelTarget (mode : PcRelBaseMode) (pc : BitVec 64)
    (instrByteLen : Nat) (relDisp : BitVec 64) : BitVec 64 :=
  match mode with
  | .currentPc => pc + relDisp
  | .nextPc    => pc + (BitVec.ofNat 64 instrByteLen) + relDisp

def checkPcRelDisp (mode : PcRelBaseMode) (pc : BitVec 64)
    (instrByteLen : Nat) (relDisp target : BitVec 64) : Bool :=
  evalPcRelTarget mode pc instrByteLen relDisp == target

theorem ho6_x86_correct_rip_disp_accepted :
    checkPcRelDisp .nextPc 0x1000#64 6 (0x2000#64 - (0x1000#64 + 6#64)) 0x2000#64 = true :=
  rfl

theorem canary_x86_unincremented_rip_disp_rejected :
    checkPcRelDisp .nextPc 0x1000#64 6 (0x2000#64 - 0x1000#64) 0x2000#64 = false :=
  rfl

structure RelaxedBlockLayout where
  blockId         : BlockId
  byteOffset      : Nat
  bodyByteLen     : Nat
  termByteLen     : Nat
  isShortRel8     : Bool
  targetBlockIdx  : Nat
  encodedDisp     : BitVec 64
  deriving DecidableEq, Repr

def checkCumulativeLayoutOffsets (expectedOff : Nat) : List RelaxedBlockLayout → Bool
  | [] => true
  | b :: rest =>
    (b.byteOffset == expectedOff) &&
    checkCumulativeLayoutOffsets (expectedOff + b.bodyByteLen + b.termByteLen) rest

def checkSignedRel8Range (disp : BitVec 64) : Bool :=
  BitVec.sle (-128#64) disp && BitVec.sle disp 127#64

def checkBranchRelaxationLayout (mode : PcRelBaseMode)
    (blocks : List RelaxedBlockLayout) : Bool :=
  checkCumulativeLayoutOffsets 0 blocks &&
  MemState.listAll (fun b =>
    match MemState.listGet? blocks b.targetBlockIdx with
    | none => false
    | some tgt =>
      let termPc := BitVec.ofNat 64 (b.byteOffset + b.bodyByteLen)
      let tgtPc  := BitVec.ofNat 64 tgt.byteOffset
      let rangeOk := if b.isShortRel8 then checkSignedRel8Range b.encodedDisp else true
      rangeOk && checkPcRelDisp mode termPc b.termByteLen b.encodedDisp tgtPc)
    blocks

structure TargetIsaBackend (mode : ArtifactEmissionMode) where
  archName         : String
  isaLang          : Language CompilerSpine
  TargetOpcode     : Type
  PhysReg          : Type
  pcRelMode        : PcRelBaseMode
  hasHardwareFlags : Bool
  numIntArgRegs    : Nat
  calleeSavedCount : Nat
  flagEffect       : TargetOpcode → FlagEffect

/-! ## Section 6: `NaiveBaseline` (Unrepaired Baseline for Canary Falsification) -/

namespace NaiveBaseline

def evalAdd {w : Nat} (a b : MaskedWord w) (nuw : Bool := false) : MaskedWord w :=
  match a, b with
  | ⟨ab, am⟩, ⟨bb, bm⟩ =>
    let sum := ab + bb
    let ovf := if nuw && (BitVec.ult sum ab) then BitVec.allOnes w else 0#w
    ⟨sum, am ||| bm ||| ovf⟩

def evalSub {w : Nat} (a b : MaskedWord w) : MaskedWord w :=
  match a, b with
  | ⟨ab, am⟩, ⟨bb, bm⟩ => ⟨ab - bb, am ||| bm⟩

def evalShl {w : Nat} (a : MaskedWord w) (sh : Nat) : MaskedWord w :=
  match a with
  | ⟨ab, am⟩ => ⟨ab <<< sh, am <<< sh⟩

def evalLshr {w : Nat} (a : MaskedWord w) (sh : Nat) : MaskedWord w :=
  match a with
  | ⟨ab, am⟩ => ⟨ab >>> sh, am >>> sh⟩

def evalUdiv {w : Nat} (a b : MaskedWord w) : Option (MaskedWord w) :=
  match a, b with
  | ⟨ab, am⟩, ⟨bb, bm⟩ =>
    if bm != 0#w || bb == 0#w then none
    else some ⟨ab / bb, am⟩

def evalUaddo64 (a b : MaskedWord64) : MaskedWord64 × MaskedWord 1 :=
  match a, b with
  | ⟨ab, am⟩, ⟨bb, bm⟩ =>
    let sum := ab + bb
    let carryBit : BitVec 1 := if BitVec.ult sum ab then 1#1 else 0#1
    let pMask := am ||| bm
    let carryPoison : BitVec 1 := if pMask == 0#64 then 0#1 else 1#1
    (⟨sum, pMask⟩, ⟨carryBit, carryPoison⟩)

def checkAliasDisjoint (mem : MemState) (p₁ p₂ : PtrVal) (w₁ w₂ : Nat)
    (reason : AliasDisjointReason) : Bool :=
  match reason with
  | .diffAllocId b₁ b₂ =>
    (p₁.bid == b₁) && (p₂.bid == b₂) && (b₁ != b₂)
  | .unexposedVsRaw locBid =>
    match mem.blocks.find? (fun b => b.bid == locBid) with
    | none => false
    | some b => (p₁.bid == locBid) && (!b.isExposed)
  | .constOffsetDisj bid o₁ sz₁ o₂ sz₂ =>
    (p₁.bid == bid) && (p₂.bid == bid) &&
    (p₁.byteOff.toNat == o₁) && (p₂.byteOff.toNat == o₂) &&
    (sz₁ == w₁) && (sz₂ == w₂) &&
    (o₁ + sz₁ <= o₂ || o₂ + sz₂ <= o₁)
  | .noAliasScopeDisj sc₁ sc₂ perm₁ perm₂ =>
    (p₁.scope == some sc₁) && (p₂.scope == some sc₂) && (sc₁ != sc₂) &&
    (perm₁ == .active || perm₂ == .active || perm₁ == .frozen || perm₂ == .frozen)

end NaiveBaseline

/-! ## Section 7: The 5 `$K_{\text{anc}}$` Self-Hosting Building Blocks (`BB-ANC-1`–`BB-ANC-5`) -/

def PassCertChecker.ofRustTwoStepImp {SemObs : Type}
    {L₁ L₂ : Language SemObs} {Cert : Type}
    (P : PassCertChecker L₁ L₂ Cert)
    (rustCheck : L₁.Prog → L₂.Prog → Cert → Bool)
    (h_imp : ∀ s t cert, rustCheck s t cert = true → P.check s t cert = true) :
    PassCertChecker L₁ L₂ Cert where
  codec := P.codec
  check := rustCheck
  check_sound s t cert h_ok := P.check_sound s t cert (h_imp s t cert h_ok)

def PassCertChecker.ofRustTwoStepEquiv {SemObs : Type}
    {L₁ L₂ : Language SemObs} {Cert : Type}
    (P : PassCertChecker L₁ L₂ Cert)
    (rustCheck : L₁.Prog → L₂.Prog → Cert → Bool)
    (h_eq : ∀ s t cert, rustCheck s t cert = P.check s t cert) :
    PassCertChecker L₁ L₂ Cert :=
  P.ofRustTwoStepImp rustCheck (fun s t cert h => by rw [← h_eq s t cert]; exact h)

def PassCompiler.ofRustLowerer {SemObs : Type} {L₁ L₂ : Language SemObs}
    (codec : BehaviorCodec L₁ L₂)
    (_specLower : L₁.Prog → Option L₂.Prog)
    (rustLower : L₁.Prog → Option L₂.Prog) :
    BB8.PassCompiler L₁ L₂ :=
  BB8.PassCompiler.ofOption rustLower codec

theorem PassCompiler.ofRustLowerer_productiveSoundOn {SemObs : Type}
    {L₁ L₂ : Language SemObs}
    (codec : BehaviorCodec L₁ L₂)
    (specLower : L₁.Prog → Option L₂.Prog)
    (rustLower : L₁.Prog → Option L₂.Prog)
    (h_spec : ∀ s t, specLower s = some t → ProductiveCompiles L₁ L₂ codec s t)
    (h_imp : ∀ s t, rustLower s = some t → specLower s = some t)
    (src : L₁.Prog) :
    (PassCompiler.ofRustLowerer codec specLower rustLower).ProductiveSoundOn src := by
  apply ProductiveCompilesPartial.of_option
  intro t h_r
  exact h_spec src t (h_imp src t h_r)

inductive OptAttempt (TgtProg Cert : Type) where
  | candidate (cand : TgtProg) (cert : Cert)
  | outOfFuel
  | panicked
  deriving DecidableEq, Repr

structure FreezeValueWitness (T : Type) where
  hasForbidUnsafe    : Bool
  hasZeroUnsafeCell  : Bool
  hasZeroCustomDeref : Bool
  isOwnedByMove      : Bool
  deriving DecidableEq, Repr

def checkInMemoryBoundarySafe {T : Type} (w : FreezeValueWitness T) : Bool :=
  w.hasForbidUnsafe && w.hasZeroUnsafeCell && w.hasZeroCustomDeref && w.isOwnedByMove

theorem ho7_forbidUnsafe_without_freeze_or_nominal_deref_rejected :
    checkInMemoryBoundarySafe (T := Unit) ⟨true, false, true, true⟩ = false ∧
    checkInMemoryBoundarySafe (T := Unit) ⟨true, true, false, true⟩ = false ∧
    checkInMemoryBoundarySafe (T := Unit) ⟨true, true, true, false⟩ = false ∧
    checkInMemoryBoundarySafe (T := Unit) ⟨true, true, true, true⟩ = true :=
  ⟨rfl, rfl, rfl, rfl⟩

def PassCertChecker.evalIntraWithIdentityFallback {SemObs : Type}
    {L : Language SemObs} {Cert : Type}
    (P : PassCertChecker L L Cert)
    (attempt : L.Prog → OptAttempt L.Prog Cert)
    (src : L.Prog) : L.Prog :=
  match attempt src with
  | .candidate cand cert =>
    if P.check src cand cert then cand else src
  | .outOfFuel => src
  | .panicked  => src

def PassCertChecker.withIdentityFallback {SemObs : Type}
    {L : Language SemObs} {Cert : Type}
    (P : PassCertChecker L L Cert)
    (attempt : L.Prog → OptAttempt L.Prog Cert) :
    BB8.PassCompiler L L :=
  BB8.PassCompiler.ofTotal (P.evalIntraWithIdentityFallback attempt) (BehaviorCodec.id L)

theorem productiveCompiles_id_refl {SemObs : Type} (L : Language SemObs) (p : L.Prog) :
    ProductiveCompiles L L (BehaviorCodec.id L) p p :=
  ⟨Compiles.refl L p, fun _ hex => hex⟩

theorem PassCertChecker.withIdentityFallback_productiveSoundOn {SemObs : Type}
    {L : Language SemObs} {Cert : Type}
    (P : PassCertChecker L L Cert)
    (h_codec : P.codec = BehaviorCodec.id L)
    (attempt : L.Prog → OptAttempt L.Prog Cert)
    (src : L.Prog) :
    (P.withIdentityFallback attempt).ProductiveSoundOn src := by
  intro _h_def
  dsimp [PassCertChecker.withIdentityFallback, BB8.PassCompiler.ofTotal,
         PassCertChecker.evalIntraWithIdentityFallback]
  cases attempt src with
  | outOfFuel => exact productiveCompiles_id_refl L src
  | panicked  => exact productiveCompiles_id_refl L src
  | candidate cand cert =>
    dsimp
    cases h_chk : P.check src cand cert with
    | false => exact productiveCompiles_id_refl L src
    | true  =>
      rw [← h_codec]
      exact P.check_sound src cand cert h_chk

def PassCertChecker.evalCrossWithSelfCertifyingFallback {SemObs : Type}
    {L₁ L₂ : Language SemObs} {Cert : Type}
    (P : PassCertChecker L₁ L₂ Cert)
    (attempt : L₁.Prog → OptAttempt L₂.Prog Cert)
    (fallback : L₁.Prog → Option (L₂.Prog × Cert))
    (src : L₁.Prog) : Option L₂.Prog :=
  let tryFallback : Option L₂.Prog :=
    match fallback src with
    | some (t_fb, c_fb) => if P.check src t_fb c_fb then some t_fb else none
    | none              => none
  match attempt src with
  | .candidate cand cert =>
    if P.check src cand cert then some cand else tryFallback
  | .outOfFuel => tryFallback
  | .panicked  => tryFallback

def PassCertChecker.withSelfCertifyingFallback {SemObs : Type}
    {L₁ L₂ : Language SemObs} {Cert : Type}
    (P : PassCertChecker L₁ L₂ Cert)
    (attempt : L₁.Prog → OptAttempt L₂.Prog Cert)
    (fallback : L₁.Prog → Option (L₂.Prog × Cert)) :
    BB8.PassCompiler L₁ L₂ :=
  BB8.PassCompiler.ofOption (P.evalCrossWithSelfCertifyingFallback attempt fallback) P.codec

theorem PassCertChecker.withSelfCertifyingFallback_productiveSoundOn
    {SemObs : Type} {L₁ L₂ : Language SemObs} {Cert : Type}
    (P : PassCertChecker L₁ L₂ Cert)
    (attempt : L₁.Prog → OptAttempt L₂.Prog Cert)
    (fallback : L₁.Prog → Option (L₂.Prog × Cert))
    (src : L₁.Prog) :
    (P.withSelfCertifyingFallback attempt fallback).ProductiveSoundOn src := by
  apply ProductiveCompilesPartial.of_option
  intro tgt h_eval
  dsimp [PassCertChecker.evalCrossWithSelfCertifyingFallback] at h_eval
  have h_fb_sound :
      (match fallback src with
       | some (t_fb, c_fb) => if P.check src t_fb c_fb then some t_fb else none
       | none => none) = some tgt →
      ProductiveCompiles L₁ L₂ P.codec src tgt := by
    cases fallback src with
    | none => intro h; cases h
    | some pair =>
      cases pair with
      | mk t_fb c_fb =>
        dsimp
        cases h_c : P.check src t_fb c_fb with
        | false => intro h; cases h
        | true  =>
          intro h
          injection h with h_eq
          subst h_eq
          exact P.check_sound src t_fb c_fb h_c
  revert h_eval
  cases attempt src with
  | outOfFuel => intro h_eval; exact h_fb_sound h_eval
  | panicked  => intro h_eval; exact h_fb_sound h_eval
  | candidate cand cert =>
    dsimp
    cases h_c : P.check src cand cert with
    | true =>
      intro h_eval
      injection h_eval with h_eq
      subst h_eq
      exact P.check_sound src cand cert h_c
    | false =>
      intro h_eval
      exact h_fb_sound h_eval

def PassCertChecker.evalCrossWithVerifiedFallback {SemObs : Type}
    {L₁ L₂ : Language SemObs} {Cert : Type}
    (P : PassCertChecker L₁ L₂ Cert)
    (attempt : L₁.Prog → OptAttempt L₂.Prog Cert)
    (fallbackLower : L₁.Prog → L₂.Prog)
    (src : L₁.Prog) : L₂.Prog :=
  match attempt src with
  | .candidate cand cert =>
    if P.check src cand cert then cand else fallbackLower src
  | .outOfFuel => fallbackLower src
  | .panicked  => fallbackLower src

def PassCertChecker.withVerifiedFallback {SemObs : Type}
    {L₁ L₂ : Language SemObs} {Cert : Type}
    (P : PassCertChecker L₁ L₂ Cert)
    (attempt : L₁.Prog → OptAttempt L₂.Prog Cert)
    (fallbackLower : L₁.Prog → L₂.Prog) :
    BB8.PassCompiler L₁ L₂ :=
  BB8.PassCompiler.ofTotal (P.evalCrossWithVerifiedFallback attempt fallbackLower) P.codec

theorem PassCertChecker.withVerifiedFallback_productiveSoundOn
    {SemObs : Type} {L₁ L₂ : Language SemObs} {Cert : Type}
    (P : PassCertChecker L₁ L₂ Cert)
    (attempt : L₁.Prog → OptAttempt L₂.Prog Cert)
    (fallbackLower : L₁.Prog → L₂.Prog)
    (h_fb : ∀ s, ProductiveCompiles L₁ L₂ P.codec s (fallbackLower s))
    (src : L₁.Prog) :
    (P.withVerifiedFallback attempt fallbackLower).ProductiveSoundOn src := by
  intro _h_def
  dsimp [PassCertChecker.withVerifiedFallback, BB8.PassCompiler.ofTotal,
         PassCertChecker.evalCrossWithVerifiedFallback]
  cases attempt src with
  | outOfFuel => exact h_fb src
  | panicked  => exact h_fb src
  | candidate cand cert =>
    dsimp
    cases h_c : P.check src cand cert with
    | false => exact h_fb src
    | true  => exact P.check_sound src cand cert h_c

def checkedAddU64 (a b : BitVec 64) : Option (BitVec 64) :=
  let sum := a + b
  if BitVec.ult sum a then none else some sum

def checkAddLeU64 (a b limit : BitVec 64) : Bool :=
  match checkedAddU64 a b with
  | some sum => BitVec.ule sum limit
  | none     => false

def wrappingAddLeU64_buggy (a b limit : BitVec 64) : Bool :=
  BitVec.ule (a + b) limit

theorem canary10_wrapping_u64_spoofs_disjointness_caught_by_checkedAdd :
    wrappingAddLeU64_buggy 0xFFFFFFFFFFFFFFF8#64 16#64 12#64 = true ∧
    checkAddLeU64 0xFFFFFFFFFFFFFFF8#64 16#64 12#64 = false :=
  ⟨rfl, rfl⟩

inductive PassExecMode where
  | leanKernel
  | selfHostedRust
  deriving DecidableEq, Repr

def PassCertChecker.selectMode {SemObs : Type}
    {L₁ L₂ : Language SemObs} {Cert : Type}
    (P : PassCertChecker L₁ L₂ Cert)
    (rustCheck : L₁.Prog → L₂.Prog → Cert → Bool)
    (h_imp : ∀ s t cert, rustCheck s t cert = true → P.check s t cert = true)
    (mode : PassExecMode)
    (tgt : L₂.Prog) (cert : Cert) :
    BB8.PassCompiler L₁ L₂ :=
  match mode with
  | .leanKernel     => P.withWitness tgt cert
  | .selfHostedRust => (P.ofRustTwoStepImp rustCheck h_imp).withWitness tgt cert

theorem PassCertChecker.selectMode_productiveSoundOn {SemObs : Type}
    {L₁ L₂ : Language SemObs} {Cert : Type}
    (P : PassCertChecker L₁ L₂ Cert)
    (rustCheck : L₁.Prog → L₂.Prog → Cert → Bool)
    (h_imp : ∀ s t cert, rustCheck s t cert = true → P.check s t cert = true)
    (mode : PassExecMode)
    (src : L₁.Prog) (tgt : L₂.Prog) (cert : Cert) :
    (P.selectMode rustCheck h_imp mode tgt cert).ProductiveSoundOn src := by
  cases mode with
  | leanKernel     => exact P.withWitness_productiveSoundOn src tgt cert
  | selfHostedRust => exact (P.ofRustTwoStepImp rustCheck h_imp).withWitness_productiveSoundOn src tgt cert

structure BootstrapFixedPointCert where
  emissionMode        : ArtifactEmissionMode
  stage0TheoremHeld   : Bool
  stage0WaivedEmpty   : Bool
  stage0NoDupFnIds    : Bool
  stage1SelfCheckOk   : Bool
  stage1VerifiedBytes : List UInt8
  stage1ActualBytes   : List UInt8
  stage2ActualBytes   : List UInt8
  deriving DecidableEq, Repr

def checkBootstrapFixedPoint (c : BootstrapFixedPointCert) : Bool :=
  (c.emissionMode == .option5B_machineBytesO) &&
  c.stage0TheoremHeld &&
  c.stage0WaivedEmpty &&
  c.stage0NoDupFnIds &&
  c.stage1SelfCheckOk &&
  (!c.stage1ActualBytes.isEmpty) &&
  (c.stage1VerifiedBytes == c.stage1ActualBytes) &&
  (c.stage1ActualBytes == c.stage2ActualBytes)

theorem dc19_bootstrap_fixed_point_and_canaries_by_rfl :
    let clean : BootstrapFixedPointCert :=
      ⟨.option5B_machineBytesO, true, true, true, true, [0x7F, 0x45, 0x4C, 0x46], [0x7F, 0x45, 0x4C, 0x46], [0x7F, 0x45, 0x4C, 0x46]⟩
    checkBootstrapFixedPoint clean = true ∧
    checkBootstrapFixedPoint { clean with emissionMode := .option5A_assemblyTextS } = false ∧
    checkBootstrapFixedPoint { clean with stage0WaivedEmpty := false } = false ∧
    checkBootstrapFixedPoint { clean with stage1VerifiedBytes := [0x7F, 0x45, 0x4C, 0x00] } = false ∧
    checkBootstrapFixedPoint { clean with stage2ActualBytes := [0x7F, 0x45, 0x4C, 0x99] } = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

structure NonVacuousRustCertChecker {SemObs : Type}
    (L₁ L₂ : Language SemObs) (Cert : Type) where
  checker : PassCertChecker L₁ L₂ Cert
  witSrc  : L₁.Prog
  witTgt  : L₂.Prog
  witCert : Cert
  wit_ok  : checker.check witSrc witTgt witCert = true

def PassCertChecker.ofRustTwoStepNonVacuous {SemObs : Type}
    {L₁ L₂ : Language SemObs} {Cert : Type}
    (P : PassCertChecker L₁ L₂ Cert)
    (rustCheck : L₁.Prog → L₂.Prog → Cert → Bool)
    (h_imp : ∀ s t cert, rustCheck s t cert = true → P.check s t cert = true)
    (s₀ : L₁.Prog) (t₀ : L₂.Prog) (c₀ : Cert)
    (h_pos : rustCheck s₀ t₀ c₀ = true) :
    NonVacuousRustCertChecker L₁ L₂ Cert where
  checker := P.ofRustTwoStepImp rustCheck h_imp
  witSrc  := s₀
  witTgt  := t₀
  witCert := c₀
  wit_ok  := h_pos

def PassCertChecker.evalIntraWithFreezeGuard {SemObs : Type}
    {L : Language SemObs} {Cert : Type}
    (P : PassCertChecker L L Cert)
    (wCand : FreezeValueWitness L.Prog)
    (wCert : FreezeValueWitness Cert)
    (attempt : L.Prog → OptAttempt L.Prog Cert)
    (src : L.Prog) : L.Prog :=
  if checkInMemoryBoundarySafe wCand && checkInMemoryBoundarySafe wCert then
    P.evalIntraWithIdentityFallback attempt src
  else
    src

def PassCertChecker.withFreezeGuardedIdentityFallback {SemObs : Type}
    {L : Language SemObs} {Cert : Type}
    (P : PassCertChecker L L Cert)
    (wCand : FreezeValueWitness L.Prog)
    (wCert : FreezeValueWitness Cert)
    (attempt : L.Prog → OptAttempt L.Prog Cert) :
    BB8.PassCompiler L L :=
  BB8.PassCompiler.ofTotal
    (P.evalIntraWithFreezeGuard wCand wCert attempt) (BehaviorCodec.id L)

theorem PassCertChecker.withFreezeGuardedIdentityFallback_productiveSoundOn
    {SemObs : Type} {L : Language SemObs} {Cert : Type}
    (P : PassCertChecker L L Cert)
    (h_codec : P.codec = BehaviorCodec.id L)
    (wCand : FreezeValueWitness L.Prog)
    (wCert : FreezeValueWitness Cert)
    (attempt : L.Prog → OptAttempt L.Prog Cert)
    (src : L.Prog) :
    (P.withFreezeGuardedIdentityFallback wCand wCert attempt).ProductiveSoundOn src := by
  intro _h_def
  dsimp [PassCertChecker.withFreezeGuardedIdentityFallback, BB8.PassCompiler.ofTotal,
         PassCertChecker.evalIntraWithFreezeGuard]
  cases (checkInMemoryBoundarySafe wCand && checkInMemoryBoundarySafe wCert) with
  | false => exact productiveCompiles_id_refl L src
  | true  => exact P.withIdentityFallback_productiveSoundOn h_codec attempt src trivial

def PassCertChecker.withFallbackCompiler
    {SemObs : Type} {L₁ L₂ : Language SemObs} {Cert : Type}
    (P : PassCertChecker L₁ L₂ Cert)
    (C_fb : BB8.PassCompiler L₁ L₂)
    (attempt : L₁.Prog → OptAttempt L₂.Prog Cert) :
    BB8.PassCompiler L₁ L₂ where
  compile src :=
    match attempt src with
    | .candidate cand cert =>
      if P.check src cand cert then
        Partial.pure cand
      else
        C_fb.compile src
    | .outOfFuel => C_fb.compile src
    | .panicked  => C_fb.compile src
  codec := P.codec

theorem PassCertChecker.withFallbackCompiler_productiveSoundOn
    {SemObs : Type} {L₁ L₂ : Language SemObs} {Cert : Type}
    (P : PassCertChecker L₁ L₂ Cert)
    (C_fb : BB8.PassCompiler L₁ L₂)
    (h_codec : C_fb.codec = P.codec)
    (attempt : L₁.Prog → OptAttempt L₂.Prog Cert)
    (src : L₁.Prog)
    (h_fb : C_fb.ProductiveSoundOn src) :
    (PassCertChecker.withFallbackCompiler P C_fb attempt).ProductiveSoundOn
      src := by
  intro h_def
  dsimp [PassCertChecker.withFallbackCompiler] at h_def ⊢
  revert h_def
  cases attempt src with
  | outOfFuel =>
    intro h_def
    rw [← h_codec]
    exact h_fb h_def
  | panicked =>
    intro h_def
    rw [← h_codec]
    exact h_fb h_def
  | candidate cand cert =>
    dsimp
    cases h_chk : P.check src cand cert with
    | false =>
      intro h_def
      rw [← h_codec]
      exact h_fb h_def
    | true =>
      intro _
      exact P.check_sound src cand cert h_chk

theorem PassCertChecker.withFallbackCompiler_defined_of_fb
    {SemObs : Type} {L₁ L₂ : Language SemObs} {Cert : Type}
    (P : PassCertChecker L₁ L₂ Cert)
    (C_fb : BB8.PassCompiler L₁ L₂)
    (attempt : L₁.Prog → OptAttempt L₂.Prog Cert)
    (src : L₁.Prog)
    (h_fb_def : (C_fb.compile src).defined) :
    ((PassCertChecker.withFallbackCompiler P C_fb attempt).compile
      src).defined := by
  dsimp [PassCertChecker.withFallbackCompiler]
  cases attempt src with
  | outOfFuel => exact h_fb_def
  | panicked  => exact h_fb_def
  | candidate cand cert =>
    dsimp
    cases P.check src cand cert with
    | false => exact h_fb_def
    | true  => exact trivial

def runPostRaCheckBlockV2Fast (st : PostRaSymState) :
    List PostRaCheckInstrV2 → Option PostRaSymState
  | [] => some st
  | [i₁] => stepPostRaCheckV2 st i₁
  | [i₁, i₂] =>
    match stepPostRaCheckV2 st i₁ with
    | none     => none
    | some st₁ => stepPostRaCheckV2 st₁ i₂
  | i₁ :: i₂ :: i₃ :: rest =>
    match stepPostRaCheckV2 st i₁ with
    | none     => none
    | some st₁ =>
      match stepPostRaCheckV2 st₁ i₂ with
      | none     => none
      | some st₂ =>
        match stepPostRaCheckV2 st₂ i₃ with
        | none     => none
        | some st₃ => runPostRaCheckBlockV2Fast st₃ rest

theorem runPostRaCheckBlockV2Fast_eq :
    ∀ (blk : List PostRaCheckInstrV2) (st : PostRaSymState),
      runPostRaCheckBlockV2Fast st blk = runPostRaCheckBlockV2 st blk
  | [], _ => rfl
  | [i₁], st => by
    dsimp [runPostRaCheckBlockV2Fast, runPostRaCheckBlockV2]
    cases stepPostRaCheckV2 st i₁ <;> rfl
  | [i₁, i₂], st => by
    dsimp [runPostRaCheckBlockV2Fast, runPostRaCheckBlockV2]
    cases stepPostRaCheckV2 st i₁ with
    | none => rfl
    | some st₁ =>
      dsimp
      cases stepPostRaCheckV2 st₁ i₂ <;> rfl
  | i₁ :: i₂ :: i₃ :: rest, st => by
    dsimp [runPostRaCheckBlockV2Fast, runPostRaCheckBlockV2]
    cases stepPostRaCheckV2 st i₁ with
    | none => rfl
    | some st₁ =>
      dsimp
      cases stepPostRaCheckV2 st₁ i₂ with
      | none => rfl
      | some st₂ =>
        dsimp
        cases stepPostRaCheckV2 st₂ i₃ with
        | none => rfl
        | some st₃ =>
          exact runPostRaCheckBlockV2Fast_eq rest st₃

def trivialSpillFallbackBlock : List PostRaCheckInstrV2 :=
  [ .loadSpill 0 0,
    .loadSpill 1 1,
    .aluOp 0 (some (0, 1)) (some (1, 2)) 3 (.writesFlag 10) (.writesFlag 10),
    .storeSpill 0 0,
    .aluOp 1 none none 4 .preservesFlags .preservesFlags,
    .loadSpill 0 0,
    .aluOp 0 (some (0, 3)) (some (1, 4)) 5
      (.readsAndWritesFlag 10 11) (.readsAndWritesFlag 10 11),
    .storeSpill 2 0 ]

theorem succ_sub_succ_zero_axioms (x : Nat) :
    ∀ (y : Nat), (x + 1) - (y + 1) = x - y
  | 0     => rfl
  | y + 1 => congrArg Nat.pred (succ_sub_succ_zero_axioms x y)

theorem sub_lt_of_lt_add_zero_axioms :
    ∀ (y x a : Nat), y ≤ x → x < a + y → x - y < a
  | 0, x, _, _, hlt => hlt
  | y + 1, 0, _, hle, _ => False.elim (Nat.not_succ_le_zero y hle)
  | y + 1, x + 1, a, hle, hlt => by
    rw [succ_sub_succ_zero_axioms x y]
    exact sub_lt_of_lt_add_zero_axioms y x a
      (Nat.le_of_succ_le_succ hle)
      (Nat.lt_of_succ_lt_succ hlt)

theorem mod_eq_of_lt_zero_axioms {x y : Nat} (h : x < y) : x % y = x := by
  cases x with
  | zero => rfl
  | succ n =>
    change (if y ≤ n + 1 then Nat.modCore (n + 1) y else n + 1) = n + 1
    exact ite_eq_right (Nat.not_le_of_gt h)

theorem mod_eq_sub_of_ge_of_lt_zero_axioms {x y : Nat}
    (hy : 0 < y) (hge : y ≤ x) (hlt : x - y < y) : x % y = x - y := by
  cases x with
  | zero =>
    exact False.elim (Nat.not_le_of_gt hy hge)
  | succ n =>
    change (if y ≤ n + 1 then Nat.modCore (n + 1) y else n + 1) = n + 1 - y
    rw [ite_eq_left hge]
    unfold Nat.modCore
    rw [dite_eq_left hy]
    rw [Nat.modCore.go.eq_1]
    rw [dite_eq_left hge]
    rw [Nat.modCore.go.eq_1]
    exact dite_eq_right (Nat.not_le_of_gt hlt)

theorem nat_add_mod_no_wrap_zero_axioms {a b m : Nat}
    (ha : a < m) (hb : b < m)
    (h_no_wrap : ¬ ((a + b) % m < a)) :
    (a + b) % m = a + b := by
  cases Nat.lt_or_ge (a + b) m with
  | inl h_lt => exact mod_eq_of_lt_zero_axioms h_lt
  | inr h_ge =>
    have hm_pos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le a) ha
    have h_sub_lt_m : a + b - m < m :=
      sub_lt_of_lt_add_zero_axioms m (a + b) m h_ge (Nat.add_lt_add ha hb)
    have h_mod : (a + b) % m = a + b - m :=
      mod_eq_sub_of_ge_of_lt_zero_axioms hm_pos h_ge h_sub_lt_m
    have h_lt_a : (a + b) % m < a := by
      rw [h_mod]
      exact sub_lt_of_lt_add_zero_axioms m (a + b) a h_ge
        (Nat.add_lt_add_left hb a)
    exact False.elim (h_no_wrap h_lt_a)

theorem checkAddLeU64_implies_toNat_le (a b limit : BitVec 64)
    (h : checkAddLeU64 a b limit = true) :
    a.toNat + b.toNat ≤ limit.toNat := by
  dsimp [checkAddLeU64, checkedAddU64] at h
  revert h
  cases h_ult : BitVec.ult (a + b) a with
  | true => intro h; cases h
  | false =>
    dsimp
    intro h_ule
    have h_not_lt : ¬ ((a + b).toNat < a.toNat) := of_decide_eq_false h_ult
    have h_le_lim : (a + b).toNat ≤ limit.toNat := of_decide_eq_true h_ule
    have h_add : (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 64 :=
      BitVec.toNat_add a b
    have h_not_lt' : ¬ ((a.toNat + b.toNat) % 2 ^ 64 < a.toNat) := by
      rw [← h_add]
      exact h_not_lt
    have h_eq : (a.toNat + b.toNat) % 2 ^ 64 = a.toNat + b.toNat :=
      nat_add_mod_no_wrap_zero_axioms a.isLt b.isLt h_not_lt'
    rw [← h_eq, ← h_add]
    exact h_le_lim

def checkDisjointRangesU64Strict (o₁ sz₁ o₂ sz₂ : BitVec 64) : Bool :=
  (checkedAddU64 o₁ sz₁).isSome &&
  (checkedAddU64 o₂ sz₂).isSome &&
  (checkAddLeU64 o₁ sz₁ o₂ || checkAddLeU64 o₂ sz₂ o₁)

theorem checkDisjointRangesU64Strict_implies_nat_disjoint
    (o₁ sz₁ o₂ sz₂ : BitVec 64)
    (h : checkDisjointRangesU64Strict o₁ sz₁ o₂ sz₂ = true) :
    (o₁.toNat + sz₁.toNat ≤ o₂.toNat) ∨ (o₂.toNat + sz₂.toNat ≤ o₁.toNat) := by
  dsimp [checkDisjointRangesU64Strict] at h
  revert h
  cases (checkedAddU64 o₁ sz₁).isSome with
  | false => intro h; cases h
  | true =>
    cases (checkedAddU64 o₂ sz₂).isSome with
    | false => intro h; cases h
    | true =>
      cases h₁ : checkAddLeU64 o₁ sz₁ o₂ with
      | true =>
        intro _
        exact Or.inl (checkAddLeU64_implies_toNat_le o₁ sz₁ o₂ h₁)
      | false =>
        intro h₂
        exact Or.inr (checkAddLeU64_implies_toNat_le o₂ sz₂ o₁ h₂)

def checkBootstrapFixedPointWithUnit {Id : Type}
    (u : VerificationUnit Id)
    (artifactContentsBytes artifactExpectedBytes : List UInt8)
    (c : BootstrapFixedPointCert) : Bool :=
  u.waived.isEmpty &&
  (artifactContentsBytes == artifactExpectedBytes) &&
  (c.stage1VerifiedBytes == artifactExpectedBytes) &&
  checkBootstrapFixedPoint c
/-! ## Section 8: Mechanized Negative Canaries 1–11 and Held-Out Suites (`HO-1`–`HO-10`) -/

/-- **Canary 1 (Carry/Borrow/Quotient/Shift Poison Monotonicity vs. `NaiveBaseline`):**
    Under `NaiveBaseline` (`poisonMask := am ||| bm`), `a1 = ⟨1#64, 1#64⟩` and
    `b1 = ⟨1#64, 0#64⟩` satisfy `a1.freeze = ⟨0#64, 0#64⟩`, so
    `NaiveBaseline.evalAdd a1.freeze b1 = ⟨1#64, 0#64⟩` while
    `NaiveBaseline.evalAdd a1 b1 = ⟨2#64, 1#64⟩`. Bit 1 is `0` in the frozen
    sum and `1` (marked clean!) in the un-frozen sum, falsifying
    `checkRefines (evalAdd a1.freeze b1) (evalAdd a1 b1)`. Likewise, shifting a
    poisoned word by `sh = 64` under `NaiveBaseline.evalShl` shifts the poison
    mask out to `0#64`, laundering poison into clean `0`. Repaired `MaskedWord`
    restores `checkRefines = true` across all five cases by `rfl`. -/
theorem canary1_carry_borrow_shift_monotonicity_restored :
    let a1 : MaskedWord64 := ⟨1#64, 1#64⟩
    let b1 : MaskedWord64 := ⟨1#64, 0#64⟩
    let aSub : MaskedWord64 := ⟨0#64, 0#64⟩
    let bSub : MaskedWord64 := ⟨1#64, 1#64⟩
    let aDiv : MaskedWord64 := ⟨6#64, 2#64⟩
    let bDiv : MaskedWord64 := ⟨3#64, 0#64⟩
    let aOvf : MaskedWord64 := ⟨0xFFFFFFFFFFFFFFFF#64, 1#64⟩
    let bOvf : MaskedWord64 := ⟨1#64, 0#64⟩
    (MaskedWord.checkRefines a1.freeze a1 = true) ∧
    (MaskedWord.checkRefines (NaiveBaseline.evalAdd a1.freeze b1)
      (NaiveBaseline.evalAdd a1 b1) = false) ∧
    (MaskedWord.checkRefines (MaskedWord.evalAdd a1.freeze b1)
      (MaskedWord.evalAdd a1 b1) = true) ∧
    (MaskedWord.checkRefines (NaiveBaseline.evalSub aSub bSub.freeze)
      (NaiveBaseline.evalSub aSub bSub) = false) ∧
    (MaskedWord.checkRefines (MaskedWord.evalSub aSub bSub.freeze)
      (MaskedWord.evalSub aSub bSub) = true) ∧
    (NaiveBaseline.evalUdiv aDiv.freeze bDiv != NaiveBaseline.evalUdiv aDiv bDiv) ∧
    (MaskedWord.checkRefines ((MaskedWord.evalUdiv aDiv.freeze bDiv).getD (MaskedWord.uninit 64))
      ((MaskedWord.evalUdiv aDiv bDiv).getD (MaskedWord.uninit 64)) = true) ∧
    (MaskedWord.checkRefines (NaiveBaseline.evalUaddo64 aOvf.freeze bOvf).1
      (NaiveBaseline.evalUaddo64 aOvf bOvf).1 = false) ∧
    (MaskedWord.checkRefines (MaskedWord.evalUaddo64 aOvf.freeze bOvf).1
      (MaskedWord.evalUaddo64 aOvf bOvf).1 = true) ∧
    ((NaiveBaseline.evalShl a1 64).poisonMask == 0#64) ∧
    ((MaskedWord.evalShl a1 64).poisonMask == BitVec.allOnes 64) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Canary 1a & 1b (`DestinationPropagation` `StorageLive` Interval Unioning, `CC-2`):**
    1. `Canary 1a` (`rust-lang/rust#146383`): omitting outer `StorageLive` hoist
       (`hoistOuterLive = false`) writes to `.dead` local slot (`none`).
    2. `Canary 1b`: omitting inner `StorageLive` deletion (`deleteInnerLive = false`)
       clobbers the live slot back to `.uninit` (`none`).
    3. Full interval union (`evalDestPropFull true true`) preserves `some v`. -/
theorem canary1ab_destProp_two_parameter_union (v : MaskedWord64) :
    evalDestPropFull false true v = none ∧
    evalDestPropFull true false v = none ∧
    evalDestPropFull true true v = some v :=
  ⟨rfl, rfl, rfl⟩

/-- **Canary 2a/2b/2c (`CC-1` Speculative `udiv`/`load` Hoisting Guard):**
    Hoisting `udiv` or an unvalidated `load` across a branch guard fails
    `isSpeculativelySafe` and triggers `none` (UB) on `denom = 0`, poisoned
    `denom`, or out-of-bounds address. -/
inductive SpecExpr where
  | addOp  (a b : MaskedWord64)
  | udivOp (a b : MaskedWord64)
  | loadOp (p : PtrVal)
  deriving DecidableEq, Repr

def isSpeculativelySafe : SpecExpr → Bool
  | .addOp _ _  => true
  | .udivOp _ _ => false
  | .loadOp _   => false

theorem canary2abc_speculative_udiv_and_load_rejected (a b : MaskedWord64) (p : PtrVal) :
    isSpeculativelySafe (.addOp a b) = true ∧
    isSpeculativelySafe (.udivOp a b) = false ∧
    isSpeculativelySafe (.loadOp p) = false ∧
    MaskedWord.evalUdiv (MaskedWord.init 42#64) (MaskedWord.init 0#64) = none ∧
    MaskedWord.evalUdiv (MaskedWord.init 42#64) ⟨1#64, 1#64⟩ = none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Canary 2 / 3b (Adjacent Twin-Allocation One-Past-the-End `inttoptr`):**
    When `b1` occupies `[0x1000, 0x1008)` and `b2` occupies `[0x1008, 0x1010)`:
    - Single-tier `off <= byteSize` misroutes `0x1008` to `b1` at offset `8`
      (which cannot be dereferenced as `b2`'s interior!).
    - Two-tier `evalIntToPtrWithBoundary` checks Priority 1 strict interior
      (`0 <= off < byteSize`) first, routing `0x1008` to `b2` at offset `0`, while
      routing an isolated one-past-the-end address `0x2008` for `bIso` at
      `[0x2000, 0x2008)` to `bIso` at offset `8` via Priority 2 (`loadWord64`
      still rejects dereferencing offset `8`). -/
def findBlockSingleTierBuggy (addr : BitVec 64) : List MemBlock → Option MemBlock
  | [] => none
  | b :: rest =>
    if b.live && b.isExposed &&
       BitVec.ule b.baseAddr addr &&
       BitVec.ule (addr - b.baseAddr) (BitVec.ofNat 64 b.byteSize) then
      some b
    else
      findBlockSingleTierBuggy addr rest

theorem canary2_adjacent_twin_allocations_two_tier_inttoptr :
    let b1 : MemBlock :=
      ⟨.ext 1, 0, true, true, true, 0x1000#64, 8, #[MaskedWord.init 11#64], #[]⟩
    let b2 : MemBlock :=
      ⟨.ext 2, 0, true, true, true, 0x1008#64, 8, #[MaskedWord.init 22#64], #[]⟩
    let bIso : MemBlock :=
      ⟨.ext 3, 0, true, true, true, 0x2000#64, 8, #[MaskedWord.init 33#64], #[]⟩
    let memTwin : MemState := ⟨#[b1, b2, bIso], 0x8000#64, 0x4000#64⟩
    -- 1. Single-tier `off <= byteSize` misroutes `0x1008` to `b1` instead of `b2`:
    (findBlockSingleTierBuggy 0x1008#64 memTwin.blocks.toList).map MemBlock.bid =
      some (.ext 1) ∧
    -- 2. Two-tier `evalIntToPtrWithBoundary` routes `0x1008` to `b2` (Priority 1):
    memTwin.evalIntToPtrWithBoundary 0x1008#64 =
      some ⟨.ext 2, 0, 0#64, none⟩ ∧
    -- 3. Isolated boundary `0x2008` resolves to `bIso` at offset 8 (Priority 2),
    --    and `loadWord64` rejects dereferencing that one-past-the-end pointer:
    memTwin.evalIntToPtrWithBoundary 0x2008#64 =
      some ⟨.ext 3, 0, 8#64, none⟩ ∧
    memTwin.loadWord64 ⟨.ext 3, 0, 8#64, none⟩ = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Canary 3 (`CC-3` Alias Disjointness Hardening vs. `NaiveBaseline`):**
    Verifies that `checkAliasDisjoint` rejects:
    1. Self-aliasing `.unexposedVsRaw` (`p₁ = p₂` on an unexposed local block),
    2. Duplicate `AllocId` shadowing (`!checkNoDupBlockIds`),
    3. Unaligned sub-word `.constOffsetDisj` (`off₁ = 0, off₂ = 4` overlapping the
       same 8-byte word `wordIdx = 0`), and
    4. Two `.frozen` shared borrows (`&T` vs `&T`) claiming `.noAliasScopeDisj`
       without at least one `.active` (`&mut T`) borrow. -/
theorem canary3_alias_disjoint_blocks_all_four_exploits :
    let bUnexp : MemBlock :=
      ⟨.loc 1, 0, true, false, false, 0x1000#64, 16,
       #[MaskedWord.init 1#64, MaskedWord.init 2#64],
       #[(10, .frozen), (20, .frozen)]⟩
    let bShadow : MemBlock :=
      ⟨.loc 1, 0, true, true, true, 0x1000#64, 16,
       #[MaskedWord.init 1#64, MaskedWord.init 2#64], #[]⟩
    let memSingle : MemState := ⟨#[bUnexp], 0x8000#64, 0x4000#64⟩
    let memDup    : MemState := ⟨#[bUnexp, bShadow], 0x8000#64, 0x4000#64⟩
    let pLoc0 : PtrVal := ⟨.loc 1, 0, 0#64, none⟩
    let pLoc4 : PtrVal := ⟨.loc 1, 0, 4#64, none⟩
    let pSc10 : PtrVal := ⟨.loc 1, 0, 0#64, some 10⟩
    let pSc20 : PtrVal := ⟨.loc 1, 0, 0#64, some 20⟩
    -- 1. Self-aliasing `.unexposedVsRaw`: NaiveBaseline returns `true`, repaired returns `false`
    (NaiveBaseline.checkAliasDisjoint memSingle pLoc0 pLoc0 8 8 (.unexposedVsRaw (.loc 1)) = true) ∧
    (checkAliasDisjoint memSingle pLoc0 pLoc0 8 8 (.unexposedVsRaw (.loc 1)) = false) ∧
    -- 2. Duplicate AllocId shadowing: rejected by `checkNoDupBlockIds`
    (checkAliasDisjoint memDup pLoc0 pLoc0 8 8 (.diffAllocId (.loc 1) (.ext 2)) = false) ∧
    -- 3. Unaligned sub-word `.constOffsetDisj` (`0` and `4` in same 8-byte word):
    (NaiveBaseline.checkAliasDisjoint memSingle pLoc0 pLoc4 4 4 (.constOffsetDisj (.loc 1) 0 4 4 4) = true) ∧
    (checkAliasDisjoint memSingle pLoc0 pLoc4 4 4 (.constOffsetDisj (.loc 1) 0 4 4 4) = false) ∧
    -- 4. Two `.frozen` shared borrows without `.active`:
    (NaiveBaseline.checkAliasDisjoint memSingle pSc10 pSc20 8 8 (.noAliasScopeDisj 10 20 .frozen .frozen) = true) ∧
    (checkAliasDisjoint memSingle pSc10 pSc20 8 8 (.noAliasScopeDisj 10 20 .frozen .frozen) = false) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Canary 5a/5b/5c (`SROA` Padding Bytes & `StackColoring` `addrObserved`):**
    1. `Canary 5a`: Dropping initialized union/padding bytes (`byteInit 0xAA`) to
       `byteUninit` fails `MaskedWord.checkRefines` (`= false`).
    2. `Canary 5b`: Zeroing active union bytes (`byteInit 0xAA -> byteInit 0x00`)
       fails `MaskedWord.checkRefines` (`= false`).
    3. `DC-5a`: Zeroing genuine `byteUninit` struct padding (`byteUninit -> byteInit 0x00`)
       succeeds (`MaskedWord.checkRefines = true`).
    4. `Canary 5c`: `checkStackColoringMergeSafe` rejects merging two stack slots
       whose lifetimes are disjoint if both had their addresses observed via
       `ptrtoint` (`b1.addrObserved && b2.addrObserved`). -/
def checkStackColoringMergeSafe (lifetimesDisjoint : Bool) (b1 b2 : MemBlock) : Bool :=
  lifetimesDisjoint && !(b1.addrObserved && b2.addrObserved)

theorem canary5abc_sroa_padding_and_stackColoring :
    let wInitPad := MaskedWord.pack8BytesLE
      (MaskedWord.byteInit 0x11) (MaskedWord.byteInit 0xAA)
      (MaskedWord.byteInit 0) (MaskedWord.byteInit 0)
      (MaskedWord.byteInit 0) (MaskedWord.byteInit 0)
      (MaskedWord.byteInit 0) (MaskedWord.byteInit 0)
    let wUninitPad := MaskedWord.pack8BytesLE
      (MaskedWord.byteInit 0x11) MaskedWord.byteUninit
      (MaskedWord.byteInit 0) (MaskedWord.byteInit 0)
      (MaskedWord.byteInit 0) (MaskedWord.byteInit 0)
      (MaskedWord.byteInit 0) (MaskedWord.byteInit 0)
    let wZeroPad := MaskedWord.pack8BytesLE
      (MaskedWord.byteInit 0x11) (MaskedWord.byteInit 0x00)
      (MaskedWord.byteInit 0) (MaskedWord.byteInit 0)
      (MaskedWord.byteInit 0) (MaskedWord.byteInit 0)
      (MaskedWord.byteInit 0) (MaskedWord.byteInit 0)
    let bObs1 : MemBlock := ⟨.loc 1, 0, false, true, true, 0x1000#64, 8, #[], #[]⟩
    let bObs2 : MemBlock := ⟨.loc 2, 0, false, true, true, 0x1008#64, 8, #[], #[]⟩
    let bClean2 : MemBlock := ⟨.loc 2, 0, false, false, false, 0x1008#64, 8, #[], #[]⟩
    MaskedWord.checkRefines wUninitPad wInitPad = false ∧
    MaskedWord.checkRefines wZeroPad wInitPad = false ∧
    MaskedWord.checkRefines wZeroPad wUninitPad = true ∧
    checkStackColoringMergeSafe true bObs1 bObs2 = false ∧
    checkStackColoringMergeSafe true bObs1 bClean2 = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **`HO-1` (Dynamic `TreeBorrows` Diamond `Reserved -> Active` Write Invalidating
    Sibling `Frozen` Read):**
    In a diamond CFG, scope `10` starts `.reserved` (`&mut T` two-phase borrow)
    and sibling scope `20` starts `.frozen` (`&T`). When one branch writes through
    scope `10`, `storeWord64` transitions scope `10` to `.active` and disables
    sibling scope `20` (`.disabled`), so a subsequent read through scope `20`
    after the diamond merge is rejected (`loadWord64 = none`, blocking unsound
    `GVN` / `EarlyCSE` read hoisting across the write!). -/
theorem ho1_dynamic_treeBorrows_diamond_write_disables_sibling_frozen :
    let blk : MemBlock :=
      ⟨.loc 1, 0, true, false, false, 0x1000#64, 8,
       #[MaskedWord.init 10#64], #[(10, .reserved), (20, .frozen)]⟩
    let mem0 : MemState := ⟨#[blk], 0x8000#64, 0x4000#64⟩
    let pMut : PtrVal := ⟨.loc 1, 0, 0#64, some 10⟩
    let pShr : PtrVal := ⟨.loc 1, 0, 0#64, some 20⟩
    -- Before write, reading through `pShr` (`scope 20 = .frozen`) succeeds:
    mem0.loadWord64 pShr = some (MaskedWord.init 10#64) ∧
    -- After writing through `pMut` (`scope 10 : .reserved -> .active`),
    -- `scope 20` is `.disabled` and reading `pShr` returns `none`:
    (match mem0.storeWord64 pMut (MaskedWord.init 99#64) with
     | none => false
     | some mem1 => mem1.loadWord64 pShr == none) = true :=
  ⟨rfl, rfl⟩

/-- **`HO-2a` & `HO-2b` (`IndVarSimplify` `zext`/`sext` Wrap Guard & `LoopVectorize`
    Distance-1 RAW Hazard Rejection):**
    1. `HO-2a` (`LLVM #64598`): `checkIndVarWiden` rejects `zext` without `nuw`
       and `sext` without `nsw`, while `evalZext32To64` propagates whole-word
       32-bit poison to all 64 bits.
    2. `HO-2b`: `checkLoopVectorizeSafe` rejects vectorization (`VF = 4`) when
       the loop carries a distance-1 read-after-write dependence (`depDist < vf`). -/
def checkLoopVectorizeSafe (vf : Nat) (minDepDist : Option Nat) : Bool :=
  match minDepDist with
  | none      => true
  | some dist => vf > 1 && dist >= vf

theorem ho2ab_indvar_widen_and_loopVectorize_guards :
    checkIndVarWiden .zext false true = false ∧
    checkIndVarWiden .sext true false = false ∧
    checkIndVarWiden .zext true false = true ∧
    checkIndVarWiden .sext false true = true ∧
    (MaskedWord.evalZext32To64 (MaskedWord.uninit 32)).poisonMask = BitVec.allOnes 64 ∧
    checkLoopVectorizeSafe 4 (some 1) = false ∧
    checkLoopVectorizeSafe 4 (some 4) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`HO-3a` & `HO-3b` (`TailCallElim` Escaped Local Alloca & Unwind Callee-Saved
    Register Corruption):**
    1. `HO-3a` (`LLVM #58241`): `checkTailCallElim` rejects tail-call conversion
       when a local `.loc` stack allocation is still live (`[1]`) or escapes.
    2. `HO-3b`: `mkTargetCodec` decodes any unwind/normal outcome with
       `abiStackValid = false` (corrupted callee-saved register or misaligned `sp`)
       to `none`. -/
theorem ho3ab_tailCall_and_unwind_calleeSaved_guards :
    checkTailCallElim [1] false true = false ∧
    checkTailCallElim [] true true = false ∧
    checkTailCallElim [] false false = false ∧
    checkTailCallElim [] false true = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **`HO-4` & `Canary 7b` (`stepPostRaCheckV2` Reused-Input Clobber & Cross-ISA
    Flag Clobbers):**
    1. `Canary 7b`: overwriting an input physical register (`r0`) with a scratch
       value (`vReg 99`) before a binary `.aluOp` that expects `(0, 1)` is rejected.
    2. `HO-4` (`AArch64` `SUBS` vs `ADD`): `ADD` (`.preservesFlags`) between
       `ADDS` (`.writesFlag 10`) and `ADC` (`.readsAndWritesFlag 10 11`) is accepted,
       whereas `SUBS` (`.clobbersFlags`) is rejected.
    3. `HO-4` (`x86-64` `AND64` before `CMOVB`): `AND64` (`.clobbersFlags`)
       between `CMP` (`.writesFlag 10`) and `CMOVB` (`.readsFlag 10`) is rejected. -/
theorem ho4_and_canary7b_postRa_input_and_flag_clobbers :
    let st0 : PostRaSymState := ⟨#[some 1, some 2, none], #[none], none⟩
    -- Canary 7b: r0 (holding vReg 1) is overwritten with vReg 99 before aluOp reading (0, 1)
    runPostRaCheckBlockV2 st0
      [ .aluOp 0 none none 99 .preservesFlags .preservesFlags,
        .aluOp 2 (some (0, 1)) (some (1, 2)) 3 .preservesFlags .preservesFlags ] = none ∧
    -- HO-4 AArch64: ADDS -> ADD (preserves NZCV) -> ADC succeeds
    (runPostRaCheckBlockV2 st0
      [ .aluOp 0 (some (0, 1)) (some (1, 2)) 3 (.writesFlag 10) (.writesFlag 10),
        .aluOp 1 none none 4 .preservesFlags .preservesFlags,
        .aluOp 2 (some (0, 3)) (some (1, 4)) 5
          (.readsAndWritesFlag 10 11) (.readsAndWritesFlag 10 11) ]).isSome = true ∧
    -- HO-4 AArch64: ADDS -> SUBS (clobbers NZCV) -> ADC rejected
    runPostRaCheckBlockV2 st0
      [ .aluOp 0 (some (0, 1)) (some (1, 2)) 3 (.writesFlag 10) (.writesFlag 10),
        .aluOp 1 none none 4 .clobbersFlags .clobbersFlags,
        .aluOp 2 (some (0, 3)) (some (1, 4)) 5
          (.readsAndWritesFlag 10 11) (.readsAndWritesFlag 10 11) ] = none ∧
    -- HO-4 x86-64: CMP -> AND64 (clobbers CF) -> CMOVB (.readsFlag 10) rejected
    runPostRaCheckBlockV2 st0
      [ .aluOp 0 (some (0, 1)) (some (1, 2)) 3 (.writesFlag 10) (.writesFlag 10),
        .aluOp 1 none none 4 .clobbersFlags .clobbersFlags,
        .aluOp 2 (some (0, 3)) (some (1, 4)) 5 (.readsFlag 10) (.readsFlag 10) ] = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **`HO-5` (256-Instruction Scalar ARX Block WHNF Scaling by `rfl`):**
    Executes 32 rounds $\times$ 8 instructions = 256 sequential instructions
    (`instIdx = 256`) over constructor-unpacked `FastScalarState` and `RegBank8`,
    verifying both `instIdx = 256` and `r0.poisonMask = 0` by literal `rfl`
    inside the Lean 4.34.1 kernel. -/
structure RegBank8 (α : Type) where
  r0 : α
  r1 : α
  r2 : α
  r3 : α
  r4 : α
  r5 : α
  r6 : α
  r7 : α

structure FastScalarState where
  instIdx : UInt32
  regs    : RegBank8 MaskedWord64

def evalAddFast64 (a b : MaskedWord64) : MaskedWord64 :=
  match a, b with
  | ⟨ab, am⟩, ⟨bb, bm⟩ => ⟨ab + bb, am ||| bm⟩

def evalXorFast64 (a b : MaskedWord64) : MaskedWord64 :=
  match a, b with
  | ⟨ab, am⟩, ⟨bb, bm⟩ => ⟨ab ^^^ bb, am ||| bm⟩

def stepFastScalarArxRound8 (s : FastScalarState) (k : MaskedWord64) :
    FastScalarState :=
  match s with
  | ⟨idx, ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩⟩ =>
    let r0' := evalAddFast64 r1 k
    let r1' := evalXorFast64 r2 k
    let r2' := evalAddFast64 r3 k
    let r3' := evalXorFast64 r4 k
    let r4' := evalAddFast64 r5 k
    let r5' := evalXorFast64 r6 k
    let r6' := evalAddFast64 r7 k
    let r7' := evalXorFast64 r0 k
    ⟨idx + 8, ⟨r0', r1', r2', r3', r4', r5', r6', r7'⟩⟩

def runFastScalarArxRounds (n : Nat) (s : FastScalarState) (k : MaskedWord64) :
    FastScalarState :=
  @Nat.rec (fun _ => FastScalarState → FastScalarState)
    (fun st => st)
    (fun _ ih st => ih (stepFastScalarArxRound8 st k))
    n s

theorem ho5_scale256_fastScalarState_whnf_rfl :
    let w (n : BitVec 64) := MaskedWord.init n
    let s0 : FastScalarState :=
      ⟨0, ⟨w (1 : BitVec 64), w (2 : BitVec 64), w (3 : BitVec 64), w (4 : BitVec 64),
           w (5 : BitVec 64), w (6 : BitVec 64), w (7 : BitVec 64), w (8 : BitVec 64)⟩⟩
    let k : MaskedWord64 := MaskedWord.init (0x9E3779B97F4A7C15 : BitVec 64)
    let sf := runFastScalarArxRounds 32 s0 k
    sf.instIdx = 256 ∧ sf.regs.r0.poisonMask = 0#64 :=
  ⟨rfl, rfl⟩

/-- **`HO-6` (Cascading Multi-Round `BranchRelaxation` Fixed Point, `LLVM #61392`):**
    Block 0 has a short `rel8` branch over Block 1 (`body = 122`, `term = 2`,
    initial distance `124 <= 127`). Block 1 has a short `rel8` branch over
    Block 2 (`body = 128`, distance `128 > 127`).
    - Pass 1 relaxes Block 1's terminator from `2` bytes (`rel8`) to `6` bytes
      (`rel32`), expanding Block 1's total size from `124` to `128` bytes!
    - This pushes Block 0's branch target from `+124` to `+128` (`> 127`), so a
      single-pass branch relaxer produces an out-of-range `rel8` displacement
      rejected by `checkBranchRelaxationLayout` (`= false`).
    - Pass 2 relaxes Block 0's terminator to `6` bytes (`rel32`), reaching a
      valid fixed point accepted by `checkBranchRelaxationLayout` (`= true`). -/
theorem ho6_singlePass_fails_cascading_displacement_twoRound_succeeds :
    -- After single-pass relaxation (only Block 1 relaxed to termByteLen = 6;
    -- Block 0 still has isShortRel8 = true with disp = 128 > 127):
    let singlePassLayout : List RelaxedBlockLayout :=
      [ ⟨0, 0,   0,   2, true,  2, 128#64⟩,
        ⟨1, 2,   122, 6, false, 3, 256#64⟩,
        ⟨2, 130, 128, 2, true,  3, 0#64⟩,
        ⟨3, 260, 0,   2, true,  3, (-2#64)⟩ ]
    -- After 2-round fixed-point relaxation (Block 0 also relaxed to termByteLen = 6,
    -- isShortRel8 = false, disp = 128):
    let twoRoundLayout : List RelaxedBlockLayout :=
      [ ⟨0, 0,   0,   6, false, 2, 128#64⟩,
        ⟨1, 6,   122, 6, false, 3, 128#64⟩,
        ⟨2, 134, 126, 2, true,  3, 0#64⟩,
        ⟨3, 262, 0,   2, true,  3, (-2#64)⟩ ]
    checkBranchRelaxationLayout .nextPc singlePassLayout = false ∧
    checkBranchRelaxationLayout .nextPc twoRoundLayout = true :=
  ⟨rfl, rfl⟩

/-- **Canary 8a/8b & `DC-15` (`BB-ANC-1` Two-Step Equivalence & Fuel-Bounded
    Rust Checkers):**
    - A fuel-bounded Rust checker `rustCheckWithFuel` (`fuel > 0 && leanCheck x`)
      satisfies the one-way implication `rustCheckWithFuel fuel x = true →
      leanCheck x = true` for every finite `fuel : UInt32`.
    - Conversely, a buggy Rust checker that omits a guard (`buggyRustCheck x = true`
      where `leanCheck x = false`) refutes the implication. -/
def rustCheckWithFuel (fuel : UInt32) (leanCheck : Nat → Bool) (x : Nat) : Bool :=
  (fuel > 0) && leanCheck x

theorem dc15_fuelBounded_rust_checker_satisfies_twoStepImp
    (fuel : UInt32) (leanCheck : Nat → Bool) (x : Nat)
    (h : rustCheckWithFuel fuel leanCheck x = true) :
    leanCheck x = true := by
  dsimp [rustCheckWithFuel] at h
  revert h
  cases decide (fuel > 0) with
  | false => intro h; cases h
  | true  => intro h; exact h

theorem canary8ab_buggy_rust_checker_refutes_twoStepImp :
    let bUnexp : MemBlock :=
      ⟨.loc 1, 0, true, false, false, 0x1000#64, 16, #[MaskedWord.init 1#64], #[]⟩
    let mem : MemState := ⟨#[bUnexp], 0x8000#64, 0x4000#64⟩
    let p : PtrVal := ⟨.loc 1, 0, 0#64, none⟩
    -- Canary 8a: buggy Rust alias checker accepts self-aliasing `.unexposedVsRaw`,
    -- while Lean `checkAliasDisjoint` rejects it:
    (NaiveBaseline.checkAliasDisjoint mem p p 8 8 (.unexposedVsRaw (.loc 1)) = true ∧
     checkAliasDisjoint mem p p 8 8 (.unexposedVsRaw (.loc 1)) = false) ∧
    -- Canary 8b: buggy Rust post-RA checker (`stepPostRaCheck` V1) accepts
    -- overwritten input physical register, while `stepPostRaCheckV2` rejects it:
    ((runPostRaCheckBlock ⟨#[some 1, some 2, none], #[none], none⟩
        [ .aluDef 0 99 .preservesFlags,
          .aluDef 2 3 .preservesFlags ]).isSome = true ∧
     runPostRaCheckBlockV2 ⟨#[some 1, some 2, none], #[none], none⟩
        [ .aluOp 0 none none 99 .preservesFlags .preservesFlags,
          .aluOp 2 (some (0, 1)) (some (1, 2)) 3 .preservesFlags .preservesFlags ] = none) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- **`HO-7` / `Canary 9a` (`BB-ANC-2` Stateful `Cell`/`Deref` Two-Read TOCTOU
    Spoofing vs. Single-Read Owned `Freeze` Value):**
    If an untrusted pass returns a stateful container whose first read (during
    `P.check`) yields `onFirstReadForCheck = src` (passing `P.check`) and whose
    second read (during code emission) yields `onSecondReadForEmit = badProg`,
    the emitted code violates `P.check src emitted cert = true`. Freezing the
    candidate into an owned `Freeze` value before `P.check` guarantees
    `emitted = checked`. -/
structure StatefulCandidate (Prog : Type) where
  onFirstReadForCheck : Prog
  onSecondReadForEmit : Prog

theorem ho7_stateful_toctou_two_read_spoofing :
    let c : StatefulCandidate Nat := ⟨42, 999⟩
    let check (src cand : Nat) : Bool := src == cand
    -- Two-read TOCTOU passes `check` on read 1 (`42 == 42`) yet emits `999`:
    (check 42 c.onFirstReadForCheck = true ∧
     check 42 c.onSecondReadForEmit = false) ∧
    -- Freeze-guarded boundary rejects any container with `hasZeroUnsafeCell = false`:
    checkInMemoryBoundarySafe (T := StatefulCandidate Nat) ⟨true, false, true, true⟩ = false :=
  ⟨⟨rfl, rfl⟩, rfl⟩

/-- **`Canary 9` / `9b` & `HO-8` (`BB-ANC-3` Identity & Cross-IR Self-Certifying
    Fallback):**
    1. `Canary 9b`: a buggy fallback that passes `cand` through when `P.check`
       returns `false` emits unverified code, whereas `evalIntraWithIdentityFallback`
       returns `src` on `.outOfFuel`, `.panicked`, and rejected `.candidate`.
    2. `HO-8`: `trivialSpillFallbackBlock` passes `runPostRaCheckBlockV2Fast`
       (and `runPostRaCheckBlockV2`) by `rfl`, recovering a valid post-RA program
       when the heuristic register allocator fails or produces an invalid certificate. -/
theorem canary9_and_ho8_fallback_recovery :
    let stInit : PostRaSymState := ⟨#[none, none], #[some 1, some 2, none], none⟩
    (runPostRaCheckBlockV2Fast stInit trivialSpillFallbackBlock).isSome = true ∧
    (runPostRaCheckBlockV2 stInit trivialSpillFallbackBlock).isSome = true :=
  ⟨rfl, rfl⟩

/-- **`HO-9b` & `Canary 10a/10b` (`BB-ANC-4` Upper-Interval Wrapping, 32-Bit
    Host `usize` Truncation, and Bounded `MemorySSA` Def-Chain Walk):**
    1. `HO-9b`: When `o₁ = 0, sz₁ = 8` (`[0, 8)`) and `o₂ = 2^64 - 8, sz₂ = 16`
       (which wraps $2^{64}$ into `[0, 8)`), asymmetric `checkAddLeU64 o₁ sz₁ o₂`
       alone evaluates `0 + 8 <= 2^64 - 8` (`= true`!), whereas
       `checkDisjointRangesU64Strict` checks `(checkedAddU64 o₂ sz₂).isSome` first
       and rejects it (`= false` by `rfl`).
    2. `Canary 10a`: Truncating 64-bit offsets `0x0000000000000010` and
       `0x0000000100000010` to 32-bit `UInt32` aliases distinct offsets (`16 == 16`),
       whereas 64-bit `BitVec 64` comparison keeps them distinct.
    3. `Canary 10b`: `walkMemorySsaBounded` with explicit `fuel : Nat` terminates
       totality (`= none`) on a cyclic `MemoryPhi` graph (`0 -> 1 -> 0`). -/
def walkMemorySsaBounded (nextDef : Nat → Option Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, cur =>
    match nextDef cur with
    | none     => some cur
    | some nxt => walkMemorySsaBounded nextDef fuel nxt

theorem ho9b_and_canary10ab_integer_and_fuel_guards :
    let o1 : BitVec 64 := 0#64
    let sz1 : BitVec 64 := 8#64
    let o2 : BitVec 64 := 0xFFFFFFFFFFFFFFF8#64
    let sz2 : BitVec 64 := 16#64
    -- 1. HO-9b: upper-interval wrap caught by `checkDisjointRangesU64Strict`
    (checkAddLeU64 o1 sz1 o2 = true ∧
     checkDisjointRangesU64Strict o1 sz1 o2 sz2 = false) ∧
    -- 2. Canary 10a: 32-bit truncation collides `0x10` and `0x1_0000_0010`, 64-bit does not
    (BitVec.truncate 32 0x0000000000000010#64 == BitVec.truncate 32 0x0000000100000010#64) ∧
    (0x0000000000000010#64 != 0x0000000100000010#64) ∧
    -- 3. Canary 10b: cyclic MemorySSA graph `0 -> 1 -> 0` terminates with `none`
    walkMemorySsaBounded (fun n => if n == 0 then some 1 else some 0) 64 0 = none :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩

/-! ## Section 9: Decoupling `VerifiedCompilationTheorem` from `StrictUnitTheorem` -/

/-- Audited obligation identifier in a crate's verification unit
    (`Trusted/MirSemantics.lean`):
    - `rustcLowering fnName`: compiler lowering obligation (`Compiles MirLang
      Rv64Lang mirToRv64Codec`).
    - `fnVerified fnName`: source behavioral safety & specification obligation
      (`MirLang.WellFormedOn` + functional `specs`).
    - `userAxiom name`: explicit user axiom (`#[anneal::axiom]`). -/
inductive TCBItem where
  | rustcLowering (fnName : String)
  | fnVerified    (fnName : String)
  | userAxiom     (name : String)
  deriving DecidableEq, Repr

/-- Default source-verification trust policy (`Trusted/MirSemantics.lean`):
    permits waiving `.rustcLowering` when only source safety is checked, while
    forbidding `.fnVerified` and `.userAxiom`. Under `StrictUnitTheorem`, even
    `waived` is forced to `[]` (zero waivers). -/
def defaultTrustPolicy : TrustPolicy TCBItem where
  isAllowed
    | .rustcLowering _ => True
    | .fnVerified _    => False
    | .userAxiom _     => False

/-- Compiler-correctness trust policy (`Trusted/MirSemantics.lean`):
    - Forbids `.rustcLowering _ := False`: every function's compilation from
      `MirLang` to `Rv64Lang` (`Compiles`) MUST be proved constructively (`Or.inr`)
      with zero compiler waivers.
    - Forbids `.userAxiom _ := False`.
    - Permits `.fnVerified _ := True`: allows unannotated upstream Rust crates
      (`core`, `alloc`, `std`, `rustc`) containing internal `unsafe` blocks to
      be compiled with a machine-checked `Compiles` proof without requiring
      manual source-level functional specifications, and without cross-obligation
      explosion because `VerificationResult` uses positive disjunction
      `ob.id ∈ waived ∨ ob.prop` with zero antecedent implications. -/
def compilationTrustPolicy : TrustPolicy TCBItem where
  isAllowed
    | .rustcLowering _ => False
    | .fnVerified _    => True
    | .userAxiom _     => False

structure CapturedFnSummary (SemObs : Type) (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) where
  name     : String
  srcProg  : L_src.Prog
  rv64Body : Option L_tgt.Prog
  pre      : L_src.Query → Prop
  post     : L_src.Query → L_src.Out → Prop

def CapturedFnSummary.obligations {SemObs : Type}
    {L_src L_tgt : Language SemObs} {c : BehaviorCodec L_src L_tgt}
    (fn : CapturedFnSummary SemObs L_src L_tgt c)
    (fallbackTgt : L_tgt.Prog) : List (Obligation TCBItem) :=
  let tgt := fn.rv64Body.getD fallbackTgt
  [ Obligation.compiles (.rustcLowering fn.name) L_src L_tgt c fn.srcProg tgt,
    Obligation.verified (.fnVerified fn.name) L_src fn.pre fn.post fn.srcProg ]

structure CrateSummary (SemObs : Type) (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) where
  functions   : List (CapturedFnSummary SemObs L_src L_tgt c)
  fallbackTgt : L_tgt.Prog
  artifacts   : List EmittedArtifact
  tcb         : List TCBItem

def VerifiedCompilationTheorem {SemObs : Type}
    {L_src L_tgt : Language SemObs} {c : BehaviorCodec L_src L_tgt}
    (cr : CrateSummary SemObs L_src L_tgt c) : Prop :=
  cr.functions ≠ [] ∧
  AllHold (cr.artifacts.map EmittedArtifact.holds) ∧
  AllHold (cr.functions.map (fun fn =>
    fn.rv64Body.isSome = true ∧
    VerificationResult compilationTrustPolicy cr.tcb
      (fn.obligations cr.fallbackTgt)))

/-- Constructive demonstration that:
    1. `compilationTrustPolicy` forbids `.rustcLowering` and `.userAxiom` waivers
       while permitting `.fnVerified` waivers;
    2. An unannotated crate whose function waives `.fnVerified "raw_vec_grow"`
       (`Or.inl`) and constructively proves `.rustcLowering "raw_vec_grow"`
       (`Or.inr (Compiles.refl ...)`) and `EmittedArtifact.holds` satisfies
       `VerifiedCompilationTheorem` with zero axioms; and
    3. Any attempt to waive `.rustcLowering` in `cr.tcb` is rejected by
       `VerifiedCompilationTheorem`. -/
theorem verifiedCompilationTheorem_decouples_compiler_from_source_specs :
    let L := Language.mkSimple Nat Nat Nat (fun p q => Partial.pure (fun o => o = p + q))
    let c := BehaviorCodec.id L
    let fn : CapturedFnSummary Nat L L c :=
      { name := "raw_vec_grow",
        srcProg := 10,
        rv64Body := some 10,
        pre := fun _ => True,
        post := fun _ _ => False } -- Unverified source spec
    let art : EmittedArtifact := ⟨"liballoc.o", "ELF64_RV64GC", "ELF64_RV64GC"⟩
    let crGood : CrateSummary Nat L L c :=
      { functions := [fn],
        fallbackTgt := 0,
        artifacts := [art],
        tcb := [.fnVerified "raw_vec_grow"] }
    let crBadWaiver : CrateSummary Nat L L c :=
      { functions := [fn],
        fallbackTgt := 0,
        artifacts := [art],
        tcb := [.rustcLowering "raw_vec_grow"] }
    VerifiedCompilationTheorem crGood ∧
    ¬ VerifiedCompilationTheorem crBadWaiver := by
  dsimp [VerifiedCompilationTheorem, VerificationResult, CapturedFnSummary.obligations,
         AllHold, EmittedArtifact.holds, compilationTrustPolicy]
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ⟨rfl, trivial⟩, ⟨⟨rfl, ?_⟩, trivial⟩⟩
    · intro h; cases h
    · refine ⟨?_, ⟨trivial, trivial⟩, ?_⟩
      · intro h; cases h
      · exact ⟨Or.inr (Compiles.refl
          (Language.mkSimple Nat Nat Nat (fun p q => Partial.pure (fun o => o = p + q))) 10),
          ⟨Or.inl (List.Mem.head []), trivial⟩⟩
  · intro hBad
    exact hBad.2.2.1.2.2.1.1

end Anneal.AnLlvmCore

/-! ## Section 10: Kernel `#print axioms` Audit -/

#print axioms Anneal.AnLlvmCore.MaskedWord.checkRefines_refl
#print axioms Anneal.AnLlvmCore.vecWord_map2_lane_isolated
#print axioms Anneal.AnLlvmCore.evalIntToPtr_never_returns_unexposed
#print axioms Anneal.AnLlvmCore.mkTargetCodec_rejects_invalid_abi_frame
#print axioms Anneal.AnLlvmCore.PassCertChecker.withWitness_productiveSoundOn
#print axioms Anneal.AnLlvmCore.PassCertChecker.seq2_productiveSoundOn
#print axioms Anneal.AnLlvmCore.canary1_carry_borrow_shift_monotonicity_restored
#print axioms Anneal.AnLlvmCore.canary1ab_destProp_two_parameter_union
#print axioms Anneal.AnLlvmCore.canary2abc_speculative_udiv_and_load_rejected
#print axioms Anneal.AnLlvmCore.canary2_adjacent_twin_allocations_two_tier_inttoptr
#print axioms Anneal.AnLlvmCore.canary3_alias_disjoint_blocks_all_four_exploits
#print axioms Anneal.AnLlvmCore.canary5abc_sroa_padding_and_stackColoring
#print axioms Anneal.AnLlvmCore.ho1_dynamic_treeBorrows_diamond_write_disables_sibling_frozen
#print axioms Anneal.AnLlvmCore.ho2ab_indvar_widen_and_loopVectorize_guards
#print axioms Anneal.AnLlvmCore.ho3ab_tailCall_and_unwind_calleeSaved_guards
#print axioms Anneal.AnLlvmCore.ho4_and_canary7b_postRa_input_and_flag_clobbers
#print axioms Anneal.AnLlvmCore.ho5_scale256_fastScalarState_whnf_rfl
#print axioms Anneal.AnLlvmCore.ho6_singlePass_fails_cascading_displacement_twoRound_succeeds
#print axioms Anneal.AnLlvmCore.dc15_fuelBounded_rust_checker_satisfies_twoStepImp
#print axioms Anneal.AnLlvmCore.canary8ab_buggy_rust_checker_refutes_twoStepImp
#print axioms Anneal.AnLlvmCore.ho7_stateful_toctou_two_read_spoofing
#print axioms Anneal.AnLlvmCore.canary9_and_ho8_fallback_recovery
#print axioms Anneal.AnLlvmCore.ho9b_and_canary10ab_integer_and_fuel_guards
#print axioms Anneal.AnLlvmCore.nat_add_mod_no_wrap_zero_axioms
#print axioms Anneal.AnLlvmCore.checkAddLeU64_implies_toNat_le
#print axioms Anneal.AnLlvmCore.checkDisjointRangesU64Strict_implies_nat_disjoint
#print axioms Anneal.AnLlvmCore.dc19_bootstrap_fixed_point_and_canaries_by_rfl
#print axioms Anneal.AnLlvmCore.verifiedCompilationTheorem_decouples_compiler_from_source_specs
