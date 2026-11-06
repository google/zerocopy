-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Putnam's Model-Theoretic Permutation Theorem, Syntax-Semantics Dualism, Emitter Non-Surjectivity, and the Irreducible TCB Boundary in Semantic Verification

This standalone Lean 4 (`v4.34.1`) mechanization proves the foundational
model-theoretic and compiler-correctness boundary laws governing the 16-candidate
evolution (`Candidate 001` through `Candidate 016`) and its 40 adversarial
pentesting exploits (`PENTEST-1`..`10`, `PENTEST-R2-1`..`10`, `PENTEST-R3-1`..`10`,
and `PENTEST-R4-1`..`10`):

1. **Part I & Part II — The Model-Theoretic Syntax-Permutation Invariance Theorem
   (`PutnamSyntaxPermutationTheorem`):**
   - Given any language `L : Language SemObs` and any syntax permutation
     `π : SyntaxPerm L.Prog` on its syntax carrier (for instance, swapping
     `"xor eax, eax\nret"` and `"mov eax, edi; inc eax; ret"` in `String`),
     the syntax-permuted language `L.permProg π` (`sem s q := L.sem (π.toFun s) q`)
     is proven 100% indistinguishable from `L` under every purely extensional or
     structural predicate in the semantic framework (`SafeAt`, `Produces`,
     `ProductiveOn`, `DeterministicOn`, `QuerySensitiveOn`, `NonChaoticOn`,
     `HasProductiveContrastOn`, `WellBehavedProgOn`, `TotalWellBehavedDomainOn`,
     `SemanticallyClosedOn`, `BiNonInterferingOn`, and `EmitterCompilesWithWitnessesOn`).
   - **Corollaries (`PENTEST-9`, `PENTEST-R2-1`, `PENTEST-R3-4`):**
     No purely extensional predicate can distinguish an honest assembly emitter
     from a trojan emitter paired with a permuted target semantics `L.permProg π`
     (`PENTEST-R3-4`) or a circular parser `L.diskLang parse` (`PENTEST-R2-1`).
     Binding concrete strings (`String`) or machine bytes (`ByteArray`) to
     operational meaning irreducibly requires an audited concrete operational
     semantics `L_isa.sem` in the Trusted Computing Base (Domain Noun 1).

2. **Part III — Impossibility of Lexical/Prefix Heuristics on Stateful Operational
   Languages (`LexicalHeuristicDualFailureTheorem`, `PENTEST-R4-2A/B`) & Emitter
   Surjectivity Impossibility (`EmitterSurjectivityImpossibility`, `PENTEST-R4-8`):**
   - **Theorem 2A (`LexicalHeuristicDualFailureTheorem`):** On a stateful
     sequential instruction language where instructions compose via state update
     (`evalSeq (i₁ :: rest) = evalSeq rest ∘ evalInstr i₁`), any lexical
     classifier `H : Prog → Bool` that enforces `H p = true → Produces p q v → v = 0`
     suffers **False Positives (Honest Accumulator-Init Lockout `PENTEST-R4-2A`)**
     if it matches leading zero-clear prefixes with an unbounded suffix wildcard
     (`[.zeroClear, .loadAndInc]`), and suffers **False Negatives (Labelled
     Trojan Bypass `PENTEST-R4-2B`)** if it checks only the first syntactic
     element (`[.label "main", .zeroClear]`).
   - **Theorem 2B (`EmitterSurjectivityImpossibility`):** Requiring an emitter
     `emit : L_src.Prog → L_asm.Prog` to be surjective onto all productive
     query-sensitive target programs (`PENTEST-R4-8`) is mathematically
     impossible (`False`) whenever `L_asm` has more distinct query-sensitive
     programs than `L_src` has productive programs—which holds for every
     single-program verification unit targeting any multi-instruction ISA.

3. **Part IV & Part V — The Next-Generation Minimal Semantic Blueprint
   (`NextGenSemanticFrameworkBlueprint`):**
   - Synthesizes all 40 pentest exploits into 4 orthogonal primitives (`Language`,
     `Tool`, `FramedCodec`, `Spec`) and a single canonical base bundle
     (`VerifiedCompilerBase`) extended via Lean structure inheritance (`extends`)
     by `VerifiedConstantTimeCompiler` and `VerifiedArtifactPipeline`, proving
     both **Exploit Rejection (zero Category A1 bypasses)** and **Honest Tool
     Non-Lockout (zero Category A2 lockouts)**.
-/

namespace PutnamAndTcbBoundary

/-!
## Part I: Core Semantic Model Primitives & Syntax Permutations
-/

/-- Preorder on behavior carrier types. -/
class Preorder (B : Type u) extends LE B where
  le_refl  : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

/-- Demonic partial computation (`defined` precondition + `val` outcome predicate). -/
structure Partial (B : Type u) where
  defined : Prop
  val     : defined → B

namespace Partial

def pure {B : Type u} (b : B) : Partial B :=
  { defined := True, val := fun _ => b }

def ub {B : Type u} : Partial B :=
  { defined := False, val := False.elim }

def map {A : Type u} {B : Type v} (f : A → B) (p : Partial A) : Partial B :=
  { defined := p.defined, val := fun h => f (p.val h) }

end Partial

instance instPreorderPred (Out : Type u) : Preorder (Out → Prop) where
  le P Q := ∀ o, P o → Q o
  le_refl _ _ h := h
  le_trans h₁ h₂ o hp := h₂ o (h₁ o hp)

instance instPreorderPartial (B : Type u) [Preorder B] : Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

instance instPreorderBehavior (Query Out : Type) : Preorder (Behavior Query Out) where
  le b₁ b₂ := ∀ q, b₁ q ≤ b₂ q
  le_refl b q := Preorder.le_refl (b q)
  le_trans h₁₂ h₂₃ q := Preorder.le_trans (h₁₂ q) (h₂₃ q)

/-- Core `Language` primitive indexed by observable spine `SemObs`. -/
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
  obs   := id
  sem   := sem

namespace Language

variable {SemObs : Type} (L : Language SemObs)

abbrev SafeAt (prog : L.Prog) (q : L.Query) : Prop :=
  (L.sem prog q).defined

abbrev Produces (prog : L.Prog) (q : L.Query) (v : SemObs) : Prop :=
  ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o ∧ L.obs o = v

def ProductiveOn (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o

def DeterministicOn (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q → ∀ v₁ v₂, L.Produces prog q v₁ → L.Produces prog q v₂ → v₁ = v₂

def QuerySensitiveOn (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  (∃ q₁ q₂ : L.Query, pre q₁ ∧ pre q₂ ∧ q₁ ≠ q₂) →
  ∃ (q₁ q₂ : L.Query) (v₁ v₂ : SemObs),
    pre q₁ ∧ pre q₂ ∧ v₁ ≠ v₂ ∧ L.Produces prog q₁ v₁ ∧ L.Produces prog q₂ v₂

def NonChaoticOn (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  L.ProductiveOn pre prog ∧
  ∀ q, pre q → ∃ v_excluded : SemObs, ¬ L.Produces prog q v_excluded

def SpecOn (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    Behavior L.Query L.Out :=
  fun q => { defined := pre q, val := fun _ o => post q o }

def SpineSpecOn (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop) :
    Behavior L.Query L.Out :=
  L.SpecOn pre (fun q o => obsPost q (L.obs o))

def VerifiedSpineOn (dom pre : L.Query → Prop)
    (obsPost : L.Query → SemObs → Prop) (prog : L.Prog) : Prop :=
  ((∃ q, pre q) ∨ (∀ q, ¬ dom q)) ∧
  L.ProductiveOn pre prog ∧
  L.sem prog ≤ L.SpineSpecOn pre obsPost

def ViolatesSpine (pre : L.Query → Prop)
    (obsPost : L.Query → SemObs → Prop) (badProg : L.Prog) : Prop :=
  ∃ q₀, pre q₀ ∧ ∃ v, L.Produces badProg q₀ v ∧ ¬ obsPost q₀ v

def ViolatesSafetyOn (pre : L.Query → Prop) (badProg : L.Prog) : Prop :=
  ∃ q₀, pre q₀ ∧ ¬ L.SafeAt badProg q₀

def ViolatesSpec (pre : L.Query → Prop)
    (obsPost : L.Query → SemObs → Prop) (badProg : L.Prog) : Prop :=
  L.ViolatesSpine pre obsPost badProg ∨ L.ViolatesSafetyOn pre badProg

def HasSameQueryContrast (pre : L.Query → Prop) (goodProg : L.Prog) : Prop :=
  ∃ (altProg : L.Prog) (q : L.Query) (v₁ v₂ : SemObs),
    pre q ∧ L.Produces goodProg q v₁ ∧ L.Produces altProg q v₂ ∧ v₁ ≠ v₂

def SpineNonDegenerate (pre : L.Query → Prop)
    (obsPost : L.Query → SemObs → Prop) (goodProg badProg : L.Prog) : Prop :=
  L.ViolatesSpine pre obsPost badProg ∨
  (L.ViolatesSafetyOn pre badProg ∧ L.HasSameQueryContrast pre goodProg)

def HasProductiveContrastOn (pre : L.Query → Prop) (goodAsm : L.Prog) : Prop :=
  (∃ invalidAsm : L.Prog, ∀ q : L.Query, pre q → ¬ (L.sem invalidAsm q).defined) ∧
  (∃ altAsm : L.Prog,
    L.ProductiveOn pre altAsm ∧
    ∃ (q₀ : L.Query) (v_good v_alt : SemObs),
      pre q₀ ∧ L.Produces goodAsm q₀ v_good ∧ L.Produces altAsm q₀ v_alt ∧ v_good ≠ v_alt)

end Language

/-- `Candidate 016` range-separation typeclass for constant initializers. -/
class CanonicalConstInit (SemObs : Type) where
  validMultiShift : (SemObs → Prop) → (SemObs → Prop) → Prop

instance instCanonicalConstInitNat : CanonicalConstInit Nat where
  validMultiShift rangeP' rangeB := ¬ rangeP' 1 ∧ ¬ rangeP' 26 ∧ ¬ rangeB 1

/-- `Candidate 016` intrinsic well-behavedness predicate (`WellBehavedProgOn`). -/
def Language.WellBehavedProgOn {SemObs : Type} [cci : CanonicalConstInit SemObs]
    (L : Language SemObs) (pre : L.Query → Prop) (p : L.Prog) : Prop :=
  L.ProductiveOn pre p ∧
  L.DeterministicOn pre p ∧
  (L.QuerySensitiveOn pre p ∨
   ((∃ b_ub : L.Prog, ∀ q : L.Query, pre q → ¬ (L.sem b_ub q).defined) ∧
    (∀ b : L.Prog, L.ProductiveOn pre b → L.DeterministicOn pre b) ∧
    (∃ (p' : L.Prog) (q₁ q₂ : L.Query) (v₁ v₂ : SemObs),
      L.ProductiveOn pre p' ∧
      pre q₁ ∧ pre q₂ ∧ v₁ ≠ v₂ ∧
      L.Produces p' q₁ v₁ ∧ L.Produces p' q₂ v₂ ∧
      (∀ (b : L.Prog),
        L.ProductiveOn pre b → L.QuerySensitiveOn pre b →
        (∀ (q : L.Query) (v : SemObs),
          pre q → (L.Produces b q v ↔ L.Produces p' q v)) ∨
        ((¬ ∃ q : L.Query, pre q ∧ L.Produces b q v₁) ∧
         L.Produces b q₁ v₂ ∧
         (∀ (q_b q_p : L.Query) (v_ov w : SemObs),
           pre q_b → pre q_p →
           L.Produces b q_b v_ov →
           L.Produces p' q_p v_ov →
           L.Produces b q_p w →
           ¬ ∃ q₃ : L.Query, pre q₃ ∧ L.Produces p' q₃ w) ∧
         (∀ (q : L.Query) (v : SemObs),
           pre q → L.Produces p q v → ¬ L.Produces p' q v) ∧
         (∀ (q : L.Query) (v : SemObs),
           pre q → L.Produces p q v → ¬ L.Produces b q v) ∧
         cci.validMultiShift
           (fun v => ∃ q : L.Query, pre q ∧ L.Produces p' q v)
           (fun v => ∃ q : L.Query, pre q ∧ L.Produces b q v))))))

/-- `Candidate 016` domain-level completeness predicate (`TotalWellBehavedDomainOn`). -/
def Language.TotalWellBehavedDomainOn {SemObs : Type} [CanonicalConstInit SemObs]
    (L : Language SemObs) (pre : L.Query → Prop) : Prop :=
  (∀ b : L.Prog, L.ProductiveOn pre b ∧ L.DeterministicOn pre b) ∨
  (∀ p₁ p₂ : L.Prog,
    L.WellBehavedProgOn pre p₁ →
    L.WellBehavedProgOn pre p₂ →
    (∀ q : L.Query, pre q → ∀ v : SemObs, L.Produces p₁ q v ↔ L.Produces p₂ q v) →
    p₁ = p₂) ∨
  (∃ p₀ : L.Prog, L.WellBehavedProgOn pre p₀ ∧ ¬ L.QuerySensitiveOn pre p₀) ∨
  (∃ p₁ p₂ p₃ : L.Prog,
    L.WellBehavedProgOn pre p₁ ∧
    L.WellBehavedProgOn pre p₂ ∧
    L.WellBehavedProgOn pre p₃ ∧
    (∃ q : L.Query, ∃ v : SemObs, pre q ∧ L.Produces p₁ q v ∧ ¬ L.Produces p₂ q v) ∧
    (∃ q : L.Query, ∃ v : SemObs, pre q ∧ L.Produces p₁ q v ∧ ¬ L.Produces p₃ q v) ∧
    (∃ q : L.Query, ∃ v : SemObs, pre q ∧ L.Produces p₂ q v ∧ ¬ L.Produces p₃ q v))

/-- Bidirectional 2-safety non-interference (`BiNonInterferingOn`). -/
def Language.BiNonInterferingOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop)
    (lowEq : L.Query → L.Query → Prop)
    (leakEq : SemObs → SemObs → Prop)
    (prog : L.Prog) : Prop :=
  (∀ q₁ q₂ : L.Query, pre q₁ → pre q₂ → lowEq q₁ q₂ →
    ∀ v₁ : SemObs, L.Produces prog q₁ v₁ →
      ∃ v₂ : SemObs, L.Produces prog q₂ v₂ ∧ leakEq v₁ v₂) ∧
  (∀ q₁ q₂ : L.Query, pre q₁ → pre q₂ → lowEq q₁ q₂ →
    ∀ v₂ : SemObs, L.Produces prog q₂ v₂ →
      ∃ v₁ : SemObs, L.Produces prog q₁ v₁ ∧ leakEq v₁ v₂)

/-- `BehaviorCodec` connecting source and target languages over shared `SemObs`. -/
structure BehaviorCodec {SemObs : Type} (L₁ L₂ : Language SemObs) where
  encodeQuery : L₁.Query → L₂.Query
  decodeQuery : L₂.Query → L₁.Query
  encodeOut   : L₁.Out → L₂.Out
  decodeOut   : L₂.Out → Option L₁.Out
  decodeQuery_encodeQuery : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁
  decodeOut_encodeOut     : ∀ o₁, decodeOut (encodeOut o₁) = some o₁
  obs_decodeOut           : ∀ o₂ o₁, decodeOut o₂ = some o₁ → L₂.obs o₂ = L₁.obs o₁

def BehaviorCodec.id {SemObs : Type} (L : Language SemObs) : BehaviorCodec L L where
  encodeQuery := _root_.id
  decodeQuery := _root_.id
  encodeOut   := _root_.id
  decodeOut   := some
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl
  obs_decodeOut _ _ h       := congrArg L.obs (Option.some.inj h)

def BehaviorCodec.toMorphism {SemObs : Type} {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂) (b₁ : Behavior L₁.Query L₁.Out) :
    Behavior L₂.Query L₂.Out :=
  fun q₂ => {
    defined := (b₁ (c.decodeQuery q₂)).defined
    val     := fun h₁ o₂ => ∃ o₁, c.decodeOut o₂ = some o₁ ∧ (b₁ (c.decodeQuery q₂)).val h₁ o₁
  }

abbrev Compiles {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ c.toMorphism (L_src.sem s)

def ProductiveCompiles {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  Compiles L_src L_tgt c s t ∧
  ∀ q₂ : L_tgt.Query,
    (∃ h₁ : (L_src.sem s (c.decodeQuery q₂)).defined,
      ∃ o₁, (L_src.sem s (c.decodeQuery q₂)).val h₁ o₁) →
    (∃ h₂ : (L_tgt.sem t q₂).defined, ∃ o₂, (L_tgt.sem t q₂).val h₂ o₂)

abbrev Tool {SemObs : Type} (L_src L_tgt : Language SemObs) : Type :=
  L_src.Prog → Partial L_tgt.Prog

/-- Semantic closure of a tool under observational equivalence (`SemanticallyClosedOn`). -/
def Tool.SemanticallyClosedOn {SemObs : Type} {L_src L_tgt : Language SemObs}
    (pre : L_src.Query → Prop) (tool : Tool L_src L_tgt) : Prop :=
  ∀ p₁ p₂ : L_src.Prog,
    (∀ q : L_src.Query, pre q → ∀ v : SemObs, L_src.Produces p₁ q v ↔ L_src.Produces p₂ q v) →
    (tool p₁).defined → (tool p₂).defined

/-- `EmitterCompiles` and `EmitterCompilesWithWitnessesOn` (`Master Theorem 10B`). -/
def EmitterCompiles {SemObs : Type} (L_tgt L_asm : Language SemObs)
    (c_asm : BehaviorCodec L_tgt L_asm) (emit : L_tgt.Prog → L_asm.Prog) : Prop :=
  ∀ t : L_tgt.Prog, ProductiveCompiles L_tgt L_asm c_asm t (emit t)

def AllHold : List Prop → Prop
  | []      => True
  | p :: ps => p ∧ AllHold ps

def EmitterCompilesWithWitnessesOn {SemObs : Type}
    (L_tgt L_asm : Language SemObs)
    (c_asm : BehaviorCodec L_tgt L_asm)
    (emit : L_tgt.Prog → L_asm.Prog)
    (dom_asm pre_asm : L_asm.Query → Prop)
    (obsPost_asm : L_asm.Query → SemObs → Prop)
    (goodTgt : L_tgt.Prog)
    (badAsmProgs : List L_asm.Prog) : Prop :=
  EmitterCompiles L_tgt L_asm c_asm emit ∧
  L_asm.VerifiedSpineOn dom_asm pre_asm obsPost_asm (emit goodTgt) ∧
  badAsmProgs ≠ [] ∧
  AllHold (badAsmProgs.map (fun badAsm =>
    emit goodTgt ≠ badAsm ∧
    L_asm.SpineNonDegenerate pre_asm obsPost_asm (emit goodTgt) badAsm))

/-!
## Part II: Putnam's Model-Theoretic Syntax-Permutation Invariance Theorem
-/

/-- Explicit bijection on a syntax carrier `α` (`SyntaxPerm α`). -/
structure SyntaxPerm (α : Type u) where
  toFun     : α → α
  invFun    : α → α
  left_inv  : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

namespace SyntaxPerm

def id (α : Type u) : SyntaxPerm α where
  toFun     := _root_.id
  invFun    := _root_.id
  left_inv  _ := rfl
  right_inv _ := rfl

def symm {α : Type u} (π : SyntaxPerm α) : SyntaxPerm α where
  toFun     := π.invFun
  invFun    := π.toFun
  left_inv  := π.right_inv
  right_inv := π.left_inv

theorem toFun_inj {α : Type u} (π : SyntaxPerm α) {x y : α}
    (h : π.toFun x = π.toFun y) : x = y := by
  have h1 := congrArg π.invFun h
  rw [π.left_inv, π.left_inv] at h1
  exact h1

theorem invFun_inj {α : Type u} (π : SyntaxPerm α) {x y : α}
    (h : π.invFun x = π.invFun y) : x = y :=
  π.symm.toFun_inj h

/-- Involutive transposition swapping two syntax elements `s₁ ↔ s₂`. -/
def swapFn {α : Type u} [DecidableEq α] (s₁ s₂ : α) (s : α) : α :=
  if s = s₁ then s₂ else if s = s₂ then s₁ else s

theorem swapFn_involutive {α : Type u} [DecidableEq α] (s₁ s₂ s : α) :
    swapFn s₁ s₂ (swapFn s₁ s₂ s) = s := by
  dsimp [swapFn]
  split
  · next h1 =>
    split
    · next h2 => rw [h1, h2]
    · next h2 =>
      split
      · next _ => exact h1.symm
      · next h3 => exact False.elim (h3 rfl)
  · next h1 =>
    split
    · next h2 =>
      split
      · next _ => exact h2.symm
      · next h3 => exact False.elim (h3 rfl)
    · next _ => rfl

def swap {α : Type u} [DecidableEq α] (s₁ s₂ : α) : SyntaxPerm α where
  toFun     := swapFn s₁ s₂
  invFun    := swapFn s₁ s₂
  left_inv  := swapFn_involutive s₁ s₂
  right_inv := swapFn_involutive s₁ s₂

end SyntaxPerm

/-- The syntax-permuted language `π^*(L)` (`Language.permProg π L`), which keeps
    the syntax carrier `L.Prog`, query type `L.Query`, outcome type `L.Out`, and
    observable spine `L.obs` identical, but interprets syntax `s` as `L.sem (π s)`. -/
abbrev Language.permProg {SemObs : Type} (L : Language SemObs)
    (π : SyntaxPerm L.Prog) : Language SemObs where
  Prog  := L.Prog
  Query := L.Query
  Out   := L.Out
  obs   := L.obs
  sem   := fun s q => L.sem (π.toFun s) q
  dom   := L.dom

/-- Conjugation of a `Tool L₁ L₂` by syntax permutations `π₁` and `π₂`. -/
def Tool.permProg {SemObs : Type} {L₁ L₂ : Language SemObs}
    (π₁ : SyntaxPerm L₁.Prog) (π₂ : SyntaxPerm L₂.Prog)
    (T : Tool L₁ L₂) : Tool (L₁.permProg π₁) (L₂.permProg π₂) :=
  fun s => (T (π₁.toFun s)).map π₂.invFun

/-- Induced codec into `L₂.permProg π` (since `Query`, `Out`, and `obs` are unchanged). -/
def BehaviorCodec.toPermTgt {SemObs : Type} {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂) (π : SyntaxPerm L₂.Prog) :
    BehaviorCodec L₁ (L₂.permProg π) where
  encodeQuery := c.encodeQuery
  decodeQuery := c.decodeQuery
  encodeOut   := c.encodeOut
  decodeOut   := c.decodeOut
  decodeQuery_encodeQuery := c.decodeQuery_encodeQuery
  decodeOut_encodeOut     := c.decodeOut_encodeOut
  obs_decodeOut           := c.obs_decodeOut

/-!
### Step-by-Step Invariance Lemmas Under Syntax Permutation `π`
-/

theorem permProg_produces_invFun_eq {SemObs : Type} (L : Language SemObs)
    (π : SyntaxPerm L.Prog) (b : L.Prog) :
    (L.permProg π).Produces (π.invFun b) = L.Produces b :=
  congrArg L.Produces (π.right_inv b)

theorem permProg_safeAt_iff {SemObs : Type} (L : Language SemObs)
    (π : SyntaxPerm L.Prog) (s : L.Prog) (q : L.Query) :
    (L.permProg π).SafeAt s q ↔ L.SafeAt (π.toFun s) q :=
  Iff.rfl

theorem permProg_produces_iff {SemObs : Type} (L : Language SemObs)
    (π : SyntaxPerm L.Prog) (s : L.Prog) (q : L.Query) (v : SemObs) :
    (L.permProg π).Produces s q v ↔ L.Produces (π.toFun s) q v :=
  Iff.rfl

theorem permProg_productiveOn_iff {SemObs : Type} (L : Language SemObs)
    (π : SyntaxPerm L.Prog) (pre : L.Query → Prop) (s : L.Prog) :
    (L.permProg π).ProductiveOn pre s ↔ L.ProductiveOn pre (π.toFun s) :=
  Iff.rfl

theorem permProg_deterministicOn_iff {SemObs : Type} (L : Language SemObs)
    (π : SyntaxPerm L.Prog) (pre : L.Query → Prop) (s : L.Prog) :
    (L.permProg π).DeterministicOn pre s ↔ L.DeterministicOn pre (π.toFun s) :=
  Iff.rfl

theorem permProg_querySensitiveOn_iff {SemObs : Type} (L : Language SemObs)
    (π : SyntaxPerm L.Prog) (pre : L.Query → Prop) (s : L.Prog) :
    (L.permProg π).QuerySensitiveOn pre s ↔ L.QuerySensitiveOn pre (π.toFun s) :=
  Iff.rfl

theorem permProg_nonChaoticOn_iff {SemObs : Type} (L : Language SemObs)
    (π : SyntaxPerm L.Prog) (pre : L.Query → Prop) (s : L.Prog) :
    (L.permProg π).NonChaoticOn pre s ↔ L.NonChaoticOn pre (π.toFun s) :=
  Iff.rfl

theorem permProg_verifiedSpineOn_iff {SemObs : Type} (L : Language SemObs)
    (π : SyntaxPerm L.Prog) (dom pre : L.Query → Prop)
    (obsPost : L.Query → SemObs → Prop) (s : L.Prog) :
    (L.permProg π).VerifiedSpineOn dom pre obsPost s ↔
      L.VerifiedSpineOn dom pre obsPost (π.toFun s) :=
  Iff.rfl

theorem permProg_violatesSpine_iff {SemObs : Type} (L : Language SemObs)
    (π : SyntaxPerm L.Prog) (pre : L.Query → Prop)
    (obsPost : L.Query → SemObs → Prop) (s : L.Prog) :
    (L.permProg π).ViolatesSpine pre obsPost s ↔
      L.ViolatesSpine pre obsPost (π.toFun s) :=
  Iff.rfl

theorem permProg_violatesSafetyOn_iff {SemObs : Type} (L : Language SemObs)
    (π : SyntaxPerm L.Prog) (pre : L.Query → Prop) (s : L.Prog) :
    (L.permProg π).ViolatesSafetyOn pre s ↔
      L.ViolatesSafetyOn pre (π.toFun s) :=
  Iff.rfl

theorem permProg_hasSameQueryContrast_iff {SemObs : Type} (L : Language SemObs)
    (π : SyntaxPerm L.Prog) (pre : L.Query → Prop) (s : L.Prog) :
    (L.permProg π).HasSameQueryContrast pre s ↔
      L.HasSameQueryContrast pre (π.toFun s) := by
  constructor
  · rintro ⟨alt, q, v₁, v₂, hq, hp₁, hp₂, hne⟩
    exact ⟨π.toFun alt, q, v₁, v₂, hq, hp₁, hp₂, hne⟩
  · rintro ⟨alt, q, v₁, v₂, hq, hp₁, hp₂, hne⟩
    refine ⟨π.invFun alt, q, v₁, v₂, hq, hp₁, ?_, hne⟩
    change L.Produces (π.toFun (π.invFun alt)) q v₂
    rw [π.right_inv]
    exact hp₂

theorem permProg_spineNonDegenerate_iff {SemObs : Type} (L : Language SemObs)
    (π : SyntaxPerm L.Prog) (pre : L.Query → Prop)
    (obsPost : L.Query → SemObs → Prop) (goodProg badProg : L.Prog) :
    (L.permProg π).SpineNonDegenerate pre obsPost goodProg badProg ↔
      L.SpineNonDegenerate pre obsPost (π.toFun goodProg) (π.toFun badProg) := by
  constructor
  · rintro (hvs | ⟨hsaf, hcon⟩)
    · exact Or.inl hvs
    · exact Or.inr ⟨hsaf, (permProg_hasSameQueryContrast_iff L π pre goodProg).mp hcon⟩
  · rintro (hvs | ⟨hsaf, hcon⟩)
    · exact Or.inl hvs
    · exact Or.inr ⟨hsaf, (permProg_hasSameQueryContrast_iff L π pre goodProg).mpr hcon⟩

theorem permProg_hasProductiveContrastOn_iff {SemObs : Type} (L : Language SemObs)
    (π : SyntaxPerm L.Prog) (pre : L.Query → Prop) (s : L.Prog) :
    (L.permProg π).HasProductiveContrastOn pre s ↔
      L.HasProductiveContrastOn pre (π.toFun s) := by
  constructor
  · rintro ⟨⟨inv, hinv⟩, ⟨alt, hprod, q₀, vg, va, hq₀, hpg, hpa, hne⟩⟩
    exact ⟨⟨π.toFun inv, hinv⟩, ⟨π.toFun alt, hprod, q₀, vg, va, hq₀, hpg, hpa, hne⟩⟩
  · rintro ⟨⟨inv, hinv⟩, ⟨alt, hprod, q₀, vg, va, hq₀, hpg, hpa, hne⟩⟩
    refine ⟨⟨π.invFun inv, fun q hq => ?_⟩,
      ⟨π.invFun alt, ?_, q₀, vg, va, hq₀, hpg, ?_, hne⟩⟩
    · change ¬ (L.sem (π.toFun (π.invFun inv)) q).defined
      rw [π.right_inv]
      exact hinv q hq
    · change L.ProductiveOn pre (π.toFun (π.invFun alt))
      rw [π.right_inv]
      exact hprod
    · change L.Produces (π.toFun (π.invFun alt)) q₀ va
      rw [π.right_inv]
      exact hpa

/-- **Putnam Permutation Invariance for `WellBehavedProgOn`:**
    Even `Candidate 016`'s AST-quantified `WellBehavedProgOn` is 100% invariant
    under any syntax permutation `π : SyntaxPerm L.Prog`. -/
theorem permProg_wellBehavedProgOn_iff {SemObs : Type}
    [cci : CanonicalConstInit SemObs] (L : Language SemObs)
    (π : SyntaxPerm L.Prog) (pre : L.Query → Prop) (s : L.Prog) :
    (L.permProg π).WellBehavedProgOn pre s ↔
      L.WellBehavedProgOn pre (π.toFun s) := by
  constructor
  · rintro ⟨hprod, hdet, hqs | ⟨⟨bub, hbub⟩, hall_det, p', q₁, q₂, v₁, v₂,
      hp'_prod, hq₁, hq₂, hne, hp'1, hp'2, hall_b⟩⟩
    · exact ⟨hprod, hdet, Or.inl hqs⟩
    · refine ⟨hprod, hdet, Or.inr ⟨⟨π.toFun bub, hbub⟩, ?_,
        π.toFun p', q₁, q₂, v₁, v₂, hp'_prod, hq₁, hq₂, hne, hp'1, hp'2, ?_⟩⟩
      · intro b hb_prod
        have hb' : (L.permProg π).ProductiveOn pre (π.invFun b) := by
          change L.ProductiveOn pre (π.toFun (π.invFun b))
          rw [π.right_inv]
          exact hb_prod
        have hd' := hall_det (π.invFun b) hb'
        change L.DeterministicOn pre (π.toFun (π.invFun b)) at hd'
        rw [π.right_inv] at hd'
        exact hd'
      · intro b hb_prod hb_qs
        have hb'_prod : (L.permProg π).ProductiveOn pre (π.invFun b) := by
          change L.ProductiveOn pre (π.toFun (π.invFun b))
          rw [π.right_inv]; exact hb_prod
        have hb'_qs : (L.permProg π).QuerySensitiveOn pre (π.invFun b) := by
          change L.QuerySensitiveOn pre (π.toFun (π.invFun b))
          rw [π.right_inv]; exact hb_qs
        have hres := hall_b (π.invFun b) hb'_prod hb'_qs
        rw [permProg_produces_invFun_eq L π b] at hres
        exact hres
  · rintro ⟨hprod, hdet, hqs | ⟨⟨bub, hbub⟩, hall_det, p', q₁, q₂, v₁, v₂,
      hp'_prod, hq₁, hq₂, hne, hp'1, hp'2, hall_b⟩⟩
    · exact ⟨hprod, hdet, Or.inl hqs⟩
    · refine ⟨hprod, hdet, Or.inr ⟨⟨π.invFun bub, fun q hq => ?_⟩, ?_,
        π.invFun p', q₁, q₂, v₁, v₂, ?_, hq₁, hq₂, hne, ?_, ?_, ?_⟩⟩
      · change ¬ (L.sem (π.toFun (π.invFun bub)) q).defined
        rw [π.right_inv]; exact hbub q hq
      · intro b hb_prod
        exact hall_det (π.toFun b) hb_prod
      · change L.ProductiveOn pre (π.toFun (π.invFun p'))
        rw [π.right_inv]; exact hp'_prod
      · change L.Produces (π.toFun (π.invFun p')) q₁ v₁
        rw [π.right_inv]; exact hp'1
      · change L.Produces (π.toFun (π.invFun p')) q₂ v₂
        rw [π.right_inv]; exact hp'2
      · intro b hb_prod hb_qs
        have hres := hall_b (π.toFun b) hb_prod hb_qs
        rw [permProg_produces_invFun_eq L π p']
        exact hres

/-- **Putnam Permutation Invariance for `TotalWellBehavedDomainOn`:**
    The whole-language predicate `TotalWellBehavedDomainOn` is 100% invariant
    under any syntax bijection `π : SyntaxPerm L.Prog`. -/
theorem permProg_totalWellBehavedDomainOn_iff {SemObs : Type}
    [CanonicalConstInit SemObs] (L : Language SemObs)
    (π : SyntaxPerm L.Prog) (pre : L.Query → Prop) :
    (L.permProg π).TotalWellBehavedDomainOn pre ↔
      L.TotalWellBehavedDomainOn pre := by
  constructor
  · rintro (h1 | h2 | ⟨p₀, hp₀_wb, hp₀_nqs⟩ | ⟨p₁, p₂, p₃, hw1, hw2, hw3, d12, d13, d23⟩)
    · refine Or.inl (fun b => ?_)
      have hb := h1 (π.invFun b)
      change L.ProductiveOn pre (π.toFun (π.invFun b)) ∧
             L.DeterministicOn pre (π.toFun (π.invFun b)) at hb
      rw [π.right_inv] at hb
      exact hb
    · refine Or.inr (Or.inl (fun p₁ p₂ hw1 hw2 heq => ?_))
      have hw1' : (L.permProg π).WellBehavedProgOn pre (π.invFun p₁) := by
        rw [permProg_wellBehavedProgOn_iff, π.right_inv]; exact hw1
      have hw2' : (L.permProg π).WellBehavedProgOn pre (π.invFun p₂) := by
        rw [permProg_wellBehavedProgOn_iff, π.right_inv]; exact hw2
      have heq' : ∀ q, pre q → ∀ v,
          (L.permProg π).Produces (π.invFun p₁) q v ↔
          (L.permProg π).Produces (π.invFun p₂) q v := by
        rw [permProg_produces_invFun_eq L π p₁, permProg_produces_invFun_eq L π p₂]
        exact heq
      exact π.invFun_inj (h2 (π.invFun p₁) (π.invFun p₂) hw1' hw2' heq')
    · refine Or.inr (Or.inr (Or.inl ⟨π.toFun p₀,
        (permProg_wellBehavedProgOn_iff L π pre p₀).mp hp₀_wb, hp₀_nqs⟩))
    · refine Or.inr (Or.inr (Or.inr ⟨π.toFun p₁, π.toFun p₂, π.toFun p₃,
        (permProg_wellBehavedProgOn_iff L π pre p₁).mp hw1,
        (permProg_wellBehavedProgOn_iff L π pre p₂).mp hw2,
        (permProg_wellBehavedProgOn_iff L π pre p₃).mp hw3,
        d12, d13, d23⟩))
  · rintro (h1 | h2 | ⟨p₀, hp₀_wb, hp₀_nqs⟩ | ⟨p₁, p₂, p₃, hw1, hw2, hw3, d12, d13, d23⟩)
    · exact Or.inl (fun b => h1 (π.toFun b))
    · refine Or.inr (Or.inl (fun p₁ p₂ hw1 hw2 heq => ?_))
      have hw1' := (permProg_wellBehavedProgOn_iff L π pre p₁).mp hw1
      have hw2' := (permProg_wellBehavedProgOn_iff L π pre p₂).mp hw2
      exact π.toFun_inj (h2 (π.toFun p₁) (π.toFun p₂) hw1' hw2' heq)
    · refine Or.inr (Or.inr (Or.inl ⟨π.invFun p₀, ?_, ?_⟩))
      · rw [permProg_wellBehavedProgOn_iff, π.right_inv]; exact hp₀_wb
      · change ¬ L.QuerySensitiveOn pre (π.toFun (π.invFun p₀))
        rw [π.right_inv]; exact hp₀_nqs
    · refine Or.inr (Or.inr (Or.inr ⟨π.invFun p₁, π.invFun p₂, π.invFun p₃,
        ?_, ?_, ?_, ?_, ?_, ?_⟩))
      · rw [permProg_wellBehavedProgOn_iff, π.right_inv]; exact hw1
      · rw [permProg_wellBehavedProgOn_iff, π.right_inv]; exact hw2
      · rw [permProg_wellBehavedProgOn_iff, π.right_inv]; exact hw3
      · rw [permProg_produces_invFun_eq L π p₁, permProg_produces_invFun_eq L π p₂]
        exact d12
      · rw [permProg_produces_invFun_eq L π p₁, permProg_produces_invFun_eq L π p₃]
        exact d13
      · rw [permProg_produces_invFun_eq L π p₂, permProg_produces_invFun_eq L π p₃]
        exact d23

/-- **Putnam Permutation Invariance for `SemanticallyClosedOn` and `BiNonInterferingOn`.** -/
theorem permProg_semanticallyClosedOn_iff {SemObs : Type}
    {L₁ L₂ : Language SemObs}
    (π₁ : SyntaxPerm L₁.Prog) (π₂ : SyntaxPerm L₂.Prog)
    (pre : L₁.Query → Prop) (T : Tool L₁ L₂) :
    @Tool.SemanticallyClosedOn SemObs (L₁.permProg π₁) (L₂.permProg π₂) pre
        (Tool.permProg π₁ π₂ T) ↔
      @Tool.SemanticallyClosedOn SemObs L₁ L₂ pre T := by
  constructor
  · intro h p₁ p₂ heq hacc
    have heq' : ∀ q, pre q → ∀ v,
        (L₁.permProg π₁).Produces (π₁.invFun p₁) q v ↔
        (L₁.permProg π₁).Produces (π₁.invFun p₂) q v := by
      rw [permProg_produces_invFun_eq L₁ π₁ p₁, permProg_produces_invFun_eq L₁ π₁ p₂]
      exact heq
    have hacc' : (Tool.permProg π₁ π₂ T (π₁.invFun p₁)).defined := by
      change (T (π₁.toFun (π₁.invFun p₁))).defined
      rw [π₁.right_inv]; exact hacc
    have hres := h (π₁.invFun p₁) (π₁.invFun p₂) heq' hacc'
    change (T (π₁.toFun (π₁.invFun p₂))).defined at hres
    rw [π₁.right_inv] at hres
    exact hres
  · intro h p₁ p₂ heq hacc
    exact h (π₁.toFun p₁) (π₁.toFun p₂) heq hacc

theorem permProg_biNonInterferingOn_iff {SemObs : Type} (L : Language SemObs)
    (π : SyntaxPerm L.Prog) (pre : L.Query → Prop)
    (lowEq : L.Query → L.Query → Prop) (leakEq : SemObs → SemObs → Prop)
    (s : L.Prog) :
    (L.permProg π).BiNonInterferingOn pre lowEq leakEq s ↔
      L.BiNonInterferingOn pre lowEq leakEq (π.toFun s) :=
  Iff.rfl

/-- **Putnam Permutation Invariance for Emitter Compilation:**
    Composing any emitter `emit : L_tgt.Prog → L_asm.Prog` with `π.invFun`
    (`emit' t := π.invFun (emit t)`) compiles into `L_asm.permProg π` if and
    only if `emit` compiles into `L_asm`! -/
theorem permProg_emitterCompiles_iff {SemObs : Type}
    (L_tgt L_asm : Language SemObs)
    (c_asm : BehaviorCodec L_tgt L_asm)
    (π : SyntaxPerm L_asm.Prog)
    (emit : L_tgt.Prog → L_asm.Prog) :
    EmitterCompiles L_tgt (L_asm.permProg π) (c_asm.toPermTgt π)
      (fun t => π.invFun (emit t)) ↔
    EmitterCompiles L_tgt L_asm c_asm emit := by
  constructor
  · intro h t
    have ht := h t
    change ProductiveCompiles L_tgt (L_asm.permProg π) (c_asm.toPermTgt π)
      t (π.invFun (emit t)) at ht
    dsimp [ProductiveCompiles, Compiles, Language.permProg, BehaviorCodec.toPermTgt] at ht ⊢
    rw [π.right_inv] at ht
    exact ht
  · intro h t
    have ht := h t
    dsimp [ProductiveCompiles, Compiles, Language.permProg, BehaviorCodec.toPermTgt] at ht ⊢
    rw [π.right_inv]
    exact ht

/-- **Theorem 1 (`PutnamSyntaxPermutationTheorem` — Master Model-Theoretic
    Invariance Theorem):**
    For any target language `L_asm`, any syntax permutation `π : SyntaxPerm L_asm.Prog`,
    and any emitter `emit : L_tgt.Prog → L_asm.Prog`, replacing `emit` by the
    permuted emitter `fun t => π.invFun (emit t)`, `badAsmProgs` by
    `badAsmProgs.map π.invFun`, and `L_asm` by `L_asm.permProg π` preserves:
    1. `EmitterCompilesWithWitnessesOn` (`Master Theorem 10B`),
    2. `HasProductiveContrastOn`,
    3. `WellBehavedProgOn`, and
    4. `TotalWellBehavedDomainOn`! -/
theorem PutnamSyntaxPermutationTheorem {SemObs : Type}
    [CanonicalConstInit SemObs]
    (L_tgt L_asm : Language SemObs)
    (c_asm : BehaviorCodec L_tgt L_asm)
    (π : SyntaxPerm L_asm.Prog)
    (emit : L_tgt.Prog → L_asm.Prog)
    (dom_asm pre_asm : L_asm.Query → Prop)
    (obsPost_asm : L_asm.Query → SemObs → Prop)
    (goodTgt : L_tgt.Prog)
    (badAsmProgs : List L_asm.Prog) :
    (EmitterCompilesWithWitnessesOn L_tgt (L_asm.permProg π) (c_asm.toPermTgt π)
       (fun t => π.invFun (emit t)) dom_asm pre_asm obsPost_asm
       goodTgt (badAsmProgs.map π.invFun) ↔
     EmitterCompilesWithWitnessesOn L_tgt L_asm c_asm emit dom_asm pre_asm
       obsPost_asm goodTgt badAsmProgs) ∧
    ((L_asm.permProg π).HasProductiveContrastOn pre_asm (π.invFun (emit goodTgt)) ↔
     L_asm.HasProductiveContrastOn pre_asm (emit goodTgt)) ∧
    ((L_asm.permProg π).WellBehavedProgOn pre_asm (π.invFun (emit goodTgt)) ↔
     L_asm.WellBehavedProgOn pre_asm (emit goodTgt)) ∧
    ((L_asm.permProg π).TotalWellBehavedDomainOn pre_asm ↔
     L_asm.TotalWellBehavedDomainOn pre_asm) := by
  have h_allHold :
      AllHold ((badAsmProgs.map π.invFun).map (fun badAsm =>
        π.invFun (emit goodTgt) ≠ badAsm ∧
        (L_asm.permProg π).SpineNonDegenerate pre_asm obsPost_asm
          (π.invFun (emit goodTgt)) badAsm)) ↔
      AllHold (badAsmProgs.map (fun badAsm =>
        emit goodTgt ≠ badAsm ∧
        L_asm.SpineNonDegenerate pre_asm obsPost_asm (emit goodTgt) badAsm)) := by
    induction badAsmProgs with
    | nil => exact Iff.rfl
    | cons b bs ih =>
      dsimp [List.map, AllHold]
      have h_ne : (π.invFun (emit goodTgt) ≠ π.invFun b) ↔ (emit goodTgt ≠ b) :=
        ⟨fun h heq => h (congrArg π.invFun heq), fun h heq => h (π.invFun_inj heq)⟩
      have h_nd :
          (L_asm.permProg π).SpineNonDegenerate pre_asm obsPost_asm
            (π.invFun (emit goodTgt)) (π.invFun b) ↔
          L_asm.SpineNonDegenerate pre_asm obsPost_asm (emit goodTgt) b := by
        rw [permProg_spineNonDegenerate_iff, π.right_inv, π.right_inv]
      exact ⟨fun ⟨⟨hne, hnd⟩, hrest⟩ => ⟨⟨h_ne.mp hne, h_nd.mp hnd⟩, ih.mp hrest⟩,
             fun ⟨⟨hne, hnd⟩, hrest⟩ => ⟨⟨h_ne.mpr hne, h_nd.mpr hnd⟩, ih.mpr hrest⟩⟩
  have h_ne_nil : badAsmProgs.map π.invFun ≠ [] ↔ badAsmProgs ≠ [] := by
    cases badAsmProgs <;> simp
  have h_emit := permProg_emitterCompiles_iff L_tgt L_asm c_asm π emit
  have h_ver :
      (L_asm.permProg π).VerifiedSpineOn dom_asm pre_asm obsPost_asm (π.invFun (emit goodTgt)) ↔
      L_asm.VerifiedSpineOn dom_asm pre_asm obsPost_asm (emit goodTgt) := by
    rw [permProg_verifiedSpineOn_iff, π.right_inv]
  refine ⟨?_, ?_, ?_, permProg_totalWellBehavedDomainOn_iff L_asm π pre_asm⟩
  · exact ⟨fun ⟨he, hv, hn, ha⟩ => ⟨h_emit.mp he, h_ver.mp hv, h_ne_nil.mp hn, h_allHold.mp ha⟩,
           fun ⟨he, hv, hn, ha⟩ => ⟨h_emit.mpr he, h_ver.mpr hv, h_ne_nil.mpr hn, h_allHold.mpr ha⟩⟩
  · rw [permProg_hasProductiveContrastOn_iff, π.right_inv]
  · rw [permProg_wellBehavedProgOn_iff, π.right_inv]

/-!
### Corollary 1A (`PENTEST-R3-4` Concrete Instantiation): Spoofing `"xor eax, eax\nret"` via Syntax Transposition
-/

inductive SimpleIR where
  | addOne
  | badZero
  deriving DecidableEq

abbrev L_simple_ir : Language Nat :=
  Language.mkSimple SimpleIR Nat Nat (fun p q => match p with
    | .addOne  => Partial.pure (fun o => o = q + 1)
    | .badZero => Partial.pure (fun o => o = 0))

/-- Honest x86-64 operational semantics for three concrete assembly strings. -/
abbrev L_x86_real : Language Nat :=
  Language.mkSimple String Nat Nat (fun s q =>
    if s = "mov eax, edi; inc eax; ret" then
      Partial.pure (fun o => o = q + 1)
    else if s = "xor eax, eax\nret" then
      Partial.pure (fun o => o = 0)
    else
      Partial.ub)

def honestEmitX86 : SimpleIR → String
  | .addOne  => "mov eax, edi; inc eax; ret"
  | .badZero => "xor eax, eax\nret"

def trojanEmitXorZero : SimpleIR → String
  | .addOne  => "xor eax, eax\nret"
  | .badZero => "mov eax, edi; inc eax; ret"

def π_x86_swap : SyntaxPerm String :=
  SyntaxPerm.swap "mov eax, edi; inc eax; ret" "xor eax, eax\nret"

def c_ir_to_x86 : BehaviorCodec L_simple_ir L_x86_real where
  encodeQuery := id
  decodeQuery := id
  encodeOut   := id
  decodeOut   := some
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl
  obs_decodeOut _ _ h       := Option.some.inj h

/-- **Corollary 1A (`PENTEST-R3-4` Mechanized Proof):**
    `trojanEmitXorZero` (which emits `"xor eax, eax\nret"` for `.addOne`)
    is equal to `fun p => π_x86_swap.invFun (honestEmitX86 p)`, and therefore
    satisfies `EmitterCompilesWithWitnessesOn` and `HasProductiveContrastOn`
    into the syntax-permuted language `L_x86_real.permProg π_x86_swap`! -/
theorem pentest_r3_4_corollary_trojan_emitter_passes_under_permuted_semantics :
    (∀ p, trojanEmitXorZero p = π_x86_swap.invFun (honestEmitX86 p)) ∧
    EmitterCompilesWithWitnessesOn L_simple_ir (L_x86_real.permProg π_x86_swap)
      (c_ir_to_x86.toPermTgt π_x86_swap) trojanEmitXorZero
      L_x86_real.dom (fun q => q < 100) (fun q v => v = q + 1)
      .addOne ["mov eax, edi; inc eax; ret"] ∧
    (L_x86_real.permProg π_x86_swap).HasProductiveContrastOn
      (fun q => q < 100) (trojanEmitXorZero .addOne) := by
  have h_eq_emit : ∀ p, trojanEmitXorZero p = π_x86_swap.invFun (honestEmitX86 p) := by
    intro p; cases p <;> decide
  have h_honest :
      EmitterCompilesWithWitnessesOn L_simple_ir L_x86_real c_ir_to_x86
        honestEmitX86 L_x86_real.dom (fun q => q < 100) (fun q v => v = q + 1)
        .addOne ["xor eax, eax\nret"] := by
    refine ⟨?_,
      ⟨Or.inl ⟨0, by decide⟩,
       fun q _ => ⟨trivial, q + 1, rfl⟩,
       fun q _ => ⟨trivial, fun o ho => ho⟩⟩,
      by decide,
      ⟨⟨by decide, Or.inl ⟨0, by decide, 0, ⟨trivial, 0, rfl, rfl⟩, by decide⟩⟩,
       trivial⟩⟩
    intro t
    cases t with
    | addOne =>
      exact ⟨fun q _ => ⟨trivial, fun o ho => ⟨o, rfl, ho⟩⟩,
             fun q _ => ⟨trivial, q + 1, rfl⟩⟩
    | badZero =>
      exact ⟨fun q _ => ⟨trivial, fun o ho => ⟨o, rfl, ho⟩⟩,
             fun q _ => ⟨trivial, 0, rfl⟩⟩
  have h_contrast :
      L_x86_real.HasProductiveContrastOn (fun q => q < 100) (honestEmitX86 .addOne) :=
    ⟨⟨"ud2", fun _ _ h => h⟩,
     ⟨"xor eax, eax\nret", fun _ _ => ⟨trivial, 0, rfl⟩,
      0, 1, 0, by decide, ⟨trivial, 1, rfl, rfl⟩, ⟨trivial, 0, rfl, rfl⟩, by decide⟩⟩
  have h_putnam := PutnamSyntaxPermutationTheorem L_simple_ir L_x86_real c_ir_to_x86
    π_x86_swap honestEmitX86 L_x86_real.dom (fun q => q < 100)
    (fun q v => v = q + 1) .addOne ["xor eax, eax\nret"]
  have h_perm_emit := h_putnam.1.mpr h_honest
  have h_perm_contrast := h_putnam.2.1.mpr h_contrast
  have h_fun_eq : (fun t => π_x86_swap.invFun (honestEmitX86 t)) = trojanEmitXorZero :=
    funext (fun p => (h_eq_emit p).symm)
  have h_list_eq :
      ["xor eax, eax\nret"].map π_x86_swap.invFun = ["mov eax, edi; inc eax; ret"] := by
    decide
  rw [h_fun_eq, h_list_eq] at h_perm_emit
  rw [← h_eq_emit .addOne] at h_perm_contrast
  exact ⟨h_eq_emit, h_perm_emit, h_perm_contrast⟩

/-!
### Corollary 1B (`PENTEST-R2-1` Circular `diskLang` Tautology Theorem)
-/

/-- `Candidate 006`'s `L.diskLang parse`, which defines the meaning of an on-disk
    string `s` by parsing `s` back into `L.Prog` and delegating to `L.sem`. -/
abbrev Language.diskLang {SemObs : Type} (L : Language SemObs)
    (parse : String → Option L.Prog) : Language SemObs where
  Prog  := String
  Query := L.Query
  Out   := L.Out
  obs   := L.obs
  sem   := fun s q => match parse s with
    | some p => L.sem p q
    | none   => Partial.ub

def c_to_diskLang {SemObs : Type} (L : Language SemObs)
    (parse : String → Option L.Prog) : BehaviorCodec L (L.diskLang parse) where
  encodeQuery := id
  decodeQuery := id
  encodeOut   := id
  decodeOut   := some
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl
  obs_decodeOut _ _ h       := congrArg L.obs (Option.some.inj h)

/-- **Corollary 1B (`PENTEST-R2-1` Circular `diskLang` Theorem):**
    For *any* emitter `emit : L.Prog → String` and parser `parse : String → Option L.Prog`
    satisfying the round-trip identity `∀ t, parse (emit t) = some t`,
    `EmitterCompiles L (L.diskLang parse) (c_to_diskLang L parse) emit` holds
    **regardless of what strings `emit` outputs** (even `emit _ := "rm -rf /"`
    or `emit .addOne := "xor eax, eax\nret"`!). -/
theorem pentest_r2_1_circular_diskLang_universal_tautology {SemObs : Type}
    (L : Language SemObs)
    (emit : L.Prog → String)
    (parse : String → Option L.Prog)
    (h_roundtrip : ∀ t : L.Prog, parse (emit t) = some t) :
    EmitterCompiles L (L.diskLang parse) (c_to_diskLang L parse) emit := by
  intro t
  have h_sem_eq : ∀ q : L.Query, (L.diskLang parse).sem (emit t) q = L.sem t q := by
    intro q
    dsimp [Language.diskLang]
    rw [h_roundtrip t]
  constructor
  · intro q h_src
    change (L.sem t q).defined at h_src
    rw [h_sem_eq q]
    exact ⟨h_src, fun o ho => ⟨o, rfl, ho⟩⟩
  · intro q h_prod
    change ∃ h₁ : (L.sem t q).defined, ∃ o₁, (L.sem t q).val h₁ o₁ at h_prod
    rw [h_sem_eq q]
    exact h_prod

/-!
## Part III: Impossibility of Lexical/Prefix Heuristics on Stateful Operational Languages (`PENTEST-R4-2A/B`) & Emitter Surjectivity Impossibility (`PENTEST-R4-8`)
-/

/-- Stateful machine register file `(edi_arg, eax_ret)`. -/
structure RegState where
  edi : Nat
  eax : Nat
  deriving DecidableEq

/-- Elementary instructions of a stateful sequential assembly language. -/
inductive AsmInstr where
  | zeroClear               -- `xor eax, eax` (`eax := 0`)
  | loadAndInc              -- `mov eax, edi; inc eax` (`eax := edi + 1`)
  | addImm (k : Nat)        -- `add eax, k` (`eax := eax + k`)
  | label (lbl : String)    -- `main:` (`no-op label / directive`)
  | trap                    -- `ud2` (`hardware fault / UB`)
  deriving DecidableEq

/-- Single-instruction state transformer (`Option RegState`). -/
def evalInstr (i : AsmInstr) (st : RegState) : Option RegState :=
  match i with
  | .zeroClear  => some { st with eax := 0 }
  | .loadAndInc => some { st with eax := st.edi + 1 }
  | .addImm k   => some { st with eax := st.eax + k }
  | .label _    => some st
  | .trap       => none

/-- Sequential composition of instructions (`evalSeq (i :: rest) = evalSeq rest ∘ evalInstr i`). -/
def evalSeq : List AsmInstr → RegState → Option RegState
  | [],        st => some st
  | i :: rest, st =>
    match evalInstr i st with
    | some st' => evalSeq rest st'
    | none     => none

/-- Sequential composition law: `evalSeq (p₁ ++ p₂) st = (evalSeq p₁ st).bind (evalSeq p₂)`. -/
theorem evalSeq_append (p₁ p₂ : List AsmInstr) (st : RegState) :
    evalSeq (p₁ ++ p₂) st = Option.bind (evalSeq p₁ st) (evalSeq p₂) := by
  induction p₁ generalizing st with
  | nil => rfl
  | cons i rest ih =>
    dsimp [evalSeq]
    cases evalInstr i st with
    | none     => rfl
    | some st' => exact ih st'

/-- Operational `Language Nat` of sequential assembly programs `List AsmInstr`. -/
abbrev L_seq_asm : Language Nat :=
  Language.mkSimple (List AsmInstr) Nat Nat (fun prog q =>
    match evalSeq prog { edi := q, eax := 0 } with
    | some st => Partial.pure (fun o => o = st.eax)
    | none    => Partial.ub)

/-- `Candidate 016`'s `validZeroClear` axiom generalized to any lexical classifier
    `H : List AsmInstr → Bool`: every program flagged by `H` (`H p = true`) must
    only produce `0`. -/
def EnforcesZeroClearRule (L : Language Nat) (pre : L.Query → Prop)
    (H : L.Prog → Bool) : Prop :=
  ∀ (p : L.Prog) (q : L.Query) (v : Nat),
    pre q → H p = true → L.Produces p q v → v = 0

/-- Wildcard-prefix lexical classifier (analogous to `isZeroClearAsmMnemonic`,
    which matches `'x' :: 'o' :: 'r' :: 'e' :: 'a' :: 'x' :: ',' :: 'e' :: 'a' :: 'x' :: _`). -/
def isLeadingZeroClearPrefix : List AsmInstr → Bool
  | .zeroClear :: _ => true
  | _               => false

/-- **Theorem 2A (`LexicalHeuristicDualFailureTheorem` — `PENTEST-R4-2A` & `R4-2B`):**
    For the stateful sequential instruction language `L_seq_asm` and any lexical
    classifier `H : List AsmInstr → Bool`:
    1. **False Positive / Honest Lockout (`R4-2A`):** If `H` flags any instruction
       sequence starting with `.zeroClear` (`∀ tail, H (.zeroClear :: tail) = true`,
       as `isLeadingZeroClearPrefix` and `isZeroClearAsmMnemonic` do), then the
       honest accumulator-initializing routine `p_accum = [.zeroClear, .loadAndInc]`
       (`xor eax, eax; mov eax, edi; inc eax; ret`) computes `q + 1` via
       state overwrite and **falsifies `EnforcesZeroClearRule`** on any precondition
       containing `q = 0`!
    2. **False Negative / Labelled Bypass (`R4-2B`):** If `H` fails to match when
       a label `.label "main"` is prepended (`H [.label "main", .zeroClear] = false`,
       as `isLeadingZeroClearPrefix` and `isZeroClearAsmMnemonic` do), then
       `p_labelled = [.label "main", .zeroClear]` has `H p_labelled = false` even
       though its operational behavior in `L_seq_asm` is **100% identical** to
       `[.zeroClear]` (`evalSeq [.label "main", .zeroClear] = evalSeq [.zeroClear]`),
       allowing a spoofed language `L_seq_asm.permProg (SyntaxPerm.swap [.loadAndInc] [.label "main", .zeroClear])`
       to satisfy `EnforcesZeroClearRule` while assigning `q + 1` to
       `[.label "main", .zeroClear]`! -/
theorem LexicalHeuristicDualFailureTheorem
    (H : List AsmInstr → Bool)
    (h_prefix_wildcard : ∀ tail : List AsmInstr, H (.zeroClear :: tail) = true)
    (h_label_blind : H [.label "main", .zeroClear] = false) :
    (¬ EnforcesZeroClearRule L_seq_asm (fun q => q < 100) H) ∧
    (H [.label "main", .zeroClear] = false ∧
      ∀ st : RegState,
        evalSeq [.label "main", .zeroClear] st = evalSeq [.zeroClear] st) ∧
    L_seq_asm.Produces [.zeroClear, .loadAndInc] 0 1 ∧
    L_seq_asm.Produces [.label "main", .zeroClear] 0 0 ∧
    isLeadingZeroClearPrefix [.zeroClear, .loadAndInc] = true ∧
    isLeadingZeroClearPrefix [.label "main", .zeroClear] = false := by
  refine ⟨?_, ⟨h_label_blind, fun _ => rfl⟩,
    ⟨trivial, 1, rfl, rfl⟩, ⟨trivial, 0, rfl, rfl⟩, rfl, rfl⟩
  intro h_rule
  have h10 : (1 : Nat) = 0 :=
    h_rule [.zeroClear, .loadAndInc] 0 1 (by decide)
      (h_prefix_wildcard [.loadAndInc])
      ⟨trivial, 1, rfl, rfl⟩
  cases h10

/-- **Theorem 2A-iii (Universal No-Go Theorem for Bounded-Prefix Classifiers on
    Sequential Languages):**
    For *any* lookahead bound `k : Nat` and *any* classifier `H : List AsmInstr → Bool`
    whose decision on `p` depends only on the first `k` instructions `p.take k`
    (`∀ p₁ p₂, p₁.take k = p₂.take k → H p₁ = H p₂`), `H` **cannot** both:
    - Flag the `k`-label-prefixed zero-clear routine `List.replicate k (.label "nop") ++ [.zeroClear]`
      (`H p_zero = true`), and
    - Satisfy `EnforcesZeroClearRule L_seq_asm (fun q => q < 100) H`!
    Because appending `.loadAndInc` at position `k + 1` shares the exact same
    `k`-instruction prefix (`take k`) yet overwrites `eax` with `q + 1`! -/
theorem prefix_classifier_universal_impossibility
    (k : Nat) (H : List AsmInstr → Bool)
    (h_depends_on_take : ∀ p₁ p₂ : List AsmInstr, p₁.take k = p₂.take k → H p₁ = H p₂) :
    let p_zero : List AsmInstr  := List.replicate k (AsmInstr.label "nop") ++ [AsmInstr.zeroClear]
    let p_accum : List AsmInstr := List.replicate k (AsmInstr.label "nop") ++ [AsmInstr.zeroClear, AsmInstr.loadAndInc]
    (∀ q : Nat, L_seq_asm.Produces p_zero q 0) ∧
    (∀ q : Nat, L_seq_asm.Produces p_accum q (q + 1)) ∧
    ¬ (H p_zero = true ∧ EnforcesZeroClearRule L_seq_asm (fun q => q < 100) H) := by
  intro p_zero p_accum
  have h_eval_nops : ∀ (n : Nat) (tail : List AsmInstr) (st : RegState),
      evalSeq (List.replicate n (AsmInstr.label "nop") ++ tail) st = evalSeq tail st := by
    intro n
    induction n with
    | zero => intro _ _; rfl
    | succ m ih =>
      intro tail st
      dsimp [List.replicate, evalSeq, evalInstr]
      exact ih tail st
  have h_take_eq : ∀ (n : Nat) (t₁ t₂ : List AsmInstr),
      (List.replicate n (AsmInstr.label "nop") ++ t₁).take n =
      (List.replicate n (AsmInstr.label "nop") ++ t₂).take n := by
    intro n
    induction n with
    | zero => intro _ _; rfl
    | succ m ih =>
      intro t₁ t₂
      dsimp [List.replicate, List.take]
      exact congrArg (List.cons (AsmInstr.label "nop")) (ih t₁ t₂)
  have h_sem_zero : ∀ q : Nat,
      L_seq_asm.sem p_zero q = Partial.pure (fun o => o = 0) := by
    intro q
    dsimp [L_seq_asm, Language.mkSimple, p_zero]
    rw [h_eval_nops k [AsmInstr.zeroClear] { edi := q, eax := 0 }]
    rfl
  have h_sem_accum : ∀ q : Nat,
      L_seq_asm.sem p_accum q = Partial.pure (fun o => o = q + 1) := by
    intro q
    dsimp [L_seq_asm, Language.mkSimple, p_accum]
    rw [h_eval_nops k [AsmInstr.zeroClear, AsmInstr.loadAndInc] { edi := q, eax := 0 }]
    rfl
  have h_prod_zero : ∀ q : Nat, L_seq_asm.Produces p_zero q 0 := by
    intro q
    unfold Language.Produces
    rw [h_sem_zero q]
    exact ⟨trivial, 0, rfl, rfl⟩
  have h_prod_accum : ∀ q : Nat, L_seq_asm.Produces p_accum q (q + 1) := by
    intro q
    unfold Language.Produces
    rw [h_sem_accum q]
    exact ⟨trivial, q + 1, rfl, rfl⟩
  refine ⟨h_prod_zero, h_prod_accum, ?_⟩
  rintro ⟨h_true, h_rule⟩
  have h_accum_true : H p_accum = true := by
    rw [← h_true]
    exact h_depends_on_take p_accum p_zero
      (h_take_eq k [AsmInstr.zeroClear, AsmInstr.loadAndInc] [AsmInstr.zeroClear])
  have h10 : (1 : Nat) = 0 :=
    h_rule p_accum 0 1 (by decide) h_accum_true (h_prod_accum 0)
  cases h10

/-!
### Theorem 2B (`EmitterSurjectivityImpossibility`, `PENTEST-R4-8`)
-/

/-- Clause 3 of `Candidate 016`'s `EmitterCompilesStrongWithWitnessesOn`:
    Requires every productive, query-sensitive assembly program `s : L_asm.Prog`
    to be in the image of a productive target program `t : L_tgt.Prog` under `emit`. -/
def EmitterQuerySensitiveSurjective {SemObs : Type}
    (L_tgt L_asm : Language SemObs)
    (c_asm : BehaviorCodec L_tgt L_asm)
    (emit : L_tgt.Prog → L_asm.Prog)
    (pre_asm : L_asm.Query → Prop) : Prop :=
  ∀ s : L_asm.Prog,
    L_asm.ProductiveOn pre_asm s →
    L_asm.QuerySensitiveOn pre_asm s →
    ∃ t : L_tgt.Prog,
      L_tgt.ProductiveOn (fun q₁ => pre_asm (c_asm.encodeQuery q₁)) t ∧
      emit t = s

/-- **Theorem 2B (`EmitterSurjectivityImpossibility` — `PENTEST-R4-8`):**
    Whenever the source/IR language `L_tgt` has at most one productive program
    on `pre₁` (`∀ t₁ t₂, ProductiveOn pre₁ t₁ → ProductiveOn pre₁ t₂ → t₁ = t₂`,
    which holds for every single-function verification unit!) and the target
    ISA `L_asm` contains at least two distinct productive query-sensitive
    programs `s₁ ≠ s₂` (e.g., `"lea eax, [rdi + 1]\nret"` and
    `"lea eax, [rdi + 2]\nret"`), **no emitter `emit : L_tgt.Prog → L_asm.Prog`
    can satisfy `EmitterQuerySensitiveSurjective` (`False`)**! -/
theorem EmitterSurjectivityImpossibility {SemObs : Type}
    (L_tgt L_asm : Language SemObs)
    (c_asm : BehaviorCodec L_tgt L_asm)
    (pre_asm : L_asm.Query → Prop)
    (h_single_src : ∀ t₁ t₂ : L_tgt.Prog,
      L_tgt.ProductiveOn (fun q₁ => pre_asm (c_asm.encodeQuery q₁)) t₁ →
      L_tgt.ProductiveOn (fun q₁ => pre_asm (c_asm.encodeQuery q₁)) t₂ →
      t₁ = t₂)
    (s₁ s₂ : L_asm.Prog)
    (h_ne : s₁ ≠ s₂)
    (h_prod₁ : L_asm.ProductiveOn pre_asm s₁)
    (h_qs₁   : L_asm.QuerySensitiveOn pre_asm s₁)
    (h_prod₂ : L_asm.ProductiveOn pre_asm s₂)
    (h_qs₂   : L_asm.QuerySensitiveOn pre_asm s₂) :
    ∀ emit : L_tgt.Prog → L_asm.Prog,
      ¬ EmitterQuerySensitiveSurjective L_tgt L_asm c_asm emit pre_asm := by
  intro emit h_surj
  have ⟨t₁, hp₁, he₁⟩ := h_surj s₁ h_prod₁ h_qs₁
  have ⟨t₂, hp₂, he₂⟩ := h_surj s₂ h_prod₂ h_qs₂
  have ht_eq : t₁ = t₂ := h_single_src t₁ t₂ hp₁ hp₂
  exact h_ne (by rw [← he₁, ← he₂, ht_eq])

/-!
## Part IV: The Next-Generation Minimal Semantic Blueprint (`NextGen`)
-/

namespace NextGen

/-- **Primitive 1 (`FramedCodec L₁ L₂ Frame`):**
    Replaces `Candidate 016`'s 7 ad-hoc typeclasses (`CanonicalQueryProjection`,
    `CanonicalOutEncoding`, `CanonicalABIState`, `BijectiveFrameFibers`,
    `ABIConformant`, `WellFormedABI`, `ObsInjectiveProgOn`) with a single
    bidirectional **Cartesian Lens / Frame Decomposition** over `Frame : Type`:
    - `splitQuery : L₂.Query → L₁.Query × Frame` decomposes every target query
      into its architectural source query `q₁` and callee-saved frame `f_in`.
    - `joinQuery : L₁.Query → Frame → L₂.Query` reconstructs the target query.
    - `decodeOut : L₂.Out → Option (L₁.Out × Frame)` extracts the decoded source
      outcome `o₁` and exit callee-saved frame `f_out` (while quotienting out
      caller-saved scratch registers such as `rcx` or dead flags!). -/
structure FramedCodec {SemObs : Type} (L₁ L₂ : Language SemObs) (Frame : Type) where
  splitQuery        : L₂.Query → L₁.Query × Frame
  joinQuery         : L₁.Query → Frame → L₂.Query
  defaultFrame      : Frame
  encodeOut         : L₁.Out → Frame → L₂.Out
  decodeOut         : L₂.Out → Option (L₁.Out × Frame)
  split_join_query  : ∀ q₁ f, splitQuery (joinQuery q₁ f) = (q₁, f)
  join_split_query  : ∀ q₂, joinQuery (splitQuery q₂).1 (splitQuery q₂).2 = q₂
  decodeOut_encodeOut : ∀ o₁ f, decodeOut (encodeOut o₁ f) = some (o₁, f)
  obs_decodeOut     : ∀ o₂ o₁ f, decodeOut o₂ = some (o₁, f) → L₂.obs o₂ = L₁.obs o₁

namespace FramedCodec

/-- Every `FramedCodec` canonically induces a standard `BehaviorCodec`. -/
def toBehaviorCodec {SemObs : Type} {L₁ L₂ : Language SemObs} {Frame : Type}
    (c : FramedCodec L₁ L₂ Frame) : BehaviorCodec L₁ L₂ where
  encodeQuery q₁ := c.joinQuery q₁ c.defaultFrame
  decodeQuery q₂ := (c.splitQuery q₂).1
  encodeOut o₁   := c.encodeOut o₁ c.defaultFrame
  decodeOut o₂   := (c.decodeOut o₂).map Prod.fst
  decodeQuery_encodeQuery q₁ := by
    change (c.splitQuery (c.joinQuery q₁ c.defaultFrame)).1 = q₁
    rw [c.split_join_query]
  decodeOut_encodeOut o₁ := by
    dsimp [Option.map]
    rw [c.decodeOut_encodeOut]
  obs_decodeOut o₂ o₁ h := by
    cases h_dec : c.decodeOut o₂ with
    | none =>
      rw [h_dec] at h
      cases h
    | some pair =>
      rw [h_dec] at h
      dsimp [Option.map] at h
      have h_eq : pair.1 = o₁ := Option.some.inj h
      rw [← h_eq]
      exact c.obs_decodeOut o₂ pair.1 pair.2 h_dec

/-- Identity `FramedCodec` with `Frame = Unit`. -/
def id {SemObs : Type} (L : Language SemObs) : FramedCodec L L Unit where
  splitQuery q        := (q, ())
  joinQuery q _       := q
  defaultFrame        := ()
  encodeOut o _       := o
  decodeOut o         := some (o, ())
  split_join_query _ _ := rfl
  join_split_query _   := rfl
  decodeOut_encodeOut _ _ := rfl
  obs_decodeOut _ _ _ h := by
    have h_inj := Option.some.inj h
    exact congrArg L.obs (congrArg Prod.fst h_inj)

/-- Vertical composition of `FramedCodec L₁ L₂ F₁` and `FramedCodec L₂ L₃ F₂`
    over the product frame `F₁ × F₂`. -/
def comp {SemObs : Type} {L₁ L₂ L₃ : Language SemObs} {F₁ F₂ : Type}
    (c₁₂ : FramedCodec L₁ L₂ F₁) (c₂₃ : FramedCodec L₂ L₃ F₂) :
    FramedCodec L₁ L₃ (F₁ × F₂) where
  splitQuery q₃ :=
    let p₂ := c₂₃.splitQuery q₃
    let p₁ := c₁₂.splitQuery p₂.1
    (p₁.1, (p₁.2, p₂.2))
  joinQuery q₁ f :=
    c₂₃.joinQuery (c₁₂.joinQuery q₁ f.1) f.2
  defaultFrame := (c₁₂.defaultFrame, c₂₃.defaultFrame)
  encodeOut o₁ f :=
    c₂₃.encodeOut (c₁₂.encodeOut o₁ f.1) f.2
  decodeOut o₃ :=
    match c₂₃.decodeOut o₃ with
    | some p₂ =>
      match c₁₂.decodeOut p₂.1 with
      | some p₁ => some (p₁.1, (p₁.2, p₂.2))
      | none    => none
    | none => none
  split_join_query q₁ f := by
    have h₂₃ := c₂₃.split_join_query (c₁₂.joinQuery q₁ f.1) f.2
    have h₁₂ := c₁₂.split_join_query q₁ f.1
    change (let p₂ := c₂₃.splitQuery (c₂₃.joinQuery (c₁₂.joinQuery q₁ f.1) f.2);
            let p₁ := c₁₂.splitQuery p₂.1;
            (p₁.1, (p₁.2, p₂.2))) = (q₁, f)
    rw [h₂₃]
    change (let p₁ := c₁₂.splitQuery (c₁₂.joinQuery q₁ f.1);
            (p₁.1, (p₁.2, f.2))) = (q₁, f)
    rw [h₁₂]
  join_split_query q₃ := by
    change c₂₃.joinQuery
      (c₁₂.joinQuery (c₁₂.splitQuery (c₂₃.splitQuery q₃).1).1
                     (c₁₂.splitQuery (c₂₃.splitQuery q₃).1).2)
      (c₂₃.splitQuery q₃).2 = q₃
    rw [c₁₂.join_split_query, c₂₃.join_split_query]
  decodeOut_encodeOut o₁ f := by
    have h₂₃ := c₂₃.decodeOut_encodeOut (c₁₂.encodeOut o₁ f.1) f.2
    have h₁₂ := c₁₂.decodeOut_encodeOut o₁ f.1
    change (match c₂₃.decodeOut (c₂₃.encodeOut (c₁₂.encodeOut o₁ f.1) f.2) with
      | some p₂ =>
        match c₁₂.decodeOut p₂.1 with
        | some p₁ => some (p₁.1, (p₁.2, p₂.2))
        | none    => none
      | none => none) = some (o₁, f)
    rw [h₂₃]
    dsimp
    rw [h₁₂]
  obs_decodeOut o₃ o₁ f h := by
    cases h₂₃ : c₂₃.decodeOut o₃ with
    | none => rw [h₂₃] at h; cases h
    | some p₂ =>
      rw [h₂₃] at h
      dsimp at h
      cases h₁₂ : c₁₂.decodeOut p₂.1 with
      | none => rw [h₁₂] at h; cases h
      | some p₁ =>
        rw [h₁₂] at h
        dsimp at h
        have h_eq := Option.some.inj h
        have ho₁ : p₁.1 = o₁ := congrArg Prod.fst h_eq
        rw [← ho₁]
        exact Eq.trans (c₂₃.obs_decodeOut o₃ p₂.1 p₂.2 h₂₃)
                       (c₁₂.obs_decodeOut p₂.1 p₁.1 p₁.2 h₁₂)

end FramedCodec

/-- **Unconditional Frame-Preserving Productive Compilation (`FramedProductiveCompiles`):**
    At every target query `q₂` with `(q₁, f_in) = c.splitQuery q₂`:
    1. Whenever `L₁.sem s q₁` is defined (`h₁`), `L₂.sem t q₂` is defined (`h₂`)
       and every target outcome `o₂` decodes to `some (o₁, f_in)` where `o₁` is
       a valid source outcome of `s` at `q₁` AND the exit frame equals the entry
       frame `f_in` (`f_out = f_in`)!
    2. Whenever `s` is productive at `q₁`, `t` is productive at `q₂`. -/
def FramedProductiveCompiles {SemObs : Type} {L₁ L₂ : Language SemObs} {Frame : Type}
    (c : FramedCodec L₁ L₂ Frame) (s : L₁.Prog) (t : L₂.Prog) : Prop :=
  (∀ (q₂ : L₂.Query) (h₁ : (L₁.sem s (c.splitQuery q₂).1).defined),
    ∃ h₂ : (L₂.sem t q₂).defined,
      ∀ o₂ : L₂.Out, (L₂.sem t q₂).val h₂ o₂ →
        ∃ o₁ : L₁.Out,
          c.decodeOut o₂ = some (o₁, (c.splitQuery q₂).2) ∧
          (L₁.sem s (c.splitQuery q₂).1).val h₁ o₁) ∧
  (∀ q₂ : L₂.Query,
    (∃ h₁ : (L₁.sem s (c.splitQuery q₂).1).defined,
      ∃ o₁ : L₁.Out, (L₁.sem s (c.splitQuery q₂).1).val h₁ o₁) →
    (∃ h₂ : (L₂.sem t q₂).defined,
      ∃ o₂ : L₂.Out, (L₂.sem t q₂).val h₂ o₂))

theorem FramedProductiveCompiles.refl {SemObs : Type} (L : Language SemObs)
    (p : L.Prog) : FramedProductiveCompiles (FramedCodec.id L) p p :=
  ⟨fun _ h₁ => ⟨h₁, fun o ho => ⟨o, rfl, ho⟩⟩, fun _ h => h⟩

/-- Vertical transitivity of `FramedProductiveCompiles` across `FramedCodec.comp`. -/
theorem FramedProductiveCompiles.comp {SemObs : Type}
    {L₁ L₂ L₃ : Language SemObs} {F₁ F₂ : Type}
    {c₁₂ : FramedCodec L₁ L₂ F₁} {c₂₃ : FramedCodec L₂ L₃ F₂}
    {p₁ : L₁.Prog} {p₂ : L₂.Prog} {p₃ : L₃.Prog}
    (h₁₂ : FramedProductiveCompiles c₁₂ p₁ p₂)
    (h₂₃ : FramedProductiveCompiles c₂₃ p₂ p₃) :
    FramedProductiveCompiles (c₁₂.comp c₂₃) p₁ p₃ := by
  constructor
  · intro q₃ h₁
    have ⟨h₂, hval₁₂⟩ := h₁₂.1 (c₂₃.splitQuery q₃).1 h₁
    have ⟨h₃, hval₂₃⟩ := h₂₃.1 q₃ h₂
    refine ⟨h₃, fun o₃ ho₃ => ?_⟩
    have ⟨o₂, hdec₂₃, ho₂⟩ := hval₂₃ o₃ ho₃
    have ⟨o₁, hdec₁₂, ho₁⟩ := hval₁₂ o₂ ho₂
    refine ⟨o₁, ?_, ho₁⟩
    change (match c₂₃.decodeOut o₃ with
      | some p₂ =>
        match c₁₂.decodeOut p₂.1 with
        | some p₁ => some (p₁.1, (p₁.2, p₂.2))
        | none    => none
      | none => none) =
      some (o₁, ((c₁₂.splitQuery (c₂₃.splitQuery q₃).1).2, (c₂₃.splitQuery q₃).2))
    rw [hdec₂₃]
    dsimp
    rw [hdec₁₂]
  · intro q₃ hprod₁
    exact h₂₃.2 q₃ (h₁₂.2 (c₂₃.splitQuery q₃).1 hprod₁)

/-- Every `FramedProductiveCompiles` proof implies observable spine preservation:
    every observable output produced by `t` at `q₂` is produced by `s` at
    `(c.splitQuery q₂).1`. -/
theorem FramedProductiveCompiles.produces_reflect {SemObs : Type}
    {L₁ L₂ : Language SemObs} {Frame : Type}
    {c : FramedCodec L₁ L₂ Frame} {s : L₁.Prog} {t : L₂.Prog}
    (h_comp : FramedProductiveCompiles c s t)
    (q₂ : L₂.Query) (v : SemObs)
    (h₁ : (L₁.sem s (c.splitQuery q₂).1).defined)
    (h_prod₂ : L₂.Produces t q₂ v) :
    L₁.Produces s (c.splitQuery q₂).1 v := by
  rcases h_prod₂ with ⟨h₂, o₂, ho₂, hobs₂⟩
  have ⟨_, hval⟩ := h_comp.1 q₂ h₁
  have ⟨o₁, hdec, ho₁⟩ := hval o₂ ho₂
  have hobs_eq := c.obs_decodeOut o₂ o₁ (c.splitQuery q₂).2 hdec
  exact ⟨h₁, o₁, ho₁, Eq.trans hobs_eq.symm hobs₂⟩

/-- **Single Canonical Master Bundle (`VerifiedCompilerBase`):**
    Every verification theorem in the Next-Generation Blueprint either IS
    `VerifiedCompilerBase` or `extends VerifiedCompilerBase`, making clause-omission
    bugs (`PENTEST-R4-10A/B`) structurally impossible! -/
structure VerifiedCompilerBase {SemObs : Type}
    (L_src L_tgt : Language SemObs)
    (Frame : Type)
    (c : FramedCodec L_src L_tgt Frame)
    (tool : Tool L_src L_tgt)
    (AcceptedDom : L_src.Prog → Prop)
    (pre : L_src.Query → Prop)
    (specSuite : List (L_src.Prog × (L_src.Query → SemObs → Prop)))
    (badProgs : List L_src.Prog) : Prop where
  /-- Non-vacuous precondition witness. -/
  pre_inhabited : ∃ q₀ : L_src.Query, pre q₀
  /-- Soundness & frame preservation on all accepted programs. -/
  sound_and_framed :
    ∀ p : L_src.Prog, ∀ h_acc : (tool p).defined,
      L_src.ProductiveOn pre p ∧
      FramedProductiveCompiles c p ((tool p).val h_acc)
  /-- Exact characterization of the tool's accepted domain (`AcceptedDom`),
      allowing syntactic type/borrow checkers (`AcceptedDom := WellTyped`)
      without locking out dead-branch ill-typed ASTs (`PENTEST-R3-2A`, `R4-3A/B`)
      or forcing acceptance of unverified `.buggySpike` (`PENTEST-R4-7`). -/
  accepted_iff_dom :
    ∀ p : L_src.Prog, (tool p).defined ↔ AcceptedDom p
  /-- Non-empty verified specification suite. -/
  specSuite_nonempty : specSuite ≠ []
  /-- Every `(pᵢ, postᵢ) ∈ specSuite` is in `AcceptedDom`, satisfies `VerifiedSpineOn`,
      and is `SpineNonDegenerate` against every `b ∈ badProgs`. -/
  suite_verified :
    AllHold (specSuite.map (fun sp =>
      AcceptedDom sp.1 ∧
      L_src.VerifiedSpineOn L_src.dom pre sp.2 sp.1 ∧
      AllHold (badProgs.map (L_src.SpineNonDegenerate pre sp.2 sp.1))))
  /-- Non-empty negative canary suite, all rejected by `tool`. -/
  badProgs_nonempty : badProgs ≠ []
  bad_rejected :
    AllHold (badProgs.map (fun b => ¬ (tool b).defined))

/-- **Nominal Wrapper Types for 2-Safety Non-Interference (`PENTEST-R4-5A/B` Fix):**
    Instead of inferring `Pub` vs. `Sec` or `Val` vs. `Leak` from unlabelled
    positional `Prod.fst` / `Prod.snd` (which failed on left-associated 3-tuples
    `((pub, sec₁), sec₂)` and `((ret, cycleCount), cacheTag)` in `PENTEST-R4-5A/B`),
    explicit nominal structures tag public vs. secret inputs and functional vs.
    leakage observations unambiguously! -/
structure PublicSecretQuery (Pub Sec : Type) where
  pub : Pub
  sec : Sec
  deriving DecidableEq

structure ValLeakObs (Val Leak : Type) where
  val  : Val
  leak : Leak
  deriving DecidableEq

/-- Nominal bidirectional 2-safety non-interference over `PublicSecretQuery` and
    `ValLeakObs`. -/
def NominalBiNonInterferingOn {Pub Sec Val Leak : Type}
    (L : Language (ValLeakObs Val Leak))
    (pre : L.Query → Prop)
    (qProj : L.Query → PublicSecretQuery Pub Sec)
    (prog : L.Prog) : Prop :=
  ∀ q₁ q₂ : L.Query,
    pre q₁ → pre q₂ → (qProj q₁).pub = (qProj q₂).pub →
    (∀ v₁ : ValLeakObs Val Leak, L.Produces prog q₁ v₁ →
      ∃ v₂ : ValLeakObs Val Leak, L.Produces prog q₂ v₂ ∧ v₁.leak = v₂.leak) ∧
    (∀ v₂ : ValLeakObs Val Leak, L.Produces prog q₂ v₂ →
      ∃ v₁ : ValLeakObs Val Leak, L.Produces prog q₁ v₁ ∧ v₁.leak = v₂.leak)

/-- **Extension 1 (`VerifiedConstantTimeCompiler extends VerifiedCompilerBase`):**
    Inherits every single field of `VerifiedCompilerBase` via `extends` (making
    clause drops impossible) and adds nominal 2-safety non-interference
    preservation + functionally-verified side-channel canary rejection! -/
structure VerifiedConstantTimeCompiler {Pub Sec Val Leak : Type}
    (L_src L_tgt : Language (ValLeakObs Val Leak))
    (Frame : Type)
    (c : FramedCodec L_src L_tgt Frame)
    (tool : Tool L_src L_tgt)
    (AcceptedDom : L_src.Prog → Prop)
    (pre : L_src.Query → Prop)
    (qProj_src : L_src.Query → PublicSecretQuery Pub Sec)
    (qProj_tgt : L_tgt.Query → PublicSecretQuery Pub Sec)
    (specSuite : List (L_src.Prog × (L_src.Query → ValLeakObs Val Leak → Prop)))
    (badProgs : List L_src.Prog)
    (badNIProgs : List L_src.Prog) : Prop extends
    VerifiedCompilerBase L_src L_tgt Frame c tool AcceptedDom pre specSuite badProgs where
  /-- Every specification in `specSuite` constrains only the functional value
      `v.val` (never rubber-stamping leakage `v.leak`, `PENTEST-R3-6A` / `R4-5B`). -/
  specs_leak_independent :
    AllHold (specSuite.map (fun sp =>
      ∀ q v₁ v₂, pre q → v₁.val = v₂.val → (sp.2 q v₁ ↔ sp.2 q v₂)))
  /-- Every accepted program is bi-non-interfering in `L_src` and compiles to a
      bi-non-interfering program in `L_tgt`. -/
  ni_preserved :
    ∀ p : L_src.Prog, ∀ h_acc : (tool p).defined,
      NominalBiNonInterferingOn L_src pre qProj_src p ∧
      NominalBiNonInterferingOn L_tgt (fun q₂ => pre (c.splitQuery q₂).1)
        qProj_tgt ((tool p).val h_acc)
  /-- Non-empty side-channel canary suite `badNIProgs` that are rejected by
      `tool` and violate `NominalBiNonInterferingOn`. -/
  badNIProgs_nonempty : badNIProgs ≠ []
  badNI_rejected :
    AllHold (badNIProgs.map (fun b =>
      ¬ (tool b).defined ∧ ¬ NominalBiNonInterferingOn L_src pre qProj_src b))

/-- **Extension 2 (`VerifiedArtifactPipeline extends VerifiedCompilerBase`):**
    Inherits `VerifiedCompilerBase` and composes `tool : Tool L_src L_tgt` with
    a total emitter `emit : L_tgt.Prog → L_isa.Prog` into an audited target ISA
    `L_isa : Language SemObs` via `FramedProductiveCompiles`—with **zero
    surjectivity lockout (`PENTEST-R4-8`)** and **zero ASCII prefix heuristics
    (`PENTEST-R4-2A/B`)**! -/
structure VerifiedArtifactPipeline {SemObs : Type}
    (L_src L_tgt L_isa : Language SemObs)
    (Frame_ir Frame_isa : Type)
    (c_ir : FramedCodec L_src L_tgt Frame_ir)
    (c_isa : FramedCodec L_tgt L_isa Frame_isa)
    (tool : Tool L_src L_tgt)
    (emit : L_tgt.Prog → L_isa.Prog)
    (AcceptedDom : L_src.Prog → Prop)
    (pre : L_src.Query → Prop)
    (specSuite : List (L_src.Prog × (L_src.Query → SemObs → Prop)))
    (badProgs : List L_src.Prog)
    (badIsaProgs : List L_isa.Prog) : Prop extends
    VerifiedCompilerBase L_src L_tgt Frame_ir c_ir tool AcceptedDom pre specSuite badProgs where
  /-- Every target IR program `t` productively compiles to `emit t` in `L_isa`
      preserving `Frame_isa`. -/
  emitter_framed_compiles :
    ∀ t : L_tgt.Prog, FramedProductiveCompiles c_isa t (emit t)
  /-- Non-empty negative ISA canary suite distinguishing valid emitted code from
      faulting/wrong ISA programs. -/
  badIsaProgs_nonempty : badIsaProgs ≠ []
  badIsa_distinct :
    AllHold (specSuite.map (fun sp =>
      ∀ h_acc : (tool sp.1).defined,
        AllHold (badIsaProgs.map (fun badIsa =>
          emit ((tool sp.1).val h_acc) ≠ badIsa))))

/-- End-to-End Theorem for `VerifiedArtifactPipeline`:
    Every accepted source program `p` compiles end-to-end (`L_src → L_tgt → L_isa`)
    via the composite framed codec `c_ir.comp c_isa` into the concrete ISA
    artifact `emit ((tool p).val h_acc)`! -/
theorem VerifiedArtifactPipeline.end_to_end_isa_framed_compiles {SemObs : Type}
    {L_src L_tgt L_isa : Language SemObs}
    {Frame_ir Frame_isa : Type}
    {c_ir : FramedCodec L_src L_tgt Frame_ir}
    {c_isa : FramedCodec L_tgt L_isa Frame_isa}
    {tool : Tool L_src L_tgt}
    {emit : L_tgt.Prog → L_isa.Prog}
    {AcceptedDom : L_src.Prog → Prop}
    {pre : L_src.Query → Prop}
    {specSuite : List (L_src.Prog × (L_src.Query → SemObs → Prop))}
    {badProgs : List L_src.Prog}
    {badIsaProgs : List L_isa.Prog}
    (h_pipe : VerifiedArtifactPipeline L_src L_tgt L_isa Frame_ir Frame_isa
      c_ir c_isa tool emit AcceptedDom pre specSuite badProgs badIsaProgs)
    (p : L_src.Prog) (h_acc : (tool p).defined) :
    FramedProductiveCompiles (c_ir.comp c_isa) p (emit ((tool p).val h_acc)) :=
  FramedProductiveCompiles.comp
    (h_pipe.toVerifiedCompilerBase.sound_and_framed p h_acc).2
    (h_pipe.emitter_framed_compiles ((tool p).val h_acc))

/-!
## Part V: Positive Non-Lockout & Negative Exploit-Rejection Proofs on `NextGen`
-/

/-- **Positive Non-Lockout 1 (`PENTEST-R2-7` & `R3-1A/B` Resolved):**
    `FramedCodec` cleanly admits a target x86 language `L_x86_rbx_rcx` whose
    state has BOTH a callee-saved register `rbx` (`Frame := Nat`, preserved as
    `rbx_out = rbx_in`) AND a caller-saved scratch register `rcx` (written with
    different scratch values `0` vs `99` by different target instructions),
    while **unconditionally rejecting** `clobberRbxTargetProg` (`rbx := 57005`)! -/
inductive X86ScratchProg where
  | addOneScratch0
  | addOneScratch99
  | clobberRbx57005
  deriving DecidableEq

/-- Target x86 language with `Query = Nat × Nat` (`(rdi, rbx_in)`) and
    `Out = Nat × (Nat × Nat)` (`(rax, (rbx_out, rcx_scratch))`). -/
abbrev L_x86_rbx_rcx : Language Nat where
  Prog  := X86ScratchProg
  Query := Nat × Nat
  Out   := Nat × (Nat × Nat)
  obs o := o.1
  sem p q := match p with
    | .addOneScratch0  => Partial.pure (fun o => o = (q.1 + 1, (q.2, 0)))
    | .addOneScratch99 => Partial.pure (fun o => o = (q.1 + 1, (q.2, 99)))
    | .clobberRbx57005 => Partial.pure (fun o => o = (q.1 + 1, (57005, 0)))

/-- Framed codec for `L_simple_ir → L_x86_rbx_rcx` with callee-saved `Frame = Nat`
    (`rbx`) and quotiented caller-saved `rcx`. -/
def c_framed_x86_rbx_rcx : FramedCodec L_simple_ir L_x86_rbx_rcx Nat where
  splitQuery q   := (q.1, q.2)
  joinQuery q f  := (q, f)
  defaultFrame   := 0
  encodeOut o f  := (o, (f, 0))
  decodeOut o    := some (o.1, o.2.1)
  split_join_query _ _    := rfl
  join_split_query _      := rfl
  decodeOut_encodeOut _ _ := rfl
  obs_decodeOut _ _ _ h   := congrArg Prod.fst (Option.some.inj h)

/-- **Theorem 3A (Caller-Saved Scratch Admitted & Callee-Saved Clobber Rejected):**
    Under `c_framed_x86_rbx_rcx`:
    1. Both `.addOneScratch0` (`rcx = 0`) and `.addOneScratch99` (`rcx = 99`)
       satisfy `FramedProductiveCompiles` from `.addOne`!
    2. `.clobberRbx57005` (`rbx := 57005`, `PENTEST-8B` / `R3-1C` / `R4-4A`)
       is **unconditionally rejected** (`¬ FramedProductiveCompiles`)! -/
theorem nextgen_admits_multi_scratch_and_rejects_callee_saved_clobber :
    FramedProductiveCompiles c_framed_x86_rbx_rcx .addOne .addOneScratch0 ∧
    FramedProductiveCompiles c_framed_x86_rbx_rcx .addOne .addOneScratch99 ∧
    ¬ FramedProductiveCompiles c_framed_x86_rbx_rcx .addOne .clobberRbx57005 := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro q _
      refine ⟨trivial, fun o ho => ⟨q.1 + 1, ?_, rfl⟩⟩
      rw [ho]; rfl
    · intro q _
      exact ⟨trivial, (q.1 + 1, (q.2, 0)), rfl⟩
  · constructor
    · intro q _
      refine ⟨trivial, fun o ho => ⟨q.1 + 1, ?_, rfl⟩⟩
      rw [ho]; rfl
    · intro q _
      exact ⟨trivial, (q.1 + 1, (q.2, 99)), rfl⟩
  · intro ⟨h_comp, _⟩
    have ⟨_, hval⟩ := h_comp (0, 0) trivial
    have ⟨o₁, hdec, _⟩ := hval (1, (57005, 0)) rfl
    dsimp [c_framed_x86_rbx_rcx] at hdec
    have h_pair := Option.some.inj hdec
    have h_rbx : (57005 : Nat) = 0 := congrArg Prod.snd h_pair
    cases h_rbx

/-- **Positive Non-Lockout 2 & Negative Rejection 2 (`PENTEST-R4-3A/B` & `R4-7` Resolved):**
    On a 5-program crate `L_spike_typed` containing `.wellTypedAddOne` (`q + 1`),
    `.wellTypedAddTwo` (`q + 2`), `.deadBranchIllTyped` (`if false { *null } else { q + 1 }`),
    `.buggySpike` (`if q = 0 then 1 else 0`), and `.liveNullDeref` (`UB`):
    1. The honest verifier `honestTypedSpikeCompiler` (which accepts only the
       well-typed verified domain `AcceptedDom p := (p = .wellTypedAddOne ∨ p = .wellTypedAddTwo)`
       and rejects `.deadBranchIllTyped`, `.buggySpike`, and `.liveNullDeref`)
       **satisfies `VerifiedCompilerBase`**!
    2. The buggy verifier `acceptBuggySpikeTool` (which accepts `.buggySpike`
       outside `AcceptedDom`) is **unconditionally rejected**! -/
inductive SpikeTypedProg where
  | wellTypedAddOne
  | wellTypedAddTwo
  | deadBranchIllTyped
  | buggySpike
  | liveNullDeref
  deriving DecidableEq

abbrev L_spike_typed : Language Nat :=
  Language.mkSimple SpikeTypedProg Nat Nat (fun p q => match p with
    | .wellTypedAddOne    => Partial.pure (fun o => o = q + 1)
    | .wellTypedAddTwo    => Partial.pure (fun o => o = q + 2)
    | .deadBranchIllTyped => Partial.pure (fun o => o = q + 1)
    | .buggySpike         => Partial.pure (fun o => o = if q = 0 then 1 else 0)
    | .liveNullDeref      => Partial.ub)

def WellTypedVerifiedDom : SpikeTypedProg → Prop
  | .wellTypedAddOne => True
  | .wellTypedAddTwo => True
  | _                => False

def honestTypedSpikeCompiler : Tool L_spike_typed L_spike_typed
  | .wellTypedAddOne => Partial.pure .wellTypedAddOne
  | .wellTypedAddTwo => Partial.pure .wellTypedAddTwo
  | _                => Partial.ub

def acceptBuggySpikeTool : Tool L_spike_typed L_spike_typed
  | .wellTypedAddOne => Partial.pure .wellTypedAddOne
  | .wellTypedAddTwo => Partial.pure .wellTypedAddTwo
  | .buggySpike      => Partial.pure .buggySpike
  | _                => Partial.ub

theorem nextgen_admits_syntactic_typechecker_and_rejects_buggySpike :
    VerifiedCompilerBase L_spike_typed L_spike_typed Unit
      (FramedCodec.id L_spike_typed) honestTypedSpikeCompiler
      WellTypedVerifiedDom (fun q => q < 100)
      [(.wellTypedAddOne, fun q v => v = q + 1),
       (.wellTypedAddTwo, fun q v => v = q + 2)]
      [.buggySpike, .liveNullDeref] ∧
    ¬ VerifiedCompilerBase L_spike_typed L_spike_typed Unit
      (FramedCodec.id L_spike_typed) acceptBuggySpikeTool
      WellTypedVerifiedDom (fun q => q < 100)
      [(.wellTypedAddOne, fun q v => v = q + 1),
       (.wellTypedAddTwo, fun q v => v = q + 2)]
      [.buggySpike, .liveNullDeref] := by
  refine ⟨?_, ?_⟩
  · refine {
      pre_inhabited := ⟨0, by decide⟩
      sound_and_framed := fun p => match p with
        | .wellTypedAddOne => fun _ =>
          ⟨fun q _ => ⟨trivial, q + 1, rfl⟩,
           FramedProductiveCompiles.refl L_spike_typed .wellTypedAddOne⟩
        | .wellTypedAddTwo => fun _ =>
          ⟨fun q _ => ⟨trivial, q + 2, rfl⟩,
           FramedProductiveCompiles.refl L_spike_typed .wellTypedAddTwo⟩
        | .deadBranchIllTyped => fun h => False.elim h
        | .buggySpike         => fun h => False.elim h
        | .liveNullDeref      => fun h => False.elim h
      accepted_iff_dom := fun p => by cases p <;> exact Iff.rfl
      specSuite_nonempty := by decide
      suite_verified :=
        ⟨⟨trivial,
          ⟨Or.inl ⟨0, by decide⟩,
           fun q _ => ⟨trivial, q + 1, rfl⟩,
           fun _ _ => ⟨trivial, fun _ ho => ho⟩⟩,
          ⟨Or.inl ⟨1, by decide, 0, ⟨trivial, 0, rfl, rfl⟩, by decide⟩,
           Or.inr ⟨⟨0, by decide, fun h => h⟩,
             .wellTypedAddTwo, 0, 1, 2, by decide,
             ⟨trivial, 1, rfl, rfl⟩, ⟨trivial, 2, rfl, rfl⟩, by decide⟩,
           trivial⟩⟩,
         ⟨trivial,
          ⟨Or.inl ⟨0, by decide⟩,
           fun q _ => ⟨trivial, q + 2, rfl⟩,
           fun _ _ => ⟨trivial, fun _ ho => ho⟩⟩,
          ⟨Or.inl ⟨0, by decide, 1, ⟨trivial, 1, rfl, rfl⟩, by decide⟩,
           Or.inr ⟨⟨0, by decide, fun h => h⟩,
             .wellTypedAddOne, 0, 2, 1, by decide,
             ⟨trivial, 2, rfl, rfl⟩, ⟨trivial, 1, rfl, rfl⟩, by decide⟩,
           trivial⟩⟩,
         trivial⟩
      badProgs_nonempty := by decide
      bad_rejected := ⟨fun h => h, fun h => h, trivial⟩
    }
  · intro h_buggy
    exact (h_buggy.accepted_iff_dom .buggySpike).mp trivial

/-- **Positive Non-Lockout 3 (`PENTEST-R4-2A` & `PENTEST-R4-8` Resolved):**
    `VerifiedArtifactPipeline` certifies the single-program compiler on `L_simple_ir`
    emitting the accumulator-initializing multi-instruction sequence
    `[.zeroClear, .loadAndInc]` (`"xor eax, eax\nmov eax, edi\ninc eax\nret"`)
    into the multi-instruction sequential ISA `L_seq_asm` (which contains
    infinitely many distinct query-sensitive programs `[.loadAndInc]`,
    `[.loadAndInc, .addImm 1]`, etc.!), with **zero surjectivity lockout** and
    **zero prefix-heuristic lockout**! -/
def compileSimpleIR : Tool L_simple_ir L_simple_ir
  | .addOne  => Partial.pure .addOne
  | .badZero => Partial.ub

def emitSeqAsm : SimpleIR → List AsmInstr
  | .addOne  => [.zeroClear, .loadAndInc]
  | .badZero => [.zeroClear]

def c_framed_ir_to_seq_asm : FramedCodec L_simple_ir L_seq_asm Unit where
  splitQuery q        := (q, ())
  joinQuery q _       := q
  defaultFrame        := ()
  encodeOut o _       := o
  decodeOut o         := some (o, ())
  split_join_query _ _    := rfl
  join_split_query _      := rfl
  decodeOut_encodeOut _ _ := rfl
  obs_decodeOut _ _ _ h   := congrArg Prod.fst (Option.some.inj h)

theorem nextgen_verifiedArtifactPipeline_admits_accum_init_and_multi_isa :
    VerifiedArtifactPipeline L_simple_ir L_simple_ir L_seq_asm Unit Unit
      (FramedCodec.id L_simple_ir) c_framed_ir_to_seq_asm
      compileSimpleIR emitSeqAsm
      (fun p => p = .addOne) (fun q => q < 100)
      [(.addOne, fun q v => v = q + 1)]
      [.badZero]
      [[.zeroClear], [.trap]] := by
  refine {
    pre_inhabited := ⟨0, by decide⟩
    sound_and_framed := fun p => match p with
      | .addOne => fun _ =>
        ⟨fun q _ => ⟨trivial, q + 1, rfl⟩,
         FramedProductiveCompiles.refl L_simple_ir .addOne⟩
      | .badZero => fun h => False.elim h
    accepted_iff_dom := fun p => by
      cases p with
      | addOne  => exact ⟨fun _ => rfl, fun _ => trivial⟩
      | badZero => exact ⟨fun h => False.elim h, fun h => by cases h⟩
    specSuite_nonempty := by decide
    suite_verified :=
      ⟨⟨rfl,
        ⟨Or.inl ⟨0, by decide⟩,
         fun q _ => ⟨trivial, q + 1, rfl⟩,
         fun _ _ => ⟨trivial, fun _ ho => ho⟩⟩,
        ⟨Or.inl ⟨0, by decide, 0, ⟨trivial, 0, rfl, rfl⟩, by decide⟩,
         trivial⟩⟩,
       trivial⟩
    badProgs_nonempty := by decide
    bad_rejected := ⟨fun h => h, trivial⟩
    emitter_framed_compiles := fun t => by
      cases t with
      | addOne =>
        exact ⟨fun q _ => ⟨trivial, fun o ho => ⟨o, rfl, ho⟩⟩,
               fun q _ => ⟨trivial, q + 1, rfl⟩⟩
      | badZero =>
        exact ⟨fun q _ => ⟨trivial, fun o ho => ⟨o, rfl, ho⟩⟩,
               fun q _ => ⟨trivial, 0, rfl⟩⟩
    badIsaProgs_nonempty := by decide
    badIsa_distinct := by
      refine ⟨fun h => ?_, trivial⟩
      dsimp [compileSimpleIR, Partial.pure, emitSeqAsm]
      exact ⟨by decide, by decide, trivial⟩
  }

/-- **Positive Non-Lockout 4 & Negative Rejection 4 (`PENTEST-R4-5A/B` Resolved):**
    Using `PublicSecretQuery` and `ValLeakObs` on a 2-secret, 2-channel language
    (`Pub := Nat`, `Sec := Nat × Nat` for `(sec₁, sec₂)`, `Val := Nat`,
    `Leak := Nat × Nat` for `(cycleCount, cacheTag)`):
    1. The constant-time cipher `.honestCtCipher` (which outputs `pub + 1` in
       `10` cycles with cache tag `0`) satisfies `NominalBiNonInterferingOn`.
    2. Both `.leakFirstSecretInVal` (`val := pub + sec₁`, `PENTEST-R4-5A`) and
       `.leakSecretInCycleCount` (`leak := (sec₁, 0)`, `PENTEST-R4-5B`) are
       **unconditionally refuted**! -/
inductive TwoSecretTwoChannelProg where
  | honestCtCipher
  | leakFirstSecretInVal
  | leakSecretInCycleCount
  deriving DecidableEq

abbrev L_nominal_ct : Language (ValLeakObs Nat (Nat × Nat)) :=
  Language.mkSimple TwoSecretTwoChannelProg
    (PublicSecretQuery Nat (Nat × Nat))
    (ValLeakObs Nat (Nat × Nat))
    (fun p q => match p with
      | .honestCtCipher =>
        Partial.pure (fun o => o = { val := q.pub + 1, leak := (10, 0) })
      | .leakFirstSecretInVal =>
        Partial.pure (fun o => o = { val := q.pub + q.sec.1, leak := (q.sec.1, 0) })
      | .leakSecretInCycleCount =>
        Partial.pure (fun o => o = { val := q.pub + 1, leak := (q.sec.1, 0) }))

theorem nextgen_nominal_ct_blocks_left_associated_tuple_leaks :
    NominalBiNonInterferingOn L_nominal_ct (fun q => q.pub < 100) id .honestCtCipher ∧
    ¬ NominalBiNonInterferingOn L_nominal_ct (fun q => q.pub < 100) id .leakFirstSecretInVal ∧
    ¬ NominalBiNonInterferingOn L_nominal_ct (fun q => q.pub < 100) id .leakSecretInCycleCount := by
  refine ⟨?_, ?_, ?_⟩
  · intro q₁ q₂ _ _ _
    constructor
    · rintro v₁ ⟨_, o₁, ho₁, hv₁⟩
      have hv₁_eq : v₁ = { val := q₁.pub + 1, leak := (10, 0) } := Eq.trans hv₁.symm ho₁
      refine ⟨{ val := q₂.pub + 1, leak := (10, 0) }, ⟨trivial, _, rfl, rfl⟩, ?_⟩
      rw [hv₁_eq]
    · rintro v₂ ⟨_, o₂, ho₂, hv₂⟩
      have hv₂_eq : v₂ = { val := q₂.pub + 1, leak := (10, 0) } := Eq.trans hv₂.symm ho₂
      refine ⟨{ val := q₁.pub + 1, leak := (10, 0) }, ⟨trivial, _, rfl, rfl⟩, ?_⟩
      rw [hv₂_eq]
  · intro h_ni
    have h_sim := (h_ni { pub := 0, sec := (0, 0) } { pub := 0, sec := (1, 0) }
      (by decide) (by decide) rfl).1
    have ⟨v₂, ⟨_, o₂, ho₂, hv₂⟩, h_leak⟩ :=
      h_sim { val := 0, leak := (0, 0) } ⟨trivial, _, rfl, rfl⟩
    have hv₂_eq : v₂ = { val := 1, leak := (1, 0) } := Eq.trans hv₂.symm ho₂
    rw [hv₂_eq] at h_leak
    cases h_leak
  · intro h_ni
    have h_sim := (h_ni { pub := 0, sec := (0, 0) } { pub := 0, sec := (1, 0) }
      (by decide) (by decide) rfl).1
    have ⟨v₂, ⟨_, o₂, ho₂, hv₂⟩, h_leak⟩ :=
      h_sim { val := 1, leak := (0, 0) } ⟨trivial, _, rfl, rfl⟩
    have hv₂_eq : v₂ = { val := 1, leak := (1, 0) } := Eq.trans hv₂.symm ho₂
    rw [hv₂_eq] at h_leak
    cases h_leak

end NextGen

/-!
## Kernel Axiom Audit (`#print axioms`)
-/

#print axioms PutnamSyntaxPermutationTheorem
#print axioms pentest_r3_4_corollary_trojan_emitter_passes_under_permuted_semantics
#print axioms pentest_r2_1_circular_diskLang_universal_tautology
#print axioms LexicalHeuristicDualFailureTheorem
#print axioms prefix_classifier_universal_impossibility
#print axioms EmitterSurjectivityImpossibility
#print axioms NextGen.VerifiedArtifactPipeline.end_to_end_isa_framed_compiles
#print axioms NextGen.nextgen_admits_multi_scratch_and_rejects_callee_saved_clobber
#print axioms NextGen.nextgen_admits_syntactic_typechecker_and_rejects_buggySpike
#print axioms NextGen.nextgen_verifiedArtifactPipeline_admits_accum_init_and_multi_isa
#print axioms NextGen.nextgen_nominal_ct_blocks_left_associated_tuple_leaks

end PutnamAndTcbBoundary
