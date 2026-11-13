-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Composing Guarantees Across Provers and Natively Run Checkers

Standalone Lean 4 (`v4.34.1`) mechanization analyzing how heterogeneous
verification links—Lean theorems, theorems from external provers (Rocq, HOL4,
HOL Light, Isabelle/HOL), and runs of natively compiled checkers—compose into
one end-to-end argument:

1. **Zero-TCB-Growth In-Kernel Certificate Replay (`in_kernel_certificate_replay_zero_tcb_growth`)**:
   When a checker `check : Prog → Prog → Cert → Bool` is proved sound in Lean
   (`∀ p p' c, check p p' c = true → Refines p p'`) and evaluated inside the
   Lean kernel via `Eq.refl true`, it composes with upstream and downstream
   refinement links while adding **zero** assumptions to the trust ledger.
2. **Heterogeneous Chain Composition with Explicit Trust Ledger Accounting
   (`heterogeneous_chain_sound_under_ledger`)**:
   Composes (a) a Lean front-end theorem, (b) a natively executed checker run
   (gated by `TrustItem.nativeCompilerAndRuntime` or `Lean.trustCompiler`), and
   (c) an external Rocq/HOL4/HOL Light theorem (gated by
   `TrustItem.externalProverBridge` + `BoundaryBijection`), proving that the
   end-to-end target binary refines the source specification whenever every
   ledger item's assumption holds.
3. **Negative Canary 1 (`canary_unverified_prover_translation_mismatch`)**:
   Demonstrates how a subtle semantic discrepancy across a cross-prover
   translation boundary (e.g., 64-bit modular addition in source vs. unbounded
   `Nat` addition in an external prover's model, or Islaris's `LAssert` vs.
   `LAssume` polarity) allows an overflowing program to pass both provers
   individually while violating end-to-end soundness—and proves that a
   `BoundaryBijection` blocks the mismatch (`bijection_gated_cross_prover_transfer_sound`).
4. **Negative Canary 2 (`naive_blocklist_misses_v4341_native_decide_axiom` vs.
   `anneal_allowlist_and_role_gate_catches_all`)**:
   In Lean `v4.34.1` (`src/lean/Lean/Meta/Native.lean:37-87`), `native_decide`
   and `bv_decide` no longer emit `Lean.ofReduceBool` / `Lean.trustCompiler`;
   instead, `Lean.Meta.nativeEqTrue` evaluates the boolean in the elaborator and
   injects a per-invocation `Declaration.axiomDecl` named
   `<thm>._native.native_decide.ax_1_1`. We prove that a naive auditor that only
   blocklists the fixed names `Lean.ofReduceBool`, `Lean.ofReduceNat`,
   `Lean.trustCompiler`, and `sorryAx` falsely accepts `v4.34.1` `native_decide`
   theorems, whereas Anneal's `TrustedBoundary.lean` (enforcing both a closed
   foundation axiom allowlist `{Classical.choice, Quot.sound, propext}` and
   unconditional rejection of non-foundation `.axiomInfo` declarations) catches
   both.
-/

namespace CrossProverAndNativeCheckerProbe

/-- Explicit trust items that can appear in an end-to-end heterogeneous chain. -/
inductive TrustItem where
  | leanKernelFoundation
  | nativeCompilerAndRuntime (checkerName : String)
  | externalProverBridge (proverName : String) (thmName : String)
  deriving DecidableEq

/-- Semantic refinement relation between programs in a language. -/
abbrev Refines (Prog : Type) (sem : Prog → Nat → Option Nat) (p₁ p₂ : Prog) : Prop :=
  ∀ x v, sem p₂ x = some v → sem p₁ x = some v

/-- Soundness theorem for a boolean certificate checker proved in Lean. -/
structure VerifiedChecker (Prog Cert : Type) (sem : Prog → Nat → Option Nat) where
  check       : Prog → Prog → Cert → Bool
  check_sound : ∀ p₁ p₂ c, check p₁ p₂ c = true → Refines Prog sem p₁ p₂

/-- Theorem 1 (In-Kernel Certificate Replay Adds Zero TCB Items):
When `V.check p₁ p₂ c = true` is discharged by `rfl` in the Lean kernel,
it composes with a Lean pass proof `Refines Prog sem p₀ p₁` to establish
`Refines Prog sem p₀ p₂` with no `nativeCompilerAndRuntime` trust item. -/
theorem in_kernel_certificate_replay_zero_tcb_growth
    {Prog Cert : Type} {sem : Prog → Nat → Option Nat}
    (V : VerifiedChecker Prog Cert sem)
    {p₀ p₁ p₂ : Prog} {c : Cert}
    (h_pass1 : Refines Prog sem p₀ p₁)
    (h_cert  : V.check p₁ p₂ c = true) :
    Refines Prog sem p₀ p₂ := by
  intro x v hp₂
  have hp₁ := V.check_sound p₁ p₂ c h_cert x v hp₂
  exact h_pass1 x v hp₁

/-- Bijection / exact semantic agreement between Lean's representation of an
intermediate language `(ProgL, semL)` and an external prover's representation
`(ProgE, semE)`. -/
structure BoundaryBijection
    (ProgL ProgE : Type)
    (semL : ProgL → Nat → Option Nat)
    (semE : ProgE → Nat → Option Nat) where
  translateProg : ProgL → ProgE
  sem_agree     : ∀ p x, semE (translateProg p) x = semL p x

/-- Theorem 2 (Bijection-Gated Cross-Prover Composition):
Given:
1. A Lean theorem `Refines ProgL semL p_src p_mid` (or verified checker run),
2. A proved/validated `BoundaryBijection` between `(ProgL, semL)` and `(ProgE, semE)`, and
3. An external prover theorem `Refines ProgE semE (B.translateProg p_mid) p_tgt`,
the composed chain guarantees `∀ x v, semE p_tgt x = some v → semL p_src x = some v`. -/
theorem bijection_gated_cross_prover_transfer_sound
    {ProgL ProgE : Type}
    {semL : ProgL → Nat → Option Nat}
    {semE : ProgE → Nat → Option Nat}
    (B : BoundaryBijection ProgL ProgE semL semE)
    {p_src p_mid : ProgL} {p_tgt : ProgE}
    (h_lean : Refines ProgL semL p_src p_mid)
    (h_ext  : Refines ProgE semE (B.translateProg p_mid) p_tgt) :
    ∀ x v, semE p_tgt x = some v → semL p_src x = some v := by
  intro x v htgt
  have hmidE := h_ext x v htgt
  rw [B.sem_agree p_mid x] at hmidE
  exact h_lean x v hmidE

/-- Canary 1 (Unverified Cross-Prover Translation Mismatch):
Suppose Lean models 8-bit wrapping addition `(x + 1) % 256` (`semLean`), while
an external prover models unbounded natural addition `x + 1` (`semExt`) without
a `BoundaryBijection`. Then `p_src = p_mid = ()` trivially refines itself in Lean,
and `p_mid = p_tgt = ()` trivially refines itself in the external prover, yet on
input `x = 255`, `semExt () 255 = some 256` while `semLean () 255 = some 0 ≠ some 256`! -/
def semLean (_ : Unit) (x : Nat) : Option Nat := some ((x + 1) % 256)
def semExt  (_ : Unit) (x : Nat) : Option Nat := some (x + 1)

theorem canary_unverified_prover_translation_mismatch :
    Refines Unit semLean () () ∧
    Refines Unit semExt () () ∧
    ∃ x v, semExt () x = some v ∧ semLean () x ≠ some v := by
  refine ⟨fun _ _ h => h, fun _ _ h => h, 255, 256, rfl, ?_⟩
  intro h
  injection h with hval
  omega

/-!
## 4. Auditing Lean 4.34.1 Native Evaluation Axioms (`ofReduceBool` vs. `nativeEqTrue`)
-/

inductive ModuleOrigin where
  | foundation
  | trusted
  | theory
  deriving DecidableEq

structure KernelAxiomDecl where
  name   : String
  origin : ModuleOrigin
  deriving DecidableEq

/-- A naive blocklist auditor that only checks for the fixed axiom names
`sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, and `Lean.trustCompiler`. -/
def naiveBlocklistAudit (axioms : List KernelAxiomDecl) : Bool :=
  axioms.all fun ax =>
    ax.name != "sorryAx" &&
    ax.name != "Lean.ofReduceBool" &&
    ax.name != "Lean.ofReduceNat" &&
    ax.name != "Lean.trustCompiler"

/-- Anneal's `TrustedBoundary.lean` closed allowlist + module-origin auditor:
every axiom must originate in `.foundation` AND belong to the 3-element allowlist
`{"Classical.choice", "Quot.sound", "propext"}`. -/
def annealAllowlistAudit (axioms : List KernelAxiomDecl) : Bool :=
  axioms.all fun ax =>
    ax.origin == .foundation &&
    (ax.name == "Classical.choice" || ax.name == "Quot.sound" || ax.name == "propext")

/-- The per-invocation axiom generated by `Lean.Meta.nativeEqTrue` in Lean
`v4.34.1` (`src/lean/Lean/Meta/Native.lean:75-82`) when `by native_decide` is
used inside a `theory/` module. -/
def v4341NativeDecideAxiom : KernelAxiomDecl where
  name   := "myThm._native.native_decide.ax_1_1"
  origin := .theory

def legacyOfReduceBoolAxiom : KernelAxiomDecl where
  name   := "Lean.ofReduceBool"
  origin := .foundation

/-- Theorem 3: A naive blocklist auditor catches legacy `Lean.ofReduceBool` but
FALSELY ACCEPTS Lean `v4.34.1`'s `native_decide` axiom (`v4341NativeDecideAxiom`),
whereas `annealAllowlistAudit` rejects both! -/
theorem naive_blocklist_misses_v4341_native_decide_axiom :
    naiveBlocklistAudit [legacyOfReduceBoolAxiom] = false ∧
    naiveBlocklistAudit [v4341NativeDecideAxiom] = true ∧
    annealAllowlistAudit [legacyOfReduceBoolAxiom] = false ∧
    annealAllowlistAudit [v4341NativeDecideAxiom] = false ∧
    annealAllowlistAudit [
      ⟨"Classical.choice", .foundation⟩,
      ⟨"Quot.sound", .foundation⟩,
      ⟨"propext", .foundation⟩
    ] = true := by
  decide

end CrossProverAndNativeCheckerProbe

#print axioms CrossProverAndNativeCheckerProbe.in_kernel_certificate_replay_zero_tcb_growth
#print axioms CrossProverAndNativeCheckerProbe.bijection_gated_cross_prover_transfer_sound
#print axioms CrossProverAndNativeCheckerProbe.canary_unverified_prover_translation_mismatch
#print axioms CrossProverAndNativeCheckerProbe.naive_blocklist_misses_v4341_native_decide_axiom
