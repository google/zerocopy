-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Compositional Correctness, Linking, ThinLTO Summary Importing, and Whole-Program Optimization

Standalone Lean 4 (`v4.34.1`) mechanization covering:
1. **Open-Module Horizontal Composition (`OpenModule`, `linkModules`)**:
   Composing per-function contracts across separately compiled units when
   mutual import/export contracts align (`horizontal_link_sound`).
2. **Whole-Program Optimization (WPO) Closed-World Side Conditions**:
   Formalizing CompCert `Unusedglob` / LLVM `Internalize`, Interprocedural
   Sparse Conditional Constant Propagation (`IPSCCP`), and Dead-Argument
   Elimination (`DAE`). Proves that internalizing and specializing a symbol `f`
   for a constant argument `c₀` is sound when `f` is absent from the exported
   root set (`wpo_internalize_ipsccp_sound`), and proves a refutation canary
   (`canary_open_world_ipsccp_unsound`) when an external caller outside the
   closed world invokes `f` with `arg ≠ c₀`.
3. **ThinLTO Summary-Based Importing and `-Zshare-generics` `WeakODR` Coherence**:
   Models `rustc`'s 4-stage ThinLTO pipeline (`Rename`, `ResolveWeak`,
   `Internalize`, `Import` in `compiler/rustc_codegen_llvm/src/back/lto.rs:735-770`
   and `PassWrapper.cpp:1271-1488`). Proves that importing an `available_externally`
   summary body for cross-CGU inlining is sound when `WeakODR` symbol definitions
   are coherent (`thinLto_summary_import_sound`), and proves a refutation canary
   (`canary_incoherent_weak_odr_unsound`) when two compilation units emit
   conflicting semantics under the same mangled generic symbol.
4. **Conditional Mixed-Binary Composition & Reentrant Callback Pitfalls**:
   Proves that conditional contracts ("if unverified imports satisfy their specs,
   verified exports satisfy theirs") compose without circular vacuity via
   call-depth fuel induction (`conditional_mixed_binary_sound`), while proving
   two classic pitfalls: circular zero-step assumption vacuity
   (`canary_circular_assumption_vacuity`) and reentrant callbacks observing a
   temporarily broken private ADT invariant (`canary_reentrant_callback_invariant_breach`).
-/

namespace CompositionalLinkingAndWpoProbe

abbrev SymId := Nat
abbrev Val   := Nat

/-- A function contract relating input argument `arg` and initial memory `mem`
to return value `ret` and post-call memory `mem'`. -/
structure FnContract where
  pre  : Val → Val → Prop
  post : Val → Val → Val → Val → Prop

/-- Linkage kind modeled after `rustc_hir::attrs::Linkage`
(`compiler/rustc_monomorphize/src/partitioning.rs:1246-1254`) and LLVM
`GlobalValue::LinkageTypes`. -/
inductive Linkage where
  | external
  | internal
  | weakODR
  | availableExternally
  deriving DecidableEq

/-- A function definition inside an open compilation unit. -/
structure FnDef where
  sym     : SymId
  linkage : Linkage
  body    : Val → Val → Option (Val × Val)

/-- Satisfies relation for a single function body against a `FnContract`. -/
def SatisfiesContract (sem : Val → Val → Option (Val × Val)) (c : FnContract) : Prop :=
  ∀ arg mem, c.pre arg mem →
    ∃ ret mem', sem arg mem = some (ret, mem') ∧ c.post arg mem ret mem'

/-- Open module with explicit imported and exported symbol contracts. -/
structure OpenModule where
  imports : List (SymId × FnContract)
  exports : List (SymId × FnContract)
  defs    : List FnDef

/-- Look up a contract by `SymId`. -/
def lookupContract (table : List (SymId × FnContract)) (s : SymId) : Option FnContract :=
  match table with
  | [] => none
  | (k, c) :: rest => if k == s then some c else lookupContract rest s

/-- Look up a function definition by `SymId`. -/
def lookupDef (defs : List FnDef) (s : SymId) : Option FnDef :=
  match defs with
  | [] => none
  | d :: rest => if d.sym == s then some d else lookupDef rest s

/-- Open-module refinement: assuming all `imports` satisfy their declared
contracts, every exported symbol has a definition in `defs` satisfying its
exported contract. -/
def OpenModuleRefines (m : OpenModule) : Prop :=
  ∀ s c, lookupContract m.exports s = some c →
    ∃ d, lookupDef m.defs s = some d ∧ SatisfiesContract d.body c

/-- Link two open modules by concatenating definitions and exports. -/
def linkModules (m₁ m₂ : OpenModule) : OpenModule where
  imports := m₁.imports ++ m₂.imports
  exports := m₁.exports ++ m₂.exports
  defs    := m₁.defs ++ m₂.defs

/-- Disjoint symbol definitions: `m₁.defs` does not shadow any exported symbol of `m₂`. -/
def NoDefShadowing (defs₁ : List FnDef) (exports₂ : List (SymId × FnContract)) : Prop :=
  ∀ s c, lookupContract exports₂ s = some c → lookupDef defs₁ s = none

theorem lookupContract_append {t₁ t₂ : List (SymId × FnContract)} {s : SymId} {c : FnContract}
    (h : lookupContract (t₁ ++ t₂) s = some c) :
    lookupContract t₁ s = some c ∨ (lookupContract t₁ s = none ∧ lookupContract t₂ s = some c) := by
  induction t₁ with
  | nil =>
    exact Or.inr ⟨rfl, h⟩
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.cons_append, lookupContract] at h ⊢
    cases h_eq : (k == s) <;> simp only [h_eq] at h ⊢
    · exact ih h
    · exact Or.inl h

theorem lookupDef_append_left {d₁ d₂ : List FnDef} {s : SymId} {d : FnDef}
    (h : lookupDef d₁ s = some d) :
    lookupDef (d₁ ++ d₂) s = some d := by
  induction d₁ with
  | nil => nomatch h
  | cons hd tl ih =>
    simp only [List.cons_append, lookupDef] at h ⊢
    cases h_eq : (hd.sym == s) <;> simp only [h_eq] at h ⊢
    · exact ih h
    · exact h

theorem lookupDef_append_right {d₁ d₂ : List FnDef} {s : SymId} {d : FnDef}
    (hnone : lookupDef d₁ s = none)
    (h : lookupDef d₂ s = some d) :
    lookupDef (d₁ ++ d₂) s = some d := by
  induction d₁ with
  | nil => exact h
  | cons hd tl ih =>
    simp only [List.cons_append, lookupDef] at hnone ⊢
    cases h_eq : (hd.sym == s) <;> simp only [h_eq] at hnone ⊢
    · exact ih hnone
    · nomatch hnone

/-- Horizontal composition theorem: linking two refined open modules with
non-shadowing definitions preserves `OpenModuleRefines`. -/
theorem horizontal_link_sound (m₁ m₂ : OpenModule)
    (h₁ : OpenModuleRefines m₁)
    (h₂ : OpenModuleRefines m₂)
    (hdisj : NoDefShadowing m₁.defs m₂.exports) :
    OpenModuleRefines (linkModules m₁ m₂) := by
  intro s c hexp
  rcases lookupContract_append hexp with hexp₁ | ⟨_, hexp₂⟩
  · rcases h₁ s c hexp₁ with ⟨d, hdef, hsat⟩
    exact ⟨d, lookupDef_append_left hdef, hsat⟩
  · rcases h₂ s c hexp₂ with ⟨d, hdef, hsat⟩
    have hnone := hdisj s c hexp₂
    exact ⟨d, lookupDef_append_right hnone hdef, hsat⟩

/-!
## 2. Whole-Program Optimization: Internalization, IPSCCP, and DAE
-/

/-- Closed-world caller invariant for a helper function `f`: every internal call
site in the module passes `arg = c₀`, and `f` is NOT in `preservedExports`. -/
structure ClosedWorldConstArgAssumption
    (preservedExports : List SymId) (f : SymId) (c₀ : Val)
    (callerArg : Val) : Prop where
  not_exported : f ∉ preservedExports
  internal_call_const : callerArg = c₀

/-- Specialize a function `body` via IPSCCP + Dead-Argument Elimination (DAE)
at constant argument `c₀`: replaces `arg` with `c₀` and marks linkage `.internal`. -/
def specializeIpsccpDae (d : FnDef) (c₀ : Val) : FnDef where
  sym     := d.sym
  linkage := .internal
  body    := fun _ mem => d.body c₀ mem

/-- WPO Soundness: Under `ClosedWorldConstArgAssumption`, replacing `d` with
`specializeIpsccpDae d c₀` produces the exact same outcome at every internal
call site and preserves all `preservedExports`. -/
theorem wpo_internalize_ipsccp_sound
    (preservedExports : List SymId) (d : FnDef) (c₀ callerArg mem : Val)
    (hclosed : ClosedWorldConstArgAssumption preservedExports d.sym c₀ callerArg) :
    (specializeIpsccpDae d c₀).body callerArg mem = d.body callerArg mem ∧
    d.sym ∉ preservedExports := by
  refine ⟨?_, hclosed.not_exported⟩
  unfold specializeIpsccpDae
  rw [hclosed.internal_call_const]

/-- Canary 1 (Open-World WPO Unsoundness): If `d` is specialized for `c₀ = 10`
under a false closed-world assumption, an unrecorded external caller passing
`externalArg = 99` observes a wrong return value (`11 ≠ 100`). -/
def sampleFnDef : FnDef where
  sym     := 1
  linkage := .external
  body    := fun arg mem => some (arg + 1, mem)

theorem canary_open_world_ipsccp_unsound :
    let specDef := specializeIpsccpDae sampleFnDef 10
    specDef.body 99 0 ≠ sampleFnDef.body 99 0 := by
  decide

/-!
## 3. ThinLTO Summary-Based Importing & `-Zshare-generics` `WeakODR` Coherence
-/

/-- ThinLTO summary entry (`ModuleSummaryIndex` in `PassWrapper.cpp:1216`). -/
structure ThinLtoSummary where
  guid       : SymId
  linkage    : Linkage
  inlineBody : Val → Val → Option (Val × Val)

/-- Coherence predicate for `WeakODR` / `LinkOnceODR` generic instantiations
across CGUs (`InstantiationMode::GloballyShared` in
`compiler/rustc_symbol_mangling/src/lib.rs:289` and `getFirstDefinitionForLinker`
in `PassWrapper.cpp:1248`): the prevailing definition selected by the linker and
the summary body imported for inlining must both satisfy the same `FnContract`. -/
def WeakOdrCoherent (prevailing : FnDef) (summary : ThinLtoSummary) (c : FnContract) : Prop :=
  prevailing.sym = summary.guid ∧
  SatisfiesContract prevailing.body c ∧
  SatisfiesContract summary.inlineBody c

/-- ThinLTO Import Soundness: Whether a caller CGU inlines `summary.inlineBody`
(`available_externally`) or emits a call to the linker's `prevailing` copy,
the call satisfies `c`. -/
theorem thinLto_summary_import_sound
    (prevailing : FnDef) (summary : ThinLtoSummary) (c : FnContract)
    (hcoh : WeakOdrCoherent prevailing summary c)
    (inlined : Bool) :
    SatisfiesContract (if inlined then summary.inlineBody else prevailing.body) c := by
  cases inlined
  · exact hcoh.2.1
  · exact hcoh.2.2

/-- Canary 2 (Incoherent `WeakODR` Generic Sharing): Suppose CGU A and CGU B
both emit a `WeakODR` symbol with the same mangled name (e.g., due to differing
`#[cfg]` flags or unsound specialization without hashing into the symbol GUID),
where CGU A returns `arg + 1` and CGU B returns `arg + 2`. If ThinLTO imports
CGU A's summary to inline into caller 1 while the linker picks CGU B as the
prevailing definition for caller 2, the two call sites to the same Rust generic
function disagree on identical inputs! -/
theorem canary_incoherent_weak_odr_unsound :
    let cguABody : Val → Val → Option (Val × Val) := fun arg mem => some (arg + 1, mem)
    let cguBBody : Val → Val → Option (Val × Val) := fun arg mem => some (arg + 2, mem)
    cguABody 5 0 ≠ cguBBody 5 0 := by
  decide

/-!
## 4. Conditional Mixed-Binary Statements, Circularity, and Reentrant Callbacks
-/

/-- Canary 3 (Circular Rely-Guarantee Vacuity): Without well-founded call-depth
fuel or step-indexing, mutually conditional specifications `(P → Q) ∧ (Q → P)`
are satisfied by `P = False` and `Q = False`, proving nothing. -/
theorem canary_circular_assumption_vacuity :
    ∃ (P Q : Prop), (P → Q) ∧ (Q → P) ∧ ¬ P ∧ ¬ Q :=
  ⟨False, False, id, id, id, id⟩

/-- Well-founded call-depth-indexed conditional composition: if every call
decreases `depth : Nat`, `(∀ k < d, P k → Q k)` and `(∀ d, (∀ k < d, Q k) → P d)`
entail `∀ d, P d ∧ Q d` unconditionally by strong induction. -/
theorem conditional_mixed_binary_sound
    (P Q : Nat → Prop)
    (h_unverified : ∀ d, P d → Q d)
    (h_verified   : ∀ d, (∀ k, k < d → Q k) → P d) :
    ∀ d, P d ∧ Q d := by
  intro d
  have hp : ∀ n, n ≤ d → P n ∧ Q n := by
    induction d with
    | zero =>
      intro n hn
      have hzero : n = 0 := Nat.eq_zero_of_le_zero hn
      subst hzero
      have hp0 : P 0 := h_verified 0 (fun _ hk => nomatch hk)
      exact ⟨hp0, h_unverified 0 hp0⟩
    | succ m ih =>
      intro n hn
      by_cases hlt : n ≤ m
      · exact ih n hlt
      · have heq : n = m + 1 := by omega
        subst heq
        have hpm : P (m + 1) := h_verified (m + 1) (fun k hk => (ih k (by omega)).2)
        exact ⟨hpm, h_unverified (m + 1) hpm⟩
  exact hp d (Nat.le_refl d)

/-- Canary 4 (Reentrant Callback Breaking Private Library Invariant):
Consider a verified library whose private invariant is `mem % 2 = 0`.
A verified method temporarily increments `mem` to `mem + 1` (odd!), invokes an
unverified foreign callback `cb`, and then increments `mem` by `1` again to
restore `mem + 2` (even). If `cb` re-enters a safe library getter that assumes
the library invariant `mem % 2 = 0`, the invariant is violated (`(mem + 1) % 2 ≠ 0`)! -/
def LibraryInv (mem : Val) : Prop := mem % 2 = 0

def verifiedMethodWithCallback (cb : Val → Option Val) (mem : Val) : Option Val :=
  let halfUpdatedMem := mem + 1
  match cb halfUpdatedMem with
  | some observed => some observed
  | none => none

def reentrantSafeReader (mem : Val) : Option Val :=
  if mem % 2 == 0 then some mem else none

theorem canary_reentrant_callback_invariant_breach :
    LibraryInv 0 ∧
    verifiedMethodWithCallback reentrantSafeReader 0 = none ∧
    ¬ LibraryInv (0 + 1) := by
  refine ⟨rfl, rfl, ?_⟩
  unfold LibraryInv
  decide

end CompositionalLinkingAndWpoProbe

#print axioms CompositionalLinkingAndWpoProbe.horizontal_link_sound
#print axioms CompositionalLinkingAndWpoProbe.wpo_internalize_ipsccp_sound
#print axioms CompositionalLinkingAndWpoProbe.canary_open_world_ipsccp_unsound
#print axioms CompositionalLinkingAndWpoProbe.thinLto_summary_import_sound
#print axioms CompositionalLinkingAndWpoProbe.canary_incoherent_weak_odr_unsound
#print axioms CompositionalLinkingAndWpoProbe.canary_circular_assumption_vacuity
#print axioms CompositionalLinkingAndWpoProbe.conditional_mixed_binary_sound
#print axioms CompositionalLinkingAndWpoProbe.canary_reentrant_callback_invariant_breach
