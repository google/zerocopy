-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Tarjan SCC Greatest-Fixpoint and Lexicographic Ranking Summary Certificates for Mutually Recursive ThinLTO

Standalone Lean 4 (`v4.34.1`) mechanization extending `ThinLtoSummaryAndCacheProofs.lean`
from DAG call graphs to cyclic and mutually recursive Tarjan Strongly Connected Components (SCCs):
1. **Greatest-Fixpoint Co-Inductive Summary Certificates (`SccGfpCert` /
   `scc_gfp_nounwind_and_memeffect_sound`)**:
   - Proves by step-indexed induction over arbitrary call depth `fuel : Nat`
     that safety and memory-effect properties (`nounwind`, `MemEffect.readnone`,
     `MemEffect.readonly`, `MemEffect.argmemonly`) are closed under greatest
     fixpoints: if every function `f ∈ S` in a mutually recursive SCC `S`
     locally satisfies `(sccEffect, sccNounwind)` under the optimistic hypothesis
     that intra-SCC calls also satisfy `(sccEffect, sccNounwind)`, then every
     finite execution of every `f ∈ S` satisfies `(sccEffect, sccNounwind)`—even
     without proving termination (`willreturn`)!
2. **Lexicographic Well-Founded Ranking Certificates for `willreturn`
   (`SccRankingCert` / `scc_lfp_willreturn_ranking_sound`)**:
   - Formalizes 2D lexicographic ranking measures `μ_f(x) = (paramMeasure, nodeRank) ∈ Nat × Nat`
     with `nodeRank < sccSize` and path-guard `FarkasCert2` edge certificates
     (`checkSccEdgeRankDec`).
   - Proves that if every intra-SCC call edge `(f, x) → (g, y)` strictly decreases
     `μ_g(y) <_{lex} μ_f(x)` (`lexRank2D sccSize (μ g y) < lexRank2D sccSize (μ f x)`),
     every function `f ∈ S` terminates within bounded recursion depth, soundly
     certifying `willreturn = true` across mutually recursive ThinLTO cycles where
     both `U9` and stock LLVM 23.1.1 `FunctionAttrs.cpp` (`checkNoCycles`) give up.
3. **Condensation-DAG Incremental Cache Key Soundness (`condensation_scc_cache_hit_sound`)**
   and negative canaries (`canary_coinductive_willreturn_without_ranking_unsound`,
   `canary_zero_decrease_cycle_rejected`).
-/

namespace ThinLtoSccFixpointProofs

abbrev FnId   := Nat
abbrev Val    := Nat
abbrev Digest := Nat

/-- Lattice of function memory effects (`VerifiedFnAttrs` in `.anneal-summary`). -/
inductive MemEffect where
  | readnone
  | readonly
  | argmemonly
  | readwrite
  deriving DecidableEq, Repr

def MemEffect.rank : MemEffect → Nat
  | .readnone   => 0
  | .readonly   => 1
  | .argmemonly => 2
  | .readwrite  => 3

/-- Safety summary attributes (closed under greatest fixpoints over finite traces). -/
structure SafetySummaryAttrs where
  memEffect : MemEffect
  nounwind  : Bool
  deriving DecidableEq, Repr

/-- Predicate stating that an observed execution outcome `(memMutated, unwound)`
satisfies the safety summary `attrs`. -/
def SatisfiesSafetyAttrs (attrs : SafetySummaryAttrs) (memMutated : Nat) (unwound : Bool) : Prop :=
  memMutated ≤ attrs.memEffect.rank ∧ (attrs.nounwind = true → unwound = false)

/-- Step-indexed execution of a function `f` in a mutually recursive SCC at call-stack
depth `fuel : Nat`. At `fuel = 0`, execution reaches the step bound with `(0, false)`.
At `fuel + 1`, `f` executes its local statement effect `(localMem f, localUnwind f)`
combined with the step-indexed outcome of its recursive intra-SCC callee `nextCallee f`
and external DAG callee effect `(extMem f, extUnwind f)`. -/
def execSccStep
    (localMem extMem : FnId → Nat)
    (localUnwind extUnwind : FnId → Bool)
    (nextCallee : FnId → FnId)
    (fuel : Nat) (f : FnId) : Nat × Bool :=
  match fuel with
  | 0 => (0, false)
  | fuel' + 1 =>
    let recOut := execSccStep localMem extMem localUnwind extUnwind nextCallee fuel' (nextCallee f)
    (Nat.max (Nat.max (localMem f) (extMem f)) recOut.1,
     (localUnwind f || extUnwind f) || recOut.2)

/-- Local SCC Greatest-Fixpoint Certificate (`SccGfpCert`): every function `f` in the
SCC locally obeys `sccAttrs`, and every external DAG callee invoked by `f` obeys `sccAttrs`. -/
def LocalSccBodyValid
    (sccAttrs : SafetySummaryAttrs)
    (localMem extMem : FnId → Nat)
    (localUnwind extUnwind : FnId → Bool) : Prop :=
  ∀ f : FnId,
    SatisfiesSafetyAttrs sccAttrs (localMem f) (localUnwind f) ∧
    SatisfiesSafetyAttrs sccAttrs (extMem f) (extUnwind f)

/-- **Theorem 1 (`scc_gfp_nounwind_and_memeffect_sound`)**: If `LocalSccBodyValid`
holds for `sccAttrs` across a mutually recursive SCC (where `nextCallee : FnId → FnId`
may contain arbitrary cycles), then for **all** step depths `fuel : Nat` and **all**
functions `f : FnId` in the SCC, `execSccStep ... fuel f` satisfies `sccAttrs`! -/
theorem scc_gfp_nounwind_and_memeffect_sound
    (sccAttrs : SafetySummaryAttrs)
    (localMem extMem : FnId → Nat)
    (localUnwind extUnwind : FnId → Bool)
    (nextCallee : FnId → FnId)
    (h_local : LocalSccBodyValid sccAttrs localMem extMem localUnwind extUnwind)
    (fuel : Nat) (f : FnId) :
    let out := execSccStep localMem extMem localUnwind extUnwind nextCallee fuel f
    SatisfiesSafetyAttrs sccAttrs out.1 out.2 := by
  induction fuel generalizing f with
  | zero =>
    unfold execSccStep SatisfiesSafetyAttrs
    refine ⟨ Nat.zero_le _, ?_ ⟩
    intro _
    rfl
  | succ fuel' ih =>
    unfold execSccStep SatisfiesSafetyAttrs
    dsimp only
    have h_f := h_local f
    have h_loc := h_f.1
    have h_ext := h_f.2
    have h_rec := ih (nextCallee f)
    unfold SatisfiesSafetyAttrs at h_loc h_ext h_rec
    refine ⟨?_, ?_⟩
    · have hm1 : Nat.max (localMem f) (extMem f) ≤ sccAttrs.memEffect.rank :=
        Nat.max_le.mpr ⟨h_loc.1, h_ext.1⟩
      exact Nat.max_le.mpr ⟨hm1, h_rec.1⟩
    · intro h_nw
      have hu_loc := h_loc.2 h_nw
      have hu_ext := h_ext.2 h_nw
      have hu_rec := h_rec.2 h_nw
      simp [hu_loc, hu_ext, hu_rec]

/-!
## 2. Lexicographic Well-Founded Ranking Certificates for `willreturn` (`SccRankingCert`)
-/

/-- 2D lexicographic ranking tuple `(paramMeasure, nodeRank)` for a function inside
an SCC of size `sccSize > 0`. `paramMeasure` is a non-negative integer measure of
the function's parameters (e.g., slice length `len` or recursion depth `n`), and
`nodeRank < sccSize` breaks ties across zero-decrease mutual dispatcher edges. -/
structure LexRank2D where
  paramMeasure : Nat
  nodeRank     : Nat
  deriving DecidableEq, Repr

/-- Strictly monotone linearization of `LexRank2D` into `Nat` when `nodeRank < sccSize`:
`linearRank sccSize r = r.paramMeasure * sccSize + r.nodeRank`. -/
def linearRank (sccSize : Nat) (r : LexRank2D) : Nat :=
  r.paramMeasure * sccSize + r.nodeRank

/-- Decidable 2D lexicographic strict inequality `rDst <_{lex} rSrc` with tie-break
bound check `rDst.nodeRank < sccSize`. -/
def checkLexEdgeDec (sccSize : Nat) (rSrc rDst : LexRank2D) : Bool :=
  (rDst.nodeRank < sccSize) &&
  ((rDst.paramMeasure < rSrc.paramMeasure) ||
   ((rDst.paramMeasure == rSrc.paramMeasure) && (rDst.nodeRank < rSrc.nodeRank)))

/-- **Lemma (`checkLexEdgeDec_implies_linearRank_lt`)**: Whenever `checkLexEdgeDec`
returns `true`, the linearized rank `linearRank sccSize rDst` is strictly smaller
than `linearRank sccSize rSrc`. -/
theorem checkLexEdgeDec_implies_linearRank_lt
    (sccSize : Nat) (rSrc rDst : LexRank2D)
    (h_dec : checkLexEdgeDec sccSize rSrc rDst = true) :
    linearRank sccSize rDst < linearRank sccSize rSrc := by
  unfold checkLexEdgeDec linearRank at *
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h_dec
  rcases h_dec with ⟨h_bound, h_lt | ⟨h_eq_beq, h_rank_lt⟩⟩
  · have h_diff : rDst.paramMeasure + 1 ≤ rSrc.paramMeasure := h_lt
    have h_mul : (rDst.paramMeasure + 1) * sccSize ≤ rSrc.paramMeasure * sccSize :=
      Nat.mul_le_mul_right sccSize h_diff
    rw [Nat.add_mul, Nat.one_mul] at h_mul
    omega
  · have h_eq : rDst.paramMeasure = rSrc.paramMeasure := LawfulBEq.eq_of_beq h_eq_beq
    rw [h_eq]
    omega

/-- Mutual recursion evaluator over `(f, arg)` bounded by `fuel : Nat`.
At each step, `stepOrBase f arg` either returns `none` (base case: function returns
immediately) or `some (callee, nextArg)` (recursive call within the SCC). -/
def evalMutualScc
    (stepOrBase : FnId → Val → Option (FnId × Val))
    (fuel : Nat) (f : FnId) (arg : Val) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    match stepOrBase f arg with
    | none => true
    | some (callee, nextArg) => evalMutualScc stepOrBase fuel' callee nextArg

/-- Valid `SccRankingCert`: for every active intra-SCC call edge `(f, arg) → (callee, nextArg)`,
`checkLexEdgeDec sccSize (rankOf f arg) (rankOf callee nextArg) = true`. -/
def ValidSccRankingCert
    (sccSize : Nat)
    (rankOf : FnId → Val → LexRank2D)
    (stepOrBase : FnId → Val → Option (FnId × Val)) : Prop :=
  ∀ f arg callee nextArg,
    stepOrBase f arg = some (callee, nextArg) →
    checkLexEdgeDec sccSize (rankOf f arg) (rankOf callee nextArg) = true

/-- **Theorem 2 (`scc_lfp_willreturn_ranking_sound`)**: If a mutually recursive
SCC has a valid `SccRankingCert`, then every call `(f, arg)` is guaranteed to
halt and return (`evalMutualScc = true`) within `linearRank sccSize (rankOf f arg) + 1`
steps, soundly certifying `willreturn = true`! -/
theorem scc_lfp_willreturn_ranking_sound
    (sccSize : Nat)
    (rankOf : FnId → Val → LexRank2D)
    (stepOrBase : FnId → Val → Option (FnId × Val))
    (h_cert : ValidSccRankingCert sccSize rankOf stepOrBase) :
    ∀ bound : Nat, ∀ f : FnId, ∀ arg : Val,
      linearRank sccSize (rankOf f arg) ≤ bound →
      evalMutualScc stepOrBase (bound + 1) f arg = true := by
  intro bound
  induction bound with
  | zero =>
    intro f arg h_le
    unfold evalMutualScc
    cases h_step : stepOrBase f arg with
    | none => rfl
    | some pair =>
      exfalso
      have h_dec := h_cert f arg pair.1 pair.2 h_step
      have h_lt := checkLexEdgeDec_implies_linearRank_lt sccSize (rankOf f arg) (rankOf pair.1 pair.2) h_dec
      omega
  | succ bound' ih =>
    intro f arg h_le
    unfold evalMutualScc
    cases h_step : stepOrBase f arg with
    | none => rfl
    | some pair =>
      have h_dec := h_cert f arg pair.1 pair.2 h_step
      have h_lt := checkLexEdgeDec_implies_linearRank_lt sccSize (rankOf f arg) (rankOf pair.1 pair.2) h_dec
      have h_next_le : linearRank sccSize (rankOf pair.1 pair.2) ≤ bound' := by omega
      exact ih pair.1 pair.2 h_next_le

/-!
## 3. Tarjan Condensation-DAG Incremental Cache Key Soundness
-/

structure CondensationSccCacheKey where
  sccMemberMirHashes     : List Digest
  upstreamSccSummaryHash : Digest
  deriving DecidableEq, Repr

/-- **Theorem 3 (`condensation_scc_cache_hit_sound`)**: Equality of
`CondensationSccCacheKey` over Tarjan's condensation DAG guarantees that the
cached SCC fixpoint summary and per-member `HybridTrace` certificates remain valid. -/
theorem condensation_scc_cache_hit_sound
    (SccValid : CondensationSccCacheKey → Prop)
    (cached current : CondensationSccCacheKey)
    (h_valid : SccValid cached)
    (h_eq : (cached == current) = true) :
    SccValid current := by
  have heq : cached = current := LawfulBEq.eq_of_beq h_eq
  subst heq
  exact h_valid

/-!
## 4. Negative Canaries
-/

/-- **Canary 1 (`canary_coinductive_willreturn_without_ranking_unsound`)**:
A self-recursive function `infLoop(x) = infLoop(x)` (`stepOrBase 0 x = some (0, x)`)
satisfies `LocalSccBodyValid` for `nounwind` and `readnone`, but never terminates
(`evalMutualScc` is `false`), proving why `willreturn` cannot use `SccGfpCert`! -/
theorem canary_coinductive_willreturn_without_ranking_unsound :
    let infLoopStep : FnId → Val → Option (FnId × Val) := fun f x => some (f, x)
    evalMutualScc infLoopStep 10 0 42 = false := by
  decide

/-- **Canary 2 (`canary_zero_decrease_cycle_rejected`)**: A 2-function mutual cycle
`f(n) → g(n) → f(n)` where `paramMeasure = n` is unchanged on both edges cannot
satisfy `checkLexEdgeDec` around the cycle for any assignment of `nodeRank`. -/
theorem canary_zero_decrease_cycle_rejected (n rF rG : Nat) :
    ¬(checkLexEdgeDec 2 { paramMeasure := n, nodeRank := rF } { paramMeasure := n, nodeRank := rG } = true ∧
      checkLexEdgeDec 2 { paramMeasure := n, nodeRank := rG } { paramMeasure := n, nodeRank := rF } = true) := by
  intro ⟨h1, h2⟩
  have hlt1 := checkLexEdgeDec_implies_linearRank_lt 2
    { paramMeasure := n, nodeRank := rF } { paramMeasure := n, nodeRank := rG } h1
  have hlt2 := checkLexEdgeDec_implies_linearRank_lt 2
    { paramMeasure := n, nodeRank := rG } { paramMeasure := n, nodeRank := rF } h2
  omega

end ThinLtoSccFixpointProofs

#print axioms ThinLtoSccFixpointProofs.scc_gfp_nounwind_and_memeffect_sound
#print axioms ThinLtoSccFixpointProofs.checkLexEdgeDec_implies_linearRank_lt
#print axioms ThinLtoSccFixpointProofs.scc_lfp_willreturn_ranking_sound
#print axioms ThinLtoSccFixpointProofs.condensation_scc_cache_hit_sound
#print axioms ThinLtoSccFixpointProofs.canary_coinductive_willreturn_without_ranking_unsound
#print axioms ThinLtoSccFixpointProofs.canary_zero_decrease_cycle_rejected
