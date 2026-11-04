<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Hyperproperties, Relational Bisimulation 2-Safety, Bounded Nondeterminism, and McLean's Refinement Paradox in Semantic Verification Models

## Summary

- **1-Trace Blindness vs. Demonic Self-Composition (`Theorem 1A` & `Theorem 1B`):** A 1-trace specification `Spec` (`Language.VerifiedSpineOn`) predicates over individual `(Query, SemObs)` execution pairs (`Clarkson & Schneider 2010`). When `SemObs` projects only functional outputs (`obs o := o.1`), a constant-time cipher `.ctCipher` (`o = (pub + 1, 10)`) and a key-leaking cipher `.leakyCipher` (`o = (pub + 1, sec)`) induce identical 1-trace behaviors and satisfy the exact same 1-trace specifications (`PENTEST-7`, [theorem1a_one_trace_blind_to_two_safety](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L469)). Conversely, encoding 2-safety via demonic self-composition on the product language `L.diag` (`Barthe, D'Argenio & Rezk 2004`; `Terauchi & Aiken 2005`) is logically equivalent to possibilistic non-interference (`Language.NonInterferingOn`) **conjoined with per-query leakage determinism** (`Language.LeakageDeterministicOn`, [theorem1b_diag_iff_possibilistic_ni_and_leakage_deterministic](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L650)). Consequently, demonic self-composition `L.diag` unconditionally locks out every program with secret-independent nondeterministic timing jitter $t \in \{10, 11\}$ (`PENTEST-R2-9B`, [pentest_r2_9b_demonic_diag_locks_out_secret_independent_jitter](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L721)), while a timing-only diagonal postcondition that omits 1-trace functional correctness certifies functionally broken constant-zero implementations (`PENTEST-R2-9A`, [pentest_r2_9a_timing_only_diag_certifies_badCipher](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L589)).
- **One-Way Simulation Failure vs. Indexed Security Domain Bisimulation (`Theorem 2A` & `Theorem 2B`):** One-directional existential 2-safety (`Language.NonInterferingOn`: $\text{lowEq}(q_1, q_2) \to \forall v_1 \in \text{Obs}(p, q_1),\ \exists v_2 \in \text{Obs}(p, q_2),\ \text{leakEq}(v_1, v_2)$) is unsound under any non-symmetric preorder `lowEq` (such as $\text{pub}_1 = \text{pub}_2 \wedge \text{sec}_1 \le \text{sec}_2$): a cipher `.subsetLeakyCipher` with timing $\{10\}$ at $\text{sec} = 0$ and $\{10, 20\}$ at $\text{sec} > 0$ passes one-way simulation even though observing $t = 20$ leaks $\text{sec} > 0$ with 100% certainty (`PENTEST-R3-7`, [pentest_r3_7_asymmetric_one_way_ni_admits_subset_leak](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L820)). Furthermore, even two-way simulation (`Language.SymmetricBiNonInterferingOn`) is bypassed when `lowEq` is trivial (`Eq`, `PENTEST-R2-9`) or punctured at master keys ($\text{sec} \ge 2$, `PENTEST-R3-6B`), when `leakEq` erases the side-channel projection (`PENTEST-R3-6A`, [pentest_r3_6_policy_degeneracies](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L913)), or when positional binary product typeclasses (`PositionalPublicQuery`, `PositionalLeakageObs`, `Candidate 016`) misclassify left-associated 3-tuples `((pub, sec₁), sec₂)` and `((ret, cycles), cache)` (`PENTEST-R4-5A/B`, [pentest_r4_5_positional_tuple_bypasses](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1031)). Parameterizing 2-safety by an explicit Cartesian **Security Domain Decomposition** (`SecurityDomain`: `projPub`, `projSec`, `projVal`, `projLeak` with verified round-trip laws) guarantees that induced `D.lowEq` and `D.leakEq` are equivalence relations with non-trivial secret fibers whenever $|\text{Sec}| \ge 2$, and proves that two-way `DomainBiNonInterferingOn` is sound and complete for possibilistic leakage-set invariance ([theorem2b_security_domain_decomposition_characterization](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1147), [defense_r4_5_explicit_security_domains_refute_both_leaks](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1239)).
- **McLean's Refinement Paradox & Bisimulation-Preserving Compilation (`Theorem 3A` & `Theorem 3B`):** Standard productive demonic compiler refinement (`ProductiveCompiles`: $\emptyset \subsetneq L_2.\text{sem}(p_2, q) \subseteq L_1.\text{sem}(p_1, q)$) **does not preserve 2-safety bisimulation non-interference** (`McLean 1994`). In `Candidate 008`–`016`, source-level `BiNonInterferingOn` conjoined with `ProductiveCompiles` allows a source cipher `.jitterSafeCipher` with secret-independent timing $\{10, 20\}$ to be compiled by `mcleanParadoxCompiler` into `.refinedLeakyCipher`, which refines $\{10, 20\}$ into $\{10\}$ when $\text{sec} = 0$ and into $\{20\}$ when $\text{sec} > 0$—satisfying `ProductiveCompiles` and target 1-trace functional correctness while leaking the secret key on $L_2$ ([theorem3a_mclean_refinement_paradox_counterexample](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1358)). We mechanize two exact resolutions: (1) if the source program is leakage-deterministic (`Language.LeakageDeterministicOn`), standard `ProductiveCompiles` transfers `SymmetricBiNonInterferingOn` to the target ([theorem3b_resolution1_leakage_deterministic_transfer](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1474)); and (2) for nondeterministic languages, **Leakage-Bisimulation-Preserving Compilation (`LeakageBisimCompiles`)** and **Secret-Uniform Refinement (`UniformRefinementCompiles`)** transfer 2-safety to the target, compose vertically across multi-pass pipelines, and reject `mcleanParadoxCompiler` while admitting both jitter-preserving and uniform determinizing compilers ([theorem3b_resolution2_leakage_bisim_compiles_and_uniform_refinement](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1574)).
- **The Nondeterminism Refinement Lattice (`Theorem 4A` & `Theorem 4B`):** Across the five-tier nondeterminism lattice (`Back & von Wright 1998`; `Roscoe 1995`; `Søndergaard & Sestoft 1992`), demonic-only `Compiles` certifies empty-semantics miracles (`.miracleEmpty`, `PENTEST-6`), target-only `Tool.SoundTargetOn` certifies chaotic uninitialized reads lowered to constants (`.uninitRead`, `PENTEST-R2-8A`), finite $k$-value exclusion `Language.NonChaoticOn` is bypassed by bounded-bitwidth uninitialized register reads (`.uninitByteRead` $0 < o < 256$, which excludes $0$ and $256 + k$ for all $k \in \mathbb{N}$, `PENTEST-R3-2C`), and angelic verification `Language.VerifiedAngelicSpineOn` certifies programs with specification-violating branches (`.nondetMixed` returning $\{8(q+1), 999\}$, `PENTEST-R3-9A`, [theorem4a_nondeterminism_pathology_hierarchy](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1797), [bounded_bitwidth_chaos_excludes_infinitely_many_values](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1886)). **Productive Demonic Specification Refinement (`Language.VerifiedSpineOn`)** is the unique verification modality that simultaneously rejects `.miracleEmpty`, `.uninitRead`, `.uninitByteRead`, and `.nondetMixed`, certifies both deterministic (`.alignedConst8`, `.alignedAllocLow`) and specification-bounded nondeterministic (`.alignedAllocChoices`) programs, and transfers soundly across `ProductiveCompiles` ([verifiedSpineOn_transfers_across_productiveCompiles](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1914), [theorem4b_productive_demonic_spec_refinement_characterization](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1954)).

## Applicability

Every subject recorded in `REPORT.json` is cataloged below with its exact version, digest, or source locator:

| Subject Kind | Name | Version / Digest / Locator / Scope |
| :--- | :--- | :--- |
| `git` | `leanprover/lean4` | Repository `https://github.com/leanprover/lean4`, commit `5045d0056413266e57c625dcd7c365b10e377c52`, version `v4.34.1` |
| `artifact` | [support/HyperpropertiesBisimulationAndRefinementParadox.lean](support/HyperpropertiesBisimulationAndRefinementParadox.lean) | Standalone 2,093-line Lean 4 (`v4.34.1`) mechanization; digest `sha256:6306b827bafa22c324b351b606cf02f35313dedd181c778f723fe65563ee43b2` |
| `symbol` | `HyperpropertiesBisimulationAndRefinementParadox.Language.diag` | `support/HyperpropertiesBisimulationAndRefinementParadox.lean:561` — diagonal 2-safety self-composition functor on `Language SemObs` |
| `symbol` | `HyperpropertiesBisimulationAndRefinementParadox.SecurityDomain` | `support/HyperpropertiesBisimulationAndRefinementParadox.lean:1092` — Cartesian security domain decomposition `Query ≃ Pub × Sec` and `SemObs ≃ Val × Leak` |
| `symbol` | `HyperpropertiesBisimulationAndRefinementParadox.LeakageBisimCompiles` | `support/HyperpropertiesBisimulationAndRefinementParadox.lean:1531` — leakage-bisimulation-preserving compiler refinement |
| `symbol` | `HyperpropertiesBisimulationAndRefinementParadox.UniformRefinementCompiles` | `support/HyperpropertiesBisimulationAndRefinementParadox.lean:1546` — secret-uniform compiler refinement preserving target 2-safety |
| `concept` | `2-safety non-interference and constant-time execution vs. 1-trace specifications` | Expressiveness separation between 1-trace safety predicates on individual executions and 2-safety hyperproperties over pairs of execution traces (`Clarkson & Schneider 2010`; `Goguen & Meseguer 1982`) |
| `concept` | `demonic self-composition vs. possibilistic bisimulation under timing jitter` | Exact equivalence of demonic self-composition on `L.diag` with possibilistic non-interference conjoined with per-query leakage determinism (`Barthe, D'Argenio & Rezk 2004`; `Terauchi & Aiken 2005`; `Mantel 2000`; `Sabelfeld & Myers 2003`) |
| `concept` | `McLean's refinement paradox across compiler pipelines` | Non-preservation of possibilistic 2-safety non-interference under standard demonic subset refinement `ProductiveCompiles` and its exact resolutions via source leakage determinism or bisimulation-preserving/secret-uniform compilation (`McLean 1994`) |
| `concept` | `nondeterminism refinement lattice (miracles, specification-bounded nondeterminism, angelic reachability, and bounded/unbounded chaos)` | Five-tier lattice of operational outcome sets relative to a specification in the refinement calculus (`Back & von Wright 1998`; `Roscoe 1995`; `Søndergaard & Sestoft 1992`) |

This report applies to semantic verification frameworks built on the 4-primitive architecture (`Language`, `Spec`, `BehaviorCodec`, `Tool`) and to any formal compiler verification spine (such as CompCert, CakeML, Jasmin, or Aeneas/Charon) that combines functional refinement with constant-time or non-interference hyperproperties.

## Findings

### 1. The 1-Trace vs. 2-Safety Expressiveness Separation & Demonic Self-Composition (`SelfCompositionVsJitterTheorem`)

`Basis: normative + source + execution + derived`

#### 1.1 Theoretical Foundation: Trace Properties vs. Hyperproperties

In the taxonomy of Clarkson and Schneider (2010, *Journal of Computer Security*, "Hyperproperties"), a **trace property** $P \subseteq \Sigma^\omega$ (or, for terminating/big-step semantics, $P \subseteq \text{Query} \times \text{SemObs}$) is a set of individual execution traces: a program $p$ satisfies $P$ demonically iff its trace set $\text{Traces}(p)$ satisfies $\text{Traces}(p) \subseteq P$. In the 4-primitive semantic model, `Language.SpecOn` ([L218-L224](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L218-L224)) and `Language.VerifiedSpineOn` ([L241-L245](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L241-L245)) are canonical 1-trace safety modalities:

$$\text{VerifiedSpineOn}_L(\text{dom}, \text{pre}, \text{obsPost}, p) \;\triangleq\; \text{NonVacuousOn}(\text{dom}, \text{pre}) \;\wedge\; \text{ProductiveOn}_L(\text{pre}, p) \;\wedge\; \forall q,\ \text{pre}(q) \to \forall o \in L.\text{sem}(p, q),\ \text{obsPost}(q, L.\text{obs}(o)).$$

By contrast, **non-interference** (Goguen & Meseguer 1982, *IEEE Symposium on Security and Privacy*) and **constant-time execution** are **2-safety hyperproperties**: a falsifying counterexample is not a single bad execution trace $(q, v)$, but a *pair* of execution traces $(q_1, v_1), (q_2, v_2) \in \text{Traces}(p)$ that agree on public inputs ($\text{lowEq}(q_1, q_2)$) yet disagree on side-channel leakage observations ($\neg\text{leakEq}(v_1, v_2)$).

```
1-Trace Modality (SpecOn / VerifiedSpineOn):
  Checks each trace (q, v) in isolation:   (pub, sec₁) ──► (ret₁, time₁)  ✓ ret₁ = pub + 1
                                           (pub, sec₂) ──► (ret₂, time₂)  ✓ ret₂ = pub + 1
  Blind to cross-trace inequality:         time₁ = sec₁ ≠ sec₂ = time₂   (UNCHECKED)

2-Safety Hyperproperty:
  Compares trace pairs ((q₁, v₁), (q₂, v₂)) with lowEq(q₁, q₂):
    • Demonic Self-Composition (L.diag):   ∀ v₁ ∈ Obs(p, q₁), ∀ v₂ ∈ Obs(p, q₂), leakEq(v₁, v₂)
      [Requires LeakageDeterministicOn — rejects hardware timing jitter {10, 11}!]
    • Possibilistic Bisimulation:          ∀ v₁ ∈ Obs(p, q₁), ∃ v₂ ∈ Obs(p, q₂), leakEq(v₁, v₂)
      (SymmetricBiNonInterferingOn)      ∧ ∀ v₂ ∈ Obs(p, q₂), ∃ v₁ ∈ Obs(p, q₁), leakEq(v₁, v₂)
      [Accepts secret-independent jitter {10, 11}; refutes timing side channels!]
```

#### 1.2 Theorem 1A: 1-Trace Blindness to 2-Safety Side Channels (`PENTEST-7` & `PENTEST-R2-9A`)

In `Candidate 003` (`PENTEST-7`), the language projection `obs : Out → SemObs` mapped concrete execution pairs `(retVal, cycleCount) : Nat × Nat` to their functional return value `o.1 : Nat` (`L_crypto_1trace`, [L439-L448](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L439-L448)). We prove in [`theorem1a_one_trace_blind_to_two_safety`](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L469-L523) that:

1. **Observable Indistinguishability (`obs o := o.1`):** For every query $q = (\text{pub}, \text{sec})$ and observable value $v \in \mathbb{N}$, `.ctCipher` (`o = (pub + 1, 10)`) and `.leakyCipher` (`o = (pub + 1, sec)`) produce the exact same observable outcomes:
   $$\forall q\, v,\ \text{Produces}_{L_{\text{crypto\_1trace}}}(\text{.ctCipher}, q, v) \;\Longleftrightarrow\; \text{Produces}_{L_{\text{crypto\_1trace}}}(\text{.leakyCipher}, q, v).$$
2. **Universal 1-Trace Specification Equivalence:** For *every* domain `dom`, precondition `pre`, and 1-trace specification `obsPost`, `.ctCipher` satisfies `VerifiedSpineOn` if and only if `.leakyCipher` satisfies `VerifiedSpineOn`. No 1-trace specification on `L_crypto_1trace` can ever separate a constant-time implementation from one that transmits the secret key directly through its execution time.
3. **Functional 1-Trace Blindness Even Under Full Observation (`L_crypto_full`):** Even when `obs := id` exposes the full tuple `(retVal, cycleCount)` (`L_crypto_full`, [L451-L457](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L451-L457)), any 1-trace functional specification `obsPost (pub, _) (ret, _) := (ret = pub + 1)` certifies `.leakyCipher` while `.leakyCipher` leaks $\text{sec}_1 = 11 \neq 22 = \text{sec}_2$ across low-equivalent queries `(0, 11)` and `(0, 22)`.
4. **Converse Pathology (`PENTEST-R2-9A`):** Conversely, [`pentest_r2_9a_timing_only_diag_certifies_badCipher`](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L589-L604) proves that if a verification suite checks *only* the 2-safety diagonal timing specification `DiagPost (fun v₁ v₂ => v₁.2 = v₂.2)` on `L_crypto_full.diag` without conjoining 1-trace functional correctness, then `.badCipher` (`o = (0, 0)`) passes 2-safety verification while violating functional correctness (`ViolatesSpine`) at every input. Thus 1-trace functional correctness and 2-safety non-interference are **strictly orthogonal** verification obligations.

#### 1.3 Theorem 1B: Exact Characterization of Demonic Self-Composition `L.diag` (`PENTEST-R2-9B`)

To express 2-safety within a 1-trace specification primitive, Barthe, D'Argenio, and Rezk (2004, *CSFW*, "Secure Information Flow by Self-Composition") and Terauchi and Aiken (2005, *SAS*, "Secure Information Flow as a Safety Problem") introduced **self-composition**: running two copies of program $p$ in a product language `L.diag` ([L561-L568](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L561-L568)) where:
- `(L.diag).Prog := L.Prog` (judgmentally equal via `rfl`),
- `(L.diag).Query := L.Query × L.Query`,
- `(L.diag).Out := L.Out × L.Out`, and
- `(L.diag).sem p (q₁, q₂)` is the Cartesian product of `L.sem p q₁` and `L.sem p q₂`.

Under demonic 1-trace verification on `L.diag` with precondition `DiagPre pre lowEq (q₁, q₂) := pre q₁ ∧ pre q₂ ∧ lowEq q₁ q₂` ([L572-L574](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L572-L574)) and postcondition `DiagPost leakEq _ (v₁, v₂) := leakEq v₁ v₂` ([L578-L580](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L578-L580)), demonic refinement requires *every* outcome pair $(v_1, v_2) \in \text{Obs}(p, q_1) \times \text{Obs}(p, q_2)$ to satisfy $\text{leakEq}(v_1, v_2)$ (`Language.AllPairsNonInterferingOn`, [L632-L639](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L632-L639)).

In [`theorem1b_diag_iff_possibilistic_ni_and_leakage_deterministic`](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L650-L695), we prove that for any productive program $p$ on `pre`, reflexive `lowEq`, and symmetric, transitive `leakEq`, the following three properties are **logically equivalent**:

1. **Demonic Self-Composition on `L.diag`:**
   $$(L.\text{diag}).\text{sem}(p) \;\le\; (L.\text{diag}).\text{SpineSpecOn}(\text{DiagPre}(\text{pre}, \text{lowEq}), \text{DiagPost}(\text{leakEq}))$$
2. **All-Pairs Demonic 2-Safety (`AllPairsNonInterferingOn`):**
   $$\forall q_1\, q_2,\ \text{pre}(q_1) \to \text{pre}(q_2) \to \text{lowEq}(q_1, q_2) \to \forall v_1 \in \text{Obs}(p, q_1),\ \forall v_2 \in \text{Obs}(p, q_2),\ \text{leakEq}(v_1, v_2)$$
3. **Possibilistic Non-Interference Conjoined with Per-Query Leakage Determinism:**
   $$\text{NonInterferingOn}_L(\text{pre}, \text{lowEq}, \text{leakEq}, p) \;\wedge\; \text{LeakageDeterministicOn}_L(\text{pre}, \text{leakEq}, p)$$
   where `LeakageDeterministicOn` ([L621-L627](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L621-L627)) requires $\forall q,\ \text{pre}(q) \to \forall v_1, v_2 \in \text{Obs}(p, q),\ \text{leakEq}(v_1, v_2)$.

**Why Demonic Self-Composition Fails on Nondeterministic Hardware (`PENTEST-R2-9B`):** Because $\text{lowEq}(q, q)$ holds by reflexivity at $q_1 = q_2 = q$, demonic self-composition instantiates `DiagPost` at $(q, q)$ and demands that any two independent runs of $p$ on the *exact same input* $q$ produce leakage-equivalent observations $\text{leakEq}(v_1, v_2)$. In [`pentest_r2_9b_demonic_diag_locks_out_secret_independent_jitter`](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L721-L754), we mechanize `L_crypto_jitter` ([L703-L708](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L703-L708)), where program `true` (`ctJitterCipher`) computes `pub + 1` in $t \in \{10, 11\}$ cycles due to secret-independent bus/interrupt jitter. Even though `L_crypto_jitter.sem true (pub, sec₁) = L_crypto_jitter.sem true (pub, sec₂)` holds **by reflexivity (`rfl`) for all secrets $\text{sec}_1, \text{sec}_2$**, demonic self-composition on `L_crypto_jitter.diag` pairs run 1 ($t_1 = 10$) against run 2 ($t_2 = 11$) at $((0, 0), (0, 0))$ and **rejects** `true` (`ViolatesSpine` and `¬ VerifiedSpine`)!

---

### 2. One-Way Simulation Failure vs. Symmetric PER / Bisimulation 2-Safety (`BisimulationTwoSafetyLaws`)

`Basis: normative + source + execution + derived`

#### 2.1 Theorem 2A: Asymmetric Preorder & Policy-Relation Bypasses (`PENTEST-R3-7`, `PENTEST-R3-6A/B`, `PENTEST-R4-5A/B`)

Replacing demonic self-composition with existential possibilistic non-interference (Mantel 2000, *IEEE S&P*; Sabelfeld & Myers 2003, *IEEE JSAC*) resolves the timing-jitter lockout, but introduces five subtle soundness traps uncovered across `Candidate 006`–`016`:

| Vulnerability ID | Candidate | Defective Formulation | Exploiting Program / Witness | Mechanized Theorem |
| :--- | :--- | :--- | :--- | :--- |
| `PENTEST-R3-7` | `Candidate 008` | One-way `NonInterferingOn` under asymmetric preorder `lowEq := (pub₁ = pub₂ ∧ sec₁ ≤ sec₂)` | `.subsetLeakyCipher`: timing $\{10\}$ at $\text{sec} = 0$, $\{10, 20\}$ at $\text{sec} > 0$ (observing $20$ leaks $\text{sec} > 0$) | [`pentest_r3_7_asymmetric_one_way_ni_admits_subset_leak`](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L820-L878) |
| `PENTEST-R2-9` | `Candidate 006` | Unconstrained `lowEq := Eq` (`q₁ = q₂`) | `.leakyCipher`: timing `sec` on all keys (vacuously matched since changing `sec` changes `q`) | [`pentest_r3_6_policy_degeneracies`](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L913-L975) (Part 1) |
| `PENTEST-R3-6B` | `Candidate 008` | Punctured equivalence relation `lowEq := (pub₁ = pub₂ ∧ (sec₁ = sec₂ ∨ (sec₁ < 2 ∧ sec₂ < 2)))` | `.backdoorLeakyCipher`: constant time $10$ on test keys $\text{sec} \in \{0, 1\}$, leaks master keys $\text{sec} \ge 2$ | [`pentest_r3_6_policy_degeneracies`](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L913-L975) (Parts 2–3) |
| `PENTEST-R3-6A` | `Candidate 008` | Timing-blind equivalence relation `leakEq v₁ v₂ := (v₁.1 = v₂.1)` or `True` | `.leakyCipher`: timing `sec` ignored by `leakEq` | [`pentest_r3_6_policy_degeneracies`](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L913-L975) (Part 4) |
| `PENTEST-R4-5A` | `Candidate 016` | Positional binary product typeclass `PositionalPublicQuery (A × B)` (`pubProj q := q.1`) | `L_two_secrets` on `Query = (Nat × Nat) × Nat` (`((pub, sec₁), sec₂)`): `pubProj` treats `sec₁` as public! | [`pentest_r4_5_positional_tuple_bypasses`](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1031-L1075) (Parts 1–2) |
| `PENTEST-R4-5B` | `Candidate 016` | Positional binary product typeclass `PositionalLeakageObs (A × B)` (`leakProj v := v.2`) | `L_multi_channel` on `SemObs = (Nat × Nat) × Nat` (`((ret, cycles), cache)`): `leakProj` treats `cycles` as functional output! | [`pentest_r4_5_positional_tuple_bypasses`](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1031-L1075) (Parts 3–4) |

Two foundational lessons emerge from `Theorem 2A`:
1. **Why One-Way Simulation Fails (`PENTEST-R3-7`):** One-way `NonInterferingOn` checks only set inclusion $\text{Leak}(p, q_1) \subseteq \text{Leak}(p, q_2)$ along directed edges of `lowEq`. Whenever `lowEq` is an asymmetric preorder ($\text{sec}_1 \le \text{sec}_2$), any program whose leakage set grows monotonically with the secret ($\{10\} \subsetneq \{10, 20\}$) passes one-way simulation, yet any observation in the difference set $\{10, 20\} \setminus \{10\} = \{20\}$ identifies the higher secret with certainty. Two-way bisimulation (`Language.SymmetricBiNonInterferingOn`, [L800-L808](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L800-L808)) immediately refutes `.subsetLeakyCipher` even under the asymmetric preorder $\text{sec}_1 \le \text{sec}_2$ ([L832-L835](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L832-L835)). Moreover, when `lowEq` and `leakEq` are symmetric, one-way `NonInterferingOn` and two-way `SymmetricBiNonInterferingOn` coincide ([`symmetry_converts_one_way_to_two_way`](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L882-L896)).
2. **Why Equivalence-Relation Proofs and Unlabelled Tuple Typeclasses Are Insufficient (`PENTEST-R3-6A/B` & `PENTEST-R4-5A/B`):** Requiring `Equivalence lowEq` and `Equivalence leakEq` (even with a single non-triviality witness $\exists q_1 \neq q_2,\ \text{lowEq}(q_1, q_2)$) does not prevent `lowEq` from collapsing equivalence classes into singleton punctures $\{(\text{pub}, \text{sec})\}$ for master keys $\text{sec} \ge 2$ (`PENTEST-R3-6B`). Likewise, synthesizing projections from unlabelled binary products `(A × B)` via `.1` and `.2` (`Candidate 016`) silently misclassifies nested products `(A × B) × C`, where the middle component `B` is grouped into `.1` (`PENTEST-R4-5A/B`).

#### 2.2 Theorem 2B: Indexed Security Domain Decomposition Characterization (`SecurityDomain`)

To eliminate all five policy-relation and positional-projection vulnerabilities simultaneously, we define an explicit Cartesian **Security Domain Decomposition** `SecurityDomain Query SemObs` ([L1092-L1108](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1092-L1108)):

```lean
structure SecurityDomain (Query SemObs : Type) where
  Pub      : Type
  Sec      : Type
  Val      : Type
  Leak     : Type
  projPub  : Query → Pub
  projSec  : Query → Sec
  mkQuery  : Pub → Sec → Query
  projVal  : SemObs → Val
  projLeak : SemObs → Leak
  mkObs    : Val → Leak → SemObs
  projPub_mkQuery  : ∀ pub sec, projPub (mkQuery pub sec) = pub
  projSec_mkQuery  : ∀ pub sec, projSec (mkQuery pub sec) = sec
  mkQuery_proj     : ∀ q, mkQuery (projPub q) (projSec q) = q
  projVal_mkObs    : ∀ val leak, projVal (mkObs val leak) = val
  projLeak_mkObs   : ∀ val leak, projLeak (mkObs val leak) = leak
  mkObs_proj       : ∀ v, mkObs (projVal v) (projLeak v) = v
```

With induced relations `D.lowEq q₁ q₂ := (D.projPub q₁ = D.projPub q₂)` ([L1111-L1113](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1111-L1113)) and `D.leakEq v₁ v₂ := (D.projLeak v₁ = D.projLeak v₂)` ([L1116-L1118](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1116-L1118)), [`theorem2b_security_domain_decomposition_characterization`](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1147-L1192) proves three structural laws:

1. **Automatic Equivalence Relations:** Both `D.lowEq` and `D.leakEq` are pullbacks of propositional equality (`=`) along `D.projPub` and `D.projLeak`, and are therefore automatically reflexive, symmetric, and transitive equivalence relations.
2. **Uniform Non-Trivial Secret Fibers (No Punctured Keys):** By the Cartesian round-trip laws `projPub_mkQuery` and `projSec_mkQuery`, every public input $\text{pub} \in D.\text{Pub}$ has a secret fiber isomorphic to $D.\text{Sec}$: for any two distinct secrets $\text{sec}_1 \neq \text{sec}_2 \in D.\text{Sec}$, the queries $q_1 = D.\text{mkQuery}(\text{pub}, \text{sec}_1)$ and $q_2 = D.\text{mkQuery}(\text{pub}, \text{sec}_2)$ satisfy $q_1 \neq q_2$ and $D.\text{lowEq}(q_1, q_2)$. Unlike a punctured equivalence relation (`PENTEST-R3-6B`), no secret key $\text{sec} \in D.\text{Sec}$ can ever be isolated into a singleton equivalence class.
3. **Soundness and Completeness for Possibilistic Leakage-Set Invariance:** Two-way domain bisimulation `L.DomainBiNonInterferingOn D pre prog` ([L1127-L1130](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1127-L1130)) holds **if and only if** for all low-equivalent queries $q_1, q_2$ satisfying `pre`, the set of reachable leakage observations is identical:
   $$\text{DomainBiNonInterferingOn}_L(D, \text{pre}, p) \;\Longleftrightarrow\; \forall q_1\, q_2,\ \text{pre}(q_1) \to \text{pre}(q_2) \to D.\text{lowEq}(q_1, q_2) \to \forall \ell \in D.\text{Leak},\ \text{ProducesLeak}_L(D, p, q_1, \ell) \leftrightarrow \text{ProducesLeak}_L(D, p, q_2, \ell).$$

In [`defense_r4_5_explicit_security_domains_refute_both_leaks`](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1239-L1260), instantiating `twoSecretDomain` (`Pub := Nat`, `Sec := Nat × Nat`, [L1198-L1214](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1198-L1214)) on `L_two_secrets` and `multiChannelDomain` (`Val := Nat`, `Leak := Nat × Nat`, [L1216-L1232](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1216-L1232)) on `L_multi_channel` unconditionally refutes both `PENTEST-R4-5A` and `PENTEST-R4-5B`.

---

### 3. McLean's Refinement Paradox & Bisimulation-Preserving Compilation (`McLeanRefinementParadoxAndResolution`)

`Basis: normative + source + execution + derived`

#### 3.1 Theorem 3A: Why `ProductiveCompiles` + Source `BiNonInterferingOn` Fails (`McLean 1994`)

In `Candidate 008` through `Candidate 016` (Master Theorem `12B`), the verification architecture certified a compiler pipeline by verifying:
1. 1-trace functional correctness (`VerifiedSpineOn`) on the source program $p_1 \in L_1.\text{Prog}$,
2. 2-safety bisimulation non-interference (`BiNonInterferingOn`) on the **source** program $p_1 \in L_1.\text{Prog}$, and
3. Productive demonic compiler refinement (`ProductiveCompiles`: $\emptyset \subsetneq L_2.\text{sem}(p_2, q) \subseteq L_1.\text{sem}(p_1, q)$) from $p_1$ to the compiled target program $p_2 \in L_2.\text{Prog}$.

While `ProductiveCompiles` soundly transfers 1-trace functional specifications from $L_1$ to $L_2$ ([`verifiedSpineOn_transfers_across_productiveCompiles`](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1914-L1938)), John McLean (1994, *IEEE Symposium on Security and Privacy*, "A General Theory of Composition for Trace Sets Closed Under Selective Interleaving Functions") proved a fundamental impossibility law: **possibilistic non-interference is not closed under demonic subset refinement ($\subseteq$)**.

```
Source Program (.jitterSafeCipher on L_mclean):
  Query (pub, sec = 0) ──► Timing outcomes {10, 20}  ┐
                                                     ├─ Identical leakage sets {10, 20}!
  Query (pub, sec = 1) ──► Timing outcomes {10, 20}  ┘  ✓ Satisfies DomainBiNonInterferingOn

           │
           │  mcleanParadoxCompiler (ProductiveCompiles: ∅ ⊂neq Sem_tgt ⊆ Sem_src)
           ▼

Target Program (.refinedLeakyCipher on L_mclean):
  Query (pub, sec = 0) ──► Timing outcome  {10}      ⊂ {10, 20} (valid demonic refinement!)
  Query (pub, sec = 1) ──► Timing outcome  {20}      ⊂ {10, 20} (valid demonic refinement!)
                                                     ✗ Disjoint leakage sets {10} ≠ {20}!
                                                       Leaks sec with 100% certainty!
```

In [`theorem3a_mclean_refinement_paradox_counterexample`](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1358-L1433), we construct a complete, kernel-checked counterexample on `L_mclean` ([L1323-L1334](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1323-L1334)):
- **Source Program `.jitterSafeCipher`:** For every `(pub, sec)`, produces `(pub + 1, 10) ∨ (pub + 1, 20)`. It satisfies 1-trace functional correctness `VerifiedSpine (fun q => q.1 < 100) (fun q v => v.1 = q.1 + 1)` **and** two-way 2-safety `DomainBiNonInterferingOn stdCryptoDomain (fun q => q.1 < 100)`.
- **Target Program `.refinedLeakyCipher`:** Produces `(pub + 1, 10)` when `sec = 0` and `(pub + 1, 20)` when `sec > 0`.
- **Valid Productive Demonic Compilation:** `mcleanParadoxCompiler` lowers `.jitterSafeCipher ↦ .refinedLeakyCipher` and satisfies `ProductiveCompiles L_mclean L_mclean (BehaviorCodec.id L_mclean) .jitterSafeCipher .refinedLeakyCipher`, because $\{(\text{pub}+1, 10)\} \subseteq \{(\text{pub}+1, 10), (\text{pub}+1, 20)\}$ and $\{(\text{pub}+1, 20)\} \subseteq \{(\text{pub}+1, 10), (\text{pub}+1, 20)\}$ are both non-empty subsets of the source behavior!
- **Target 2-Safety Collapse:** Despite satisfying source 1-trace verification, source 2-safety bisimulation, productive demonic compilation, and target 1-trace verification, the compiled target program `.refinedLeakyCipher` **violates both one-way `NonInterferingOn` and two-way `DomainBiNonInterferingOn`**, leaking `sec = 0` vs. `sec = 1` via deterministic timing `10 ≠ 20`.

#### 3.2 Theorem 3B: Two Exact Resolutions of McLean's Refinement Paradox

How must a semantic verification framework be structured so that target-level 2-safety is guaranteed? We prove two exact, complementary theorems in Section 3.2 of [support/HyperpropertiesBisimulationAndRefinementParadox.lean](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1435-L1661):

1. **Resolution 1 — Leakage-Deterministic Source Transfer ([`theorem3b_resolution1_leakage_deterministic_transfer`](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1474-L1525)):**
   If the source program $p_1$ is productive on `pre₁`, satisfies `SymmetricBiNonInterferingOn`, **and is leakage-deterministic on `pre₁`** (`L₁.LeakageDeterministicOn pre₁ leakEq p₁`), then **standard `ProductiveCompiles` automatically transfers `SymmetricBiNonInterferingOn` to every compiled target program $p_2$ on $L_2$**!
   - *Proof Sketch:* By `Theorem 1B`, `SymmetricBiNonInterferingOn` + `LeakageDeterministicOn` implies `AllPairsNonInterferingOn` on $L_1$: all source outcomes across low-equivalent queries $c.\text{decodeQuery}(q_2)$ and $c.\text{decodeQuery}(q_2')$ inhabit a single `leakEq` equivalence class. Since `Compiles.produces_imp` ([L375-L386](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L375-L386)) maps every target observable outcome at $q_2$ to an identical source observable outcome at $c.\text{decodeQuery}(q_2)$, and `ProductiveCompiles` guarantees at least one target outcome at $q_2'$, any target outcome at $q_2$ is `leakEq`-equivalent to the guaranteed target outcome at $q_2'$.

2. **Resolution 2 — Leakage-Bisimulation-Preserving Compilation (`LeakageBisimCompiles`) and Secret-Uniform Refinement (`UniformRefinementCompiles`, [`theorem3b_resolution2_leakage_bisim_compiles_and_uniform_refinement`](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1574-L1661)):**
   When source semantics genuinely exhibits secret-independent nondeterminism (such as hardware timing jitter $\{10, 20\}$):
   - **`LeakageBisimCompiles`** ([L1531-L1539](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1531-L1539)) conjoins `ProductiveCompiles` with **backward leakage simulation**:
     $$\forall q_2,\ \text{pre}_1(c.\text{decodeQuery}(q_2)) \to \forall v_1 \in \text{Produces}_{L_1}(p_1, c.\text{decodeQuery}(q_2)),\ \exists v_2 \in \text{Produces}_{L_2}(p_2, q_2),\ \text{leakEq}(v_1, v_2).$$
   - **`UniformRefinementCompiles`** ([L1546-L1556](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1546-L1556)) conjoins `ProductiveCompiles` with target-level `SymmetricBiNonInterferingOn` across `lowEq₁`-equivalent queries, allowing the compiler to determinize nondeterminism (e.g., lowering `.jitterSafeCipher`'s $\{10, 20\}$ to `.uniformDet10Cipher`'s $\{10\}$) provided the refinement choice is uniform across secrets.
   - We prove in [`theorem3b_resolution2_leakage_bisim_compiles_and_uniform_refinement`](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1574-L1661) that:
     1. `LeakageBisimCompiles` transfers `SymmetricBiNonInterferingOn` from $L_1$ to $L_2$ (and therefore implies `UniformRefinementCompiles`);
     2. `LeakageBisimCompiles` composes vertically across multi-pass compiler pipelines $L_1 \xrightarrow{c_{12}} L_2 \xrightarrow{c_{23}} L_3$;
     3. Both `LeakageBisimCompiles` and `UniformRefinementCompiles` **refute** `.jitterSafeCipher ↦ .refinedLeakyCipher` (`mcleanParadoxCompiler`), while `LeakageBisimCompiles` **admits** jitter-preserving compilation (`.jitterSafeCipher ↦ .jitterSafeCipher`) and `UniformRefinementCompiles` **admits** uniform determinizing compilation (`.jitterSafeCipher ↦ .uniformDet10Cipher`).

---

### 4. The Nondeterminism Refinement Lattice: Chaos vs. Bounded Nondeterminism vs. Angelic Reachability (`NondeterminismRefinementLattice`)

`Basis: normative + source + execution + derived`

#### 4.1 Theorem 4A: The Five-Tier Nondeterminism Hierarchy & Why Weak Exclusions Fail

In the refinement calculus of Back and von Wright (1998, *Refinement Calculus: A Systematic Introduction*), Roscoe (1995, *The Theory and Practice of Concurrency*), and Søndergaard and Sestoft (1992, *The Computer Journal*, "Non-Determinism in Functional Languages"), the operational outcome set $\text{Obs}(p, q) = \{v \mid \text{Produces}_L(p, q, v)\}$ of a program $p$ at query $q$ relative to a 1-trace specification $S(q) = \{v \mid \text{obsPost}(q, v)\}$ forms a five-tier lattice ordered by demonic subset inclusion:

| Lattice Tier | Outcome Set $\text{Obs}(p, q)$ | Representative Program (`L_lattice`) | `Compiles` (Demonic Only) | `SoundTargetOn` (`PENTEST-R2-8A`) | `NonChaoticOn` (`PENTEST-R3-2C`) | `VerifiedAngelicSpineOn` (`PENTEST-R3-9A`) | `VerifiedSpineOn` (`Theorem 4B`) |
| :--- | :--- | :--- | :---: | :---: | :---: | :---: | :---: |
| **Tier 1: Miracle ($\bot_{\text{demonic}}$)** | $\emptyset$ (`fun _ => False`) | `.miracleEmpty` | **PASS** (Vacuous!) | FAIL | FAIL | FAIL | **REJECT** |
| **Tier 2: Deterministic Exact** | $\{8\}$ or $\{8(q+1)\}$ | `.alignedConst8`, `.alignedAllocLow` | PASS | PASS | PASS | PASS | **ACCEPT** |
| **Tier 3: Spec-Bounded Nondeterminism** | $\{8(q+1), 8(q+2)\} \subseteq S(q)$ | `.alignedAllocChoices` | PASS | PASS | PASS | PASS | **ACCEPT** |
| **Tier 4: Angelic / May-Violate** | $\{8(q+1), 999\} \not\subseteq S(q)$ | `.nondetMixed` | FAIL | **PASS** (Bypass!) | **PASS** (Bypass!) | **PASS** (Bypass!) | **REJECT** |
| **Tier 5a: Bounded Bitwidth Chaos** | $\{1, \dots, 255\} \not\subseteq S(q)$ | `.uninitByteRead` | FAIL | **PASS** (Bypass!) | **PASS** (Bypass!) | **PASS** (Bypass!) | **REJECT** |
| **Tier 5b: Unbounded Chaos ($\top_{\text{demonic}}$)** | $\mathbb{N}$ (`fun _ => True`) | `.uninitRead` | FAIL | **PASS** (Bypass!) | FAIL | **PASS** (Bypass!) | **REJECT** |

In [`theorem4a_nondeterminism_pathology_hierarchy`](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1797-L1878) and [`bounded_bitwidth_chaos_excludes_infinitely_many_values`](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1886-L1890), we mechanize all four historical failure modes on `L_lattice` ([L1722-L1730](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1722-L1730)) against the 8-byte aligned allocator specification `alignedAllocSpec q v := 0 < v ∧ v % 8 = 0 ∧ v ≤ 8 * (q + 2)` ([L1763-L1764](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1763-L1764)):

1. **Miracle Vacuity (`PENTEST-6`):** Because $\emptyset \subseteq \text{Obs}(s, q)$ holds vacuously for every source program $s$, `.miracleEmpty` satisfies `Compiles L_lattice L_lattice (BehaviorCodec.id L_lattice) .alignedAllocLow .miracleEmpty` despite producing zero outcomes (`¬ ProductiveOn`).
2. **Unbounded Chaos Bypass of Target-Only Verification (`PENTEST-R2-8A`):** In `Candidate 006`, `Tool.SoundTargetOn` ([L1751-L1759](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1751-L1759)) required source productivity (`ProductiveOn`), productive demonic compilation (`ProductiveCompiles`), and target specification satisfaction (`L_tgt.sem t ≤ L_tgt.SpineSpecOn`), but omitted source `VerifiedSpineOn`. Because $\text{Obs}(\text{.alignedAllocLow}, q) = \{8(q+1)\} \subseteq \mathbb{N} = \text{Obs}(\text{.uninitRead}, q)$, the compiler `resolveToAlignedLowCompiler` ([L1768-L1775](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1768-L1775)) lowers `.uninitRead ↦ .alignedAllocLow` and `.uninitByteRead ↦ .alignedConst8`, satisfying `Tool.SoundTargetOn` while accepting chaotic uninitialized-memory programs into the "verified" source domain!
3. **Bounded Bitwidth Chaos Bypass of Finite $k$-Value Exclusion (`PENTEST-R3-2C`):** In `Candidate 008`, `Language.NonChaoticOn` ([L1734-L1737](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1734-L1737)) attempted to rule out `.uninitRead` without a source specification by requiring $\forall q,\ \text{pre}(q) \to \exists v_{\text{excl}},\ \neg\text{Produces}(p, q, v_{\text{excl}})$. However, in any typed systems language, uninitialized reads of fixed-width registers or bytes (`u8`, `u16`, `u32`, `u64`) have bounded range: `.uninitByteRead` ($0 < o < 256$) excludes $0$ and excludes $256 + k$ for **every** $k \in \mathbb{N}$ ([`bounded_bitwidth_chaos_excludes_infinitely_many_values`](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1886-L1890)). Thus **no** finite $k$-value exclusion predicate can ever distinguish bounded-bitwidth uninitialized memory reads from specification-bounded nondeterminism!
4. **Angelic Reachability Bypass (`PENTEST-R3-9A`):** `Language.VerifiedAngelicSpineOn` ([L1741-L1746](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1741-L1746)) requires only $\exists v \in \text{Obs}(p, q),\ \text{obsPost}(q, v)$. Both `.uninitByteRead` (via witness $v = 8$) and `.nondetMixed` (via witness $v = 8(q+1)$) satisfy `NonChaoticOn` and `VerifiedAngelicSpineOn` under `alignedAllocSpec`, yet `.uninitByteRead` can return unaligned `1` (`1 % 8 ≠ 0`) and `.nondetMixed` can return unaligned `999` (`999 % 8 ≠ 0`) at $q = 0$.

#### 4.2 Theorem 4B: Demonic-Productive Specification-Bounded Nondeterminism Characterization (`VerifiedSpineOn`)

In [`theorem4b_productive_demonic_spec_refinement_characterization`](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1954-L2006) and [`verifiedSpineOn_transfers_across_productiveCompiles`](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1914-L1938), we prove that **Productive Demonic Specification Refinement** (`Language.VerifiedSpineOn`: $\text{NonVacuousOn} \wedge \text{ProductiveOn} \wedge L.\text{sem}(p) \le L.\text{SpineSpecOn}$) is the unique verification modality that:
- **Rejects Tier 1 Miracles ($\bot$):** `¬ L_lattice.VerifiedSpine (fun q => q < 100) alignedAllocSpec .miracleEmpty` (fails `ProductiveOn`),
- **Rejects Tier 5a/5b Bounded & Unbounded Chaos ($\top$):** `¬ L_lattice.VerifiedSpine (fun q => q < 100) alignedAllocSpec .uninitRead` and `¬ L_lattice.VerifiedSpine (fun q => q < 100) alignedAllocSpec .uninitByteRead` (fail demonic `SpineSpecOn` at $o = 1$),
- **Rejects Tier 4 Angelic May-Violate Nondeterminism:** `¬ L_lattice.VerifiedSpine (fun q => q < 100) alignedAllocSpec .nondetMixed` (fails demonic `SpineSpecOn` at $o = 999$),
- **Certifies Tier 2 Deterministic & Tier 3 Specification-Bounded Nondeterminism:** Certifies `.alignedConst8`, `.alignedAllocLow`, and `.alignedAllocChoices` (which genuinely produces multiple distinct aligned addresses $8 \neq 16$ at $q = 0$), and
- **Transfers Soundly Across `ProductiveCompiles`:** For any `c : BehaviorCodec L₁ L₂`, source `VerifiedSpineOn` and `ProductiveCompiles` imply target `VerifiedSpineOn`.

## Boundaries

1. **Possibilistic vs. Probabilistic / Quantitative Non-Interference:** `Language.DomainBiNonInterferingOn` and `LeakageBisimCompiles` characterize *possibilistic* 2-safety bisimulation (`Sabelfeld & Myers 2003`; `Mantel 2000`): the set of reachable leakage observations $\text{ProducesLeak}(p, (\text{pub}, \text{sec}), \ell)$ is invariant across secrets. If an implementation produces leakage outcomes $\{10, 20\}$ with probability $(0.99, 0.01)$ when $\text{sec} = 0$ and probability $(0.01, 0.99)$ when $\text{sec} = 1$, possibilistic bisimulation holds while a statistical side channel remains. Capturing probabilistic non-interference requires enriching `Behavior Query Out` from `Query → Partial (Out → Prop)` to sub-probability distributions or Markov kernels.
2. **$k$-Safety for $k \ge 3$ and Liveness Hyperproperties:** The diagonal self-composition functor `Language.diag` and `DomainBiNonInterferingOn` address $k = 2$ safety hyperproperties (non-interference, constant-time execution, determinism). General $k$-safety hyperproperties (such as $k$-way secret sharing or transitivity properties) require $k$-fold product languages `L.prod ...`, and hyperliveness properties (such as generalized non-inference or fairness across traces, `Clarkson & Schneider 2010`) cannot be reduced to safety specifications on finite trace products.
3. **Explicit `SecurityDomain` Registration:** As proved in `Theorem 2A.3` (`PENTEST-R4-5A/B`), no syntactic typeclass on unlabelled binary tuples `(A × B)` can infer which components of a compound query or observation type represent secrets vs. public inputs or functional outputs vs. side channels. Consequently, every verification target must supply an explicit `SecurityDomain Query SemObs` instance declaring `(Pub, Sec, Val, Leak)` and their Cartesian round-trip projections.

## Evidence

All claims and counterexamples in this report are mechanized and kernel-verified in the standalone Lean 4 (`v4.34.1`) file [support/HyperpropertiesBisimulationAndRefinementParadox.lean](support/HyperpropertiesBisimulationAndRefinementParadox.lean) (`2,093` lines, `sha256:6306b827bafa22c324b351b606cf02f35313dedd181c778f723fe65563ee43b2`):

| Theorem / Definition | Lines in `support/HyperpropertiesBisimulationAndRefinementParadox.lean` | Kernel Axioms (`#print axioms`) |
| :--- | :--- | :--- |
| `Language`, `SpecOn`, `VerifiedSpineOn`, `BehaviorCodec`, `Compiles`, `ProductiveCompiles`, `Tool` | [L174-L401](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L174-L401) | `[]` (core definitions & composition lemmas) |
| `theorem1a_one_trace_blind_to_two_safety` (`PENTEST-7`) | [L469-L523](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L469-L523) | `[]` (zero axioms) |
| `pentest_r2_9a_timing_only_diag_certifies_badCipher` (`PENTEST-R2-9A`) | [L589-L604](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L589-L604) | `[]` (zero axioms) |
| `theorem1b_diag_iff_possibilistic_ni_and_leakage_deterministic` | [L650-L695](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L650-L695) | `[]` (zero axioms) |
| `pentest_r2_9b_demonic_diag_locks_out_secret_independent_jitter` (`PENTEST-R2-9B`) | [L721-L754](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L721-L754) | `[]` (zero axioms) |
| `pentest_r3_7_asymmetric_one_way_ni_admits_subset_leak` (`PENTEST-R3-7`) | [L820-L878](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L820-L878) | `[propext]` |
| `symmetry_converts_one_way_to_two_way` | [L882-L896](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L882-L896) | `[]` (zero axioms) |
| `pentest_r3_6_policy_degeneracies` (`PENTEST-R2-9`, `PENTEST-R3-6A/B`) | [L913-L975](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L913-L975) | `[propext]` |
| `pentest_r4_5_positional_tuple_bypasses` (`PENTEST-R4-5A/B`) | [L1031-L1075](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1031-L1075) | `[]` (zero axioms) |
| `SecurityDomain`, `DomainBiNonInterferingOn`, `theorem2b_security_domain_decomposition_characterization` | [L1092-L1192](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1092-L1192) | `[]` (zero axioms) |
| `defense_r4_5_explicit_security_domains_refute_both_leaks` | [L1239-L1260](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1239-L1260) | `[propext]` |
| `theorem3a_mclean_refinement_paradox_counterexample` (`McLean 1994`) | [L1358-L1433](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1358-L1433) | `[propext]` |
| `theorem3b_resolution1_leakage_deterministic_transfer` | [L1474-L1525](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1474-L1525) | `[]` (zero axioms) |
| `LeakageBisimCompiles`, `UniformRefinementCompiles`, `theorem3b_resolution2_leakage_bisim_compiles_and_uniform_refinement` | [L1531-L1661](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1531-L1661) | `[propext]` |
| `theorem4a_nondeterminism_pathology_hierarchy` (`PENTEST-6`, `R2-8A`, `R3-2C`, `R3-9A`) | [L1797-L1878](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1797-L1878) | `[propext, Quot.sound]` |
| `bounded_bitwidth_chaos_excludes_infinitely_many_values` | [L1886-L1890](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1886-L1890) | `[propext, Quot.sound]` |
| `verifiedSpineOn_transfers_across_productiveCompiles` | [L1914-L1938](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1914-L1938) | `[]` (zero axioms) |
| `theorem4b_productive_demonic_spec_refinement_characterization` | [L1954-L2006](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L1954-L2006) | `[propext]` |
| `hyperproperties_bisimulation_mclean_and_lattice_synthesis` | [L2043-L2072](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L2043-L2072) | `[propext]` |

### Primary Literature Citations

- **Back, R.-J., & von Wright, J. (1998).** *Refinement Calculus: A Systematic Introduction*. Graduate Texts in Computer Science, Springer. (Demonic vs. angelic nondeterminism, miracles $\bot$, and chaos $\top$ in predicate transformer lattices.)
- **Barthe, G., D'Argenio, P. R., & Rezk, T. (2004).** "Secure Information Flow by Self-Composition." *Proceedings of the 17th IEEE Computer Security Foundations Workshop (CSFW)*, pp. 100–114. (Reduction of deterministic 2-safety non-interference to 1-trace safety of the self-composed product program $(p, p)$.)
- **Clarkson, M. R., & Schneider, F. B. (2010).** "Hyperproperties." *Journal of Computer Security*, 18(6), pp. 1157–1210. (Formal separation between 1-trace properties and $k$-safety hyperproperties.)
- **Goguen, J. A., & Meseguer, J. (1982).** "Security Policies and Security Models." *Proceedings of the 1982 IEEE Symposium on Security and Privacy*, pp. 11–20. (Foundational formulation of non-interference.)
- **Mantel, H. (2000).** "Possibilistic Definitions of Security — An Assembly Kit." *Proceedings of the 13th IEEE Computer Security Foundations Workshop (CSFW)*, pp. 185–199. (Basic Security Predicates and two-way possibilistic bisimulation.)
- **McLean, J. (1994).** "A General Theory of Composition for Trace Sets Closed Under Selective Interleaving Functions." *Proceedings of the 1994 IEEE Symposium on Research in Security and Privacy*, pp. 79–93. (Discovery of the Refinement Paradox: possibilistic security properties are not preserved under demonic subset refinement.)
- **Roscoe, A. W. (1995).** "CSP and Determinism in Security Modelling." *Proceedings of the 1995 IEEE Symposium on Security and Privacy*, pp. 114–127. (Low-determinism and resolution of refinement anomalies in CSP.)
- **Sabelfeld, A., & Myers, A. C. (2003).** "Language-Based Information-Flow Security." *IEEE Journal on Selected Areas in Communications*, 21(1), pp. 5–19. (PER model of non-interference and possibilistic vs. probabilistic timing channels.)
- **Søndergaard, H., & Sestoft, P. (1992).** "Non-Determinism in Functional Languages." *The Computer Journal*, 35(5), pp. 514–523. (Taxonomy of erratic, demonic, and angelic nondeterminism and plural vs. singular semantics.)
- **Terauchi, T., & Aiken, A. (2005).** "Secure Information Flow as a Safety Problem." *Proceedings of the 12th International Static Analysis Symposium (SAS)*, LNCS 3672, pp. 352–367. (Type-directed self-composition for 2-safety verification.)

## Revalidation

To revalidate the standalone Lean 4 (`v4.34.1`) mechanization from the package directory (`reports/semantic-models-hyperproperties-bisimulation-and-mclean-refinement-paradox-2026/`), run:

```bash
lean -DElab.async=false -Ddebug.skipKernelTC=false support/HyperpropertiesBisimulationAndRefinementParadox.lean
sha256sum support/HyperpropertiesBisimulationAndRefinementParadox.lean
```

Expected verification criteria:
1. The command exits with status `0` and emits zero errors, zero warnings, and zero `sorryAx` occurrences.
2. The `#print axioms` audit at lines [L2074-L2090](support/HyperpropertiesBisimulationAndRefinementParadox.lean#L2074-L2090) confirms that every theorem depends exclusively on `[]`, `[propext]`, or `[propext, Quot.sound]`.
3. The SHA-256 digest of [support/HyperpropertiesBisimulationAndRefinementParadox.lean](support/HyperpropertiesBisimulationAndRefinementParadox.lean) matches `6306b827bafa22c324b351b606cf02f35313dedd181c778f723fe65563ee43b2`.
