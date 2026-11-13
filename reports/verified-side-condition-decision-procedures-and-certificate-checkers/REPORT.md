# Verified Decision Procedures and Certificate Checkers for Compiler Side Conditions

## Summary

Light-witness expanders in a proof-producing Rust compiler must discharge four
recurring classes of side conditions—**bit-vector arithmetic and masks
(`BitVec 64`), linear bounds and index scaling (`Nat` / `Int`), 64-bit memory
interval disjointness (`[b1, b1+n1) ∩ [b2, b2+n2) = ∅`), and bit-exact IEEE-754
floating-point identities (`Float32Bits` / `Float64Bits`)**—while strictly
respecting Anneal's `TrustedBoundary` axiom policy (`propext`,
`Classical.choice`, and `Quot.sound` only; **`Lean.ofReduceBool` /
`native_decide` is forbidden**). Combining our corpus-wide solver/certificate
baselines with new kernel proof-term DAG measurements in Lean `v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`, `support/SideConditionBench.lean`)
establishes the exact decision-procedure selection table and measured costs:

1. **Bit-Vector Peepholes & Masks (`bv_normalize` vs. `bv_decide` Stage 2):**
   - `Std.Tactic.BVDecide.bv_normalize` (Stage 1 `Sym.Simp` AC/bitmask
     rewriter) closes mask idempotence (`0xff#64 &&& (0xff#64 &&& x) = 0xff#64 &&& x`)
     with **`42` `Expr` DAG nodes**, **`0` auxiliary theorems**, and **only
     `[propext, Quot.sound]`** (`bv64_mask_idempotent_bv_normalize`).
   - By contrast, whenever `bv_decide` enters **Stage 2 (CaDiCaL + LRAT
     reflection)**, it invokes `Lean.ofReduceBool` (`_native.bv_decide.ax`),
     which is **rejected by `TrustedBoundary.lean`**. To check propositional or
     bit-blasted UNSAT certificates without `Lean.ofReduceBool`, the expander
     must apply a **kernel-reducible boolean checker theorem** (`checkUnitConflict_sound`
     by `rfl`, which depends only on `[propext]`) or rewrite to `BitVec.toNat`
     algebraic lemmas.
2. **Wrapping 64-Bit Range & Overflow Bounds (`bv64_add_range_algebraic` vs.
   `bv_omega`):**
   - Discharging `lo1 + lo2 ≤ (x + y).toNat ∧ (x + y).toNat ≤ hi1 + hi2` (under
     `hi1 + hi2 < 2^64`) with raw `bv_omega` expands three `% 2^64` Euclidean
     division case splits, generating **`8,416` `Expr` DAG nodes**, **`48.1 ms`
     kernel checking time**, and `288.2 ms` elaboration time.
   - Pre-eliminating the modulo via `Nat.mod_eq_of_lt (by omega)` followed by
     `omega` (`bv64_add_range_mod_elim`) cuts the proof term to **`2,605` DAG
     nodes (`3.2x` smaller)**.
   - Replacing `omega` entirely with a parameterized **schematic algebraic
     theorem (`bv64_add_range_algebraic`)** using `Nat.add_le_add` and
     `Nat.mod_eq_of_lt` reduces the proof term to **`230` DAG nodes (`36.6x`
     smaller than `bv_omega`)**, requires **only `[propext]`** (not even
     `Classical.choice` or `Quot.sound`), and replays in **`< 1 ms` (`0.78 ms`,
     `61.7x` faster)**.
3. **Linear Index Arithmetic (`omega`, `grind`, and Reflected Farkas
   `checkFarkas2_sound`):**
   - For GEP multi-dimensional slice bounds (`gep_slice_offset_bound_omega`),
     `omega` generates **`990` DAG nodes**; for congruence + offset transitivity
     (`f a + 8 < c` from `a = b` and `f b + 16 ≤ c`), `grind` generates **`454`
     DAG nodes** (`gep_congruence_offset_grind`).
   - When an untrusted pass emits explicit non-negative Farkas multipliers
     $(w_1, w_2)$, the reflected checker lemma `checkFarkas2_sound` requires only
     **`52` DAG nodes** and **zero axioms**!
4. **64-Bit Memory Range Disjointness (`checkDisjoint64_sound`) and Bit-Exact
   IEEE-754 (`Float32Bits`):**
   - Our overflow-guarded boolean checker `checkDisjoint64 base1 len1 base2 len2`
     (`checkDisjoint64_sound`: **`5,771` one-time library DAG nodes**, **`74`
     per-callsite DAG nodes** via `rfl` in `stack_slots_disjoint_example`)
     discharges concrete stack-slot and constant-offset alias obligations in
     $O(1)$ kernel reduction using only `[propext, Quot.sound]`.
   - For IEEE-754 floating-point optimizations, bitwise sign-manipulation rules
     (`f32_neg_involutive`, `f32_abs_idem`) hold unconditionally over `BitVec 32`
     (`Float32Bits`), whereas `feq x x = true` is falsified by `qNaN32`
     (`f32_qnan_feq_irrefl : feq qNaN32 qNaN32 = false`) and requires an explicit
     non-NaN side condition (`f32_feq_refl_of_not_nan`).

## Applicability

This report extends `lean-bitvec-proof-term-scaling-bv-omega-bv-decide-and-meta-fvar-caching`,
`smt-sat-alethe-carcara-and-numerical-proof-certificate-reconstruction`,
`lean-tactic-extensions-simp-omega-and-grind`, and
`anneal-solvers-decision-procedures-and-certificates-survey`. All kernel DAG
node counts, axiom footprints, and tactic comparisons in
`support/SideConditionBench.lean` were measured on Lean `v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`) on `x86_64-unknown-linux-gnu` and
comply with `joshlf/anneal`'s `TrustedBoundary.lean` (`af3c1e99c0a7410aa63522fc3888d34c32c13175`).

## Findings

### 1. Measured Cost and Axiom Footprint across Lean 4.34.1 Side-Condition Procedures

Basis: execution of `support/SideConditionBench.lean` and `MeasureSideConditions.lean`
under Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).

| Side-Condition Class & Obligation | Discharging Procedure / Tactic | Kernel `Expr` DAG Nodes (Root / With Aux) | Kernel Axiom Footprint (`#print axioms`) | `TrustedBoundary` Compliant? | Measured Cost & Scaling Profile |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **1A. Bit-Vector Mask Idempotence** (`0xff#64 &&& (0xff#64 &&& x) = 0xff#64 &&& x`) | `bv_normalize` (Stage 1 `Sym.Simp` rewriter) | **`42` / `42`** | `[propext, Quot.sound]` | **Yes** | `<2 ms` elaboration, `<0.5 ms` kernel check; zero SAT/LRAT invocation |
| **1B. Bit-Vector Alignment Mask Equivalence** (`~~~(align - 1#64) = 0#64 - align`) | `BitVec.eq_of_toNat_eq` + `simp` + `omega` | **`1,093` / `1,301`** | `[propext, Classical.choice, Quot.sound]` | **Yes** | `~12 ms` elaboration; handles symbolic `align : BitVec 64` without bit-blasting |
| **1C. 64-Bit Wrapping Add Range Propagation** (`lo1+lo2 ≤ (x+y).toNat ≤ hi1+hi2`) | Raw `bv_omega` (`MeasureSideConditions.lean`) | **`8,416` / `8,416`** | `[propext, Classical.choice, Quot.sound]` | **Yes** | `288.2 ms` elab, **`48.1 ms` kernel check** (`3x` Euclidean `% 2^64` splits) |
| **1C'. 64-Bit Wrapping Add Range Propagation** (modulo pre-eliminated) | `rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega` (`bv64_add_range_mod_elim`) | **`2,605` / `2,605`** | `[propext, Classical.choice, Quot.sound]` | **Yes** | **`3.23x` smaller DAG** than raw `bv_omega` by eliminating `% 2^64` before `omega` |
| **1D. 64-Bit Wrapping Add Range Propagation** (schematic algebraic lemma) | `Nat.add_le_add` + `Nat.mod_eq_of_lt` (`bv64_add_range_algebraic`) | **`230` / `230`** | **`[propext]` only** | **Yes** | **`36.6x` smaller DAG**, **`0.78 ms` kernel check (`61.7x` faster)** than `bv_omega` |
| **1E. Bit-Blasted Symbolic Bit-Vector Identity** | `bv_decide` Stage 2 (CaDiCaL + LRAT `ofReduceBool`) | Small wrapper + `_native.bv_decide.ax` | Includes **`Lean.ofReduceBool` (`_native`)** | **NO (Rejected)** | Bypasses kernel reduction via compiled C/LLVM evaluator; forbidden in `theory/` |
| **2A. GEP Multi-Dimensional Slice Bound** (`base + idx*8 + 8 ≤ base + len*8`) | `subst` + `omega` (`gep_slice_offset_bound_omega`) | **`990` / `990`** | `[propext, Classical.choice, Quot.sound]` | **Yes** | `<10 ms` elaboration, `<3 ms` kernel check |
| **2B. Congruence + Linear Offset Transitivity** (`a = b → f b + 16 ≤ c → f a + 8 < c`) | `grind` (`gep_congruence_offset_grind`) | **`356` / `454`** | `[propext, Classical.choice, Quot.sound]` | **Yes** | Combines E-graph congruence closure with cutsat/offset linear arithmetic |
| **2C. Linear Inequality Combination** (`w1*a1 + w2*a2 ≤ w1*b1 + w2*b2`) | Schematic Farkas lemma (`checkFarkas2_sound`) | **`52` / `52`** | **`[]` (Zero axioms!)** | **Yes** | $O(1)$ kernel application when compiler certificate supplies Farkas weights $(w_1, w_2)$ |
| **3A. 64-Bit Interval Disjointness Library Theorem** (`checkDisjoint64_sound`) | `decide_eq_true_eq` + `omega` (proved once in library) | `5,771` / `5,771` (one-time library cost) | `[propext, Quot.sound]` | **Yes** | Proved once in expander library; amortizes across all compilations |
| **3B. Concrete Stack-Slot Disjointness Instance** (`[32, 40) ∩ [40, 56) = ∅`) | `checkDisjoint64_sound 32 8 40 16 rfl` (`stack_slots_disjoint_example`) | **`74` / `74`** (per callsite!) | `[propext, Quot.sound]` | **Yes** | **`<0.2 ms` kernel check** via GMP `Nat` reduction in `rfl` |
| **4A. Propositional UNSAT Certificate Instance** (`sample_cnf_unsat`) | `checkUnitConflict_sound ... rfl` | **`<100`** (per callsite) | **`[propext]` only** | **Yes** | Pure kernel-reducible boolean reflection (`rfl`), zero `Lean.ofReduceBool` |
| **4B. IEEE-754 `Float32Bits` Sign Laws & NaN Guard** (`f32_neg_involutive`, `f32_feq_refl_of_not_nan`) | `BitVec.xor_assoc` / `BitVec.and_assoc` / `simp` | **`<150`** | `[propext, Quot.sound]` | **Yes** | Exact bit-level IEEE-754 verification without hardware float axiomatization |

### 2. Why Schematic Algebraic Lemmas and Kernel-Reducible Checkers Beat Raw Tactic Reconstruction for Light-Witness Expanders

Basis: execution (`support/SideConditionBench.lean`, lines 42–205) +
`lean-bitvec-proof-term-scaling-bv-omega-bv-decide-and-meta-fvar-caching`.

When a compiler pass emits thousands of side conditions across a crate (such as
non-wrapping GEP offset bounds, range propagation through `nuw`/`nsw` arithmetic,
and stack-slot disjointness), invoking general-purpose elaborator tactics
(`bv_omega`, `omega`, `grind`) at every obligation site has two compounding
costs:

1. **Euclidean Modulo Case-Split Explosion in `bv_omega`:**
   Because `BitVec.toNat (x + y)` is defined as `(x.toNat + y.toNat) % 2^64`,
   `zify`/`omega` introduces an auxiliary quotient variable $q$ and splits on
   wraparound regimes for every bit-vector operation. Even on a two-variable
   addition (`bv64_add_range_bv_omega`), this emits **`8,416` DAG nodes** (`48.1 ms`
   kernel check). By contrast, when the compiler's range analysis already knows
   `hi1.toNat + hi2.toNat < 2^64`, applying the 4-line schematic theorem
   `bv64_add_range_algebraic` (`support/SideConditionBench.lean`, lines 66–74)
   discharges the obligation in **`230` DAG nodes (`36.6x` smaller)** and
   **`0.78 ms` (`61.7x` faster)**.
2. **One-Time Soundness Theorem + Per-Site `rfl` (`checkDisjoint64_sound` and
   `checkUnitConflict_sound`):**
   Proving `checkDisjoint64_sound` once in the expander support library costs
   `5,771` DAG nodes. Every subsequent stack-slot or constant-range disjointness
   obligation in a compiled function (`stack_slots_disjoint_example`) simply
   invokes `checkDisjoint64_sound b1 n1 b2 n2 rfl`, costing only **`74` DAG
   nodes** at the callsite and evaluating in microseconds via Lean's kernel
   reducer (`decide` / `rfl` with GMP-backed `Nat` arithmetic).

### 3. SMT Certificate Reconstruction (`Alethe` / `Carcara` / `lean-smt`) vs. Specialized Reflected Checkers

Basis: corpus baseline `smt-sat-alethe-carcara-and-numerical-proof-certificate-reconstruction`
(`cvc5` `1.4.2` @ `282d5e0c84ba`, `Carcara` `1.1.0` @ `20bf49c5ce31`,
`ufmg-smite/lean-smt` @ `9abdd01c13dc`) + `anneal-solvers-decision-procedures-and-certificates-survey`.

When a side condition falls outside fixed schematic lemmas and requires general
combinations of Uninterpreted Functions (`UF`), Linear Integer Arithmetic
(`LIA`), Arrays (`ArraysEx`), and Bit-Vectors (`BV`), two certificate paths
exist:

1. **Alethe Proof Certificates (`cvc5 --produce-proofs --proof-format-mode=alethe`):**
   - **External Fast Verification (`Carcara 1.1.0`):** Checks Alethe proofs in
     `10%–40%` of `cvc5` solve time across `QF_UF`, `QF_LIA`, and `QF_BV`, useful
     as a fast pre-check before kernel reconstruction.
   - **In-Kernel Lean 4 Reconstruction (`lean-smt`):** Translates Alethe steps
     (`resolution`, `cong`, `la_generic`, `lia_generic`, bit-blasting) into native
     Lean 4 proof terms (`94%–98%` reconstruction success on SMT-LIB benchmarks).
     However, `la_generic` and `lia_generic` steps invoke `omega` / Micromega-style
     linear combinations during elaboration. As shown in Finding 1, emitting the
     Farkas multipliers directly into a reflected checker (`checkFarkas2_sound`,
     `52` DAG nodes) avoids re-running Fourier-Motzkin elimination during proof
     checking.
2. **Bit-Exact IEEE-754 Floating-Point Side Conditions (`Float32Bits` /
   `Float64Bits`):**
   - Lean 4's built-in `Float` type is backed by C `double` in the VM and opaque
     axioms in the kernel, so `Float` cannot be used for foundational compiler
     proofs.
   - Instead, compiler side conditions for IEEE-754 optimizations must be stated
     over explicit bit-vector structures (`Float32Bits` over `BitVec 32` in
     `support/SideConditionBench.lean`, lines 210–254, or Flocq/Fp-Lean IEEE-754
     formats):
     - **Bitwise sign operations (`fneg`, `fabs`, `copysign`)** are unconditionally
       sound over all bit-patterns including NaNs (`f32_neg_involutive`,
       `f32_abs_idem`).
     - **Algebraic and comparison rewrites (`x == x -> true`, `x + 0.0 -> x`,
       `x - x -> 0.0`)** are **invalid** on unrestricted `Float32Bits` (`f32_qnan_feq_irrefl`
       proves `feq qNaN32 qNaN32 = false` by `rfl`) and are sound *only* when
       guarded by an explicit fast-math flag (`nnan`, `nsz`) or a proven range
       bound `x.isNaN = false` (`f32_feq_refl_of_not_nan`).

### 4. Decision-Procedure Routing Matrix for Light-Witness Expanders

Basis: derived from Findings 1–3.

| Compiler Side-Condition Obligation | Primary Light-Witness Expander Procedure | Fallback / Heavy Procedure | Certificate Payload Emitted by Compiler Pass |
| :--- | :--- | :--- | :--- |
| **Bitwise masks, shifts, & AC identities** (`&&&`, `\|\|\|`, `^^^`, `<<<`, `>>>`) | `bv_normalize` (or reflected rewrite trace `checkDirectedRefinementTrace_sound`) | Kernel-reducible LRAT checker (`checkUnitConflict_sound` / `rfl`, never `Lean.ofReduceBool`) | Rule ID + subterm path (or LRAT clause-ID chain) |
| **Wrapping / `nuw` / `nsw` integer range & overflow bounds** | Schematic algebraic lemmas (`bv64_add_range_algebraic` with `Nat.mod_eq_of_lt`) | `rw [Nat.mod_eq_of_lt]; omega` (`bv64_add_range_mod_elim`, `3.2x` smaller than `bv_omega`) | Proven interval bounds `[lo, hi]` per SSA value + non-overflow witness |
| **Affine loop-index, GEP offset, & slice bounds** | Reflected Farkas combination (`checkFarkas2_sound`) | `omega` (`990` DAG nodes) or `grind` (`454` DAG nodes when UF congruence is mixed with offsets) | Non-negative Farkas multiplier vector $\vec{w} \in \mathbb{N}^k$ |
| **64-bit pointer / stack-slot interval disjointness** | `checkDisjoint64_sound b1 n1 b2 n2 rfl` (`74` DAG nodes) | `omega` over symbolic `base + offset` expressions | Concrete or symbolic `(base, len)` pairs + separation orientation bit (`left_before_right : Bool`) |
| **IEEE-754 floating-point rewrites** | Bit-level `Float32Bits`/`Float64Bits` lemmas (`f32_neg_involutive`, `f32_abs_idem`, `f32_feq_refl_of_not_nan`) | Interval/rounding certifiers (FloVer / Gappa / VCFloat2) if fast-math error bounds are requested | Non-NaN / non-negative-zero predicate witness (`isNaN = false`) |

## Boundaries

- **Why `bv_decide` Stage 2 (`Lean.ofReduceBool`) Cannot Be Used Directly in
  `theory/`:** `Std.Tactic.BVDecide.bv_decide` delegates Stage 2 LRAT checking
  to compiled native code via `Lean.reduceBool` (`Lean.ofReduceBool`), which
  introduces the axiom `_native.bv_decide.ax` (and `Lean.trustCompiler`).
  Anneal's `trusted/audit/TrustedBoundary.lean` rejects any theorem whose
  transitive axiom cone contains `Lean.ofReduceBool`. Therefore, only Stage 1
  (`bv_normalize`) or kernel-reduced (`rfl` / `decide`) certificate checkers are
  admissible inside `theory/`.
- **Non-Linear Bit-Vector Multiplication and Division (`mul`, `udiv`, `urem`):**
  Neither `omega` nor `grind` decides non-linear symbolic multiplication
  $x \times y$ or variable-divisor remainder $x \bmod y$. When one operand is a
  known constant or power of two, shift/add strength reduction (`bv64_mul_four_eq_shl_two`)
  reduces the obligation to linear arithmetic; for general symbolic `mul`/`udiv`,
  the compiler pass must apply pre-proved algebraic monotonicity/distributivity
  lemmas rather than bit-blasting 64-bit multipliers (which exceed tractable
  CDCL/LRAT sizes).

## Evidence

- **Standalone Lean 4.34.1 Benchmark & Mechanization:**
  `support/SideConditionBench.lean` (`276` lines, zero `sorry`, verified on Lean
  `v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52` with `#guard_msgs in #print axioms`)
  mechanizes and checks:
  - Class 1 (`BitVec 64`): `bv64_mask_idempotent_bv_normalize`,
    `bv64_align_mask_equiv`, `bv64_add_range_mod_elim`, and
    `bv64_add_range_algebraic` (lines 42–75),
  - Class 2 (`Nat` / `Int` / Farkas): `gep_slice_offset_bound_omega`,
    `gep_congruence_offset_grind`, and `checkFarkas2_sound` (lines 80–104),
  - Class 3 (`UInt64` Disjointness): `checkDisjoint64`, `checkDisjoint64_sound`,
    and `stack_slots_disjoint_example` (lines 111–136),
  - Class 4A (Kernel-reducible RUP/LRAT): `checkUnitConflict`,
    `checkUnitConflict_sound`, and `sample_cnf_unsat` (lines 140–205),
  - Class 4B (Bit-exact IEEE-754 `Float32Bits`): `f32_neg_involutive`,
    `f32_abs_idem`, `f32_qnan_feq_irrefl`, and `f32_feq_refl_of_not_nan` (lines
    210–254).
- **Primary Upstream Repositories:**
  - `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`,
    `Std.Tactic.BVDecide`, `omega`, `grind`).
  - `joshlf/anneal` at `af3c1e99c0a7410aa63522fc3888d34c32c13175` and
    `24367bd1a8c784f2578535954f9915e24894a56f` (`TrustedBoundary.lean`).
  - `ufmg-smite/carcara` at `20bf49c5ce31089ac83118574c888669355aaae1` and
    `ufmg-smite/lean-smt` at `9abdd01c13dc7ac2bac4d68d17ee661c63ed0894`.
  - `CakeML/cake_lpr` (Tan, Heule, & Myreen, TACAS 2021
    `doi:10.1007/978-3-030-72013-1_14`).

## Revalidation

Run the standalone Lean `v4.34.1` side-condition suite via `anneal-lean-run` to
verify all theorems and their `#guard_msgs in #print axioms` footprints:

```bash
anneal-lean-run --mode file --concurrency 4 -- \
  lake env lean reports/verified-side-condition-decision-procedures-and-certificate-checkers/support/SideConditionBench.lean
```
