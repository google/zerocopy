# Bidirectional `Runtime(PostCleanup)` MIR ↔ `MiniSSA` Refinement and Backward VC Transport via `HybridTrace`

Created: 2026-11-14
Updated: 2026-11-14

## Summary

Using the verified compiler's `Runtime(PostCleanup) MIR → Canonical MiniSSA` canonicalizer (`Mem2Reg + SROA + CopyProp + ConstProp + SimplifyCFG + Inlining`) simultaneously as (1) the first link of forward compilation to machine code and (2) **Anneal's verification normalizer**—transporting functional correctness proofs discharged on canonical `MiniSSA` backward to `Trusted.VerificationResult` on `Runtime(PostCleanup)` MIR without expanding `trusted/lean/`—requires resolving a fundamental **directionality inversion** at the `MIR ↔ MiniSSA` boundary. By mechanizing the two-mode `HybridTrace` normalization checker `checkNormBisim` and bridge theorems in Lean `v4.34.1` ([`support/BidirectionalMirMiniSsaTransportProbe.lean`](support/BidirectionalMirMiniSsaTransportProbe.lean), `695` lines, checked in `3.89` seconds with **`0` `sorryAx`**, **`0` `Lean.ofReduceBool`**, and **`0` additions to `Trusted`**), we establish four governing architectural findings:

1. **The Directionality Inversion Between Forward Compilation and Backward VC Transport:**
   - **Forward compilation (`MiniSSA ⊑ MIR`)** requires **demonic safe-source refinement** (`forwardRefines`): whenever the `Runtime(PostCleanup)` MIR execution is UB-free (`evalMirFuel ≠ .ub`), the `MiniSSA` execution produces the same observable outcome. An optimization pass may freely *erase* source-level MIR Undefined Behavior (turning `.ub` into a defined return value).
   - **Backward Anneal VC transport (`WP_MiniSSA ⟹ WP_MIR`)** requires the converse **safety-reflecting backward simulation** (`checkNormBisim_backward_reflects_safety`): proving that canonical `MiniSSA` terminates safely in $k_{\text{ssa}}$ steps and satisfies postcondition $Q$ under precondition $P$ must guarantee that the original `Runtime(PostCleanup)` MIR program **never triggers a MIR-only UB or trap that `MiniSSA` erased**, and terminates in $k_{\text{mir}} \le c_1 \cdot k_{\text{ssa}} + c_2$ steps satisfying $Q$.
2. **Three-Tier `HybridTrace` Rule Stratification (`BisimExact` vs. `GuardedBisim` vs. `RefinesOnly`):**
   - Cataloging all 12 normalization rule families ([`support/hybrid_trace_bisim_rule_catalog.json`](support/hybrid_trace_bisim_rule_catalog.json)) proves that naive compiler passes (`RefinesOnly`) break Anneal soundness along five concrete vectors:
     1. Eliminating a dead load from an uninitialized, dead, or out-of-bounds `Place` (`refinesOnly_deadUninitLoad_unsound_for_vc_transport`);
     2. Scalarizing (`SROA`) an aggregate copy whose source violated field/niche validity or copied invalid unvalidated bytes (`refinesOnly_sroaBadPadding_unsound_for_vc_transport`);
     3. Eliding a `StorageLive`/`StorageDead` + `&mut` reborrow chain when an aliased raw-pointer access conflicted with the Tree Borrows retag (`refinesOnly_aliasedReborrow_unsound_for_vc_transport`);
     4. Removing `StorageDead(s)` while a dangling raw pointer `&raw const s` is dereferenced later in the function (`NORM-12`); and
     5. Eliminating a dead `Div`/`Rem` or checked operation without proving `denom ≠ 0` (`NORM-11`).
   - Equipping `HybridTrace` certificates with explicit side-condition guards $\Phi_{\text{no-erased-UB}}$ (`GuardedBisim`: definite initialization dominance for `Mem2Reg`, field validity for `SROA`, non-escaping borrow non-interference for `elideStorageReborrow`, and `slotInitAndLive` for dead-load elimination) upgrades the normalization pass to a **bidirectional safety-preserving bisimulation**. A single `checkNormBisim mir ssa cert = true` certificate simultaneously yields forward compilation refinement (`checkNormBisim_forward_refines`) and backward Anneal VC transport (`verifyMirViaMiniSSA_sound`).
3. **Zero-TCB-Expansion Architecture (`trusted/lean/` vs. `theory/`):**
   - Because `MiniSsaProg`, `evalMiniSsaFuel`, `NormCert`, `synthNormEndpoints`, `checkNormBisim`, and `verifyMirViaMiniSSA_sound` reside entirely in the `Theory` namespace (`theory/Anneal/`), `trusted/audit/` (`TrustedBoundary.lean`) inspects the exact same `Trusted.VerificationResult` statement over `Runtime(PostCleanup)` MIR. Inside `Proof/<Crate>/<Item>.lean`, the proof applies `verifyMirViaMiniSSA_sound` to `rfl` (discharging `checkNormBisim mir ssa cert = true` via endpoint synthesis `synthNormEndpoints`) and a concise proof over pure register-only `MiniSSA`.
4. **Exact Affine Fuel Preservation Across `Mem2Reg`, `SROA`, `SimplifyCFG`, and `Inlining`:**
   - Every `NormCert` constructor computes a static administrative fuel slack `certFuelSlack cert` (`+0` for `assignConst`/`assignAdd`/`copyReg`/`sroaSplitCopy`/`checkDiv`, `+1` for `simplifyGoto`, `+1` for `inlineHelperAdd`, `+2` for `elideStorageReborrow`, `+3` for `mem2RegField0`), proving $k_{\text{mir}} \le k_{\text{ssa}} + \text{certFuelSlack}(\text{cert})$ in `verifyStatefulMirViaMiniSSA_sound`.

## Applicability

- **Extends:** `end-to-end-verified-mir-to-isa-refinement-chain-and-seams`, `observable-behavior-property-transfer-and-anneal-statement-forms`, `lean-derivation-checker-soundness-and-completeness-prototype`, `anneal-behavior-codec-and-partial-compile-refinement-algebra`
- **Subjects:**
  - **Lean 4 (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`)**: Kernel typechecker and `Init` prelude (`-DElab.async=false -Ddebug.skipKernelTC=false`).
  - **Anneal (`joshlf/anneal@9027a6c9c5c363ee8fb74c2efc1c0481eaf188bc`)**: `Trusted.CrateTheorem`, `Trusted.VerificationResult`, `trusted/audit/TrustedBoundary.lean`, and `theory/Anneal/` refinement architecture.
  - **Rust Compiler (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`, `1.99.1`)**: `Runtime(PostCleanup)` MIR operational semantics (`StorageLive`, `StorageDead`, `Place` projections, `Rvalue::Ref`, and aggregate copies).

## Findings

### 1. Mathematical Formulation of the Bidirectional `MIR ↔ MiniSSA` Seam

`Basis: derived + execution (support/BidirectionalMirMiniSsaTransportProbe.lean)`

Let $\llbracket p_{\text{mir}} \rrbracket_{\text{MIR}}(k, \sigma) \in \{\texttt{returned}(v, k_{\text{used}}), \texttt{panic}(c), \texttt{ub}, \texttt{outOfFuel}\}$ denote fuel-indexed evaluation of a `Runtime(PostCleanup)` MIR body (`Trusted.evalMirFuel`), and let $\llbracket p_{\text{ssa}} \rrbracket_{\text{SSA}}(k, \sigma)$ denote evaluation of its canonical `MiniSSA` form (`Theory.evalMiniSsaFuel`).

1. **Forward Compilation Requirement (Target Refines Safe Source):**
   To compile `Runtime(PostCleanup)` MIR through `MiniSSA` to `MiniMach` and Tier 1 assembly, the compiler requires:
   $$\forall \sigma, k_{\text{mir}}, k_{\text{ssa}}.\; \llbracket p_{\text{mir}} \rrbracket_{\text{MIR}}(k_{\text{mir}}, \sigma) \notin \{\texttt{ub}, \texttt{outOfFuel}\} \implies \llbracket p_{\text{ssa}} \rrbracket_{\text{SSA}}(k_{\text{ssa}}, \sigma) =_{\text{obs}} \llbracket p_{\text{mir}} \rrbracket_{\text{MIR}}(k_{\text{mir}}, \sigma)$$
   Under this implication, if $\llbracket p_{\text{mir}} \rrbracket_{\text{MIR}}(k_{\text{mir}}, \sigma) = \texttt{ub}$, the implication holds vacuously even when $\llbracket p_{\text{ssa}} \rrbracket_{\text{SSA}}(k_{\text{ssa}}, \sigma) = \texttt{returned}(42, 2)$.
2. **Backward Anneal VC Transport Requirement (Target Safety Reflects Source Safety):**
   In Anneal, the user or proof agent discharges `VerificationResult p_mir Pre Post`, which requires proving that for every $\sigma$ satisfying $\text{Pre}(\sigma)$, $\llbracket p_{\text{mir}} \rrbracket_{\text{MIR}}$ **does not** hit $\texttt{ub}$ or $\texttt{panic}$ and instead returns $v$ satisfying $\text{Post}(\sigma, v)$. To discharge this obligation by proving $\text{Pre}(\sigma) \implies \llbracket p_{\text{ssa}} \rrbracket_{\text{SSA}}(k_{\text{ssa}}, \sigma) = \texttt{returned}(v, k_{\text{used}}) \wedge \text{Post}(\sigma, v)$ on canonical `MiniSSA`, the normalization certificate `cert` must establish the **reverse implication**:
   $$\llbracket p_{\text{ssa}} \rrbracket_{\text{SSA}}(k_{\text{ssa}}, \sigma) = \texttt{returned}(v, k_{\text{used}}) \wedge \texttt{checkNormBisim}(p_{\text{mir}}, p_{\text{ssa}}, \text{cert}) = \texttt{true} \implies \exists k_{\text{mir}} \le k_{\text{used}} + \Delta(\text{cert}),\; \llbracket p_{\text{mir}} \rrbracket_{\text{MIR}}(k_{\text{ssa}} + \Delta(\text{cert}), \sigma) = \texttt{returned}(v, k_{\text{mir}})$$

---

### 2. Classification of `HybridTrace` Normalization Rules (`BisimExact`, `GuardedBisim`, `RefinesOnly`)

`Basis: source + execution (support/hybrid_trace_bisim_rule_catalog.json, support/BidirectionalMirMiniSsaTransportProbe.lean)`

Table 1 classifies all 12 `Runtime(PostCleanup) MIR → Canonical MiniSSA` transformation families across the three modes:

| Rule ID | Transformation Rule | `RuleMode` | Forward Compilation (`MiniSSA ⊑ MIR`) | Backward Anneal VC Transport (`Safe(MiniSSA) ⟹ Safe(MIR)`) | Required Guard $\Phi_{\text{no-erased-UB}}$ Checked by `checkNormBisim` | Fuel Slack $\Delta(\text{rule})$ |
| :--- | :--- | :---: | :---: | :---: | :--- | :---: |
| **`NORM-01`** | `CopyProp_MoveCopyReg` (`dst = copy/move src`) | `BisimExact` | **Yes** | **Yes** | `src` is a live initialized SSA/MIR local | `+0` |
| **`NORM-02`** | `ConstProp_ScalarAndPair` (`dst = const c`) | `BisimExact` | **Yes** | **Yes** | `c` evaluated at `RequiredConsts` capture time | `+0` |
| **`NORM-03`** | `SimplifyCfg_GotoChainCollapse` (`goto -> bb_next`) | `BisimExact` | **Yes** | **Yes** | Single-predecessor block merge or edge jump | `+1` per collapsed `goto` |
| **`NORM-04`** | `Mem2Reg_NonEscapingSlot` (`StorageLive; StoreField; LoadField; StorageDead`) | `GuardedBisim` | **Yes** | **Yes** | Slot `s` has no address-taken escape (`&raw` / escaping `&s`) and every load is dominated by a store after `StorageLive(s)` | `+3` (`StorageLive` + `Store` + `StorageDead`) |
| **`NORM-05`** | `SROA_ScalarizeAggregateCopy` (`dst_agg = copy src_agg`) | `GuardedBisim` | **Yes** | **Yes** | `paddingValid = true`: aggregate has no unvalidated niche/discriminant trap and all fields satisfy `validValue` | `+0` (`1` MIR step $\leftrightarrow$ `1` `copyPair` step) |
| **`NORM-06`** | `ElideShortLivedReborrow_SliceSubslice` (`&(*s)[off..]`) | `GuardedBisim` | **Yes** | **Yes** | `noConflict = true`: temporary borrow local `s` does not conflict with any raw-pointer access between `StorageLive(s)` and `StorageDead(s)` | `+2` (`StorageLive` + `StorageDead`) |
| **`NORM-07`** | `InlineNonRecursiveCallee` (`Call(f, args) -> bb_ret`) | `GuardedBisim` | **Yes** | **Yes** | Callee resolved, `target_features` compatible, and entry parameter validity (`noundef`, `align`) preserved | `+1` (call/return framing overhead) |
| **`NORM-08`** | `CheckDivRem_Preserved` (`Assert(d != 0); Div(n, d)`) | `BisimExact` | **Yes** | **Yes** | Explicit zero-divisor and `INT_MIN / -1` checks retained identically | `+0` |
| **`NORM-09`** | `DeadLoadElim_Guarded` (unused load of valid place) | `GuardedBisim` | **Yes** | **Yes** | `slotInitAndLive = true`: place is statically live, aligned, dereferenceable, and initialized | `+1` |
| **`NORM-10`** | `DeadLoadElim_Unguarded` (unused load of possibly uninit/OOB place) | `RefinesOnly` | **Yes** | **No (Rejected)** | Rejected (`checkNormBisim = false`); proved unsound by `refinesOnly_deadUninitLoad_unsound_for_vc_transport` | `+1` |
| **`NORM-11`** | `DeadDivRemElim_Unguarded` (unused `n / d` without `d != 0`) | `RefinesOnly` | **Yes** | **No (Rejected)** | Rejected (`checkNormBisim = false`); erasing dead `1 / 0` masks source panic/UB | `+1` |
| **`NORM-12`** | `RemoveStorageMarkers_WithDanglingRawPtr` (`StorageDead(s)` with escaping `&raw const s`) | `RefinesOnly` | **Yes** | **No (Rejected)** | Rejected (`checkNormBisim = false`) whenever `s` has an address-taken raw pointer live across `StorageDead(s)` | `+1` |

---

### 3. Lean 4.34.1 Mechanization of `checkNormBisim`, Counterexamples, and the Three Verified Fixtures

`Basis: execution (support/BidirectionalMirMiniSsaTransportProbe.lean, support/audit_output.json)`

In [`support/BidirectionalMirMiniSsaTransportProbe.lean`](support/BidirectionalMirMiniSsaTransportProbe.lean), `checkNormBisim` uses total endpoint synthesis (`synthNormEndpoints : NormCert → Option (MirProg × MiniSsaProg)`) so that checking a certificate in a user proof reduces by kernel `rfl` (`decide (synthNormEndpoints cert = some (mir, ssa)) = true`) without quadratic case-splitting:

```lean
theorem verifyMirViaMiniSSA_sound
    (mir : MirProg) (ssa : MiniSsaProg) (cert : NormCert)
    (pre : MirState → Prop) (post : MirState → Nat → Prop)
    (hCheck : checkNormBisim mir ssa cert = true)
    (hSsaVerified : ∀ st : MirState, pre st →
      ∃ (fuel : Nat) (ret : Nat) (kSsa : Nat),
        evalMiniSsaFuel fuel st ssa = .returned ret kSsa ∧ post st ret) :
    Trusted.VerificationResult mir pre post
```

A crucial structural lemma enabling linear-time proof transport across `Mem2Reg` (`mem2RegField0`) and `StorageLive`/`StorageDead` elision (`elideStorageReborrow`) is **register-state frame isolation** (`evalMiniSsaFuel_slots_irrel`): because `MiniSSA` instructions never read `st.slots`, mutating stack slot liveness and field storage in `Runtime(PostCleanup)` MIR leaves the continuation's `MiniSSA` evaluation strictly identical (`rw [← hFrame, hSub]`).

Table 2 summarizes all nine kernel-checked theorems and fixtures in `BidirectionalMirMiniSsaTransportProbe.lean`:

| Theorem Name | Category | MIR Steps ($k_{\text{mir}}$) | `MiniSSA` Steps ($k_{\text{ssa}}$) | Fuel Slack $\Delta(\text{cert})$ | Kernel Axioms (`#print axioms`) | `Trusted/` Additions |
| :--- | :--- | :---: | :---: | :---: | :--- | :---: |
| `Theory.verifyMirViaMiniSSA_sound` | Stateless VC Transport Bridge | $k_{\text{ssa}} + \Delta$ | $k_{\text{ssa}}$ | $\Delta(\text{cert})$ | `[propext, Classical.choice, Quot.sound]` | **`0`** |
| `Theory.verifyStatefulMirViaMiniSSA_sound` | Stateful + Fuel-Bounded Bridge | $\le K + \Delta$ | $\le K$ | $\Delta(\text{cert})$ | `[propext, Classical.choice, Quot.sound]` | **`0`** |
| `Theory.checkNormBisim_forward_refines` | Forward Compiler Refinement (`MiniSSA ⊑ MIR`) | $k_{\text{ssa}} + \Delta$ | $k_{\text{ssa}}$ | $\Delta(\text{cert})$ | `[propext, Classical.choice, Quot.sound]` | **`0`** |
| `Theory.refinesOnly_deadUninitLoad_unsound_for_vc_transport` | Counterexample (`NORM-10`) | `.ub` | `.returned 42 2` | `1` (rejected) | `[propext]` | **`0`** |
| `Theory.refinesOnly_sroaBadPadding_unsound_for_vc_transport` | Counterexample (`NORM-05` unguarded) | `.ub` | `.returned 10 2` | `0` (rejected) | `[propext]` | **`0`** |
| `Theory.refinesOnly_aliasedReborrow_unsound_for_vc_transport` | Counterexample (`NORM-06` unguarded) | `.ub` | `.returned 104 2` | `2` (rejected) | `[propext]` | **`0`** |
| `Theory.fixture1_mir_verified` | **Fixture 1**: Slice subslice `&s[4..]` + `StorageLive`/`StorageDead` + `goto` | **`5`** | **`2`** | **`3`** (`2.50x` step reduction) | `[propext, Classical.choice, Quot.sound]` | **`0`** |
| `Theory.fixture2_mir_verified` | **Fixture 2**: Struct `SROA` split + `Mem2Reg` slot promotion (`fst + 10`) | **`7`** | **`4`** | **`3`** (`1.75x` step reduction) | `[propext, Classical.choice, Quot.sound]` | **`0`** |
| `Theory.fixture3_mir_stateful_verified` | **Fixture 3**: Two inlined helper calls + `goto` with step bound `k_mir ≤ 6` | **`6`** | **`3`** | **`3`** (`2.00x` step reduction) | `[propext, Classical.choice, Quot.sound]` | **`0`** |

## Boundaries

1. **Loop-Body Affine Fuel Scaling (`known not to apply` with constant additive slack alone for unbounded loops):**
   - For straight-line and unrolled normalization (`NormCert`), `certFuelSlack` computes an exact additive constant $c_2$ such that $k_{\text{mir}} \le 1 \cdot k_{\text{ssa}} + c_2$. When normalization collapses $d$ administrative MIR steps inside a loop body that executes $N$ iterations, the affine step bound is $k_{\text{mir}} \le (1 + d_{\text{loop}}) \cdot k_{\text{ssa}} + c_{\text{entry/exit}}$, where $d_{\text{loop}}$ is the maximum per-backedge slack of any normalized basic block cycle.
2. **Escaping Stack Allocations and Address-Taken Locals (`known not to apply` for pure register `Mem2Reg`):**
   - Stack locals whose address is passed to an opaque function or stored into memory cannot be eliminated by `NORM-04` (`Mem2Reg_NonEscapingSlot`) and must remain explicit memory allocations in `MiniSSA` until proven non-aliasing or discharged via separation-logic / frame lenses.

## Evidence

1. **Kernel-Checked Lean 4.34.1 Mechanization:**
   - [`support/BidirectionalMirMiniSsaTransportProbe.lean`](support/BidirectionalMirMiniSsaTransportProbe.lean): Self-contained `695`-line Lean `v4.34.1` probe defining `Trusted.VerificationResult`, `Trusted.StatefulVerificationResult`, `Theory.MiniSsaProg`, `Theory.NormCert`, `Theory.checkNormBisim`, `Theory.verifyMirViaMiniSSA_sound`, three formal `RefinesOnly` counterexamples, and three end-to-end verified fixtures.
2. **Rule Catalog and Audit Receipt:**
   - [`support/hybrid_trace_bisim_rule_catalog.json`](support/hybrid_trace_bisim_rule_catalog.json): Machine-readable classification of all 12 `HybridTrace` normalization rule families (`BisimExact`, `GuardedBisim`, `RefinesOnly`).
   - [`support/audit_output.json`](support/audit_output.json): Execution timing (`3.89s` wall-clock, `573,108 KB` peak RSS) and `#print axioms` audit output confirming `0` `sorryAx`, `0` `Lean.ofReduceBool`, and `0` added `Trusted` definitions.

## Revalidation

Run the Lean `v4.34.1` kernel check under `anneal-lean-run`:

```bash
anneal-lean-run --mode file --concurrency 4 -- \
  elan run leanprover/lean4:v4.34.1 lean \
  -DElab.async=false -Ddebug.skipKernelTC=false \
  reports/bidirectional-mir-minissa-refinement-and-anneal-vc-transport/support/BidirectionalMirMiniSsaTransportProbe.lean
```
