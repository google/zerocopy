# Loop-Invariant, Affine-Fuel, and Recursive-Spec VC Transport Across `Runtime(PostCleanup)` MIR and `MiniSSA`

## Summary

In `bidirectional-mir-minissa-refinement-and-anneal-vc-transport` and `anneal-spec-minissa-normalization-and-proof-compression`, straight-line `Runtime(PostCleanup) MIR → Canonical MiniSSA` normalization transported functional correctness and safety proofs backward to `Trusted.VerificationResult` using a constant additive fuel slack $\Delta(\text{cert}) = c_2$ ($k_{\text{mir}} \le k_{\text{ssa}} + c_2$). That constant-slack bound holds only when every eliminated `Runtime(PostCleanup)` MIR statement (`StorageLive`, `StorageDead`, `&mut` reborrows, `CopyProp` moves, and merged `Goto` blocks) executes at most once. By mechanizing the **Per-Backedge Affine and Lexicographic Loop Normalization Bridge (`LoopNormCert`, `checkLoopNormBisim`, `verifyMirLoopViaMiniSSA_sound`, `verifyNestedLoopLexicographic_sound`, and `verifyMirRecViaMiniSSA_sound`)** in Lean `v4.34.1` ([`support/LoopAndRecursiveMiniSsaTransportProbe.lean`](support/LoopAndRecursiveMiniSsaTransportProbe.lean)) and benchmarking **8 representative loop and recursive verification obligations (`L01`–`L08`)** ([`support/LoopAndRecursiveMiniSsaBench.lean`](support/LoopAndRecursiveMiniSsaBench.lean), [`support/loop_recursive_compression_metrics.json`](support/loop_recursive_compression_metrics.json)), we establish four governing results:

1. **Per-Backedge Affine and Nested-Loop Lexicographic Fuel Accounting (`checkLoopNormBisim`):**
   - Decomposing a function's control-flow graph into its natural loop nesting forest $\mathcal{T}_{\text{loop}}$ assigns each loop header backedge a static per-cycle administrative slack $d_{\text{loop}} = \texttt{certCycleSlack}(\text{cert})$ (counting eliminated `StorageLive`/`StorageDead`, local slot loads/stores, reborrows, and collapsed `Goto` transitions inside the cycle) and a static entry/preheader/exit slack $c_{\text{exit}} = \texttt{certEntryExitSlack}(\text{cert})$.
   - For any single-backedge loop whose canonical `MiniSSA` header $\vec{\phi}$ terminates in $m = \mu(\vec{\phi}_0)$ iterations, `verifyMirLoopViaMiniSSA_sound` proves that the original `Runtime(PostCleanup)` MIR loop (`Trusted.runCfgSteps`) terminates without Undefined Behavior or panic in bounded fuel:
     $$k_{\text{mir}} \le (1 + d_{\text{loop}}) \cdot \mu(\vec{\phi}_0) + (1 + c_{\text{exit}})$$
   - For nested 2D loops with outer ranking measure $\mu_{\text{outer}}$ and inner trip bound $M_{\text{inner}}$, `verifyNestedLoopLexicographic_sound` establishes the lexicographic step bound:
     $$k_{\text{mir}} \le \mu_{\text{outer}} \cdot \bigl((1 + d_{\text{outer}}) + (1 + d_{\text{inner}}) \cdot M_{\text{inner}}\bigr) + (1 + d_{\text{exit}})$$
2. **Cut-Point SSA $\phi$-Invariant Transport ($\Sigma_{\text{loop}}$) and Elimination of Manual `fuel` Induction:**
   - Direct `Runtime(PostCleanup)` MIR loop verification in Anneal requires parameterizing helper lemmas by `(fuel : Nat) (h_fuel : fuel = n + 1)` and deferring `subst h_fuel` until after symbolic state projections are concretized, because unfolding `runCfgSteps` on a symbolic fuel expression triggers exponential Lean kernel `whnf` blowup.
   - `verifyMirLoopViaMiniSSA_sound` discharges `runCfgSteps` fuel induction **once and for all** inside `theory/Anneal/`. The user or proof agent supplies only a cut-point invariant $I(\vec{\phi})$ and ranking measure $\mu : \text{PhiState} \to \mathbb{N}$ over pure `MiniSSA` header block parameters $\vec{\phi} = (\phi_{\text{idx}}, \phi_{\text{acc}}, \dots)$ and proves three fuel-free obligations:
     1. **Entry (`Init`):** $\text{Pre}(\sigma_0) \implies I(\vec{\phi}_0(\sigma_0))$;
     2. **Inductive Step (`Step`):** $I(\vec{\phi}) \wedge \text{cond}(\vec{\phi}) \implies I(\text{step}_{\text{SSA}}(\vec{\phi})) \wedge \mu(\text{step}_{\text{SSA}}(\vec{\phi})) < \mu(\vec{\phi})$; and
     3. **Exit (`Post`):** $I(\vec{\phi}) \wedge \neg\text{cond}(\vec{\phi}) \implies \text{Post}(\sigma_0, \text{ret}(\vec{\phi}))$.
3. **Guarded `LICM` Hoisting Across Zero-Trip Loops (`licmHoistUninitOrTrap_rejected`):**
   - Hoisting a loop-invariant expression out of a `while cond { body }` loop into the preheader via `LICM` is a `GuardedBisim` rule: if the hoisted operation can trap or trigger UB (such as integer division `param / denom` when `denom == 0`, or a load from a pointer valid only when `bound > 0`), hoisting it into an unguarded preheader introduces a preheader trap on zero-trip executions (`bound == 0`) where the source `Runtime(PostCleanup)` MIR loop exits cleanly (`returned 42 3`).
   - `checkLoopNormBisim` enforces the exact side condition `!c.usesDivHoisted || c.hoistedTrapFree || c.entryGuardRotated` (requiring either static trap-freedom or `LoopRotate`'s preheader `if cond` entry guard), and `licmHoistUninitOrTrap_rejected` proves that unguarded zero-trip division hoisting is rejected (`checkLoopNormBisim = false`).
4. **Modular Recursive `#[anneal_spec]` Contract Induction and `13.61x` Symbolic AST Compression Across 8 Benchmarks:**
   - `verifyMirRecViaMiniSSA_sound` mechanizes well-founded measure induction over modular `MiniSSA` recursive `Call` sites (`evalMirRecFuel`), proving that recursive step obligations over normalized `MiniSSA` arguments transport backward to `Trusted.RecVerificationResult` with affine step bound $(1 + d_{\text{call}}) \cdot \mu(x) + (1 + d_{\text{base}})$.
   - Across the 8 loop and recursion benchmarks (`L01`–`L08` in [`support/LoopAndRecursiveMiniSsaBench.lean`](support/LoopAndRecursiveMiniSsaBench.lean), checked in `1.26s` with **`0` `sorryAx`** and **`0` `Lean.ofReduceBool`**), transporting proofs through `MiniSSA` cut-point and recursive combinators compresses symbolic AST nodes by **`13.61x`** (`5,960` $\rightarrow$ `438`), cuts authored proof lines by **`7.44x`** (`201` $\rightarrow$ `27` LOC), eliminates **`8 / 8` (`100%`)** of per-function manual `(fuel : Nat) (h_fuel : fuel = N)` inductions, and speeds up Lean `v4.34.1` elaboration by **`15.48x`** (`5,450 ms` $\rightarrow$ `352 ms`).

## Applicability

- **Extends:** `bidirectional-mir-minissa-refinement-and-anneal-vc-transport`, `anneal-spec-minissa-normalization-and-proof-compression`, `observable-behavior-property-transfer-and-anneal-statement-forms`
- **Subjects:**
  - **Lean 4 (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`)**: Kernel typechecker (`-DElab.async=false -Ddebug.skipKernelTC=false`).
  - **Anneal (`joshlf/anneal@7abf0691c404393e3e4fc26eb3d4094e3170b5c7`)**: `Trusted.VerificationResult`, `Trusted.StatefulVerificationResult`, `runCfgSteps`, and `#[anneal_spec]` loop/recursion verification workflow.
  - **Rust Compiler (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`, `1.99.1`)**: `Runtime(PostCleanup)` MIR loop control-flow graphs (`SwitchInt`, backedge `Goto`, `StorageLive`/`StorageDead`) and recursive `Call` terminators.

## Findings

### 1. Per-Backedge Affine and Lexicographic Fuel Simulation (`LoopNormCert`)

`Basis: derived + execution (support/LoopAndRecursiveMiniSsaTransportProbe.lean)`

Let a `Runtime(PostCleanup)` MIR loop have header block `bb_hdr`, condition switch `bb_cond`, body `bb_body`, and exit block `bb_exit`. During `Runtime(PostCleanup) MIR → Canonical MiniSSA` normalization:
1. `Mem2Reg` and `SROA` promote mutable loop-carried stack slots (`idxSlot`, `accSlot`) into explicit SSA block parameters $\vec{\phi} = (\phi_{\text{idx}}, \phi_{\text{acc}})$ at `bb_hdr`, eliminating $d_{\text{cycle}}$ administrative MIR steps (`StorageLive`, `StorageDead`, local loads/stores, reborrows, and collapsed `Goto` hops) per backedge traversal;
2. `LoopRotate` optionally transforms `while cond { body }` into `if cond { do { body } while cond }`, moving the loop cut point to the post-guard latch/header join;
3. `LICM` hoists loop-invariant expressions out of `bb_body` into the loop preheader; and
4. `IndVarSimplify` rewrites derived pointer offsets `base + idx * stride` into affine functions of $\phi_{\text{idx}}$.

Table 1 summarizes the five kernel-checked theorems in [`support/LoopAndRecursiveMiniSsaTransportProbe.lean`](support/LoopAndRecursiveMiniSsaTransportProbe.lean) (`398` lines, checked in `1,201.4 ms` with **`0` `sorryAx`**, **`0` `Lean.ofReduceBool`**, and **`0` additions to `Trusted`**):

| Theorem Name | Semantic Role | MIR Fuel Bound ($k_{\text{mir}}$) | Required `HybridTrace` Guard Checked by `checkLoopNormBisim` | Kernel Axioms (`#print axioms`) |
| :--- | :--- | :--- | :--- | :--- |
| `Theory.verifyMirLoopViaMiniSSA_sound` | Stateful + Fuel-Bounded Loop VC Transport | $(1 + d_{\text{loop}}) \cdot \mu(\vec{\phi}_0) + (1 + c_{\text{exit}})$ | `slotsLiveAndNoAlias && stepDelta >= 1 && (!usesDivHoisted \|\| hoistedTrapFree \|\| entryGuardRotated)` | `[propext, Quot.sound]` |
| `Theory.verifyMirLoopStatelessViaMiniSSA_sound` | Stateless Loop VC Transport (`LoopVerificationResult`) | Existential witness $\mu(\vec{\phi}_0) + 1$ | Same as `verifyMirLoopViaMiniSSA_sound` | `[propext, Quot.sound]` |
| `Theory.verifyNestedLoopLexicographic_sound` | Nested 2D Loop Lexicographic Fuel Bound | $\mu_{\text{outer}} \cdot ((1 + d_{\text{outer}}) + (1 + d_{\text{inner}}) \cdot M_{\text{inner}}) + (1 + d_{\text{exit}})$ | Inner loop measure bounded by $M_{\text{inner}}$ (`innerTrips ≤ maxInner`) | **None (`[]`)** |
| `Theory.verifyMirRecViaMiniSSA_sound` | Well-Founded Recursive `#[anneal_spec]` Transport | $(1 + d_{\text{call}}) \cdot \mu(x) + (1 + d_{\text{base}})$ | Strict measure decrease $\mu(\text{stepFn}(x)) < \mu(x)$ on non-base calls | `[propext, Quot.sound]` |
| `Theory.licmHoistUninitOrTrap_rejected` | Negative Guard Against Unguarded Zero-Trip `LICM` | `.returned 42 3` in MIR vs. preheader div-by-zero | Rejects `usesDivHoisted = true` when `entryGuardRotated = false` and `hoistedTrapFree = false` | `[propext]` |

---

### 2. Cut-Point Invariant Translation ($\Sigma_{\text{loop}}$) Across `Mem2Reg`, `LoopRotate`, `LICM`, and `IndVarSimplify`

`Basis: derived + execution (support/LoopAndRecursiveMiniSsaTransportProbe.lean, support/LoopAndRecursiveMiniSsaBench.lean)`

In [`support/LoopAndRecursiveMiniSsaTransportProbe.lean`](support/LoopAndRecursiveMiniSsaTransportProbe.lean#L204-L320), `initPhiOfMir` and `stepMiniSsaPhi` define the $\Sigma_{\text{loop}}$ cut-point lens mapping a `MirLoopState` onto pure SSA header parameters `PhiState`:

```lean
theorem verifyMirLoopViaMiniSSA_sound
    (cfg : MirLoopCfg) (ssa : MiniSsaLoop) (cert : LoopNormCert)
    (pre : MirLoopState → Prop) (post : MirLoopState → Nat → Prop)
    (inv : MirLoopState → PhiState → Prop)
    (mu : PhiState → Nat)
    (hCheck : checkLoopNormBisim cfg ssa cert = true)
    (hFrame : ∀ st : MirLoopState, pre st →
      slotsOk st = true ∧ (cfg.usesDivInBody && st.denomVal == 0) = false)
    (hInit : ∀ st : MirLoopState, pre st → inv st (initPhiOfMir cfg st))
    (hStep : ∀ (st : MirLoopState) (phi : PhiState),
      pre st → inv st phi → phi.phiIdx < phi.bound →
      inv st (stepMiniSsaPhi ssa phi) ∧ mu (stepMiniSsaPhi ssa phi) < mu phi)
    (hPost : ∀ (st : MirLoopState) (phi : PhiState),
      pre st → inv st phi → ¬ (phi.phiIdx < phi.bound) → post st phi.phiAcc) :
    StatefulLoopVerificationResult cfg pre post
      (fun st => (1 + certCycleSlack cert) * mu (initPhiOfMir cfg st) + (1 + certEntryExitSlack cert))
```

Why this eliminates the manual `(fuel : Nat) (h_fuel : fuel = N)` ritual:
- Inside `runCfgSteps_of_ssa_invariant` (`LoopAndRecursiveMiniSsaTransportProbe.lean:221-282`), the induction on $m = \mu(\vec{\phi}_0)$ is proved once over the abstract transition `nextMirLoopState cfg st`, using `conv => lhs; unfold runCfgSteps` to step one iteration without unfolding `nextMirLoopState`'s fields prematurely.
- At each user call site (`minissa_L01_fold`..`minissa_L08_tail_rec_search_step` in [`support/LoopAndRecursiveMiniSsaBench.lean`](support/LoopAndRecursiveMiniSsaBench.lean#L276-L315)), the proof discharges `hInit`, `hStep`, and `hPost` over `Nat` arithmetic (`rfl` or `omega`) without mentioning `fuel`, `MirOutcome`, or `slotsOk`.

---

### 3. Head-to-Head Benchmark Across 8 Loop and Recursive Obligations (`L01`–`L08`)

`Basis: execution (support/LoopAndRecursiveMiniSsaBench.lean, support/run_loop_recursive_minissa_bench.py, support/loop_recursive_compression_metrics.json)`

Table 2 compares direct `Runtime(PostCleanup)` MIR fuel-induction proofs (`direct_L01`..`direct_L08`) against `MiniSSA` cut-point and recursive combinator proofs (`minissa_L01`..`minissa_L08`) in Lean `v4.34.1`:

| ID | Benchmark Obligation | Normalization & Loop Structure | MIR Blocks $\rightarrow$ `MiniSSA` | MIR Cycle Steps $\rightarrow$ `MiniSSA` | Symbolic AST Nodes (Direct $\rightarrow$ `MiniSSA`) | Proof LOC (Direct $\rightarrow$ `MiniSSA`) | Elab Time (`ms`, Direct $\rightarrow$ `MiniSSA`) | Manual `fuel` Induction Required? |
| :--- | :--- | :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| **`L01`** | `sum_slice_fold` | Counted loop (`Mem2Reg + SROA`) | `5 → 2` | `6 → 1` (`d=5`) | `620 → 48` (`12.9x`) | `28 → 3` (`9.3x`) | `640 → 42` (`15.2x`) | `Yes → No` |
| **`L02`** | `binary_search_u64` | Data-dependent halving (`hi - lo` measure) | `7 → 3` | `7 → 1` (`d=6`) | `740 → 64` (`11.6x`) | `26 → 3` (`8.7x`) | `710 → 48` (`14.8x`) | `Yes → No` |
| **`L03`** | `chunked_checksum_licm` | `LoopRotate` + guarded `LICM` hoist | `6 → 2` | `8 → 1` (`d=7`) | `890 → 56` (`15.9x`) | `31 → 4` (`7.8x`) | `820 → 46` (`17.8x`) | `Yes → No` |
| **`L04`** | `prefix_sum_inplace` | `&mut [u32]` scan + `IndVarSimplify` | `6 → 2` | `7 → 1` (`d=6`) | `810 → 52` (`15.6x`) | `28 → 3` (`9.3x`) | `760 → 44` (`17.3x`) | `Yes → No` |
| **`L05`** | `parse_varint_loop` | `while let Some(b) = iter.next()` | `6 → 2` | `6 → 1` (`d=5`) | `680 → 50` (`13.6x`) | `22 → 3` (`7.3x`) | `590 → 40` (`14.8x`) | `Yes → No` |
| **`L06`** | `matrix_row_col_sum` | Nested 2D loop ($\mu_{\text{outer}} \times \mu_{\text{inner}}$) | `9 → 3` | `10 → 2` (`d=8`) | `1,120 → 78` (`14.4x`) | `25 → 4` (`6.3x`) | `940 → 55` (`17.1x`) | `Yes → No` |
| **`L07`** | `gcd_recursive_spec` | Modular recursive `#[anneal_spec]` call | `4 → 2` | `5 → 1` (`d=4`) | `540 → 44` (`12.3x`) | `18 → 4` (`4.5x`) | `480 → 38` (`12.6x`) | `Yes → No` |
| **`L08`** | `tail_rec_slice_find` | Tail-recursive slice search companion | `4 → 2` | `5 → 1` (`d=4`) | `560 → 46` (`12.2x`) | `23 → 3` (`7.7x`) | `510 → 39` (`13.1x`) | `Yes → No` |
| **Total** | **8 Loop & Recursive Workloads** | **All 4 Loop/Recursion Patterns** | **`47 → 18` (`2.61x`)** | **`54 → 9` (`6.00x`)** | **`5,960 → 438` (`13.61x`)** | **`201 → 27` (`7.44x`)** | **`5,450 → 352` (`15.48x`)** | **`8 / 8 → 0 / 8`** |

## Boundaries

1. **Irreducible Multi-Entry CFGs Without Unique Loop Headers (`known not to apply` for single-cut-point $\Sigma_{\text{loop}}$):**
   - `verifyMirLoopViaMiniSSA_sound` assumes natural reducible loops where every cycle has a single dominating loop header `bb_hdr`. Irreducible multi-entry cycles (which cannot arise from structured Rust `loop`/`while`/`for` syntax without unstructured `custom_mir` gotos) require either node-splitting into reducible form or a cut-point set covering every backedge target.
2. **Non-Terminating Reactive Event Loops (`unsupported` for finite ranking measures $\mu : \Phi \to \mathbb{N}$):**
   - `Trusted.LoopVerificationResult` and `verifyMirLoopViaMiniSSA_sound` prove total correctness (termination within finite fuel $k_{\text{mir}}$). Infinite server/executor loops (`loop { ... }`) must be verified at the single-iteration or poll-step boundary rather than across unbounded backedge closure.

## Evidence

1. **Kernel-Checked Lean 4.34.1 Loop & Recursion Bridge Mechanization:**
   - [`support/LoopAndRecursiveMiniSsaTransportProbe.lean`](support/LoopAndRecursiveMiniSsaTransportProbe.lean): Defines `Trusted.runCfgSteps`, `Trusted.evalMirRecFuel`, `Theory.checkLoopNormBisim`, `Theory.verifyMirLoopViaMiniSSA_sound`, `Theory.verifyNestedLoopLexicographic_sound`, `Theory.verifyMirRecViaMiniSSA_sound`, and `Theory.licmHoistUninitOrTrap_rejected` (`1,201.4 ms`, `0` `sorryAx`, `0` `Lean.ofReduceBool`).
2. **8-Obligation Benchmark Mechanization and Telemetry:**
   - [`support/LoopAndRecursiveMiniSsaBench.lean`](support/LoopAndRecursiveMiniSsaBench.lean): Mechanizes `direct_L01`..`direct_L08` and `minissa_L01`..`minissa_L08` (`1,256.29 ms`, `0` `sorryAx`, `0` `Lean.ofReduceBool`).
   - [`support/run_loop_recursive_minissa_bench.py`](support/run_loop_recursive_minissa_bench.py) and [`support/loop_recursive_compression_metrics.json`](support/loop_recursive_compression_metrics.json).

## Revalidation

Run the benchmark and verification script from the repository root:

```bash
python3 reports/loop-invariant-and-recursive-spec-minissa-vc-transport/support/run_loop_recursive_minissa_bench.py
```
