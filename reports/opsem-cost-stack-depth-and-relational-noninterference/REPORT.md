# Operational Cost Accounting, Transient Call-Stack High-Water Marks, and Relational Finite-Prefix Noninterference in Lean 4.34.1

## Summary

Preserving safety (`NoUB`) and completed return values across an operational lowering or abstract-machine simulation is insufficient to preserve execution-cost budgets, transient call-stack depth bounds, or side-channel noninterference. This report documents eight machine-checked Lean 4.34.1 modules (`PrefixAccounting`, `CostStack`, `Observations`, `ObservationAdapters`, `OperationalObservations`, `OperationalAdapter`, `CallSecuritySpecimens`, and `CallSecurityComposition`, totaling 113 `#print axioms` audits across target modules) that formalize the exact simulation, adapter, and boundary-state conditions required to transport quantitative resource bounds and 2-safety possibilistic finite-prefix noninterference across multi-step operational semantics and sequential call boundaries.

Key findings:

1. **Reverse target-prefix coverage for cost and peak-stack transport (`PrefixAccounting`, `CostStack`):** Forward stuttering simulation (`StutteringSimulation`), `NoUB` on both machines, a bounded source cost (`≤ 1`), and identical completed outputs (`{0}`) are jointly consistent with unbounded charged target steps (`ExtraTarget.safety_and_output_do_not_bound_target`). Sound upper-bound transport across all execution prefixes requires **reverse target-prefix coverage** (`Accounting`: every reachable target prefix $t$ is related to a reachable source prefix $s$ with $\text{targetCost}(t) \le \text{costMap}(\text{sourceCost}(s))$ and $\text{targetPeak}(t) \le \text{peakMap}(\text{sourcePeak}(s))$).
2. **Transient stack high-water marks vs. terminal frame depth (`CostStack`):** In a recursive call/return machine parameterized by nesting depth $n$, terminal return configurations always have call-stack depth $0$, hiding intermediate recursion depth. Tracking the prefix high-water mark $\text{peak} = \max(\text{peak}, \text{depth}(c'))$ proves exact source bounds ($\text{work} \le 2n+2$, $\text{peak} \le n+1$) and 2-phase (`armed : Bool`) target bounds ($\text{total} = 2 \cdot \text{work} + \text{phaseCost}(\text{armed}) \le 4n+4$, $\text{peak} \le n+1$), whereas a deeper-call counterexample (`deeper_stack_counterexample`) reaches transient $\text{peak} = n+2$ before returning $0$ at depth $0$.
3. **2-safety possibilistic finite-prefix noninterference and one-way simulation failures (`Observations`):** Equal return values and a shared worst-case cost bound do not prevent branch or address-trace leakage (`mutant_same_output_and_common_cost_bound`). Neither forward trace inclusion (`forward_matching_does_not_preserve_noninterference`, where the target adds a secret-dependent branch) nor reverse trace refinement (`trace_refinement_does_not_preserve_noninterference`, where the target resolves source nondeterminism using the secret) preserves 2-safety possibilistic `FiniteNoninterference`; bidirectional trace coverage (`finite_noninterference_of_bidirectional_coverage`) is required. Furthermore, pointwise trace equality per fixed coin flip (`same_coin_observations`) does not prevent secret-biased probability distributions (`same_coin_but_distinguishing_distribution`).
4. **Public-uniform relational observation adapters (`ObservationAdapters`, `OperationalObservations`, `OperationalAdapter`):** Lowering passes that expand one source step into a multi-step target sequence violate literal trace-set equality (`expansion_is_not_literal_trace_equivalence`). A `PublicUniform` relational observation adapter (`expansionAdapter`, which depends only on public inputs and source traces) preserves `FiniteNoninterference` across exact adapter images (`target_noninterference_of_adapter_image`) and across operational `LoggedPath` prefix closures (`operational_adapter_exact_image`, `target_prefix_noninterference_via_adapter`), whereas a secret-dependent adapter fails (`secret_adapter_not_noninterference`).
5. **Sequential call composition and residual-state coupling (`CallSecuritySpecimens`, `CallSecurityComposition`):** In a two-call nondeterministic state machine (`Mode.retained`), call 1 chooses a random mask $r \in \{\text{false}, \text{true}\}$, stores it in residual state, and emits $\text{address}(\text{first}, r)$; call 2 reads $r$ and emits $\text{address}(\text{second}, r \oplus \text{secret})$. Both calls' root-projected marginal trace sets satisfy `FiniteNoninterference` (`retained_marginals_noninterference`), and every completed run returns $[0,0]$ with $\text{logicalCost} = 2$ (`completed_return_cost`), yet the composed two-call execution violates `FiniteNoninterference` (`retained_not_noninterference`, witnessed by the 4-event prefix `distinguishing = [address .first false, charge .first, returned .first, address .second false]`; conceptually `perCallOnly_fails_composedPossibilisticNI`). Compositional preservation requires a two-sided residual-state boundary relation (`StageMatch` over entry/boundary/final relations $R_0, R_1, R_2$), which holds for independent per-call choices (`Mode.fresh`, `fresh_call_cut_noninterference`) and fails on `Mode.retained` (`retained_boundary_mismatch`, `marginal_summary_does_not_supply_stage_contract`).

## Applicability

These findings apply to:

- Operational semantics and abstract-machine verification frameworks (such as MiniRust-based verifiers and compiler correctness proofs) that seek to transport WCET/instruction-count budgets, stack-frame space bounds, or constant-time/side-channel noninterference across IR lowerings.
- Modular verification of sequential function calls in the presence of nondeterminism, allocator/cache/register residual state, and microarchitectural or memory-address leakage models.

Specific version and configuration anchors:

- **Lean 4 kernel verification:** Lean `4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`, `x86_64-unknown-linux-gnu`), verified with `lean -j1 -M2048`.
- **Operational semantics alignment:** Prefix-based operational execution (`Execution.Reach`, `Execution.NoUB`) aligned with MiniRust (`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`) frame and step conventions.

## Findings

### 1. Reverse Prefix Coverage for Operational Cost and Stack-Depth Bounds (`PrefixAccounting.lean`)

`Basis: execution | derived`

In `support/PrefixAccounting.lean` (SHA-256 `4f495dca01c7561788dcd2b741958e80e146ba0ad25ea46dddf9cf2dc5669eda`), an `Accounting` witness between a source transition system `(SourceStep, sourceInitial, sourceCost, sourcePeak)` and a target transition system `(TargetStep, targetInitial, targetCost, targetPeak)` requires:

1. **Reverse target-prefix coverage (`cover`):**
   $$\forall t,\; \text{Reach}(\text{TargetStep}, \text{targetInitial}, t) \implies \exists s,\; \text{Reach}(\text{SourceStep}, \text{sourceInitial}, s) \land \text{Related}(s, t)$$
2. **Monotone quantitative maps (`cost_le`, `peak_le`):**
   $$\forall s\, t,\; \text{Related}(s, t) \implies \text{targetCost}(t) \le \text{costMap}(\text{sourceCost}(s)) \;\land\; \text{targetPeak}(t) \le \text{peakMap}(\text{sourcePeak}(s))$$

When `costMap` and `peakMap` are monotone (`MonotoneNat`), `Accounting.upper_bounds` proves that any all-prefix source upper bounds $\text{sourceCost}(s) \le B_{\text{cost}}$ and $\text{sourcePeak}(s) \le B_{\text{peak}}$ transport to all reachable target prefixes:

$$\text{targetCost}(t) \le \text{costMap}(B_{\text{cost}}) \quad\text{and}\quad \text{targetPeak}(t) \le \text{peakMap}(B_{\text{peak}})$$

To demonstrate why forward simulation and safety are insufficient, `PrefixAccounting.ExtraTarget` defines a source machine that steps `.start → .done 0` in 1 step and a target machine `.extra k` that can either finish (`.done 0`) or increment `.extra (k + 1)` arbitrarily while relating every `.extra k` to `.start`. `ExtraTarget.safety_and_output_do_not_bound_target` proves that:

- Forward `PrefixTransfer.StutteringSimulation` holds from source to target;
- Both source and target satisfy `Execution.NoUB`;
- Source cost is bounded by $1$ on all reachable prefixes;
- Source and target have identical completed outputs (`{0}`);
- Yet target cost is unbounded (`ExtraTarget.no_target_cost_bound`: $\neg \exists B,\; \forall t,\; \text{Reach}(\text{TargetStep}, \text{targetInitial}, t) \implies \text{TargetCost}(t) \le B$).

### 2. Recursive Call-Stack High-Water Marks and Two-Phase Step Expansion (`CostStack.lean`)

`Basis: execution | derived`

In `support/CostStack.lean` (SHA-256 `61307e94341b2db58906b915b4172bb40fc76ba3c38a098bb3ccfa874ada1977`), a recursive call/return state machine is parameterized by recursion depth $n : \mathbb{N}$:

- **Control and frame state:** `SourceControl` is either `.descend remaining stack` (pushing `()` frames until `remaining = 0`) or `.ascend stack value` (popping frames until `stack = []`, returning `0`).
- **Cumulative work and high-water mark:** Each `SourceStep` increments `work := s.work + 1` and updates `peak := max s.peak (depth c')`, starting from `sourceInitial n` with `work = 0` and `peak = 1` (representing the root activation frame).
- **Exact source witnesses and prefix bounds:**
  - `source_completion`: `sourceInitial n` reaches a completed state `.ascend [] 0` with `work = 2 * n + 2`, current stack depth `0`, and `peak = n + 1`.
  - `source_peak_witness`: `sourceInitial n` reaches the deepest frame `.descend 0 (List.replicate n ())` with current depth `n + 1` and `peak = n + 1`.
  - `source_prefix_bounds`: every reachable source prefix satisfies `s.work ≤ 2 * n + 2` and `s.peak ≤ n + 1`.
- **Two-phase target expansion:** `TargetConfig` pairs `source : SourceConfig` with `armed : Bool`. Each source transition is split into an arming step (`armed = false → true`) and a committing step (`armed = true → false` advancing `source`). Total target cost is `total t = 2 * t.source.work + phaseCost t.armed` (`target_exact_cost`, where `phaseCost true = 1`).
  - `target_prefix_bounds`: every reachable target prefix satisfies `total t ≤ 4 * n + 4` and `t.source.peak ≤ n + 1`.
  - `arbitrary_prefix_bound_transport` and `arbitrary_bound_transport`: any symbolic user budget `time n` bounding source work transports to `total t ≤ 2 * time n + 1` across all target prefixes (including `armed = true` mid-macro-step states) and `total t ≤ 2 * time n` across settled states (`armed = false`).
- **Negative controls:**
  - `charged_extra_step_counterexample`: the target machine exceeds the unadjusted source budget `2 * n + 2` (`total (targetCompleted n) > 2 * n + 2`).
  - `deeper_stack_counterexample`: running `targetInitial (n + 1)` still returns output `0` at final stack depth `0`, but reaches a transient stack high-water mark `peak = n + 2 > n + 1`.
  - `BadPrefix.bad_prefix_visible_in_both`: a fault prefix that transitions into an infinite `.spin` loop is still caught as unsafe (`¬ NoUB`) on both source and target machines.

### 3. Possibilistic Finite-Prefix Noninterference and Simulation Counterexamples (`Observations.lean`)

`Basis: execution | derived`

In `support/Observations.lean` (SHA-256 `82b65c96389e0d04f4908d47d8800ba14f14e1fba1433b497c77cbc1c33f9bf2`), execution traces are lists of `Event`:

$$\text{Event} ::= \text{branch}(\text{taken} : \text{Bool}) \mid \text{address}(\text{slot} : \mathbb{N}) \mid \text{cost}(\text{units} : \mathbb{N}) \mid \text{returned}(\text{value} : \mathbb{N})$$

For an observation family $F : \text{Input} \to \text{List Event} \to \text{Prop}$ and public-equivalence relation `PublicRelated` ($x.\text{public} = y.\text{public}$), 2-safety possibilistic noninterference is defined as:

$$\text{FiniteNoninterference}(F) \iff \forall x\, y,\; \text{PublicRelated}(x, y) \implies \forall \tau,\; F(x, \tau) \iff F(y, \tau)$$

`finite_noninterference_of_bidirectional_coverage` proves that if $F$ satisfies `FiniteNoninterference` and $G$ satisfies both `TraceCoverage F G` and `TraceCoverage G F` (`TraceEquivalent F G`), then $G$ satisfies `FiniteNoninterference`. Four machine-checked negative controls demonstrate why weaker conditions fail:

| Negative Control Theorem | Mechanism | What Fails |
| --- | --- | --- |
| `branch_address_mutant_not_noninterference`, `mutant_same_output_and_common_cost_bound` | `branchAddressMutant` emits `[branch x.secret, address (if x.secret then 1 else 0), cost x.public, returned 0]`. | Both secret values return `0` and incur cost `x.public`, yet the prefix `[branch true]` distinguishes `secret = true` from `secret = false`. |
| `forward_matching_does_not_preserve_noninterference` | `addsLeak` includes all `constantPrefixes` plus `[branch x.secret]`. | Forward inclusion `TraceCoverage constantPrefixes addsLeak` holds and `constantPrefixes` is noninterfering, but `addsLeak` violates `FiniteNoninterference`. |
| `trace_refinement_does_not_preserve_noninterference` | Source `twoChoices` nondeterministically emits `[branch false]` or `[branch true]`; target `selectsSecret` refines this to `[branch x.secret]`. | Reverse refinement `TraceCoverage selectsSecret twoChoices` holds and `twoChoices` is noninterfering, but `selectsSecret` violates `FiniteNoninterference`. |
| `same_coin_but_distinguishing_distribution` | For each coin sample $c \in \{\text{false}, \text{true}\}$, `coinTrace x c` is identical across secrets (`same_coin_observations`), but `weightedMass` assigns weight $2$ when $x.\text{secret} = c$ and $0$ otherwise. | Possibilistic trace sets and per-coin traces match, but total event mass for `[branch true]` is $2$ when $\text{secret} = \text{true}$ and $0$ when $\text{secret} = \text{false}$, separating possibilistic from probabilistic noninterference. |

### 4. Relational Observation Adapters for Step-Expanding Lowerings (`ObservationAdapters.lean`, `OperationalObservations.lean`, `OperationalAdapter.lean`)

`Basis: execution | derived`

When a compiler or operational lowering splits one source cost step into two half-steps, literal trace equality between source and target fails (`ObservationAdapters.expansion_is_not_literal_trace_equivalence`). `support/ObservationAdapters.lean` (SHA-256 `dfe7291e870da855aafe4545554867274c0a1a61e573eca516398465051e3eff`) introduces relational observation adapters:

$$\text{Adapter} : \text{Input} \to \text{List Event} \to \text{List Event} \to \text{Prop}$$

An adapter is `PublicUniform` if related public inputs induce identical source-to-target trace relations ($\text{PublicRelated}(x, y) \implies (\text{adapter } x\, \tau_s\, \tau_t \iff \text{adapter } y\, \tau_s\, \tau_t)$). `adapter_image_noninterference` and `target_noninterference_of_adapter_image` prove that if $F$ satisfies `FiniteNoninterference`, `adapter` is `PublicUniform`, and target family $G$ is trace-set equivalent to `AdapterImage F adapter`, then $G$ satisfies `FiniteNoninterference`. Conversely, `secret_adapter_not_noninterference` proves that an adapter that inspects `x.secret` destroys noninterference even when applied to `constantPrefixes`.

`support/OperationalObservations.lean` (SHA-256 `49d6187219f7717bc8d11bf80e73853b7436d1be3cdc414f549b347fa6a1537a`) and `support/OperationalAdapter.lean` (SHA-256 `6f78fe1e66f7ea5157398dc391e12a2a4527dff4af1004db8eb6d65bd2b2024d`) connect this relational adapter theory directly to operational `LoggedPath` executions of `CostStack`:

- Every source transition emits `[Event.cost 1]`; every target arming transition (`armed = false → true`) emits `[Event.cost 1]` and every target committing transition (`armed = true → false`) emits `[Event.cost 1]`.
- For any reachable target prefix ending in an unsettled state (`armed = true`), its emitted trace has length $2k + 1$. `OperationalAdapter.target_logged_prefix_covered` proves that because `.running c true` is only reachable when `SourceStep` is enabled from `c` (`armed_has_next_source_step`), advancing the source path by that one enabled step yields a source trace of length $k + 1$ whose 2x expansion `[Event.cost 1, Event.cost 1]^{k+1}` has the target's $2k + 1$ trace as an exact prefix.
- `OperationalAdapter.operational_adapter_exact_image` proves exact trace-set equivalence between `AdapterImage (PrefixClosure sourceRuns) expansionAdapter` and `PrefixClosure targetRuns`, and `target_prefix_noninterference_via_adapter` concludes `FiniteNoninterference (PrefixClosure targetRuns)`.

### 5. Sequential Call Composition and Residual-State Boundary Contracts (`CallSecuritySpecimens.lean`, `CallSecurityComposition.lean`)

`Basis: execution | derived`

To test whether per-call noninterference summaries compose across sequential calls, `support/CallSecuritySpecimens.lean` (SHA-256 `896ed03254ffa71d3bcd388033c46de541c4a09f7f91bc03fae61a98983d1701`) defines a two-call operational machine with 6 micro-event steps (`address1`, `cost1`, `return1`, `address2Retained`/`address2Fresh`, `cost2`, `return2`), secret input `secret : Bool`, and residual state `retainedBit : Option Bool`:

1. **In `Mode.retained`:**
   - Call 1 nondeterministically picks `firstBit : Bool`, stores `retainedBit := some firstBit`, emits `MicroEvent.address .first firstBit`, charges `MicroEvent.charge .first`, and emits `MicroEvent.returned .first`.
   - Call 2 reads `firstBit` from `retainedBit` and emits `MicroEvent.address .second (xorBit firstBit secret)`, followed by `charge .second` and `returned .second`.
   - **Per-call marginals pass (`retained_marginals_noninterference`, `completed_return_cost`):** Because `xorBit false true = true` and `xorBit true true = false` is a bijection on `Bool`, the marginal projection of Call 2 alone (`SecondMarginal (.retained secret)`) emits `{[address .second false, ...], [address .second true, ...]}` for both `secret = false` and `secret = true`. Thus Call 1 and Call 2 each satisfy `FiniteNoninterference` in isolation, and every completed run returns `[0, 0]` with `logicalCost = 2`.
   - **Joint two-call execution fails (`retained_not_noninterference`, `retained_distinguishing_prefix`):** In the composed trace, the 4-event prefix
     $$\text{distinguishing} = [\text{address}(\text{first}, \text{false}),\; \text{charge}(\text{first}),\; \text{returned}(\text{first}),\; \text{address}(\text{second}, \text{false})]$$
     is reachable when `secret = false` (via `firstBit = false`, since $\text{false} \oplus \text{false} = \text{false}$) and unreachable when `secret = true` (since `firstBit = false` forces $\text{false} \oplus \text{true} = \text{true}$). Thus per-call marginal noninterference fails to imply composed possibilistic noninterference (`retained_not_noninterference`, corresponding to the conceptual property `perCallOnly_fails_composedPossibilisticNI`).
2. **In `Mode.fresh`:**
   - Call 2 nondeterministically picks a fresh `choice : Bool` independent of `retainedBit` and `secret`, satisfying `fresh_all_microevent_prefixes_noninterference`.
3. **Compositional residual-state contract (`support/CallSecurityComposition.lean`, SHA-256 `9999dac26164877aa06f31d8a634ba26053ae37c32d383589609fdbc8b421fdd`):**
   - `StageMatch Step1 Step2 Rentry Rnext` requires that for every pair of entry states $(s_1, s_2) \in R_{\text{entry}}$, every step from $s_1$ can be matched by a step from $s_2$ with the **exact same emitted event** `ev` and successor states in $R_{\text{next}}$, and vice versa (`backward`).
   - Given `StageMatch` across entry/boundary/final relations $(R_0, R_1, R_2)$, `stage_observations_iff` and `call_cut_runs_iff` prove exact composed trace equivalence across `Cut.zero`, `Cut.one`, and `Cut.two`, yielding `fresh_call_cut_noninterference`.
   - Conversely, `retained_boundary_mismatch` proves that after Call 1 emits `address .first firstBit`, the boundary states `(afterFirst false firstBit, afterFirst true firstBit)` cannot satisfy `StageMatch` for Call 2's first step, and `marginal_summary_does_not_supply_stage_contract` proves that marginal noninterference plus identical return/cost summaries do not supply a composable boundary relation.

## Boundaries

- **`not examined`:**
  - Concrete hardware timing channels (cache set/way contention, branch predictor state, speculative execution) or cycle-accurate microarchitectural models.
  - Quantitative information-flow bounds (such as Rényi or min-entropy leakage) for probabilistic channels beyond the discrete weighted-mass counterexample in `Observations.lean`.
  - Automated static analysis or type-system inference for synthesizing `StageMatch` boundary relations on arbitrary Rust MIR programs.
- **`unknown`:**
  - Minimal sufficient conditions under which relaxed (non-lockstep) observation adapters compose with state-dependent dynamic memory allocation in concurrent executions.
- **`known not to apply`:**
  - Forward simulation (`StutteringSimulation`), `NoUB`, and completed output equality do **not** bound target execution steps or transient stack depth (`ExtraTarget.safety_and_output_do_not_bound_target`, `deeper_stack_counterexample`).
  - One-way trace inclusion (`TraceCoverage` in either direction alone) does **not** preserve 2-safety possibilistic noninterference (`forward_matching_does_not_preserve_noninterference`, `trace_refinement_does_not_preserve_noninterference`).
  - Per-call marginal noninterference does **not** compose across sequential calls when unprojected residual state correlates choices across the call boundary (`retained_not_noninterference`, `marginal_summary_does_not_supply_stage_contract`).
- **`unsupported`:**
  - Secret-dependent observation adapters (`secretAdapter` in `ObservationAdapters.lean`) are unsupported as soundness justification for noninterference transport because they can absorb secret-dependent trace variations into the adapter relation (`secret_adapter_not_noninterference`).

## Evidence

All eight Lean 4.34.1 source modules and the complete revalidation ledger are archived in `support/`:

| File | Bytes | SHA-256 | Audits (Axiom-Free) | Role |
| --- | ---: | --- | ---: | --- |
| `support/PrefixAccounting.lean` | 6,958 | `4f495dca01c7561788dcd2b741958e80e146ba0ad25ea46dddf9cf2dc5669eda` | 11 (9) | Reverse target-prefix coverage `Accounting` and `ExtraTarget` unbounded-cost counterexample. |
| `support/CostStack.lean` | 19,173 | `61307e94341b2db58906b915b4172bb40fc76ba3c38a098bb3ccfa874ada1977` | 19 (4) | Recursive call/return machine, transient stack `peak` bounds, and 2-phase cost expansion. |
| `support/Observations.lean` | 15,080 | `82b65c96389e0d04f4908d47d8800ba14f14e1fba1433b497c77cbc1c33f9bf2` | 14 (11) | 2-safety possibilistic `FiniteNoninterference` and 4 negative controls (branch/address, forward, refinement, probabilistic weight). |
| `support/ObservationAdapters.lean` | 11,013 | `dfe7291e870da855aafe4545554867274c0a1a61e573eca516398465051e3eff` | 15 (6) | `PublicUniform` relational observation adapters and `secretAdapter` counterexample. |
| `support/OperationalObservations.lean` | 9,191 | `49d6187219f7717bc8d11bf80e73853b7436d1be3cdc414f549b347fa6a1537a` | 12 (2) | `LoggedPath` event-trace semantics for `CostStack` transitions. |
| `support/OperationalAdapter.lean` | 9,893 | `6f78fe1e66f7ea5157398dc391e12a2a4527dff4af1004db8eb6d65bd2b2024d` | 14 (1) | Exact operational adapter image equivalence across settled and unsettled (`armed = true`) target prefixes. |
| `support/CallSecuritySpecimens.lean` | 23,873 | `896ed03254ffa71d3bcd388033c46de541c4a09f7f91bc03fae61a98983d1701` | 15 (10) | Two-call `Mode.retained` vs. `Mode.fresh` state machine, marginal noninterference, and joint 4-event distinguishing prefix. |
| `support/CallSecurityComposition.lean` | 20,661 | `9999dac26164877aa06f31d8a634ba26053ae37c32d383589609fdbc8b421fdd` | 13 (5) | Two-sided `StageMatch` residual-state simulation and `marginal_summary_does_not_supply_stage_contract`. |
| `support/lean-check-results.json` | 41,632 | `b268ce4f43eb1d3877181872865fa9d26fea3b3f3a1755e50fc3cd6ae0760098` | — | Complete Lean 4.34.1 verification ledger (`exit_code: 0`, `.olean` digests, and `#print axioms` audits). |

## Revalidation

To revalidate all eight Lean 4.34.1 modules in topological order (after compiling base modules `Execution` and `PrefixTransfer` onto `LEAN_PATH`):

```bash
for mod in PrefixAccounting CostStack Observations ObservationAdapters OperationalObservations OperationalAdapter CallSecuritySpecimens CallSecurityComposition; do
  lean -j1 -M2048 -o "/tmp/build/AnnealResearch/${mod}.olean" "support/${mod}.lean"
done
```

Every module compiles with exit code `0`, zero warnings, and only standard Lean axioms (`propext`, `Quot.sound`, `Classical.choice` where applicable; 48 of the 113 target audits are completely axiom-free).
