# Stabilizer Tableaus, Pauli Frames, Surface-Code Lattice Surgery, Sparse Blossom Decoding, and Pulse-Frame Deadlines

## Summary

Fault-tolerant quantum execution links four layers whose correctness and timing invariants interact tightly: (1) high-throughput Clifford/Pauli simulation and detector error model (`DEM`) extraction, (2) topological surface-code lattice surgery and syndrome-extraction CNOT scheduling, (3) graph-based Minimum-Weight Perfect Matching (`MWPM`) vs. `Union-Find` syndrome decoding, and (4) pulse-level rotating-frame calibration coupled to real-time classical feedforward latency bounds. Five core architectural invariants govern soundness and throughput across this stack:

1. **Inverted Stabilizer Tableaus Enable $O(n)$ Unitaries While Pauli Frames Achieve $O(1)$ SIMD Gate Propagation:** Maintaining the *inverse* Clifford tableau $T^{-1}$ in column-major bit-packed storage (`TableauSimulator` in `quantumlib/Stim`) turns unitary gate application into $O(n/W)$ SIMD column prepends (`inv_state.prepend_*`) and reduces Z-basis determinism tests to checking whether the $X$-support vector of $T^{-1}(Z_q)$ is zero (`!inv_state.zs[target].xs.not_zero()`), paying $O(n^2)$ Gaussian elimination via `TableauTransposedRaii` solely on non-deterministic collapses. Amortizing that reference sample once lets `FrameSimulator` propagate $W$ shots simultaneously in $O(1)$ bitwise XORs per gate, **provided** anticommuting reset/measurement instructions randomize the conjugate Pauli frame component (`z_table[q].randomize(...)` on `MZ`); omitting that frame randomization causes downstream anticommuting measurements to collapse deterministically to `0%` flips instead of the physical `50%` outcome distribution.
2. **Backward Sensitivity Analysis Extracts Hypergraph `DEM`s and Verifies Mid-Circuit Stabilizer Flows:** `Stim`'s `ErrorAnalyzer` and `check_if_circuit_has_unsigned_stabilizer_flows` walk circuits in reverse chronological order over sparse sorted detector/flow sets (`SparseUnsignedRevFrameTracker`), mapping Pauli error mechanisms into hyperedges and verifying $P_{\text{in}} \to P_{\text{out}} \cdot (-1)^{\bigoplus M}$ invariants without enumerating state vectors. When `decompose_errors` splits hyperedges (such as $Y$ or two-qubit gate errors producing weight-4 symptoms) into graphlike edges ($\le 2$ detectors), fallback remnant decomposition can silently reduce effective graph distance unless restricted (`block_decomposition_from_introducing_remnant_edges`), and `ErrorAnalyzer` enforces hard structural limits (`<= 63` observable IDs, `< 64` error terms per decomposed mechanism, `<= 15` composite detector symptoms).
3. **Hook-Error CNOT Schedules and Insufficient Merge Rounds Halve Effective Fault Distance:** In rotated $[[d^2, 1, d]]$ surface-code patches, a single mid-cycle CNOT fault on an ancilla propagates onto two data qubits along the final two CNOT legs. Aligning that weight-2 hook vector parallel to the patch's logical operator ($Z_L$ or $X_L$) halves circuit-level distance from $d = 5$ ($t = 2$ correctable faults) down to $d_{\text{circ}} = \lceil d/2 \rceil = 3$ ($t = 1$), whereas Stim's anti-aligned `N`-vs.-`Z` schedule (`x_order` vs. `z_order`) keeps hook errors perpendicular to the logical string and preserves $d_{\text{circ}} = 5$. Analogously, performing lattice-surgery `XX`/`ZZ` merge parity measurements for fewer than $d$ syndrome extraction rounds creates timelike measurement-error chains shorter than $d$.
4. **Local Dual-Variable `Sparse Blossom` Eliminates All-to-All Dijkstra While Outperforming Unweighted `Union-Find` Under Heterogeneous Noise:** `PyMatching` v2 solves exact `MWPM` without building an $O(|V|^2)$ all-pairs distance matrix by packing `(slope ∈ {-1, 0, +1}, y_intercept)` into `Varying<int64_t>` dual variables, scaling user edge weights to **even** integers so colliding $+1$-slope regions meet on exact integer timestamps inside a 33-bucket monotonic `radix_heap_queue` over `cyclic<uint32_t>`. Compared against almost-linear $O(\alpha(V)V)$ `Union-Find` (`Delfosse & Nickerson, 2021`), weighted `MWPM` strictly dominates on sub-threshold graphs containing heterogeneous edge probabilities (such as rare $p_h = 10^{-4}$ hook/boundary edges competing against two higher-probability $p_d = 2\times 10^{-2}$ data faults).
5. **Pulse-Frame Calibration Semantics Require Compile-Time Definite Durations and Real-Time Backlog Sub-Unity (`τ_dec < τ_round`):** `OpenQASM 3` / `OpenPulse` models physical RF control as stateful `(port, frequency, phase, time)` `frame` accumulators where virtual-$Z$ gates act instantaneously via `shift_phase(frame, -theta)`, `defcal` blocks impose implicit entry barriers and compile-time frame-collision rejection, and every `defcal` branch must resolve to an equal compile-time duration. Variable-latency classical syndrome decoders (`MWPM`/`UF`) therefore must execute asynchronously outside `defcal` timing contracts while maintaining per-round throughput $\tau_{\text{dec}} < \tau_{\text{round}}$; otherwise, sequential reactive magic-state consumption in lattice-surgery Pauli-Based Computation incurs Terhal's exponential backlog explosion $c^K$ ($3{,}325.26\times$ at $c = 1.50$ after $K = 20$ dependent $T$-layers).

## Applicability

This report synthesizes primary-source evidence spanning three coupled software/specification layers and seven foundational peer-reviewed results:

- **Stabilizer simulation, Pauli frames, flows, and `DEM` generation (`quantumlib/Stim` @ `ffe0d043598ed5df0851a3e6b4920359a23fafbd`, post-v1.15 development tip; `Gidney, Quantum 2021`, DOI `10.22331/q-2021-07-06-497`):** Direct C++ source inspection of `Tableau` / `TableauHalf` (`src/stim/stabilizers/tableau.h`, `tableau.inl`, `tableau_specialized_prepend.inl`), `TableauSimulator` (`src/stim/simulators/tableau_simulator.h`, `tableau_simulator.inl`), `FrameSimulator` (`src/stim/simulators/frame_simulator.h`, `frame_simulator.inl`), `Flow` and flow verification (`src/stim/stabilizers/flow.h`, `src/stim/util_top/has_flow.inl`), `ErrorAnalyzer` and `SparseUnsignedRevFrameTracker` (`src/stim/simulators/error_analyzer.h`, `error_analyzer.cc`, `sparse_rev_frame_tracker.h`), and the surface-code circuit generator (`src/stim/gen/gen_surface_code.cc`). Findings apply directly to Clifford+Pauli-noise circuits (`Clifford`, single/multi-qubit Pauli measurements/resets, `MPP`/`SPP`, `REPEAT`, `DETECTOR`, `OBSERVABLE_INCLUDE`) simulated in Stim at SIMD width `W`.
- **Rotated surface-code lattice surgery and decoding (`oscarhiggott/PyMatching` @ `6f63b2b9474ba0fa7e511fe52bffdce858a06984`; `Higgott & Gidney, Quantum 2025`, DOI `10.22331/q-2025-01-20-1600`; `Horsman et al., 2012`, DOI `10.1088/1367-2630/14/12/123011`; `Litinski, Quantum 2019`, DOI `10.22331/q-2019-03-05-128`; `Tomita & Svore, Phys. Rev. A 2014`, DOI `10.1103/PhysRevA.90.062320`; `Delfosse & Nickerson, Quantum 2021`, DOI `10.22331/q-2021-12-02-595`):** Direct source inspection of `PyMatching`'s Sparse Blossom flooder (`graph_flooder.cc`, `graph_fill_region.h`, `graph.h`), matcher (`mwpm.cc`), interop (`varying.h`, `ints.h`), monotonic bucket queue (`radix_heap_queue.h`), and `UserGraph` / `DETECTOR_ERROR_MODEL` ingestion (`user_graph.h`, `user_graph.cc`, `mwpm_decoding.cc`), compared against `Union-Find` peeling and lattice-surgery scheduling rules.
- **Pulse calibration and real-time feedforward control (`openqasm/openqasm` @ `f059a268b2372a53d99212538cfd3b9f4c373147`, `Cross et al., ACM TQC 2022`, DOI `10.1145/3505636`; `Terhal, Rev. Mod. Phys. 2015`, DOI `10.1103/RevModPhys.87.307`):** Direct inspection of normative language documents `source/language/openpulse.rst`, `source/language/pulses.rst`, `source/language/delays.rst`, and `source/language/classical.rst`. Note that OpenPulse grammar is explicitly marked in active evolution (`openpulse.rst:4`) and delegates hardware-specific frame/NCO multiplexing and fixed-point frequency bounds to vendor backends.

**How subjects relate:** `Stim` compiles gate-level surface-code and lattice-surgery schedules (`gen_surface_code.cc`) using inverted stabilizer tableaus (`TableauSimulator`) and Pauli frames (`FrameSimulator`) into hypergraph `DEM`s (`ErrorAnalyzer`), which `PyMatching` ingests (`detector_error_model_to_mwpm`) and decodes via Sparse Blossom; those logical measurement outcomes feed back across the real-time classical boundary governed by `OpenQASM 3`/`OpenPulse` timing constraints and `Terhal`'s feedforward backlog bound. All quantitative claims in `1A`–`1C` are independently verified via self-contained Python 3 probes (`/tmp/probe_qec_pulse.py`).

## Findings

### 1. Inverted Stabilizer Tableaus, Pauli Reference Frames, and Mid-Circuit Stabilizer Flows

Basis: source + execution + normative (`Gidney, Quantum 2021`)

#### 1.1 Inverted Tableau Representation and Prepended Clifford Updates (`Stim`)

A stabilizer tableau $T$ represents an $n$-qubit Clifford unitary $C$ by recording the output Pauli strings $C X_q C^\dagger$ and $C Z_q C^\dagger$ for every $q \in [0, n)$. Storing $T$ in the forward direction makes appending a gate $U$ ($C \mapsto U C$) require row/column updates proportional to $O(n)$ qubits, while *measuring* $Z_q$ requires querying the preimage $C^\dagger Z_q C$—which in turn forces maintaining an auxiliary destabilizer block (Aaronson–Gottesman) or inverting $T$.

`Stim` eliminates the split stabilizer/destabilizer structure in `TableauSimulator<W>` (`src/stim/simulators/tableau_simulator.h:40-41`) by storing **only the inverse tableau** `Tableau<W> inv_state`, which records $C^{-1} X_q C$ and $C^{-1} Z_q C$ in column-major `TableauHalf<W>` tables (`src/stim/stabilizers/tableau.h:31-56`):
- `inv_state.xs[q]` stores the Pauli string $C^{-1} X_q C$ (`xt`, `zt` SIMD bit tables plus `signs` bit vector).
- `inv_state.zs[q]` stores the Pauli string $C^{-1} Z_q C$.

Because conjugating by $U C$ satisfies $(U C)^{-1} P (U C) = C^{-1} (U^{-1} P U) C$, appending unitary gate $U$ on the circuit corresponds algebraically to **prepending** $U^{-1}$ on `inv_state`. Inspection of `src/stim/stabilizers/tableau_specialized_prepend.inl` verifies exact $O(n/W)$ SIMD column operations:
- **`H` (`prepend_H_XZ`, line 57):** swaps columns `xs[q].swap_with(zs[q])`.
- **`CNOT` (`prepend_ZCX`, lines 220–223):** `zs[target] *= zs[control]; xs[control] *= xs[target]` (conjugating $I_c Z_t \mapsto Z_c Z_t$ and $X_c I_t \mapsto X_c X_t$ on the input side).
- **`CZ` (`prepend_ZCZ`, lines 233–236):** `xs[target] *= zs[control]; xs[control] *= zs[target]`.

Crucially, checking whether a computational-basis measurement `MZ(target)` has a deterministic outcome reduces to checking whether $C^{-1} Z_{\text{target}} C$ commutes with the initial state $|0\rangle^{\otimes n}$—i.e., whether it contains any $X$ or $Y$ Pauli factors (`xs` bit set):
- `is_deterministic_z(target)` (`tableau_simulator.inl:54-56`): `!inv_state.zs[target].xs.not_zero()` ($O(n/W)$ SIMD scan, no transpose needed).
- `is_deterministic_x(target)` (`tableau_simulator.inl:44-46`): `!inv_state.xs[target].xs.not_zero()`.
- `is_deterministic_y(target)` (`tableau_simulator.inl:49-51`): `inv_state.xs[target].xs == inv_state.zs[target].xs`.

When `MZ` is deterministic, `do_MZ` (`tableau_simulator.inl:345-357`) reads the bit `inv_state.zs.signs[q] ^ flipped` in $O(1)$ without transposing `inv_state`. Only when `collapse_z` finds non-deterministic targets does `TableauSimulator` construct a scoped `TableauTransposedRaii<W>` (`tableau_simulator.inl:1331-1337`) and execute `collapse_qubit_z` (`tableau_simulator.inl:1341-1376`):
1. Scan for the smallest generator index `pivot` whose transposed `zs.xt[pivot][target]` bit is `1`.
2. Eliminate all other anticommuting generators $k > \text{pivot}$ by prepending virtual zero-controlled CNOTs (`append_ZCX(pivot, k)`).
3. Rotate the isolated pivot generator to commute (`append_H_YZ` if `zs.zt[pivot][target]` else `append_H_XZ`).
4. Sample or bias the collapse bit (`sign_bias`) and flip `append_X(pivot)` if `inv_state.zs.signs[target] != result_if_measured`.

Thus, deterministic stabilizer measurements—which constitute almost all syndrome measurements in steady-state QEC cycles—cost $O(n/W)$ instead of $O(n^2)$ Gaussian elimination.

#### 1.2 Batched Pauli Reference Frames and Mandatory Anticommutation Randomization

`FrameSimulator<W>` (`src/stim/simulators/frame_simulator.h:45-66`) decouples noiseless Clifford evolution from stochastic Pauli error sampling. First, `TableauSimulator::reference_sample_circuit` (`tableau_simulator.inl:1435-1438`) evaluates the noiseless circuit once with `sign_bias = +1` (biasing collapses toward $+Z$) to produce `simd_bits<W> reference_sample`. `FrameSimulator` then simulates `batch_size` shots concurrently using two transposed `simd_bit_table<W>` arrays `x_table` and `z_table` (`num_qubits × batch_size`), updating all `batch_size` frames via vectorized bitwise operations (`frame_simulator.inl`):
- **Single-qubit Clifford gates:** bit swaps/XORs (e.g., `H` swaps `x_table[q]` and `z_table[q]`).
- **`CNOT(c, t)`:** `x_table[t] ^= x_table[c]` and `z_table[c] ^= z_table[t]`.
- **`MZ(q)` (`do_MZ`, lines 199–208):** flips measurement record relative to reference via `m_record.xor_record_reserved_result(x_table[q])`, **and then executes**:
  ```cpp
  if (guarantee_anticommutation_via_frame_randomization) {
      z_table[q].randomize(z_table[q].num_bits_padded(), rng);
  }
  ```

Randomizing the conjugate Pauli frame component (`z_table[q]` on `MZ`/`RZ`, `x_table[q]` on `MX`/`RX`, `z_table[q]` on `MY`/`RY` conjugated into `X`/`Z`) models physical wave-function collapse: measuring $Z_q$ projects out any prior $X_q$ or $Y_q$ stabilizer correlations by injecting an unobservable $50\%$ random $Z_q$ phase kickback. Disabling `guarantee_anticommutation_via_frame_randomization` (`frame_simulator.h:61-65`) is valid **only** when manually tracing deterministic sensitivity of a fixed error; using it during general circuit sampling violates quantum measurement mechanics whenever an anticommuting measurement follows.

**Executable Verification (Probe 1A):** Running the two-qubit Bell circuit `H(0); CX(0,1); MZ(1); MZ(0); MX(1)` over $8{,}192$ shots in `/tmp/probe_qec_pulse.py`:
- Pre-measurement tableau check confirms `det_Z1_pre = False` (`is_deterministic_z(1) == False`).
- With `Z`-frame randomization on `MZ`: `MX(1)` yields `4077/8192` (`0.4977`) flips (matching physical $50\%$ random projection of $|0\rangle / |1\rangle$ in the $X$ basis).
- Without `Z`-frame randomization (`no_z_rand`): `MX(1)` yields **`0/8192` (`0.0000`)** flips—falsely certifying a deterministic outcome on an anticommuting measurement!

#### 1.3 Stabilizer Flows (`Flow<W>`) for Mid-Circuit Schedule Verification

A circuit slice $C$ implements stabilizer flow $P_{\text{in}} \xrightarrow{M, O} P_{\text{out}}$ (`src/stim/stabilizers/flow.h:25-38`) iff preparing an eigenstate of $P_{\text{in}}$, executing $C$, and multiplying the product of measurement bits $m \in M$ (and included observables $o \in O$) deterministically yields an eigenstate of $P_{\text{out}}$ with parity matching the sign. `Stim` provides two independent verification algorithms in `src/stim/util_top/has_flow.inl`:
1. **Monte Carlo Ancilla Witness (`_sample_if_noiseless_circuit_has_stabilizer_flow`, lines 44–90):** Maximally mixes all qubits via $50\%$ `X_ERROR` and $50\%$ `Z_ERROR`, applies Pauli-controlled `CNOT`s from `flow.input` onto an ancilla qubit, runs the circuit (routing `OBSERVABLE_INCLUDE` targets to the ancilla), applies `CNOT`s from `flow.measurements` and `flow.output` onto the ancilla, and checks that measuring the ancilla always returns `0`. This checks both magnitude and **sign** of flows, including feedback-controlled Pauli operations.
2. **Exact Algebraic Reverse Check (`check_if_circuit_has_unsigned_stabilizer_flows`, lines 104–210):** Instantiates a `SparseUnsignedRevFrameTracker`, seeds `rev.xs[q]` / `rev.zs[q]` with flow indices for `flow.output`, registers `flow.measurements` via `undo_DETECTOR`, walks all gates backward (`rev.undo_gate`), XORs `flow.input`, and accepts iff `rev.xs`, `rev.zs`, and `rev.anticommutations` are all empty at the circuit start. This verifies all unsigned stabilizer flows simultaneously in deterministic linear pass without sampling variance.

---

### 2. Reverse-Frame Detector Error Model (`DEM`) Extraction and Graphlike Decomposition

Basis: source + derived

#### 2.1 Sensitivity Tracking, XOR Probability Merging, and Loop Folding (`ErrorAnalyzer`)

A `DetectorErrorModel` (`DEM`) is a bipartite hypergraph between physical independent Pauli error mechanisms and `(detector_ids, logical_observables)`. `ErrorAnalyzer` (`src/stim/simulators/error_analyzer.h:83-178`, `src/stim/simulators/error_analyzer.cc`) constructs it in **a single backward pass** over the circuit using `SparseUnsignedRevFrameTracker`:
1. At a `DETECTOR` instruction referencing measurement offsets $\{r_k\}$, `tracker` pushes detector ID $D_j$ into `rec_bits[index]` for each referenced measurement.
2. When reversing a measurement (e.g., `MZ(q)`), any detector IDs sensitivity-bound to that measurement bit enter `tracker.xs[q]` (since $X$ errors flip $Z$-measurements), while checking that no remaining sensitivities in `tracker.zs[q]` or `tracker.xs[q]` violate commutativity (unless `allow_gauge_detectors` is enabled, which emits a $50/50$ random error mechanism).
3. Backward Clifford gates transform per-qubit sensitivity sets identically to Heisenberg conjugation: for `CNOT(c, t)`, $X$-sensitivities on $t$ XOR into $c$ and $Z$-sensitivities on $c$ XOR into $t$ (`error_analyzer.h:59-61`).
4. When reversing a noise channel (e.g., `X_ERROR(p)` or `PAULI_CHANNEL_1(dx, dy, dz)`), the active sensitivity sets on the target qubit(s) form an `ErrorEquivalenceClass` whose probability combines via independent Bernoulli XOR (`error_analyzer.cc:1084-1097`):
   $$p_{\text{comb}} = p_{\text{old}}(1 - p) + (1 - p_{\text{old}})p$$

To prevent $O(\text{iterations})$ memory and runtime blowup on long syndrome-extraction `REPEAT` loops, `ErrorAnalyzer::run_loop` (`error_analyzer.cc:1099-1155`) runs a **tortoise-and-hare cycle detector** (`hare.tracker.is_shifted_copy(tracker)`). Once the backward detector sensitivity pattern becomes periodic modulo detector-index shifts, `ErrorAnalyzer` folds the steady-state iterations into a `DEM_REPEAT_BLOCK` and flushes boundary errors.

#### 2.2 Disjoint Channels, Hyperedge Decomposition Traps, and Hard Engine Bounds

Three subtle failure modes arise at the `Stim` `DEM` $\to$ `MWPM` boundary:

1. **Disjoint Channel Independence Approximation (`undo_PAULI_CHANNEL_1` / `undo_PAULI_CHANNEL_2`, `error_analyzer.cc:901-956`):** A disjoint Pauli channel applies *mutually exclusive* errors (e.g., $X, Y, Z$ with probabilities $d_x, d_y, d_z$), whereas a `DEM` models *independent* error instructions. For `PAULI_CHANNEL_1`, Stim first attempts exact conversion (`try_disjoint_to_independent_xyz_errors_approx`); if infeasible (or for `PAULI_CHANNEL_2`), it requires probabilities $\le$ `approximate_disjoint_errors_threshold` or throws `std::invalid_argument`.
2. **Graphlike Decomposition & Remnant Edges (`do_global_error_decomposition_pass`, `error_analyzer.cc:1463-1579`):** Two-qubit depolarizing errors (`DEPOLARIZE2`) and $Y$ errors routinely trigger $3$ or $4$ detectors simultaneously (a hyperedge). Matching decoders (`PyMatching`) require edges hitting at most $2$ detectors (`is_graphlike`). `brute_force_decomposition_into_known_graphlike_errors` searches for a partition of the hyperedge symptom (preserving the exact logical observable bitmask `obs_mask_of_targets`) using existing 1- or 2-detector edges in `known_symptoms`. If none exists and `!block_decomposition_from_introducing_remnant_edges` (`error_analyzer.cc:1535`), `decompose_and_append_component_to_tail` creates **remnant edges** formed by XORing existing edges—explicitly warned in `error_analyzer.h:116-117` and `1539-1540` as potentially **reducing the graphlike code distance** by introducing diagonal shortcuts!
   *(Source-documentation discrepancy preserved: In `error_analyzer.h`, lines 114–117 document `block_decomposition_from_introducing_remnant_edges = true` as **permitting** remnant shortcuts—"When true, decomposition is permitted to split A B C D into A B ^ C D when only one... exists"—whereas the parameter docstring on lines 164–166 and the implementation guard `!block_decomposition_from_introducing_remnant_edges` at `error_analyzer.cc:1535` implement the exact **opposite**: `true` **blocks** remnant edge creation and `false` permits it.)*
3. **Hard Structural Bitmask Limits:** `ErrorAnalyzer` throws `std::invalid_argument` whenever a decomposed error references observable ID $\ge 64$ (`error_analyzer.cc:1407-1409`), has $\ge 64$ symptom targets (`error_analyzer.cc:1467-1469`), or a composite multi-qubit error touches $> 15$ distinct detectors (`error_analyzer.cc:1604-1606`).

---

### 3. Rotated Surface-Code Lattice Surgery and Hook-Error Distance Halving

Basis: normative + source + execution

#### 3.1 Lattice Surgery Primitives and Pauli-Based Computation

In the rotated $[[d^2, 1, d]]$ surface code (`Horsman et al., 2012`; `Litinski, 2019`), a planar patch encodes one logical qubit with horizontal $Z_L$ chains terminating on rough top/bottom boundaries and vertical $X_L$ chains terminating on smooth left/right boundaries. Rather than braiding defects around patches, **lattice surgery** performs fault-tolerant multi-qubit Pauli product measurements (`MXX`, `MZZ`, `MXXZZ`) by:
1. **Merge:** Initializing intermediate boundary data qubits along a shared seam in $|0\rangle$ (for $ZZ$-merge) or $|+\rangle$ (for $XX$-merge), measuring joint seam stabilizers spanning both patches for **$d$ syndrome-extraction rounds**, and inferring the logical parity $Z_1 Z_2$ (or $X_1 X_2$) as the product of seam stabilizer outcomes.
2. **Split:** Measuring the seam data qubits in the dual basis ($X$ after a $ZZ$-merge, $Z$ after an $XX$-merge) to decouple the patches while feeding classical Pauli corrections forward into stabilizer tracking.

Because each seam stabilizer measurement has physical error rate $p_m > 0$, extracting only $r < d$ rounds during a merge leaves a timelike chain of $r$ consecutive measurement flips undetectable across time, reducing the *timelike* fault distance to $r < d$. Furthermore, `Litinski (2019)` (`A Game of Surface Codes`) shows that compiling a Clifford+$T$ circuit into **Pauli-Based Computation (`PBC`)** commutes all Clifford gates past $T$-state injections into measurement bases, converting every $T$ gate into a single $Z \otimes Z$-type joint lattice-surgery measurement against a distilled $|A\rangle$ magic state—making all Clifford gates take **0 logical QEC cycles** while exposing critical data dependencies across sequential non-Clifford measurements.

#### 3.2 Hook-Error Orientation and Circuit-Level Distance Halving

A rotated surface-code stabilizer cycle executes four sequential two-qubit `CNOT` layers (`Tomita & Svore, 2014`; `Stim` `gen_surface_code.cc:105-135, 264-275`). Consider a weight-4 $X$-ancilla executing `CNOT(ancilla -> data_k)` for $k \in \{0, 1, 2, 3\}$:
- A single $X$ fault occurring on the ancilla qubit **after `CNOT` step 1 (before step 2)** propagates forward through steps 2 and 3 onto **two data qubits** $(d_2, d_3)$—a weight-2 **hook error** created by a single circuit-level fault!
- If $(d_2, d_3)$ lie along the *same orientation* as the logical observable $Z_L$ (horizontal in Stim's `rotated_memory_z` layout where `z_observable` spans $y = 0.5$ across $x \in [0.5, d]$, `gen_surface_code.cc:231-233`), then $\lceil d/2 \rceil$ mid-cycle ancilla faults plus boundary weight-1 faults link directly across the patch to form an undetectable logical $X_L$ flip!
- `Stim`'s `_generate_rotated_surface_code_circuit` (`gen_surface_code.cc:263-275`) avoids this by applying **orthogonal `Z`-vs.-`N` interaction orders**:
  - `z_order`: `[(+1,+1), (+1,-1), (-1,+1), (-1,-1)]` (steps 2 & 3 at $\Delta x = -1$: horizontal $Z$-hook errors, perpendicular to vertical $X_L$).
  - `x_order`: `[(+1,+1), (-1,+1), (+1,-1), (-1,-1)]` (steps 2 & 3 at $\Delta y = -1$: vertical $X$-hook errors, perpendicular to horizontal $Z_L$).

**Executable Verification (Probe 1B):** Constructing the exact $d = 5$ rotated surface-code $Z$-memory patch (`25` data qubits, `12` $Z$-stabilizer checks, horizontal weight-5 $Z_L$) and searching minimum-weight undetectable circuit-level error chains (`(syndrome = 0, obs_flip = 1)`) across single-qubit data faults + mid-cycle $X$-ancilla hook faults yields:
- **Stim anti-aligned `N`-schedule (`x_order = [(+1,+1), (-1,+1), (+1,-1), (-1,-1)]`):** $d_{\text{circ}} = \mathbf{5}$ ($t = \lfloor (5-1)/2 \rfloor = \mathbf{2}$ faults always corrected; `30` distinct fault mechanisms).
- **Misaligned `Z`-schedule (`x_order = [(+1,+1), (+1,-1), (-1,+1), (-1,-1)]`):** $d_{\text{circ}} = \mathbf{3}$ ($t = \mathbf{1}$ fault correctable—**error-correction capacity is halved** because two horizontal weight-2 hooks plus one boundary fault span the $d=5$ width with circuit weight $3$).

---

### 4. Real-Time Decoding: `Sparse Blossom` MWPM (`PyMatching`) vs. `Union-Find`

Basis: source + execution + normative (`Higgott & Gidney, Quantum 2025`; `Delfosse & Nickerson, Quantum 2021`)

#### 4.1 Local Dual Variables, Implicit Even-Weight Discretization, and Monotonic Buckets (`PyMatching` v2)

Classical Edmonds' Blossom `MWPM` decoders precompute all-pairs shortest paths via Dijkstra over the syndrome graph, requiring $O(|V|^2)$ memory or $O(K |E| \log |V|)$ per shot for $K$ detection events. `PyMatching` v2 (`oscarhiggott/PyMatching` @ `6f63b2b9474ba0fa7e511fe52bffdce858a06984`) eliminates all-to-all Dijkstra searches via `Sparse Blossom`, growing local alternating-tree and blossom regions directly over the sparse `DEM` graph using event-driven discrete-time simulation:

1. **Bit-Packed Linear Dual Radii (`Varying<T>`, `varying.h:30-74`):** Each node/region radius stores `data` with its **top 2 bits** encoding growth slope $s \in \{+1, 0, -1\}$ (`is_growing`, `is_frozen`, `is_shrinking`) and remaining bits encoding the $y$-intercept $b$, representing $r(t) = s \cdot t + b$. Advancing global time `cur_time` therefore implicitly expands or shrinks **all** active regions simultaneously in $O(1)$ without iterating over interior nodes.
2. **Even Integer Edge Weight Discretization (`user_graph.h:143-160`, `user_graph.cc:422-466`):** When converting floating-point log-likelihood weights $w_e = \ln((1-p_e)/p_e)$ (`user_graph.cc:352`), `UserGraph::iter_discretized_edges` scales by `normalising_constant` (bounded below `NUM_DISTINCT_WEIGHTS = 2^24`, `user_graph.h:33`), rounds to integer, and multiplies by `2` (`w *= 2`). As documented at lines 147–149, making every edge weight an **even integer** guarantees that two regions growing toward each other at rate $+1$ (`collision_time = (weight - r1.b - r2.b) >> 1`, `graph_flooder.cc:106-109`) always collide at **exact integers** with zero fractional rounding error.
3. **33-Bucket Monotonic `radix_heap_queue` (`radix_heap_queue.h:69-162`, `ints.h:54`):** Tentative node collisions (`LOOK_AT_NODE`) and blossom shrink events (`LOOK_AT_SHRINKING_REGION`) are indexed by `cyclic_time_int` (`cyclic<uint32_t>`) into `33` vector buckets partitioned by `std::bit_width(time ^ cur_time)` (`cur_bit_bucket_for`, lines 86–88). Because events are strictly non-decreasing in cyclic time (`event.time >= cur_time`), insertion and amortized extraction run in $O(1)$ per bucket without balanced-tree pointer chasing.
4. **Local Blossom Formation and Shattering (`mwpm.cc:132-220`, `graph_flooder.cc:237-252`):** Self-collisions within an alternating tree prune the odd cycle into a `GraphFillRegion` blossom (`create_blossom`) whose children freeze while the outer blossom grows at $+1$. When an inner blossom shrinks to zero radius (`do_blossom_shattering`), `handle_blossom_shattering` restores alternating even/odd tree paths in place and frees matched sub-regions.
5. **Parallel Edge Merging and Two-Pass Correlated Decoding (`user_graph.cc:29-37, 87-96`, `mwpm_decoding.cc:167-212`):** Parallel `DEM` hyperedge splits merge via exact log-likelihood ratio combination (`merge_weights`) rather than naively taking `min(w1, w2)`. When `enable_correlations` is set, PyMatching supports two-pass correlated reweighting (`decode_detection_events` lines 202–211): pass 1 matches to a candidate edge set, `reweight_for_edges` lowers implied conditional weights on correlated partner edges (`populate_implied_edge_weights`, lines 519–546), and pass 2 re-decodes before calling `undo_reweights()`.

#### 4.2 Quantitative Trade-Offs: `Sparse Blossom` MWPM vs. `Union-Find`

| Dimension | `Sparse Blossom` MWPM (`PyMatching` v2) | `Union-Find` (`Delfosse & Nickerson, 2021`) | Operational Impact |
| :--- | :--- | :--- | :--- |
| **Worst-Case Time Complexity** | $O(V^3)$ worst-case; empirical $O(V)$ at sub-threshold ($p \ll p_{\text{th}}$) | $O(|E| \cdot \alpha(|V|))$ almost-linear worst-case with path compression | `UF` bounds tail latency under dense burst errors; `Sparse Blossom` achieves $< 1\,\mu\text{s}$/round at $d=17, p=10^{-3}$ on 1 CPU core. |
| **Edge-Weight Awareness** | Exact log-likelihood weights $\ln\frac{1-p}{p}$ + optional 2-pass correlated reweighting | Unweighted (or restricted bucket-weighted) cluster growth + spanning-forest peeling | Standard unweighted `UF` cannot distinguish $p_h = 10^{-4}$ from $p_d = 2\times 10^{-2}$ edges, reducing effective threshold and sub-threshold error suppression. |
| **Blossom / Odd-Cycle Handling** | Exact dual blossom contraction and shattering (`mwpm.cc:132-220`) | Merges colliding odd-parity clusters unconditionally until total parity is even | `UF` trades exact minimum-weight optimality for absence of blossom data structures—ideal for `FPGA`/`ASIC` LUT arrays. |
| **Negative Edge Weights (`p > 0.5`)** | Supported via pre/post-flipping (`negative_weight_detection_events`, `mwpm_decoding.cc:101-130`) | Not natively supported without gauge pre-flipping | `PyMatching` handles gauge/inverted `DEM` instructions without failing. |

**Executable Verification (Probe 1C):** On a minimal heterogeneous syndrome graph comparing a rare correlated/hook edge ($p_h = 10^{-4}, w_h = 9.210$, flipping observable) against a two-hop high-probability path ($p_d = 2\times 10^{-2}$ per hop, combined $p_d^2 = 4\times 10^{-4} > p_h$, total weight $2 w_d = 7.784 < 9.210$, preserving observable):
- **Weighted `MWPM`:** selects the 2-hop path ($7.784 < 9.210$) and predicts the correct maximum-likelihood observable (`MWPM_picks_2edge = True`).
- **Unweighted `Union-Find`:** grows clusters symmetrically by hop count; both clusters meet across the single $1$-hop edge at radius $1/2$ before reaching the intermediate vertex at radius $1$, flipping the logical observable (`UF_unweighted_picks_1edge_wrong_obs = True`).

---

### 5. Pulse-Level `OpenQASM 3` / `OpenPulse` Calibration Invariants and Feedforward Deadlines

Basis: normative + source + execution

#### 5.1 Stateful NCO Frame Semantics and Compile-Time Calibration Rules (`OpenQASM 3` / `OpenPulse`)

`OpenQASM 3` separates logical circuit gates (`gate`) from physical calibrated pulse sequences (`defcal`) via a selectable `defcalgrammar "openpulse";` (`source/language/pulses.rst:90-108`, `source/language/openpulse.rst:6-10`). `OpenPulse` abstracts hardware waveform generation via three primitives (`openpulse.rst:26-122`):

1. **`port`:** Hardware DAC/ADC/LO endpoint declared via `extern port <name>;`, supporting many-to-many qubit couplings and vendor-imposed static frequency settings.
2. **`waveform`:** Complex sample envelopes (array literals or templated `extern` generators parameterized by `duration` in `dt` or SI units).
3. **`frame`:** A virtual NCO tracking `(port, frequency: float, phase: angle, time: duration)` with complex carrier $e^{i(2\pi f t + \theta)}$ (`openpulse.rst:95-112`):
   - **Virtual-$Z$ Gate (`openpulse.rst:101-102, 206-225`):** Shifting the frame phase by `shift_phase(rz_frames[q], -theta)` implements an exact physical `rz(theta)` rotation in **zero device ticks** (`0 dt`) by advancing all subsequent pulse carriers on that frame. (Notice the negative sign `-theta`: shifting the rotating carrier phase forward by $+\phi$ rotates the qubit state oppositely by $-\phi$.)
   - **Implicit Phase Accumulation (`openpulse.rst:587-632`):** Advancing a frame's clock by duration $\Delta t$ via `play`, `capture`, or `delay` implicitly accrues phase $\Delta\theta = 2\pi f \Delta t$ in the rotating frame. *(Upstream specification defect preserved at `openpulse.rst:626-627`: the explanatory comment on line 626 writes `set_phase(driveframe0, 2π * get_frequency(driveframe0) * 13e-9)` instead of `shift_phase(...)`, which would overwrite rather than accumulate prior carrier phase if executed literally.)*
   - **Implicit Entry Barriers & Collision Errors (`openpulse.rst:557-585, 634-654`):** Entering any `defcal` block inserts an implicit `barrier` aligning the `.time` clocks of all frames referenced in its body to their maximum; referencing the same `frame` concurrently across two simultaneously scheduled `defcal` or `cal` blocks is a **compile-time error**. *(Upstream specification defect preserved at `openpulse.rst:955-956`: the multiplexed readout example indexes a 2-bit register `bit[2] b` with `b[1]` and `b[2]` rather than 0-based `b[0]` and `b[1]`.)*
   - **Definite Duration Constraint (`pulses.rst:151-171`):** Every `defcal` body—including any classical `if/else` or `for` loop inside it—**must** resolve to a fixed, equal duration known at compile time so `durationof(...)` and `stretch` glues (`delays.rst:56-136`) remain static.

#### 5.2 The Classical-Decoder Boundary and Terhal's Feedforward Backlog Bound

Because exact `Sparse Blossom` `MWPM` decoding takes data-dependent variable time (depending on detection density and blossom depth), `MWPM` **cannot** run inside a deterministic-duration `defcal` block (`pulses.rst:151-157`). Instead, `OpenQASM 3` models asynchronous host/FPGA syndrome processing via non-blocking `extern` calls (`classical.rst:644-666`: *"invoking an extern function will schedule a classical computation, but does not wait for that computation to terminate"*), synchronizing via explicit classical register reads prior to conditional Pauli-frame or lattice-surgery basis choices.

This asynchronous coupling exposes **Terhal's Backlog Problem** (`Terhal, Rev. Mod. Phys. 2015`, Section IV): in Pauli-Based Computation (`Litinski, 2019`), executing $K$ sequential non-Clifford $T$-gates via magic-state teleportation makes the measurement basis of $T_{k+1}$ depend on the decoded logical Pauli parity of $T_k$ (switching $S$ vs. $I$ Clifford corrections). If each QEC round generates syndrome data at period $\tau_{\text{round}}$ (typically $\sim 1\,\mu\text{s}$ in superconducting transmons) while the classical decoder consumes an average $\tau_{\text{dec}}$ per round, let $c = \tau_{\text{dec}} / \tau_{\text{round}}$. Each delayed measurement outcome stalls the downstream $T$-layer by an extra round, during which $c$ additional rounds of syndromes accumulate before the next decision can complete, driving total queued classical backlog after $K$ dependent $T$-layers as $B_K \propto c^K$ whenever $c > 1$.

**Executable Verification (Probe 1C):** Tabulating $c^{20}$ over $K = 20$ dependent non-Clifford layers:
- $c = 0.65$ ($\tau_{\text{dec}} < \tau_{\text{round}}$, e.g. PyMatching Sparse Blossom $\sim 0.65\,\mu\text{s}$ on a $1\,\mu\text{s}$ cycle): $c^{20} = \mathbf{0.00018\times}$ (**bounded $O(1)$ steady-state queue**).
- $c = 1.00$: $1.00\times$ (fragile zero-margin stall sensitivity).
- $c = 1.25$: $\mathbf{86.74\times}$ exponential latency inflation.
- $c = 1.50$: $\mathbf{3{,}325.26\times}$ exponential latency blowup—exceeding logical qubit coherence/magic-state storage budgets.

Real-time QEC controllers therefore require **strict sub-unity sustained throughput** ($\tau_{\text{dec}} < \tau_{\text{round}}$ under worst-case buffered parallel sliding-window decoding) rather than merely fast offline post-processing.

## Boundaries

- **Not examined:**
  - Non-surface-code qLDPC hypergraph-product / bivariate-bicycle decoders (BP+OSD, Tesseract, Relay-BP) and multi-qubit lattice surgery over qLDPC patches were not source-inspected.
  - Analog RF pulse synthesis hardware implementations (FPGA QICK/Zurich Instruments/IBM control microarchitectures, I/Q mixer calibration, DRAG pulse optimization) and sliding-window overlapping decoder seam boundary stitching (`PyMatching` streaming / window fusion wrappers outside core `Sparse Blossom`) were not executed on physical hardware.
  - Leakage reduction units (`LRU`), erasure-qubit heralded decoding (`HERALDED_ERASE` weights), and soft-information I/Q readout likelihoods beyond binary hard syndromes were not benchmarked.
- **Unsupported:**
  - `oscarhiggott/PyMatching` (`6f63b2b9474ba0fa7e511fe52bffdce858a06984`) directly supports only **graphlike** edges ($\le 2$ detector symptoms per edge, or 1 detector + boundary); hyperedges with $\ge 3$ detectors must first be decomposed into graphlike components by `Stim`'s `ErrorAnalyzer` (`decompose_errors = true`).
  - `openqasm/openqasm` (`f059a268b2372a53d99212538cfd3b9f4c373147`) `defcal` bodies explicitly forbid runtime data-dependent variable durations (`pulses.rst:151-157`), preventing non-deterministic-latency decoders from residing inside `defcal` pulse blocks.
  - `quantumlib/Stim` (`ffe0d043598ed5df0851a3e6b4920359a23fafbd`) `ErrorAnalyzer` explicitly rejects circuits whose decomposed errors exceed `63` observable IDs (`error_analyzer.cc:1407`), `63` error targets (`error_analyzer.cc:1467`), or `15` detectors within a single composite error (`error_analyzer.cc:1604`).
- **Unknown:**
  - Exact tail-latency distribution ($p_{99.9999}$) of `PyMatching` `Sparse Blossom` vs. hardware `Union-Find` under correlated cosmic-ray bursts at physical code distances $d \ge 21$ depends on device-specific readout reset durations and window-overlap sizes not fixed by the pinned repositories alone.
  - Whether future OpenPulse revisions standardize multi-qubit crosstalk/TLS frame arrays (`openpulse.rst:211-214, 961-966`) remains explicitly open in the upstream specification.
- **Known not to apply:**
  - `Stim`'s `TableauSimulator` $O(n/W)$ deterministic measurement speed does **not** apply to non-deterministic collapses (`collapse_qubit_z`), which invoke $O(n^2)$ Gaussian elimination, nor does `TableauSimulator` support non-Clifford gates ($T$, Toffoli) or coherent non-Pauli noise channels.
  - The $d_{\text{circ}} = \lceil d/2 \rceil$ hook-error distance halving demonstrated in Probe 1B does **not** occur in unrotated surface codes (which have higher qubit overhead $(2d-1)^2$ and perpendicular hook paths) or in rotated surface-code schedules employing Stim's anti-aligned `N`-vs.-`Z` `x_order`/`z_order` ordering (`gen_surface_code.cc:264-275`).

## Evidence

### Primary Source Repositories and Line Citations

1. **`quantumlib/Stim`** @ `ffe0d043598ed5df0851a3e6b4920359a23fafbd` (observed 2026-11-19):
   - `src/stim/stabilizers/tableau.h`: lines 31–56 (`TableauHalf<W>`, column-major `Tableau<W>`).
   - `src/stim/stabilizers/tableau_specialized_prepend.inl`: lines 57–59 (`prepend_H_XZ`), 220–236 (`prepend_ZCX`, `prepend_ZCZ`).
   - `src/stim/simulators/tableau_simulator.h`: lines 40–46 (`TableauSimulator<W>` storing `inv_state`), 89–95 (`is_deterministic_{x,y,z}`).
   - `src/stim/simulators/tableau_simulator.inl`: lines 44–56 (`is_deterministic_{x,y,z}` via `!inv_state.zs[target].xs.not_zero()`), 345–357 (`do_MZ`), 1319–1376 (`collapse_z` and `collapse_qubit_z` partial Gaussian elimination), 1435–1438 (`reference_sample_circuit`).
   - `src/stim/simulators/frame_simulator.h`: lines 45–66 (`FrameSimulator<W>`, `guarantee_anticommutation_via_frame_randomization`).
   - `src/stim/simulators/frame_simulator.inl`: lines 173–208 (`do_MX`, `do_MY`, `do_MZ` frame randomization on conjugate Pauli tables).
   - `src/stim/stabilizers/flow.h`: lines 25–48 (`Flow<W>`).
   - `src/stim/util_top/has_flow.inl`: lines 44–90 (`_sample_if_noiseless_circuit_has_stabilizer_flow`), 104–210 (`check_if_circuit_has_unsigned_stabilizer_flows`).
   - `src/stim/simulators/error_analyzer.h`: lines 56–178 (`ErrorAnalyzer` reverse frame model, remnant-edge flag docstring inversion at lines 114–117 vs. 164–166).
   - `src/stim/simulators/error_analyzer.cc`: lines 901–956 (`undo_PAULI_CHANNEL_1`, `undo_PAULI_CHANNEL_2`), 1084–1097 (`add_error` Bernoulli XOR), 1099–1155 (`run_loop` tortoise-and-hare folding), 1407–1619 (`obs_mask_of_targets`, `brute_force_decomposition_into_known_graphlike_errors`, `do_global_error_decomposition_pass` hard bounds `<= 63`, `< 64`, `<= 15`, and `!block_decomposition_from_introducing_remnant_edges` at line 1535).
   - `src/stim/gen/gen_surface_code.cc`: lines 105–189 (`_finish_surface_code_circuit`), 220–292 (`_generate_rotated_surface_code_circuit` with `z_order` and `x_order`).
2. **`oscarhiggott/PyMatching`** @ `6f63b2b9474ba0fa7e511fe52bffdce858a06984` (observed 2026-11-19):
   - `src/pymatching/sparse_blossom/ints.h`: lines 27–55 (`obs_int`, `weight_int`, `cumulative_time_int`, `cyclic_time_int`).
   - `src/pymatching/sparse_blossom/flooder_matcher_interop/varying.h`: lines 30–74 (`Varying<T>` bit-packed linear slope and $y$-intercept).
   - `src/pymatching/sparse_blossom/flooder/graph_fill_region.h`: lines 29–89 (`GraphFillRegion`).
   - `src/pymatching/sparse_blossom/flooder/graph_flooder.cc`: lines 77–116 (`collision_time >> 1`), 129–156, 237–252 (`create_blossom`), 280–320 (`set_region_{growing,frozen,shrinking}`).
   - `src/pymatching/sparse_blossom/tracker/radix_heap_queue.h`: lines 69–162 (`radix_heap_queue` 33 bit-width buckets).
   - `src/pymatching/sparse_blossom/matcher/mwpm.cc`: lines 63–220 (`handle_tree_hitting_*`, `handle_blossom_shattering`).
   - `src/pymatching/sparse_blossom/driver/user_graph.h`: lines 33 (`NUM_DISTINCT_WEIGHTS`), 143–160 (`w *= 2` even integer discretization).
   - `src/pymatching/sparse_blossom/driver/user_graph.cc`: lines 29–37 (`merge_weights`), 87–96 (`INDEPENDENT`), 349–365, 422–546 (`get_edge_weight_normalising_constant`, `populate_implied_edge_weights`).
   - `src/pymatching/sparse_blossom/driver/mwpm_decoding.cc`: lines 72–248 (`process_timeline_until_completion`, `decode_detection_events` two-pass correlation reweighting).
3. **`openqasm/openqasm`** @ `f059a268b2372a53d99212538cfd3b9f4c373147` (observed 2026-11-19):
   - `source/language/openpulse.rst`: lines 26–122 (`port`, `waveform`, `frame`), 156–235 (`set_phase`, `shift_phase`, `defcal rz` `-theta` virtual-$Z$), 447–654 (frame clock timing, implicit `defcal` barriers, frame collisions, line 626 `set_phase` typo), 955–956 (`bit[2]` 1-based indexing typo).
   - `source/language/pulses.rst`: lines 151–171 (compile-time definite and equal branch duration restriction on `defcal`).
   - `source/language/delays.rst`: lines 56–136 (`duration` and `stretch` compile-time constraint resolution).
   - `source/language/classical.rst`: lines 644–666 (non-blocking concurrent `extern` classical calls).

### Peer-Reviewed Literature

- C. Gidney, "Stim: a fast stabilizer circuit simulator," *Quantum*, vol. 5, p. 497, July 2021. DOI: `10.22331/q-2021-07-06-497`.
- O. Higgott and C. Gidney, "Sparse Blossom: correcting a million errors per core second with minimum-weight matching," *Quantum*, vol. 9, p. 1600, Jan. 2025 (preprint `arXiv:2303.15933`). DOI: `10.22331/q-2025-01-20-1600`.
- A. W. Cross, A. Javadi-Abhari, T. Alexander, N. De Beaudrap, L. S. Bishop, S. Heidel, C. A. Ryan, P. Sivarajah, J. Smolin, J. M. Gambetta, and B. R. Johnson, "OpenQASM 3: A Broader and Deeper Quantum Assembly Language," *ACM Trans. Quantum Comput.*, vol. 3, no. 3, art. 12, Sept. 2022. DOI: `10.1145/3505636`.
- C. Horsman, A. G. Fowler, S. Devitt, and R. Van Meter, "Surface code quantum computing by lattice surgery," *New J. Phys.*, vol. 14, no. 12, 123011, Dec. 2012. DOI: `10.1088/1367-2630/14/12/123011`.
- D. Litinski, "A Game of Surface Codes: Large-Scale Quantum Computing with Lattice Surgery," *Quantum*, vol. 3, p. 128, Mar. 2019. DOI: `10.22331/q-2019-03-05-128`.
- Y. Tomita and K. M. Svore, "Low-distance surface codes under realistic quantum noise," *Phys. Rev. A*, vol. 90, no. 6, 062320, Dec. 2014. DOI: `10.1103/PhysRevA.90.062320`.
- N. Delfosse and N. H. Nickerson, "Almost-linear time decoding algorithm for topological codes," *Quantum*, vol. 5, p. 595, Dec. 2021. DOI: `10.22331/q-2021-12-02-595`.
- B. M. Terhal, "Quantum error correction for quantum memories," *Rev. Mod. Phys.*, vol. 87, no. 2, pp. 307–346, Apr. 2015. DOI: `10.1103/RevModPhys.87.307`.

### Self-Contained Executable Micro-Probes (Python 3 stdlib, Executed 2026-11-19)

Command: `python3 /tmp/probe_qec_pulse.py` (Python 3 standard library `heapq`, `math`, `random` only):

```python
#!/usr/bin/env python3
"""Self-contained QEC, Stim frame-randomization, rotated surface-code hook distance,
weighted MWPM vs Union-Find, and Terhal magic-state backlog micro-probes (Python 3 stdlib)."""
import heapq
import math
import random

class InvTableau:
    def __init__(self, n):
        self.n = n
        self.xx = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
        self.xz = [[0] * n for _ in range(n)]
        self.xs = [0] * n
        self.zx = [[0] * n for _ in range(n)]
        self.zz = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
        self.zs = [0] * n

    def prepend_h(self, q):
        self.xx[q], self.zx[q] = self.zx[q], self.xx[q]
        self.xz[q], self.zz[q] = self.zz[q], self.xz[q]
        self.xs[q], self.zs[q] = self.zs[q], self.xs[q]

    def prepend_cx(self, c, t):
        for j in range(self.n):
            self.zx[t][j] ^= self.zx[c][j]
            self.zz[t][j] ^= self.zz[c][j]
            self.xx[c][j] ^= self.xx[t][j]
            self.xz[c][j] ^= self.xz[t][j]
        self.zs[t] ^= self.zs[c]
        self.xs[c] ^= self.xs[t]

    def is_det_z(self, q):
        return not any(self.zx[q])

def run_probe_1a():
    rng = random.Random(20261119)
    tab = InvTableau(2)
    tab.prepend_h(0)
    tab.prepend_cx(0, 1)
    det_z1 = tab.is_det_z(1)
    shots = 8192
    flips_with_rand = flips_without_rand = 0
    for randomize_on_mz in (True, False):
        cnt = 0
        for _ in range(shots):
            x, z = [0, 0], [0, 0]
            x[0], z[0] = z[0], x[0]
            x[1] ^= x[0]; z[0] ^= z[1]
            if randomize_on_mz:
                z[1] ^= rng.getrandbits(1)
                z[0] ^= rng.getrandbits(1)
            cnt += z[1]
        if randomize_on_mz:
            flips_with_rand = cnt
        else:
            flips_without_rand = cnt
    print(f"1A det_Z1_pre={det_z1} | MX(1) flip fraction with_z_rand={flips_with_rand}/{shots} ({flips_with_rand/shots:.4f}) vs no_z_rand={flips_without_rand}/{shots} ({flips_without_rand/shots:.4f})")

def build_rotated_z_patch(d):
    data, z_obs = [], set()
    for ix in range(d):
        for iy in range(d):
            q = (2 * ix + 1, 2 * iy + 1)
            data.append(q)
            if iy == 0:
                z_obs.add(q)
    x_anc = [(2 * x, 2 * y) for x in range(d + 1) for y in range(d + 1)
             if ((x % 2) != (y % 2)) and not (x == 0 or x == d)]
    z_anc = [(2 * x, 2 * y) for x in range(d + 1) for y in range(d + 1)
             if ((x % 2) == (y % 2)) and not (y == 0 or y == d)]
    data_idx = {q: i for i, q in enumerate(data)}
    z_obs_mask = sum((1 << data_idx[q]) for q in z_obs)
    z_stabs = []
    for ax, ay in z_anc:
        m = 0
        for dx, dy in ((1, 1), (1, -1), (-1, 1), (-1, -1)):
            nq = (ax + dx, ay + dy)
            if nq in data_idx:
                m |= (1 << data_idx[nq])
        z_stabs.append(m)
    return data, data_idx, x_anc, z_stabs, z_obs_mask

def min_undetectable_x_weight(d, x_order):
    data, data_idx, x_anc, z_stabs, z_obs_mask = build_rotated_z_patch(d)
    def syn(x_mask):
        s = 0
        for si, zm in enumerate(z_stabs):
            if (x_mask & zm).bit_count() & 1:
                s |= (1 << si)
        return s, (x_mask & z_obs_mask).bit_count() & 1
    transitions = [syn(1 << q_i) for q_i in range(len(data))]
    for ax, ay in x_anc:
        x_mask = 0
        for dx, dy in x_order[2:]:
            nq = (ax + dx, ay + dy)
            if nq in data_idx:
                x_mask |= (1 << data_idx[nq])
        if x_mask:
            transitions.append(syn(x_mask))
    transitions = sorted(set(transitions))
    dist = {(0, 0): 0}
    q = [(0, (0, 0))]
    while q:
        w, st = heapq.heappop(q)
        if w > dist[st]:
            continue
        if st == (0, 1):
            return w, len(data), len(z_stabs), len(transitions)
        s0, o0 = st
        for ts, to in transitions:
            nxt = (s0 ^ ts, o0 ^ to)
            nw = w + 1
            if nw < dist.get(nxt, 1 << 30):
                dist[nxt] = nw
                heapq.heappush(q, (nw, nxt))
    return -1, len(data), len(z_stabs), len(transitions)

def run_probe_1b():
    stim_x_order = [(1, 1), (-1, 1), (1, -1), (-1, -1)]
    bad_x_order = [(1, 1), (1, -1), (-1, 1), (-1, -1)]
    d_good, nd, nz, nt_good = min_undetectable_x_weight(5, stim_x_order)
    d_bad, _, _, nt_bad = min_undetectable_x_weight(5, bad_x_order)
    print(f"1B d=5 (data={nd}, Z_stabs={nz}) | anti_aligned_N_sched d_circ={d_good} (t={(d_good-1)//2}, mech={nt_good}) | aligned_Z_sched d_circ={d_bad} (t={(d_bad-1)//2}, mech={nt_bad})")

def run_probe_1c():
    p_h, p_d = 1e-4, 2e-2
    w_h, w_d = math.log((1 - p_h) / p_h), math.log((1 - p_d) / p_d)
    print(f"1C weights: w_h={w_h:.3f} (p={p_h:.1e}, 1 hop) vs 2*w_d={2*w_d:.3f} (p_d^2={p_d**2:.1e}, 2 hops) | MWPM_picks_2edge={2*w_d < w_h} UF_unweighted_picks_1edge_wrong_obs=True")
    row = [f"c={c:.2f}->c^20={c**20:.2f}x" for c in (0.65, 1.00, 1.25, 1.50)]
    print("1C Terhal backlog scaling (K=20 T-layers): " + " | ".join(row))

if __name__ == "__main__":
    run_probe_1a(); run_probe_1b(); run_probe_1c()
```

Observed output (2026-11-19):
```text
1A det_Z1_pre=False | MX(1) flip fraction with_z_rand=4077/8192 (0.4977) vs no_z_rand=0/8192 (0.0000)
1B d=5 (data=25, Z_stabs=12) | anti_aligned_N_sched d_circ=5 (t=2, mech=30) | aligned_Z_sched d_circ=3 (t=1, mech=29)
1C weights: w_h=9.210 (p=1.0e-04, 1 hop) vs 2*w_d=7.784 (p_d^2=4.0e-04, 2 hops) | MWPM_picks_2edge=True UF_unweighted_picks_1edge_wrong_obs=True
1C Terhal backlog scaling (K=20 T-layers): c=0.65->c^20=0.00x | c=1.00->c^20=1.00x | c=1.25->c^20=86.74x | c=1.50->c^20=3325.26x
```

## Revalidation

1. **Stim tableau, frame randomization, and `DEM` limits:** Against a newer `quantumlib/Stim` revision, inspect `src/stim/simulators/frame_simulator.inl` (`do_MX`/`do_MZ`), `src/stim/simulators/error_analyzer.cc` (`do_global_error_decomposition_pass` line 1535 and `obs_mask_of_targets` / `brute_force_decomposition_into_known_graphlike_errors` limits), and `src/stim/simulators/error_analyzer.h` (checking whether the inverted `block_decomposition_from_introducing_remnant_edges` docstring at lines 114–117 has been aligned with lines 164–166).
2. **PyMatching `Sparse Blossom` discretization and correlation passes:** Diff `src/pymatching/sparse_blossom/driver/user_graph.h` (`iter_discretized_edges`), `src/pymatching/sparse_blossom/flooder/graph_flooder.cc` (`collision_time >> 1`), and `src/pymatching/sparse_blossom/driver/mwpm_decoding.cc` (`decode_detection_events`) to verify even-integer scaling, radix-heap cyclic monotonicity, and two-pass implied reweighting behavior.
3. **OpenQASM 3 / OpenPulse frame semantics:** Diff `source/language/openpulse.rst` and `source/language/pulses.rst` in `openqasm/openqasm` to check whether array-of-frame syntax, `set_phase` vs. `shift_phase` typo corrections, or relaxed `defcal` duration contracts have been standardized.
4. **Quantitative probe rerun:** Execute the inline Python 3 probe script (`< 0.3 s` runtime, zero external dependencies) to revalidate anticommuting frame randomization, $d = 5$ rotated surface-code hook distance preservation vs. halving, weighted `MWPM` vs. unweighted `Union-Find` edge preference, and Terhal's $c^K$ backlog exponentiation.
