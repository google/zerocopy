# Electrostatic Placement, Static Timing Closure with OCV/CRPR, and Layout DRC/LVS Signoff

## Summary

End-to-end RTL-to-GDSII physical implementation and signoff across `OpenROAD`, `OpenSTA`, `KLayout`, `Magic`, and `Netgen` form a coupled chain of mathematical relaxations, statistical timing bounds, spatial decompositions, and graph-isomorphism reductions. Three cross-tool invariants dominate whether a placed, routed, and extracted integrated circuit survives physical silicon bring-up:

1. **Electrostatic Potential Regularity and Wirelength Stabilization (`OpenROAD`)**: Global placement replaces non-differentiable half-perimeter wirelength (`HPWL`) with a max-shifted Weighted-Average (`WA`) exponential surrogate and solves a zero-mean Neumann-boundary 2D Poisson equation via discrete cosine/sine transforms (`Ooura` DCT-II/DST-II on CPU or Kokkos/CUDA on GPU). Nesterov momentum acceleration coupled with dynamic density penalty scaling (`lambda_k`) prevents overflow oscillations, while `OpenDP` site/power-rail legalization, `TritonCTS` buffered H-trees, and `TritonRoute` maze routing preserve physical legality and routability.
2. **Propagated-Clock Timing Closure, Common-Path Variance Cancellation, and SDC Exception Soundness (`OpenSTA`)**: Accurate static timing requires `CCS` receiver effective-capacitance (`C_eff`) modeling over extracted `SPEF` RC trees plus propagated clocks (`isPropagated()`). Clock Reconvergence Pessimism Removal (`CRPR`) cancels shared launch/capture common-path min/max derating and `POCV` variance (`crpr_sigma2 = src_arrival.stdDev2() + tgt_arrival.stdDev2()`). Silicon hold failures occur not from arithmetic errors in STA propagation, but from missing `set_propagated_clock` (treating clock trees as zero-delay ideal nets, as documented in the SkyWater `sky130` Caravel MPW-1 silicon failure), overly broad `set_false_path` wildcards (`FalsePath` priority `4000` overriding all synchronous constraints), or unpaired `set_multicycle_path N -setup` rules that silently shift hold checks by `(N - 1) * T_clk`.
3. **Locality Radius (`DRCTechHalo`) vs. Topological Whole-Net Checks (`KLayout`, `Magic`, `Netgen`)**: Local geometric rules (width, spacing, enclosure) require padding tile boundaries by the maximum rule interaction radius (`DRCTechHalo` in `Magic`, `tile_borders` in `KLayout`), whereas invoking `tiles(tx, ty)` in `KLayout` silently clears `@deep = false` and severs net connectivity across tile seams—invalidating whole-net `antenna_check` accumulation. Finally, `Netgen` LVS reduces circuit equivalence to bipartite 1-Weisfeiler–Lehman (`1-WL`) partition refinement plus series/parallel folding, stalling on symmetric circuits (differential pairs, SRAM bitcells) until backtracking `ResolveAutomorphisms()` breaks symmetry.

## Applicability

This report characterizes the open-source ASIC physical design and signoff stack defined by the following pinned revisions and formulations:

- **Physical implementation (`OpenROAD` @ `0c210b22ed42ed677ff28ff539a11bc37a7453f9`)**: Covers electrostatic global placement (`openroad/gpl`), detailed row/site legalization (`openroad/dpl`), clock tree synthesis (`openroad/cts`), detailed routing (`openroad/drt`), and LEF/DEF antenna checking (`openroad/ant`). Note that at this revision, `OpenROAD` has removed CMake entirely (as of November 1, 2026) and builds strictly via Bazel (`bazelisk build //:openroad`) under `openroad/<module>/BUILD`, with an optional `ENABLE_GPU` / Kokkos FFT backend (`gpl_kokkos`).
- **Static timing analysis (`OpenSTA` @ `cc510896e8e097771100d7dec4f5cbfdb3d6d71a`)**: Covers delay calculation (`dcalc/CcsCeffDelayCalc.cc`), `SPEF` parasitic parsing (`parasitics/SpefReader.cc`), `AOCV`/`POCV` statistical modes (`search/PocvMode.cc`), `CRPR` (`search/Crpr.cc`), and `SDC` exception semantics (`sdc/ExceptionPath.cc`, `sdc/Sdc.cc`, `sdc/Sdc.tcl`).
- **DRC, extraction, and LVS signoff**: Covers polygon/region and Ruby-DSL DRC plus layout-to-netlist antenna extraction in `KLayout` (`53911acd6dfaa113c188d11d20b2ae290aa60a6b`), corner-stitched continuous/incremental DRC and SPICE extraction in `Magic` (`cc0360b3a4c3ca4b3c81ab69379be630c5d6df87`), and hierarchical/flattened graph-isomorphism LVS in `Netgen` (`e2a49567d5e3e451d51130de0227678be31f32e0`).
- **Cross-subject relationship**: The subjects represent a sequential compiler-style pipeline (`RTL/Gate Netlist + Liberty + SDC + LEF` -> `OpenROAD` placed/routed DEF & GDSII -> `OpenSTA` `SPEF` timing signoff -> `KLayout`/`Magic` physical DRC & SPICE extraction -> `Netgen` LVS). Findings apply to standard-cell synchronous digital ASICs and mixed-signal blocks using Manhattan/octilinear planar or FinFET processes represented in Liberty `.lib`, `IEEE 1481` (`SPEF`), `SDC`, `LEF/DEF`, `GDSII`/`OASIS`, and `SPICE`.

## Findings

### 1. Electrostatic Global Placement, Legalization, CTS, and Detailed Routing (`OpenROAD`)

#### 1.1 Max-Shifted Weighted-Average Wirelength and Neumann DCT-II Poisson Field
`Basis: source + normative (IEEE TCAD 2019) + execution`

Classical half-perimeter wirelength $\mathrm{HPWL}(e) = (\max_{i \in e} x_i - \min_{i \in e} x_i) + (\max_{i \in e} y_i - \min_{i \in e} y_i)$ is piecewise linear and non-differentiable at pin ties. `RePlAce` (`DOI: 10.1109/TCAD.2018.2859220`) approximates $\max$ and $\min$ along each axis using the smooth Weighted-Average (`WA`) operator parameterized by smoothing scale $\gamma > 0$:

$$\mathrm{WA}_{\gamma, x}(e) = \frac{\sum_{i \in e} x_i \exp\bigl((x_i - x_{\max})/\gamma\bigr)}{\sum_{i \in e} \exp\bigl((x_i - x_{\max})/\gamma\bigr)} - \frac{\sum_{i \in e} x_i \exp\bigl(-(x_i - x_{\min})/\gamma\bigr)}{\sum_{i \in e} \exp\bigl(-(x_i - x_{\min})/\gamma\bigr)}$$

Subtracting $x_{\max}$ and $x_{\min}$ inside the exponentials is not cosmetic: during late placement iterations as $\gamma \to 0$ (e.g., $\gamma = 2.0\text{ DBU}$ when coordinates span $x_i > 2000\text{ DBU}$), unshifted $\exp(x_i/\gamma)$ overflows IEEE 754 `binary32`/`binary64` (`exp(1205) = +Inf`), causing `Inf / Inf = NaN` gradients. `NesterovPlace::checkInvalidValues` (`openroad/gpl/src/nesterovPlace.cpp:1687-1699`) explicitly traps `std::isnan` / `std::isinf` on `wireLengthGradSum` and `densityGradSum` (diagnostic code `GPL 306`) and triggers snapshot reversion (`isDiverged(curA)` at line `1492`).

To spread overlapping standard cells without artificial grid repulsion discontinuities, `RePlAce` models cell area density $\rho(x,y)$ on an $M_x \times M_y$ bin grid as electrostatic charge and solves the 2D Poisson equation $\nabla^2 \phi(x,y) = -\rho(x,y)$ under homogeneous Neumann boundary conditions ($\hat{n} \cdot \nabla \phi|_{\partial \Omega} = 0$, ensuring zero outward force at the die edge). In `openroad/gpl/src/fft.cpp:82-194`, `CpuFftBackend` precomputes aspect-scaled wavenumbers:

- $w_x[u] = \pi u / M_x$, $w_y[v] = (\pi v / M_y) \cdot (\Delta x_{\mathrm{bin}} / \Delta y_{\mathrm{bin}})$ (`fft.cpp:82-89`);
- Forward 2D Type-II DCT via Ooura's `ddct2d(bin_cnt_x_, bin_cnt_y_, -1, ...)` (`fft.cpp:122-141`);
- DC-mode gauge fixing at `(i == 0 && j == 0)` (`phi_value = electro_x = electro_y = 0.0f` at `fft.cpp:155-157`), enforcing charge neutrality $\tilde{\rho} = \rho - \bar{\rho}$ so total excess charge integrates to zero;
- Spectral division $\hat{\phi}_{u,v} = \hat{\rho}_{u,v} / (w_x[u]^2 + w_y[v]^2)$ and field spectral components $\hat{E}_x = w_x[u]\hat{\phi}_{u,v}$, $\hat{E}_y = w_y[v]\hat{\phi}_{u,v}$ (`fft.cpp:159-161`), inverted back to real space via `ddct2d` ($\phi$), `ddsct2d` ($E_x$), and `ddcst2d` ($E_y$) (`fft.cpp:171-190`).

#### 1.2 Nesterov Momentum, Legalization, CTS Skew Balancing, and Maze Routing
`Basis: source + documentation`

1. **Nesterov Accelerated Gradient & Backtracking (`openroad/gpl/src/nesterovPlace.cpp:1191-1520`)**: At each iteration, `curA = (1.0 + sqrt(4.0 * prevA * prevA + 1.0)) * 0.5` computes the Nesterov extrapolation coefficient `coeff = (prevA - 1.0) / curA` (`lines 1446-1449`), and `doBackTracking(coeff)` (`line 1191`) evaluates `nbc_->updateWireLengthForceWA` and Lipschitz step-size backtracking (`maxBackTrack`). When `wireLengthGradSum == 0` (`lines 123, 157`), wirelength coefficients halve up to `maxRecursionWlCoef`. Timing-driven passes (`runTimingDriven`, `line 1484`) restart Nesterov momentum (`curA = 1.0`, `line 1437`) whenever net weights change so stale velocity vectors do not overshoot newly critical paths. Routability-driven mode saves snapshots (`routabilitySnapshot`, `line 1504`) before cell inflation to revert if inflation causes divergence (`routability_driven_revert_count`).
2. **Row/Site & Power-Rail Legalization (`OpenDP`, `openroad/dpl/src/Opendp.cpp`, `NegotiationLegalizer.cpp`)**: Continuous Nesterov coordinates must snap to discrete placement rows (`Site` grid), matching alternating `R0`/`MX` cell VDD/VSS power-rail orientations (`adjustNodesOrient()`, `Opendp.cpp:217`), non-overlapping macro/blockage halos, and maximum displacement caps (`max_displacement_x`, `max_displacement_y`). In `Opendp::detailedPlacement` (`Opendp.cpp:200-255`), fixed instances and fillers are accounted for, and negotiation-based or diamond search (`use_diamond_legalizer`) resolves multi-height or congested region overlaps while minimizing quadratic displacement $\sum_i \|x_i^{\mathrm{legal}} - x_i^{\mathrm{global}}\|_2^2$.
3. **Clustered H-Tree Clock Synthesis (`TritonCTS`, `openroad/cts/src/HTreeBuilder.cpp`)**: `HTreeBuilder` partitions flip-flop sinks using spatial/capacitive clustering (`sink_clustering_size`, `sink_clustering_max_diameter`, `HTreeBuilder.cpp:143-167`), builds symmetric buffered H-tree spines characterized by LUT delay/slew tables (`TechChar`), and invokes `LatencyBalancer` to match insertion latency across non-uniform leaf branches and macro-obstruction detours.
4. **Detailed Maze Routing (`TritonRoute`, `openroad/drt/src/TritonRoute.cpp`)**: Routes within global-router guide corridors using grid-graph A* maze search with track-assignment costs, via-pillar penalties, and iterative rip-up-and-reroute DRC violation minimization (`WatermarkCost.h`, `FlexMazeTypes.h`). Residual design-rule violations after `drt` convergence (e.g., via-to-via min-spacing or off-grid pin access) must be resolved prior to `KLayout`/`Magic` signoff.

### 2. Static Timing Analysis, CCS/POCV/CRPR, and SDC Silicon Hold Escapes (`OpenSTA`)

#### 2.1 `NLDM` vs. `CCS` Effective Capacitance and `POCV` Statistical Arrival Propagation
`Basis: source + documentation`

In standard-cell timing, `NLDM` characterizes cell arc delay and output slew as bilinearly interpolated 2D tables indexed by `(input_slew, total_lumped_C)`. At sub-28nm nodes where wire resistance $R_w$ becomes comparable to or larger than driver output impedance $R_{\mathrm{drv}}$, downstream pin capacitance is **resistively shielded**: the driver initially sees only the near-end capacitance $C_{\mathrm{near}}$ and a fraction of downstream $C_{\mathrm{far}}$. `NLDM` with total capacitance $C_{\mathrm{total}} = C_{\mathrm{near}} + C_{\mathrm{far}}$ systematically over-predicts driver delay while under-predicting far-end RC interconnect delay.

`OpenSTA` addresses resistive shielding in `dcalc/CcsCeffDelayCalc.cc` (`CcsCeffDelayCalc`, paired with `DmpDelayCalc` and `FindRoot`) by reading `Liberty` Composite Current Source (`CCS`) waveforms (`output_current_fall`/`rise`) and solving an iterative root-finding problem (`C_eff`) against reduced $\pi$-model `SPEF` RC trees (`parasitics/SpefReader.cc`): $C_{\mathrm{eff}}$ matches the average current drawn by the real RC interconnect during the switching window $[t_0, t_{50\%}]$ (for delay) and $[t_{20\%}, t_{80\%}]$ (for slew).

For on-chip variation (`OCV`), flat global early/late derates (`set_timing_derate`) scale path delays linearly with logic depth ($O(N)$), becoming overly pessimistic on deep paths because random within-die variation averages out as $\sqrt{N}$. `OpenSTA` supports:
- **`AOCV`** (Advanced OCV): stage-depth-indexed derating tables reducing pessimism monotonically with path depth;
- **`POCV`** (Parametric OCV, `search/PocvMode.cc:31-46`): propagates arrival times as distributions parameterized by mean and variance (`PocvMode::{scalar, normal, skew_normal}`). Under `normal` mode, uncorrelated gate variations add in quadrature: $\mu_{\mathrm{path}} = \sum_i \mu_i$ and $\sigma_{\mathrm{path}} = \sqrt{\sum_i \sigma_i^2}$.

#### 2.2 Clock Reconvergence Pessimism Removal (`CRPR`) and Variance Subtraction
`Basis: source`

In a synchronous setup or hold check between launch flip-flop $FF_L$ and capture flip-flop $FF_C$, the clock tree shares a common root prefix up to a Lowest Common Ancestor (`LCA`) reconvergence buffer $P_{\mathrm{common}}$ before diverging into launch branch $B_L$ and capture branch $B_C$. Because a single launch event travels through $P_{\mathrm{common}}$ at a single physical corner/temperature/voltage/variation state on a given die, simultaneously applying **early** derating (`-3σ` / `0.92×`) to $P_{\mathrm{common}}$ on the launch clock path and **late** derating (`+3σ` / `1.08×`) to the *same* $P_{\mathrm{common}}$ on the capture clock path (or vice versa for setup) creates physically impossible pessimism.

`OpenSTA` removes this artifact in `CheckCrpr::checkCrpr1` and `CheckCrpr::findCrpr1` (`search/Crpr.cc:115-296`):

1. **Preconditions (`search/Crpr.cc:136-145`)**: CRPR applies **if and only if** `crprPossible(src_clk, tgt_clk)`, **both** `src_clk_info->isPropagated()` and `tgt_clk_info->isPropagated()` are `true` (ideal clocks have no modeled physical common delay to credit), and `src_clk_min_max != tgt_clk_path->minMax(this)` (opposite Early/Late analysis corners).
2. **Generated-Clock & LCA Pin Matching (`search/Crpr.cc:187-237, 241-261`)**: If `clkSrc()` differs between source and target (e.g., divided/generated clocks), `genClkSrcPaths` walks back through master clock source paths to locate a shared clock root, then intersects `src_pin_map` with `tgt` back-pointers. When `crpr_mode == same_pin` (`line 109`), any common pin matches; otherwise (`same_transition`), `src->transition(this) == tgt->transition(this)` (`line 231`) prevents crediting mismatched rising/falling polarity across inverting clock gates.
3. **POCV Common-Prefix Variance Subtraction (`search/Crpr.cc:268-296`)**: In flat/AOCV mode (`lines 291-295`), `common_delay = std::min(src_delta, tgt_delta)`. Under `variables_->pocvEnabled()` (`lines 268-280`), `OpenSTA` computes:
   ```cpp
   float crpr_mean = std::abs(src_arrival.mean() - src_clk_time
                              - (tgt_arrival.mean() - tgt_clk_time));
   float crpr_sigma2 = src_arrival.stdDev2() + tgt_arrival.stdDev2();
   return makeDelay2(crpr_mean, -crpr_sigma2);
   ```
   Subtracting `crpr_sigma2` cancels both the launch and capture `stdDev2()` terms accumulated along the shared prefix $P_{\mathrm{common}}$ rather than subtracting a single standard deviation linearly, avoiding both double-counted variance and negative-variance underflow.

#### 2.3 Anatomy of Silicon Hold-Time Escapes (`Ideal Clock`, `FalsePath` Priority, Unpaired `Multicycle`)
`Basis: source + documentation (Caravel MPW-1) + execution`

Hold-time checks ($\text{Launch}_\text{early} + T_{\mathrm{data,min}} \ge \text{Capture}_\text{late} + t_{\mathrm{hold}}$) are frequency-independent: slowing the clock frequency after silicon tapeout **cannot** rescue a hold failure. Across `OpenSTA` and open-source RTL-to-GDSII flows, three distinct mechanisms cause timing signoff to report positive hold slack while silicon fails functionally:

1. **Missing `set_propagated_clock` (Zero-Delay Ideal Clock Omission)**: Until `Sdc::setPropagatedClock` (`sdc/Sdc.cc:1755-1772`) sets `clk->setIsPropagated(true)` post-CTS, `OpenSTA` treats the clock network delay as `0` (plus any idealized `set_clock_latency`). If post-route signoff accidentally keeps an ideal clock constraint, physical clock-tree insertion skew $\Delta_{\mathrm{skew}} = \tau_{B_C} - \tau_{B_L} > 0$ disappears from the hold calculation, making fast data paths appear safe while real silicon clocks $FF_C$ late and corrupts the state. This exact misconfiguration caused widespread hold-time failures in the RISC-V management core on the initial open-source **Efabless Caravel MPW-1** (`sky130`) multi-project wafer shuttle, where OpenSTA timing reports showed `0` clock network delay and omitted hold-buffer insertion (`sky130_fd_sc_hd__dlygate4*`).
2. **SDC Exception Priority Masking (`sdc/ExceptionPath.cc`, `include/sta/ExceptionPath.hh:100-106`)**: `OpenSTA` enforces a strict numeric priority hierarchy:
   - `falsePathPriority() = 4000` (`ExceptionPath.hh:101`)
   - `pathDelayPriority() = 3000` (`line 102`)
   - `multiCyclePathPriority() = 2000` (`line 103`)
   - `filterPathPriority() = 1000`, `pathMarginPriority() = 500`, `groupPathPriority() = 0` (`lines 104-106`)
   Qualifier specificity (`fromThruToPriority`, `0..127` bitmask `priority |= (1 << 2..6)` at `ExceptionPath.cc:188-200`) resolves ties *within* an exception class, but **never overrides `typePriority()` across classes** (`FalsePath::overrides` / `ExceptionPath.cc:647-758`). Consequently, a broad `set_false_path -from [get_clocks clk_a] -to [get_clocks clk_b]` (base priority `4000+`) silently disables timing checks on **all** paths between those domains—including single-cycle synchronizer capture flops or paths that happen to share an unconstrained reset/scan mux (`set_false_path -through ...`), leaving zero hold repair (`dly` buffers) on physical silicon.
3. **Unpaired `set_multicycle_path N -setup` Without `-hold (N-1)` (`sdc/Sdc.tcl:3255-3271`, `ExceptionPath.cc:728-747`)**: In `OpenSTA`, `set_multicycle_path N -setup` sets `min_max = "max"` and `use_end_clk = 1` (`Sdc.tcl:3262-3266`), shifting the setup capture edge from $T_{\mathrm{clk}}$ to $N \cdot T_{\mathrm{clk}}$. Because standard SDC defines the default hold check as one cycle *before* the active setup capture edge, omitting a matching `set_multicycle_path (N-1) -hold` moves the hold requirement forward to $(N-1) \cdot T_{\mathrm{clk}}$—forcing the optimizer to pad massive delay chains (`(N-1)` clock periods of delay buffers) or, if masked/inconsistent across clocks (`-start`/`-end`), checking hold against the wrong clock edge. Note also `MultiCyclePath::pathMultiplier(MinMax::min())` (`ExceptionPath.cc:730-733`): when *neither* `-setup` nor `-hold` is passed (`min_max == all`), `OpenSTA` fixes the `min` (hold) multiplier to `0` rather than `N`.

#### 2.4 Reproducible Micro-Probe: `WA` Stabilization, Neumann DCT-II Poisson, and `POCV`/`CRPR`/Hold Escapes
`Basis: execution`

Running the standalone Python 3.13 probe below directly verifies (a) unshifted `WA` overflow vs. max-shifted accuracy as $\gamma \to 2.0$, (b) 4-bin zero-mean Neumann DCT-II potential and electric-field symmetry, and (c) `POCV` common-variance cancellation vs. ideal-clock silicon hold escape (`+5.48 ps` false pass on a real `-58.74 ps` violation):

```python
import math

# 1. Weighted-Average (WA) wirelength overflow vs max-shift stabilization
coords = [10.0, 420.0, 1850.0, 2410.0]
hpwl = max(coords) - min(coords)
for gamma in [500.0, 100.0, 20.0, 2.0]:
    xmax, xmin = max(coords), min(coords)
    ep = [math.exp((x - xmax) / gamma) for x in coords]
    em = [math.exp(-(x - xmin) / gamma) for x in coords]
    wa_shifted = sum(x * e for x, e in zip(coords, ep)) / sum(ep) - sum(x * e for x, e in zip(coords, em)) / sum(em)
    try:
        ep_raw = [math.exp(x / gamma) for x in coords]
        raw_s = f"{sum(x * e for x, e in zip(coords, ep_raw)) / sum(ep_raw):.4f}"
    except OverflowError:
        raw_s = "OverflowError(exp(2410/2.0))"
    print(f"gamma={gamma:5.1f}: HPWL={hpwl:.2f}, WA_shifted={wa_shifted:.4f}, err={abs(hpwl-wa_shifted):.4f}, unshifted={raw_s}")

# 2. 1D 4-bin Neumann DCT-II Poisson check (openroad/gpl/src/fft.cpp model)
rho = [1.35, 1.15, 0.85, 0.65]
q = [r - sum(rho) / len(rho) for r in rho]
M = len(q)
a_hat = [sum(q[m] * math.cos(math.pi * (m + 0.5) * u / M) for m in range(M)) for u in range(M)]
phi_hat = [0.0] + [a_hat[u] / ((math.pi * u / M) ** 2) for u in range(1, M)]
phi = [(2.0 / M) * sum(phi_hat[u] * math.cos(math.pi * (m + 0.5) * u / M) for u in range(1, M)) for m in range(M)]
xi = [(2.0 / M) * sum((phi_hat[u] * (math.pi * u / M)) * math.sin(math.pi * (m + 0.5) * u / M) for u in range(1, M)) for m in range(M)]
print("Poisson potential phi:", [round(v, 4) for v in phi], "E-field xi:", [round(v, 4) for v in xi])

# 3. OpenSTA POCV + CRPR variance cancellation vs ideal-clock & unpaired-MCP hold traps
T_clk = 1000.0
mu_c, sig_c = 240.0, 18.0
mu_l_br, sig_l_br = 90.0, 9.0
mu_t_br, sig_t_br = 110.0, 11.0
mu_data_min, sig_data_min = 65.0, 7.0
t_hold_req = 35.0
launch_mu = 0.92 * (mu_c + mu_l_br) + 0.92 * mu_data_min
launch_var = (0.92 ** 2) * (sig_c ** 2 + sig_l_br ** 2 + sig_data_min ** 2)
cap_mu = 1.08 * (mu_c + mu_t_br) + t_hold_req
cap_var = (1.08 ** 2) * (sig_c ** 2 + sig_t_br ** 2)
slack_no_crpr = (launch_mu - cap_mu) - 3.0 * math.sqrt(launch_var + cap_var)
crpr_mean = (1.08 - 0.92) * mu_c
crpr_sigma2 = (0.92 * sig_c) ** 2 + (1.08 * sig_c) ** 2
slack_with_crpr = (launch_mu - cap_mu + crpr_mean) - 3.0 * math.sqrt(launch_var + cap_var - crpr_sigma2)
slack_ideal_clk = (0.92 * mu_data_min - t_hold_req) - 3.0 * (0.92 * sig_data_min)
slack_unpaired_mcp3 = slack_with_crpr - 2.0 * T_clk
print(f"Hold slack (ps): no_CRPR={slack_no_crpr:.2f}, with_POCV_CRPR={slack_with_crpr:.2f}, ideal_clk_bug={slack_ideal_clk:.2f}, unpaired_MCP3_setup={slack_unpaired_mcp3:.2f}")
```

Observed output (Python 3.13, `2026-11-19`):
```text
gamma=500.0: HPWL=2400.00, WA_shifted=2055.4917, err=344.5083, unshifted=2232.8988
gamma=100.0: HPWL=2400.00, WA_shifted=2391.2528, err=8.7472, unshifted=2407.9368
gamma= 20.0: HPWL=2400.00, WA_shifted=2400.0000, err=0.0000, unshifted=2410.0000
gamma=  2.0: HPWL=2400.00, WA_shifted=2400.0000, err=0.0000, unshifted=OverflowError(exp(2410/2.0))
Poisson potential phi: [0.57, 0.237, -0.237, -0.57] E-field xi: [0.1837, 0.4487, 0.4487, 0.1837]
Hold slack (ps): no_CRPR=-139.77, with_POCV_CRPR=-58.74, ideal_clk_bug=5.48, unpaired_MCP3_setup=-2058.74
```

### 3. Geometric DRC, Gate-Oxide Antenna Checks, and Netlist-Isomorphism LVS (`KLayout`, `Magic`, `Netgen`)

#### 3.1 Corner Stitching (`Magic`) vs. Scanline/Hierarchical/Tiled Regions (`KLayout`)
`Basis: source + normative (IEEE TCAD 1984)`

`Magic` and `KLayout` embody fundamentally opposite spatial representations:

| Dimension | `Magic` Corner Stitching (`tiles/tile.h`, `drc/DRCcontin.c`) | `KLayout` Region & Edge Engines (`dbRegion.cc`, `dbDeepRegion.cc`, `_drc_engine.rb`) |
|---|---|---|
| **Spatial Representation** | Planar maximal horizontal strips (`struct tile` with `ti_ll` and 4 stitches `ti_lb`, `ti_bl`, `ti_tr`, `ti_rt`; `TOP(tp)=BOTTOM(RT(tp))`, `RIGHT(tp)=LEFT(TR(tp))` at `tiles/tile.h:65-105`), explicitly tiling **empty space** alongside solid paint. | Orthogonal/arbitrary-angle polygons (`db::Polygon`) processed by $O((V + k)\log V)$ scanline `dbEdgeProcessor` (`dbEdgeProcessor.cc`), hierarchical `DeepShapeStore` (`dbDeepRegion.cc:137-193`), or rectangular tiling (`_drc_engine.rb:1140-1185`). |
| **Memory Overhead** | ~3× compact polygon lists due to explicit space tiles + 4 pointers + `ti_body`/`ti_client` per tile (Ousterhout, *IEEE TCAD* 1984, `DOI: 10.1109/TCAD.1984.1270061`). | Compact vertex vectors in flat `Region`, or cell-instanced copy-on-write trees in `DeepRegion` (`@deep = true`) deduplicating SRAM/array instances. |
| **Incremental / Halo Guarantees** | Automatic background DRC (`DRCContinuous`, `DRCCheckThis`, `drc/DRCcontin.c:184-717`): every edit box automatically expands by process-wide `DRCTechHalo` (`GEO_EXPAND(&erasebox, DRCTechHalo, &checkbox)` at `line 701`) and traverses stitches in $O(\text{local tiles})$. | **Manual** in tiled mode (`_drc_engine.rb:1140-1185`): `def tiles(tx, ty)` explicitly forces `@deep = false` (`line 1143`) and relies on caller-supplied `tile_borders(bx, by)` (`lines 1168-1171`). |
| **Non-Manhattan Geometry** | Restricted to axis-aligned rectangles (diagonal edges emulated by `TT_DIAGONAL` split tiles in a single tile). | Native arbitrary-angle `db::Edge` / `db::Polygon` intersections, beveling, and `area_ratio` checks (`dbDeepRegion.cc:137`). |

**The `KLayout` Tiling-vs.-Connectivity Trap**: Calling `tiles(1000.um)` in a `KLayout` `.drc` deck for parallel multi-threaded throughput triggers two silent soundness hazards:
1. Because `def tiles(tx, ty = nil)` sets `@deep = false` (`src/drc/drc/built-in-macros/_drc_engine.rb:1140-1144`), hierarchical cell deduplication is disabled for subsequent operations unless re-enabled via `deep`, inflating memory on dense arrays if tile size is large, or missing rules whose interaction distance exceeds `tile_borders(bx, by)` if `tile_borders` is omitted (`no_borders` sets `@bx = @by = nil`, `line 1184`) or smaller than the rule halo (e.g., wide-metal run-length spacing or deep N-well enclosure).
2. Multi-layer netlist extraction (`dbLayoutToNetlist.cc:1972`) and whole-net checks (`antenna_check` at `_drc_engine.rb:2495`) compute topological equivalence classes across entire conductors. Tiling truncates wires at artificial tile boundaries, severing connected metal area from distant gate or protection-diode diffusion polygons and yielding **false-pass antenna signoff**.

#### 3.2 Plasma-Induced Gate-Oxide Antenna Ratios (`OpenROAD ant` & `KLayout`)
`Basis: source`

During back-end-of-line (`BEOL`) plasma etching, long floating metal segments or vias accumulate charge proportional to exposed top area (`PAR` / `CAR`) or sidewall perimeter (`PSR` / `CSR`) before upper metal layers bridge the net to a low-impedance reverse-biased diffusion diode. Both `OpenROAD` (`openroad/ant/src/AntennaChecker.cc:295-685`) and `KLayout` (`LayoutToNetlist::antenna_check` in `src/db/db/dbLayoutToNetlist.cc:1972-1989`) evaluate layer-by-layer partial (`PAR`/`PSR`) and cumulative (`CAR`/`CSR`) ratios:

$$\text{Partial Ratio} = \frac{f_{\mathrm{metal}} \cdot A_{\mathrm{metal}} \cdot r_{\mathrm{diff}}(A_{\mathrm{diff}}) - k_- \cdot A_{\mathrm{diff}}}{A_{\mathrm{gate}} + k_+ \cdot A_{\mathrm{diff}}}$$

where `AntennaChecker::Impl::calculatePAR` (`AntennaChecker.cc:295-367, 476`) and `calculateCAR` (`line 501`) evaluate piecewise-linear (`pwl_pair`) LEF factors `getAreaDiffReduce()` and `gate_plus_diff_ratios` (`lines 299-360`) keyed on whether a connected diffusion node area `info.iterm_diff_area != 0`. In `OpenROAD`, block pins carry `ANTENNAMAX*CAR` cumulative history from sub-macro signoff (`lines 505-562`) so top-level checking remains compositional without flattening the IP block's internal polygons.

#### 3.3 Bipartite `1-WL` Netlist Isomorphism, Device Folding, and Automorphism Stalls (`Netgen`)
`Basis: source + execution`

`Netgen` (`base/netcmp.c`) checks structural equivalence between extracted SPICE layout netlists and schematic netlists by casting the circuit as a labeled bipartite multigraph $G = (V_E \cup V_N, E_{\mathrm{pins}})$ of **Element** vertices (`ElementClass`) and **Net** vertices (`NodeClass`). Its core algorithm (`Iterate()` at `base/netcmp.c:4205-4260`):

1. **Canonical Folding (`series_optimize`, `parallel_optimize`, `PropertySortAndCombine`, `base/netcmp.c:4268-4991`)**: Before partitioning, topologically equivalent multi-finger transistors (`M` parallel fingers or `S` series-stacked FETs/resistors/capacitors) are combined and their geometric properties (`W`, `L`, `AS`, `AD`) summed/merged so a 4-finger layout FET matches a 1-device schematic FET with `M=4`.
2. **Pin Permutation Equivalence (`PermuteSetup`, `Permute`, `base/netcmp.c:6944-7090`)**: Symmetric pins (e.g., MOSFET source/drain `(S, D)` or resistor terminals) are assigned identical pin-class tags in `ElementHash` (`line 4173`), whereas asymmetric pins (gate `G`, bulk `B`, diode anode/cathode) retain distinct tags; swapping `D/S` passes LVS while swapping `G/S` fails.
3. **Color Refinement (`ElementHash`/`NodeHash` + `FractureElementClass`/`FractureNodeClass`, `lines 3024-3085, 4225-4249`)**: Each iteration hashes every element's type and incident net-class multiset (`ElementHash`) and every net's incident `(element_class, pin_type)` multiset (`NodeHash`), splitting any class with non-identical signatures into finer subclasses with randomized `Magic()` class identifiers (`line 3021`). Notice lines `4231-4233` and `4244-4246`: a partition of size 2 belonging entirely to one graph (`graph == graph`) immediately flags `legalpartition = 0` (structural mismatch!).
4. **The 1-WL Automorphism Blind Spot (`ResolveAutomorphisms`, `base/netcmp.c:6865-6927`)**: Color refinement (`1-WL`) stabilizes whenever remaining classes contain $\ge 2$ indistinguishable symmetric elements/nets in *both* circuits (`C1 == C2 && C1 != 1`, lines `6888, 6911`)—common in differential pairs, cross-coupled SRAM bitcells, ring oscillators, and balanced H-trees. `Netgen` picks one arbitrary candidate pair `(E1, E2)` or `(N1, N2)`, assigns them a unique shared `Magic(newhash)`, sets `ExhaustiveSubdivision = 1` (`line 6923`), and re-iterates (`while (!Iterate() && (VerifyMatching() >= 0));`, `line 6924`). If an asymmetric swap inside the symmetric subcircuit exists downstream, backtracking/subdivision detects the contradiction via `VerifyMatching()`.

Reproducible `1-WL` stall probe on a cross-coupled CMOS differential load (`Basis: execution`, Python 3.13):

```python
elements = {
    "M1": ("nmos", {"G": "in_p", "D": "out_n", "S": "tail", "B": "vss"}),
    "M2": ("nmos", {"G": "in_n", "D": "out_p", "S": "tail", "B": "vss"}),
    "P1": ("pmos", {"G": "out_p", "D": "out_n", "S": "vdd", "B": "vdd"}),
    "P2": ("pmos", {"G": "out_n", "D": "out_p", "S": "vdd", "B": "vdd"}),
}
sym_pins = {"G": 1, "D": 2, "S": 2, "B": 3}  # MOSFET S/D permute symmetry
nets = sorted({n for _, pins in elements.values() for n in pins.values()})
e_cls = {e: t for e, (t, _) in elements.items()}
n_cls = {n: ("SUPPLY" if n in ("vdd", "vss") else ("PORT_IN" if n.startswith("in_") else "INT")) for n in nets}
for it in range(5):
    new_e = {e: (t, tuple(sorted((sym_pins[p], n_cls[n]) for p, n in pins.items()))) for e, (t, pins) in elements.items()}
    new_n = {n: (n_cls[n], tuple(sorted((sym_pins[p], new_e[e]) for e, (_, pins) in elements.items() for p, pn in pins.items() if pn == n))) for n in nets}
    e_map = {sig: f"EC{i}" for i, sig in enumerate(sorted(set(new_e.values())))}
    n_map = {sig: f"NC{i}" for i, sig in enumerate(sorted(set(new_n.values())))}
    e_next, n_next = {e: e_map[s] for e, s in new_e.items()}, {n: n_map[s] for n, s in new_n.items()}
    if e_next == e_cls and n_next == n_cls:
        print(f"1-WL fixed point at iter {it}: e_cls={e_cls}, n_cls={ {k: v for k, v in n_cls.items() if k not in ('vdd', 'vss')} }")
        break
    e_cls, n_cls = e_next, n_next
```

Observed output (`2026-11-19`):
```text
1-WL fixed point at iter 1: e_cls={'M1': 'EC0', 'M2': 'EC0', 'P1': 'EC1', 'P2': 'EC1'}, n_cls={'in_n': 'NC2', 'in_p': 'NC2', 'out_n': 'NC0', 'out_p': 'NC0', 'tail': 'NC1'}
```
Unless external top-level pin bindings distinguish `in_p` from `in_n` (or `ResolveAutomorphisms` breaks the `NC2` / `EC0` symmetry), pure `1-WL` partition refinement halts permanently at iteration 1 with paired equivalence classes `{M1, M2}` and `{P1, P2}`.

### 4. Six-Level Performance and Resource Footprint Matrix (`L1`–`L6`)

`Basis: documentation + source + derived`

Physical EDA toolchains exhibit sharply asymmetric costs across human authoring, compiler builds, interactive incremental timing, full-chip placement/routing, signoff geometry/isomorphism checks, and memory/artifact footprints:

| Level | Metric / Domain | `OpenROAD` (`gpl`/`dpl`/`cts`/`drt`/`ant`) | `OpenSTA` (Timing & `CRPR`) | `KLayout` / `Magic` (`DRC` & Extract) | `Netgen` (`LVS`) |
|---|---|---|---|---|---|
| **L1: Human & Agent Authoring Velocity** | Rule/constraint LoC, repair churn & failure loops | Tcl/Python flow configs (`100–500 LoC`); density/DRC parameter tuning requires `1–4` full PnR iterations (`hours`). | `SDC` constraints (`50–2,000 LoC`); wildcard `set_false_path` or missing `set_propagated_clock` causes silent escapes undetectable by syntax linting. | Foundry DRC decks (`1,000–15,000 LoC` Ruby/Tcl); `tiles()` vs `deep` mode flag flips require careful manual halo auditing (`tile_borders`). | Setup Tcl (`100–400 LoC`); symmetric subcircuit `permute` / blackbox property tolerances frequently iterate per IP cell. |
| **L2: Toolchain Build Time & Memory** | Cold compile time & compiler RSS | Bazel C++20 monorepo (`BUILD.bazel`) + Boost/Lemon/Eigen/OR-Tools (+ optional `Kokkos`/`CUDA` via `:gpl_kokkos`): `15–45 min` multi-core build, `2–6 GB` linker peak RSS. | Lean standalone C++ + Bison/Flex (`SpefLex.ll`/`SpefParse.yy`, `CMakeLists.txt`): `~1–3 min` build, `< 1 GB` compiler RSS. | `KLayout` Qt/Ruby/Python C++ build: `10–25 min`; `Magic` C (`autoconf`/`make`): `< 1 min`, `< 200 MB` RSS. | Minimal pure C + Tcl (`base/Makefile`, `~25` `.c` files): `< 15 s` build, `< 100 MB` RSS. |
| **L3: Interactive / Incremental Latency** | Incremental update & feedback turnaround | `Opendp` incremental legalization (`incremental=true` in `Opendp.cpp:132`): `ms–s`; full `doNesterovPlace` (`500–1500` iters) + `TritonRoute`: `minutes–hours`. | Incremental graph timing update after single ECO gate swap: `< 50 ms–500 ms` (lazy dirty-vertex arrival/required propagation). | `Magic` `DRCContinuous` (`drc/DRCcontin.c:495`): `< 10–50 ms` per interactive paint stroke (`GEO_EXPAND` by `DRCTechHalo`). `KLayout` batch `deep` deck: `seconds–minutes`. | Cell-level hierarchical compare: `< 1 s`; flat macro LVS with symmetry resolution: `seconds–minutes`. |
| **L4: Runtime Execution Throughput** | Inner-loop algorithmic complexity & throughput | `CpuFftBackend` (`fft.cpp`): $O(M^2 \log M)$ per step (`Ooura` DCT-II/DST-II), `~5–20×` slower than `GpuFftBackend` (`Kokkos`/cuFFT) at `1M+` instances (`DOI: 10.1109/TCAD.2018.2859220`). | `NLDM` lookup `O(1)` vs `CCS` `C_eff` root-finding (`~3–8×` slower per arc); graph traversal $O(|V|+|E|)$ per mode/corner; `CRPR` LCA walk bounded by clock-tree depth `O(d)`. | `Magic` corner-stitch neighbor query `O(1)` expected; `KLayout` scanline `dbEdgeProcessor` `O((V + k) log V)` edges/s; multi-core tile scaling near-linear when `deep` disabled. | `Iterate()` `O(|E| + |N|)` per WL pass; `ResolveAutomorphisms` worst-case exponential on symmetric graphs lacking pin/property asymmetry. |
| **L5: Verification / Signoff Checking Speed** | Full-chip DRC/STA/LVS signoff latency | `AntennaChecker` (`ant`): $O(\text{nets} \times \text{layers})$ linear pass (`seconds`); `PlacementDRC` site check `< 5 s`. | Multi-corner multi-mode (`MCMM`) full-chip `SPEF` + `CRPR` + `POCV`: `minutes` for `1M–10M` instances. | `KLayout` `deep` hierarchical DRC compresses `10^8` flat SRAM shapes back to `10^4` unique cell ops (`minutes` vs `hours` flat). | Hierarchical cell-by-cell bottom-up compare avoids flattening repetitive memory arrays (`seconds` vs `hours` flattened). |
| **L6: RAM, Disk & Artifact Footprints** | Peak RSS & interchange serialization sizes | `OpenDB` `.odb` binary (`100 MB–4 GB`); `RePlAce` bin grids + `TritonRoute` 3D track/maze tables drive `8–64+ GB` peak RSS on `1M–5M` cells. | `SPEF` ASCII RC networks routinely reach `1–20 GB` on disk (`2–4×` peak parser RSS if not compressed `.spef.gz`); timing graph `~200–600 B/pin`. | `GDSII` uncompressed vs `OASIS` (`~10–30×` smaller); `Magic` corner-stitched tiles `~3×` polygon memory (`48 B+/tile` on 64-bit); `KLayout` `DeepShapeStore` shares cell sub-trees. | Extracted `.spice` netlists `10 MB–2 GB`; `ElementClass`/`NodeClass` hash/list nodes `< 2 GB` hierarchically, `> 16 GB` if forced flat. |

### 5. Human Comprehensibility (`C1`) and Conceptual Simplicity / Universal Model Refinement (`C2`)

#### 5.1 Human Comprehensibility and Mental-Model Ergonomics (`C1`)
`Basis: source + derived`

- **Nonlocal Imperative Ordering in `SDC` Timing Contracts**: A human engineer inspecting a single clock or path constraint cannot tell locally whether it is enforced. A single `set_false_path -through ...` in an included Tcl file (`falsePathPriority() = 4000`, `ExceptionPath.hh:101`) silently voids `create_clock` and `set_multicycle_path` (`2000`) declarations elsewhere, while `set_multicycle_path 3 -setup` subtly rewrites the hold edge unless a second, seemingly inverse command (`set_multicycle_path 2 -hold`) accompanies it. Furthermore, forgetting `set_propagated_clock` changes zero lines of report structure unless a reader inspects the `clock network delay` column in `report_checks` and notices `0.00`.
- **Silent Mode Switching in Geometric Signoff**: In `KLayout` `_drc_engine.rb:1140-1185`, calling `tiles(500.um)` reads like a pure performance hint (`parallelize over 500 um tiles`), yet mutates `@deep = false` as an invisible side effect—breaking downstream connectivity assumptions (`antenna_check`) without raising a type error or warning.
- **Legibility of Failures**: `OpenSTA`'s path-based arrival/required breakdown (`report_checks`) and `Magic`'s visual feedback boxes (`DRCCheckThis`) provide strong local human diagnostics. By contrast, `Netgen` `PrintIllegalClasses` (`netcmp.c:1798-2134`) dumps fragmented hash equivalence classes (`ElementClass`/`NodeClass`) where an unmatched node near a symmetric boundary can fracture half the circuit's partitions before reporting a clear root cause.

#### 5.2 Simplicity, Orthogonality, and Universal Model Refinement (`C2`)
`Basis: derived`

Applying Felleisen's macro-expressibility lens (whether removing a concept forces nonlocal boilerplate) and Ousterhout's deep-module principle (small, invariant-enforcing interfaces hiding complex mechanics):

1. **Unifying `SDC` Exceptions into Typed Cycle-Relational Contracts**: Today `OpenSTA` splits synchronous cycle geometry (`create_clock`, `set_multicycle_path`, `set_false_path`, `set_max_delay`) across an imperative mutation sequence evaluated through a `4000 > 3000 > 2000` override table (`ExceptionPath.hh:101-106`). The minimal, orthogonal universal refinement replaces imperative overrides with a **Typed Launch-to-Capture Epoch Relation** $R(p) \in \{ \text{Sync}(\Delta_{\mathrm{setup}}, \Delta_{\mathrm{hold}}), \text{SkewBounded}(\delta), \text{AsyncCDC}(\text{meta-proof}) \}$ where every `AsyncCDC` exemption requires an explicit synchronizer/FIFO proof obligation (`set_false_path` ceases to be an untyped wildcard eraser), `setup` and `hold` cycle offsets are co-specified in one record (making unpaired `-setup` shifts unrepresentable), and propagated-clock mode is the default post-CTS invariant rather than an opt-in Tcl flag.
2. **Halo-Indexed Local vs. Topological Operator Typing in Physical DRC**: Instead of exposing raw `tiles()`, `no_borders`, and `deep` flags as uncoupled mutable globals (`_drc_engine.rb:1140-1185`), a deep-module DRC IR classifies every operator algebraically:
   - *Finite-radius morphological operators* (width, space, notch, enclosure, density) compute a static interaction radius $r_{\mathrm{op}}$ from the expression AST (`DRCTechHalo` generalized per-rule), automatically enforcing `tile_border >= sum(r_op)` (zero silent cross-tile misses);
   - *Unbounded net-topological operators* (`antenna_check`, `l2n` short/open) carry a `NetTopological` effect forbidding tile truncation altogether and routing automatically through hierarchical `DeepShapeStore` or full-net union-find.

## Boundaries

- **Encrypted Commercial Foundry DRC/LVS Decks & SVRF Semantics (`not examined`)**: This report examined open-source `KLayout`, `Magic`, and `Netgen` engines; proprietary foundry decks written for Siemens Calibre SVRF / Synopsys IC Validator (including complex equation-based DRC, multi-layer CMP fill synthesis, and encrypted device recognition) were not examined.
- **Lithography OPC, Inverse Lithography (ILT), and SRAF Placement (`unsupported` / `not examined`)**: None of the pinned open-source signoff tools at these revisions perform full sub-wavelength aerial-image optical proximity correction or etch-bias simulation; mask manufacturability beyond geometric design rules is outside scope.
- **Dynamic IR-Drop, Electromigration, and Full SPICE Transient Timing (`known not to apply`)**: `OpenSTA` static timing assumes fixed corner rail voltages and linearized `CCS`/`NLDM` driver models; dynamic simultaneous-switching noise (`dI/dt`), self-heating, and analog setup/hold metastability characterization require SPICE transient and dedicated PDN solvers not covered here.
- **Non-Manhattan / Curvilinear Silicon Photonics in `Magic` (`known not to apply`)**: `Magic`'s corner-stitched tile plane (`tiles/tile.h`) is fundamentally rectilinear (45-degree diagonals encoded via split rectangular tiles); smooth Bézier/curvilinear waveguide DRC requires `KLayout`'s arbitrary-angle `Polygon` / `Region` engine.
- **Sub-5nm GAA/Forksheet Multi-Patterning Coloring in `Netgen` (`unknown`)**: While `Netgen` handles arbitrary SPICE netlist topology and device property folding, end-to-end mask-coloring-aware parasitic extraction and double-patterning decomposition across `Magic` + `Netgen` at sub-5nm nodes were not experimentally verified at these revisions.

## Evidence

- **Upstream Repository Sources Inspected (`2026-11-19`)**:
  - `The-OpenROAD-Project/OpenROAD` @ `0c210b22ed42ed677ff28ff539a11bc37a7453f9`: `CMakeLists.txt` (CMake removal notice, Nov 1, 2026); `BUILD.bazel`; `openroad/gpl/BUILD` (`:gpl`, `:gpl_kokkos`, `fftsg.cpp`/`fftsg2d.cpp`); `openroad/gpl/src/fft.cpp:1-288` (`CpuFftBackend`, `ddct2d`/`ddsct2d`/`ddcst2d`, `bin_size_x / bin_size_y` aspect scaling, `phi_value = electro_x = electro_y = 0.0f`); `openroad/gpl/src/nesterovPlace.cpp:1191-1699` (`doBackTracking`, `doNesterovPlace`, `curA`/`coeff`, `checkInvalidValues`, `GPL 306`); `openroad/dpl/src/Opendp.cpp:110-257` (`detailedPlacement`, `adjustNodesOrient`); `openroad/cts/src/HTreeBuilder.cpp:143-167` (`sink_clustering_size`, `sink_clustering_max_diameter`); `openroad/ant/src/AntennaChecker.cc:295-685` (`calculatePAR`, `calculateCAR`, `pwl_pair` diffusion diode reduction).
  - `parallaxsw/OpenSTA` @ `cc510896e8e097771100d7dec4f5cbfdb3d6d71a`: `CMakeLists.txt`; `dcalc/CcsCeffDelayCalc.cc:1-70`; `search/PocvMode.cc:31-46` (`scalar`, `normal`, `skew_normal`); `search/Crpr.cc:55-296` (`CheckCrpr::checkCrpr1`, `findCrpr`, `genClkSrcPaths`, `findCrpr1`, `crpr_sigma2 = src_arrival.stdDev2() + tgt_arrival.stdDev2()`); `include/sta/ExceptionPath.hh:97-111` (`falsePathPriority() = 4000`, `pathDelayPriority() = 3000`, `multiCyclePathPriority() = 2000`); `sdc/ExceptionPath.cc:180-200, 647-762, 2460-2476` (`FalsePath`, `MultiCyclePath::pathMultiplier`, qualifier bitmask); `sdc/Sdc.cc:1755-1772` (`setPropagatedClock`); `sdc/Sdc.tcl:3255-3299` (`set_multicycle_path`).
  - `KLayout/klayout` @ `53911acd6dfaa113c188d11d20b2ae290aa60a6b`: `src/db/db/db.pro`; `src/db/db/dbDeepRegion.cc:137-193`; `src/db/db/dbLayoutToNetlist.cc:1972-1989` (`LayoutToNetlist::antenna_check`); `src/drc/drc/built-in-macros/_drc_engine.rb:1140-1185, 2495-2508` (`tiles`, `tile_borders`, `no_borders`, `antenna_check`).
  - `RTimothyEdwards/magic` @ `cc0360b3a4c3ca4b3c81ab69379be630c5d6df87`: `tiles/tile.h:46-105` (`struct tile`, `TOP`/`RIGHT` corner-stitch macros); `drc/DRCcontin.c:152-717` (`DRCCheckThis`, `DRCContinuous`, `GEO_EXPAND(..., DRCTechHalo, ...)`).
  - `RTimothyEdwards/netgen` @ `e2a49567d5e3e451d51130de0227678be31f32e0`: `base/Makefile`; `base/netcmp.c:3020-3065, 4205-4991, 6865-7090` (`FractureElementClass`, `Iterate`, `series_optimize`, `parallel_optimize`, `ResolveAutomorphisms`, `PermuteSetup`).
- **Literature & Post-Mortems**:
  - C.-K. Cheng, A. B. Kahng, I. Kang, and L. Wang, "RePlAce: Advancing Solution Quality and Routability Validation in Global Placement," *IEEE TCAD*, 2019, `DOI: 10.1109/TCAD.2018.2859220`.
  - T. Ajayi et al., "Toward an Open-Source Digital Flow: First Learnings from the OpenROAD Project," *Proc. ACM/IEEE DAC*, 2019, `DOI: 10.1145/3316781.3326334`.
  - J. K. Ousterhout, "Corner Stitching: A Data-Structuring Technique for VLSI Layout Tools," *IEEE TCAD*, 3(1):87–100, Feb. 1984, `DOI: 10.1109/TCAD.1984.1270061`.
  - Efabless / SkyWater `sky130` Caravel MPW-1 silicon hold-violation post-mortem (zero reported clock network delay in OpenSTA due to ideal clock configuration, omitting hold-buffer insertion).
- **Execution Environment**: Standalone Python 3.13.x standard-library probes executed directly (`2026-11-19`) verifying `WA` overflow/stabilization, 4-bin Neumann DCT-II Poisson symmetry, `POCV`/`CRPR` hold-slack sensitivity, and `1-WL` differential-pair automorphism stalling.

## Revalidation

To cheaply verify whether upstream changes alter these findings:

1. **Check `OpenSTA` `CRPR` & `SDC` Exception Priority Invariants** (inspect for changes in variance subtraction or priority constants):
   ```bash
   curl -sSL "https://raw.githubusercontent.com/parallaxsw/OpenSTA/HEAD/search/Crpr.cc" | grep -n -A 12 "findCrpr1("
   curl -sSL "https://raw.githubusercontent.com/parallaxsw/OpenSTA/HEAD/include/sta/ExceptionPath.hh" | grep -n "Priority()"
   ```
2. **Check `KLayout` `tiles` / `@deep` Side Effect and `OpenROAD` Poisson/Nesterov Guards**:
   ```bash
   curl -sSL "https://raw.githubusercontent.com/KLayout/klayout/HEAD/src/drc/drc/built-in-macros/_drc_engine.rb" | grep -n -A 6 "def tiles("
   curl -sSL "https://raw.githubusercontent.com/The-OpenROAD-Project/OpenROAD/HEAD/openroad/gpl/src/nesterovPlace.cpp" | grep -n -A 8 "checkInvalidValues("
   ```
3. **Re-run Mathematical Micro-Probes**: Execute the two embedded Python 3 scripts from **Findings** (§2.4 and §3.3) with `python3 -` to confirm exact numerical reproducibility of `WA` shift stabilization, `POCV+CRPR` variance subtraction, and `1-WL` symmetric partition stalling.
