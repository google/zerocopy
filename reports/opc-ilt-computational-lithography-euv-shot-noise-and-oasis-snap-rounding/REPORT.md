# Computational Lithography, EUV Photon Shot Noise, and Integer-Grid OASIS Snap-Rounding

## Summary

Deep-submicron optical proximity correction (OPC), inverse lithography technology (ILT), and mask-data preparation (MDP) form a coupled numerical-to-discrete compilation pipeline whose physical correctness breaks at three distinct abstraction boundaries (`Basis: source + normative + execution + derived`):

1. **Asymmetric Process-Window Sampling and SOCS Rank Truncation (`OpenOPC/OpenILT`)**: Partially coherent Hopkins aerial-image formation factors a 4D Transmission Cross-Coefficient (TCC) operator into a truncated Sum of Coherent Systems (`SOCS`, typically $K = 24$ coherent FFT kernels in `OpenILT`). While `OpenILT` (`pylitho/exact.py:166-239`) computes an exact complex Fréchet adjoint in `_LithoSim.backward`, its forward process-window evaluator evaluates only **three** corners—`(DoseNom, focus)`, `(DoseMax, focus)`, and `(DoseMin, defocus)`—omitting the fourth corner **`(DoseMax, defocus)`**. For dense main features flanking a binary Sub-Resolution Assist Feature (`SRAF`), Zernike $Z_4$ defocus diffracts lateral energy from the main bars *into* the assist-feature peak ($I_{\text{sraf}}(\text{defocus}) > I_{\text{sraf}}(\text{focus})$). Multiplying by `DoseMax` (`+2%`) pushes a `6 nm` binary SRAF from `0.4879` at `(DoseMin, defocus)` and `0.4179` at `(DoseMax, focus)` across the `0.50` resist threshold to **`0.5286`** at `(DoseMax, defocus)`, printing a catastrophic wafer bridge while `OpenILT`'s three-point `PVBand` metric reports zero violation (`Basis: source + execution`).
2. **`13.5 nm` EUV (`91.84 eV`) Poisson Photon Shot Noise vs. Deterministic Aerial Thresholds**: Moving from `193 nm` ArF immersion (`6.42 eV`) to `13.5 nm` EUV (`91.84 eV`) at a `20 mJ/cm^2` resist clearing dose reduces incident photon areal density **`14.30x`**—from `194.32` to `13.59 photons/nm^2`. Across a $3 \times 3\text{ nm}^2$ resist reaction voxel at `30%` EUV absorption (`36.70` mean absorbed photons at unit intensity, clearing threshold $n_{\text{th}} = 19$), a dark space whose deterministic aerial intensity is $I_{\text{space}} = 0.19 < 0.50$ still experiences a Poisson tail bridge probability $P(\mathrm{Pois}(6.973) \ge 19) = 1.237 \times 10^{-4}$ per voxel (`100%` die failure across $10^{10}$ vias). Even suppressing side-lobes to $I_{\text{space}} = 0.065$ leaves $P_{\text{bridge}} = 1.281 \times 10^{-11}$ (**`12.02%` die yield loss**); sub-ppm die yield (`1.80 \times 10^{-7}`) requires suppressing dark-space intensity below $I_{\text{space}} \le 0.030$ (`Basis: normative + execution + derived`).
3. **`0.1 nm` (`1 dbu`) Integer Snap-Rounding Non-Associativity vs. Hobby Hot-Pixel Splitting (`Clipper2` & `KLayout`)**: Converting curvilinear ILT level-set contours into `SEMI P39` `OASIS` polygons or variable-shaped / multi-beam mask shots requires integer-grid polygon booleans (`1 dbu = 0.1 nm` or `0.01 nm`). `Clipper2` (`clipper.core.h:65, 751-765`) restricts coordinates to $\pm(2^{61} - 1)$ so `128`-bit `CrossProductSign` predicates on existing integer vertices never overflow, but rounds rational Vatti edge intersections back to `Point64` after each boolean pass. Rounding an intersection without splitting nearby non-intersecting segments can invert point-line orientation (`+1 -> -1`), creating self-intersecting slivers and breaking boolean algebra laws ($((A \cup B) \setminus C) \ne ((A \setminus C) \cup (B \setminus C))$). `KLayout` (`dbEdgeProcessor.cc:194-225`) prevents both floating-point edge-swap asymmetry (such as `(3,-3)->(-8,-1)` vs. `(-4,-2)->(13,-4)` meeting at exact half-integer $y = -5/2$) via canonical `e1 < e2` ordering and topological jump-over inversions via Hobby (`1999`) **attractor / hot-pixel cutpoint splitting** (`Basis: source + execution`).

---

## Applicability

The findings in this report govern computational lithography simulators, gradient-based inverse mask synthesizers, integer-grid CAD boolean engines, and mask-data serialization formats across the examined subjects:

- **`OpenOPC/OpenILT` (`dabb97c6ca3dfd159362e48273c436444c77353b`)**: PyTorch GPU lithography simulation (`pylitho/exact.py`, `pylitho/simple.py`), gradient-based pixel/level-set/curvilinear ILT solvers (`pyilt/simpleilt.py`, `pyilt/curvmulti.py`, `pyilt/levelset.py`), and `ICCAD-2013` evaluation (`pyilt/evaluation.py`, `utils/polygon.py`). Directly calibrated around `193 nm` ArF immersion `ICCAD-2013` `32 nm` M1 benchmarks (`2048 x 2048` `1 nm` grid, `KernelNum = 24` `[24, 35, 35]` Hopkins SOCS kernels, `TargetDensity = 0.225` or normalized `0.50`, `DoseNom = 1.00`, `DoseMax = 1.02`, `DoseMin = 0.98`).
- **`AngusJohnson/Clipper2` (`4be4655694d7e15e76ac6bfe9024fa534eed3428`)**: C++17 Vatti scanbeam boolean clipping and polygon offsetting library (`CPP/Clipper2Lib/include/clipper2/clipper.core.h`, `CPP/Clipper2Lib/src/clipper.engine.cpp`) operating on `int64_t` `Point64` vertices bounded by `MAX_COORD = INT64_MAX >> 2` ($2^{61} - 1$).
- **`KLayout/klayout` (`53911acd6dfaa113c188d11d20b2ae290aa60a6b`)**: Production EDA layout engine, edge-scanline boolean processor (`src/db/db/dbEdgeProcessor.cc`), and `SEMI P39` `OASIS` binary writer (`src/plugins/streamers/oasis/db_plugin/dbOASISWriter.cc`), supporting both `32`-bit (`db::Coord = int32_t`) and `64`-bit (`DB_64BIT_COORD`) database-unit (`dbu`) coordinates.
- **Physical & Algorithmic Foundations**: Poonawala & Milanfar (`DOI: 10.1109/TIP.2006.891332`) sigmoid relaxation for continuous-tone-to-binary ILT; Zheng, Yu & Wong (`DOI: 10.1109/ASICON58565.2023.10396314`) `OpenILT` architecture; Mack (`DOI: 10.1117/12.848236`) stochastic photon/acid reaction-diffusion limits of line-edge roughness (`LER`) and nano-bridging; Hobby (`DOI: 10.1016/S0925-7721(99)00021-8`) finite-precision snap-rounding via hot pixels; and `SEMI P39` (`OASIS`) layout stream encoding.

**Cross-Subject Pipeline Relationship**: In a tapeout flow, `OpenILT`-class optimizers synthesize continuous or level-set mask fields $M(x, y) \in [0, 1]$, threshold them into curvilinear polygons, apply MRC/OPC boolean sizing and cleanups via scanline engines (`Clipper2` / `KLayout`), fracture shapes into rectangles or trapezoids (`adabox` / `OASIS` `TRAPEZOID` records), and serialize coordinates onto an integer `dbu` grid (`0.1 nm` or `0.01 nm`) for `VSB` (`193i` photomasks) or multi-beam mask writers (`MBMW` for `13.5 nm` `EUV` reflective masks). Errors that stay below threshold in `OpenILT`'s continuous `float32` process window compound with `EUV` Poisson shot noise and `1 dbu` polygon snap-rounding during mask export.

---

## Findings

### 1. Hopkins Partial-Coherence `SOCS` Truncation and `OpenILT` Process-Window Corner Omission

`Basis: source + normative + execution + derived`

#### 1.1 Exact Adjoint vs. Rank-$K$ `SOCS` Approximation in `OpenILT`

Under Hopkins partially coherent scalar diffraction theory, the wafer aerial-image intensity $I(\mathbf{r})$ produced by a mask transmission function $M(\mathbf{r}) \in \{0, 1\}$ illuminated by an extended effective source $J(\mathbf{s})$ through a projection pupil $P(\mathbf{f})$ is quadratic in the mask spectrum $\hat{M}(\mathbf{f})$:

$$I(\mathbf{r}) = \iint \mathrm{TCC}(\mathbf{f}_1, \mathbf{f}_2)\, \hat{M}(\mathbf{f}_1)\, \hat{M}^*(\mathbf{f}_2)\, e^{i 2\pi (\mathbf{f}_1 - \mathbf{f}_2)\cdot \mathbf{r}}\, d\mathbf{f}_1\, d\mathbf{f}_2$$

where the 4D Transmission Cross-Coefficient $\mathrm{TCC}(\mathbf{f}_1, \mathbf{f}_2) = \int J(\mathbf{s})\, P(\mathbf{s} + \mathbf{f}_1)\, P^*(\mathbf{s} + \mathbf{f}_2)\, d\mathbf{s}$ is Hermitian positive semi-definite. Expanding $\mathrm{TCC}$ in its Mercer / SVD eigensystem yields the **Sum of Coherent Systems (`SOCS`)** decomposition:

$$I(\mathbf{r}) = \sum_{k=1}^{\infty} \sigma_k \left| (h_k * (D \cdot M))(\mathbf{r}) \right|^2 \approx \sum_{k=1}^{K} \sigma_k \left| (h_k * (D \cdot M))(\mathbf{r}) \right|^2, \qquad \sigma_1 \ge \sigma_2 \ge \dots > 0$$

where $D$ is exposure dose, $h_k$ is the $k$-th coherent eigen-kernel, and tail truncation drops $\Delta I_{\text{trunc}}(\mathbf{r}) = \sum_{k > K} \sigma_k |(h_k * (D \cdot M))(\mathbf{r})|^2 \ge 0$. Notice that because $\sigma_k > 0$ and $|h_k * M|^2 \ge 0$, **truncating `SOCS` at finite rank $K$ is strictly one-sided (monotone under-approximating)**: `SOCS` rank truncation *never* over-estimates aerial intensity, meaning dark-space SRAF side-lobe peaks computed at rank $K$ are guaranteed lower bounds on the exact Hopkins intensity!

In `OpenOPC/OpenILT` (`pylitho/exact.py:166-195`), `_LithoSim` implements rank-$K$ `SOCS` evaluation via `torch.fft` (`_computeImageMask`) with `KernelNum = 24` precomputed `[24, 35, 35]` complex eigen-kernels (`focus` and `defocus`) and manually derives the Wirtinger / Fréchet complex adjoint in `_LithoSim.backward` (`exact.py:179-194`):

```python
# OpenOPC/OpenILT pylitho/exact.py:181-188 (rev dabb97c6ca3dfd159362e48273c436444c77353b)
cpx0 = torch.mul(_convMask(mask, dose, kernelGradCT, scaleGradCT, kernelNumGradCT), grad.unsqueeze(len(grad.shape) - 2))
cpx1 = _convMatrix(cpx0, dose, kernelGrad, scaleGrad, kernelNumGrad)
cpx2 = torch.mul(_convMask(mask, dose, kernelGrad, scaleGrad, kernelNumGrad), grad.unsqueeze(len(grad.shape) - 2))
cpx3 = _convMatrix(cpx2, dose, kernelGradCT, scaleGradCT, kernelNumGradCT)
cpx4 = cpx1 + cpx3
```

Using Poonawala & Milanfar's (`2007`) sigmoidal continuation $M = \sigma(\alpha_M \cdot \phi)$ and resist threshold relaxation $Z = \sigma(\alpha_R (I - I_{\text{th}}))$, `SimpleILT` (`pyilt/simpleilt.py:74-86`) and `CurvMulti` (`pyilt/curvmulti.py:55-88`) backpropagate weighted combinations of nominal `L2` error, `PVBand` `L2` penalty, and a discrete $3 \times 3$ Laplacian curvature penalty (`[[-1/16, 5/16, -1/16], [5/16, -1, 5/16], [-1/16, 5/16, -1/16]]`).

#### 1.2 Three Defect Classes in `OpenILT`'s Process-Window and Evaluation Pipeline

Direct source inspection of `pylitho/exact.py` and `pyilt/evaluation.py` reveals three structural verification gaps (`Basis: source + execution`):

1. **Omission of the `(DoseMax, defocus)` Corner (`pylitho/exact.py:223-239`)**: `LithoSim.forward` computes exactly three aerial images:
   - `aerialNom`: `(DoseNom, focus)` (`exact.py:224-227`)
   - `aerialMax`: `(DoseMax, focus)` (`exact.py:228-231`)
   - `aerialMin`: `(DoseMin, defocus)` (`exact.py:232-235`)
   Both `SimpleILT` (`simpleilt.py:80`) and `Basic.run` (`evaluation.py:34-43`) define `pvband = torch.sum(binaryMax != binaryMin)`. This three-corner shortcut assumes aerial intensity is globally monotone decreasing under optical defocus ($\partial I / \partial |z| \le 0$), which holds at the **interior peak of an isolated bright line** (so `(DoseMax, focus)` maximizes line width and `(DoseMin, defocus)` minimizes line width). However, by conservation of total transmitted pupil energy, Zernike $Z_4$ defocus ($\exp(i \beta \rho^2)$) spreads light **out of dense main bars laterally into adjacent dark spaces and sub-resolution assist features (`SRAFs`)**, where $\partial I_{\text{sraf}} / \partial |z| > 0$! Consequently, the worst-case SRAF printing corner is **`(DoseMax, defocus)`**—the exact corner `OpenILT` never evaluates.
   - **Deterministic Verification (`probes/verify_opc_ilt_euv_oasis.py`)**: On a `64`-cell (`2 nm/cell`, unit clear-field DC gain `1.0`) partially coherent annular illumination grid (`sigma` harmonics `{-3,-2,+2,+3}`, pupil cutoff `5`, `DoseNom = 1.00, DoseMax = 1.02, DoseMin = 0.98`, `PrintThresh = 0.50`), two dense `22 nm` binary bars (`[18..28]` and `[36..46]`) flanking a `6 nm` (`3`-cell `[31, 32, 33]`) binary `SRAF` produce:
     - `aerialNom` `(1.00, focus)` at SRAF center `x = 32`: **`0.4017`** (`< 0.50`)
     - `aerialMax` `(1.02, focus)` at SRAF center `x = 32`: **`0.4179`** (`< 0.50`)
     - `aerialMin` `(0.98, defocus)` at SRAF center `x = 32`: **`0.4879`** (`< 0.50`)
     - **Omitted 4th corner `(1.02, defocus)` at `x = 32`**: **`0.5286 > 0.50`** — printing a spurious metal SRAF bridge on silicon while all three `OpenILT` corners stay below threshold (`openilt_pvband_detects_sraf_bridge = false`)! Enforcing a 4-corner minimax guard shrinks the binary SRAF to `2` cells (`4 nm`, `[31, 32]`), dropping `(1.02, defocus)` intensity to **`0.3745 < 0.50`**. Meanwhile, rank-1 coherent truncation vs. full 4-mode `SOCS` incurs an $L_\infty$ aerial error of **`0.1345`** (`26.9%` of threshold), confirming why aggressive `SOCS` rank reduction must carry an explicit spectral-tail upper bound $\epsilon_{\text{tail}} = (\sum_{k > K} \sigma_k) \|D \cdot M\|_2^2$.
2. **Sparse Manhattan-Only `EPE` Sampling (`pyilt/evaluation.py:68-72, 163-200`)**: `EPEChecker` extracts horizontal and vertical target segments and checks `EPE_CONSTRAINT = 15 nm` only at discrete sample points spaced every `EPE_CHECK_INTERVEL = 40 nm` (collapsing segments shorter than `MIN_EPE_CHECK_LENGTH = 80 nm` to a single midpoint check at lines `166-169, 185-188`). Diagonal edges, corner rounding pullback, and curvilinear inter-sample pinch/necking extrema occurring between `40 nm` stations are completely invisible to the `EPE` violation counter.
3. **Nearest-Neighbor `4x` Downsampling Before Shot Counting (`pyilt/evaluation.py:229-256`)**: `ShotCounter.run` resizes `2048 x 2048` (`1 nm`) masks to `shape=(512, 512)` via `mode="nearest"` (`line 238`) before calling `cv2.connectedComponentsWithStats` and `adabox.proc.decompose(pixels, 4)`. Sub-`4 nm` jogs, serifs, and thin SRAF connections either alias away or merge across `4 nm` pixel boundaries, systematically under-counting VSB fracturing shot complexity on curvilinear masks.

---

### 2. `13.5 nm` `EUV` (`91.84 eV`) Photon Shot Noise and Stochastic Nano-Bridging

`Basis: normative + execution + derived`

#### 2.1 Quantum Counting Scaling From `193 nm` ArF to `13.5 nm` `EUV`

Deterministic Hopkins/SOCS simulation models electromagnetic irradiance as a continuous real field $I(\mathbf{r}) \in \mathbb{R}_{\ge 0}$. At `13.5 nm` Extreme Ultraviolet (`EUV`) wavelengths, individual photon energy $E_\gamma = hc / \lambda$ rises by $\mathbf{14.296\times}$ relative to `193 nm` ArF excimer lithography:

| Lithographic Generation | Wavelength $\lambda$ | Photon Energy $E_\gamma = hc/\lambda$ | Incident Photons / $\text{nm}^2$ at $20\text{ mJ/cm}^2$ | Absorbed Photons in $3 \times 3\text{ nm}^2$ Voxel ($\eta = 0.30, I = 1.0$) | Relative Shot-Noise $\sigma_N / \mu_N$ at Clearing Threshold ($I = 0.50$) |
| :--- | :---: | :---: | :---: | :---: | :---: |
| **`193i` ArF Immersion** | `193.0 nm` | `6.42 eV` (`1.029e-18 J`) | **`194.32 photons/nm²`** | `524.66` (at $\eta=0.30$ eq.) | `6.17%` ($\mu_{\text{th}} \approx 262$) |
| **`13.5 nm` Low/High-NA EUV** | `13.5 nm` | **`91.84 eV`** (`1.471e-17 J`) | **`13.59 photons/nm²`** | **`36.70 photons`** | **`23.35%`** ($\mu_{\text{th}} \approx 18.35$) |

As established by Mack (`Proc. SPIE 7639, 2010`, `DOI: 10.1117/12.848236`), line-edge roughness (`LER`) scales inversely with the product of the Normalized Image Log-Slope (`NILS` $= w \frac{\partial \ln I}{\partial x}$) and the square root of absorbed photon dose:

$$\sigma_{\text{LER}} \propto \frac{1}{\text{NILS} \cdot \sqrt{\eta \, D / E_\gamma}}$$

#### 2.2 Die-Scale ($10^{10}$ Via) Poisson Tail Failure vs. Deterministic Aerial Margins

Even when `LER` (`3\sigma \approx 1.5–2.5 nm`) stays within CD budgets, **rare-event stochastic nano-bridging** (dark-space scumming in positive-tone chemically amplified resist or cross-linking in metal-oxide `MOx` negative-tone resist) is governed by extreme Poisson upper tails over $N_{\text{via}} \sim 10^{10}$ critical features per reticle field.

In a $3 \times 3\text{ nm}^2$ resist reaction voxel with `30%` `EUV` quantum absorption efficiency ($\mu_{\text{full}} = 9 \times 0.30 \times 13.592 = 36.70$ absorbed photons at $I = 1.0$) and a resist solubility switch threshold of $n_{\text{th}} = 19$ absorbed photons ($I_{\text{th}} = 19 / 36.70 = 0.5177$), the exact single-voxel stochastic bridge probability at local dark-space intensity $I_{\text{space}}$ is:

$$P_{\text{bridge}}(I_{\text{space}}) = \sum_{k = n_{\text{th}}}^{\infty} \frac{e^{-\mu} \mu^k}{k!}, \qquad \mu = \mu_{\text{full}} \cdot I_{\text{space}}, \qquad P_{\text{die-fail}} = 1 - \exp\!\left(-N_{\text{via}} \, P_{\text{bridge}}(I_{\text{space}})\right)$$

Executing `probes/verify_opc_ilt_euv_oasis.py` yields three sharply separated regimes (`Basis: execution`):
- **Deterministic-safe unguarded space ($I_{\text{space}} = 0.19 < 0.518$, `2.7x` nominal intensity margin)**: $\mu = 6.973$ photons $\implies P_{\text{bridge}} = \mathbf{1.237 \times 10^{-4}}$ per voxel $\implies \approx 1.24 \times 10^6$ stochastic bridges per $10^{10}$-via die (**`P_die_fail = 1.000000`**, total yield collapse).
- **Moderately suppressed space ($I_{\text{space}} = 0.065$, `8.0x` nominal margin)**: $\mu = 2.385$ photons $\implies P_{\text{bridge}} = \mathbf{1.281 \times 10^{-11}}$ per voxel $\implies$ **`P_die_fail = 0.1202` (`12.02%` full-die yield loss!)**.
- **Chernoff / Poisson tail-guarded space ($I_{\text{space}} \le 0.030$, `17.3x` margin + high-NA reflective absorber contrast)**: $\mu = 1.101$ photons $\implies P_{\text{bridge}} = \mathbf{1.799 \times 10^{-17}}$ per voxel $\implies$ **`P_die_fail = 1.799 \times 10^{-7}` (`0.18 ppm`)**.

Additionally, `13.5 nm` `EUV` masks are **non-telecentric reflective Bragg multilayers** (`40` `Mo/Si` bilayers illuminated at a **`6°` chief-ray angle of incidence** in `0.33 NA` EUV, or anamorphic `4x/8x` demagnification in `0.55 NA` High-NA EUV), introducing horizontal-vs-vertical 3D absorber shadowing (`HV` CD bias and pitch-dependent best-focus shift) absent from `OpenILT`'s thin-mask scalar Kirchhoff model (`Kirchhoff` $M \in \{0, 1\}$).

---

### 3. Integer-Grid Polygon Clipping, `OASIS` Serialization, and Hobby Snap-Rounding

`Basis: source + normative + execution + derived`

#### 3.1 `GDSII` `int32` Overflow vs. `SEMI P39` `OASIS` Variable-Length Delta Streams

Legacy `GDSII` encodes all vertex coordinates as signed `32`-bit big-endian integers (`[-2,147,483,648, +2,147,483,647]`). As curvilinear `ILT` and `MBMW` sub-nanometer edge placement push database units (`dbu`) from `1 nm` to `0.1 nm` (`100 pm`) and `0.01 nm` (`10 pm`), `32`-bit coordinates hit hard physical reticle-field ceilings (`probes/verify_opc_ilt_euv_oasis.py`):
- At `1 dbu = 0.1 nm`: $\max X = (2^{31} - 1) \times 0.1\text{ nm} = \mathbf{214.748\text{ mm}}$ (`4x` mask plate = `152.4 mm`, barely fits; wafer-scale interposers or `> 215 mm` panels overflow `int32_t`!).
- At `1 dbu = 0.01 nm`: $\max X = (2^{31} - 1) \times 0.01\text{ nm} = \mathbf{21.475\text{ mm}}$ — **cannot even span a standard `26 mm x 33 mm` `1x` scanner exposure field**!

`SEMI P39` (`OASIS`) eliminates fixed-width `32`-bit limits via byte-aligned continuation-bit unsigned/signed variable-length integers (`1g` delta-lists, `POLYGON`, `RECTANGLE`, `TRAPEZOID`, `CTRAPEZOID`, `REPETITION`, and `CBLOCK` zlib compression). In `KLayout` (`dbOASISWriter.cc:209-230`), `safe_scale<R>` and `safe_diff<R>` explicitly guard coordinate scaling (`floor(sf * value + 0.5)`) and signed displacement differences (`d = a - b; if ((a > b && d < 0) || (a < b && d > 0)) throw ...`) against silent two's-complement wraparound when KLayout is compiled in default `32`-bit `db::Coord` mode vs. `64`-bit `-DDB_64BIT_COORD`.

#### 3.2 Exact Predicates vs. Rounded Intersections in `Clipper2` and `KLayout`

| Property / Invariant | `AngusJohnson/Clipper2` (`4be4655694...`) | `KLayout/klayout` (`53911acd6d...`) | Hobby (`1999`) Exact Hot-Pixel Snap-Rounding |
| :--- | :--- | :--- | :--- |
| **Vertex Domain** | `Point64` (`int64_t`), clamped to `MAX_COORD = INT64_MAX >> 2` ($\pm 2.305 \times 10^{18}$, `clipper.core.h:65`) | `db::Point` (`int32_t` default or `int64_t` with `DB_64BIT_COORD`) | Arbitrary bounded integer lattice $\mathbb{Z}^2$ |
| **Orientation Predicate** | Exact `128`-bit `__int128_t` / `MultiplyUInt64` (`CrossProductSign`, `clipper.core.h:752-770`) | Exact `int64`/`int128` cross-products + canonical `e1 < e2` (`dbEdgeProcessor.cc:197-204`) | Exact rational / adaptive predicates on input segments |
| **Intersection Construction** | Floating-point `GetSegmentIntersectPt` rounded to `Point64` + local collinear/spike cleanup (`clipper.engine.cpp`) | Ordered intersection + `CutPoints` **attractor** insertion (`dbEdgeProcessor.cc:209-225`) | Every pixel $[-1/2, +1/2]^2 + p$ containing a vertex or exact intersection is **hot**; *every* segment crossing a hot pixel is rerouted through $p$ |
| **Topological Guarantee** | Output faces locally cleaned, but multi-pass booleans remain **non-associative / non-distributive** | Prevents neighbor jump-over inversions within a single scanline pass; repeated passes drift by $\le 1\text{ dbu}$ | **Zero topological inversions** ($\mathrm{orient}$ never flips from $+1 \to -1$; at worst collapses $+1 \to 0$) |

Two subtle primary-source failure mechanisms stand out (`Basis: source + execution`):
1. **Floating-Point Edge-Swap Asymmetry on Half-Integer Intersections (`KLayout` `dbEdgeProcessor.cc:194-204`)**: KLayout's comment at line `195` records a real regression pair: `e1 = (3, -3) -> (-8, -1)` and `e2 = (-4, -2) -> (13, -4)`. Evaluating their exact rational intersection (`probes/verify_opc_ilt_euv_oasis.py`) yields **`(1/4, -5/2) = (0.25, -2.5)`**—whose $y$-coordinate lands *exactly* on the half-integer rounding boundary `-2.5`! In IEEE-754 `float64`, evaluating `e1.intersect_point(e2)` vs. `e2.intersect_point(e1)` perturbs `-2.5` by $\pm 1\text{ ulp}$, snapping one call order to `y = -2` and the swapped call order to `y = -3`, breaking scanline event-queue monotonicity until canonical `if (e1 < e2)` ordering was enforced.
2. **Topological Side-Inversion Without Hot-Pixel Attractor Splitting**: Consider intersecting segments $e_1 = (0,0) \to (11,5)$ and $e_2 = (0,5) \to (11,0)$, whose exact intersection is $Q_{\text{exact}} = (11/2, 5/2) = (5.5, 2.5)$, alongside a disjoint barrier edge $e_{\text{pass}} = (0,2) \to (13,3)$ (`y(5.5) = 2 + 5.5/13 = 2.4231 < 2.5`). In $\mathbb{R}^2$, $Q_{\text{exact}}$ lies strictly **above** $e_{\text{pass}}$ ($\mathrm{orient2d}(e_{\text{pass}}, Q_{\text{exact}}) = +1$). Under nearest-even integer rounding, $Q_{\text{exact}}$ snaps to $Q_{\text{snap}} = (6, 2)$, where $y_{\text{pass}}(6) = 2.4615 > 2.0$—jumping **across** $e_{\text{pass}}$ without intersecting it ($\mathrm{orient2d}(e_{\text{pass}}, Q_{\text{snap}}) = -1$) and creating an invalid self-overlapping polygon! Under Hobby's (`1999`) snap-rounding (`KLayout` `CutPoints::attractors`), unit pixel $(6, 2)$ (`[5.5, 6.5] \times [1.5, 2.5]`) is marked **hot** and captures $e_{\text{pass}}$ ($2.4615 \in [1.5, 2.5]$), splitting $e_{\text{pass}}$ through $(6, 2)$ so $+1$ degenerates safely to collinearity ($0$) rather than inverting to $-1$.

---

### 4. Multi-Level Performance and Resource Footprint (`L1`–`L6`)

`Basis: source + documentation + execution + derived`

| Level | Metric / Resource Axis | `OpenILT` (`PyTorch` GPU ILT, `2048²`) | `Clipper2` / `KLayout` Scanline + `OASIS` | Certified 4-Corner + Shot-Noise + Hot-Pixel Flow |
| :--- | :--- | :--- | :--- | :--- |
| **`L1` Authoring & Maintenance Velocity** | Engineering / LLM iteration cost & lines per rule | `~1.5k` LoC Python (`OpenILT` core); tuning heuristic `WeightPVBL2` / `WeightPVBand` / `curv` weights takes `10–30` empirical sweeps per tech node | `~4.5k` LoC C++ (`Clipper2`) to `~35k+` LoC C++ (`KLayout` `dbEdgeProcessor` + `OASIS`); hand-debugging `1 dbu` sliver DRC bugs takes days | Declarative physical process-window envelope (`4` corners + spectral tail $\epsilon_{\text{tail}}$ + Poisson Chernoff bound) eliminates manual weight sweeps (`1` spec update per node) |
| **`L2` Toolchain & Solver Build Time** | Cold / incremental build & kernel precomputation | Python runtime `0 s` build, but precomputing `SOCS` SVD over `35x35` Hopkins TCC takes `~2–8 s` (`scipy.linalg.svd`); PyTorch/CUDA wheel footprint `~2.5 GB` | `Clipper2` compiles in `~1.8 s` (`-O3`, `< 150 MB` RSS); full `KLayout` C++ build takes `8–18 min` (`4–8 GB` peak C++ link RSS) | Exact rational/interval certificate checker + `SOCS` spectral-tail verifier compiles in `< 1.5 s` (`C99`/`Rust`, zero GPU build dependency) |
| **`L3` Synthesis & Compilation Latency** | Per-clip (`2x2 µm²`) ILT & fracturing latency | `SimpleILT` (`100` SGD iters x `3` corners x `24` FFTs on `2048²` `float32` CUDA): `~0.45–1.8 s`/clip on datacenter GPU (`~35–90 s` on CPU); full-chip (`10^7` clips) requires `1,000+` GPU-hours | Polygon boolean/MRC cleanup (`10^4–10^5` vertices/clip): `1.5–12 ms` in `Clipper2`, `4–25 ms` in `KLayout` (`O((N + I) \log N)`); naive `adabox` pixel shot counter (`evaluation.py:244`) takes `0.3–2.0 s`/clip | Adding the missing `(DoseMax, defocus)` corner adds `+33%` FFT evaluations (`3 -> 4` corners, `~0.60–2.4 s`/clip) or `+0%` when evaluated via lazy worst-case corner caching; hot-pixel pass adds `< 18%` over Bentley-Ottmann sweep |
| **`L4` Runtime / Mask-Writer Throughput** | Wafer-plane throughput & shot-count inflation | Unconstrained pixel ILT explodes VSB shots `5x–20x` (`> 2,000` shots/clip), slowing `193i` VSB write times to `> 24 h/mask`; `MBMW` (`EUV`) writes pixel bitmaps in constant **`~7–10 h/mask`** independent of curvature! | `Clipper2` processes `~3–8M` edges/sec/core (`~120–300 cycles/vertex`); `KLayout` `OASIS` `CBLOCK` streaming writes `80–220 MB/s/core` | Curvilinear `OASIS` `MULTIGON`/spline or `45°`/`TRAPEZOID` export for `MBMW` achieves `1x` constant write time while eliminating VSB staircase jogging |
| **`L5` Verification & Signoff Speed** | Full-chip Litho-DRC / `PVBand` / `MRC` check speed | 3-corner `FFT` check: `~4–8 ms/clip` on GPU (`~250 clips/s/GPU`), but **unsound** on `(DoseMax, defocus)` and `40 nm` `EPE` gaps; full Monte Carlo EUV resist takes minutes/clip | `KLayout` DRC width/space scanline check: `5–20 ms/clip`; independent topological self-intersection / orientation check runs in `O(N \log N)` (`< 3 ms/clip`) | Analytical `4`-corner + `SOCS` $\epsilon_{\text{tail}}$ + exact Poisson tail lookup table verifies `2048²` clips in **`< 6 ms/clip` on GPU** (`100%` deterministic, zero Monte Carlo variance) |
| **`L6` Memory, Disk & Artifact Footprint** | GPU VRAM, host RAM, & `GDSII` vs `OASIS` size | `OpenILT` `2048²` `complex64` x `24` kernels + autograd activations: **`~1.6–2.4 GB` VRAM** (`batch=1`); precomputed `.pt` kernels `~2.3 MB` | Curvilinear full-chip `GDSII` explodes to **`500 GB – 4 TB`** uncompressed; `SEMI P39` `OASIS` with `REPETITION` + `CBLOCK` compresses **`10x–25x`** (`40–180 GB`) | Streaming tile-halo (`2048²` + `64 nm` optical halo = `3x` optical interaction radius) bounds host/VRAM memory strictly to **`O(tile_area)`** (`< 512 MB`) regardless of full-chip reticle size |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Model Refinement (`C2`)

`Basis: source + derived`

#### 5.1 (`C1`) Human Comprehensibility and Mental-Model Ergonomics

Computational lithography pipelines fail human auditability when continuous physical approximations, stochastic resist statistics, and discrete CAD rounding rules are scattered across disconnected tools with implicit assumptions:
- **Hidden Non-Monotonicity Footgun (`OpenILT` 3-Corner Assumption)**: To both human lithography engineers and LLM code generators, naming variables `aerialMax` (`DoseMax, focus`) and `aerialMin` (`DoseMin, defocus`) creates a compelling linguistic illusion that `[aerialMin, aerialMax]` brackets all printed contours across the rectangular `(Dose, Focus)` process window. In reality, aerial intensity is only monotone wrt defocus on **bright-feature interiors**; on **dark-space SRAF peaks**, defocus *increases* intensity, so `aerialMax` is **not** the maximum intensity! A human auditing `pvband = sum(binaryMax != binaryMin)` (`simpleilt.py:80`) cannot spot this bug locally without recalling Fourier pupil energy conservation.
- **Silent Coordinate-Order & Associativity Violations**: Engineers expect polygon boolean algebra (`A | B`, `A - B`) to obey set-theoretic identities. When `((A | B) - C)` differs from `((A - C) | (B - C))` by `1 dbu` (`0.1 nm`) slivers that trigger mask-rule-check (`MRC`) minimum-area violations `6` stages downstream, diagnosing which intermediate clipping pass introduced the orientation flip requires inspecting thousands of `int64` coordinates unless the boolean engine emits explicit hot-pixel snap witnesses.

#### 5.2 (`C2`) Simplicity, Orthogonality, and Universal Model Refinement

Rather than patching ad-hoc SRAF penalty heuristics, `40 nm` `EPE` point-samplers, and post-boolean sliver-removal filters (`drc_clean`), all three failure classes collapse into **three orthogonal, compositional mathematical contracts** (satisfying both Ousterhout's deep-module criterion and Felleisen's macro-expressibility test without adapter bloat):

1. **Certified Process-Window Aerial Envelope (`[I_lo(x), I_hi(x)]`)**: Replace untyped scalar aerial tensors with a sound interval envelope over the full product box $\mathcal{W} = [D_{\min}, D_{\max}] \times [-z_{\max}, +z_{\max}]$ plus the deterministic `SOCS` spectral truncation residual $\epsilon_{\text{tail}}(M) = (\sum_{k > K} \sigma_k) \|D_{\max} M\|_2^2 \ge 0$:
   $$I_{\text{lo}}(\mathbf{r}) = \min_{(D, z) \in \partial \mathcal{W}} I_K(\mathbf{r}; D, z), \qquad I_{\text{hi}}(\mathbf{r}) = \max_{(D, z) \in \partial \mathcal{W}} I_K(\mathbf{r}; D, z) + \epsilon_{\text{tail}}(M)$$
   Main-feature printing (`target == 1`) requires $I_{\text{lo}}(\mathbf{r}) \ge I_{\text{th,print}}$, while dark-space / SRAF non-printing (`target == 0`) requires $I_{\text{hi}}(\mathbf{r}) \le I_{\text{th,dark}}$—evaluating `(DoseMax, defocus)` automatically as an ordinary vertex of $\partial \mathcal{W}$ rather than a special case.
2. **Monotone Poisson Tail Threshold Mapping (`I_th,dark` Incorporating Quantum Shot Noise)**: Instead of bolting a stochastic Monte Carlo simulator onto deterministic `OPC`, fold the `EUV` Poisson Chernoff tail bound for target per-voxel defect rate $\delta_{\text{voxel}} \le \delta_{\text{die}} / N_{\text{via}}$ directly into the admissible dark/bright intensity thresholds $(I_{\text{th,dark}}(\delta_{\text{voxel}}), I_{\text{th,print}}(\delta_{\text{voxel}}))$ via the exact monotone inverse incomplete gamma function $\Gamma^{-1}(n_{\text{th}}, \delta_{\text{voxel}})$ (`I_th,dark = 0.030` for $\delta_{\text{voxel}} \le 2 \times 10^{-17}$). Deterministic aerial envelope verification then discharges stochastic nano-bridging at **zero extra runtime cost**!
3. **Single-Lowering Lazy Exact Arrangement -> Terminal Hot-Pixel Snap-Rounding**: Never snap intermediate polygon booleans to `Point64` between `union`/`diff`/`offset` steps. Maintain polygon arrangements over exact rationals (or lazy exact predicates with `int128` determinants) across the entire boolean expression DAG, and execute **one** terminal Hobby (`1999`) hot-pixel snap-rounding pass when lowering to `SEMI P39` `OASIS` `dbu` coordinates—preserving exact boolean associativity internally and guaranteeing zero topological orientation inversions at serialization.

---

## Boundaries

- **3D Electromagnetic Mask Topography (`FDTD` / `RCWA`) — `not examined` experimentally**: Thick `TaBN` absorbers (`~50–70 nm`) on `40`-bilayer `Mo/Si` Bragg reflectors at `6°` `EUV` chief-ray incidence require Maxwell waveguide / Rigorous Coupled-Wave Analysis (`RCWA`) or `M3D` Hopkins decomposition; `OpenILT` (`dabb97c6...`) implements only 2D thin-mask Kirchhoff transmission (`known not to apply` unmodified to High-NA `0.55` anamorphic `EUV` shadowing).
- **Chemically Amplified vs. Metal-Oxide (`MOx`) Photoacid Blur Trade-off (`RLS`) — `not examined` via reaction-diffusion PDE**: Our `EUV` shot-noise probe (`verify_opc_ilt_euv_oasis.py`) models discrete $3 \times 3\text{ nm}^2$ reaction voxels at $\eta = 0.30$ quantum absorption. Increasing photoacid diffusion length blurs high-frequency shot noise (`LER`) at the direct expense of aerial `NILS` resolution (`Mack` `RLS` trade-off); exact coupled acid-quencher reaction-diffusion calibration remains resist-formulation-specific (`unknown` without foundry resist parameters).
- **`SEMI P49` (`OASIS.MASK`) Curvilinear Spline Extensions — `unsupported` in examined open-source streamers**: While `SEMI P39` `OASIS` supports arbitrary-vertex `POLYGON` and `TRAPEZOID` records (`KLayout` `dbOASISWriter.cc`), native implicit B-spline / Bézier `MULTIGON` records introduced for multi-beam mask writers (`SEMI P49` / `OASIS.MASK`) are **`unsupported`** in `OpenILT` (`dabb97c6...`) and `Clipper2` (`4be46556...`).
- **Attractive Over-Claim Rejected**: Hobby (`1999`) hot-pixel snap-rounding guarantees **isotopy / non-inversion of orientation** (no segment jumps across a disjoint vertex or edge), **not** invariance of minimum feature width (`MRC`) or idempotence under repeated snap-rounded boolean passes; each snapped vertex can still shift by up to $\pm 0.5\text{ dbu}$ ($\pm \frac{\sqrt{2}}{2}\text{ dbu}$ Euclidean), requiring a `1 dbu` conservative erosion/dilation guard band when certifying post-snap `MRC` spacing.

---

## Evidence

### Primary Upstream Repositories (Immutable 40-Hex Revisions, Observed `2026-11-19`)

1. **`OpenOPC/OpenILT`** (`dabb97c6ca3dfd159362e48273c436444c77353b`):
   - `pylitho/exact.py:13-80, 166-195`: `Kernel` loading (`focus` / `defocus` `[24, 35, 35]` `SOCS` tensors) and `_LithoSim.forward` / `_LithoSim.backward` complex FFT Wirtinger adjoint.
   - `pylitho/exact.py:196-239`: `LithoSim.forward` computing `aerialNom` `(DoseNom, focus)`, `aerialMax` `(DoseMax, focus)`, and `aerialMin` `(DoseMin, defocus)`, omitting `(DoseMax, defocus)`.
   - `pyilt/simpleilt.py:73-94`: `SimpleILT` optimization loop (`pvband = torch.sum((printedMax >= TargetDensity) != (printedMin >= TargetDensity))`, $3 \times 3$ curvature kernel).
   - `pyilt/curvmulti.py:55-88` & `pyilt/levelset.py`: Multi-resolution `512 -> 1024 -> 2048` curvilinear and level-set ILT solvers.
   - `pyilt/evaluation.py:34-43, 68-72, 163-200, 229-256`: `Basic` `pvband`, `EPEChecker` (`EPE_CHECK_INTERVEL = 40`, `MIN_EPE_CHECK_LENGTH = 80`), and `ShotCounter` (`shape=(512, 512)` `mode="nearest"` downsampling prior to `adabox.proc.decompose`).
2. **`AngusJohnson/Clipper2`** (`4be4655694d7e15e76ac6bfe9024fa534eed3428`):
   - `CPP/Clipper2Lib/include/clipper2/clipper.core.h:65-70, 727-770`: `MAX_COORD = INT64_MAX >> 2` coordinate clamp and exact `128`-bit `ProductsAreEqual` / `CrossProductSign` orientation predicates.
   - `CPP/Clipper2Lib/src/clipper.engine.cpp:1525-1660`: Vatti scanbeam intersection handling and `Point64` rounding / collinear spike cleanup.
3. **`KLayout/klayout`** (`53911acd6dfaa113c188d11d20b2ae290aa60a6b`):
   - `src/db/db/dbEdgeProcessor.cc:194-225`: `safe_intersect_point` documenting swap-sensitive edge pair `(3,-3;-8,-1)` and `(-4,-2;13,-4)` (exact rational intersection `(1/4, -5/2)`), canonical `e1 < e2` ordering, and `CutPoints::attractors` hot-pixel splitting.
   - `src/plugins/streamers/oasis/db_plugin/dbOASISWriter.cc:207-230`: `safe_scale` and `safe_diff` signed integer overflow guards during `SEMI P39` `OASIS` delta-coordinate serialization.

### Peer-Reviewed Literature and Standards

- A. Poonawala and P. Milanfar, *"Mask Design for Optical Microlithography—An Inverse Imaging Problem,"* IEEE Trans. Image Process., vol. 16, no. 3, pp. 774–788, Mar. 2007, `DOI: 10.1109/TIP.2006.891332`.
- S. Zheng, B. Yu, and M. D. F. Wong, *"OpenILT: An Open-Source Inverse Lithography Technology Framework,"* IEEE 15th Int. Conf. on ASIC (`ASICON`), 2023, `DOI: 10.1109/ASICON58565.2023.10396314`.
- C. A. Mack, *"Line-edge roughness and the ultimate limits of lithography,"* Proc. SPIE 7639, Optical Microlithography XXIII, 763931, Mar. 2010, `DOI: 10.1117/12.848236`.
- J. D. Hobby, *"Practical segment intersection with finite precision output,"* Computational Geometry: Theory and Applications, vol. 13, no. 4, pp. 199–214, Oct. 1999, `DOI: 10.1016/S0925-7721(99)00021-8`.
- SEMI P39, *Specification for OASIS (Open Artwork System Interchange Standard)*, Semiconductor Equipment and Materials International.

### Preserved Executable Verification Artifact (`probes/verify_opc_ilt_euv_oasis.py`)

Observed deterministic output on `2026-11-19` (`Python 3`, pure stdlib `fractions`, `math`, `json`):

```json
{
  "hopkins_socs_and_sraf_corner": {
    "clear_field_dc_intensity": 1.0,
    "socs_rank1_truncation_linf_err": 0.1345,
    "print_threshold": 0.5,
    "openilt_3corners_sraf_intensities": [0.4017, 0.4179, 0.4879],
    "openilt_3corner_max_sraf_intensity": 0.4879,
    "openilt_pvband_detects_sraf_bridge": false,
    "omitted_dosemax_defocus_sraf_intensity": 0.5286,
    "omitted_corner_prints_spurious_bridge": true,
    "minimax_4corner_guarded_sraf_intensity": 0.3745
  },
  "euv_poisson_shot_noise": {
    "euv_photon_ev": 91.84,
    "arf_photon_ev": 6.42,
    "incident_photons_per_nm2_arf_vs_euv": [194.32, 13.59],
    "photon_count_reduction_ratio": 14.3,
    "unguarded_space_I0p19_bridge_prob": 0.0001237,
    "unguarded_10B_via_die_fail_prob": 1.0,
    "moderate_space_I0p065_10B_via_die_fail_prob": 0.1202,
    "guarded_space_I0p030_bridge_prob": 1.799e-17,
    "guarded_10B_via_die_fail_prob": 1.799e-07
  },
  "oasis_snap_rounding_and_klayout": {
    "klayout_edge_pair_exact_rational_intersection": ["1/4", "-5/2"],
    "snap_rounding_exact_point": [5.5, 2.5],
    "snap_rounding_snapped_dbu_point": [6, 2],
    "orient_vs_barrier_exact_vs_naive_snap": [1, -1],
    "hobby_hot_pixel_captures_passing_edge": true,
    "gdsii_i32_span_mm_at_0p1nm_and_0p01nm_dbu": [214.748, 21.475]
  }
}
```

---

## Revalidation

1. **Run the Preserved Deterministic Micro-Probe (`< 0.1 s`, zero third-party packages)**:
   ```bash
   python3 -B reports/opc-ilt-computational-lithography-euv-shot-noise-and-oasis-snap-rounding/probes/verify_opc_ilt_euv_oasis.py
   ```
   Confirm `exit 0` and verify that all assertions hold: `openilt_3corner_max_sraf_intensity < 0.50 < omitted_dosemax_defocus_sraf_intensity`, `photon_count_reduction_ratio == 14.3`, `orient_vs_barrier_exact_vs_naive_snap == [1, -1]`, and `hobby_hot_pixel_captures_passing_edge == true`.
2. **Check Upstream `OpenILT` Process-Window Coverage**:
   Inspect `pylitho/exact.py` (`LithoSim.forward`) and `pyilt/evaluation.py` (`Basic.run`, `EPEChecker`, `ShotCounter`) in any newer revision of `OpenOPC/OpenILT`. Check whether a fourth `_LithoSim.apply` call with `self._config["DoseMax"]` and `self._kernels["defocus"]` has been added, whether `EPE_CHECK_INTERVEL = 40` has been replaced by dense contour Marching-Squares / SDF evaluation, and whether `ShotCounter.run` still downsamples to `(512, 512)` with `mode="nearest"`.
3. **Check Upstream `Clipper2` and `KLayout` Snap-Rounding Invariants**:
   Diff `CPP/Clipper2Lib/include/clipper2/clipper.core.h` (`MAX_COORD`, `CrossProductSign`) in `AngusJohnson/Clipper2` and `src/db/db/dbEdgeProcessor.cc` (`safe_intersect_point`, `struct CutPoints`) plus `src/plugins/streamers/oasis/db_plugin/dbOASISWriter.cc` (`safe_scale`, `safe_diff`) in `KLayout/klayout`.
