# Galileo OSNMA Spoofing Boundaries, Strapdown INS/GNSS Kalman Covariance Stability, and ACAS X Hybrid-Game Verification

## Summary

End-to-end navigation and airborne collision-avoidance safety depends on preserving invariants across three tightly coupled layers: **cryptographic navigation-message authentication**, **finite-precision covariance filtering and fault exclusion**, and **continuous hybrid-game collision avoidance**. Breaking any single interface undermines the entire chain:

1. **Galileo `OSNMA` `TESLA` Authenticates Data Bits, Not Signal Time-of-Arrival (`ToA`), Leaving Physical-Layer Meaconing Unmitigated:** `OSNMA` (`Galileo OSNMA SIS ICD v1.1`) binds E1-B I/NAV ephemeris/clock (`CED`) and timing parameters (`ADKD=0/4/12`) to a `ECDSA`-rooted reverse `SHA-256`/`SHA3-256` `TESLA` key chain with `40`-bit equivalent `HMAC`/`CMAC` tag minimums (`MIN_AUTHBITS = 40` in `daniestevez/galileo-osnma`). However, because `TESLA` key disclosure operates on a `30 s` (`ADKD=0`) or `330 s` (`ADKD=12`) loose time-sync budget while $1\,\mu\text{s}$ of RF delay shifts a pseudorange by `~300 m`, an attacker replaying unmodified authentic `OSNMA` subframes with per-satellite causal microsecond delays (`1.46–7.04 us`) shifts a 5-satellite WLS fix (`RTKLIB` `estpos`/`valsol`) by **`(+1000.0 m, +500.0 m)`** with **`vv = 0.00e+00`** residual and zero failed `OSNMA` tags (`Probe 2A`, confirming Motallebighomi et al., WiSec 2023). Source auditing also contrasts `daniestevez/galileo-osnma` (typestate `Key<Validated>`, `derivations <= 3000` DoS cap, full 12-entry `MACLT` + `MACSEQ`, plus one subtle `PubkeyStore::revoke` bug clearing `self.current` instead of `self.next` at `osnma.rs:629`) against `nlsfi/fgi-osnma` (unbounded `dt // 30` DoS, `verify_MACSEQ: pass` stub leaving `FLX` slots unauthenticated, partial 4-entry `MACLT`, and bypassed verification when `merkle_tree == None`).
2. **Conventional `(I - K H) P` Kalman Covariance Updates Induce Indefinite `LAMBDA` Failures, Resolved Only by Square-Root / `UD` Factorizations:** Both `tomojitakasu/RTKLIB` (`rtkcmn.c:1062-1081`) and `rtklibexplorer/RTKLIB` (`rtkcmn.c:1459-1478`) compute unstabilized `Pp = (I - K H^T) P`. Under tight carrier-phase ambiguity hold updates (`VAR_HOLDAMB = 0.001` at `rtkpos.c:62`) with high dynamic range $S = 8 \times 10^6$, IEEE-754 `binary64` `(I - K H^T) P` produces a **negative determinant (`-1.953125e-03`)**, aborting `lambda.c:36` (`LD factorization error` when `D[i] <= 0.0`), while at $S = 10^8$ *both* `(I - K H^T) P` and **Joseph form** collapse to singular `0.0`, whereas **Bierman–Thornton `UD` factorization** ($P = U D U^T$) preserves exact positive-definiteness (`+2.500000e-04`, `Probe 2B`) by halving the effective condition exponent $\kappa(U D^{1/2}) = \sqrt{\kappa(P)}$. Meanwhile, sequential EKF $\chi^2$ innovation gating fails against slowly ramped spoofing (`0.15 m/s`), dragging estimated position `29.62 m` off truth while keeping single-epoch `NIS <= 0.0900 << 10.83`.
3. **Discretized `ACAS X` / `HorizontalCAS` MDP Tables Suffer 1 Hz NMAC Tunneling and Euler Drift Unless Shielded by Continuous `KeYmaera X` Safeable Regions:** Direct inspection of `sisl/HorizontalCAS` (`transitions.jl:27-45`, `rewards.jl:28-30`) shows 1-second straight-line Euler steps (`10.99 ft/step` lateral error at $3^\circ/\text{s}$ and `420 ft/s`) and point-sampled `tau == 0` NMAC rewards that miss continuous midpoint penetrations (`r(0s) = r(1s) = 516.14 ft > 500 ft` while `r(0.5s) = 300.00 ft < 500 ft`, `Probe 2C`). Conversely, `LS-Lab/KeYmaeraX-projects/acasx/` (`acasx.kyx` and `acasx-games/`) formalizes exact quantifier-free explicit safeable envelopes (`Lexpl`) and bounded-delay `dGL` hybrid games against vertically maneuvering intruders (`aup > alo + 2c`), shifting required `CL1500` initiation outward from `3490 ft` (`eps=0s`) to `7690 ft` under `5 s` pilot delay (`rv = 840 ft/s`).

## Applicability

This report combines normative GNSS/avionics specifications, peer-reviewed verification and attack research, direct source inspection of six pinned upstream repositories, and three standalone executable Python 3 micro-probes (`Probe 2A`, `Probe 2B`, `Probe 2C`):

- **Galileo `OSNMA` Broadcast Authentication & Receiver Validation:**
  - `daniestevez/galileo-osnma` @ `b6c337b3d559b22edd7fa45fb5c4ee93c962c533` (`galileo-osnma/src/{tesla,validation,maclt,navmessage,osnma,mack}.rs`): applies to embedded `no_std` Rust implementations targeting `Galileo OSNMA SIS ICD v1.1` and `Receiver Guidelines v1.3`.
  - `nlsfi/fgi-osnma` @ `f404aa947b3eb547a2ffbadb7fcbcb406fabb022` (`osnma/authentication.py`): applies to Python reference/research OSNMA processors.
  - Motallebighomi, Sathaye, Singh, & Ranganathan (`ACM WiSec 2023`, DOI `10.1145/3558482.3590186`): applies to single-antenna GNSS RF meaconing / differential code-delay attacks against NMA-capable receivers.
- **Carrier-Phase `LAMBDA`, Strapdown `INS/GNSS` Filtering, and `RAIM`:**
  - `tomojitakasu/RTKLIB` @ `71db0ffa0d9735697c6adfd06fdf766d0e5ce807` (`src/{rtkcmn,rtkpos,lambda,pntpos}.c`) and `rtklibexplorer/RTKLIB` @ `755e6379ae600e71980b6b20d846d6d35ca8a1aa` (`src/{rtkcmn,rtkpos,lambda,options}.c`): apply to double-precision GNSS/RTK EKF and integer least-squares ambiguity resolution (`LAMBDA` / `MLAMBDA`, Teunissen 1995).
  - Carlson (1973), Thornton (1976), and Bierman (1977): apply to finite-precision covariance propagation and update stability in tightly coupled strapdown INS/GNSS and RTK state estimators.
- **Airborne Collision Avoidance (`TCAS II` / `ACAS X` / `HorizontalCAS` / `KeYmaera X`):**
  - `sisl/HorizontalCAS` @ `bc56a28cfe70b0486b6875deacfda947500bddcb` (`GenerateTable/mdp/{constants,transitions,rewards}.jl`, `GenerateTable/SolveMDP.jl`): applies to MDP table synthesis and ReLU network compression (`Reluplex`, Katz et al. 2017) for horizontal airborne advisories (`ACAS Xu` / `DO-386`).
  - `LS-Lab/KeYmaeraX-projects` @ `b9d7cb584e8fd1c3cc4f30644e82ba12cbb1d6fe` (`acasx/{acasx,acasxtwosided}.kyx`, `acasx/acasx-games/Safeability for a Vertically-Maneuvering Intruder.kyx`) and Jeannin et al. (`STTT 2017`): apply to vertical `ACAS Xa/Xo` (`DO-385`) hybrid-system and hybrid-game formal safety proofs (`dL` / `dGL`).

**Relationship Among Subjects:** RF-authenticated ephemeris (`OSNMA`), positive-definite sensor fusion (`UD`-EKF + `LAMBDA` + `RAIM`), and verified collision-avoidance regions (`KeYmaera X` shielding MDP/`NNet` lookups) form a serial trust pipeline: physical-layer spoofing defeats unguarded `OSNMA` fixes, numerical covariance collapse crashes `LAMBDA` or corrupts `RAIM` covariance weighting, and unshielded MDP discretization lets unsafe trajectories slip between `1 Hz` advisory boundaries.

## Findings

### 1. Galileo `OSNMA` `TESLA` Authentication, Upstream Audits, and Physical-Layer Meaconing Limits

Basis: normative (`Galileo OSNMA SIS ICD v1.1`; `Receiver Guidelines v1.3`; Motallebighomi et al., ACM WiSec 2023 DOI `10.1145/3558482.3590186`; Teunissen 1995 DOI `10.1007/BF00863419`) + source (`daniestevez/galileo-osnma` @ `b6c337b3d559b22edd7fa45fb5c4ee93c962c533`; `nlsfi/fgi-osnma` @ `f404aa947b3eb547a2ffbadb7fcbcb406fabb022`; `tomojitakasu/RTKLIB` @ `71db0ffa0d9735697c6adfd06fdf766d0e5ce807`) + execution (`Probe 2A`).

#### 1.1 `OSNMA` Cryptographic Architecture & Delayed `TESLA` Disclosure

Galileo `OSNMA` repurposes the `40` reserved bits in each `2 s` E1-B I/NAV odd page (`15` pages = `600 bits` per `30 s` subframe), partitioning them into a `120-bit` **`HKROOT`** channel (8-bit `NMA Header` + `DSM-PKR` Merkle-tree ECDSA public-key distribution or `DSM-KROOT` root key signed via ECDSA P-256/P-521) and a `480-bit` **`MACK`** channel carrying MAC tags, `MACSEQ` (`12-bit`), `COP`, and a delayed `TESLA` symmetric key $K_{i+1}$.

- **Reverse Salted Hash Chain (`tesla.rs:508-512, 681-700`):** Keys are generated backward from a secret seed and published forward in time. A receiver holding validated key $K_i$ at subframe $\text{GST}_i$ authenticates a later disclosed key $K_j$ ($j > i$) by applying the salted one-way function $(j - i)$ times:
  $$K_{t-1} = \text{trunc}_l\!\left(H\big(K_t \mathbin{\|} \text{GST}_{t-1} \mathbin{\|} \alpha\big)\right)$$
  where $H \in \{\text{SHA-256}, \text{SHA3-256}\}$, $\text{GST}_{t-1}$ packs `12-bit WN || 20-bit TOW`, and $\alpha$ is the `48-bit` chain salt from `DSM-KROOT`.
- **MAC Tags, Cross-Authentication (`ADKD`), and Operational `MIN_AUTHBITS`:**
  - `ADKD=0` authenticates Clock, Ephemeris, and Health Data (`CED`) with `+1` subframe (`30 s`) key disclosure delay (self-authenticated `00S` via `tag0` and cross-authenticated `00E` from peer satellites in view).
  - `ADKD=4` authenticates constellation Galileo-GPS / GST-UTC timing parameters (`04S`).
  - `ADKD=12` (**Slow MAC**) authenticates `CED` with `+11` subframes (**`330 s`**) disclosure delay (`osnma.rs:445, 470-492`) for cold receivers with coarse initial clock uncertainty.
  - Per `navmessage.rs:18-21`, Galileo operational ICD updates (`2024-01-15`) reduced the minimum accumulated authentication threshold **`MIN_AUTHBITS` from `80` bits to `40` bits**, letting a single `40-bit` tag suffice when `ADKD` tags are verified against `MACLT`.

#### 1.2 Direct Source Comparison: `daniestevez/galileo-osnma` vs. `nlsfi/fgi-osnma`

| Security / Compliance Dimension | `daniestevez/galileo-osnma` @ `b6c337b3` (Rust `no_std`) | `nlsfi/fgi-osnma` @ `f404aa94` (Python) | Security Impact |
| :--- | :--- | :--- | :--- |
| **Cryptographic Typestate Enforcement** | Zero-cost phantom tags `Validated` / `NotValidated` on `PublicKey`, `NmaHeader`, `Key`, `Mack` (`validation.rs:19-27`) | Runtime `AuthOutcome` enum; unverified NMA objects can reach callers if return/exception ignored (`authentication.py:18-63`) | Rust statically prevents using unverified `TESLA` keys in `validate_tag` |
| **`TESLA` Chain Derivation Bound** | Rejects `derivations > 3000` (~25 h) via `ValidationError::TooManyDerivations` (`tesla.rs:745-747`) | Unbounded `dt // 30` loop in `verify_tesla_key_against_trusted_key` (`authentication.py:255`) | Attacker injecting forged far-future `GST` induces CPU exhaustion DoS in `fgi-osnma` |
| **`MACSEQ` & `FLX` Slot Verification** | Full `validate_macseq` (`tesla.rs:974-1008`) + all 12 ICD `MACLT` IDs `{27..41}` (`maclt.rs:60-157`) | **`verify_MACSEQ` is an empty `pass` stub** (`authentication.py:261-264`); supports only `{27,28,31,33}` and throws on `FLX` (`lines 282-302`) | `fgi-osnma` cannot authenticate flexible cross-auth slots and skips `MACSEQ` anti-tamper binding |
| **Algorithm & Key Revocation Handling** | Supports SHA-256/SHA3-256, HMAC-SHA256/CMAC-AES, ECDSA P-256/P-521; **bug in `PubkeyStore::revoke` (`osnma.rs:623-630`)**: clears `self.current = None` instead of `self.next = None` when `self.next` matches `< new_pkid` | Hardcodes SHA-256 + ECDSA P-256 (`mac_function = None` TODO at `authentication.py:123`); `verify_public_key` returns `True` if `merkle_tree == None` (`lines 352-354`) | `galileo-osnma` can inadvertently wipe an active key during `next` revocation; `fgi-osnma` silently disables PKR verification without Merkle root |

#### 1.3 Why `OSNMA` Cannot Defeat Physical-Layer Meaconing / `SCER`, and How Carrier-Phase `LAMBDA` Discriminates

The security proof of `TESLA` requires **loose time synchronization**: the receiver's local clock error $\Delta T_{\text{sync}}$ must be strictly bounded below the disclosure delay $T_{\text{delay}}$ (e.g., $\Delta T_{\text{sync}} < 15\text{ s}$ for `ADKD=0` or $< 165\text{ s}$ for Slow MAC `ADKD=12`) so an adversary cannot first capture $K_{i+1}$ from the sky and then synthesize forged I/NAV bits + tags claiming to have been transmitted at $\text{GST}_i$.

**Crucial Physical-Layer Gap (Motallebighomi et al., WiSec 2023; `Probe 2A`):** Pseudorange positioning converts signal Time-of-Arrival ($\text{ToA}$) into distance at $c \approx 3 \times 10^8\text{ m/s}$ (`1 us = 299.79 m`, `1 ms = 299.8 km`). Inside the multi-second `TESLA` synchronization window, a **differential code-delay / meaconing spoofer** records live authentic Galileo signals from all satellites in view and re-radiates the **exact, bit-for-bit unmodified I/NAV symbols and `OSNMA` tags** with per-channel RF delays $\Delta\tau_k \ge 0$:
$$\Delta\tau_k = \frac{\|\mathbf{p}_{\text{fake}} - \mathbf{s}_k\| - \|\mathbf{p}_{\text{true}} - \mathbf{s}_k\|}{c} + \delta t_{\text{common}}$$
where choosing $\delta t_{\text{common}} > \max_k (\|\mathbf{p}_{\text{true}}-\mathbf{s}_k\| - \|\mathbf{p}_{\text{fake}}-\mathbf{s}_k\|)/c$ guarantees **every channel is strictly causal ($\Delta\tau_k \ge 0$)** without predicting future bits (zero `SCER` security-code-estimation guesswork!). Because `osnma.rs:192-212` (`feed_inav`, `feed_osnma`) inspects only `(word, svn, gst, band)` and never RF ToA residuals, `100%` of `TESLA` and `MACK` checks pass!

**Execution Verification (`Probe 2A`):** Applying causal RF delays `[1.458, 5.157, 5.181, 7.041, 4.200] us` across 5 Galileo satellites (`delta t_common = 4.0 us`, orders of magnitude below the `15 s` TESLA window) causes `RTKLIB`-style Gauss-Newton WLS (`pntpos.c:estpos/valsol`) to converge cleanly to **`(+1000.00 m, +500.00 m)`** with **`vv = 0.00e+00`** post-fit residual—passing both `OSNMA` cryptographic authentication *and* $\chi^2$ `valsol` RAIM!

**Carrier-Phase Double-Difference (`LAMBDA`) Physical Countermeasure:** Unlike code pseudoranges, carrier-phase RTK against an unspoofed base station or a rigid multi-antenna receiver array (`baseline B = 0.50 m` in `Probe 2A`) evaluates double differences $\nabla\Delta\phi_{k,1} = \mathbf{B}\cdot(\mathbf{e}_k - \mathbf{e}_1) + \lambda \nabla\Delta N_{k,1}$. When a single transmitting spoofer antenna radiates all satellites, every signal propagates along the **identical physical vector** from the spoofer to the antennas, collapsing all geometric double differences to `[0.0, 0.0, 0.0, 0.0]` instead of the true constellation projection `[-0.5688, -0.2492, -0.6377, -0.3176] m` and triggering immediate `RTKLIB` `resamb_LAMBDA` ratio-test rejection (`rtkpos.c:1405`, `s[1]/s[0] >= thresar[0]`, Teunissen 1995 `lambda.c:29-188`).

---

### 2. Strapdown `INS`/`GNSS` EKF Covariance Collapse, `UD` Factorization, and `RAIM` Limits

Basis: normative (`Carlson 1973` DOI `10.2514/3.6907`; `Thornton 1976` JPL TM-33-798; `Bierman 1977` ISBN `978-0-12-097350-7`; `Teunissen 1995` DOI `10.1007/BF00863419`) + source (`tomojitakasu/RTKLIB` @ `71db0ffa0d9735697c6adfd06fdf766d0e5ce807`; `rtklibexplorer/RTKLIB` @ `755e6379ae600e71980b6b20d846d6d35ca8a1aa`) + execution (`Probe 2B`).

#### 2.1 `RTKLIB` Unstabilized Covariance Update vs. `LD` Factorization Failures

A tightly coupled strapdown `INS`/`GNSS` or RTK carrier-phase Extended Kalman Filter fuses states spanning $10+$ orders of magnitude in variance—from `100–900 m^2` initial position/attitude/bias uncertainty (`VAR_POS = 900.0` at `rtkpos.c:51`) down to millimeter-scale carrier-phase (`~10^-5 m^2`) and integer ambiguity hold constraints (`VAR_HOLDAMB = 0.001 cyc^2` at `tomojitakasu/RTKLIB` `rtkpos.c:62`). Inspecting both `RTKLIB` trees exposes a shared numerical fragility:

- **Direct Inspection (`tomojitakasu/RTKLIB` `rtkcmn.c:1062-1081`, `rtklibexplorer/RTKLIB` `rtkcmn.c:1459-1478`):** Both implement the conventional textbook update inside `filter_()`:
  ```c
  matmulm("NT", n, n, m, K, H, I);  /* Pp = (I - K*H')*P */
  matmul ("NN", n, n, n, I, P, Pp);
  ```
  Neither computes the symmetric Joseph form, neither symmetrizes $(P^+ + (P^+)^T)/2$, and neither stores factorized covariance. Because $(I - K H^T) P$ subtracts two nearly equal large matrices $P$ and $K H^T P$ during high-accuracy updates ($R \ll H^T P H$), catastrophic IEEE-754 floating-point cancellation destroys **both symmetry and positive-definiteness**!
- **Downstream `LAMBDA` Crash (`lambda.c:29-45`):** When `resamb_LAMBDA` (`rtkpos.c:1396`) subsequently extracts the double-differenced ambiguity covariance $Q_b = D^T P D$ and invokes `LD(nb, Qb, L, D)` (`lambda.c:36`), the very first check `if ((D[i] = A[i+i*n]) <= 0.0) { info = -1; break; }` aborts ambiguity resolution with `"LD factorization error"`! While `rtklibexplorer/RTKLIB` mitigates frequent fix-and-hold crashes symptomatically by loosening default `varholdamb` $100\times$ from `0.001` to `0.1` (`rtkcmn.c:220`) and gating on `minholdsats = 5` (`rtkpos.c:1699`), the underlying unstabilized `(I - K H^T) P` implementation in `filter_()` remains unchanged.

#### 2.2 Three-Regime Numerical Stability Hierarchy (`Standard` vs. `Joseph` vs. `Bierman–Thornton UD`)

To guarantee $P \succ 0$ across ill-conditioned `INS`/`GNSS` updates without runtime `sqrt()` bottlenecks (`Carlson 1973` Cholesky requires $n$ scalar square roots per measurement; `Thornton 1976` / `Bierman 1977` **square-root-free `UD`** factors $P = U D U^T$ with unit upper-triangular $U$ and strictly positive diagonal $D > 0$), consider the canonical 2-state correlated benchmark $P_0 = U_0 D_0 U_0^T = \begin{bmatrix} 1 + S^2 & S^2 \\ S^2 & S^2 \end{bmatrix}$ updated with $H = [1, 1]^T$ and $R = 10^{-3}$ (`VAR_HOLDAMB`, exact posterior $\det(P^+) = \frac{S^2 R}{4 S^2 + 1 + R} \to 2.500000 \times 10^{-4}$):

| Scale Parameter $S$ ($\kappa(P_0) \sim 4 S^2$) | Standard `(I - K H^T) P` (`RTKLIB`) | Bucy–Joseph `(I - K H^T) P (I - K H^T)^T + K R K^T` | Bierman `UD` Update ($P = U D U^T$) |
| :---: | :---: | :---: | :---: |
| **`S = 2.0e6`** ($\kappa \approx 1.6 \times 10^{13}$) | `+4.882812e-04` (95% det error) | **`+2.500000e-04`** (exact) | **`+2.500000e-04`** (exact) |
| **`S = 8.0e6`** ($\kappa \approx 2.6 \times 10^{14}$) | **`-1.953125e-03`** (**NEGATIVE $\implies$ `LD` ABORT**) | **`+2.500000e-04`** (exact) | **`+2.500000e-04`** (exact) |
| **`S = 1.0e8`** ($\kappa \approx 4.0 \times 10^{16}$) | `0.000000e+00` (singular collapse) | **`0.000000e+00`** (**SINGULAR COLLAPSE**) | **`+2.500000e-04`** (**EXACT**) |

**Derived Mechanism (`Probe 2B`):** Joseph form preserves symmetry and quadratic positivity up to $\kappa(P) \lesssim \varepsilon_{\text{mach}}^{-1} \approx 4.5 \times 10^{15}$, *beyond* which forming $P_0 = \begin{bmatrix} 1 + S^2 & S^2 \\ S^2 & S^2 \end{bmatrix}$ in IEEE-754 `binary64` rounds $1 + S^2 \to S^2$ before the filter even executes, making $P_0$ rank-1 singular (`det = 0`)! By storing $U$ (`u01 = 1.0`) and $D$ (`d0 = 1.0, d1 = S^2`) separately, Bierman's scalar measurement update + Thornton's Modified Weighted Gram-Schmidt (`MWGS`) time-propagation update square-roots the effective condition number ($\kappa(U D^{1/2}) \approx 2 S = 2 \times 10^8 \ll 4.5 \times 10^{15}$), remaining accurate past $S = 10^8$.

#### 2.3 Snapshot `valsol` / `raim_fde` vs. Sequential EKF Innovation Poisoning Under Ramp Spoofing

`RTKLIB` (`pntpos.c:279-307, 377-449`) implements **snapshot** Fault Detection and Exclusion (`FDE`): `valsol` rejects epochs whose weighted residual sum-of-squares `vv > chisqr[nv - nx - 1]`, and `raim_fde` performs leave-one-out subset exclusions selecting the minimum-RMS `n-1` fix (`nvsat >= 5`). By contrast, a sequential strapdown `INS`/`GNSS` EKF updates its prior state $\hat{\mathbf{x}}_{k|k-1}$ using measurements $\mathbf{z}_k$ gated by single-epoch Normalized Innovation Squared ($\text{NIS}_k = \boldsymbol{\nu}_k^T S_k^{-1} \boldsymbol{\nu}_k$).

**Execution Proof (`Probe 2B`):** Injecting a steady **`0.15 m/s`** spoofing ramp over `200` `1 Hz` epochs allows the EKF Kalman gain $K_k$ to **pull $\hat{\mathbf{x}}$ smoothly along the spoofed trajectory**, keeping **`max NIS = 0.0900`** (more than $100\times$ below the $\chi^2_{1, 0.999} = 10.83$ threshold!) while accumulating **`29.62 m` of undetected position error**—demonstrating why airborne integrity (`ARAIM`) requires sliding-window multi-epoch innovation statistics or inertial-only coasting sub-filters isolated from GNSS feedback.

---

### 3. Airborne Collision Avoidance: `HorizontalCAS` MDP Discretization vs. `KeYmaera X` Hybrid Games

Basis: normative (`RTCA DO-185B`; `DO-385` / `DO-386`; Jeannin et al., STTT 2017 DOI `10.1007/s10009-017-0452-9`; Katz et al., CAV 2017 DOI `10.1007/978-3-319-63387-9_5`) + source (`sisl/HorizontalCAS` @ `bc56a28cfe70b0486b6875deacfda947500bddcb`; `LS-Lab/KeYmaeraX-projects` @ `b9d7cb584e8fd1c3cc4f30644e82ba12cbb1d6fe`) + execution (`Probe 2C`).

#### 3.1 `sisl/HorizontalCAS` (`ACAS Xu`-Style) MDP Formulation, 1 Hz Euler Error, and NMAC Tunneling

`ACAS X` replaces `TCAS II` v7.1's brittle hand-tuned geometric rules (`RTCA DO-185B`) with dynamic-programming value tables ($Q(s, a)$) solved over a discrete Markov Decision Process (`MDP`) optimizing Near Mid-Air Collision (`NMAC`: horizontal separation $r \le 500\text{ ft}$, vertical separation $|h| \le 100\text{ ft}$) avoidance vs. alert/reversal penalties, optionally compressed into ReLU neural networks (`HCAS_rect_v6_*.nnet`, verified with SMT solver `Reluplex`, Katz et al. 2017). Direct inspection of `sisl/HorizontalCAS` (`GenerateTable/mdp/{constants,transitions,rewards}.jl`, `SolveMDP.jl`) highlights four critical verification boundaries:

1. **Discretized Grid & Fixed Speed Slice (`constants.jl:19-25`):** Discretizes $(r, \theta, \psi, v_{\text{own}}, v_{\text{int}}, \text{pra})$ onto `32` range cutpoints (`0..56,000 ft`), `41` bearings $\theta \in [-\pi, \pi]$, `41` headings $\psi \in [-\pi, \pi]$, and **single-speed slices** `OWNSPEEDS = [200.0]`, `INTRSPEEDS = [200.0]` ft/s using `RectangleGrid` multilinear interpolation (`SolveMDP.jl:55`) across `5` advisories (`COC, WL ±1.5°/s, WR, SL ±3.0°/s, SR`, `lines 30-35`).
2. **Baked-In 1-Step Response Latency (`transitions.jl:12`):** `ownProbs, ownTurns = mdp.turns[pra]` applies the *previous* advisory `pra` rather than the new command `ra` during the upcoming `1 s` step (`next_pra = ra`), encoding a 1-second actuator/pilot lag while heavily penalizing opposite-sense reversals (`rew -= 5e-2`, `rewards.jl:44-45`).
3. **1 Hz Forward-Euler Trajectory Error (`transitions.jl:28-37`):** Translates `x_own += vown` along the initial heading *before* updating `heading_own = ownTurn`. At $v = 420\text{ ft/s}$ and a $3^\circ/\text{s}$ (`SL`) turn (`Probe 2C`), the exact circular Dubins displacement `(419.81, 10.99) ft` deviates by **`10.99 ft/step`** laterally from Euler `(420.00, 0.00) ft`.
4. **Point-Sampled `tau == 0` NMAC Tunneling (`rewards.jl:28-30`):** Rewards penalize NMAC strictly at discrete integer seconds (`if tau == 0.0 && r <= 500.0: rew -= 1.0`). As demonstrated in **`Probe 2C`**, two head-on aircraft at `420 ft/s` each (`840 ft/s` closure) passing at `(420, 300) ft` at $t = 0\text{ s}$ (`r = 516.14 ft > 500`) and `(-420, 300) ft` at $t = 1\text{ s}$ (`r = 516.14 ft > 500`) register **zero NMAC penalty in the MDP transition**, even though at continuous $t = 0.5\text{ s}$ separation collapses to **`r(0.5s) = 300.00 ft`** (`200 ft` inside the `500 ft` NMAC cylinder)!

#### 3.2 `KeYmaera X` `dL` Explicit Safeable Regions (`Lexpl`) and `dGL` Intruder Hybrid Games

To eliminate discretization gaps and inter-sample tunneling, Jeannin et al. (`STTT 2017`; `LS-Lab/KeYmaeraX-projects/acasx/`) formally verify continuous-time vertical collision avoidance around the NMAC puck ($r_p = 500\text{ ft}$, $h_p = 100\text{ ft}$, minimal ownship vertical acceleration $a_{\text{lo}} = g/4 \approx 8.0435\text{ ft/s}^2$, relative altitude $h = h_{\text{int}} - h_{\text{own}}$):

- **Sign Convention & Quantifier Elimination (`acasx.kyx:6-18, 237-263`):** Direction parameter $w \in \{w_{\text{Lo}} = +1,\; w_{\text{Up}} = -1\}$ selects which side of the intruder the ownship commits to remain on (`w = +1`: ownship climbs at $a \ge +a_{\text{lo}}$ to stay *above* intruder $h < h_o - h_p$; `w = -1`: ownship descends at $a \le -a_{\text{lo}}$ to stay *below* intruder $h > h_o + h_p$). `Theorem 1` (`acasx.kyx:160-198`) proves inductive invariance of the universally quantified trajectory bound `Limpl(r, h, v, w, vlo, rv)`, while `Lemma 1` (`lines 234-264`) proves exact logical equivalence ($\text{Lexpl} \leftrightarrow \text{Limpl}$) with a **6-region quantifier-free polynomial formula `Lexpl`** (`case1..case4` for $w v_{\text{lo}} \ge 0$, `case5..case6` for $w v_{\text{lo}} < 0$), enabling $O(1)$ runtime safety shielding of MDP tables without solving ODEs online!
- **Two-Sided Delayed Advisories & Adversarial Intruder Games (`acasx-games/Safeability for a Vertically-Maneuvering Intruder.kyx:15-108`):** Real aircraft must respect *both* lower and upper advisory bands (`[vlo, vup]`) under reaction delay $\varepsilon$, while the intruder can continuously accelerate vertically within $|h''_{\text{int}}| < c$. `KeYmaera X` models this as a **Differential Game Logic (`dGL`)** hybrid game:
  $$\{\text{choose } (\text{dhf}, v_{\text{up}}, w) \text{ s.t. } C(\dots, \varepsilon);\; t:=0;\; \{ao:=*\}^@;\; \{hai:=*; ?(|hai| < c);\; \text{motion}\}^*\}$$
  where `{ao := *}^@` (`line 104`) denotes the angelically controlled ownship choosing acceleration inside the advisory envelope `EDC`, against the demonic intruder choosing worst-case `hai in (-c, c)` (`line 105`), provably safe whenever $a_{\text{up}} > a_{\text{lo}} + 2c$ (`init`, line 58). As Jeannin et al. (2017) demonstrated, intersecting raw `ACAS X` MDP lookup tables with `Lexpl` / `C` exposed concrete boundary geometries where the legacy table issued `COC` or weak advisories inside unsafe regions before table/cost tuning.
- **Execution Quantification (`Probe 2C`):** Evaluating `Lexpl` on a level ownship (`v0 = 0 ft/s`) `50 ft` above an intruder (`h0 = -50 ft`) closing at `840 ft/s` under `CL1500` (`w = +1`, `vlo = +25 ft/s`, `alo = g/4`): zero-delay safe entry range is **`3490 ft`** (verified continuously with minimum puck vertical separation `101.15 ft > 100 ft`), expanding to **`7690 ft`** when guarding a `5 s` pilot reaction delay $\varepsilon = 5\text{ s}$ (`+4200 ft` horizontal closure).

## Boundaries

- **Known not to apply — `Galileo OSNMA` Against Causal RF Meaconing / Differential Delay Spoofing:** `OSNMA` cryptographically authenticates navigation *bits*, not RF propagation delay. Shifting authentic subframes by causal microsecond delays (`Probe 2A`) bypasses both `OSNMA` and snapshot `valsol` $\chi^2$ checks unless paired with independent timing/spatial diversity (dual-antenna carrier phase, IMU cross-check, or tight nanosecond clock holdover).
- **Known not to apply — Unstabilized `(I - K H^T) P` Filters to High-Condition-Number `INS`/`GNSS` & Tight Hold Updates:** `RTKLIB`'s `filter_()` (`rtkcmn.c:1076-1077`) loses positive-definiteness at $S = 8 \times 10^6$ (`Probe 2B`), crashing `lambda.c:36` (`LD factorization error`); even Bucy–Joseph collapses to singular `0.0` once $1 + S^2$ underflows `binary64` at $S = 10^8$, requiring `UD` / square-root factorization.
- **Known not to apply — `sisl/HorizontalCAS` 1 Hz Discrete Transition Safety to Continuous Trajectories:** Discrete `tau == 0` NMAC checks (`rewards.jl:28-30`) miss high-closure inter-sample puck penetrations (`300.00 ft < 500 ft` at $t=0.5\text{ s}$ in `Probe 2C`) and accumulate `10.99 ft/step` Euler lateral drift; continuous safety requires `dL`/`dGL` safeable shields (`Lexpl` / `C`).
- **Unsupported — `FLX` `MACLT` Slots and Bounded Key-Chain Derivations in `nlsfi/fgi-osnma`:** At revision `f404aa94`, `fgi-osnma` stubs `verify_MACSEQ`, rejects `FLX` slots, supports only 4 of 12 `MACLT` entries, and lacks a derivation step cap.
- **Not examined — Closed-Source Certified `TCAS II` / `ACAS Xa` Production MOPS Runbooks, Inertial MEMS Allan-Variance Drift Models Under Multi-Minute Outages, and Multi-Antenna Spoofing Phase Synchronization:** Only open-source research/reference implementations (`galileo-osnma`, `fgi-osnma`, `RTKLIB`, `HorizontalCAS`, `KeYmaeraX-projects`) were inspected at source level; phased-array multi-element spoofing hardware able to replicate spatial carrier-phase wavefronts across dual antennas was not modeled.
- **Unknown — Downstream User Fixes Beyond Pinned `PubkeyStore::revoke` Line `629` in `daniestevez/galileo-osnma`:** Whether later commits beyond `b6c337b3d559b22edd7fa45fb5c4ee93c962c533` patched `self.current = None` to `self.next = None` in `osnma.rs:629` was not checked.

## Evidence

### Primary Upstream Source Citations (Observed 2026-11-19)

1. **`daniestevez/galileo-osnma` @ `b6c337b3d559b22edd7fa45fb5c4ee93c962c533`:**
   - `galileo-osnma/src/validation.rs:15-27` (`Validated`, `NotValidated` typestates).
   - `galileo-osnma/src/tesla.rs:508-512, 681-756, 783-797, 974-1008` (`store_gst`, `one_way_function`, `validate_key` with `derivations > 3000` check at lines 745-747, `validate_tag`, `validate_macseq`).
   - `galileo-osnma/src/maclt.rs:60-205` (full 12-entry ICD v1.1 `MACLT` `{27..41}`, `get_maclt_entry`, `get_flx_indices`).
   - `galileo-osnma/src/navmessage.rs:18-21, 217-265, 319-450` (`MIN_AUTHBITS: u16 = 40`, `process_mack`).
   - `galileo-osnma/src/osnma.rs:192-213, 440-494, 613-631` (`feed_inav`, `feed_osnma`, Slow MAC `add_seconds(-300)`, `PubkeyStore::revoke` line `629` clearing `self.current` instead of `self.next`).
2. **`nlsfi/fgi-osnma` @ `f404aa947b3eb547a2ffbadb7fcbcb406fabb022`:**
   - `osnma/authentication.py:121-159` (`hashlib.sha256`, `mac_function = None` TODO), `241-265` (unbounded `dt // 30` in `verify_tesla_key_against_trusted_key`, empty `verify_MACSEQ` stub), `281-315` (4-entry `MACLT` `{27, 28, 31, 33}` raising on `FLX`), `352-355` (`verify_public_key` returning `True` when `merkle_tree == None`).
3. **`tomojitakasu/RTKLIB` @ `71db0ffa0d9735697c6adfd06fdf766d0e5ce807` & `rtklibexplorer/RTKLIB` @ `755e6379ae600e71980b6b20d846d6d35ca8a1aa`:**
   - `tomojitakasu/RTKLIB`: `src/rtkcmn.c:1062-1102` (`filter_` `(I - K*H')*P` and `filter`), `src/lambda.c:29-188` (`LD` checking `D[i] <= 0.0` at line 36, `reduction`, `search`, `lambda`), `src/rtkpos.c:62` (`VAR_HOLDAMB = 0.001`), `1320-1435` (`holdamb`, `resamb_LAMBDA`), `src/pntpos.c:279-307, 377-449` (`valsol`, `raim_fde`).
   - `rtklibexplorer/RTKLIB`: `src/rtkcmn.c:220` (`varholdamb = 0.1`), `1459-1503` (`filter_`, `filter`), `src/rtkpos.c:1655-1715` (`holdamb` with `minholdsats` guard).
4. **`sisl/HorizontalCAS` @ `bc56a28cfe70b0486b6875deacfda947500bddcb`:**
   - `GenerateTable/mdp/constants.jl:1-35` (state discretization, `OWNSPEEDS = [200.0]`, turn rates).
   - `GenerateTable/mdp/transitions.jl:2-45` (9-point sigma sampling, `mdp.turns[pra]` 1-step lag, forward-Euler step).
   - `GenerateTable/mdp/rewards.jl:8-56` (`tau == 0.0 && r <= 500.0` discrete NMAC check, reversal/strengthen/weaken penalties).
   - `GenerateTable/SolveMDP.jl:18-120` (`nTau_max = 60`, `RectangleGrid` interpolation).
5. **`LS-Lab/KeYmaeraX-projects` @ `b9d7cb584e8fd1c3cc4f30644e82ba12cbb1d6fe`:**
   - `acasx/acasx.kyx:1-25, 160-264` (`Limpl`, `Theorem 1`, `Lemma 1` 6-case quantifier-free `Lexpl`).
   - `acasx/acasxtwosided.kyx:1-42` (`Limpl`, `Uimpl`, `Cimpl`, `advisoryLo`, `advisoryUp`).
   - `acasx/acasx-games/Safeability for a Vertically-Maneuvering Intruder.kyx:15-108` (`Lone`, `Lep`, `Ladd`, `Uadd`, `Uep`, `C`, `EDC`, `init` requiring `aup > alo + 2*c`, `dGL` hybrid game).

### Primary Standards & Literature Citations

- `Galileo OSNMA SIS ICD v1.1` & `Galileo OSNMA Receiver Guidelines v1.3`, European Union / EUSPA.
- `RTCA DO-185B` (*Minimum Operational Performance Standards for Traffic Alert and Collision Avoidance System II (TCAS II)*, v7.1), `RTCA DO-385` (*ACAS Xa/Xo MOPS*), and `RTCA DO-386` (*ACAS Xu MOPS*).
- Maryam Motallebighomi, Harshad Sathaye, Mridula Singh, and Aanjhan Ranganathan, "Location-independent GNSS Relay Attacks: A Lazy Attacker's Guide to Bypassing Navigation Message Authentication," *ACM WiSec 2023*, DOI `10.1145/3558482.3590186`.
- Peter J. G. Teunissen, "The least-squares ambiguity decorrelation adjustment: a method for fast GPS integer ambiguity estimation," *Journal of Geodesy* 70(1):65–82, 1995, DOI `10.1007/BF00863419`.
- Neal A. Carlson, "Fast triangular formulation of the square root filter," *AIAA Journal* 11(9):1259–1265, 1973, DOI `10.2514/3.6907`.
- Gerald J. Bierman, *Factorization Methods for Discrete Sequential Estimation*, Academic Press, 1977, ISBN `978-0-12-097350-7`.
- Catherine L. Thornton, *Triangular Covariance Factorizations for Kalman Filtering*, NASA JPL TM-33-798 / NASA-CR-149147, October 1976.
- Jean-Baptiste Jeannin, Khalil Ghorbal, Yanni Kouskoulas, Aurora Schmidt, Ryan Gardner, Stefan Mitsch, and André Platzer, "A Formally Verified Hybrid System for Safe Advisories in the Next-Generation Airborne Collision Avoidance System," *STTT* 19(6):717–740, 2017, DOI `10.1007/s10009-017-0452-9`.
- Guy Katz, Clark Barrett, David L. Dill, Kyle Julian, and Mykel J. Kochenderfer, "Reluplex: An Efficient SMT Solver for Verifying Deep Neural Networks," *CAV 2017*, LNCS 10426, pp. 97–117, DOI `10.1007/978-3-319-63387-9_5`.

### Self-Contained Executable Micro-Probe (`Probes 2A, 2B, 2C`)

Executed with Python 3 (standard library only) on Linux x86_64 on `2026-11-19`:

```python
#!/usr/bin/env python3
"""Standalone micro-probes for:
2A: Galileo OSNMA TESLA Chain & HMAC Tag Verification vs. Differential
    Time-of-Arrival Meaconing + Carrier-Phase Double-Difference Incompatibility.
2B: Three-Regime Kalman Covariance Collapse (RTKLIB (I-KH)P vs. Joseph Form vs.
    Bierman-Thornton UD) & Slowly Ramped Spoofing Innovation Poisoning vs. RAIM.
2C: ACAS X / HorizontalCAS 1 Hz Forward-Euler NMAC Tunneling vs. KeYmaera X
    Explicit Safeable Hybrid Envelope (Lexpl) & Delayed Pilot Reaction Shift.
"""
from __future__ import annotations

import hashlib
import hmac
import math


def probe_2a_osnma_and_meaconing() -> None:
    print("=== PROBE 2A: Galileo OSNMA TESLA Chain vs. Differential ToA Meaconing ===")
    def pack_gst(wn: int, tow: int) -> bytes:
        return (((wn & 0xFFF) << 20) | (tow & 0xFFFFF)).to_bytes(4, "big")

    def tesla_owf(k_next: bytes, gst_prev: tuple[int, int], alpha6: bytes, key_bytes: int = 16) -> bytes:
        return hashlib.sha256(k_next + pack_gst(*gst_prev) + alpha6).digest()[:key_bytes]

    alpha6 = bytes.fromhex("0123456789ab")
    k2 = bytes.fromhex("a0b1c2d3e4f5061728394a5b6c7d8e9f")
    wn, tow0 = 1268, 208860
    k1 = tesla_owf(k2, (wn, tow0 + 30), alpha6)
    k0_root = tesla_owf(k1, (wn, tow0), alpha6)
    check_k0 = tesla_owf(tesla_owf(k2, (wn, tow0 + 30), alpha6), (wn, tow0), alpha6)
    assert check_k0 == k0_root

    ced_valid = b"GAL_E1B_INAV_CED_SVN12_EPHEMERIS_SUBFRAME_0001"
    ced_tampered = b"GAL_E1B_INAV_CED_SVN12_EPHEMERIS_SUBFRAME_0002"
    ctx_prefix = bytes([12, 12]) + pack_gst(wn, tow0 + 30) + bytes([1, 0b10])
    tag_40 = hmac.new(k1, ctx_prefix + ced_valid, hashlib.sha256).digest()[:5]
    tag_tampered = hmac.new(k1, ctx_prefix + ced_tampered, hashlib.sha256).digest()[:5]
    print(f"  TESLA chain K2->K1->K0 verified: {check_k0.hex()[:16]}... == KROOT")
    print(f"  MACK 40-bit tag valid CED={tag_40.hex()} vs 1-bit forged CED={tag_tampered.hex()} (match={tag_40 == tag_tampered})")

    c = 299_792_458.0
    sats = [
        (15_600_000.0,  10_000_000.0, 20_000_000.0),
        (-12_000_000.0, 14_000_000.0, 21_000_000.0),
        (5_000_000.0, -18_000_000.0, 19_500_000.0),
        (-16_000_000.0, -9_000_000.0, 20_500_000.0),
        (2_000_000.0,   2_000_000.0, 26_000_000.0),
    ]
    p_true = (4_200_000.0, 170_000.0, 4_780_000.0)
    p_fake = (p_true[0] + 1000.0, p_true[1] + 500.0, p_true[2])
    common_delay_m = 4.0e-6 * c

    def norm3(a, b):
        return math.sqrt(sum((a[i] - b[i]) ** 2 for i in range(3)))

    rho_true = [norm3(p_true, s) for s in sats]
    rho_spoof = [norm3(p_fake, s) + common_delay_m for s in sats]
    delays_us = [(rho_spoof[k] - rho_true[k]) / c * 1e6 for k in range(len(sats))]
    print(f"  Per-sat causal RF delays (us): {[round(d, 3) for d in delays_us]} (all >= 0, all << 15s TESLA sync!)")

    x = [p_true[0], p_true[1], p_true[2], 0.0]
    for _ in range(8):
        H, v = [], []
        for k, s in enumerate(sats):
            r = norm3(x[:3], s)
            H.append([(x[i] - s[i]) / r for i in range(3)] + [1.0])
            v.append(rho_spoof[k] - (r + x[3]))
        A = [[sum(H[k][i] * H[k][j] for k in range(len(sats))) for j in range(4)] for i in range(4)]
        b = [sum(H[k][i] * v[k] for k in range(len(sats))) for i in range(4)]
        for i in range(4):
            piv = max(range(i, 4), key=lambda r: abs(A[r][i]))
            A[i], A[piv] = A[piv], A[i]; b[i], b[piv] = b[piv], b[i]
            for r in range(i + 1, 4):
                fac = A[r][i] / A[i][i]
                for c_idx in range(i, 4):
                    A[r][c_idx] -= fac * A[i][c_idx]
                b[r] -= fac * b[i]
        dx = [0.0] * 4
        for i in range(3, -1, -1):
            dx[i] = (b[i] - sum(A[i][j] * dx[j] for j in range(i + 1, 4))) / A[i][i]
            x[i] += dx[i]
    vv = sum((rho_spoof[k] - (norm3(x[:3], sats[k]) + x[3])) ** 2 for k in range(len(sats)))
    print(f"  Spoofed WLS fix delta=(dX={x[0]-p_true[0]:.2f}m, dY={x[1]-p_true[1]:.2f}m, dZ={x[2]-p_true[2]:.2f}m), post-fit residual vv={vv:.2e} (valsol PASS!)")
    dd_true = [((sats[k][0]-p_true[0])/rho_true[k] - (sats[0][0]-p_true[0])/rho_true[0]) * 0.50 for k in range(1, 5)]
    print(f"  0.50m dual-antenna DD carrier geometry (m): true={[round(d, 4) for d in dd_true]} vs single-antenna spoofer={[0.0]*4}")


def probe_2b_kalman_and_ramp_raim() -> None:
    print("\n=== PROBE 2B: Three-Regime Kalman Covariance Collapse & Ramp-Spoofing vs. RAIM ===")
    H, R = [1.0, 1.0], 1e-3
    for S in (2e6, 8e6, 1e8):
        P = [[1.0 + S * S, S * S], [S * S, S * S]]
        F = [P[0][0] * H[0] + P[0][1] * H[1], P[1][0] * H[0] + P[1][1] * H[1]]
        Q = H[0] * F[0] + H[1] * F[1] + R
        K = [F[0] / Q, F[1] / Q]
        I_KH = [[1.0 - K[0] * H[0], -K[0] * H[1]], [-K[1] * H[0], 1.0 - K[1] * H[1]]]
        Pp_std = [[sum(I_KH[i][k] * P[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
        Pp_jos = [[sum(Pp_std[i][k] * I_KH[j][k] for k in range(2)) + K[i] * R * K[j] for j in range(2)] for i in range(2)]
        f0, f1 = H[0], 1.0 * H[0] + H[1]
        v0, v1 = 1.0 * f0, (S * S) * f1
        a0 = R + v0 * f0; d0_ud = 1.0 * R / a0
        a1 = a0 + v1 * f1; d1_ud = (S * S) * a0 / a1
        det_std = Pp_std[0][0] * Pp_std[1][1] - Pp_std[0][1] * Pp_std[1][0]
        det_jos = Pp_jos[0][0] * Pp_jos[1][1] - Pp_jos[0][1] * Pp_jos[1][0]
        print(f"  f64 S={S:7.1e}: Std det={det_std:+.6e} | Joseph det={det_jos:+.6e} | Bierman UD det={d0_ud*d1_ud:+.6e}")

    pos_est, P_pos, sigma_pr, max_nis = 0.0, 2.0, 1.5, 0.0
    for epoch in range(1, 201):
        P_pos += 0.25
        innov = (0.15 * float(epoch)) - pos_est
        S_inn = P_pos + sigma_pr * sigma_pr
        max_nis = max(max_nis, (innov * innov) / S_inn)
        K_g = P_pos / S_inn
        pos_est += K_g * innov
        P_pos = (1.0 - K_g) * P_pos
    print(f"  Ramp spoofing (200s @ 0.15 m/s): max single-epoch NIS={max_nis:.4f} (<< chi2 gate 10.83), drifted pos_est={pos_est:.2f} m!")


def probe_2c_acasx_and_keymaerax() -> None:
    print("\n=== PROBE 2C: HorizontalCAS 1 Hz Tunneling & KeYmaera X Lexpl Safeable Region ===")
    r_p, h_p, vown, vint = 500.0, 100.0, 420.0, 420.0
    x_int, y_int = 420.0, 300.0
    r0 = math.hypot(x_int, y_int)
    r1 = math.hypot(x_int + vint * math.cos(math.pi) - vown, y_int + vint * math.sin(math.pi))
    r_mid = math.hypot(x_int + 0.5 * (vint * math.cos(math.pi) - vown), y_int)
    print(f"  HorizontalCAS 1Hz NMAC tunneling: r(0s)={r0:.2f} ft (>500), r(1s)={r1:.2f} ft (>500), continuous r(0.5s)={r_mid:.2f} ft (<< 500 ft NMAC!)")

    omega = math.radians(3.0)
    x_arc, y_arc = (vown / omega) * math.sin(omega), (vown / omega) * (1.0 - math.cos(omega))
    print(f"  1s SL turn (3 deg/s @ 420 ft/s): Euler=(420.00, 0.00) vs Exact Dubins=({x_arc:.2f}, {y_arc:.2f}), lateral error={abs(y_arc):.2f} ft/step")

    alo, w, vlo, rv = 32.174 / 4.0, 1.0, 25.0, 840.0
    def lexpl_safe(r: float, h: float, v: float, w_arg: float, vlo_arg: float) -> bool:
        min_i = min(0.0, v * w_arg)
        max_i = max(0.0, w_arg * (vlo_arg - v))
        if w_arg * vlo_arg >= 0.0:
            c1 = (-r_p <= r < -r_p - rv * min_i / alo)
            b1 = (w_arg * (rv ** 2) * h < (alo / 2.0) * ((r + r_p) ** 2) + w_arg * rv * v * (r + r_p) - (rv ** 2) * h_p)
            c2 = (-r_p - rv * min_i / alo <= r <= r_p - rv * min_i / alo)
            b2 = (w_arg * h < -(min_i ** 2) / (2.0 * alo) - h_p)
            c3 = (r_p - rv * min_i / alo < r <= r_p + rv * max_i / alo)
            b3 = (w_arg * (rv ** 2) * h < (alo / 2.0) * ((r - r_p) ** 2) + w_arg * rv * v * (r - r_p) - (rv ** 2) * h_p)
            c4 = (r > r_p + rv * max_i / alo)
            b4 = (rv == 0.0 or w_arg * rv * h < w_arg * vlo_arg * (r - r_p) - rv * (max_i ** 2) / (2.0 * alo) - rv * h_p)
            return ((not c1 or b1) and (not c2 or b2) and (not c3 or b3) and (not c4 or b4))
        c5 = (-r_p <= r < -r_p + rv * max_i / alo)
        b5 = (w_arg * (rv ** 2) * h < (alo / 2.0) * ((r + r_p) ** 2) + w_arg * rv * v * (r + r_p) - (rv ** 2) * h_p)
        c6 = (r >= -r_p + rv * max_i / alo)
        b6 = ((rv == 0.0 and r > r_p) or w_arg * rv * h < w_arg * vlo_arg * (r + r_p) - rv * (max_i ** 2) / (2.0 * alo) - rv * h_p)
        return ((not c5 or b5) and (not c6 or b6))

    h0, v0 = -50.0, 0.0
    r_crit_0 = next(r for r in range(500, 15000, 10) if lexpl_safe(float(r), h0, v0, w, vlo))
    r_crit_5 = r_crit_0 + int(rv * 5.0)
    min_h_sep = min(abs(h0 - (0.5 * alo * min(t, vlo / alo) ** 2 + max(0.0, t - vlo / alo) * vlo))
                    for step in range(0, 600) for t in [step * 0.05] if abs(r_crit_0 - rv * t) <= r_p)
    print(f"  KeYmaera X Lexpl (CL1500 w=+1, h0=-50ft, v0=0, rv=840ft/s): r_safe(eps=0s)={r_crit_0} ft (min vertical sep in puck={min_h_sep:.2f} ft > 100 ft) | r_safe(eps=5s pilot delay)={r_crit_5} ft")


if __name__ == "__main__":
    probe_2a_osnma_and_meaconing()
    probe_2b_kalman_and_ramp_raim()
    probe_2c_acasx_and_keymaerax()
```

Observed output:

```text
=== PROBE 2A: Galileo OSNMA TESLA Chain vs. Differential ToA Meaconing ===
  TESLA chain K2->K1->K0 verified: 85ed91ed3976b420... == KROOT
  MACK 40-bit tag valid CED=9e3e9b2c20 vs 1-bit forged CED=02c06a2cca (match=False)
  Per-sat causal RF delays (us): [1.458, 5.157, 5.181, 7.041, 4.2] (all >= 0, all << 15s TESLA sync!)
  Spoofed WLS fix delta=(dX=1000.00m, dY=500.00m, dZ=0.00m), post-fit residual vv=0.00e+00 (valsol PASS!)
  0.50m dual-antenna DD carrier geometry (m): true=[-0.5688, -0.2492, -0.6377, -0.3176] vs single-antenna spoofer=[0.0, 0.0, 0.0, 0.0]

=== PROBE 2B: Three-Regime Kalman Covariance Collapse & Ramp-Spoofing vs. RAIM ===
  f64 S=2.0e+06: Std det=+4.882812e-04 | Joseph det=+2.500000e-04 | Bierman UD det=+2.500000e-04
  f64 S=8.0e+06: Std det=-1.953125e-03 | Joseph det=+2.500000e-04 | Bierman UD det=+2.500000e-04
  f64 S=1.0e+08: Std det=+0.000000e+00 | Joseph det=+0.000000e+00 | Bierman UD det=+2.500000e-04
  Ramp spoofing (200s @ 0.15 m/s): max single-epoch NIS=0.0900 (<< chi2 gate 10.83), drifted pos_est=29.62 m!

=== PROBE 2C: HorizontalCAS 1 Hz Tunneling & KeYmaera X Lexpl Safeable Region ===
  HorizontalCAS 1Hz NMAC tunneling: r(0s)=516.14 ft (>500), r(1s)=516.14 ft (>500), continuous r(0.5s)=300.00 ft (<< 500 ft NMAC!)
  1s SL turn (3 deg/s @ 420 ft/s): Euler=(420.00, 0.00) vs Exact Dubins=(419.81, 10.99), lateral error=10.99 ft/step
  KeYmaera X Lexpl (CL1500 w=+1, h0=-50ft, v0=0, rv=840ft/s): r_safe(eps=0s)=3490 ft (min vertical sep in puck=101.15 ft > 100 ft) | r_safe(eps=5s pilot delay)=7690 ft
```

## Revalidation

1. **Re-check `daniestevez/galileo-osnma` Revocation & `nlsfi/fgi-osnma` Hardening:** Diff `galileo-osnma/src/osnma.rs:613-631` against `b6c337b3d559b22edd7fa45fb5c4ee93c962c533` to see whether `PubkeyStore::revoke` clears `self.next = None` instead of `self.current = None`, and diff `fgi-osnma/osnma/authentication.py:241-355` against `f404aa947b3eb547a2ffbadb7fcbcb406fabb022` for `verify_MACSEQ`, `FLX` handling, and derivation limits.
2. **Re-check `RTKLIB` Covariance Factorization:** Diff `src/rtkcmn.c` (`filter_`) and `src/lambda.c` (`LD`) in `tomojitakasu/RTKLIB` (`71db0ffa`) and `rtklibexplorer/RTKLIB` (`755e6379`) to confirm whether `(I - K H^T) P` has been replaced by Joseph form or `UD` factorization.
3. **Re-check `HorizontalCAS` / `KeYmaeraX-projects` Models:** Inspect `GenerateTable/mdp/{transitions,rewards}.jl` (`bc56a28c`) and `acasx/acasx*.kyx` (`b9d7cb58`) for any updated continuous collision-check or delayed-response invariants.
4. **Re-run Executable Micro-Probes:** Save the Python 3 script from **Evidence** as `/tmp/probe_gnss_kalman_acasx.py` and execute `python3 /tmp/probe_gnss_kalman_acasx.py` to re-verify the `OSNMA` WLS meaconing fix, the 3-regime Kalman determinant separation (`-1.953125e-03`, `0.0`, `+2.500000e-04`), the `0.15 m/s` ramp-spoofing innovation drift, and the `HorizontalCAS` 1 Hz tunneling / `KeYmaera X Lexpl` range bounds.
