# Target-Controlled Propofol Anesthesia PK/PD Models, Allometric Covariate Paradoxes, BIS EMG Artifacts, and Pharmacometric ODE Solvers

## Summary

Target-Controlled Infusion (TCI) syringe pumps and Bayesian clinical precision-dosing systems compute intravenous anesthetic infusion profiles by integrating three-compartment mammillary pharmacokinetic (PK) ordinary differential equations coupled to a first-order effect-site pharmacodynamic (PD) compartment ($C_e$, equilibration rate $k_{e0}$). Direct inspection of primary clinical models (Marsh 1991, Schnider 1998, Eleveld 2018) and four open-source pharmacometric solver stacks (`mrgsolve`, `Torsten`, `PKPDsim`, and `stan-dev/math`), paired with standalone double-precision numerical probes, establishes five load-bearing invariants and failure mechanisms:

1. **Quadratic Anthropometric Paradox in Schnider (1998):** Schnider's elimination clearance $\mathrm{CL}_1 = 1.89 + 0.0456(W - 77) - 0.0681(\mathrm{LBM} - 59) + 0.0264(H - 177)$ depends *negatively* on James Lean Body Mass ($\mathrm{LBM}_M = 1.10 W - 128(W/H)^2$, $\mathrm{LBM}_F = 1.07 W - 148(W/H)^2$). Because James LBM turns strictly decreasing above $\mathrm{BMI} = 42.97\text{ kg/m}^2$ (male) and $\mathrm{BMI} = 36.15\text{ kg/m}^2$ (female), and crosses zero at $\mathrm{BMI} = 85.94\text{ kg/m}^2$ (male) and $72.30\text{ kg/m}^2$ (female), both the $+W$ and $-\mathrm{LBM}$ terms accelerate $\mathrm{CL}_1$ quadratically in obese patients while $V_1 = 4.27\text{ L}$ remains fixed—producing $k_{10} = 2.15\text{ min}^{-1}$ (a $2.15\times$ clearance and $3.95\times$ $k_{10}$ overdose relative to Eleveld) in a $180\text{ kg}, 165\text{ cm}$ female and $k_{10} = 4.31\text{ min}^{-1}$ at $250\text{ kg}$. Simultaneously, Schnider's affine age terms drive $V_2 \le 0$ at $\text{Age} \ge 101.34\text{ yr}$ and $\mathrm{CL}_2 \le 0$ at $\text{Age} \ge 106.75\text{ yr}$. Eleveld (2018) eliminates both domain collapses via strictly positive, weight-monotone Al-Sallami fat-free mass, saturating central volume $V_{1,\text{art}}(W) \to 9.29\text{ L}$, allometric $W^{0.75}$ scaling, and exponential aging.
2. **Closed-Form Cubic Degeneracy NaNs in `mrgsolve` and `PKPDsim`:** Both `mrgsolve` (`src/odeproblem.cpp:625-649`, `advan11`) and `PKPDsim` (`src/pk_3cmt_iv_infusion.cpp:52-68`) compute three-compartment eigenvalues via trigonometric cubic formulas without clamping the `acos`/`sqrt` arguments or guarding coalescent partial-fraction denominators. Although `mrgsolve` explicitly allows $Q \ge 0, Q_2 \ge 0$, at the $Q = Q_2 = 0$ one-compartment boundary IEEE-754 rounding triggers `acos(1 + 1 ULP) = NaN` in `49/199` tested $k_{10}$ values in `mrgsolve` and `sqrt(-q) = NaN` ($q > 0$) in `71/199` values in `PKPDsim`.
3. **Inhomogeneous Matrix-Exponential Cancellation vs. Fixed-Step RK4 Blowup:** `stan-dev/math`'s Higham (2005) scaling-and-squaring Padé `[3/3]`–`[13/13]` propagator (`MatrixExponential.h:65-212`) remained non-negative and accurate to $\sim 10^{-16}$ on tested Metzler rate matrices, but `Torsten`'s constant-infusion wrapper `exp(dt * K) * (y + K^{-1} r) - K^{-1} r` (`pmx_linode_model.hpp:147-159`) suffers catastrophic cancellation at small intervals (yielding negative compartment state $-7.11 \times 10^{-15}$ at $\Delta t = 10^{-10}\text{ min}$) and throws on singular $K$ (e.g., models augmented with a cumulative elimination sink). Van Loan's augmented block matrix exponential eliminates both failures with $0.0$ mass-balance residual. Separately, `PKPDsim`'s general ODE template (`inst/cpp/sim.cpp:2`) hardcodes fixed-step explicit `runge_kutta4` (default `int_step_size = 0.01`); under stiff obese Schnider kinetics ($k_{10} = 160.7\text{ h}^{-1}$, $h_{\text{crit}} = 0.0142\text{ h}$), stepping at $h = 0.015\text{ h}$ explodes to $-7.47 \times 10^5\text{ mg}$.
4. **Cross-Engine Bioavailability-Duration Semantic Divergence & Lag-Time Truncation Bug:** On infusions with bioavailability $F < 1$, `mrgsolve` (`src/datarecord.cpp:140-142`) scales *duration* ($D = F \cdot \mathrm{AMT}/\mathrm{RATE}$) at fixed rate (NONMEM convention), whereas `Torsten` (`ev_history.hpp:639`, `ev_manager.hpp:237`) and `PKPDsim` (`inst/cpp/sim.cpp:225-227`) scale *rate* ($F \cdot \mathrm{RATE}$) at fixed duration—yielding a $+52.8\%$ higher $C_{\max}$ in `mrgsolve` for $F = 0.6$. Additionally, `PKPDsim`'s `apply_lagtime` (`inst/cpp/sim.cpp:92,111`) casts `rate` to `std::vector<int>`, silently truncating fractional infusion rates ($0 < |\text{rate}| < 1$) to `0` and failing to lag infusion-stop records.
5. **Closed-Loop BIS EMG Spoofing and Pure Transport Lag:** Because the Bispectral Index (BIS) integrates $30\text{--}47\text{ Hz}$ cortical power that overlaps frontalis electromyography (EMG), muscle tone or electrocautery can falsely elevate BIS to $65\text{--}80$ while Eleveld's age-dependent BIS processing delay $\mathrm{BIS}_{\text{delay}} = 15 + e^{0.0517 \cdot \text{Age}}$ reaches $77.6\text{ s}$ at age $80\text{ yr}$. Unprotected PID-TCI loops escalate into deep overdose under EMG spikes; even hard $C_e$ ceilings overshoot via central-to-effect-site equilibration inertia unless paired with EMG/SQI freeze gating.

## Applicability

These findings govern:

- **Clinical PK/PD Model Specifications:** Three-compartment linear mammillary intravenous propofol models with first-order effect-site link ($dC_e/dt = k_{e0}(C_1 - C_e)$): Marsh et al. (1991), Schnider et al. (1998, `DOI: 10.1097/00000542-199805000-00006`), and Eleveld et al. (2018, `DOI: 10.1016/j.bja.2018.01.018`), evaluated across pediatric ($5\text{ yr}, 18\text{ kg}$), reference adult ($35\text{ yr}, 70\text{ kg}$), elderly/centenarian ($80\text{--}105\text{ yr}$), and obese/super-obese ($W \in [115, 250]\text{ kg}, \mathrm{BMI} \in [36, 92]\text{ kg/m}^2$) cohorts.
- **Pinned Upstream Software Revisions Examined via Source Inspection:**
  - `metrumresearchgroup/mrgsolve` at `c529f2decd8d5b48b11760126d68d883547932b0` (v2.1.0.9000): closed-form `ADVAN` 1/2/3/4/11/12 (`src/odeproblem.cpp`) and `ODEPACK` `LSODA` (`ADVAN 13`, `src/LSODA.cpp`, `src/devtran.cpp`, `src/datarecord.cpp`).
  - `metrumresearchgroup/Torsten` at `16a954822cf794648d2e0535aa0d877b295e90b1`: linear-ODE matrix-exponential (`pmx_linode_model.hpp`), `NONMEM` event history/manager (`ev_history.hpp`, `ev_manager.hpp`, `ev_solver.hpp`), and SUNDIALS `CVODES` wrappers (`dsolve/pmx_cvodes_integrator.hpp`).
  - `InsightRX/PKPDsim` at `b5b81157c1550d2ae429aa46b59dc678f5670878` (v1.5.0): analytical 3-compartment C++ routines (`src/pk_3cmt_iv_infusion.cpp`) and Boost.Odeint C++ simulation template (`inst/cpp/sim.cpp`, `R/sim.R`, `R/new_ode_model.R`).
  - `stan-dev/math` at `3d16e8f14e620e2cd35cc59bf92766ad98a9559b`: Padé scaling-and-squaring (`stan/math/prim/fun/matrix_exp.hpp`, `matrix_exp_pade.hpp`, `MatrixExponential.h`), Al-Mohy–Higham exponential action (`matrix_exp_action_handler.hpp`), and SUNDIALS `ode_bdf` / ARKODE `ode_rk45` wrappers (`stan/math/rev/functor/ode_bdf.hpp`, `stan/math/prim/functor/ode_rk45.hpp`).
- **Relationship Between Subjects:** `Torsten` builds directly atop `stan-dev/math` (invoking `stan::math::matrix_exp` and SUNDIALS `CVODES`/forward-sensitivity machinery) and is compared orthogonally against `mrgsolve` (C++/R simulation engine used in pharmacometric trial design) and `PKPDsim` (point-of-care hospital TDM dosing engine). Published clinical papers and `IEC 60601-2-24` supply normative clinical/safety requirements against which solver invariants are evaluated.
- **Scope Qualification (Observation vs. Execution):** Source-level algorithms, guards, defaults, and bugs are verified directly in the pinned upstream trees (`Basis: source`). Numerical accuracy, non-negativity, degeneracy `NaN` counts, RK4 blowup thresholds, and closed-loop EMG trajectories were measured in standalone Python 3.13 IEEE-754 double-precision micro-probes replicating the exact upstream formulas (`Basis: execution (standalone numerical probe)`), not by compiling Rcpp/CmdStan C++ binaries on this host; published C++/HMC benchmark claims are attributed explicitly to their primary papers (`Basis: documentation`).

## Findings

### 1. Three-Compartment Mammillary PK/PD Structure and Clinical Model Parameterizations

All three clinical propofol TCI models share a linear four-state mammillary system driven by piecewise-constant intravenous input rate $u(t) \ge 0$ (mg/min) plus Dirac bolus impulses $D_k \delta(t - t_k)$ into central compartment $A_1$:

$$\frac{d}{dt}\begin{pmatrix} A_1 \\ A_2 \\ A_3 \\ C_e \end{pmatrix} = \underbrace{\begin{pmatrix} -(k_{10}+k_{12}+k_{13}) & k_{21} & k_{31} & 0 \\ k_{12} & -k_{21} & 0 & 0 \\ k_{13} & 0 & -k_{31} & 0 \\ k_{e0}/V_1 & 0 & 0 & -k_{e0} \end{pmatrix}}_{K \in \mathbb{R}^{4 \times 4}} \begin{pmatrix} A_1 \\ A_2 \\ A_3 \\ C_e \end{pmatrix} + \begin{pmatrix} u(t) \\ 0 \\ 0 \\ 0 \end{pmatrix}$$

where $k_{10} = \mathrm{CL}/V_1$, $k_{12} = Q_2/V_1$, $k_{21} = Q_2/V_2$, $k_{13} = Q_3/V_1$, $k_{31} = Q_3/V_3$, and plasma concentration is $C_1(t) = A_1(t)/V_1$. Because $K$ is a **Metzler matrix** ($K_{ij} \ge 0$ for all $i \ne j$) with column sums $\sum_{i=1}^3 K_{ij} \le 0$ (strictly $-k_{10} < 0$ for column 1, zero for columns 2 and 3), the continuous-time semigroup $e^{t K}$ is entrywise non-negative for all $t \ge 0$ and satisfies the exact compartmental mass conservation law:

$$A_1(t) + A_2(t) + A_3(t) + \underbrace{\int_0^t k_{10} A_1(\tau)\,d\tau}_{A_{\text{elim}}(t)} = A_1(0) + A_2(0) + A_3(0) + \int_0^t u(\tau)\,d\tau + \sum_{t_k \le t} D_k$$

Basis: normative (Schnider 1998, Eleveld 2018) + derived.

#### 1.1 Exact Parameterizations: Marsh (1991), Schnider (1998), and Eleveld (2018)

| Model | Cohort Scope | $V_1$ (L) | $V_2$ (L) | $V_3$ (L) | $\mathrm{CL}$ (L/min) | $Q_2, Q_3$ (L/min) | $k_{e0}$ ($\text{min}^{-1}$) & PD |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Marsh (1991)** (Diprifusor) | Non-obese adults | $0.228\,W$ | $0.464\,W$ ($k_{12}/k_{21} V_1$) | $2.895\,W$ ($k_{13}/k_{31} V_1$) | $0.02713\,W$ ($k_{10}=0.119$) | $k_{12}=0.112, k_{21}=0.055$, $k_{13}=0.0419, k_{31}=0.0033$ | $0.26$ (Diprifusor) or $1.21$ (modified Marsh); no age/sex/BMI terms |
| **Schnider (1998)** | 24 healthy adult volunteers (25–81 yr) | $4.27$ (fixed) | $18.9 - 0.391(\text{Age}-53)$ | $238$ (fixed) | $1.89 + 0.0456(W-77) - 0.0681(\mathrm{LBM}-59) + 0.0264(H-177)$ | $Q_2 = 1.29 - 0.024(\text{Age}-53)$, $Q_3 = 0.836$ | $k_{e0} = 0.456$ (fixed, $\mathrm{TTPE} \approx 1.6\text{ min}$, canonical univariate EEG) |
| **Eleveld (2018)** | 1,033 subjects (27 wk PMA–88 yr; $0.68\text{--}160\text{ kg}$) | $6.28 \frac{f_c(W)}{f_c(70)}$, $f_c(x)=\frac{x}{x+33.6}$ | $25.5 \frac{W}{70} e^{-0.0156(\text{Age}-35)}$ | $273 \frac{\mathrm{FFM}}{\mathrm{FFM}_{\text{ref}}} f_{\text{op}}(-0.0138)$ | $\theta_{\text{sex}} (\frac{W}{70})^{0.75} \frac{f_{\text{CLmat}}(\text{PMA})}{f_{\text{CLmat,ref}}} f_{\text{op}}(-0.00286)$ ($\theta_M=1.79, \theta_F=2.10$) | $Q_2 = 1.75 (\frac{V_2}{25.5})^{0.75}(1 + 1.30(1-f_{Q3\text{mat}}))$; $Q_3 = 1.11(\frac{V_3}{273})^{0.75} \frac{f_{Q3\text{mat}}}{f_{Q3\text{mat,ref}}}$ | $k_{e0,\text{art}} = 0.146 (W/70)^{-0.25}$; $C_{e50} = 3.08 e^{-0.00635(\text{Age}-35)}$; $\mathrm{BIS}_{\text{delay}} = 15 + e^{0.0517 \cdot \text{Age}}\text{ s}$ |

*Source note on Eleveld (2018) internal notation discrepancy (`Basis: normative`, Eleveld et al. BJA 120(5):948,952):* Eleveld's text equations on p. 948 write $\gamma = \theta_4$ for $C_e \le C_{e50}$ and $\gamma = \theta_9$ for $C_e > C_{e50}$, whereas Table 3 on p. 952 labels $\theta_4 = 1.47$ as `PD sigmoid slope (Ce>Ce50)` and $\theta_9 = 1.89$ as `PD sigmoid slope (Ce<Ce50)`. Additionally, a post-publication corrigendum noted that the reference individual's $Q_2$ evaluates to $1.83\text{ L/min}$ (rather than the abstract's $1.75\text{ L/min}$) due to $(1 + 1.30(1 - f_{Q3\text{mat}}(\text{PMA}_{\text{ref}}))) \approx 1.046$. Implementations must verify which side of $C_{e50}$ binds $\gamma = 1.89$ vs. $1.47$ against the published supplementary NONMEM control stream rather than blindly transcribing the body text.

Basis: normative (Schnider 1998, Eleveld 2018 full-text PDF Table 2 & Table 3) + documentation (Marsh 1991).

### 2. Anthropometric Covariate Monotonicity Breakdowns and Domain Boundaries

#### 2.1 Exact Breakdown of the Quadratic James LBM Equation

The James (1976) lean-body-mass equations embedded in Schnider (1998) and Minto (1997) remifentanil TCI pumps are concave quadratics in total body weight $W$ (kg) at fixed height $H$ (cm):

$$\mathrm{LBM}_M(W, H) = 1.10\,W - 128\left(\frac{W}{H}\right)^2, \qquad \mathrm{LBM}_F(W, H) = 1.07\,W - 148\left(\frac{W}{H}\right)^2$$

Differentiating with respect to $W$ yields exact BMI-invariant critical points independent of height:

$$\frac{\partial \mathrm{LBM}}{\partial W} = a - \frac{2b W}{H^2} = 0 \implies \mathrm{BMI}_{\text{peak}} = \frac{a}{2b}\times 10^4, \qquad \mathrm{LBM} = 0 \implies \mathrm{BMI}_{\text{zero}} = \frac{a}{b}\times 10^4$$

- **Males ($a=1.10, b=128$):** $\mathrm{BMI}_{\text{peak}} = \mathbf{42.97\text{ kg/m}^2}$ ($W_{\text{peak}} = 124.18\text{ kg}$ at $170\text{ cm}$, $\mathrm{LBM}_{\max} = 68.30\text{ kg}$); $\mathrm{BMI}_{\text{zero}} = \mathbf{85.94\text{ kg/m}^2}$ ($W_{\text{zero}} = 248.36\text{ kg}$ at $170\text{ cm}$).
- **Females ($a=1.07, b=148$):** $\mathrm{BMI}_{\text{peak}} = \mathbf{36.15\text{ kg/m}^2}$ ($W_{\text{peak}} = 92.54\text{ kg}$ at $160\text{ cm}$, $104.47\text{ kg}$ at $170\text{ cm}$); $\mathrm{BMI}_{\text{zero}} = \mathbf{72.30\text{ kg/m}^2}$ ($W_{\text{zero}} = 185.08\text{ kg}$ at $160\text{ cm}$).

Because Schnider's clearance $\mathrm{CL}_1$ carries a **negative** coefficient on $\mathrm{LBM}$ ($-0.0681$) alongside a positive coefficient on $W$ ($+0.0456$), substituting $\mathrm{LBM}_{\text{James}}$ yields a strictly convex quadratic in $W$:

$$\mathrm{CL}_{1,\text{Schnider}}(W, H) = \text{const}(H) + (0.0456 - 0.0681\,a)\,W + 0.0681\,b\left(\frac{W}{H}\right)^2$$

Above $\mathrm{BMI}_{\text{peak}}$, decreasing (and eventually negative) $\mathrm{LBM}$ flips from dampening $\mathrm{CL}_1$ to *amplifying* it quadratically. Simultaneously, because $V_1 = 4.27\text{ L}$ is constant, $k_{10} = \mathrm{CL}_1 / 4.27$ explodes—instructing a TCI pump to deliver lethal maintenance propofol rates to maintain a target plasma or effect-site concentration. Commercial TCI pumps (e.g., Orchestra Base Primea, Alaris PK) therefore impose ad-hoc hard BMI clamps ($\mathrm{BMI} \le 42\text{ kg/m}^2$ male, $\le 35\text{ kg/m}^2$ female) or prohibit Schnider above fixed weight thresholds.

In stark contrast, Eleveld (2018) adopts the **Al-Sallami et al. (2015)** fat-free mass equation (Janmahasatian hyperbolic adult FFM multiplied by a Hill age-maturation factor):

$$\mathrm{FFM}_M = \left(0.88 + \frac{0.12}{1 + (\text{Age}/13.4)^{-12.7}}\right)\frac{9270\,W}{6680 + 216\,\mathrm{BMI}}, \qquad \mathrm{FFM}_F = \left(1.11 - \frac{0.11}{1 + (\text{Age}/7.1)^{-1.1}}\right)\frac{9270\,W}{8780 + 244\,\mathrm{BMI}}$$

Because $\frac{\partial}{\partial W}\left(\frac{9270\,W}{b_0 + c_0 W/H_m^2}\right) = \frac{9270\,b_0}{(b_0 + c_0 W/H_m^2)^2} > 0$ for all $W > 0, H_m > 0$, Al-Sallami FFM is **globally strictly positive and strictly monotonically increasing in $W$**, saturating smoothly to $42.92 H_m^2\text{ kg}$ (adult male) and $37.99 H_m^2\text{ kg}$ (adult female) as $W \to \infty$.

#### 2.2 Cohort Verification Table (Standalone Numerical Probe)

Basis: execution (standalone Python double-precision probe of published Marsh, Schnider, and Eleveld equations).

| Patient Cohort | $W$ (kg) / $H$ (cm) / Age / Sex | BMI | James LBM (kg) | Al-Sallami FFM (kg) | Schnider $\mathrm{CL}_1$ (L/min) | Schnider $k_{10}$ ($\text{min}^{-1}$) | Schnider $V_2$ (L) | Eleveld $V_1$ (L) | Eleveld $\mathrm{CL}$ (L/min) | Eleveld $k_{10}$ ($\text{min}^{-1}$) | Eleveld $C_{e50}$ ($\mu$g/mL) | Eleveld $\mathrm{BIS}_{\text{delay}}$ (s) | Marsh $V_1$ (L) / $\mathrm{CL}$ (L/min) |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Child 5 yr M | 18 / 109 / 5 / M | 15.2 | 16.3 | 14.8 | 0.31 | 0.073 | 37.67 | 3.24 | 0.65 | 0.199 | 3.73 | 16.3 | 4.10 / 0.49 |
| Reference Adult M | 70 / 170 / 35 / M | 24.2 | 55.3 | 54.5 | 1.64 | 0.384 | 25.94 | 6.28 | 1.79 | 0.285 | 3.08 | 21.1 | 15.96 / 1.90 |
| Reference Adult F | 60 / 165 / 35 / F | 22.0 | 44.6 | 39.9 | 1.78 | 0.416 | 25.94 | 5.96 | 1.87 | 0.314 | 3.08 | 21.1 | 13.68 / 1.63 |
| Elderly 80 yr M | 70 / 170 / 80 / M | 24.2 | 55.3 | 54.5 | 1.64 | 0.384 | 8.34 | 6.28 | 1.79 | 0.285 | 2.31 | **77.6** | 15.96 / 1.90 |
| Centenarian 102 yr F | 60 / 165 / 102 / F | 22.0 | 44.6 | 39.5 | 1.78 | 0.416 | **-0.26** | 5.96 | 1.87 | 0.314 | 2.01 | **210.1** | 13.68 / 1.63 |
| Obese BMI 40 M | 115.6 / 170 / 35 / M | 40.0 | 68.0 | 69.9 | 2.85 | 0.668 | 25.94 | 7.20 | 2.61 | 0.362 | 3.08 | 21.1 | 26.36 / 3.14 |
| Obese BMI 45 F | 122.5 / 165 / 35 / F | 45.0 | 49.5 | 58.4 | 4.30 | 1.006 | 25.94 | 7.29 | 3.20 | 0.438 | 3.08 | 21.1 | 27.93 / 3.32 |
| Super-Obese 180 kg F | 180 / 165 / 35 / F | 66.1 | **16.5** | 68.1 | **9.17** | **2.147** | 25.94 | 7.83 | 4.26 | 0.544 | 3.08 | 21.1 | 41.04 / 4.88 |
| Extreme 250 kg M | 250 / 170 / 35 / M | 86.5 | **-1.8** | 91.4 | **13.74** | **3.217** | 25.94 | 8.19 | 4.65 | 0.568 | 3.08 | 21.1 | 57.00 / 6.78 |
| Extreme 250 kg F | 250 / 165 / 35 / F | 91.8 | **-72.3** | 75.5 | **18.40** | **4.309** | 25.94 | 8.19 | 5.46 | 0.666 | 3.08 | 21.1 | 57.00 / 6.78 |

**Secondary Elderly Domain Collapse in Schnider:** Beyond obesity, Schnider's linear age reductions violate compartmental positivity at the upper age tail: $V_2 = 18.9 - 0.391(\text{Age} - 53) \le 0$ for $\text{Age} \ge \mathbf{101.34\text{ yr}}$ ($-0.26\text{ L}$ at $102\text{ yr}$), and $\mathrm{CL}_2 = 1.29 - 0.024(\text{Age} - 53) \le 0$ for $\text{Age} \ge \mathbf{106.75\text{ yr}}$. Passing $V_2 \le 0$ directly into `mrgsolve`'s `advan11` triggers an immediate runtime abort (`src/odeproblem.cpp:609`: `if(MRGSOLVE_GET_PRED_VP <= 0) Rcpp::stop("pred_VP has a 0 or negative value.")`), whereas passing $V_2 < 0$ into an unchecked ODE solver flips $k_{21} = Q_2/V_2 < 0$, causing exponential divergence. Conversely, Marsh's pure linear weight scaling inflates central volume $V_1$ to $57.0\text{ L}$ at $250\text{ kg}$ ($6.96\times$ Eleveld's $8.19\text{ L}$), causing massive induction bolus overdoses in obese patients unless clinicians manually substitute an adjusted body weight (e.g., Servin $\mathrm{IBW} + 0.4(W - \mathrm{IBW})$).

### 3. Pharmacometric ODE Solvers, Matrix Exponentials, and Event Discontinuities

#### 3.1 Architecture Comparison Across `mrgsolve`, `Torsten`, `PKPDsim`, and `stan-dev/math`

Basis: source (`mrgsolve@c529f2decd8d5b48b11760126d68d883547932b0`, `Torsten@16a954822cf794648d2e0535aa0d877b295e90b1`, `PKPDsim@b5b81157c1550d2ae429aa46b59dc678f5670878`, `stan-dev/math@3d16e8f14e620e2cd35cc59bf92766ad98a9559b`).

| Dimension | `mrgsolve` | `Torsten` (atop `stan-dev/math`) | `PKPDsim` | `stan-dev/math` (primitives) |
| :--- | :--- | :--- | :--- | :--- |
| **Linear 3-Cmt Solver** | Closed-form trigonometric cubic eigenvalues + `PolyExp` (`advan11`/`12`, `src/odeproblem.cpp:603-809`) | `PMXLinODEModel::solve` via `stan::math::matrix_exp` + `mdivide_left` (`pmx_linode_model.hpp:131-161`); optional `PMXLinOdeEigenDecompModel` (`:275-318`) | Analytical cubic C++ (`src/pk_3cmt_iv_infusion.cpp:6-114`, `pk_3cmt_iv_bolus.cpp`) | `matrix_exp` (`matrix_exp.hpp:25-43`): 2×2 closed-form when real distinct eigenvalues, else Higham (2005) Padé `[3/3..13/13]` (`MatrixExponential.h:187-212`); Al-Mohy–Higham action (`matrix_exp_action_handler.hpp`) |
| **General / Nonlinear ODE Solver** | `ODEPACK` `LSODA` (`ADVAN 13`, auto Adams/BDF stiffness switching, default `rtol=1e-8`, `atol=1e-8`, `maxsteps=20000`, `R/class_mrgmod.R:120-126`) | SUNDIALS `CVODES` (`CV_BDF` / `CV_ADAMS`, forward sensitivities `CVodeSensReInit`, `dsolve/pmx_cvodes_integrator.hpp:17-99`), Boost `odeint` RK45, `ARKODE` | **Fixed-step explicit Boost.Odeint `runge_kutta4`** (`inst/cpp/sim.cpp:2,39`, default `int_step_size=0.01`, `R/sim.R:108`) | `ode_bdf` (CVODES `CV_BDF`, defaults `rtol=1e-10`, `atol=1e-10`, `max_num_steps=1e8`, `rev/functor/ode_bdf.hpp:152-154`); `ode_rk45` (ARKODE Dormand-Prince 7(4,5), defaults `1e-6`, `1e6`, `prim/functor/ode_rk45.hpp:164-166`) |
| **Event Splitting & Discontinuity Restart** | Priority-sorted deque (`src/devtran.cpp:530-668`); inserts phantom `EVID=9` infusion-off record at $t + \text{dur}$ (`:629-643`); calls `prob.lsoda_init()` (`Istate=1`) on state/parameter discontinuities | `EventHistory::generate_rates` inserts `EVID=9` at $t + \mathrm{amt}/\mathrm{rate}$ (`ev_history.hpp:630-646`); rebuilds exact total rate per unique interval $(t_k, t_{k+1}]$ (`:661-671`) | R-side design pre-splits infusion start/stop (`dummy==1`) and passes piecewise intervals to `sim_cpp` (`inst/cpp/sim.cpp:212-243`); `new_regimen.R:133-136` clamps zero-length non-bolus infusions to $t_{\text{inf}} = 1/60$ | Caller-managed piecewise integration; no built-in clinical event table |
| **Concurrent Infusion Superposition** | Reference-counted accumulator `R0[pos] += value` (`rate_add`), `R0[pos] -= value` (`rate_rm`, clamps `<0` to `0`, `odeproblem.cpp:348-367`); does **not** force `R0=0` when `infusion_count==0` if residual `+1e-16` remains | Re-sums active rates from scratch per unique time interval ($O(N_{\text{ev}}^2)$, `ev_history.hpp:661-670`); immune to floating-point subtraction drift | Running additive sum `rate[c] = rate[c] + rates[i] * bioav[c]` (`inst/cpp/sim.cpp:226`); no counter, no zero-clamp; time-varying `bioav` leaks permanent nonzero phantom rate | N/A |
| **Bioavailability $F$ on Infusions** | **Duration scaling (NONMEM):** `datarecord::dur()` returns `Fn * Amt / Rate` (`src/datarecord.cpp:140-142`); rate stays unscaled (`:168`) | **Rate scaling:** `ev_history.hpp:639` sets duration `amt/rate` unscaled by $F$; `ev_manager.hpp:237` scales rate by `params.bioavailability(i, j)` | **Rate scaling:** `inst/cpp/sim.cpp:226` multiplies `rates[i] * bioav[c]` while holding `t_inf` fixed | N/A |

#### 3.2 Directly Verified Upstream Source Bugs and Numerical Edge Cases

1. **Closed-Form Cubic Degeneracy `NaN`s in `mrgsolve` and `PKPDsim` (`Basis: source + execution (standalone probe)`):**
   - In `mrgsolve` `src/odeproblem.cpp:611-612, 637-649`, `advan11` accepts `Q >= 0` and `Q2 >= 0` (rejecting only strictly negative values) and computes:
     ```cpp
     double sq = sqrt(-aa / 3.0);
     double theta = acos(bb / (2.0 * sq * sq * sq)) / 3.0;
     ```
     Because the `acos` argument is never clamped to `[-1.0, 1.0]`, evaluating the legitimate 1-compartment boundary ($Q = Q_2 = 0$, $k_{10} \in \{0.0137 \cdot n\}_{n=1}^{199}$) produced `arg = 1.0000000000000002` ($1 + 1\text{ ULP}$) and **`NaN` on 49 of 199 (24.6%) tested values** (first hit at $k_{10} = 0.0959$). Moreover, unlike `advan2` (which guards `std::fabs(ka - k10) < 2.22e-14` at line 434), `advan4` and `advan11` omit coalescent-eigenvalue guards on `d0, d1, d2` (`:647-649`) and `(ka - alpha[i])` (`:672-674`), and on `Q = Q2 = 0` floating-point roots drift to $\alpha_{1,2} \approx \pm 9.93 \times 10^{-10}$, inducing spurious exponential growth $e^{+9.93\times 10^{-10} t}$ or $0/0$ division in `PolyExp` (`:861`).
   - In `PKPDsim` `src/pk_3cmt_iv_infusion.cpp:58-60`:
     ```cpp
     q = (pow(n,2.0))/4.0 + (pow(m,3.0))/27.0;
     alpha = sqrt(-1.0*q);
     ```
     On the same $Q = Q_2 = 0$ sweep, IEEE-754 rounding yielded $q = +3.97 \times 10^{-23} > 0$, triggering `sqrt(-q) = NaN` on **71 of 199 (35.7%) tested values** (first hit at $k_{10} = 15 \times 0.0137 \approx 0.20550000000000002$; exact decimal literal hit at $k_{10} = 0.3151$, $q = +2.12 \times 10^{-22}$). Separately, lines 32–37 (`while(TIME[i] == 0) { ... i++; }`) lack an `i < A1.size()` bounds check, risking out-of-bounds access if all input times equal zero.
2. **Torsten `PMXLinODEModel::solve` Catastrophic Cancellation and Singular-$K$ Failure (`Basis: source + execution (standalone probe)`):**
   - `Torsten` (`pmx_linode_model.hpp:147-160`) propagates constant-rate linear ODEs via:
     ```cpp
     x = mdivide_left(par_, rate_vec);
     x2 = x + y;
     pred = matrix_exp(dt_system) * x2;
     pred -= x;
     ```
   - Testing an exact IEEE-754 replica of `stan-dev/math`'s `MatrixExponential.h` + `PMXLinODEModel::solve` on the obese Schnider 3-compartment matrix ($200\text{ kg}, 165\text{ cm}$ female, $y_0 = [0,0,0]$, $r = [20, 0, 0]\text{ mg/min}$) across $\Delta t \in [10^{-10}, 1]\text{ min}$ versus **Van Loan's augmented block matrix exponential** $\exp\left(\Delta t \begin{pmatrix} K & r \\ 0 & 0 \end{pmatrix}\right)\begin{pmatrix} y_0 \\ 1 \end{pmatrix}$:
     - At $\Delta t = 10^{-8}\text{ min}$, Torsten's `pred - x` cancels $y_2$ and $y_3$ completely to `0.0` (exact: $4.03 \times 10^{-16}, 1.96 \times 10^{-16}$).
     - At $\Delta t = 10^{-10}\text{ min}$, Torsten produces a **strictly negative peripheral mass** $y_2 = \mathbf{-7.105 \times 10^{-15}\text{ mg}}$ (Van Loan: $+4.033 \times 10^{-20}\text{ mg}$).
     - When $K$ is augmented with a cumulative elimination sink compartment ($dA_{\text{elim}}/dt = k_{10} A_1$, making $\det(K) = 0$), Torsten's `mdivide_left` **throws (`Singular matrix`)**, whereas Van Loan integrates all four states with exact mass balance $|A_1 + A_2 + A_3 + A_{\text{elim}} - 20.0| = \mathbf{0.00 \times 10^0}$.
   - **Honest Positivity Result for Padé `[3/3]`–`[13/13]` Itself:** Directly testing `stan-dev/math`'s Higham (2005) scaling-and-squaring Padé routine (`MatrixExponential.h:193-211`, thresholds $\theta_3 = 1.496\times 10^{-2}$, $\theta_5 = 0.2539$, $\theta_7 = 0.9504$, $\theta_9 = 2.098$, $\theta_{13} = 5.3719$) on stiff Metzler matrices across $\|\Delta t K\|_1 \in [0.0149, 5.37]$ and $\Delta t \in [0.1, 10000]\text{ min}$ (up to $s = 13$ squarings) yielded **zero negative matrix entries** (minimum entry $+5.26 \times 10^{-19}$ at $\Delta t = 10^4\text{ min}$) and relative error $8.5 \times 10^{-15}$ on $\exp(-5.36)$. Thus, for these Metzler matrices, negativity in Torsten originates from the affine $K^{-1} r$ subtraction rather than `matrix_exp_pade` itself.
3. **Fixed-Step Explicit RK4 Instability Under Stiff Kinetics in `PKPDsim` (`Basis: source + execution (standalone probe)`):**
   - `PKPDsim/inst/cpp/sim.cpp:2` fixes Boost.Odeint's classical explicit 4th-order Runge-Kutta (`runge_kutta4<state_type> stepr`), whose real-axis absolute stability interval is $[-2.7853, 0]$. For the obese Schnider female ($k_{10} = 2.678\text{ min}^{-1} = 160.7\text{ h}^{-1}$, dominant eigenvalue $\lambda_{\max} \approx -196.4\text{ h}^{-1}$), the stability ceiling in hour-based clinical models is $h_{\text{crit}} = 2.7853 / 196.4 = \mathbf{0.01418\text{ h}}$—only $1.42\times$ `PKPDsim`'s default `int_step_size = 0.01` (`R/sim.R:108`):
     - At $h = 0.010\text{ h}$: stable (`max_err = 9.62e-8 mg`, `min_y = 0.0`).
     - At $h = 0.015\text{ h}$ ($0.90\text{ min}$): **catastrophic oscillation to `min_y = -7.474e+05 mg`** (`max_err = 9.17e+05 mg`) while global mass sum appears deceptively conserved (`mass_err = 1.16e-10`) due to opposing-sign blowup across compartments!
     - At $h = 0.020\text{ h}$: diverges past `-1.857e+12 mg`.
     - Implicit L-stable BDF-1 (Backward Euler) stayed strictly non-negative (`min_y = 0.0`, `mass_err <= 1.42e-13`) at all tested steps, with $O(h)$ truncation error ($0.066\text{--}0.324\text{ mg}$).
4. **Integer Truncation Bug in `PKPDsim` `apply_lagtime` (`Basis: source`):**
   - In `PKPDsim/inst/cpp/sim.cpp:92,111`:
     ```cpp
     std::vector<int> rate = as<std::vector<int> >(new_design["rate"]);
     ...
     if(evid[i] == 1 | (evid[i] == 2 & rate[i] != 0)) { times[i] += lagtime[cmt[i]-1]; }
     ```
     Casting floating-point `rate` to `std::vector<int>` truncates any fractional infusion rate ($0 < |\text{rate}| < 1$, e.g., $0.5\text{ mg/min}$ or $0.2\text{ mg/h}$) to `0`, preventing the infusion-stop record (`evid == 2`) from shifting by `lagtime` while the start record (`evid == 1`) shifts—silently shortening or inverting the infusion interval.
5. **Bioavailability $F < 1$ Infusion Divergence Across Engines (`Basis: source + execution (standalone probe)`):**
   - For a nominal $100\text{ mg}$ infusion at $10\text{ mg/min}$ ($10\text{ min}$) with $F = 0.6$ ($60\text{ mg}$ net) in the reference Eleveld adult: `mrgsolve` infuses at $10\text{ mg/min}$ for $6\text{ min}$ ($C_{\max} = \mathbf{2.2785\text{ }\mu\text{g/mL}}$ at $t = 6\text{ min}$, dropping to $0.3809\text{ }\mu\text{g/mL}$ at $t = 10\text{ min}$), whereas `Torsten` and `PKPDsim` infuse at $6\text{ mg/min}$ for $10\text{ min}$ ($C_{\max} = \mathbf{1.4914\text{ }\mu\text{g/mL}}$ at $t = 10\text{ min}$)—a **$+52.8\%$ peak concentration discrepancy** on identical input tables.

### 4. Closed-Loop BIS Electromyographic Spoofing, Sensor Lag, and Safety Interlocks

Processed EEG depth-of-anesthesia monitors such as the Bispectral Index (BIS, $0\text{--}100$, target $40\text{--}60$ for general anesthesia) blend time-domain burst-suppression ratio, bispectral phase coupling (`SynchFastSlow`), and high-frequency spectral power ratios (`BetaRatio`, $\log(P_{30\text{--}47\text{ Hz}} / P_{11\text{--}20\text{ Hz}})$). Because frontalis muscle electromyography spans $30\text{--}300\text{ Hz}$, its lower skirt overlaps the $30\text{--}47\text{ Hz}$ BIS band directly. Schuller et al. (2015, `DOI: 10.1093/bja/aev072`) demonstrated in fully awake, unanesthetized volunteers receiving isolated-forearm neuromuscular blockade (suxamethonium/rocuronium) that abolishing EMG caused BIS to fall as low as $44\text{--}47$ despite complete consciousness; symmetrically, Messner et al. (2003) and Dahaba (2005) established that frontalis EMG power ($> 30\text{ dB}$) or monopolar electrocautery falsely elevates BIS from $\sim 45$ into the $65\text{--}85$ "awake" range in deeply anesthetized patients.

Compounding EMG spoofing is pure sensor transport delay: Eleveld (2018) models $\mathrm{BIS}_{\text{delay}}(\text{Age}) = 15 + e^{0.0517 \cdot \text{Age}}\text{ s}$, growing from $21.1\text{ s}$ at age $35$ to $77.6\text{ s}$ at age $80$ (and $109.6\text{ s}$ at age $88$). In a closed-loop TCI controller, a $+30$ BIS EMG artifact lasting $5\text{ min}$ drives integral windup and infusion escalation (`Basis: execution (standalone toy PID-TCI probe on Eleveld reference adult; not a commercial closed-loop pump)`):

| Closed-Loop Controller Configuration (Toy Probe) | Peak $C_e$ ($\mu$g/mL) | Nadir True BIS | Excess Propofol Delivered (mg) | Failure Mechanism |
| :--- | ---: | ---: | ---: | :--- |
| Unprotected PID ($K_p=0.35, K_i=0.15$) | 5.38 | 28.5 | +127.9 | Integral windup on $+30$ EMG offset drives deep hypnotic overdose |
| Hard $C_e \le 4.5\text{ }\mu$g/mL cutoff only | 4.71 | 32.4 | +84.6 | Plasma-to-brain ($A_1 \to C_e$) inertia overshoots ceiling by $+0.21\text{ }\mu$g/mL after pump halt |
| Active EMG ($> 30\text{ dB}$) / SQI ($< 50$) freeze gate + $C_e$ cap | 3.08 | 46.5 | 0.0 | Freezes integrator and holds baseline TCI rate during artifact window |

Under `IEC 60601-2-24` (basic safety and essential performance of infusion pumps), TCI delivery hardware must additionally bound short-term mechanical delivery jitter via **trumpet curves** (maximum/minimum percentage flow error across observation windows $p = 2, 5, 11, 19, 31\text{ min}$), detect downstream line occlusions within prescribed pressure/time ceilings, and suppress post-occlusion pressure-windup boluses—each of which introduces physical discontinuities between commanded TCI rate $u_{\text{cmd}}(t)$ and delivered venous rate $u_{\text{actual}}(t)$.

### 5. Multi-Level Performance and Resource Footprint (`L1`–`L6`)

Basis: source (source-tree measurements of pinned archives) + documentation (Margossian et al. 2022, Eleveld 2018, Stan/Torsten/mrgsolve documentation) + derived.

| Level | Metric Dimension | `mrgsolve` (`ADVAN 11` / `LSODA`) | `Torsten` + `stan-dev/math` (`pmx_solve_linode` / `ode_bdf`) | `PKPDsim` (`pk_3cmt` / `sim.cpp` RK4) | Embedded TCI Pump Firmware (Clinical Target) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **L1 (Authoring & Maintenance)** | Model LoC, covariate spec effort, proof/audit expansion | 20–60 LoC `$PKMODEL`/`$ODE` DSL; high clinician readability; covariate errors require manual `$MAIN` guards | 60–150 LoC Stan model + event-table prep; high Bayesian workflow iteration cost for priors/HMC diagnostics (Margossian 2022) | 30–80 LoC JSON5/R model templates (`inst/models/` holds 40+ hospital TDM models); low barrier for pharmacists | Strict IEC 62304 Class C / IEC 60601-2-24 traceability; 5–15× verification-to-code effort for static bounds & FMEA |
| **L2 (Toolchain & Build Time)** | From-scratch & incremental build footprint | `src/` 12 C++ files (`7,820` LoC, `236.7 KiB`) + `inst/base/` (`800` LoC); compiles model shared object in ~2–8 s via Rcpp/g++ | `torsten/` 156 headers (`28,959` LoC, `1.11 MiB`) atop `stan-dev/math` (`29 MiB`) & CmdStan (`164 MiB` archive); full C++ template compile 30–180 s, 2–6 GB RAM | `src/` 11 C++ files (`896` LoC, `30.6 KiB`) + `inst/cpp/` (`299` LoC); model compile ~2–6 s via Rcpp/Boost headers | Cross-compiled static C/Rust firmware (< 5 s build, zero dynamic codegen) |
| **L3 (Elaboration / Inference Latency)** | Per-evaluation & posterior sampling latency | Closed-form `advan11`: $O(N_{\text{ev}})$ ~µs/patient; `LSODA`: adaptive Jacobian + step retries across discontinuities | `pmx_solve_linode` (`matrix_exp` + `var` reverse-mode autodiff) delivers order-of-magnitude HMC speedups over `pmx_solve_bdf`/`rk45` (Margossian 2022); `CVODES` defaults `max_num_steps=500` in Torsten (`pmx_cvodes_integrator.hpp:19`) vs `1e8` in `stan-dev/math` (`ode_bdf.hpp:154`) | Analytical `pk_3cmt`: ~µs/patient; fixed-step `RK4` scales strictly as $O(T / h)$ with 4 RHS evals/step | Real-time control tick $\Delta t = 1\text{--}10\text{ s}$; analytical/Van Loan 4×4 step takes < 50 µs on Cortex-M4F (FPU) |
| **L4 (Generated Code Execution)** | Throughput, cache/SIMD, tail latency | Compiled native C++ shared library; zero R-callback overhead inside `DEVTRAN` inner loop (`src/devtran.cpp`) | Native C++ with Eigen vectorization; reverse-mode autodiff tape (`stan::math::var`) dominates memory bandwidth during `matrix_exp` squarings and sensitivity ODEs | Compiled Rcpp C++; no adaptive step rejection, deterministic WCET per step, but catastrophic stability failure if $|\lambda| h > 2.785$ | Deterministic WCET (< 1 ms/tick) mandatory under IEC 60601-2-24; floating-point exception traps required |
| **L5 (Verification / Certificate Checking)** | Runtime / SMT invariant check speed | No built-in positivity or monotonicity verifier; external Z3/interval check over covariate formulas completes in < 10 ms | Parameter checks (`pmx_check.hpp`) run $O(N_{\text{ev}})$ in µs; no formal mass-conservation or non-negativity certificate | Minimal runtime input validation; no ODE stability or mass-balance assertions | Online runtime monitor checking $V_i > 0, \mathrm{CL}_i > 0$, mass balance $|\Delta M| < \epsilon$, and $C_e$ rate bounds in < 10 µs/tick |
| **L6 (RAM, Disk & Binary Footprint)** | Source/binary/runtime memory & power | Package archive `832 KiB`; R session + compiled model `.so` typically 50–200 MB RSS | Source tarball `164 MiB`; compiled CmdStan binary + autodiff arena scales from 100 MB to multi-GB RAM for large hierarchical cohorts | Package archive `232 KiB`; lightweight point-of-care RSS (tens of MB) | Embedded MCU target: < 256 KiB Flash, < 64 KiB SRAM, < 1 W battery-backed infusion pump |

### 6. Human Comprehensibility and Conceptual Simplicity / Model Refinement (`C1`–`C2`)

#### 6.1 Human Comprehensibility & Mental-Model Ergonomics (`C1`)

- **Empirical Polynomials vs. Mechanistic Priors:** Clinicians naturally expect physiological monotonicity ("a heavier patient does not have *negative* lean tissue or $4\times$ higher metabolic clearance per liter of blood"). Schnider's quadratic James LBM + negative `-0.0681 * LBM` clearance term violates this mental model non-locally: the sign inversion only manifests when two coupled formulas interact above $\mathrm{BMI} > 36.15$ (female) or $42.97$ (male), making visual inspection of either formula in isolation deceptive. By contrast, Eleveld's 18 PK + 9 PD parameters increase surface formula count (higher *syntactic* working-memory load), yet every factor is factored into a positive multiplicative dimension (saturating central volume, allometric $W^{0.75}$, Hill maturation, exponential aging), restoring local sign auditability.
- **Hidden Event-Table Semantics (`F`, `ALAG`, `SS`, `EVID`):** Across `mrgsolve`, `Torsten`, and `PKPDsim`, identical NONMEM-like column names (`AMT`, `RATE`, `EVID`, `F`, `ALAG`) conceal divergent operational semantics—most starkly bioavailability scaling *duration* (`mrgsolve`) vs. *rate* (`Torsten`/`PKPDsim`), producing a $+52.8\%$ $C_{\max}$ divergence without any diagnostic warning. An automated agent or clinician porting a regimen table between engines cannot infer this difference from column schemas alone.
- **Opaque Error Diagnostics vs. Silent Corruption:** Silent failure modes (`PKPDsim`'s `std::vector<int>` lag-time rate truncation, `mrgsolve`'s unclamped `acos` `NaN` at $Q = Q_2 = 0$, or `PKPDsim`'s fixed-step RK4 sign-oscillating mass-conserving explosion) provide far worse human debuggability than explicit pre-condition aborts (`mrgsolve`'s `pred_VP <= 0` stop).

#### 6.2 Simplicity, Orthogonality & Universal Model Refinement (`C2`)

Three distinct solver mechanisms currently coexist across pharmacometric tools to propagate linear mammillary PK/PD systems: (1) ad-hoc trigonometric cubic eigenvalue formulas (`mrgsolve advan11`, `PKPDsim pk_3cmt`), (2) inhomogeneous `exp(dt*K)*(y + K^{-1}r) - K^{-1}r` (`Torsten`), and (3) generic numerical ODE stepping (`LSODA`, `CVODES`, `RK4`). Applying an Ousterhout deep-module and Felleisen macro-expressibility lens reveals a single unifying abstraction for **all** piecewise-constant linear compartmental PK/PD schedules:

- **Universal Primitive — Van Loan Augmented Block Exponential on Positive-Parametrized Covariates:**
  $$\begin{pmatrix} y(t_{k+1}) \\ 1 \end{pmatrix} = \exp\!\left(\Delta t \begin{pmatrix} K(\theta) & r_k \\ 0 & 0 \end{pmatrix}\right) \begin{pmatrix} y(t_k) + D_k e_{c_k} \\ 1 \end{pmatrix}$$
  1. **Eliminates special cases without shifting complexity:** Handles 1-, 2-, 3-, and $n$-compartment models, coalescent eigenvalues ($Q = 0$, $k_{21} = k_{31}$, $k_a = \alpha_i$), singular elimination/AUC sink compartments ($\det K = 0$), zero-duration boluses ($D_k$), zero-order infusions ($r_k$), concurrent overlapping infusions (via interval-rebuilt exact sums as in `Torsten`), and effect-site $C_e$ coupling in **one** singularity-free operator—removing trigonometric `acos`/`sqrt` branch cuts and `K^{-1}` cancellation completely.
  2. **Orthogonal Separation of Event Normalization from State Propagation:** Representing every infusion canonically as an explicit tuple `(t_start, t_end, rate_net)` *before* integration decouples NONMEM duration-vs-rate bioavailability policy from the numerical propagator and eliminates floating-point rate-accumulator drift.
  3. **Positive-Cone Covariate Grammar:** Restricting clinical covariate models to compositions of positive-preserving monotone primitives ($\exp$, power laws $W^\alpha$, Hill sigmoids $x^n/(x^n + E_{50}^n)$, positive rational asymptotes like Al-Sallami FFM) makes strict positivity ($V_i > 0, \mathrm{CL}_i > 0$) and bounded asymptotic scaling structural invariants rather than post-hoc BMI clamp patches.

### 7. End-to-End Solution & Implementation Validation (`V1`–`V4`)

Formal proofs or unit tests over idealized ODEs are insufficient to guarantee clinical safety across covariate extrapolation, solver lowering, infusion hardware mechanics, and human/sensor reality gaps. End-to-end validation requires all four tiers:

- **`V1` (Specification Adequacy, Non-Vacuity & Property-Based Testing):**
  - Encode clinical domain contracts as executable SMT/interval properties and QuickCheck/Hypothesis generators over the full human physiological envelope ($W \in [0.5, 300]\text{ kg}$, $H \in [40, 220]\text{ cm}$, $\text{Age} \in [0, 120]\text{ yr}$, $\text{Sex} \in \{M, F\}$): (a) strict positivity $V_i, \mathrm{CL}_i, Q_i, k_{e0} > 0$, (b) non-negative weight sensitivity $\partial \mathrm{FFM}/\partial W \ge 0$ and bounded clearance elasticity $\partial \ln \mathrm{CL} / \partial \ln W \in [0, 1]$, and (c) mutant-specification testing (injecting sign flips on $\theta_{10}$ or James LBM without clamps) verifying that the specification catches every known clinical overdose mode non-vacuously.
- **`V2` (Cross-Solver Differential & Adversarial Edge-Case Fuzzing):**
  - Run automated differential testing comparing `mrgsolve` (`ADVAN 11` vs `ADVAN 13 LSODA`), `Torsten` (`pmx_solve_linode` vs `pmx_solve_bdf`), `PKPDsim` (`pk_3cmt` vs `sim.cpp`), and a 128-bit/arbitrary-precision Van Loan oracle across adversarial regimens: degenerate $Q = 0$ / $k_{21} = k_{31}$, micro-steps $\Delta t \in [10^{-12}, 10^4]\text{ min}$, fractional rates $0 < \text{rate} < 1$ with `ALAG > 0`, simultaneous bolus + multi-infusion superposition, and $F \in (0, 1)$ cross-checks (catching every bug documented in §3.2 automatically).
- **`V3` (Hardware, Timing, Occlusion & Numerical Fault Injection):**
  - Validate embedded TCI controllers against `IEC 60601-2-24` physical-layer non-idealities: stepper-motor discretization & syringe-plunger compliance stiction (trumpet-curve flow error sweeps), simulated downstream line occlusion + sudden release post-occlusion boluses, real-time clock drift/pause recovery (ensuring the internal PK state continues decaying during pump occlusion rather than freezing $t$), and IEEE-754 floating-point exception/rounding-mode fuzzing (subnormals, `FE_INVALID` trap checks).
- **`V4` (Plant Falsification, Clinical Waveform Replay & Clinician Mental-Model Testing):**
  - **STL Falsification & Real Waveform Replay:** Replay real perioperative EEG/BIS + EMG + electrocautery clinical recordings (e.g., VitalDB / OpenTCI datasets and Schuller 2015 neuromuscular-blockade paradigms) through closed-loop TCI controllers using Signal Temporal Logic (STL) robustness falsification over safety specs ($\Box_{[t_{\text{ind}}, T]}(\text{true\_BIS} \ge 30 \wedge C_e \le C_{e,\max})$) and runtime `ModelPlex`-style model-validity monitors comparing predicted vs. measured BIS residuals to trigger open-loop fallback when $|\mathrm{BIS}_{\text{meas}} - \mathrm{BIS}_{\text{pred}}|$ diverges concurrently with $\mathrm{EMG} > 30\text{ dB}$ or $\mathrm{SQI} < 50$.
  - **Human Comprehension Validation:** Empirically litmus-test anesthesiologists' mental models on edge-case TCI displays (e.g., whether clinicians recognize when a pump silently clamps BMI in Schnider mode, or distinguish plasma-target vs. effect-site-target induction boluses across Marsh, Schnider, and Eleveld).

## Boundaries

- **Compiled C++ Runtime Benchmarks (`not examined`):** Neither `mrgsolve`, `Torsten`/CmdStan, `PKPDsim`, nor `stan-dev/math` C++ binaries were compiled or executed on this host. All numerical probe numbers in §§2.2, 3.2, and 4 come from standalone Python 3.13 IEEE-754 double-precision replicas of the exact inspected upstream formulas and are explicitly labeled as such; relative C++/HMC runtime comparisons in §5 rely on published documentation (Margossian et al. 2022) and direct source-tree size measurements.
- **Proprietary Commercial TCI Pump Firmware (`unknown` / `not examined`):** Commercial infusion pump implementations (e.g., Fresenius Orchestra Base Primea, BD Alaris PK, B. Braun Space) are closed-source; exact vendor-specific BMI clamping policies, internal integration timesteps, and alarm thresholds beyond public `IEC 60601-2-24` and published clinical audits were not directly inspected.
- **Nonlinear / Saturable PK and Multi-Drug Synergy (`not examined`):** Propofol PK/PD interactions with remifentanil/fentanyl (response-surface Minto/Bouillon models beyond Eleveld's binary opioid covariate $f_{\text{opiates}}$) and saturable Michaelis–Menten kinetics (where matrix exponentials do not apply and `ode_bdf`/`LSODA` are strictly required) were outside scope.
- **Padé Non-Negativity for General Non-Metzler or Extreme-Norm Systems (`known not to apply` unconditionally):** Although `stan-dev/math`'s Higham (2005) Padé `[3/3]`–`[13/13]` routine stayed entrywise non-negative across all tested 3-compartment propofol Metzler matrices, diagonal Padé approximants $R_{m,m}(z)$ are *not* unconditionally positivity-preserving for arbitrary stiff matrices with large oscillatory/non-normal components or extreme scaling; positivity guarantees require verified interval enclosure or uniformization ($e^{\Delta t K} = e^{-\gamma \Delta t} \sum_{k=0}^\infty \frac{(\gamma \Delta t)^k}{k!} (I + K/\gamma)^k$, which is strictly non-negative term-by-term for $\gamma \ge \max_i |K_{ii}|$).
- **Eleveld (2018) Sedation Range Extrapolation (`unsupported` by training data):** As Eleveld et al. (2018, p. 950) explicitly caution, no studies targeting light MAC sedation were included in the PD training cohort, so BIS predictions near $C_{e10}$ ($\mathrm{BIS} \approx 84$) and beyond $W > 160\text{ kg}$ or $\text{Age} > 88\text{ yr}$ represent out-of-distribution extrapolations whose variance is clinically unvalidated even though the formulas remain mathematically smooth and positive.
- **Stan Autodiff Memory Overhead of Van Loan Augmentation (`unknown`):** Replacing Torsten's $n \times n$ `matrix_exp` + `mdivide_left` with an $(n+1) \times (n+1)$ Van Loan block exponential adds one row/column (e.g., $4 \times 4 \to 5 \times 5$) and avoids `mdivide_left` adjoints; exact Stan reverse-mode `var` tape memory and HMC ESS/s trade-offs were not benchmarked in compiled CmdStan.

## Evidence

- **Primary Upstream Source Inspection (`observed_at: 2026-11-19`):**
  - `metrumresearchgroup/mrgsolve` @ `c529f2decd8d5b48b11760126d68d883547932b0`:
    - `src/odeproblem.cpp:348-367` (`rate_add`, `rate_rm` accumulator without zero-reset on `infusion_count == 0`), `:415-437` (`advan2` `ka == k10` guard), `:603-809` (`advan11` cubic eigenvalues `acos(bb/(2*sq^3))` without clamping or coalescent denominator guard), `:818-922` (`PolyExp`).
    - `src/datarecord.cpp:140-142` (`dur() { return Fn*Amt/Rate; }`), `:148-174` (`implement()`).
    - `src/devtran.cpp:501-676` (`mindt`, `ALAG`, `EVID=9` infusion-off insertion, `prob.advance`).
    - `R/class_mrgmod.R:120-156` (defaults `atol=1e-8`, `rtol=1e-8`, `maxsteps=20000`, `advan=13`, `mindt=10*.Machine$double.eps`).
  - `metrumresearchgroup/Torsten` @ `16a954822cf794648d2e0535aa0d877b295e90b1`:
    - `cmdstan/stan/lib/stan_math/stan/math/torsten/pmx_linode_model.hpp:130-161` (`PMXLinODEModel::solve`, `mdivide_left(par_, rate_vec)` + `matrix_exp(dt_system) * (x + y) - x`), `:225-248` (steady-state truncated infusions), `:275-318` (`PMXLinOdeEigenDecompModel`).
    - `cmdstan/stan/lib/stan_math/stan/math/torsten/ev_history.hpp:571-574` (`is_bolus_dosing` `eps=1e-12`), `:630-682` (`generate_rates`: `gen_time += amt/rate` unscaled by $F$; interval rate re-summation).
    - `cmdstan/stan/lib/stan_math/stan/math/torsten/ev_manager.hpp:93-96, 232-240` (`fractioned_rates` multiplying rate by `params.bioavailability(i, j)`).
    - `cmdstan/stan/lib/stan_math/stan/math/torsten/dsolve/pmx_cvodes_integrator.hpp:17-99` (`CVODES_MAX_STEPS = 500`, `CVodeSensReInit`).
  - `InsightRX/PKPDsim` @ `b5b81157c1550d2ae429aa46b59dc678f5670878`:
    - `src/pk_3cmt_iv_infusion.cpp:31-37` (unbounded `while(TIME[i] == 0)`), `:40-104` (cubic discriminant `q`, unclamped `sqrt(-1.0*q)`, mass-balance AUC formula line 99).
    - `inst/cpp/sim.cpp:2` (`runge_kutta4<state_type> stepr`), `:25-43` (`sim_cpp`), `:92,111` (`std::vector<int> rate` truncation in `apply_lagtime`), `:225-227` (`rate[c] += rates[i] * bioav[c]`).
    - `R/sim.R:108` (`int_step_size = 0.01`), `R/new_regimen.R:133-136` (zero-length infusion floor `1/60`).
  - `stan-dev/math` @ `3d16e8f14e620e2cd35cc59bf92766ad98a9559b`:
    - `stan/math/prim/fun/matrix_exp.hpp:25-43`, `matrix_exp_pade.hpp:23-46`, `MatrixExponential.h:65-212` (Higham 2005 Padé `[3/3..13/13]` thresholds & `maxnorm = 5.371920351148152`).
    - `stan/math/prim/fun/matrix_exp_action_handler.hpp:26-100` (Al-Mohy & Higham 2011 shifted action `mu = trace/n`).
    - `stan/math/rev/functor/ode_bdf.hpp:150-158` (`rtol=1e-10, atol=1e-10, max_num_steps=1e8`); `stan/math/prim/functor/ode_rk45.hpp:162-170` (`rtol=1e-6, atol=1e-6, max_num_steps=1e6`).
- **Primary Peer-Reviewed Literature & Standards:**
  - T. W. Schnider et al., *Anesthesiology* 88(5):1170–1182, 1998 (`DOI: 10.1097/00000542-199805000-00006`).
  - D. J. Eleveld, P. Colin, A. R. Absalom, M. M. R. F. Struys, *Br. J. Anaesth.* 120(5):942–959, 2018 (`DOI: 10.1016/j.bja.2018.01.018`, full text verified via University of Groningen repository PDF).
  - C. C. Margossian, Y. Zhang, W. R. Gillespie, *CPT: Pharmacometrics Syst. Pharmacol.* 11(9):1151–1169, 2022 (`DOI: 10.1002/psp4.12812`).
  - P. J. Schuller, S. Newell, P. A. Strickland, J. J. Barry, *Br. J. Anaesth.* 115(Suppl 1):i95–i103, 2015 (`DOI: 10.1093/bja/aev072`).
  - `IEC 60601-2-24` Ed. 2.0 (2012), infusion pump accuracy trumpet curves, bolus limits, and occlusion alarm requirements.
- **Reproducible Execution Probes (`Python 3.13.15`, Linux x86_64, IEEE-754 binary64):**
  - Covariate monotonicity & cohort sweep (Marsh, Schnider, Eleveld), Torsten `K^{-1} r` vs. Van Loan cancellation/singularity probe, `mrgsolve`/`PKPDsim` cubic degeneracy sweep (`49/199` and `71/199` `NaN`s), fixed-step RK4 vs. BDF-1 stiff obese Schnider blowup probe, bioavailability $F=0.6$ peak divergence probe (`+52.8%`), Padé `[3/3]`–`[13/13]` Metzler positivity sweep, and toy PID-TCI EMG spoofing simulation.

## Revalidation

To cheaply verify whether these findings still hold on newer upstream commits or a candidate clinical dosing engine:

1. **Upstream Source Diff Checks (cheapest, < 5 s):**
   - `mrgsolve`: Diff `src/odeproblem.cpp` (`advan11`, `rate_rm`) and `src/datarecord.cpp` (`dur`) for `std::clamp(..., -1.0, 1.0)` on `acos`, coalescent eigenvalue branching, and `infusion_count == 0` zeroing.
   - `Torsten`: Diff `pmx_linode_model.hpp:147-160` to check whether `mdivide_left` + subtraction has been replaced by Van Loan block exponentiation, and diff `ev_history.hpp:639` + `ev_manager.hpp:237` for bioavailability-duration vs. rate semantics.
   - `PKPDsim`: Diff `inst/cpp/sim.cpp:2,92,111,226` for adaptive/stiff stepper support, fixing `std::vector<int> rate` -> `std::vector<double> rate`, and `src/pk_3cmt_iv_infusion.cpp:32,58-60` for loop bounds and `std::max(0.0, -q)` clamping.
   - `stan-dev/math`: Diff `stan/math/prim/fun/MatrixExponential.h:187-212` for Al-Mohy & Higham (2009) trace-shift / $\|A^p\|^{1/p}$ scaling updates.
2. **Minimal Standalone Discriminating Probe (< 1 s in Python 3):**
   ```python
   import math
   # 1. Verify Schnider James LBM inversion & elderly V2 collapse
   lbm_f = lambda w, h: 1.07*w - 148.0*(w/h)**2
   cl_s = lambda w, h: 1.89 + 0.0456*(w-77) - 0.0681*(lbm_f(w,h)-59) + 0.0264*(h-177)
   assert lbm_f(200, 165) < 0 and cl_s(200, 165) > 10.0
   assert 18.9 - 0.391*(102 - 53) < 0
   # 2. Verify mrgsolve advan11 acos(>1.0) NaN at Q=Q2=0, k10=0.0959
   s1 = 0.0959; aa = -s1*s1/3.0; bb = 2.0*s1*s1*s1/27.0; sq = math.sqrt(-aa/3.0)
   assert bb/(2.0*sq*sq*sq) > 1.0
   # 3. Verify PKPDsim pk_3cmt_iv_infusion q > 0 NaN at Q=Q2=0, k10=0.3151
   a = 0.3151; m = -(a**2)/3.0; n = 2.0*(a**3)/27.0; q = (n**2)/4.0 + (m**3)/27.0
   assert q > 0.0
   ```
3. **Full End-to-End Revalidation (when native R/C++ toolchains are available):** Execute the four differential test vectors from §3.2 (`Q = Q2 = 0`, `dt = 1e-10 min` with infusion, `F = 0.6` infusion, and `ALAG = 0.5` with `rate = 0.5`) directly against compiled `mrgsolve`, `Torsten`, and `PKPDsim` binaries and assert agreement against an arbitrary-precision Van Loan reference.
