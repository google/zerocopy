# Thermal-runaway criteria, relief sizing (API 520 gas/liquid, omega, Leung) and stiff-integration tolerances: Semenov/Frank-Kamenetskii/TMRad, a T2-type runaway through Cantera/CVODES, and fluids/thermo at pinned revisions

## Summary

- **Criteria.** Semenov's critical point is a tangency; with ε = R·T_a/E the exact values are θ_c = (1 − 2ε − √(1 − 4ε))/(2ε²), ψ_c = θ_c·e^(−θ_c/(1+εθ_c)), so ΔT_c = R·T_a²/E and ψ_c = 1/e hold only as ε → 0 (ψ_c = 0.4115 at ε = 0.1). FK δ_c computed here: slab 0.878458, cylinder 2.000000, sphere 3.321992. Doubling vessel scale lowers the critical ambient temperature by ≈ (R·T²/E)·ln 2. The zero-order TMRad = c_p·R·T0²/(q0·E) is 12–31 % shorter than first-order TMR (conservative). Dividing a measured TMR by φ is 2–16 % *non*-conservative for consuming kinetics. Basis: derived + execution (toy models).
- **T2 Laboratories (CSB 2008-3-I-FL).** Published constants give TD24 ≈ 204.6 °C for the diglyme decomposition and MTSR ≈ 238.4 °C, i.e. Stoessel class 4 or 5 whatever MTT is. Basis: documentation + derived; loading and pressure model assumed. With A = 10^84 h⁻¹, E = 800 kJ/mol, the closed-vessel peak dT/dt (≈ 6×10^28 K/s on a 10^-28 s scale) is unresolvable in double precision. CVODES warns "t + h = t … continue anyway" and integrators report 10^10–10^27 K/s. Times to 390 °F and to the 400 psig set point are well-posed and converge with rtol.
- **Loose tolerances fail silently.** Through Cantera at rtol = 10^-2 the T2-type run misses the runaway and returns normally, with diglyme 27 % above its initial value. GRI-Mech 3.0 ignition delay with atol = 10^-6 is off by +2.6 %/+4.6 %/−30 % at rtol 10^-4/10^-6/10^-2; atol ≤ 10^-10 with rtol ≤ 10^-6 gives ≤ 2×10^-5. Quantities evaluated *at* a peak (vent area) stall at 10^-4–10^-3 error from co-variable sampling. Basis: execution.
- **Cantera → CVODES.** Defaults: BDF, a dense Jacobian differenced by CVODES, rtol 10^-9, atol 10^-15, max_steps 20000 enforced by Cantera's own `CV_ONE_STEP` loop, no hmax. The docstring's "default is 10" error-test failures is IDA's value; CVODES uses MXNEF = 7 because Cantera does not set it. At 1268 species GMRES + AdaptivePreconditioner is 4× faster than DENSE; at 53 species DENSE is 3.6× faster. Basis: source + execution.
- **fluids and thermo.** fluids implements API 520 gas/steam/liquid sizing but no omega/two-phase method. It differs from exact-constant equations by −5.7×10^-4 (subcritical); the area jumps 10 % at the critical ratio when K_b ≠ 1. `API520_A_g(k=1.0)` and `API520_A_l` with default `Kv` crash. thermo flashes give the two-point ω, whose omega flux matches a direct HEM integral within 1 %. The saturated-liquid ω is off 12.7 % for propane near its critical point. A source install of thermo at the pin lacks a generated SQLite database. Basis: source + execution.

## Applicability

| Subject (REPORT.json) | Role | Evidence used |
|---|---|---|
| Cantera/cantera @ 25c1ab1c397e2991c77560b1ad5154919a12c733 (head) | source of tolerance/integrator plumbing | source only |
| Cantera/cantera @ 4a8358eb80cfeb50474386b5f9ec0b3a83519889 (tag `v3.2.0`) | source matching the executed wheel (`ct.__git_commit__` = `4a8358e`) | source |
| `cantera-3.2.0-cp313-cp313-manylinux_2_28_x86_64.whl` (sha256 `52335f69…4365`) | executed; reports SUNDIALS 7.4.0; ships GRI-Mech 3.0, h2o2, n-hexane NUIG-2015 | execution |
| LLNL/sundials @ 312fc0f3684f27209ca9dc9249d194436eb41a7a (7.9.0) and @ 8e17876d3b4d682b4098684b07a85b005a122f81 (tag `v7.4.0`) | CVODES/IDA defaults | source |
| CalebBell/fluids @ 7737f7051109d4de62cfccfc38af37a9214c3103 | installed from this tarball (`fluids.__version__` 1.3.1) | source + execution |
| CalebBell/thermo @ 2bb466e98439c2395a004e7095d07f9b97a5a0f0 | installed from this tarball (0.6.1) with PyPI `chemicals` 1.5.2 | source + execution |
| CSB 2008-3-I-FL; UMich module; Duxbury & Wilday; Stoessel lecture; THT sheet 22 | incident facts, constants, worked examples | documentation |

Exact observation versus extension:

- **Cantera execution is 3.2.0, not the pinned head (576 commits ahead).** The `CVodesIntegrator.cpp` diff is mostly refactoring (`span`, removal of SUNDIALS < 6 branches). Two changes matter:
  - head applies tolerance changes to live CVODES memory (L165–168), whereas 3.2.0 sets `m_init = false` and re-initialises the whole network (tag `ReactorNet.cpp` L66–75);
  - head adds default-atol hooks, overridden only by `MoleReactor` and used only when no atol is set.

  The probes set rtol/atol before the first step, so the tolerance semantics exercised are the same at both revisions (derived). Two things are not covered at head. Default-atol mole-reactor runs would get different absolute tolerances. The `ExtensibleReactor` path was not executed there: head's `delegatable_methods` (`reactor.py` L693) drop `sync_state`, the surface hooks and `species_index`, although the four hooks used here remain.
- **SUNDIALS.** The wheel links 7.4.0; the pin is 7.9.0. The CVODES constants cited (MXNEF 7, MXNCF 10, MXSTEP_DEFAULT 500, NLS_MAXCOR 3, BDF_Q_MAX 5) are identical at both tags; nothing was executed against 7.9.0.
- **fluids/thermo evidence is the pinned source**, installed in its own venv. PyPI builds of the same version numbers were not used; for thermo they differ at least by a generated database (Finding 3).
- **Host:** x86-64 Linux host, Python 3.13 (3.13.15), NumPy 2.5.4, SciPy 1.18.1, single-threaded. Wall times are indicative.
- **Standards:** API 520 Part I, API 521 and ISO 4126-10 are paywalled and were **not examined**. Equations attributed to them are the forms implemented in fluids, derived here, or taken from the cited public sources.

## Findings

### 1. Thermal-explosion criteria and their sensitivities

| Criterion | Statement | Inputs | Hidden assumption |
|---|---|---|---|
| Semenov (lumped) | Runaway when ψ = V·q_v(T_a)·E/(U·S·R·T_a²) > ψ_c(ε); tangency ⇒ θ_c = (1+εθ_c)² | E, A·ΔH (in q_v), U, S/V, T_a | uniform T; no reactant consumption |
| Frank-Kamenetskii | Runaway when δ = (E/R T_a²)·r0²·q_v(T_a)/λ > δ_c(geometry) | adds λ, characteristic size r0 | conduction-limited; wall at T_a (Bi → ∞) |
| TMRad | TMRad = c_p·R·T0²/(q0·E) | q0, E, c_p | zero-order (no consumption), adiabatic |
| φ-correction | φ = 1 + M_b·c_pb/(M_s·c_ps); ΔT_ad = φ·ΔT_ad,meas (THT sheet 22); TMR at φ = 1 from measured/φ on a log-TMR vs 1/T line (NETZSCH) | cell mass and heat capacity | exact only in the zero-order limit (see below) |
| Stoessel classes | Ordering of MTSR, MTT, TD24 above T_p: 1 MTSR<MTT<TD24; 2 MTSR<TD24<MTT; 3 MTT<MTSR<TD24; 4 MTT<TD24<MTSR; 5 TD24<MTSR and TD24<MTT | four temperatures | ties and the T_p reference undefined |

Measured with `criteria.py` (toy, generic Arrhenius models written for this report; Basis: execution + derived):

- Semenov exact critical values: ε = 0 → θ_c = 1, ψ_c = 0.36788; ε = 0.05 → 1.11456 / 0.38780; ε = 0.2 → 1.90983 / 0.47953. ΔT_c ≈ R·T_a²/E underestimates the exact critical excess by 4 % at ε = 0.02 and 27 % at ε = 0.1.
- FK δ_c (shooting on u'' + (j/s)u' + e^u = 0 with δ = max s²e^{u(s)}): slab 0.878458, infinite cylinder 2.000000, sphere 3.321992; centre excess θ0,c = 1.18684, 1.38629 (= ln 4), 1.60746.
- First-order versus zero-order TMR (E = 100 kJ/mol, T0 = 400 K): ratio TMR₁/TMR₀ = 1.308 (B = 3.76 and 7.52), 1.178 (B = 15.0), 1.120 (B = 30.1). The zero-order formula is only meaningful when B = E·ΔT_ad/(R·T0²) ≫ 1.
- φ-correction with first-order consumption (ΔT_ad = 200 K): (TMR_meas/φ)/TMR_true = 1.000, 1.023, 1.057, 1.110, 1.156 for φ = 1, 1.2, 1.5, 2, 3. A larger φ lowers the effective B, so dividing by φ over-predicts the plant TMR.
- Scale-up (toy sphere, U = 20 W m⁻² K⁻¹, 10 W m⁻³ at 350 K): critical T_a falls from 432.74 K (r = 0.05 m) to 378.77 K (r = 2 m) at E = 100 kJ/mol. The 0.5 → 1 m drop is 13.30/9.51/5.58 K for E = 80/100/150 kJ/mol against (R·T²/E)·ln 2 = 12.54/9.10/5.43 K. Sensitivities: d(ln ψ)/d(ln A) = 1, d(ln ψ)/d(ln U) = −1, d(ln ψ)/d(ln L) = +1 (S/V ∝ 1/L), d(ln ψ)/dT_a = E/(R·T_a²) − 2/T_a. The higher E is, the sharper the cliff and the smaller the scale-up margin in kelvin.
- Stoessel classifier: the two worked examples in Stoessel's 2020 EPSC lecture (T_p/MTSR/MTT/TD24 = 40/81/56/130 °C → class 3; 30/200/125/90 °C → class 5) are reproduced. A vendor blog consulted during research words classes 2–3 inconsistently with these examples, so the lecture is used as the authority.

### 2. T2 Laboratories: what the record supports, and a partially sourced re-implementation through Cantera

CSB report 2008-3-I-FL (Board Voting Copy, 15 Sep 2009; Basis: documentation):

| Item | Reported |
|---|---|
| Event | 19 Dec 2007, 1:33 pm; four killed, 32 injured; cooling problem reported at 1:23 pm |
| Equipment | 2,450-gallon batch reactor; MAWP reduced from 1,200 to 600 psig; 4-inch rupture disk "set at 400 psig" (per employees) |
| Process | First (metalation) step at about 350 °F (176.7 °C); sodium + MCPD in diglyme |
| Tests | VSP2 closed cell: second exotherm above 390 °F (198.9 °C), sodium–diglyme; ≈ 2340 °F/min (1300 °C/min) and 32,000 psi/min (2206 bar/min); cells burst |
| Normal recipe (Run 6) | Na 5.147 g, MCPD dimer 21.164 g, diglyme (95 %) 20.690 g, mineral oil 1.591 g |
| Relief conclusion | "unlikely that an overpressure relief device of any size set at 400 psig could have prevented failure … once the second exothermic reaction began"; a disk at 75 psig would likely have relieved the first exotherm |

**Model provenance.**
- The published reconstruction (Willey, Fogler & Cutlip 2011, 10.1002/prs.10431) is paywalled and was **not examined**.
- Constants come from a public UMich module citing Fogler's 5th edition:
  - r1 = k1·C_A·C_B (A + B → C + ½D), k10 = 4×10^14 L mol⁻¹ h⁻¹, E1 = 1.28×10^5 J/mol, ΔH1 = −45,400 J/mol Na;
  - r2 = k2·C_S (S → 3D + byproducts), k20 = 10^84 h⁻¹, E2 = 8×10^5 J/mol, ΔH2 = −3.2×10^5 J/mol;
  - V = 4000 L, ρ = 7.31 mol/L, C_p = 430.91 J mol⁻¹ K⁻¹ (ΣN·C_p = 1.26×10^7 J/K), coolant 373 K. The module writes E in "J mol⁻¹ K⁻¹", read here as J/mol.
- **Assumptions:**
  - C_A0/C_B0/C_S0 = 5.055/4.285/2.804 mol/L, from the Run 6 charge with dimer = 2 monomers and density 0.93 kg/L;
  - headspace = vessel − liquid = 5.274 m³, an ideal gas at 1 atm initially, with no vapour pressure, swell or venting; T0 = 350 °F;
  - "area" = the API 520 critical-gas area passing the H₂ generation rate at 400 psig (K_d 0.62, Z 1); 4-inch bore = 8.22×10^-3 m².
- This is a partially sourced model, **not** a validated incident model.

**Results** (`t2_cantera.py`, Cantera 3.2.0 `ExtensibleReactor` + CVODES; Basis: execution):
- **Criticality.** ΔT_ad1 = 61.76 K, ΔT_ad2 = 284.83 K. Reaction 2 has TMRad = 653/9.57/0.167 h at 470/480/490 K and TD24 = 477.79 K (204.64 °C). MTSR = 238.42 °C, so the class is 4 or 5. TD24 is close to the CSB's observed 390 °F onset; these are different quantities (consistency, not validation).
- **Loss of cooling** (adiabatic from 350 °F, Cantera defaults): 390 °F at 309.45 s, 400 psig at 347.29 s, 600 psig at 445.94 s. The gas-only area at burst is 3.7×10^-5 m² (dT/dt 0.116 K/s); it exceeds the 4-inch bore only at 530.80 s (513.23 K), once reaction 2 runs away. Two-phase venting and solvent boiling, which underlie the CSB's 75 psig argument, are outside the model.
- **Peak dT/dt is ill-posed.**
  - The model's true peak is ≈ (R·T_f²/E2)·k2(T_f) = 6.2×10^28 K/s at T_f = 796.4 K, on a time scale 1/k2 = 1.1×10^-28 s.
  - SciPy Radau (rtol 10^-12) stops with status −1, "Required step size is less than spacing between numbers", at 530.895 s and 577 K. Cantera continues through `MSGCV_HNIL` warnings with 220 error-test failures.
  - "Peak on steps": Cantera and LSODA ≈ 3.0×10^27 K/s, Radau 7.3×10^11, BDF 8.3×10^10. The VSP2 measurement was 21.7 K/s, so the model is falsified for peak rates (V4).
- **Critical cooling** (T_a 373 K; runaway = T_max ≥ 390 °F within 3 h): the simulated UA_crit is 3315 W/K. Lumped no-consumption criteria give 7789 W/K (balance) and 45,520 W/K (Semenov tangency), i.e. 2.3× and 13.7× conservative.

Tolerance sweep (relative error against the SciPy Radau rtol 10^-12 event reference; crossing times interpolated linearly between internal steps):

| rtol | atol | steps | RHS | Jac | wall s | t_390F | t_disk | A_disk | t_A4 | outcome |
|---|---|---|---|---|---|---|---|---|---|---|
| 1e-2 | 1e-15 | 40 | 62 | 4 | 0.001 | −9.1e-3 | −1.0e-2 | −2.4e-2 | — | runaway **missed**; at t = 4645 s T = 431.9 K, C_S = 3.554 > C_S0 = 2.804; energy invariant holds (3e-8 K) |
| 1e-3 | 1e-15 | 233 | 669 | 128 | 0.013 | −5.8e-3 | −3.2e-3 | −6.2e-3 | −1.8e-3 | runaway found |
| 1e-4 | 1e-15 | 278 | 906 | 28 | 0.009 | −2.3e-3 | −1.7e-3 | −4.6e-3 | −1.5e-3 | |
| 1e-6 | 1e-15 | 560 | 1319 | 11 | 0.013 | −1.9e-4 | −1.7e-4 | −3.5e-4 | −5.1e-5 | |
| 1e-9 (default) | 1e-15 | 2045 | 2812 | 37 | 0.032 | −5.9e-7 | −2.5e-5 | ≈ −6e-5 | −2.2e-7 | from the printed default and REF values |
| 1e-12 | 1e-20 | 6871 | 8083 | 113 | 0.085 | −3.1e-6 | −3.6e-6 | −8.0e-6 | −6.4e-10 | |

Notes on the sweep:
- The 10^-6–10^-5 floor on t_disk at tight rtol comes from interpolating crossings linearly between long internal steps, not from CVODES dense output.
- `max_time_step` 1.0 s / 0.1 s at rtol 10^-6 cuts the t_disk error from −1.7×10^-4 to −7.1×10^-7 / −7.0×10^-9, at 2.7× / 10× the steps.
- SciPy Radau/BDF/LSODA at rtol 10^-6 give t_disk errors of 1.6×10^-7 / 6.7×10^-6 / 1.9×10^-6 (V2).

### 3. Relief sizing: API 520 equations, fluids, the omega method and thermo

**Coefficient conventions (derived; `fluids_api520.py` section A).** From G = P1·√(k·M/(Z·R·T)·(2/(k+1))^((k+1)/(k−1))):

| Form | Equation as implemented/commonly published | Exact constant | Effect of rounding on area |
|---|---|---|---|
| SI critical | A[mm²] = W[kg/h]/(C·K_d·P1[kPa]·K_b·K_c)·√(T·Z/M), C = 0.03948·√(k(2/(k+1))^((k+1)/(k−1))) | 0.039481 | +1.9×10^-5 |
| USC critical | A[in²] = W[lb/h]/(C·K_d·P1[psia]·K_b·K_c)·√(T[°R]·Z/M), C = 520·√(…) | 519.448 | −1.1×10^-3 |
| SI subcritical | A[mm²] = 17.9·W/(F2·K_d·K_c)·√(T·Z/(M·P1·(P1−P2))) | 17.9102 | −5.7×10^-4 |
| USC subcritical | A[in²] = W/(735·F2·K_d·K_c)·√(T·Z/(M·P1·(P1−P2))) | 734.61 | −5.3×10^-4 |
| Critical ratio | r_c = (2/(k+1))^(k/(k−1)); F2 = √(k/(k−1)·r^(2/k)·(1−r^((k−1)/k))/(1−r)) | — | — |

"C" is not dimensionless; its value depends on the unit system. The USC and SI forms of the same standard differ by 0.1 % in area. Basis: derived; the 520/735 USC constants are the commonly published forms, and the standard text itself was not examined.

**What fluids implements** (`fluids/safety_valve.py` @ 7737f7051109d4de62cfccfc38af37a9214c3103; Basis: source).
- `__all__` (L65–84) has the API520_B/C/F2/N/SH/W factors, `API520_A_g/A_l/A_steam`, `API520_Kv`, API 526 sizes and API 521/VDI flare noise.
- There is no omega, HEM, Leung or ISO 4126-10 routine anywhere in the package. The `omega`/`Leung` grep hits are flow-meter Δω̄, a geometry blockage ω, a Friedel Ω and L. S. Leung saltation citations.
- `API520_A_g(m, T, Z, MW, k, P1, P2=101325, Kd=0.975, Kb=1, Kc=1)` (L588) takes SI inputs and works internally in kg/h, kPa and mm² (L663–671):
  - critical: `A = m/(C*Kd*Kb*Kc*P1)*sqrt(T*Z/MW)`;
  - else: `A = 17.9*m/(F2*Kd*Kc)*sqrt(T*Z/(MW*P1*(P1-P2)))`, so **K_b is applied only in the critical branch**.
- P2 is used as an absolute pressure (ratio and difference, default 101325), although the docstring (L617–619) calls it "the increase in pressure during flow at the outlet".
- The regime test `is_critical_flow` (`compressible.py` L618–619) is `return Pcf > P2` with `P_critical_flow = P*(2.0/(k + 1.0))**(k/(k - 1.0))` (L514).
- `API520_C` (L142–187) returns `0.023945830445454768` for k = 1, and its docstring (L161–162) says 0.0239 is "the highest value possible for C".
- `API520_A_l(m, rho, P1, P2, overpressure, Kd=0.65, Kc=1.0, Kw=None, Kv=None, edition=TENTH_EDITION, mu=None)` (L907–908) computes `A = 11.78*Q*sqrt(G1/(P1-P2))/(Kd*Kw*Kc*Kv)` (L1089). `Kv` is filled only `if Kv is None and mu is not None` (L1081).

Observed behaviour (`fluids_api520.py`, pinned install; Basis: execution):

| Check (API 520 example fluid: 24,270 kg/h, 348 K, Z 0.90, M 51, k 1.11, P1 670 kPa; r_c = 0.582588) | Result |
|---|---|
| fluids vs exact-constant hand code, critical (r = 0.30 … r_c) | +1.90×10^-5 |
| fluids vs exact-constant hand code, subcritical (r_c … 0.99) | −5.68×10^-4 |
| Area jump across r_c, Kb = 1 | A_sub/A_crit − 1 = −5.87×10^-4 (constant rounding only) |
| Area jump across r_c, Kb = 0.9 | −1.005×10^-1: the required area *drops* 10 % when backpressure rises past r_c |
| `API520_C(k)` on k ∈ [1, 2] | strictly increasing (0.023946 at k = 1 … 0.030392 at k = 2), so 0.0239 is the *lowest* C, i.e. the conservative (largest-area) choice; the docstring word "highest" is wrong |
| `API520_A_g(k=1.0)` | `ZeroDivisionError: float division by zero`, raised in `P_critical_flow` (k − 1 in the exponent) before the `API520_C` special case is reached |
| `API520_F2(1.11, 1, r)` vs a 60-digit Decimal reference | rel. error −2.2e-13 (1 − r = 1e-3), +2.0e-10 (1e-6), −1.7e-7 (1e-9), +2.3e-4 (1e-12), +5.9e-2 (1e-15); ZeroDivisionError at r = 1. An `expm1`/`log` form is exact to 2e-16 |
| `API520_A_l(...)` with default `Kv=None` and no `mu` | `TypeError: unsupported operand type(s) for *: 'float' and 'NoneType'`; the docstring examples always pass `Kv` |
| Docstring examples | reproduced: 0.0036990460646834414 m², 0.004248358775943481 m², liquid 0.0030661356 m² |

Apart from rounding (≤ 0.06 %), two items matter: the K_b discontinuity, which is undocumented, and the k = 1 and default-`Kv` cases, which crash rather than return wrong numbers.

**Omega method (derived from the ω-EOS v/v0 = ω(P0/P − 1) + 1).**
- The nozzle equation G = √(2∫_P^P0 v dP)/v gives G = √(P0/v0)·√(−2[ω ln η + (ω−1)(1−η)])/(ω(1/η−1)+1).
- Its maximum over η is the choked state: η_c² + (ω²−2ω)(1−η_c)² + 2ω² ln η_c + 2ω²(1−η_c) = 0 and G_c = η_c·√(P0/(v0·ω)). `thermo_omega.py` confirms argmax = root and G_max = η_c/√ω to six digits for ω = 0.5–30. ω = 1 gives η_c = e^-½ (isothermal gas).
- These are the forms attributed to Leung (AIChE J. 32:1743, 10.1002/aic.690321019; content not examined) and API 520 Annex C (not examined).
- ω definitions compared:
  - saturated liquid: ω_s = (c_pl·T0·P0/v0)(v_lg/h_lg)²;
  - two-point: ω = (v(P)/v0 − 1)/(P0/P − 1), which is 9(v_0.9/v0 − 1) at P = 0.9·P0.
- thermo inputs:
  - `FlashPureVLS.flash(P, VF=0|1)` (saturation);
  - `flash(P=0.9·P0, S=S0)` (isentropic);
  - `flash(P, H=H0)` (isenthalpic).
  
  Code locations: `flash` at `thermo/flash/flash_base.py` L158, `FlashPureVLS` at `flash_pure_vls.py` L58, IAPWS-95 phases at `phases/iapws_phase.py` L185/190, `PRMIX` at `eos_mix.py` L6624.
- G_HEM below is a 500-point isentropic HEM integral using the same flashes (saturated-liquid inlet; Basis: execution).

| Fluid, P0 | ω_s | ω_0.9 isentropic | ω_0.9 isenthalpic | ω_0.7 isentropic | G_HEM kg m⁻² s⁻¹ (η) | G_ω/G_HEM − 1: ω_s / ω_0.9s / ω_0.9h |
|---|---|---|---|---|---|---|
| water, 2 bar | 50.83 | 52.17 | 52.47 | 55.50 | 1788 (0.942) | +0.009 / −0.003 / −0.006 |
| water, 5 bar | 26.36 | 26.93 | 27.14 | 28.48 | 3747 (0.917) | +0.010 / +0.001 / −0.003 |
| water, 20 bar | 10.22 | 10.27 | 10.43 | 10.75 | 10875 (0.861) | +0.008 / +0.006 / −0.000 |
| water, 80 bar | 4.35 | 4.01 | 4.15 | 4.14 | 28906 (0.780) | −0.021 / +0.010 / −0.004 |
| propane (PR), 10 bar | 7.55 | 7.28 | 7.46 | 7.46 | 6849 (0.830) | −0.010 / +0.005 / −0.005 |
| propane (PR), 30 bar (T_r = 0.95) | 4.93 | 3.38 | 3.56 | 3.42 | 13349 (0.755) | **−0.127** / +0.004 / −0.015 |

Further results:
- Subcritical: ω_0.9s vs HEM is −0.4 % (water, 5 bar, η_b = 0.95) and 0.0 to +0.2 % (propane, 30 bar, η_b = 0.95–0.8).
- Two-phase inlet (water, 5 bar, quality 0.01/0.05/0.20): ω_0.9s = 6.71/2.24/1.17 with deviations +1.0/+1.1/+0.2 %.
- The two-point ω tracks HEM within 1 % everywhere tested. ω_s degrades near the critical point. ω_0.7 differs from ω_0.9 by up to 6 %.
- Flash cost: IAPWS-95 ≈ 6 ms per flash, PR ≈ 0.1 ms.
- PR is not a reference propane EOS, so these runs test the ω approximation against a consistent EOS, not the EOS itself.

**Source-install packaging gap (thermo; Basis: source + execution).** `thermo/unifac.py` L3514–3523 opens `os_path_join(source_path, "Phase Change", "DDBST_UNIFAC_assignments.sqlite")` with `sqlite3.connect`. The file is generated by `dev/dump_UNIFAC_assignments_to_sqlite.py` (L51 `to_location = …'DDBST_UNIFAC_assignments.sqlite'`) and ignored by `.gitignore` L53 (`*.sqlite`), so the git tree at the pin does not contain it; the PyPI thermo 0.6.1 install in the Cantera venv does (2,605,056 bytes). On a source install, `ChemicalConstantsPackage.from_IDs(["propane"])` raises `sqlite3.OperationalError: no such table: DDBST` (L3555), and `sqlite3.connect` leaves a 0-byte database file in site-packages. The probe builds the propane flasher from `chemicals` constants instead.

**Leung's tempered-system vent formula (golden check; Basis: documentation + execution).** Duxbury & Wilday (IChemE Symp. Ser. 115) present Leung's method as A = M0·q/(G·[(V/M0 · h_fg/v_fg)^½ + (C·ΔT)^½]²), where q is the mean heat release per unit mass (W/kg, *not* a self-heat rate), plus an ideal-gas variant and the equilibrium-rate model G = (dP/dT)·√(T/C) = h_fg/(v_fg·√(C·T)). Their Appendix 1 example (M0 1500 kg, V 2.1 m³, q 1405 W/kg, h_fg 668,950 J/kg, v_fg 0.2404 m³/kg, C 1960 J/kg/K, ΔT 10.5 K, G 1238 kg m⁻² s⁻¹) is reproduced: 0.04017 m² (published 0.040), variant 0.03719 m² (0.0372), ERM G 2385 and 1907 kg m⁻² s⁻¹ (published 2385, 1907). The latent term is 62.4 against a sensible term of 143.5, so ΔT (allowed overpressure) dominates the result. The original AIChE J. 32:1622 (DOI 10.1002/aic.690321006) was verified by metadata only.

### 4. Stiff numerics: how Cantera's ReactorNet drives CVODES, and what tolerances do

Plumbing at head (RN = `src/zeroD/ReactorNet.cpp`, CI = `src/numerics/CVodesIntegrator.cpp` @ 25c1ab1c397e2991c77560b1ad5154919a12c733; Basis: source):

| Python knob | Path → CVODES | Default |
|---|---|---|
| construction | `newIntegrator(isOde ? "CVODE" : "IDA"); setMethod(BDF_Method); setLinearSolverType("DENSE")` (RN L164–169) → `CVodeCreate` (CI L315) | BDF/Newton/dense |
| `rtol`, `atol` | `setRelativeTolerance`/`setAbsoluteTolerance` (RN L190–209) → `updateTolerances` (L233–245) → `CVodeSVtolerances` (CI L150–169) | 1e-9, 1e-15 (`ReactorNet.h` L483–485) |
| `max_time_step` | RN L179–183 → `CVodeSetMaxStep` | 0 = none |
| `max_steps` | RN L341–344; `integrate()` loops `CVode(…, CV_ONE_STEP)` and throws "Maximum number of timesteps ({}) taken without reaching output time" (CI L489–500), then `CVodeGetDky` interpolates (L525) | 20000 (`CVodesIntegrator.h` L131) |
| `max_err_test_fails` | RN L185–188; `CVodeSetMaxErrTestFails` only `if (m_maxErrTestFails > 0)` (CI L474–476) | CVODES `MXNEF 7` |
| `linear_solver_type`, `preconditioner` | RN L324–339; DENSE = `SUNLinSol_Dense` with no user Jacobian, so CVODES difference quotients (CI L384–402); GMRES = `SUNLinSol_SPGMR` + `CVodeSetPreconditioner` (L424–434) | DENSE |

- **Documentation discrepancy (source).** `reactor.py` L2014–2015 (head) and `reactor.pyx` L1812–1813 (v3.2.0): "The maximum number of error test failures permitted by the CVODES integrator in a single step. The default is 10." Cantera never calls `CVodeSetMaxErrTestFails` at its default `m_maxErrTestFails = 0` (`CVodesIntegrator.h` L132), and SUNDIALS sets `cv_mem->cv_maxnef = MXNEF;` (`cvodes.c` L548) with `#define MXNEF 7` (`cvodes_impl.h` L126; L122 at v7.4.0). The value 10 is IDA's (`ida.c` L179). Similarly, "default value is 4" for `max_nonlinear_iterations` is IDA's; CVODES uses `NLS_MAXCOR 3`, and `CVodesIntegrator` leaves `Integrator::maxNonlinIterations` as a warning stub (`Integrator.h` L279–281).
- **Floating-point resolution.** CVODES tests `cv_tn + cv_h == cv_tn` and emits `MSGCV_HNIL` ("… t + h = t on the next step. The solver will continue anyway.") at most `mxhnil` = 10 times (`cvodes.c` L3540–3552). Through Cantera this is only a warning.

GRI-Mech 3.0 constant-volume ignition (CH4/air, φ = 1, 1100 K, 10 atm, 1 m³; real Cantera chemistry; `ignition.py`):
- Peaks are taken over internal steps from `net.get_derivative(1)`, with dP/dt = ρR[(dT/dt)Σ Y_k/W_k + T·Σ(dY_k/dt)/W_k].
- Reference (rtol 10^-12, atol 10^-20): τ = 16.7263452 ms, peak dT/dt 1.2473×10^9 K/s, peak dP/dt 1.2996×10^12 Pa/s, 6953 steps. Moving to rtol 10^-11 shifts τ by 3.5×10^-8 and the peaks by ≈ 3×10^-6, which bounds what is resolvable.
- "Area" is the API 520 gas area that would hold P at peak dP/dt (≈ 998 m² per m³). It is illustrative only: confined ignition is not a relief-valve problem.

| rtol | atol | steps | Jac | wall s | τ err | peak dT/dt err | peak dP/dt err | area err | T_end K |
|---|---|---|---|---|---|---|---|---|---|
| 1e-2 | 1e-6 | 830 | 222 | 0.14 | −3.0e-1 | +7.8e10 | +6.5e10 | +5.0e10 | **3719.8** (non-physical) |
| 1e-4 | 1e-6 | 279 | 22 | 0.02 | +2.6e-2 | +3.4e-3 | +3.1e-3 | +4.8e-4 | 2959.1 |
| 1e-6 | 1e-6 | 387 | 26 | 0.05 | +4.6e-2 | +4.3e-3 | +8.9e-4 | +2.2e-3 | 2959.1 |
| 1e-3 | 1e-15 | 549 | 24 | 0.03 | −4.9e-4 | +1.5e-4 | −3.2e-4 | −3.0e-3 | 2959.1 |
| 1e-6 | 1e-10 | 845 | 28 | 0.05 | −2.1e-5 | −3.5e-5 | +1.1e-5 | +7.4e-4 | 2959.1 |
| 1e-6 | 1e-15 | 1489 | 33 | 0.07 | −1.7e-6 | −1.0e-4 | −4.1e-5 | −6.7e-4 | 2959.1 |
| 1e-8 | 1e-15 | 2171 | 40 | 0.10 | −6.6e-8 | −7.0e-6 | −2.9e-6 | −8.3e-5 | 2959.1 |
| 1e-10 | 1e-15 | 3156 | 56 | 0.14 | +7.6e-9 | +1.9e-6 | +3.5e-6 | +5.0e-4 | 2959.1 |

Findings from the sweep:
- atol on mass fractions controls τ more than rtol does, because radicals at Y ≈ 10^-10 are invisible to atol = 10^-6; errors are non-monotone in rtol.
- Peaks are stationary, so their sampling error is second order. The area also uses T, P, M̄ and k *at* the peak instant, which are first-order sensitive to where the step falls, so its error stalls at 10^-4–10^-3.
- `max_time_step` 10^-4 s cuts the peak-dT/dt error from 1.0×10^-4 to 7×10^-6 (1820 steps). 10^-6 s brings τ to 5.6×10^-8 but takes 50,767 steps (≈ 2 s).

Linear-solver scaling (constant-pressure mole reactor, φ = 1, 1000 K, 20 atm, default tolerances; peak RSS from `/proc/self/status` VmHWM of a fresh process):

| Mechanism (species/reactions) | DENSE wall, steps, Jacobians, extra RHS for FD Jacobian | GMRES + AdaptivePreconditioner wall, steps, linear iterations | τ agreement | peak RSS |
|---|---|---|---|---|
| h2o2 (10/29) | 0.011 s, 1907, 35, 385 | 0.029 s, 1489, 4197 | identical | 45 MiB / 45 MiB |
| GRI-Mech 3.0 (53/325) | 0.097 s, 2722, 50, 2700 | 0.349 s, 2033, 8874 | identical | 50 / 50 MiB |
| n-hexane NUIG-2015 (1268/5336) | 90.1 s, 3605, 70, 88,830 | 22.5 s, 1761, 6840 | 2.8×10^-6 | 159 / 146 MiB |

The dense path's cost is finite-difference Jacobians (70 × 1268 RHS evaluations); the matrix itself is only 12.9 MB. The crossover between 53 and 1268 species was not located.

### 5. Cross-cutting assessment

| Level | What was measured or established | Status |
|---|---|---|
| L1 authoring velocity | A T2-type model in Cantera's `ExtensibleReactor` needs ≈ 10 lines (`after_initialize/get_state/update_state/eval`); a full omega/HEM comparison ≈ 50 lines of thermo calls. No person-month or token data | not examined |
| L2 toolchain build | Prebuilt wheel used; building Cantera head with SUNDIALS 7.9 not attempted; fluids/thermo pure-Python source installs | not examined |
| L3 solve latency | T2-type run: 40–6871 steps, 0.001–0.085 s, ≈ 11 µs per Python-callback RHS. GRI ignition 0.02–0.20 s (2 s with hmax 10^-6). n-hexane 22–90 s. Flash: IAPWS-95 ≈ 6 ms, PR ≈ 0.1 ms | measured (this host) |
| L4 executed code | RHS cost dominates: n-hexane ≈ 1 ms per RHS evaluation (88,830 FD-Jacobian RHS in 90 s). No SIMD/cache study | partially measured |
| L5 checking cost | No certificates exist. The analogue is an independent re-integration: SciPy Radau at rtol 10^-12 needs 33,157 RHS evaluations (1.5 s) for the T2-type run | measured analogue |
| L6 memory | Peak RSS 45–159 MiB; dense Jacobian n² × 8 B (12.9 MB at n = 1268). Disk/energy not measured | partially measured |

**C1 (comprehensibility).** Semenov needs two numbers (ψ, ε), FK one more (geometry/Biot), Stoessel four temperatures and an ordering; each is auditable by hand. The hidden footguns are the dropped assumptions: zero order in TMRad and φ-scaling, no consumption in Semenov (2.3–13.7× conservative here), and the T_p reference in the classes. API 520 gas sizing has a non-local trap: the reader must know that K_b applies only to the critical equation, and that "P2" is an absolute pressure despite its docstring. ω-method diagnostics are legible (ω, η_c, G_c). CVODES failure diagnostics are not: loose rtol produced a wrong answer with no warning, while the true singularity produced only warnings.

**C2 (simplicity / model refinement).** Critical and subcritical gas equations, liquid sizing and flashing flow are all instances of one rule: maximise G(η) = √(2∫v dP)/v over the throat pressure, given an equation of state v(P). The omega EOS is the one-parameter closure that makes the regime boundary ordinary. Choking emerges from the maximisation (ω = 1 recovers isothermal gas choking, ω → 0 recovers liquid G = √(2ρΔP)). This removes the 0.06 % boundary jump and the K_b inconsistency instead of hiding them in rounded constants. Likewise, Semenov and FK are one bifurcation with different heat-loss operators, and a Biot-number continuum joins them. Where this unification would add complexity: real valves need separate discharge coefficients and backpressure corrections per regime, which a single nozzle integral does not supply.

| Validation axis | Done here | Not done |
|---|---|---|
| V1 specification adequacy / golden values | Stoessel examples 2/2; Leung worked example and ERM values; fluids docstring examples; FK δ_c vs closed-form cylinder value 2; omega argmax = closed-form root | mutation testing of fluids/Cantera; property-based search of the API 520 boundary |
| V2 differential testing | fluids vs exact-constant equations; Cantera/CVODES vs SciPy Radau/BDF/LSODA; DENSE vs GMRES+AP; ω vs HEM on two EOSs | fuzzing of CVODES options; cross-checking IAPWS-95 against an independent implementation |
| V3 concurrency/crash/physical | Floating-point time resolution (t + h = t) identified as the platform failure mode | known not to apply otherwise (single-threaded numerics) |
| V4 plant/incident replay | CSB facts versus model: TD24 near the observed second-exotherm onset; model peak rates falsified (10^10–10^27 vs 21.7 K/s) | replay of measured VSP2/ARSST traces (not published as data); operator mental-model testing |

## Boundaries

- **Not examined:**
  - The texts of API 520 Part I (incl. Annex C), API 521, ISO 4126-10 and the DIERS Project Manual.
  - Willey/Fogler/Cutlip (2011) and Fogler's textbook, apart from the constants transcribed in the UMich module; whether its batch loading or vent model match the assumptions here is **unknown**.
  - Townsend & Tou (1980) beyond metadata; its exact φ treatment and onset-temperature corrections are not checked.
  - Building and executing Cantera at the pinned head, and SUNDIALS 7.9.0 execution.
  - CVODES sensitivity analysis, IDA/DAE reactors, and `advance()` with advance limits.
  - Any third relief-sizing implementation (only fluids was compared against hand-coded equations).
- **Known not to apply:**
  - The T2-type model's peak dT/dt and dP/dt are not physical predictions. The Arrhenius fit (A = 10^84 h⁻¹, E = 800 kJ/mol) is extrapolated hundreds of kelvin past where it could have been fitted.
  - The model has no vapour pressure, boiling, two-phase swell, vessel failure or venting, so it cannot test the CSB's 75 psig argument.
  - The gas-only vent areas are lower bounds, not DIERS designs.
- **Unknown:**
  - The actual T2 batch loading, cooling capacity at the time of failure, and temperature at loss of cooling. The model's ≈ 7–9 min from 350 °F to MAWP/runaway against the CSB's ≈ 10 min between the cooling call and the explosion is **not** a reproduction.
  - Whether the fluids P2 docstring wording or the Kb-only-in-critical choice reflects the standard's intent (the standard was not examined).
- **Unsupported:** fluids has no omega/HEM/Leung two-phase relief sizing. CVODES offers no exact-arithmetic or extended-precision time variable to resolve 10^-28 s features at t ≈ 500 s.
- **Not established:**
  - That two-point ω is always within 1 % of HEM: only two fluids, saturated or low-quality inlets, and frictionless isentropic nozzles were tested.
  - That rtol 10^-6 / atol 10^-15 is "safe" in general: it was adequate for these two problems only.
  - That the Stoessel classifier's tie handling matches the original: ties are undefined in the sources used.

## Evidence

All evidence was gathered on 2026-11-20. Pins were resolved via the GitHub commits API; tags were resolved to commits (Cantera annotated tag object `3f552702…` → 4a8358eb80cfeb50474386b5f9ec0b3a83519889; LLNL/sundials `v7.4.0` → 8e17876d3b4d682b4098684b07a85b005a122f81).

Source lines cited:
- Cantera head:
  - `src/zeroD/ReactorNet.cpp` 164–169, 179–245, 276–357;
  - `include/cantera/zeroD/ReactorNet.h` 483–493;
  - `src/numerics/CVodesIntegrator.cpp` 150–244, 281–529;
  - `include/cantera/numerics/CVodesIntegrator.h` 120–132; `Integrator.h` 279–281;
  - `src/zeroD/MoleReactor.cpp` 64–76;
  - `interfaces/cython/cantera/reactor.py` 693–705, 2012–2021, 2084–2111.
- Cantera v3.2.0: `ReactorNet.cpp` 66–75, 106–187, 451–455; `CVodesIntegrator.h` 125–133; `CVodesIntegrator.cpp` 519–565; `reactor.pyx` 681–695, 1810–1816, 1876–1895.
- SUNDIALS pin (CMake 7.9.0): `src/cvodes/cvodes_impl.h` 54, 62, 125–126, 198; `src/cvodes/cvodes.c` 528–549, 3540–3552; `src/ida/ida.c` 178–179. At v7.4.0: `cvodes_impl.h` 50, 58, 121–122, 194.
- fluids: `fluids/safety_valve.py` 65–84, 142–234, 588–671, 907–1091; `fluids/compressible.py` 477–514, 580–619.
- thermo:
  - `thermo/unifac.py` 3510–3555; `.gitignore` 53; `dev/dump_UNIFAC_assignments_to_sqlite.py` 51;
  - `thermo/flash/flash_base.py` 158; `flash_pure_vls.py` 58; `phases/iapws_phase.py` 185–190; `eos_mix.py` 6624.

Literature (Crossref metadata verified; content **not** examined unless marked read):
- Semenoff, Z. Phys. 48:571–582 (1928), 10.1007/BF01340021.
- Frank-Kamenetskii, *Diffusion and Heat Exchange in Chemical Kinetics*, Princeton UP (1955), 10.1515/9781400877195.
- Townsend & Tou, Thermochim. Acta 37:1–30 (1980), 10.1016/0040-6031(80)85001-5.
- Leung, AIChE J. 32:1622–1634 and 32:1743–1746 (1986), 10.1002/aic.690321006 and 10.1002/aic.690321019.
- Hindmarsh et al., ACM TOMS 31:363–396 (2005), 10.1145/1089014.1089020; Gardner et al., ACM TOMS 48(3):1–24 (2022), 10.1145/3539801.
- Stoessel, *Thermal Safety of Chemical Processes*, Wiley-VCH (2008), 10.1002/9783527621606.
- Willey, Fogler & Cutlip, Process Saf. Prog. 30(1):39–44 (online 2010-12-06, issue March 2011), 10.1002/prs.10431.
- Read: the CSB report, the UMich module, Duxbury & Wilday, the Stoessel 2020 lecture, THT sheet 22, and the NETZSCH TD24 note (https://analyzing-testing.netzsch.com/en/blog/2023/determination-of-td24-by-arc-instruments-for-thermal-risk-assessment-in-chemical-processes).
- Not cited: one candidate TD24-estimation DOI that could not be resolved. The DIERS Project Manual (AIChE, 1992) has no DOI and was not examined.

Reproduction (x86-64 Linux host, Python 3.13):

```bash
python3 -m venv /tmp/venv && /tmp/venv/bin/pip install cantera==3.2.0 scipy numpy
python3 -m venv /tmp/venv_pin && /tmp/venv_pin/bin/pip install numpy scipy \
  https://codeload.github.com/CalebBell/fluids/tar.gz/7737f7051109d4de62cfccfc38af37a9214c3103 \
  https://codeload.github.com/CalebBell/thermo/tar.gz/2bb466e98439c2395a004e7095d07f9b97a5a0f0
/tmp/venv/bin/python criteria.py; /tmp/venv/bin/python t2_cantera.py; /tmp/venv/bin/python ignition.py
/tmp/venv_pin/bin/python fluids_api520.py; /tmp/venv_pin/bin/python thermo_omega.py
```

Run times: criteria 3 s, t2_cantera 8 s, ignition 2 min (90 s of it n-hexane DENSE), fluids < 1 s, thermo 38 s. SUNDIALS warnings go to stdout; filter lines containing `t + h = t`. The tables in Findings are copied from the outputs of these scripts:

`criteria.py` (toy models):

```python
import math, numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq, minimize_scalar
R = 8.314462618
def semenov(eps):  # theta_c=(1+eps*theta_c)^2 (smaller root), psi_c=theta_c*exp(-theta_c/(1+eps*theta_c))
    th = 1.0 if eps == 0 else (1 - 2*eps - math.sqrt(1 - 4*eps)) / (2*eps*eps)
    return th, th * math.exp(-th / (1 + eps*th))
for eps in (0, 0.02, 0.05, 0.1, 0.2):
    print("A eps=%.2f theta_c=%.5f psi_c=%.5f" % ((eps,) + semenov(eps)))
for j, nm in ((0, "slab"), (1, "cylinder"), (2, "sphere")):  # delta(s)=s^2 exp(u(s)), u''+(j/s)u'+e^u=0
    f = lambda s, y: [y[1], -math.exp(y[0])/(j+1) if s == 0 else -j/s*y[1] - math.exp(y[0])]
    s0 = 1e-8; sol = solve_ivp(f, (s0, 12), [-s0*s0/(2*(j+1)), -s0/(j+1)], rtol=1e-12, atol=1e-14, dense_output=True)
    r = minimize_scalar(lambda s: -s*s*math.exp(sol.sol(s)[0]), bounds=(0.5, 6), method="bounded", options={"xatol": 1e-12})
    print("B %-8s delta_c=%.6f theta0_c=%.5f" % (nm, -r.fun, -sol.sol(r.x)[0]))
E, T0, A = 100e3, 400.0, 1e10; k0 = A*math.exp(-E/(R*T0))
def tmr_first_order(dT):  # time of max rate, adiabatic first order; event: (1-X)*E*dT/(R T^2) = 1
    rhs = lambda t, y: [dT*A*math.exp(-E/(R*y[0]))*(1-y[1]), A*math.exp(-E/(R*y[0]))*(1-y[1])]
    ev = lambda t, y: (1-y[1])*E*dT/(R*y[0]**2) - 1; ev.terminal = True; ev.direction = -1
    return solve_ivp(rhs, (0, 1e7), [T0, 0], method="Radau", rtol=1e-10, atol=1e-12, events=ev).t_events[0][0]
for dT in (50, 100, 200, 400):
    z = R*T0**2/(dT*k0*E)  # zero-order TMRad = c R T0^2/(q0 E) with q0 = c dT k(T0)
    print("C dTad=%d B=%.2f TMR0=%.5f h TMR1=%.5f h ratio=%.3f" % (dT, E*dT/(R*T0**2), z/3600, tmr_first_order(dT)/3600, tmr_first_order(dT)/z))
true = tmr_first_order(200.0)
for phi in (1.0, 1.2, 1.5, 2.0, 3.0):  # thermal inertia: measured dT_ad = dT_ad/phi
    tm = tmr_first_order(200.0/phi)
    print("D phi=%.1f TMR_meas=%.5f h (TMR_meas/phi)/TMR_true=%.3f" % (phi, tm/3600, tm/phi/true))
qref, Tref, U = 10.0, 350.0, 20.0  # toy: 10 W/m3 at 350 K, U=20 W/m2/K, sphere S/V=3/r
for Ex in (80e3, 100e3, 150e3):
    def Tac(r):
        g = lambda Ta: qref*math.exp(-Ex/R*(1/Ta - 1/Tref))*Ex/(U*3/r*R*Ta*Ta) - semenov(R*Ta/Ex)[1]
        return brentq(g, 200, 900)
    t = [Tac(r) for r in (0.05, 0.5, 1.0, 2.0)]
    print("E E=%.0f Ta_c(r=0.05,0.5,1,2 m)=%s drop(0.5->1)=%.2f K  (R Ta^2/E)ln2=%.2f K" % (Ex/1e3, " ".join("%.2f" % x for x in t), t[1]-t[2], R*t[1]**2/Ex*math.log(2)))
def stoessel(Tp, MTSR, MTT, TD24):
    if MTSR < TD24: return (1 if MTT < TD24 else 2) if MTSR < MTT else 3
    return 4 if MTT < TD24 else 5
for a, want in (((40, 81, 56, 130), 3), ((30, 200, 125, 90), 5)):
    print("F", a, "->", stoessel(*a), "published", want)
```

`t2_cantera.py` (partially sourced T2-type model through Cantera's ReactorNet/CVODES, SciPy reference):

```python
import math, time, warnings; warnings.simplefilter("ignore", DeprecationWarning)
import numpy as np, cantera as ct
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
R = 8.314462618; k10, E1, k20, E2 = 4e14/3600, 1.28e5, 1e84/3600, 8e5     # L/mol/s, J/mol, 1/s, J/mol
dH1, dH2, V, NCp, Tc = -45400.0, -3.2e5, 4000.0, 7.31*4000*430.91, 373.0  # J/mol, L, J/K, K
psig = lambda p: p*6894.757293 + 101325.0; P_DISK, P_MAWP = psig(400), psig(600)
V_H = (2450*3.785411784 - V)/1000; T390F = (390-32)/1.8 + 273.15; T0 = (350-32)/1.8 + 273.15
Vs = 48.592/0.93/1000  # CSB Run 6 charge (g): Na 5.147, MCPD dimer 21.164, diglyme(95%) 20.690; rho 0.93 kg/L assumed
y0 = [2*21.164/160.26/Vs, 5.147/22.98977/Vs, 0.95*20.690/134.17/Vs, T0, 0.0]; CA0, CB0, CS0 = y0[:3]
N0 = 101325.0*V_H/(R*T0); A4 = math.pi/4*0.1023**2
def rhs(t, z, UA=0.0):
    r1 = k10*math.exp(-E1/(R*z[3]))*max(z[0], 0)*max(z[1], 0); r2 = k20*math.exp(-E2/(R*z[3]))*max(z[2], 0)
    return [-r1, -r1, -r2, (V*(-dH1)*r1 + V*(-dH2)*r2 - UA*(z[3]-Tc))/NCp, V*(0.5*r1 + 3*r2)]
P = lambda z: (N0 + z[4])*R*z[3]/V_H
def area(z, d):  # API 520 critical gas area for the H2 generation rate, at P1 = disk set pressure, Kd=0.62, Z=1
    k = 1.41; C = 0.03948*math.sqrt(k*(2/(k+1))**((k+1)/(k-1)))
    return d[4]*2.01588e-3*3600/(C*0.62*P_DISK/1000)*math.sqrt(z[3]/2.01588)*1e-6
class T2(ct.ExtensibleReactor):
    UA = 0.0
    def after_initialize(self, t0): self.n0 = self.n_vars; self.n_vars += 5
    def after_get_state(self, y):
        for i in range(5): y[self.n0+i] = y0[i]
    def after_update_state(self, y): self.z = [y[self.n0+i] for i in range(5)]
    def after_eval(self, t, LHS, RHS):
        d = rhs(t, self.z, self.UA)
        for i in range(5): RHS[self.n0+i] = d[i]
def run(rtol, atol, t_end=3600.0, hmax=None, max_steps=None):
    g = ct.Solution(thermo="ideal-gas", species=[s for s in ct.Species.list_from_file("gri30.yaml") if s.name == "N2"])
    r = T2(g, energy="off"); net = ct.ReactorNet([r]); net.rtol, net.atol = rtol, atol
    if hmax: net.max_time_step = hmax
    if max_steps: net.max_steps = max_steps
    ts, zs = [0.0], [list(y0)]; w = time.perf_counter()
    while net.time < t_end and not (zs[-1][2] < 1e-9*CS0 and zs[-1][3] > 600):
        net.step(); ts.append(net.time); zs.append(list(r.z))
    return np.array(ts), np.array(zs), time.perf_counter() - w, net.solver_stats, (net, r)
def metrics(ts, zs):
    ds = np.array([rhs(t, z) for t, z in zip(ts, zs)]); Pz = np.array([P(z) for z in zs]); Ar = np.array([area(z, d) for z, d in zip(zs, ds)])
    def cross(a, lev):
        i = int(np.argmax(a >= lev))
        return float("nan") if a[i] < lev else ts[i-1] + (lev - a[i-1])*(ts[i]-ts[i-1])/(a[i]-a[i-1])
    td = cross(Pz, P_DISK); tA = cross(Ar, A4)
    return dict(t390F=cross(zs[:, 3], T390F), t_disk=td, dTdt_disk=float(np.interp(td, ts, ds[:, 3])), A_disk=float(np.interp(td, ts, Ar)),
                t_mawp=cross(Pz, P_MAWP), t_A4=tA, T_A4=float(np.interp(tA, ts, zs[:, 3])), pk=float(ds[:, 3].max()), Tmax=float(zs[:, 3].max()))
print("cantera", ct.__version__, "sundials", ct.__sundials_version__, "git", ct.__git_commit__)
print("C0 = %.3f %.3f %.3f mol/L, T0=%.2f K, NCp=%.4e J/K, V_H=%.3f m3, dTad1=%.2f K, dTad2=%.2f K" % (CA0, CB0, CS0, T0, NCp, V_H, -dH1*CB0*V/NCp, -dH2*CS0*V/NCp))
tmr2 = lambda T: (NCp/V)*R*T*T/((-dH2)*CS0*k20*math.exp(-E2/(R*T))*E2)
TD24 = brentq(lambda T: tmr2(T) - 86400, 400, 600)
print("TD24=%.2f C  MTSR=%.2f C  TMRad2(470,480,490 K)=%.4g %.4g %.4g h" % (TD24-273.15, T0 - dH1*CB0*V/NCp - 273.15, tmr2(470)/3600, tmr2(480)/3600, tmr2(490)/3600))
ts, zs, w, st, _ = run(1e-9, 1e-15); m = metrics(ts, zs)
print("default:", {k: round(v, 6) for k, v in m.items()}, "steps", st["steps"], "rhs", st["rhs_evals"], "jac", st["jac_evals"], "errfails", st["err_test_fails"], "wall %.3f s" % w)
ev = [lambda t, z: P(z) - P_DISK, lambda t, z: z[3] - T390F, lambda t, z: area(z, rhs(t, z)) - A4]
w = time.perf_counter(); s = solve_ivp(rhs, (0, 3600), y0, method="Radau", rtol=1e-12, atol=[1e-12]*3 + [1e-9, 1e-8], dense_output=True, events=ev)
print("SciPy Radau ref: status=%d %r t_last=%.9f T_last=%.2f nfev=%d wall=%.2f s" % (s.status, s.message, s.t[-1], s.y[3, -1], s.nfev, time.perf_counter() - w))
REF = dict(t390F=s.t_events[1][0], t_disk=s.t_events[0][0], t_A4=s.t_events[2][0]); zd = s.sol(REF["t_disk"])
REF.update(dTdt_disk=rhs(0, zd)[3], A_disk=area(zd, rhs(0, zd)), T_A4=float(s.sol(REF["t_A4"])[3])); print("REF", {k: round(float(v), 9) for k, v in REF.items()})
Tf = T0 - dH1*CB0*V/NCp - dH2*CS0*V/NCp; k2f = k20*math.exp(-E2/(R*Tf))
print("model peak dT/dt estimate (R Tf^2/E2) k2(Tf) = %.3e K/s at Tf=%.1f K; 1/k2(Tf)=%.2e s; spacing(530.0)=%.2e s" % (R*Tf*Tf/E2*k2f, Tf, 1/k2f, np.spacing(530.0)))
print("rtol  atol  steps  rhs  jac errf wall_s | rel.err: t390F t_disk dTdt_disk A_disk t_A4 | T_A4 K | peak dT/dt on steps, Tmax")
for rtol in (1e-2, 1e-3, 1e-4, 1e-6, 1e-8, 1e-10, 1e-12):
    for atol in (1e-8, 1e-15, 1e-20):
        ts, zs, w, st, _ = run(rtol, atol); m = metrics(ts, zs); e = lambda k: (m[k] - REF[k])/REF[k]
        print("%.0e %.0e %5d %5d %4d %4d %.3f | %+.1e %+.1e %+.1e %+.1e %+.1e | %.3f | %.2e %.1f" % (rtol, atol, st["steps"], st["rhs_evals"], st["jac_evals"], st["err_test_fails"], w, e("t390F"), e("t_disk"), e("dTdt_disk"), e("A_disk"), e("t_A4"), m["T_A4"], m["pk"], m["Tmax"]))
ts, zs, w, st, _ = run(1e-2, 1e-15); z = zs[-1]; X1, X2 = 1 - z[1]/CB0, 1 - z[2]/CS0
print("rtol=1e-2 final: t=%.1f T=%.2f CS=%.4f (CS0=%.4f) invariant=%+.2e K" % (ts[-1], z[3], z[2], CS0, z[3] - T0 - (-dH1*CB0*V/NCp*X1 - dH2*CS0*V/NCp*X2)))
for meth in ("Radau", "BDF", "LSODA"):
    w = time.perf_counter(); s = solve_ivp(rhs, (0, 3600), y0, method=meth, rtol=1e-6, atol=[1e-12]*3 + [1e-9, 1e-8], events=ev[:1])
    print("SciPy %-5s rtol=1e-6 status=%d nfev=%d njev=%d wall=%.3f t_disk err=%+.1e peak dT/dt on steps=%.2e Tmax=%.1f" % (meth, s.status, s.nfev, s.njev, time.perf_counter() - w, (s.t_events[0][0] - REF["t_disk"])/REF["t_disk"], max(rhs(t, y)[3] for t, y in zip(s.t, s.y.T)), s.y[3].max()))
for hmax in (None, 1.0, 0.1):
    ts, zs, w, st, _ = run(1e-6, 1e-15, hmax=hmax); m = metrics(ts, zs)
    print("rtol=1e-6 max_time_step=%s steps=%d wall=%.3f t_disk err=%+.1e t_A4 err=%+.1e" % (hmax, st["steps"], w, (m["t_disk"] - REF["t_disk"])/REF["t_disk"], (m["t_A4"] - REF["t_A4"])/REF["t_A4"]))
_, _, _, _, (net, r) = run(1e-9, 1e-15, t_end=0.0)
net.max_steps = 50
try: net.advance(3600.0)
except Exception as ex: s_ = str(ex); print("advance with max_steps=50:", s_[s_.find("Maximum"):s_.find("Maximum") + 100].replace("\n", " "))
def tmax(UA): return solve_ivp(lambda t, z: rhs(t, z, UA), (0, 3*3600), y0, method="Radau", rtol=1e-9, atol=[1e-12]*3 + [1e-9, 1e-8]).y[3].max()
print("UA[W/K] -> Tmax:", " ".join("%g:%.2f" % (u, tmax(u)) for u in (1e3, 2e3, 4e3, 6e3, 8e3)))
lo, hi = 1e3, 1e4
for _ in range(40):
    mid = math.sqrt(lo*hi); lo, hi = (lo, mid) if tmax(mid) < T390F else (mid, hi)
Q0 = V*(-dH1)*k10*math.exp(-E1/(R*T0))*CA0*CB0
print("UA_crit(sim)=%.4g W/K; lumped no-consumption: balance %.4g W/K, tangency %.4g W/K" % (hi, Q0/(T0 - Tc), Q0*E1/(R*T0*T0)))
```

`ignition.py` (GRI-Mech 3.0 tolerance sweep; DENSE vs GMRES+AdaptivePreconditioner scaling):

```python
import math, sys, time, json, subprocess, warnings; warnings.simplefilter("ignore", DeprecationWarning)
import numpy as np, cantera as ct
def area(W, T, M, k, P1, Kd=0.975):  # API 520 critical gas area, SI form, Z=1
    return W*3600/(0.03948*math.sqrt(k*(2/(k+1))**((k+1)/(k-1)))*Kd*P1/1000)*math.sqrt(T/M)*1e-6
def sweep_run(rtol, atol, hmax=None, t_end=0.05):  # GRI-Mech 3.0, CH4/air phi=1, 1100 K, 10 atm, constant volume 1 m3
    g = ct.Solution("gri30.yaml"); g.TP = 1100.0, 10*ct.one_atm; g.set_equivalence_ratio(1.0, "CH4", "O2:1.0, N2:3.76")
    r = ct.IdealGasReactor(g); r.volume = 1.0; net = ct.ReactorNet([r]); net.rtol, net.atol = rtol, atol
    if hmax: net.max_time_step = hmax
    W, rho = g.molecular_weights, r.density; bT, bP = (-1, 0, 0), (-1, 0, 0, 0, 0); w = time.perf_counter()
    while net.time < t_end:
        net.step(); d = net.get_derivative(1); iM = float(np.sum(r.Y/W))  # state = [m, V, T, Y_k]
        dT = d[2]; dP = rho*ct.gas_constant*(dT*iM + r.T*float(np.sum(d[3:]/W)))
        if dT > bT[0]: bT = (dT, net.time, r.T)
        if dP > bP[0]: bP = (dP, r.T, r.thermo.P, 1/iM, r.thermo.cp/r.thermo.cv)
    w = time.perf_counter() - w; st = net.solver_stats
    Wv = 1.0*bP[3]*bP[0]/(ct.gas_constant*bP[1])  # mass flow holding P constant at peak dP/dt (illustrative)
    return dict(tau=bT[1], dTdt=bT[0], dPdt=bP[0], A=area(Wv, bP[1], bP[3], bP[4], bP[2]), Tend=r.T, steps=st["steps"],
                rhs=st["rhs_evals"], jac=st["jac_evals"], errf=st["err_test_fails"], ncf=st["nonlinear_conv_fails"], wall=w)
def scaling_run(mech, fuel, solver):  # constant-pressure mole reactor, phi=1, 1000 K, 20 atm
    g = ct.Solution(mech); g.TP = 1000.0, 20*ct.one_atm; g.set_equivalence_ratio(1.0, fuel, "O2:1.0, N2:3.76")
    r = ct.IdealGasConstPressureMoleReactor(g); net = ct.ReactorNet([r])
    if solver == "GMRES+AP": net.preconditioner = ct.AdaptivePreconditioner()
    w = time.perf_counter(); best, tau, Tp, tp = -1, 0, r.T, 0.0
    while net.time < 0.1:
        net.step(); s = (r.T - Tp)/(net.time - tp)
        if s > best: best, tau = s, net.time
        Tp, tp = r.T, net.time
    st = net.solver_stats
    return dict(Ns=g.n_species, Nr=g.n_reactions, lst=net.linear_solver_type, tau=tau, wall=time.perf_counter() - w, steps=st["steps"],
                rhs=st["rhs_evals"], lin_rhs=st["lin_rhs_evals"], jac=st["jac_evals"], lin_iters=st["lin_iters"], prec=st["prec_evals"],
                rss_mib=int([l for l in open("/proc/self/status") if l.startswith("VmHWM")][0].split()[1])/1024)  # peak RSS of this process
if len(sys.argv) == 4: print(json.dumps(scaling_run(*sys.argv[1:]))); sys.exit()
print("cantera", ct.__version__, "sundials", ct.__sundials_version__)
ref = sweep_run(1e-12, 1e-20); r11 = sweep_run(1e-11, 1e-20)
print("REF", {k: float("%.9g" % v) for k, v in ref.items()}, "| 1e-11 vs 1e-12: tau %+.1e dTdt %+.1e dPdt %+.1e" % tuple((r11[k] - ref[k])/ref[k] for k in ("tau", "dTdt", "dPdt")))
print("rtol  atol  steps  rhs  jac errf ncf wall_s | tau_s rel.err: tau dTdt_pk dPdt_pk A | T_end")
for rtol in (1e-2, 1e-3, 1e-4, 1e-6, 1e-8, 1e-10):
    for atol in (1e-6, 1e-10, 1e-15, 1e-20):
        m = sweep_run(rtol, atol); e = lambda k: (m[k] - ref[k])/ref[k]
        print("%.0e %.0e %5d %5d %4d %4d %3d %.3f | %.6e %+.1e %+.1e %+.1e %+.1e | %.1f" % (rtol, atol, m["steps"], m["rhs"], m["jac"], m["errf"], m["ncf"], m["wall"], m["tau"], e("tau"), e("dTdt"), e("dPdt"), e("A"), m["Tend"]))
for h in (None, 1e-4, 1e-5, 1e-6):
    m = sweep_run(1e-6, 1e-15, hmax=h)
    print("rtol=1e-6 atol=1e-15 max_time_step=%s steps=%d wall=%.3f err tau %+.1e dTdt %+.1e dPdt %+.1e" % (h, m["steps"], m["wall"], *((m[k] - ref[k])/ref[k] for k in ("tau", "dTdt", "dPdt"))))
for mech, fuel in (("h2o2.yaml", "H2"), ("gri30.yaml", "CH4"), ("example_data/n-hexane-NUIG-2015.yaml", "NC6H14")):
    for solver in ("DENSE", "GMRES+AP"):
        d = json.loads(subprocess.run([sys.executable, __file__, mech, fuel, solver], capture_output=True, text=True, timeout=900).stdout.splitlines()[-1])
        print("%-36s Ns=%4d Nr=%4d %-8s(%s) tau=%.6e wall=%.3f s steps=%d rhs=%d lin_rhs=%d jac=%d lin_iters=%d prec_evals=%d maxrss=%.1f MiB" % (mech, d["Ns"], d["Nr"], solver, d["lst"], d["tau"], d["wall"], d["steps"], d["rhs"], d["lin_rhs"], d["jac"], d["lin_iters"], d["prec"], d["rss_mib"]))
```

`fluids_api520.py` (pinned fluids vs exact-constant API 520 equations; Leung golden check):

```python
import math
from decimal import Decimal, getcontext
import fluids
from fluids import safety_valve as sv
from fluids.compressible import is_critical_flow
print("fluids", fluids.__version__, fluids.__file__)
R, lb, psi, in2 = 8.314462618, 0.45359237, 6894.757293168, 0.0254**2
cSI = (1000/math.sqrt(R*1000))/(1e6/3600)            # A[mm2]=W[kg/h]/(C Kd P1[kPa]) sqrt(T Z/M)
cUSC = cSI*(1e6*in2)*(psi/1000)*math.sqrt(1.8)/lb      # A[in2]=W[lb/h]/(C Kd P1[psia]) sqrt(T[R] Z/M)
kSI = (1e6/3600)/(1000*math.sqrt(2/(R*1000)))          # A[mm2]=kSI W/(F2 Kd Kc) sqrt(T Z/(M P1 (P1-P2)))
kUSC = 1/(kSI/(1e6*in2)*lb/(psi/1000)/math.sqrt(1.8))  # A[in2]=W/(kUSC F2 Kd Kc) sqrt(...), psia
print("A exact: crit SI %.6f (0.03948) USC %.3f (520); subcrit SI %.4f (17.9) USC %.2f (735)" % (cSI, cUSC, kSI, kUSC))
print("  area effect of rounded constant: SI crit %+.1e, USC crit %+.1e, SI sub %+.1e, USC sub %+.1e" % (cSI/0.03948-1, cUSC/520-1, 17.9/kSI-1, kUSC/735-1))
C = lambda k: cSI*math.sqrt(k*(2/(k+1))**((k+1)/(k-1)))
F2 = lambda k, r: math.sqrt(k/(k-1)*r**(2/k)*(1-r**((k-1)/k))/(1-r))
def A_hand(m, T, Z, M, k, P1, P2, Kd=0.975, Kb=1.0, Kc=1.0):
    W, a, b = m*3600, P1/1e3, P2/1e3
    if P2/P1 < (2/(k+1))**(k/(k-1)): return W/(C(k)*Kd*Kb*Kc*a)*math.sqrt(T*Z/M)*1e-6
    return kSI*W/(F2(k, P2/P1)*Kd*Kc)*math.sqrt(T*Z/(M*a*(a-b)))*1e-6
m, T, Z, M, k, P1 = 24270/3600, 348.0, 0.90, 51.0, 1.11, 670e3; rc = (2/(k+1))**(k/(k-1))
print("B r_c=%.6f" % rc)
for r in (0.3, rc*(1-1e-9), rc*(1+1e-9), 0.62, 0.794, 0.9, 0.99):
    Af = sv.API520_A_g(m=m, T=T, Z=Z, MW=M, k=k, P1=P1, P2=r*P1)
    print("  r=%.9f fluids=%.10e hand(exact)=%.10e rel=%+.2e critical=%s" % (r, Af, A_hand(m, T, Z, M, k, P1, r*P1), Af/A_hand(m, T, Z, M, k, P1, r*P1)-1, is_critical_flow(P1, r*P1, k)))
for Kb in (1.0, 0.9):
    lo = sv.API520_A_g(m=m, T=T, Z=Z, MW=M, k=k, P1=P1, P2=rc*P1*(1-1e-12), Kb=Kb); hi = sv.API520_A_g(m=m, T=T, Z=Z, MW=M, k=k, P1=P1, P2=rc*P1*(1+1e-12), Kb=Kb)
    print("  jump across r_c with Kb=%.1f: A_sub/A_crit-1 = %+.3e" % (Kb, hi/lo-1))
print("C API520_C:", " ".join("%g:%.6f" % (kk, sv.API520_C(kk)) for kk in (1.0, 1.001, 1.1, 1.4, 1.67, 2.0)), "monotone:", all(sv.API520_C(1+i/1e3) < sv.API520_C(1+(i+1)/1e3) for i in range(1, 1000)))
try: sv.API520_A_g(m=m, T=T, Z=Z, MW=M, k=1.0, P1=P1)
except Exception as ex: print("  API520_A_g(k=1.0) -> %s: %s" % (type(ex).__name__, ex))
getcontext().prec = 60
def F2dec(k, r):
    k, r, o = Decimal(repr(k)), Decimal(repr(r)), Decimal(1)
    return ((k/(k-o))*r**(Decimal(2)/k)*((o - r**((k-o)/k))/(o-r))).sqrt()
F2s = lambda k, r: math.sqrt(k/(k-1)*r**(2/k)*math.expm1((k-1)/k*math.log(r))/math.expm1(math.log(r)))
print("D F2(1.11, 1-10^-e) rel.err fluids | expm1 form:", " ".join("e=%d:%+.1e|%+.0e" % (e, sv.API520_F2(1.11, 1.0, 1-10.0**-e)/float(F2dec(1.11, 1-10.0**-e))-1, F2s(1.11, 1-10.0**-e)/float(F2dec(1.11, 1-10.0**-e))-1) for e in (3, 6, 9, 12, 14, 15)))
for args in ((1.0, 1.0), ):
    try: sv.API520_F2(1.11, *args)
    except Exception as ex: print("  API520_F2(r=1) -> %s" % type(ex).__name__)
Q = 6814*1.6666666666666667e-05; rho = 0.9*999; P1l, P2l = 1.1*1724e3 + 101325, 0.2*1724e3 + 101325
print("E API520_A_l(Kw=0.97,Kv=1) = %.10f" % sv.API520_A_l(m=rho*Q, rho=rho, P1=P1l, P2=P2l, overpressure=0.1, Kd=0.65, Kw=0.97, Kc=1.0, Kv=1.0))
try: sv.API520_A_l(m=rho*Q, rho=rho, P1=P1l, P2=P2l, overpressure=0.1)
except Exception as ex: print("  API520_A_l(defaults Kv=None, mu=None) -> %s: %s" % (type(ex).__name__, ex))
M0, Vv, q, hfg, vfg, Cl, dT, G = 1500.0, 2.1, 1405.0, 668950.0, 0.2404, 1960.0, 10.5, 1238.0  # Duxbury & Wilday 1989, App. 1
A1a = M0*q/(G*(math.sqrt(Vv/M0*hfg/vfg) + math.sqrt(Cl*dT))**2)
A1b = M0*q/(G*(math.sqrt(Vv*(273+115.3)*(0.96e5/10.5)/M0) + math.sqrt(Cl*dT))**2)
print("F Leung (1a) A=%.5f m2 (published 0.040); (1b) A=%.5f m2 (published 0.0372); ERM G(4a)=%.0f (2385) G(4b)=%.0f (1907)" % (A1a, A1b, 0.65*8300*math.sqrt(383/1960), 0.65*674900/((1/3.75-1/847)*math.sqrt(1960*383))))
print("  terms sqrt(V hfg/(M0 vfg))=%.2f sqrt(C dT)=%.2f" % (math.sqrt(Vv/M0*hfg/vfg), math.sqrt(Cl*dT)))
```

`thermo_omega.py` (pinned thermo flashes; omega vs HEM):

```python
import math, os, time
import numpy as np
from scipy.optimize import brentq
import thermo
from thermo import FlashPureVLS, IAPWS95Liquid, IAPWS95Gas, iapws_constants, iapws_correlations, ChemicalConstantsPackage, CEOSGas, CEOSLiquid, PRMIX
print("thermo", thermo.__version__, thermo.__file__)
db = os.path.join(os.path.dirname(thermo.__file__), "Phase Change", "DDBST_UNIFAC_assignments.sqlite")
print("DDBST sqlite present:", os.path.exists(db))
try: ChemicalConstantsPackage.from_IDs(["propane"])
except Exception as ex:
    print("from_IDs(['propane']) -> %s: %s; sqlite now exists=%s size=%s" % (type(ex).__name__, ex, os.path.exists(db), os.path.getsize(db) if os.path.exists(db) else None))
    if os.path.exists(db) and os.path.getsize(db) == 0: os.remove(db)  # undo empty file created by sqlite3.connect
def water():
    return FlashPureVLS(iapws_constants, iapws_correlations, IAPWS95Gas(T=300, P=1e5, zs=[1]), [IAPWS95Liquid(T=300, P=1e5, zs=[1])], []), iapws_constants.MWs[0]
def propane():  # built without from_IDs: chemicals constants + PR EOS
    from chemicals import Tc, Pc, omega, MW
    from thermo import HeatCapacityGas, PropertyCorrelationsPackage, VaporPressure
    cas = "74-98-6"; c = ChemicalConstantsPackage(Tcs=[Tc(cas)], Pcs=[Pc(cas)], omegas=[omega(cas)], MWs=[MW(cas)], CASs=[cas])
    p = PropertyCorrelationsPackage(constants=c, HeatCapacityGases=[HeatCapacityGas(CASRN=cas)], VaporPressures=[VaporPressure(CASRN=cas)], skip_missing=True)
    kw = dict(Tcs=c.Tcs, Pcs=c.Pcs, omegas=c.omegas); a = dict(HeatCapacityGases=p.HeatCapacityGases, T=300, P=1e5, zs=[1])
    return FlashPureVLS(c, p, CEOSGas(PRMIX, kw, **a), [CEOSLiquid(PRMIX, kw, **a)], []), c.MWs[0]
def eta_c(w): return brentq(lambda e: e*e + (w*w - 2*w)*(1-e)**2 + 2*w*w*math.log(e) + 2*w*w*(1-e), 1e-9, 1-1e-12)
def G_omega(w, P0, v0, eb=None):
    ec = eta_c(w)
    if eb is None or eb <= ec: return ec*math.sqrt(P0/(v0*w))
    return math.sqrt(-2*(w*math.log(eb) + (w-1)*(1-eb)))*math.sqrt(P0/v0)/(w*(1/eb-1) + 1)
def hem(fl, MW, P0, S0, n=500, emin=0.2):  # isentropic HEM nozzle: G(P)=sqrt(2 int_P^P0 v dP)/v(P), maximised over P
    Ps = np.linspace(P0, emin*P0, n); vs = np.array([fl.flash(P=x, S=S0).V()/(MW/1000) for x in Ps])
    G = np.sqrt(2*np.concatenate([[0], np.cumsum(0.5*(vs[1:] + vs[:-1])*(Ps[:-1] - Ps[1:]))]))/vs
    return G, Ps
for name, mk, P0s, Psub in (("water IAPWS-95", water, (2e5, 5e5, 20e5, 80e5), 5e5), ("propane PR", propane, (10e5, 30e5), 30e5)):
    fl, MW = mk(); print("== %s saturated liquid: P0 T0 | w_sat w_9s w_9h w_7s | G_HEM eta_HEM | G_omega/G_HEM-1 for w_sat w_9s w_9h | eta_c(w_9s) | s" % name)
    for P0 in P0s:
        t = time.perf_counter(); s0 = fl.flash(P=P0, VF=0); sg = fl.flash(P=P0, VF=1); v0 = s0.V()/(MW/1000)
        w_sat = s0.Cp()*s0.T*P0/s0.V()*((sg.V() - s0.V())/(sg.H() - s0.H()))**2   # (c_pl T0 P0/v0)(v_lg/h_lg)^2
        w9s = 9*(fl.flash(P=0.9*P0, S=s0.S()).V()/s0.V() - 1); w9h = 9*(fl.flash(P=0.9*P0, H=s0.H()).V()/s0.V() - 1)
        w7s = (fl.flash(P=0.7*P0, S=s0.S()).V()/s0.V() - 1)/(1/0.7 - 1)
        G, Ps = hem(fl, MW, P0, s0.S()); k = int(np.argmax(G))
        print("  %5.1f bar %7.2f K | %.3f %.3f %.3f %.3f | %8.1f %.4f | %+.3f %+.3f %+.3f | %.4f | %.2f" % (P0/1e5, s0.T, w_sat, w9s, w9h, w7s, G[k], Ps[k]/P0,
              G_omega(w_sat, P0, v0)/G[k]-1, G_omega(w9s, P0, v0)/G[k]-1, G_omega(w9h, P0, v0)/G[k]-1, eta_c(w9s), time.perf_counter() - t))
    s0 = fl.flash(P=Psub, VF=0); v0 = s0.V()/(MW/1000); w9s = 9*(fl.flash(P=0.9*Psub, S=s0.S()).V()/s0.V() - 1)
    G, Ps = hem(fl, MW, Psub, s0.S(), n=2000, emin=0.5); e = Ps/Psub; k = int(np.argmax(G))
    print("  subcritical P0=%.0f bar (eta_b: G_HEM G_omega9s dev):" % (Psub/1e5), " ".join("%.2f: %.0f %.0f %+.3f" % (eb, np.interp(eb, e[::-1], G[::-1]) if eb > e[k] else G[k], G_omega(w9s, Psub, v0, eb), G_omega(w9s, Psub, v0, eb)/(np.interp(eb, e[::-1], G[::-1]) if eb > e[k] else G[k]) - 1) for eb in (0.95, 0.9, 0.8)))
fl, MW = water()
for x0 in (0.0, 0.01, 0.05, 0.2):
    s0 = fl.flash(P=5e5, VF=x0); v0 = s0.V()/(MW/1000); w9s = 9*(fl.flash(P=4.5e5, S=s0.S()).V()/s0.V() - 1); G, Ps = hem(fl, MW, 5e5, s0.S())
    print("== water 5 bar quality x0=%.2f: w_9s=%.3f G_HEM=%.1f G_omega=%.1f dev=%+.3f" % (x0, w9s, G.max(), G_omega(w9s, 5e5, v0), G_omega(w9s, 5e5, v0)/G.max() - 1))
for w in (0.5, 1, 2, 5, 10, 30):  # max over eta of subcritical formula == eta_c/sqrt(w) (units of sqrt(P0/v0))
    e = np.linspace(0.02, 0.999, 200000); g = np.sqrt(-2*(w*np.log(e) + (w-1)*(1-e)))/(w*(1/e-1) + 1)
    print("== w=%g argmax=%.5f eta_c=%.5f Gmax=%.6f eta_c/sqrt(w)=%.6f" % (w, e[np.argmax(g)], eta_c(w), g.max(), eta_c(w)/math.sqrt(w)))
```

## Revalidation

- **Cantera/CVODES plumbing:** diff `src/zeroD/ReactorNet.cpp` (`updateTolerances`, `initialize`, `setMaxSteps`) and `src/numerics/CVodesIntegrator.cpp` (`setTolerances`, `applyOptions`, `integrate`) against 25c1ab1c397e2991c77560b1ad5154919a12c733. Grep the `max_err_test_fails` docstring and SUNDIALS `#define MXNEF` to see whether the documented default still disagrees.
- **Tolerance behaviour:** rerun `t2_cantera.py` and `ignition.py` on a new wheel. The discriminating rows are T2 rtol 10^-2 (runaway missed?), GRI rtol 10^-6/atol 10^-6 (τ +4.6 %?) and the reference τ = 16.7263452 ms.
- **fluids:** rerun `fluids_api520.py`. Each discrepancy has a one-line oracle: `API520_A_g(k=1.0)` raises; the jump across r_c with Kb = 0.9 is −10 %; `API520_A_l` defaults raise TypeError; the F2 error at 1 − 10^-12. Also grep `fluids/` for `omega`/`two_phase` relief functions to see whether two-phase sizing has been added.
- **thermo:** rerun `thermo_omega.py`. Check whether `DDBST_UNIFAC_assignments.sqlite` is now tracked or built by `_custom_build/backend.py`; the ω and G deviations should agree to ≈ 10^-3.
- **Criteria:** `criteria.py` is self-contained (FK δ_c and Semenov values are mathematical constants of the stated models). The Stoessel examples guard the classifier.
- **T2 facts:** these depend on the CSB report (Board Voting Copy, 15 Sep 2009). If a later CSB revision is used, recheck the recipe table and the 390 °F, 400/75 psig and VSP2 rate statements.
