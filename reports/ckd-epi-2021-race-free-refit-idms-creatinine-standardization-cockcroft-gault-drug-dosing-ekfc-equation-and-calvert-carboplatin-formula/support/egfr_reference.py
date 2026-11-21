#!/usr/bin/env python3
"""Reference implementations of published kidney-function formulas and derived propagation checks.

Formulas are transcribed from the cited publications (coefficients listed in REPORT.md). This is
NOT clinical software: it computes formula outputs for synthetic inputs to characterise how
implementation choices (equation form, assay calibration, indexing, caps) change the numbers.

Usage: python3 egfr_reference.py [path/to/egfr_probe.out]
If the R differential output is given, its grid is compared against these reference formulas.
"""
import math, sys

def ckdepi2021_cr(scr, age, female):            # Inker et al. 2021, mg/dL, mL/min/1.73 m^2
    k, a = (0.7, -0.241) if female else (0.9, -0.302)
    return 142 * min(scr / k, 1) ** a * max(scr / k, 1) ** -1.200 * 0.9938 ** age * (1.012 if female else 1)

def ckdepi2009_compact(scr, age, female, black=False):   # Levey et al. 2009 single-equation form
    k, a = (0.7, -0.329) if female else (0.9, -0.411)
    return (141 * min(scr / k, 1) ** a * max(scr / k, 1) ** -1.209 * 0.993 ** age
            * (1.018 if female else 1) * (1.159 if black else 1))

def ckdepi2009_table(scr, age, female, black=False):     # Levey et al. 2009 Table 2 (rounded intercepts)
    k, a = (0.7, -0.329) if female else (0.9, -0.411)
    icpt = {(True, True): 166, (False, True): 163, (True, False): 144, (False, False): 141}[(female, black)]
    return icpt * (scr / k) ** (a if scr <= k else -1.209) * 0.993 ** age

def mdrd4(scr, age, female, black=False, idms=True):     # Levey 2006/2007 (175) vs 1999-calibration (186)
    return (175 if idms else 186) * scr ** -1.154 * age ** -0.203 * (0.742 if female else 1) * (1.212 if black else 1)

def ekfc_q_umol(age, female):                             # Pottel et al. 2021 rescaling factor Q (umol/L)
    if age <= 25:
        if female:
            return math.exp(3.080 + 0.177 * age - 0.223 * math.log(age) - 0.00596 * age ** 2 + 0.0000686 * age ** 3)
        return math.exp(3.200 + 0.259 * age - 0.543 * math.log(age) - 0.00763 * age ** 2 + 0.0000790 * age ** 3)
    return 62.0 if female else 80.0

def ekfc_cr(scr_mgdl, age, female, q_mgdl_adult=None):
    q = ekfc_q_umol(age, female) / 88.4
    if age > 25 and q_mgdl_adult is not None:
        q = q_mgdl_adult[female]
    x = scr_mgdl / q
    return 107.3 * x ** (-0.322 if x < 1 else -1.132) * (1 if age <= 40 else 0.990 ** (age - 40))

def cockcroft_gault(scr, age, weight_kg, female):        # Cockcroft & Gault 1976, mL/min (not indexed)
    return (140 - age) * weight_kg / (72 * scr) * (0.85 if female else 1)

def calvert(auc, gfr_ml_min, cap=None):                  # Calvert et al. 1989: dose(mg) = AUC x (GFR + 25)
    g = gfr_ml_min if cap is None else min(gfr_ml_min, cap)
    return auc * (g + 25)

def bsa_dubois(h_cm, w_kg):
    return 0.007184 * w_kg ** 0.425 * h_cm ** 0.725

def main():
    print("## Published-form identities (derived)")
    print(f"MDRD: 186 x 0.95^1.154 = {186 * 0.95 ** 1.154:.2f}  (re-expressed intercept is 175)")
    print(f"MDRD umol/L intercept: 175 x 88.4^1.154 = {175 * 88.4 ** 1.154:.0f}  (published 30849)")
    for lab, compact, table in [("white/other F", 141 * 1.018, 144), ("Black F", 141 * 1.018 * 1.159, 166),
                                ("Black M", 141 * 1.159, 163)]:
        print(f"CKD-EPI 2009 {lab}: compact intercept {compact:.3f} vs table {table} -> table/compact = {table / compact:.5f}")
    print(f"EKFC adult Q: 62/88.4 = {62 / 88.4:.4f} mg/dL, 80/88.4 = {80 / 88.4:.4f} mg/dL;"
          f" eGFR ratio above knee (umol Q vs 0.70/0.90 mg/dL Q): F {(62 / 88.4 / 0.7) ** 1.132:.5f}, M {(80 / 88.4 / 0.9) ** 1.132:.5f}")
    print(f"Default-unit misuse: 1.0 read as umol/L = {1 / 88.4:.5f} mg/dL; F40 2021 eGFR {ckdepi2021_cr(1 / 88.4, 40, True):.2f}"
          f" vs intended {ckdepi2021_cr(1.0, 40, True):.2f}")

    print("\n## Calibration shift propagation: Scr_new = f x Scr_old (f = 0.95 is the MDRD-laboratory factor of Levey 2007;")
    print("##   it is NOT a general correction; other laboratories differed). Ratios new/old.")
    f = 0.95
    print(f"CG ratio (all Scr): {1 / f:.4f}; MDRD ratio: {f ** -1.154:.4f}")
    print(f"CKD-EPI 2021 above knee: {f ** -1.200:.4f}; below knee F: {f ** -0.241:.4f}; below knee M: {f ** -0.302:.4f}")
    print("profile, Scr_old, CG_old, CG_new, Calvert(AUC5)_old, _new, _new_capped125, relative change uncapped/capped")
    for (lab, female, age, w, scr) in [("F45 60kg", True, 45, 60, 0.6), ("F45 60kg", True, 45, 60, 0.9),
                                       ("M30 90kg", False, 30, 90, 0.8), ("M70 70kg", False, 70, 70, 1.4),
                                       ("F80 50kg", True, 80, 50, 1.1)]:
        cg0 = cockcroft_gault(scr, age, w, female); cg1 = cockcroft_gault(scr * f, age, w, female)
        d0, d1, d1c = calvert(5, cg0), calvert(5, cg1), calvert(5, cg1, cap=125)
        print(f"{lab}, {scr}, {cg0:.1f}, {cg1:.1f}, {d0:.0f}, {d1:.0f}, {d1c:.0f}, {100 * (d1 / d0 - 1):+.1f}% / {100 * (d1c / d0 - 1):+.1f}%")

    print("\n## Floor vs cap (CTEP 2010 follow-up letter: Scr floor 0.6 mg/dL OR GFR cap 125 mL/min)")
    for (female, age, w, scr) in [(True, 35, 55, 0.45), (False, 25, 110, 0.7), (True, 60, 70, 0.6)]:
        cg = cockcroft_gault(scr, age, w, female); cgf = cockcroft_gault(max(scr, 0.6), age, w, female)
        print(f"female={female} age={age} wt={w} Scr={scr}: CG {cg:.1f}; CG with floor {cgf:.1f}; capped {min(cg, 125):.1f};"
              f" both {min(cgf, 125):.1f}")

    print("\n## Indexed vs absolute GFR in the Calvert formula (eGFR is per 1.73 m^2; Calvert expects mL/min)")
    for (h, w) in [(150, 45), (170, 70), (190, 120)]:
        bsa = bsa_dubois(h, w); egfr = 90.0
        print(f"height {h} cm weight {w} kg: BSA {bsa:.2f} m^2; eGFR 90 indexed -> {egfr * bsa / 1.73:.1f} mL/min absolute;"
              f" Calvert(AUC5) indexed-as-absolute {calvert(5, egfr):.0f} vs de-indexed {calvert(5, egfr * bsa / 1.73):.0f}")

    print("\n## Properties of the reference formulas (derived by evaluation)")
    for female in (True, False):
        q25 = ekfc_q_umol(25, female); q_adult = ekfc_q_umol(25.0001, female)
        print(f"EKFC Q at age 25 ({'F' if female else 'M'}): polynomial {q25:.2f} umol/L vs adult constant {q_adult:.0f}"
              f" -> eGFR step at 25->25+ for Scr above Q: x{(q_adult / q25) ** 1.132:.4f}")
    k_ok = all(abs(ckdepi2021_cr(k * (1 + 1e-9), 50, f) - ckdepi2021_cr(k * (1 - 1e-9), 50, f)) < 1e-6
               for k, f in ((0.7, True), (0.9, False)))
    grid = [0.3 + 0.01 * i for i in range(500)]
    mono = all(ckdepi2021_cr(a, 50, True) > ckdepi2021_cr(b, 50, True) for a, b in zip(grid, grid[1:]))
    print(f"CKD-EPI 2021 continuous at the knee: {k_ok}; strictly decreasing in Scr on 0.30-5.29 mg/dL: {mono}")
    mono_age = all(ckdepi2021_cr(1.0, a, True) > ckdepi2021_cr(1.0, a + 1, True) for a in range(18, 100))
    print(f"CKD-EPI 2021 strictly decreasing in age 18-100: {mono_age}; EKFC age factor flat to 40 then 0.990/yr")

    if len(sys.argv) > 1:
        print("\n## Comparison with R differential grid (max |R - reference|; kidney.epi rounds to 2 dp)")
        cols = None; worst = {}
        for line in open(sys.argv[1], encoding='utf-8', errors='replace'):
            line = line.strip()
            if line.startswith("sex,age,scr"):
                cols = line.split(","); continue
            if cols and line and line[0] in "01" and line.count(",") == len(cols) - 1:
                v = dict(zip(cols, line.split(",")))
                female = v["sex"] == "0"; age = float(v["age"]); scr = float(v["scr"])
                ref = {"ke2021": ckdepi2021_cr(scr, age, female), "ne2021": ckdepi2021_cr(scr, age, female),
                       "ke2009": ckdepi2009_table(scr, age, female), "ne2009": ckdepi2009_compact(scr, age, female),
                       "keEKFC": ekfc_cr(scr, age, female), "neEKFC": ekfc_cr(scr, age, female, {True: 0.7, False: 0.9}),
                       "keMDRDdefault": mdrd4(scr, age, female, idms=False), "keMDRDidms": mdrd4(scr, age, female),
                       "neMDRDdefault": mdrd4(scr, age, female), "neMDRDlower_idms": mdrd4(scr, age, female, idms=False),
                       "keCG70": cockcroft_gault(scr, age, 70, female), "neCG70": cockcroft_gault(scr, age, 70, female)}
                for c, r in ref.items():
                    worst[c] = max(worst.get(c, 0.0), abs(float(v[c]) - r))
            elif cols and not line:
                cols = None if worst else cols
        for c, w in worst.items():
            print(f"{c:18s} max|diff| = {w:.6f}")
        # cross-form discrepancy
        mx = max(abs(ckdepi2009_table(s, a, True) / ckdepi2009_compact(s, a, True) - 1) for s in (0.5, 0.9, 2) for a in (20, 80))
        print(f"2009 table vs compact (female) max relative difference: {mx:.5f}")

if __name__ == "__main__":
    main()
