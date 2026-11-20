#!/usr/bin/env python3
"""Python transliteration probe of selected transplantr R functions vs. OPTN policy text.

NOT transplantr itself: R was not available, so each R function below is transliterated
line by line (R `ifelse` -> elementwise, R `max` -> maximum over ALL arguments, `log` -> ln).
Lookup tables (kdpi_lookup, epts_lookup) are parsed from the R sources fetched at the pinned
revision, not hand-copied. Reference formulas are transcribed from OPTN documents:
  * OPTN "Improving Liver Allocation: MELD, PELD, Status 1A, Status 1B" policy notice
    (Board approved June 27, 2022): pre-2023 MELD(i)/MELD-Na text and MELD 3.0 text.
  * OPTN "A Guide to Calculating and Interpreting the KDPI" (updated April 23, 2026):
    refit KDRI coefficients (implemented October 31, 2024) and its worked example.
  * OPTN "A Guide to Calculating and Interpreting the EPTS Score" (updated April 07, 2026).
Usage: python3 transplantr_translit_probe.py   (needs network access to raw.githubusercontent.com)
"""
import math, re, urllib.request

REV = "9662038338390be81ef91a46131e7ddfb348ca9c"
BASE = f"https://raw.githubusercontent.com/johnasher/transplantr/{REV}/R/"
ln = math.log

def fetch(name):
    req = urllib.request.Request(BASE + name, headers={"User-Agent": "reference-probe"})
    return urllib.request.urlopen(req, timeout=60).read().decode()

def parse_case_when(src, fn):
    body = src[src.index(fn + " = function"):]
    body = body[:body.index("TRUE ~")]
    return [(float(a), int(b)) for a, b in re.findall(r"<=\s*([0-9.]+)\s*~\s*(\d+)", body)]

def lookup(table, x, default):
    for thr, val in table:
        if x <= thr:
            return val
    return default

# ---------- transliterations of transplantr (R/liver.R, R/uskdri.R, R/epts.R, R/liver_scores.R) ----------
def tr_meld(INR, bili, creat, dialysis, units="SI"):
    if units == "SI":
        bili, creat = bili / 17.1, creat / 88.4
    bili = 1 if bili < 1 else bili
    creat = 1 if creat < 1 else creat
    creat = 4 if creat > 4 else creat
    INR = 1 if INR < 1 else INR
    creat = 4.0 if dialysis == 1 else creat
    meldi = 0.957 * ln(creat) + 0.378 * ln(bili) + 1.12 * ln(INR) + 0.643
    return 10 * round(meldi, 10)

def tr_meld_na(INR, bili, creat, Na, dialysis, units="SI"):
    if units == "SI":
        bili, creat = bili / 17.1, creat / 88.4
    bili = 1 if bili < 1 else bili
    creat = 1 if creat < 1 else creat          # note: no upper cap at 4 in meld_na
    INR = 1 if INR < 1 else INR
    creat = 4.0 if dialysis == 1 else creat
    m = 10 * round(0.957 * ln(creat) + 0.378 * ln(bili) + 1.12 * ln(INR) + 0.643, 10)
    m0 = m - Na - (0.025 * m * (140 - Na)) + 140
    return m0 if m > 11 else m

def tr_ukeld(INR, bili, creat, Na, units="SI"):
    if units == "US":
        bili, creat = bili / 17.1, creat / 88.4
    return 5.395 * ln(INR) + 1.485 * ln(creat) + 3.13 * ln(bili) - 81.565 * ln(Na) + 435

def tr_ukeld_US(INR, bili, creat, Na):
    return 5.395 * ln(INR) + 1.485 * ln(creat / 88.4) + 3.13 * ln(bili / 17.1) - 81.565 * ln(Na) + 435

def tr_uskdri(age, height, weight, eth, htn, dm, cva, creat, hcv, dcd, scaling=1, units="SI"):
    if units == "SI":
        creat = creat / 88.4
    agevar = 0.0128 * (age - 40) + (-0.0194 * (age - 18) if age < 18 else 0) + (0.0107 * (age - 50) if age > 50 else 0)
    heightvar = -0.0464 * (height - 170) / 10
    weightvar = -0.0199 * (weight - 80) / 5 if weight < 80 else 0
    ethvar = 0.1790 if eth == "black" else 0
    creatvar = 0.2200 * (creat - 1) + (-0.2090 * (creat - 1.5) if creat > 1.5 else 0)
    x = agevar + heightvar + weightvar + ethvar + 0.1260 * htn + 0.1300 * dm + 0.0881 * cva + creatvar + 0.2400 * hcv + 0.1330 * dcd
    return math.exp(x) / scaling

def tr_raw_epts_vector(ages, dm, prev_tx, dx):
    # R: agebase = max(age - 25, 0)  -- `max` collapses the whole vector to one number
    agebase = max([a - 25 for a in ages] + [0])
    out = []
    for _ in ages:
        log_dx = ln(dx + 1); dxnull = 1 if dx == 0 else 0
        out.append(0.047 * agebase - 0.015 * dm * agebase + 0.398 * prev_tx - 0.237 * dm * prev_tx
                   + 0.315 * log_dx - 0.099 * dm * log_dx + 0.130 * dxnull - 0.348 * dm * dxnull + 1.262 * dm)
    return out

def tr_soft_points(Albumin, DonorSCr, Units="SI"):
    # soft(): converts once, then calls p_soft()/soft2() WITHOUT Units, whose default "SI" converts again
    if Units == "SI":
        Albumin, DonorSCr = Albumin / 10, DonorSCr / 88.4
    alb_in_psoft = Albumin / 10            # p_soft default Units = "SI"
    scr_in_soft2 = DonorSCr / 88.4         # soft2 default Units = "SI"
    return (2 if alb_in_psoft < 2.0 else 0), (2 if scr_in_soft2 > 1.5 else 0), alb_in_psoft, scr_in_soft2

# ---------- OPTN reference formulas ----------
def optn_meld_na_pre2023(INR, bili, creat_mgdl, Na, dialysis):
    bili, INR = max(bili, 1.0), max(INR, 1.0)
    creat = min(max(creat_mgdl, 1.0), 4.0)
    if dialysis: creat = 4.0
    meldi = round(0.957 * ln(creat) + 0.378 * ln(bili) + 1.120 * ln(INR) + 0.643, 1) * 10
    meldi = min(meldi, 40)
    if meldi > 11:
        na = min(max(Na, 125), 137)
        return meldi + 1.32 * (137 - na) - (0.033 * meldi * (137 - na)), meldi
    return meldi, meldi

def optn_meld3(INR, bili, creat_mgdl, Na, albumin, female, dialysis):
    bili, INR = max(bili, 1.0), max(INR, 1.0)
    creat = max(creat_mgdl, 1.0)
    if creat > 3.0 or dialysis: creat = 3.0
    na = min(max(Na, 125), 137); alb = min(max(albumin, 1.5), 3.5)
    v = (1.33 * female + 4.56 * ln(bili) + 0.82 * (137 - na) - 0.24 * (137 - na) * ln(bili) + 9.09 * ln(INR)
         + 11.14 * ln(creat) + 1.85 * (3.5 - alb) - 1.83 * (3.5 - alb) * ln(creat) + 6)
    return min(max(round(v), 6), 40), v

def optn_kdri_refit(age, height, weight, htn, dm, cva, creat, dcd):
    x = (0.0092 * (age - 40) + (0.0113 * (age - 18) if age < 18 else 0) + (0.0067 * (age - 50) if age > 50 else 0)
         - 0.0557 * (height - 170) / 10 - (0.0333 * (weight - 80) / 5 if weight < 80 else 0)
         + 0.1106 * htn + 0.2577 * dm + 0.0743 * cva + 0.2128 * (creat - 1)
         - (0.2199 * (creat - 1.5) if creat > 1.5 else 0) + 0.1966 * dcd)
    return x, math.exp(x)

def main():
    kdpi_tab = parse_case_when(fetch("uskdri.R"), "kdpi_lookup")
    epts_tab = parse_case_when(fetch("epts.R"), "epts_lookup")
    print(f"parsed kdpi_lookup thresholds: {len(kdpi_tab)} (values {kdpi_tab[0][1]}..{kdpi_tab[-1][1]})")
    epts_vals = [v for _, v in epts_tab]
    print(f"parsed epts_lookup thresholds: {len(epts_tab)}; last explicit bin {epts_tab[-1]}; "
          f"missing percentile values in 0..100: {sorted(set(range(101)) - set(epts_vals) - {100})}")

    print("\n[1] MELD rounding: transplantr test fixture meld(INR=2.0, bili=54 umol/L, creat=170 umol/L)")
    t = tr_meld(2.0, 54, 170, 0)
    _, meldi = optn_meld_na_pre2023(2.0, 54 / 17.1, 170 / 88.4, 137, 0)
    print(f"    transplantr = {t:.3f}; OPTN MELD(i) rounded to tenth then x10 = {meldi:.1f}")

    print("\n[2] Creatinine 6.0 mg/dL, not on dialysis, INR 1.5, bili 3.0 mg/dL, Na 137 (US units)")
    print(f"    transplantr meld = {tr_meld(1.5, 3.0, 6.0, 0, 'US'):.3f}; meld_na = {tr_meld_na(1.5, 3.0, 6.0, 137, 0, 'US'):.3f}; "
          f"OPTN pre-2023 MELD-Na = {optn_meld_na_pre2023(1.5, 3.0, 6.0, 137, 0)[0]:.3f}")

    print("\n[3] Sodium handling, INR 1.8, bili 2 mg/dL, creat 2 mg/dL (transplantr test fixture uses Na 131)")
    for na in (120, 125, 131, 137, 140, 145):
        t = tr_meld_na(1.8, 2, 2, na, 0, "US")
        o = optn_meld_na_pre2023(1.8, 2, 2, na, 0)[0]
        print(f"    Na={na}: transplantr meld_na = {t:.3f}   OPTN pre-2023 MELD-Na = {o:.3f}   diff = {t - o:+.3f}")

    print("\n[4] UKELD unit handling: SI fixture ukeld(1.0, 212, 54, 126) and the same patient in US units")
    si = tr_ukeld(1.0, 212, 54, 126)
    us_args = (1.0, 212 / 17.1, 54 / 88.4, 126)
    print(f"    ukeld SI = {si:.2f}; ukeld(units='US') = {tr_ukeld(*us_args, units='US'):.2f}; ukeld_US = {tr_ukeld_US(*us_args):.2f}")
    print(f"    correct conversion (mg/dL x 17.1, x 88.4) would give {tr_ukeld(1.0, us_args[1] * 17.1, us_args[2] * 88.4, 126):.2f}")

    print("\n[5] EPTS: vector call raw_epts(age = c(30, 60), dm = 0, prev_tx = 0, dx = 0)")
    v = tr_raw_epts_vector([30, 60], 0, 0, 0)
    s = [tr_raw_epts_vector([a], 0, 0, 0)[0] for a in (30, 60)]
    print(f"    vector call -> {[round(x, 4) for x in v]}; scalar calls -> {[round(x, 4) for x in s]}")
    hi = epts_tab[-1][0]
    print(f"    raw EPTS just above the last explicit threshold ({hi}) maps to {lookup(epts_tab, hi + 1e-6, 100)}")

    print("\n[6] KDRI/KDPI: OPTN KDPI-guide worked example (age 52, 183 cm, 81 kg, HTN, no DM, CVA, creat 1.7 mg/dL, DCD)")
    x, raw = optn_kdri_refit(52, 183, 81, 1, 0, 1, 1.7, 1)
    scale = 1.40436817065005
    print(f"    OPTN refit: Xb = {x:.5f}, KDRI_RAO = {raw:.11f}, scaled = {raw / scale:.11f} (guide: 0.53787, 1.71235565748184, 1.21930679808076 -> KDPI 72%)")
    tr_raw = tr_uskdri(52, 183, 81, "white", 1, 0, 1, 1.7, 0, 1, units="US")
    print(f"    transplantr uskdri (Rao 2009 coefficients, non-black, HCV-) = {tr_raw:.5f}; scaled by 2024 factor = {tr_raw / scale:.5f}; "
          f"kdpi_lookup(scaled) = {lookup(kdpi_tab, tr_raw / scale, 100)}; kdpi_lookup(refit scaled) = {lookup(kdpi_tab, raw / scale, 100)}")
    print(f"    transplantr kdpi() with its default scaling = 1 -> kdpi_lookup({tr_raw:.5f}) = {lookup(kdpi_tab, tr_raw, 100)}; "
          f"with the 2018 factor 1.250609 named in its documentation -> kdpi_lookup({tr_raw / 1.250609:.5f}) = {lookup(kdpi_tab, tr_raw / 1.250609, 100)}")
    tr_blk = tr_uskdri(52, 183, 81, "black", 1, 0, 1, 1.7, 0, 1, units="US")
    print(f"    same donor with eth='black': transplantr scaled = {tr_blk / scale:.5f}, kdpi_lookup = {lookup(kdpi_tab, tr_blk / scale, 100)}")

    print("\n[7] SOFT unit double conversion: soft(Albumin = 30 g/L, DonorSCr = 140 umol/L)")
    a, c, alb, scr = tr_soft_points(30, 140)
    print(f"    albumin seen by p_soft = {alb:.3f} g/dL -> {a} points (3.0 g/dL intended -> 0); "
          f"creatinine seen by soft2 = {scr:.4f} mg/dL -> {c} points (1.58 mg/dL intended -> 2)")

    print("\n[8] Rank order: two adult candidates, transplantr meld_na vs OPTN MELD 3.0")
    A = dict(INR=1.6, bili=2.5, creat=1.0, Na=137, albumin=2.0, female=1)
    B = dict(INR=1.7, bili=3.0, creat=1.1, Na=137, albumin=3.5, female=0)
    for name, c in (("A", A), ("B", B)):
        t = tr_meld_na(c["INR"], c["bili"], c["creat"], c["Na"], 0, "US")
        m3, m3raw = optn_meld3(c["INR"], c["bili"], c["creat"], c["Na"], c["albumin"], c["female"], 0)
        print(f"    {name}: {c} -> transplantr meld_na = {t:.2f}; OPTN MELD 3.0 = {m3} (unrounded {m3raw:.2f})")

if __name__ == "__main__":
    main()
