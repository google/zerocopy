#!/usr/bin/env python3
"""Reimplementation of two published warfarin dose-prediction equations, evaluated on
synthetic inputs to show where the equations diverge. Not a dosing tool; outputs are
algorithm-comparison numbers only.

IWPC 2009 pharmacogenetic and clinical algorithms (output = sqrt(weekly dose, mg)), with
the published coding: "Age in decades = 1 for 10-19, 2 for 20-29, etc."; indicator
variables for VKORC1 rs9923231 A/G, A/A, unknown; CYP2C9 *1/*2, *1/*3, *2/*2, *2/*3, *3/*3,
unknown; Asian, Black or African American, Missing or Mixed race; enzyme inducer;
amiodarone.
Gage 2008 pharmacogenetic equation (output = daily dose, mg = exp(linear predictor)), with
allele counts for VKORC1 -1639A (rs9923231), CYP2C9*3, CYP2C9*2; BSA (m^2, DuBois); age in
years; target INR; amiodarone; smoker; African-American race; prior DVT/PE.
Usage: python3 dosing_equations_probe.py
"""
import itertools
import json
import math

IWPC_PG = {"intercept": 5.6044, "age_decades": -0.2614, "height_cm": 0.0087, "weight_kg": 0.0128,
           "vk_AG": -0.8677, "vk_AA": -1.6974, "vk_unknown": -0.4854,
           "c_12": -0.5211, "c_13": -0.9357, "c_22": -1.0616, "c_23": -1.9206, "c_33": -2.3312,
           "c_unknown": -0.2188, "asian": -0.1092, "black": -0.2760, "mixed": -0.1032,
           "inducer": 1.1816, "amiodarone": -0.5503}
IWPC_CLIN = {"intercept": 4.0376, "age_decades": -0.2546, "height_cm": 0.0118, "weight_kg": 0.0134,
             "asian": -0.6752, "black": 0.4060, "mixed": 0.0443, "inducer": 1.2799, "amiodarone": -0.5695}
GAGE_PG = {"intercept": 0.9751, "vk_1639A": -0.3238, "bsa": 0.4317, "c3": -0.4008, "age_years": -0.00745,
           "c2": -0.2066, "target_inr": 0.2029, "amiodarone": -0.2538, "smokes": 0.0922,
           "aa_race": -0.0901, "dvt_pe": 0.0664}


def dubois_bsa(weight_kg, height_cm):
    return 0.007184 * weight_kg ** 0.425 * height_cm ** 0.725


def iwpc_pg_weekly(p, vk, c9):
    x = IWPC_PG
    s = (x["intercept"] + x["age_decades"] * (p["age"] // 10) + x["height_cm"] * p["height"]
         + x["weight_kg"] * p["weight"])
    s += {"GG": 0.0, "AG": x["vk_AG"], "AA": x["vk_AA"], "unknown": x["vk_unknown"]}[vk]
    s += {"*1/*1": 0.0, "*1/*2": x["c_12"], "*1/*3": x["c_13"], "*2/*2": x["c_22"], "*2/*3": x["c_23"],
          "*3/*3": x["c_33"], "unknown": x["c_unknown"]}[c9]
    s += {"white": 0.0, "asian": x["asian"], "black": x["black"], "mixed": x["mixed"]}[p["race"]]
    s += x["inducer"] * p["inducer"] + x["amiodarone"] * p["amiodarone"]
    return s * s


def iwpc_clin_weekly(p):
    x = IWPC_CLIN
    s = (x["intercept"] + x["age_decades"] * (p["age"] // 10) + x["height_cm"] * p["height"]
         + x["weight_kg"] * p["weight"])
    s += {"white": 0.0, "asian": x["asian"], "black": x["black"], "mixed": x["mixed"]}[p["race"]]
    s += x["inducer"] * p["inducer"] + x["amiodarone"] * p["amiodarone"]
    return s * s


def gage_pg_weekly(p, vk, c9):
    x = GAGE_PG
    a = {"GG": 0, "AG": 1, "AA": 2}[vk]
    alleles = c9.split("/")
    n2, n3 = alleles.count("*2"), alleles.count("*3")
    lp = (x["intercept"] + x["vk_1639A"] * a + x["bsa"] * dubois_bsa(p["weight"], p["height"])
          + x["c3"] * n3 + x["age_years"] * p["age"] + x["c2"] * n2 + x["target_inr"] * p["target_inr"]
          + x["amiodarone"] * p["amiodarone"] + x["smokes"] * p["smokes"]
          + x["aa_race"] * (1 if p["race"] == "black" else 0) + x["dvt_pe"] * p["dvt_pe"])
    return 7.0 * math.exp(lp)


PROFILES = {
    "P1_65y_170cm_75kg_white": dict(age=65, height=170, weight=75, race="white", inducer=0,
                                    amiodarone=0, target_inr=2.5, smokes=0, dvt_pe=0),
    "P2_45y_160cm_60kg_asian": dict(age=45, height=160, weight=60, race="asian", inducer=0,
                                    amiodarone=0, target_inr=2.5, smokes=0, dvt_pe=0),
    "P3_55y_178cm_95kg_black": dict(age=55, height=178, weight=95, race="black", inducer=0,
                                    amiodarone=0, target_inr=2.5, smokes=0, dvt_pe=0),
    "P4_80y_165cm_65kg_white_amiodarone": dict(age=80, height=165, weight=65, race="white",
                                               inducer=0, amiodarone=1, target_inr=2.5,
                                               smokes=0, dvt_pe=0),
}
VK = ["GG", "AG", "AA"]
C9 = ["*1/*1", "*1/*2", "*1/*3", "*2/*2", "*2/*3", "*3/*3"]


def grid():
    rows = []
    for (pname, p), vk, c9 in itertools.product(PROFILES.items(), VK, C9):
        iw, ga = iwpc_pg_weekly(p, vk, c9), gage_pg_weekly(p, vk, c9)
        rows.append({"profile": pname, "VKORC1": vk, "CYP2C9": c9,
                     "iwpc_pg_mg_wk": round(iw, 1), "gage_pg_mg_wk": round(ga, 1),
                     "ratio_gage_over_iwpc": round(ga / iw, 3)})
    return rows


def coding_sensitivity():
    """Same synthetic person P1 with VKORC1 AG and a CYP2C9 variant outside *2/*3 (for
    example *8): IWPC score if coded *1/*1 versus coded 'CYP2C9 genotype unknown';
    and if VKORC1 is coded 'unknown' instead of AG or AA."""
    p = PROFILES["P1_65y_170cm_75kg_white"]
    return {
        "P1_AG_c9_as_1_1": round(iwpc_pg_weekly(p, "AG", "*1/*1"), 1),
        "P1_AG_c9_as_unknown": round(iwpc_pg_weekly(p, "AG", "unknown"), 1),
        "P1_AG_c9_as_1_2_(same_decrease_class)": round(iwpc_pg_weekly(p, "AG", "*1/*2"), 1),
        "P1_vk_AA_1_1": round(iwpc_pg_weekly(p, "AA", "*1/*1"), 1),
        "P1_vk_unknown_1_1": round(iwpc_pg_weekly(p, "unknown", "*1/*1"), 1),
        "P1_vk_GG_1_1": round(iwpc_pg_weekly(p, "GG", "*1/*1"), 1),
    }


def age_coding():
    """IWPC uses the decade bin index; show the step at a decade boundary vs Gage's
    continuous age term (same P1 otherwise, VKORC1 AG, CYP2C9 *1/*1)."""
    out = {}
    for age in (59, 60, 69, 70):
        p = dict(PROFILES["P1_65y_170cm_75kg_white"], age=age)
        out[str(age)] = {"iwpc_pg": round(iwpc_pg_weekly(p, "AG", "*1/*1"), 2),
                         "gage_pg": round(gage_pg_weekly(p, "AG", "*1/*1"), 2)}
    return out


def main():
    rows = grid()
    ratios = [r["ratio_gage_over_iwpc"] for r in rows]
    per_profile = {}
    for pname, p in PROFILES.items():
        sub = [r for r in rows if r["profile"] == pname]
        per_profile[pname] = {
            "iwpc_clinical_mg_wk": round(iwpc_clin_weekly(p), 1),
            "iwpc_pg_min_max": [min(r["iwpc_pg_mg_wk"] for r in sub),
                                max(r["iwpc_pg_mg_wk"] for r in sub)],
            "gage_pg_min_max": [min(r["gage_pg_mg_wk"] for r in sub),
                                max(r["gage_pg_mg_wk"] for r in sub)],
            "bsa_m2": round(dubois_bsa(p["weight"], p["height"]), 3),
        }
    worst = sorted(rows, key=lambda r: abs(math.log(r["ratio_gage_over_iwpc"])), reverse=True)[:5]
    out = {
        "n_rows": len(rows),
        "ratio_gage_over_iwpc_min_max": [min(ratios), max(ratios)],
        "rows_differing_by_more_than_20pct": sum(1 for x in ratios if x > 1.2 or x < 1 / 1.2),
        "largest_divergences": worst,
        "per_profile": per_profile,
        "coding_sensitivity": coding_sensitivity(),
        "age_coding": age_coding(),
        "grid": rows,
    }
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
