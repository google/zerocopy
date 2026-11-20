#!/usr/bin/env python3
"""Recompute threshold metrics from counts published in two external
evaluations of a deployed proprietary sepsis model (standard library only).

Inputs are copied from the published papers (see REPORT.md, Evidence):
  Wong et al., JAMA Intern Med 2021;181(8):1065-1070 (doi:10.1001/jamainternmed.2021.2626)
    38,455 hospitalizations; 2,552 with sepsis; 6,971 hospitalizations with a
    score >= 6 at any time before onset; 1,709 sepsis hospitalizations never
    reaching >= 6 before onset; 183 flagged sepsis hospitalizations without
    timely antibiotics.
  Wong et al., JAMA Netw Open 2021;4(11):e2135286 (doi:10.1001/jamanetworkopen.2021.35286)
    3 weeks before vs after first COVID-19 case: census 10,159 -> 6,634;
    alerts/day 953 -> 1,363.
Nothing here is new measurement; it is a consistency check (Basis: derived).
"""
N, S, ALERTED, MISSED, FLAG_NO_ABX = 38455, 2552, 6971, 1709, 183
TP = S - MISSED
FP = ALERTED - TP
NEG = N - S
FN = MISSED
TN = NEG - FP
sens = TP / S
spec = TN / NEG
ppv = TP / ALERTED
npv = TN / (TN + FN)
print(f"prevalence           = {S}/{N} = {S/N:.4f}")
print(f"sensitivity          = {TP}/{S} = {sens:.4f}   (paper: 33%)")
print(f"specificity          = {TN}/{NEG} = {spec:.4f}   (paper: 83%)")
print(f"PPV                  = {TP}/{ALERTED} = {ppv:.4f}   (paper: 12%)")
print(f"NPV                  = {TN}/{TN+FN} = {npv:.4f}   (paper: 95%)")
print(f"alerted fraction     = {ALERTED}/{N} = {ALERTED/N:.4f}   (paper: 18%)")
print(f"number needed to evaluate (1/PPV) = {1/ppv:.2f}   (paper: 8)")
print(f"missed fraction      = {MISSED}/{S} = {MISSED/S:.4f}   (paper: 67%)")
print(f"flagged w/o timely abx = {FLAG_NO_ABX}/{S} = {FLAG_NO_ABX/S:.4f}   (paper: 7%)")
# Bayes-rule cross-check using only rounded sens/spec/prevalence
p = S / N
ppv_bayes = 0.33 * p / (0.33 * p + (1 - 0.83) * (1 - p))
print(f"PPV from rounded sens=0.33, spec=0.83, prevalence={p:.4f}: {ppv_bayes:.4f}")
alert_bayes = 0.33 * p + 0.17 * (1 - p)
print(f"alert fraction from rounded sens/spec: {alert_bayes:.4f}")
print()
c0, c1, a0, a1 = 10159, 6634, 953, 1363
print(f"COVID-19 alert study: alert proportion {a0}/{c0} = {a0/c0:.4f} -> {a1}/{c1} = {a1/c1:.4f}")
print(f"  census change = {c1/c0 - 1:+.4f}; alert-count change = {a1/a0 - 1:+.4f}")
