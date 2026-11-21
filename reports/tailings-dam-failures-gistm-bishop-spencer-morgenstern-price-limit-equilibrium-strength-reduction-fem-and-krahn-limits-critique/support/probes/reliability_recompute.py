#!/usr/bin/env python3
"""Derived recomputation of the reliability indices in Christian, Ladd & Baecher
(1994), Table 7 (James Bay dikes), from the tabulated E[F] and variance
components, and comparison with the lognormal reliability index used by the
Taylor Series Probability Method (TSPM) formula
    beta_ln = ln(F / sqrt(1 + V^2)) / sqrt(ln(1 + V^2)),   V = sigma_F / F
when (a) the spatial-variability variance is reduced by averaging along the slip
surface, as in the paper, and (b) it is not reduced (the TSPM as usually applied
perturbs point values and has no averaging step).

All inputs are copied from the paper's Tables 5-7; nothing here is a new
measurement of any embankment.
"""
import math

def phi(x):
    return 0.5 * (1 + math.erf(x / math.sqrt(2)))

cases = [
    # name, E[F], V_spatial_unreduced, reduction_ratio, V_systematic, V_model_error_or_None, E[F]_with_model_error
    ("single stage H=6 m",  1.500, None,   0.7, 0.024, 0.012, 1.575),
    ("single stage H=12 m", 1.453, 0.0459, 0.2, 0.0199, 0.011, 1.526),
    ("multistage H=23 m",   1.427, None,   None, 0.0122, 0.0110, 1.498),
]
# Reduced spatial variances as tabulated in Table 7 (column 3):
reduced_spatial = {"single stage H=6 m": 0.050, "single stage H=12 m": 0.009, "multistage H=23 m": 0.0012}
published_beta = {"single stage H=6 m": (1.84, 1.96), "single stage H=12 m": (2.66, 2.60), "multistage H=23 m": (3.69, 3.19)}

print("case | E[F] | V_total(reduced) | beta_normal(recomputed) | beta_published | p_f normal | beta_ln (TSPM formula) | p_f lognormal")
for name, EF, Vsp_un, R, Vsys, Vme, EFme in cases:
    Vsp = reduced_spatial[name]
    Vt = Vsp + Vsys
    b = (EF - 1) / math.sqrt(Vt)
    cov = math.sqrt(Vt) / EF
    bln = math.log(EF / math.sqrt(1 + cov ** 2)) / math.sqrt(math.log(1 + cov ** 2))
    print(f"{name} | {EF:.3f} | {Vt:.4f} | {b:.2f} | {published_beta[name][0]} | {1-phi(b):.2e} | {bln:.2f} | {1-phi(bln):.2e}")

print()
print("H=12 m without spatial averaging (V_spatial unreduced = 0.0459):")
EF = 1.453; Vt = 0.0459 + 0.0199
b = (EF - 1) / math.sqrt(Vt); cov = math.sqrt(Vt) / EF
bln = math.log(EF / math.sqrt(1 + cov ** 2)) / math.sqrt(math.log(1 + cov ** 2))
print(f"V_total={Vt:.4f} beta_normal={b:.2f} p_f={1-phi(b):.2e} beta_ln={bln:.2f} p_f_ln={1-phi(bln):.2e}")
print()
print("With model error (Table 7 second rows): E[F] x 1.05, V[e] = (0.07 E[F])^2 as tabulated")
for name, EF, Vsp_un, R, Vsys, Vme, EFme in cases:
    Ve = (0.07 * EFme) ** 2
    Vt = reduced_spatial[name] + Vsys + Ve
    b = (EFme - 1) / math.sqrt(Vt)
    print(f"{name}: E[F]={EFme:.3f} V[e]={Ve:.4f} V_total={Vt:.4f} beta={b:.2f} (published {published_beta[name][1]}; differences of 0.03 or less reflect rounding of tabulated variances)")
