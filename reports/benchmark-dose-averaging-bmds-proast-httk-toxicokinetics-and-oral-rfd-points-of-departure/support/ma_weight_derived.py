#!/usr/bin/env python3
"""Derived effect of integer division in the Laplace log-evidence term on
posterior model weights, for the default dichotomous Bayesian model-averaging
set in USEPA/BMDS (pybmds) revision 0018abea713f61b0bcc9dd30821af18b61a77e77.
Standard library only. This is arithmetic, not an execution of BMDS
(Basis: derived).

Default model set (src/pybmds/session.py lines 50-60) and Bayesian prior
parameter counts (src/pybmds/types/priors.csv rows with prior_class 2):
  Hill 4, Gamma 3, Logistic 2, LogLogistic 3, LogProbit 3,
  Multistage (degree 2 in add_default_bayesian_models) 3, Probit 2,
  QuantalLinear 2, Weibull 3.

In src/bmdscore/dichotomous_entry_code.cpp line 612 the term is
`nparms / 2 * log(2 * M_PI)` with `int nparms` (bmdStruct.h line 109). For odd
k, floor(k/2) = k/2 - 1/2, so each odd-k model's log-evidence is lower by
0.5*log(2*pi) and its unnormalised weight is multiplied by (2*pi)**-0.5,
whatever the data. The script maps any 'intended' weight vector to the weight
vector produced by the integer-division expression.
"""
import math

models = {"Hill": 4, "Gamma": 3, "Logistic": 2, "LogLogistic": 3, "LogProbit": 3,
          "Multistage(2)": 3, "Probit": 2, "QuantalLinear": 2, "Weibull": 3}
factor = (2 * math.pi) ** -0.5

def as_computed(intended):
    un = {m: w * (factor if models[m] % 2 else 1.0) for m, w in intended.items()}
    s = sum(un.values())
    return {m: u / s for m, u in un.items()}

def show(title, intended):
    got = as_computed(intended)
    print(title)
    print(f"  {'model':<14} k  intended  computed")
    for m in models:
        print(f"  {m:<14} {models[m]}  {intended[m]:.4f}    {got[m]:.4f}")
    odd = [m for m in models if models[m] % 2]
    print(f"  total weight on 3-parameter models: intended={sum(intended[m] for m in odd):.4f} "
          f"computed={sum(got[m] for m in odd):.4f}")

print(f"odd-k multiplicative factor (2*pi)^-1/2 = {factor:.6f}")
show("Example 1: intended posterior weights all equal (1/9)", {m: 1 / 9 for m in models})
ex2 = {m: 0.0 for m in models}; ex2.update({"Logistic": 0.5, "LogLogistic": 0.5})
show("Example 2: intended weights split 50/50 between a 2-parameter and a 3-parameter model", ex2)
