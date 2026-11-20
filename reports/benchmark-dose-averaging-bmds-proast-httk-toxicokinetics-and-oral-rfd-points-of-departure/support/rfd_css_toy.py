#!/usr/bin/env python3
"""TOY MODEL: deterministic versus probabilistic composition of uncertainty
factors, and steady-state reverse dosimetry arithmetic. Requires numpy.

Part A (uncertainty factors). The deterministic reference-dose recipe divides a
point of departure by a product of factors (often 10 x 10). If, purely for
illustration, each factor of 10 is read as the 95th percentile of an
independent lognormal with median 1, the 95th percentile of the PRODUCT is
smaller than the product of the 95th percentiles. The lognormal inputs here
are ILLUSTRATIVE ASSUMPTIONS chosen by the author, not WHO/IPCS or EPA
default distributions.

Part B (reverse dosimetry). The steady-state relation transcribed from
USEPA/CompTox-ExpoCast-httk revision f6605eebc6eb5a483a8824dce6cbddb36c8fb091,
httk/R/calc_analytic_css_3compss.R lines 223-229, and the well-stirred liver
clearance from httk/R/calc_hep_clearance.R line 272:
    Css   = dose_rate * Fabsgut * Fhep / (Qgfr * Fup + CLh)
    CLh   = Qliver * Fup * Clint / (Qliver + Fup * Clint)
and the oral-equivalent dose from httk/R/calc_mc_oral_equiv.R line 399:
    dose  = conc / Css(at 1 mg/kg/day)
Parameter values below are HYPOTHETICAL round numbers, not httk data for any
chemical. Fhep is taken as 1 here for simplicity (httk computes it).
"""
import math
import numpy as np

rng = np.random.default_rng(7)
z95 = 1.6448536269514722
sigma = math.log(10) / z95
print("Part A: two independent lognormal factors, median 1, P95 = 10 each (illustrative)")
print(f"  sigma (log scale) = ln(10)/z95 = {sigma:.4f}")
analytic = math.exp(z95 * math.sqrt(2) * sigma)
print(f"  analytic P95 of product = exp(z95*sqrt(2)*sigma) = {analytic:.2f}  vs product of P95s = 100")
draws = np.exp(rng.normal(0, sigma, 2_000_000) + rng.normal(0, sigma, 2_000_000))
print(f"  Monte Carlo P95 of product (2e6 draws) = {np.quantile(draws, 0.95):.2f}")
print(f"  P(product > 100) = {np.mean(draws > 100):.5f}")
pod = 1.65  # illustrative POD in mg/kg-day (the model-averaged BMDL of a quantal example in EFSA 2022, Annex)
print(f"  deterministic RfD = {pod} / 100 = {pod/100:.4f} mg/kg-day; 'P95-product' RfD = {pod/analytic:.4f} mg/kg-day")
print()
print("Part B: steady-state Css and oral equivalent dose (hypothetical parameters)")
BW = 70.0
Qgfrc, Qliverc = 6.5, 90.0   # L/h/kg^0.75 (hypothetical round numbers)
Qgfr, Qliver = Qgfrc / BW**0.25, Qliverc / BW**0.25
for fup, clint in [(0.5, 1.0), (0.05, 1.0), (0.5, 50.0), (0.01, 50.0)]:
    clh = Qliver * fup * clint / (Qliver + fup * clint)
    dose_rate = 1.0 / 24.0  # 1 mg/kg/day expressed per hour
    css = dose_rate * 1.0 * 1.0 / (Qgfr * fup + clh)
    print(f"  Fup={fup:<5} Clint={clint:<5} CLh={clh:.4f} L/h/kg  Css(1 mg/kg/d)={css:.4f} mg/L  "
          f"dose for 1 mg/L = {1.0/css:.4f} mg/kg/d")
