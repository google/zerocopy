#!/usr/bin/env python3
"""Derive the per-geolevel and per-query zCDP allocation of the 2020 redistricting
(PL 94-171) US persons run from the values in the production configuration and
strategy class, using exact rational arithmetic, and (optionally) run the release's
own zCDP -> (epsilon, delta) conversion (programs/engine/curve.py) on them.

Inputs are transcribed from uscensusbureau/DAS_2020_Redistricting_Production_Code
at 289ee463936a6f0efcf2e378abe410ec01d0e140:
  source/configs/production/pl94/person_default.ini:70   global_scale = 339/542
  source/configs/production/pl94/person_US.ini:29        geolevel_budget_prop (topdown order US..Block)
  source/programs/strategies/strategies.py:873-914        ProductionCandidate20210527US_mult8_add02_dsepJune3
Arithmetic follows source/programs/engine/engine_utils.py:484-492
  (inverse_scale = dpq_prop * geolevel_prop / global_scale**2, i.e. 1/sigma^2)
and source/programs/engine/budget.py:160 (rho = 1 / global_scale**2).

Usage:
  python3 probe_budget.py                      # exact table only (stdlib)
  python3 probe_budget.py --curve <engine_dir> # also run curve.zCDPEpsDeltaCurve
"""
import sys
from fractions import Fraction as Fr

GLOBAL_SCALE = Fr(339, 542)
LEVELS = ["US", "State", "County", "Tract", "Block_Group", "Block"]
GEO_PROP = dict(zip(LEVELS, [Fr(104, 4099), Fr(1440, 4099), Fr(447, 4099), Fr(687, 4099), Fr(1256, 4099), Fr(165, 4099)]))
Q11 = ("total", "cenrace", "hispanic", "votingage", "hhinstlevels", "hhgq", "hispanic * cenrace",
       "votingage * cenrace", "votingage * hispanic", "votingage * hispanic * cenrace", "detailed")
QUERIES = {
    "US": (Q11[1:], (Fr(52, 4097), Fr(26, 4097), Fr(26, 4097), Fr(26, 4097), Fr(26, 4097), Fr(130, 4097), Fr(130, 4097), Fr(26, 4097), Fr(26, 241), Fr(189, 241))),
    "State": (Q11, (Fr(3773, 4097), Fr(6, 4097), Fr(6, 4097), Fr(6, 4097), Fr(6, 4097), Fr(6, 4097), Fr(12, 4097), Fr(12, 4097), Fr(6, 4097), Fr(2, 241), Fr(230, 4097))),
    "County": (Q11, (Fr(3126, 4097), Fr(10, 4097), Fr(10, 4097), Fr(10, 4097), Fr(10, 4097), Fr(10, 4097), Fr(28, 4097), Fr(28, 4097), Fr(10, 4097), Fr(101, 4097), Fr(754, 4097))),
    "Tract": (Q11, (Fr(1567, 4102), Fr(4, 2051), Fr(5, 4102), Fr(5, 4102), Fr(5, 4102), Fr(5, 4102), Fr(1933, 4102), Fr(10, 2051), Fr(5, 4102), Fr(67, 4102), Fr(241, 2051))),
    "Block_Group": (Q11, (Fr(1705, 4099), Fr(3, 4099), Fr(3, 4099), Fr(3, 4099), Fr(3, 4099), Fr(3, 4099), Fr(1055, 4099), Fr(9, 4099), Fr(3, 4099), Fr(24, 4099), Fr(1288, 4099))),
    "Block": (Q11, (Fr(5, 4097), Fr(9, 4097), Fr(5, 4097), Fr(5, 4097), Fr(5, 4097), Fr(5, 4097), Fr(21, 4097), Fr(21, 4097), Fr(5, 4097), Fr(71, 4097), Fr(3945, 4097))),
}


def main():
    rho = 1 / GLOBAL_SCALE ** 2
    print(f"global rho = 1/global_scale^2 = {rho} = {float(rho):.6f}")
    assert sum(GEO_PROP.values()) == 1, "geolevel props must sum to exactly 1"
    total_rho = Fr(0)
    rows = []
    for lev in LEVELS:
        names, props = QUERIES[lev]
        assert len(names) == len(props)
        s = sum(props)
        print(f"{lev:12s} geolevel prop {GEO_PROP[lev]} ({float(GEO_PROP[lev]):.5f}); rho_level = {float(GEO_PROP[lev]*rho):.5f}; "
              f"within-level props sum = {s} ({float(s):.12f})")
        for n, p in zip(names, props):
            inv_scale = p * GEO_PROP[lev] / GLOBAL_SCALE ** 2     # engine_utils.py:490
            sigma_sq = 1 / inv_scale                                # primitives.py:209
            # bounded-DP L2 sensitivity^2 of a marginal is 2, so rho_q = 2/(2 sigma^2) = inv_scale
            total_rho += inv_scale
            rows.append((lev, n, p, inv_scale, sigma_sq))
    print(f"sum of per-query rho = {total_rho} (equals global rho: {total_rho == rho})")
    print()
    print(f"{'level':12s} {'query':34s} {'q-prop':>10s} {'rho_q':>10s} {'sigma^2':>12s} {'sigma':>9s}")
    for lev, n, p, inv, s2 in rows:
        print(f"{lev:12s} {n:34s} {float(p):10.5f} {float(inv):10.6f} {float(s2):12.3f} {float(s2)**0.5:9.3f}")
    if len(sys.argv) >= 3 and sys.argv[1] == "--curve":
        sys.path.insert(0, sys.argv[2])
        import curve  # the release's own module; needs numpy, scipy, matplotlib, mpmath
        geo_alloc = {lev: (GEO_PROP[lev], list(QUERIES[lev][1])) for lev in LEVELS}
        c = curve.zCDPEpsDeltaCurve(geo_alloc, verbose=False)
        for delta in (1e-10,):
            eps = c.get_epsilon(delta, GLOBAL_SCALE, bounded=True, tol=1e-7, zcdp=True)  # as budget.py:131
            print(f"curve.zCDPEpsDeltaCurve: rho={c.get_rho(float(GLOBAL_SCALE)):.6f}, delta={delta:g} -> epsilon={eps:.4f}")


if __name__ == "__main__":
    main()
