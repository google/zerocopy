#!/usr/bin/env python3
"""Arithmetic check of the published PurpleAir corrections (coefficients as printed):
  US-wide (2021, Eq. 10 / 2022 Eq. 1):  PM = 0.524*PA - 0.0862*RH + 5.75
  extended (2022): PA < 570 -> Eq.1;  570 <= PA < 611 -> w*Eq3 + (1-w)*Eq1 with w = 0.0244*PA - 13.9;
                   PA >= 611 -> Eq.3 = 4.21e-4*PA^2 + 0.392*PA + 3.44
PA = raw PurpleAir cf_1 (A/B mean), RH in percent as measured by the sensor."""
def eq1(pa, rh): return 0.524 * pa - 0.0862 * rh + 5.75
def eq3(pa): return 4.21e-4 * pa * pa + 0.392 * pa + 3.44
def ext(pa, rh):
    if pa < 570: return eq1(pa, rh)
    if pa < 611:
        w = 0.0244 * pa - 13.9
        return w * eq3(pa) + (1 - w) * eq1(pa, rh)
    return eq3(pa)
eps = 1e-9
for rh in (20, 50, 80):
    j570 = ext(570, rh) - ext(570 - eps, rh)
    j611 = ext(611, rh) - ext(611 - eps, rh)
    print(f"RH={rh}%: blend weight at 570 = {0.0244*570-13.9:.4f}, at 611- = {0.0244*611-13.9:.4f}; "
          f"jump at 570 = {j570:+.3f}, jump at 611 = {j611:+.3f} ug/m3; corrected(570)={ext(570,rh):.2f}, corrected(611)={ext(611,rh):.2f}")
print("US-wide at PA=0, RH=100:", round(eq1(0, 100), 4))
for pa in (100, 300, 570, 611, 1000):
    print(f"PA={pa}: US-wide(RH50)={eq1(pa,50):.1f}  extended(RH50)={ext(pa,50):.1f}")
