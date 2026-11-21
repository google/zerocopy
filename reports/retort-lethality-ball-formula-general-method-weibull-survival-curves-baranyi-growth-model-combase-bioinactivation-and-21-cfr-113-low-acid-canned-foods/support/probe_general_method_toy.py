#!/usr/bin/env python3
"""Toy-model probe: numerical sensitivity of the general-method lethality
F0 = integral 10**((T - 121.1)/z) dt for a SYNTHETIC cold-spot history.

The history uses Ball's semi-log heating/cooling forms with illustrative
parameters (not data from any real product):
  heating: T(t) = TR - jh*(TR - T0)*10**(-t/fh),            0 <= t <= Pt
  cooling: T(t) = Tw + jc*(Tc - Tw)*10**(-(t-Pt)/fc) capped at Tc, t > Pt
The point is how integration rule, sampling interval, a 0.5 C sensor bias
and the assumed z-value move F0 -- not the value of F0 itself.
"""
import numpy as np

TR, T0, Tw = 121.1, 70.0, 20.0
jh, fh, Pt = 1.4, 40.0, 75.0
jc, fc = 1.4, 40.0


def T(t):
    t = np.asarray(t, float)
    heat = TR - jh * (TR - T0) * 10 ** (-t / fh)
    Tc = TR - jh * (TR - T0) * 10 ** (-Pt / fh)
    cool = np.minimum(Tw + jc * (Tc - Tw) * 10 ** (-(t - Pt) / fc), Tc)
    return np.where(t <= Pt, np.minimum(heat, TR), cool)


def L(t, z=10.0, bias=0.0):
    return 10 ** ((T(t) + bias - 121.1) / z)


tend = Pt + 60.0
fine = np.linspace(0, tend, 810001)
ref = np.trapezoid(L(fine), fine)
print(f"cold-spot temperature at end of heating: {T(Pt):.2f} C")
print(f"reference F0 (trapezoid, dt = {fine[1]-fine[0]:.4f} min): {ref:.4f} min")
for dt in (0.5, 1.0, 2.0, 5.0):
    t = np.arange(0, tend + 1e-9, dt)
    y = L(t)
    left = np.sum(y[:-1]) * dt
    trap = np.trapezoid(y, t)
    if (len(t) - 1) % 2 == 0:
        simp = dt / 3 * (y[0] + y[-1] + 4 * y[1:-1:2].sum() + 2 * y[2:-1:2].sum())
    else:
        simp = float("nan")
    print(f"dt={dt:3.1f} min: left-rectangle {left:.4f} ({(left-ref)/ref:+.2%})  "
          f"trapezoid {trap:.4f} ({(trap-ref)/ref:+.2%})  Simpson {simp:.4f} ({(simp-ref)/ref:+.2%})")
for bias in (-0.5, +0.5):
    b = np.trapezoid(L(fine, bias=bias), fine)
    print(f"sensor bias {bias:+.1f} C: F0 {b:.4f} ({(b-ref)/ref:+.2%}); closed form 10**({bias}/10)-1 = {10**(bias/10)-1:+.2%}")
for z in (8.0, 10.0, 12.0):
    fz = np.trapezoid(L(fine, z=z), fine)
    print(f"z={z:4.1f} C: F(121.1, z) {fz:.4f} min ({(fz-ref)/ref:+.2%} vs z=10)")
# heating-phase vs cooling-phase share of lethality
h = fine <= Pt
print(f"share of F0 delivered after steam-off (cooling): {np.trapezoid(L(fine[~h]), fine[~h]) / ref:.2%}")
