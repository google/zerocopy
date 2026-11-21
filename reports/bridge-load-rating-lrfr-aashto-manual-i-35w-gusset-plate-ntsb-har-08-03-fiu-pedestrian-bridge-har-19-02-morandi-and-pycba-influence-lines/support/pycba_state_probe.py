#!/usr/bin/env python3
"""State and edge-case probe of pycba.InfluenceLines (ccaprani/pycba src/pycba/inf_lines.py).
  (a) calling create_ils() twice: InfluenceLines.pos is never reset (only vResults is),
  (b) a step that does not divide the beam length so that the last load position exceeds L,
  (c) section snapping of get_il for a POI between result points, for several npts.
Usage: python3 pycba_state_probe.py
"""
import numpy as np
import pycba as cba

L, EI = 10.0, 1.0e5
ils = cba.InfluenceLines([L], EI, [-1, 0, -1, 0])
ils.create_ils(step=0.5)
x1, e1 = ils.get_il(5.0, "M")
print("(a) first create_ils(step=0.5): len(x)=", len(x1), " len(eta)=", len(e1))
ils.create_ils(step=0.5)
try:
    x2, e2 = ils.get_il(5.0, "M")
    print("    second create_ils(step=0.5): len(x)=", len(x2), " len(eta)=", len(e2))
except Exception as e:  # noqa: BLE001
    print("    second create_ils raised", type(e).__name__, e)

ils = cba.InfluenceLines([L], EI, [-1, 0, -1, 0])
print("(b) L=10, step=0.6 -> npts = round(10/0.6)+1 =", round(L / 0.6) + 1, "; last pos =", (round(L / 0.6)) * 0.6)
try:
    ils.create_ils(step=0.6)
    x, e = ils.get_il(5.0, "M")
    ref = np.where(x <= 5.0, x * 5.0 / L, 5.0 * (L - x) / L)
    for xi, ei, ri in list(zip(x, e, ref))[-3:]:
        print(f"    pos={xi:.2f} pycba={ei:.6f} closed-form(on-beam)={ri:.6f}")
except Exception as e:  # noqa: BLE001
    print("    create_ils(step=0.6) raised", type(e).__name__, e)

print("(c) POI 3.33 on L=10 simple span, M IL peak ordinate (closed form a(L-a)/L = 2.22111)")
for npts in (10, 20, 100, 1000):
    ba = cba.BeamAnalysis([L], EI, [-1, 0, -1, 0])
    ba.npts = npts
    il = cba.InfluenceLines.__new__(cba.InfluenceLines)
    il.ba, il.L, il.vResults, il.pos = ba, ba.beam.length, [], []
    il.create_ils(step=0.01)
    x, e = il.get_il(3.33, "M")
    sx = il.vResults[0].vRes[0].x
    used = sx[np.abs(sx[1:-1] - 3.33).argmin() + 1]
    print(f"    npts={npts}: section used x={used:.4f}, max ordinate {e.max():.5f}")
