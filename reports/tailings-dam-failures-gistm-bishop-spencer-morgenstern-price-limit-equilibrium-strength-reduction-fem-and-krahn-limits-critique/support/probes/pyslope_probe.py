#!/usr/bin/env python3
"""Execution probe of the unmodified upstream PySlope analysis core
(JesseBonanno/PySlope @ d6167796769743e069ec540588193216753b678f, pyslope/pyslope.py)
with import shims for its plotting/progress dependencies (see pyslope_shims.py).

P1  reproduce documentation validation example (a) circles.
P2  automatic entry/exit search on a 2H:1V, H = 10 m slope (gamma 20 kN/m3,
    c' 15 kPa, phi' 20 deg, dry) at several search densities and slice counts;
    record min FS, critical circle, wall time and circles/s.
P3  silent non-convergence: same circle evaluated with max_iterations = 15
    (default) vs 1000 and tolerance 0.005 (default) vs 1e-9.
P4  base-normal admissibility: evaluate circles whose toe-side slices have
    m_alpha = cos(a) + sin(a) tan(phi)/F <= 0.2 or < 0 and show what PySlope
    returns (it checks only denom == 0).
"""
import math, resource, sys, time
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import pyslope_shims  # noqa: F401
import pyslope as ps
import toy_lem as T

def p1():
    s = ps.Slope(height=1, angle=None, length=1)
    s.set_materials(ps.Material(20, 35, 0, 0.5), ps.Material(20, 35, 0, 1), ps.Material(18, 30, 0, 5))
    for r in range(2, 6):
        s.add_single_circular_plane(c_x=s.get_bottom_coordinates()[0], c_y=s.get_bottom_coordinates()[1] + 2.5, radius=r)
    s.update_analysis_options(slices=50, iterations=2000)
    s.analyse_slope()
    slide = {2: 1.272, 3: 2.180, 4: 3.907, 5: 5.736}
    print("P1 radius pySlope Slide(doc) rel_diff")
    for x in sorted(s._search, key=lambda d: d['radius']):
        r = x['radius']; f = x['FOS']
        print(f"P1 {r} {f:.4f} {slide[r]:.3f} {abs(f - slide[r]) / ((f + slide[r]) / 2):.4f}")

def make_slope(slices=25, iterations=1000):
    s = ps.Slope(height=10, angle=None, length=20)
    s.set_materials(ps.Material(unit_weight=20, friction_angle=20, cohesion=15, depth_to_bottom=40))
    s.update_analysis_options(slices=slices, iterations=iterations)
    return s

def p2():
    print("P2 slices iterations circles_evaluated minFS centre_x' centre_y' R lowest_y' wall_s circles_per_s")
    for slices in (25, 50):
        for it in (1000, 2000, 5000, 10000):
            s = make_slope(slices, it)
            t0 = time.perf_counter()
            s.analyse_slope()
            dt = time.perf_counter() - t0
            n = len(s._search)
            best = s._search[0]
            tx, ty = s._top_coord; bx, by = s._bot_coord
            print(f"P2 {slices} {it} {n} {best['FOS']:.4f} {best['c_x']-tx:.3f} {best['c_y']-by:.3f} {best['radius']:.3f} {best['c_y']-best['radius']-by:.3f} {dt:.3f} {n/dt:.0f}")
            sys.stdout.flush()

def p3(circles):
    print("P3 circle(x',y',R) FS_default(15it,tol0.005) FS_1000it_tol1e-9 abs_diff")
    for (xc, yc, R) in circles:
        out = []
        for (mi, tol) in ((15, 0.005), (1000, 1e-9)):
            s = make_slope(50, 1000)
            s.update_analysis_options(max_iterations=mi, tolerance=tol)
            tx, ty = s._top_coord; bx, by = s._bot_coord
            out.append(s._analyse_circular_failure_bishop(xc + tx, yc + by, R))
        a, b = out
        d = None if (a is None or b is None) else abs(a - b)
        print(f"P3 ({xc},{yc},{R}) {a} {b} {d}")

def p4(circles):
    """Compare PySlope FS with toy Bishop on the same circle and report m_alpha."""
    print("P4 circle(x',y',R) pySlope_FS toyBishop_FS toy_iters min_m_alpha n_slices_m<0.2 n_slices_m<0")
    H, L, g, c, phi = 10.0, 20.0, 20.0, 15.0, 20.0
    tp = math.tan(math.radians(phi))
    for (xc, yc, R) in circles:
        s = make_slope(50, 1000)
        s.update_analysis_options(max_iterations=1000, tolerance=1e-9)
        tx, ty = s._top_coord; bx, by = s._bot_coord
        fp = s._analyse_circular_failure_bishop(xc + tx, yc + by, R)
        res = T.slices(xc, yc, R, H, L, g, 50)
        if res is None:
            print(f"P4 ({xc},{yc},{R}) {fp} no-intersection"); continue
        S, xl, xr = res
        fb, it, mmin = T.bishop(S, c, tp, tol=1e-9, itmax=1000)
        ms = [math.cos(z['a']) + math.sin(z['a']) * tp / fb for z in S] if fb else []
        print(f"P4 ({xc},{yc},{R}) {fp} {fb} {it} {min(ms) if ms else None} {sum(m < 0.2 for m in ms)} {sum(m < 0 for m in ms)}")

if __name__ == '__main__':
    which = sys.argv[1:] or ['p1', 'p2', 'p3', 'p4']
    if 'p1' in which: p1()
    if 'p2' in which: p2()
    circles = [(5.0, 20.0, 16.0), (8.0, 14.0, 14.0), (14.0, 12.0, 14.0), (18.0, 11.0, 13.5), (22.0, 10.5, 13.0), (26.0, 10.2, 13.5)]
    if 'p3' in which: p3(circles)
    if 'p4' in which: p4(circles)
    print(f"maxrss_kB {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}")
