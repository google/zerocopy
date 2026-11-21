"""Differential probe of open heat-index implementations over a temperature/humidity grid.

Executes the real pythermalcomfort, thermofeel and MetPy functions (installed from pinned
source tarballs) and two transcriptions written for this probe:
  * nws_literal: the NWS Weather Prediction Center text, reading "the simple formula is
    computed first and the result averaged with the temperature" as a second averaging
    (switch criterion (A + T)/2 >= 80 F). This is a transcription, not NWS software.
  * wm_translit: a line-by-line Python transliteration of weathermetrics
    R/heat_index.R::heat.index.algorithm (R itself was not executed).
Usage: python probe_hi.py   (prints a text report to stdout)
"""
import warnings
import numpy as np

warnings.filterwarnings("ignore")

from pythermalcomfort.models import heat_index_rothfusz, heat_index_lu
import thermofeel as tf
from metpy.calc import heat_index as metpy_hi
from metpy.units import units


def c2f(c):
    return c * 9.0 / 5.0 + 32.0


def f2c(f):
    return (f - 32.0) * 5.0 / 9.0


def rothfusz_f(t, rh):
    return (-42.379 + 2.04901523 * t + 10.14333127 * rh - 0.22475541 * t * rh
            - 6.83783e-3 * t * t - 5.481717e-2 * rh * rh + 1.22874e-3 * t * t * rh
            + 8.5282e-4 * t * rh * rh - 1.99e-6 * t * t * rh * rh)


def adjust(t, rh, hi):
    hi = np.array(hi, dtype=float)
    m1 = (rh < 13) & (t >= 80) & (t <= 112)
    hi[m1] -= ((13 - rh[m1]) / 4) * np.sqrt((17 - np.abs(t[m1] - 95.0)) / 17)
    m2 = (rh > 85) & (t >= 80) & (t <= 87)
    hi[m2] += ((rh[m2] - 85) / 10) * ((87 - t[m2]) / 5)
    return hi


def nws_literal(t, rh):
    a = 0.5 * (t + 61.0 + (t - 68.0) * 1.2 + rh * 0.094)
    use_reg = (a + t) / 2 >= 80
    hi = np.where(use_reg, rothfusz_f(t, rh), a)
    adj = adjust(t, rh, hi)
    return np.where(use_reg, adj, hi)


def wm_translit_scalar(t, rh):
    if t <= 40:
        return t
    alpha = 61 + ((t - 68) * 1.2) + (rh * 0.094)
    hi = 0.5 * (alpha + t)
    if hi > 79:
        hi = rothfusz_f(t, rh)
        if rh <= 13 and 80 <= t <= 112:
            hi -= (13 - rh) / 4 * np.sqrt((17 - abs(t - 95)) / 17)
        elif rh > 85 and 80 <= t <= 87:
            hi += (rh - 85) / 10 * (87 - t) / 5
    return hi


def wm_translit(t, rh):
    return np.vectorize(wm_translit_scalar)(t, rh)


def td_from_rh_magnus(t_c, rh):
    # exact inverse of thermofeel's calculate_relative_humidity_percent Magnus form
    es = 6.11 * 10.0 ** (7.5 * t_c / (237.3 + t_c))
    e = es * rh / 100.0
    x = np.log10(e / 6.11)
    return 237.3 * x / (7.5 - x)


# NWS office table (weather.gov/ama/heatindex): Caution 80-90, Extreme Caution 90-103,
# Danger 103-124, Extreme Danger >=125 F. Boundary closure is not specified there; we use
# [lo, hi).
def nws_cat(hi_f):
    return np.digitize(hi_f, [80, 90, 103, 125])


# pythermalcomfort HEAT_INDEX_RISK_CATEGORIES (validation.py): upper-closed bins at 27/32/41/54 C
def ptc_cat_f(hi_f):
    c = f2c(hi_f)
    return np.digitize(c, [27.0, 32.0, 41.0, 54.0], right=True)


def main():
    tf_grid = np.arange(70.0, 125.01, 0.5)          # deg F
    rh_grid = np.arange(0.0, 100.01, 1.0)           # percent
    T, R = np.meshgrid(tf_grid, rh_grid, indexing="ij")
    t, r = T.ravel(), R.ravel()
    tc = f2c(t)

    res = {}
    res["nws_literal"] = nws_literal(t, r)
    res["wm_translit"] = wm_translit(t, r)
    res["metpy"] = np.asarray(metpy_hi(t * units.degF, r * units.percent,
                                       mask_undefined=False).to("degF").magnitude).ravel()
    td_c = td_from_rh_magnus(tc, r)
    with np.errstate(all="ignore"):
        hk = tf.calculate_heat_index_adjusted(tc + 273.15, td_c + 273.15)
    res["thermofeel_adjusted"] = c2f(np.asarray(hk) - 273.15)
    res["thermofeel_simplified"] = c2f(tf.calculate_heat_index_simplified(tc + 273.15, r.copy()) - 273.15)
    res["ptc_rothfusz_nolimit"] = c2f(heat_index_rothfusz(tc, r, round_output=False, limit_inputs=False).hi)
    res["ptc_rothfusz_default"] = c2f(heat_index_rothfusz(tc, r, round_output=False).hi)
    res["ptc_lu"] = c2f(heat_index_lu(tc, r, round_output=False).hi)
    res["rothfusz_raw_f"] = rothfusz_f(t, r)

    print("grid: T 70..125 F step 0.5 (%d), RH 0..100 %% step 1 (%d), %d points"
          % (len(tf_grid), len(rh_grid), t.size))
    print("\n[1] Celsius-coefficient Rothfusz (pythermalcomfort, no limit) vs Fahrenheit Rothfusz:")
    d = res["ptc_rothfusz_nolimit"] - res["rothfusz_raw_f"]
    print("    max |diff| = %.4f F" % np.nanmax(np.abs(d)))

    print("\n[2] Pairwise max |diff| (F) over grid points where both are finite:")
    keys = ["nws_literal", "wm_translit", "metpy", "thermofeel_adjusted",
            "thermofeel_simplified", "ptc_rothfusz_nolimit", "ptc_lu"]
    for i, a in enumerate(keys):
        for b in keys[i + 1:]:
            m = np.isfinite(res[a]) & np.isfinite(res[b])
            dd = np.abs(res[a][m] - res[b][m])
            k = np.argmax(dd)
            print("    %-22s vs %-22s max %7.3f at T=%.1fF RH=%.0f%%  n_diff>0.05=%d"
                  % (a, b, dd[k], t[m][k], r[m][k], int((dd > 0.05).sum())))

    print("\n[3] Switch-rule disagreement region (simple formula vs regression):")
    for a, b in [("nws_literal", "wm_translit"), ("wm_translit", "metpy"),
                 ("nws_literal", "metpy"), ("thermofeel_adjusted", "nws_literal")]:
        dd = np.abs(res[a] - res[b])
        m = dd > 0.05
        if m.any():
            print("    %s vs %s: %d points differ by >0.05F; T range %.1f..%.1f F, RH range %.0f..%.0f %%, max %.3f F"
                  % (a, b, m.sum(), t[m].min(), t[m].max(), r[m].min(), r[m].max(), dd[m].max()))
        else:
            print("    %s vs %s: no point differs by >0.05F" % (a, b))

    print("\n[4] Spot values (F):")
    for (tt, rr) in [(80.0, 5.0), (80.0, 13.0), (81.0, 40.0), (85.0, 90.0), (96.0, 65.0),
                     (100.0, 15.0), (100.0, 55.0), (110.0, 40.0), (115.0, 60.0), (120.0, 80.0),
                     (70.0, 50.0), (90.0, 0.0)]:
        i = np.where((t == tt) & (r == rr))[0][0]
        print("    T=%5.1f RH=%3.0f  " % (tt, rr) + "  ".join(
            "%s=%.2f" % (k, res[k][i]) for k in keys + ["ptc_rothfusz_default"]))

    print("\n[5] Category disagreement vs nws_literal under the NWS office table (count of grid points):")
    base = nws_cat(res["nws_literal"])
    for k in keys:
        m = np.isfinite(res[k])
        print("    %-22s differs from nws_literal category at %5d / %d finite points"
              % (k, int((nws_cat(res[k][m]) != base[m]).sum()), int(m.sum())))
    print("\n[6] Same function (nws_literal), NWS office table vs pythermalcomfort category edges:")
    m = np.isfinite(res["nws_literal"])
    hi = res["nws_literal"][m]
    a, b = nws_cat(hi), ptc_cat_f(hi)
    print("    differing points: %d / %d" % (int((a != b).sum()), hi.size))
    for lo, hi_ in [(103.0, 105.8), (125.0, 129.2)]:
        mm = (hi >= lo) & (hi <= hi_)
        print("    HI in [%.1f, %.1f] F: %d points (NWS level %s vs pythermalcomfort level %s)"
              % (lo, hi_, int(mm.sum()), sorted(set(a[mm])), sorted(set(b[mm]))))

    print("\n[7] Extended heat index (pythermalcomfort heat_index_lu) minus nws_literal (F), by T band, RH>=50%:")
    for lo, hi_ in [(80, 90), (90, 100), (100, 110), (110, 125.01)]:
        m = (t >= lo) & (t < hi_) & (r >= 50) & np.isfinite(res["ptc_lu"])
        dd = res["ptc_lu"][m] - res["nws_literal"][m]
        print("    T in [%g,%g): min %.2f  max %.2f  mean %.2f" % (lo, min(hi_, 125), dd.min(), dd.max(), dd.mean()))

    print("\n[7b] Same difference restricted to the NWS chart domain T 80..110 F, RH 40..100 %:")
    m = (t >= 80) & (t <= 110) & (r >= 40)
    dd = res["ptc_lu"][m] - res["nws_literal"][m]
    kmax, kmin = np.argmax(dd), np.argmin(dd)
    print("    max %.2f F at T=%.1f RH=%.0f (nws %.1f, lu %.1f); min %.2f F at T=%.1f RH=%.0f (nws %.1f, lu %.1f)"
          % (dd[kmax], t[m][kmax], r[m][kmax], res["nws_literal"][m][kmax], res["ptc_lu"][m][kmax],
             dd[kmin], t[m][kmin], r[m][kmin], res["nws_literal"][m][kmin], res["ptc_lu"][m][kmin]))
    mm = m & (res["nws_literal"] <= 137.0)
    dd2 = res["ptc_lu"][mm] - res["nws_literal"][mm]
    k2 = np.argmax(dd2)
    print("    ... and NWS HI <= 137 F: max %.2f F at T=%.1f RH=%.0f; min %.2f F" % (
        dd2[k2], t[mm][k2], r[mm][k2], dd2.min()))
    print("    Celsius-vs-Fahrenheit Rothfusz max |diff| = %.3e F" % np.nanmax(np.abs(res["ptc_rothfusz_nolimit"] - res["rothfusz_raw_f"])))

    print("\n[8] Cool-weather behaviour (T = 0..60 F, RH 0..100):")
    t2, r2 = np.meshgrid(np.arange(0.0, 60.01, 1.0), np.arange(0.0, 100.01, 5.0), indexing="ij")
    t2, r2 = t2.ravel(), r2.ravel()
    tc2 = f2c(t2)
    simp = c2f(tf.calculate_heat_index_simplified(tc2 + 273.15, r2.copy()) - 273.15)
    roth = c2f(heat_index_rothfusz(tc2, r2, round_output=False, limit_inputs=False).hi)
    rdef = heat_index_rothfusz(tc2, r2, round_output=False).hi
    lu = c2f(heat_index_lu(tc2, r2, round_output=False).hi)
    print("    ptc_rothfusz_nolimit - T: max %.1f F (at T=%.0f RH=%.0f)" % (
        np.max(roth - t2), t2[np.argmax(roth - t2)], r2[np.argmax(roth - t2)]))
    print("    ptc_rothfusz_default: NaN at %d / %d points" % (int(np.isnan(rdef).sum()), rdef.size))
    print("    thermofeel_simplified - T: max |diff| %.3f F" % np.max(np.abs(simp - t2)))
    print("    ptc_lu - T: min %.2f max %.2f F" % (np.min(lu - t2), np.max(lu - t2)))


if __name__ == "__main__":
    main()
