"""Probe: WBGT approximations vs the Liljegren model, and UTCI across two libraries.

Executes real thermofeel and pythermalcomfort functions (installed from pinned source
tarballs). All meteorological inputs are synthetic grid points, not station records.
Usage: python probe_wbgt_utci.py
"""
import warnings
import itertools
import numpy as np

warnings.filterwarnings("ignore")
import thermofeel as tf
from pythermalcomfort.models import utci as ptc_utci, esi as ptc_esi

K = 273.15


def hardy_es_hpa(t_c):
    return tf.calculate_saturation_vapour_pressure(np.asarray(t_c) + K)


def wbgt_section():
    print("== WBGT: approximations minus thermofeel Liljegren (deg C); synthetic inputs, p = 1013.25 hPa")
    Ta = [25.0, 30.0, 35.0, 40.0, 45.0]
    RH = [10.0, 30.0, 50.0, 70.0, 90.0]
    V10 = [0.5, 1.0, 2.0, 4.0]
    scen = {"night": (0.0, 0.0, 0.0), "sun800": (800.0, 0.8, 0.85)}
    rows = []
    for name, (ssrd, fdir, cz) in scen.items():
        g = np.array(list(itertools.product(Ta, RH, V10)))
        t, rh, v = g[:, 0], g[:, 1], g[:, 2]
        n = t.size
        lil = tf.calculate_wbgt_liljegren(t + K, rh, np.full(n, 1013.25), v,
                                          np.full(n, ssrd), np.full(n, fdir), np.full(n, cz)) - K
        swbgt = tf.calculate_wbgt_simple(t + K, rh) - K
        esi = np.asarray(ptc_esi(tdb=t, rh=rh, sol_radiation_global=np.full(n, ssrd), round_output=False).esi)
        out = {"sWBGT": swbgt, "ESI": esi}
        if name == "night":
            # shade/night: mean radiant temperature = air temperature, Stull wet bulb + Guo globe
            td = tf.calculate_dew_point_from_relative_humidity(rh, t + K)
            out["Stull+globe"] = tf.calculate_wbgt(t + K, t + K, v, td) - K
        print("-- scenario %s (ssrd=%g W/m2, fdir=%g, cos(sza)=%g); Liljegren NaN count: %d / %d"
              % (name, ssrd, fdir, cz, int(np.isnan(lil).sum()), n))
        for k, val in out.items():
            d = val - lil
            for hum_lo, hum_hi in [(10, 30), (50, 50), (70, 90)]:
                m = (rh >= hum_lo) & (rh <= hum_hi) & np.isfinite(d)
                print("   %-11s RH %2d-%2d%%: diff min %6.2f  median %6.2f  max %6.2f"
                      % (k, hum_lo, hum_hi, d[m].min(), np.median(d[m]), d[m].max()))
            hf_a = tf.calculate_heat_force(val + K)
            hf_l = tf.calculate_heat_force(lil + K)
            m = np.isfinite(hf_a) & np.isfinite(hf_l)
            print("   %-11s heat-force level differs from Liljegren at %d / %d points (max |level diff| %d)"
                  % (k, int((hf_a[m] != hf_l[m]).sum()), int(m.sum()), int(np.max(np.abs(hf_a[m] - hf_l[m])))))
        # decision example
        for tt, rr, vv in [(35.0, 70.0, 1.0), (40.0, 10.0, 1.0), (30.0, 90.0, 0.5)]:
            i = np.where((t == tt) & (rh == rr) & (v == vv))[0][0]
            print("   spot Ta=%g RH=%g v10=%g: Liljegren %.2f  " % (tt, rr, vv, lil[i]) +
                  "  ".join("%s %.2f" % (k, out[k][i]) for k in out))
        rows.append((name, lil))
    # wind-scaling option inside thermofeel
    t, rh, v = 35.0, 50.0, 2.0
    a = tf.calculate_wbgt_liljegren(np.array([t + K]), np.array([rh]), np.array([1013.25]), np.array([v]),
                                    np.array([800.0]), np.array([0.8]), np.array([0.85]))[0] - K
    b = tf.calculate_wbgt_liljegren(np.array([t + K]), np.array([rh]), np.array([1013.25]), np.array([v]),
                                    np.array([800.0]), np.array([0.8]), np.array([0.85]), wind_scaling="brode")[0] - K
    print("-- wind_scaling at Ta=35 RH=50 v10=2 sun800: liljegren-profile %.3f  brode-log-profile %.3f  diff %.3f"
          % (a, b, b - a))


def utci_section(ptc_src, tf_src):
    print("\n== UTCI: thermofeel calculate_utci vs pythermalcomfort utci (deg C); synthetic grid")
    Ta = [-20.0, 0.0, 10.0, 20.0, 30.0, 35.0, 40.0, 45.0]
    dTr = [-10.0, 0.0, 10.0, 20.0, 30.0, 40.0]
    V = [0.5, 1.0, 2.0, 4.0, 8.0, 16.0]
    RH = [10.0, 30.0, 50.0, 70.0, 90.0]
    g = np.array(list(itertools.product(Ta, dTr, V, RH)))
    t, dtr, v, rh = g.T
    tr = t + dtr
    p = np.asarray(ptc_utci(t, tr, v, rh, limit_inputs=False, round_output=False).utci)
    pd = np.asarray(ptc_utci(t, tr, v, rh, round_output=False).utci)
    e = hardy_es_hpa(t) * rh / 100.0
    q = tf.calculate_utci(t + K, v, tr + K, ehPa=e) - K
    d = q - p
    print("grid points: %d; same vapour pressure fed to both: max |diff| = %.2e C" % (t.size, np.nanmax(np.abs(d))))
    print("pythermalcomfort default (limit_inputs=True) NaN at %d / %d points (vapour pressure > 5 kPa or other limits)"
          % (int(np.isnan(pd).sum()), t.size))
    # thermofeel dew-point path: e = Hardy_es(T) * MagnusRH(T, Td) / 100 vs physically consistent Hardy_es(Td)
    td_c = tf.calculate_dew_point_from_relative_humidity(rh, t + K) - K
    q_td = tf.calculate_utci(t + K, v, tr + K, td_k=td_c + K) - K
    q_cons = tf.calculate_utci(t + K, v, tr + K, ehPa=hardy_es_hpa(td_c)) - K
    dd = q_td - q_cons
    print("thermofeel td_k path vs e=Hardy_es(Td): max |diff| = %.3f C (median %.4f)" % (np.max(np.abs(dd)), np.median(np.abs(dd))))
    # vapour pressure on the dewpoint path vs the RH-defined value
    e_td = hardy_es_hpa(t) * tf.calculate_relative_humidity_percent(t + K, td_c + K) / 100.0
    print("   vapour pressure ratio (td path / Hardy_es(T)*RH): min %.4f max %.4f" % (np.min(e_td / e), np.max(e_td / e)))
    # out-of-range behaviour
    for (tt, trr, vv, rr) in [(30.0, 30.0, 0.1, 50.0), (30.0, 30.0, 25.0, 50.0), (55.0, 55.0, 1.0, 20.0), (40.0, 40.0, 1.0, 90.0)]:
        a = float(np.asarray(ptc_utci(tt, trr, vv, rr, round_output=False).utci))
        b = float(np.asarray(ptc_utci(tt, trr, vv, rr, limit_inputs=False, round_output=False).utci))
        c = float(tf.calculate_utci(np.array([tt + K]), np.array([vv]), np.array([trr + K]),
                                    ehPa=np.array([hardy_es_hpa(tt) * rr / 100.0]))[0] - K)
        print("   out-of-range Ta=%g Tr=%g v=%g RH=%g: ptc default %s  ptc unlimited %.2f  thermofeel %.2f"
              % (tt, trr, vv, rr, "nan" if np.isnan(a) else "%.2f" % a, b, c))


if __name__ == "__main__":
    import sys
    wbgt_section()
    utci_section(sys.argv[1], sys.argv[2])
