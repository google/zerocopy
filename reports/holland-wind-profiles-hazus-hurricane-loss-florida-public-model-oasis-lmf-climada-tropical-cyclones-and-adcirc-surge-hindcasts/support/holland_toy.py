"""Toy re-implementations of the Holland-profile "recipes" used by four open codes.

THIS IS A TOY MODEL. Each function transliterates, by hand, the chain of constants and
formulas read from one upstream source file at a pinned revision (cited per function).
Only the axisymmetric speed component at the surface is reproduced (no inflow angle,
no translational vector, no land/roughness adjustment, no time interpolation).
Agreement with the upstream code was checked by execution only for the two CLIMADA
recipes (see climada_profile_probe.py); the ADCIRC and GeoClaw recipes are unexecuted
transliterations.

Run: python3 holland_toy.py
"""
import math

import numpy as np

E = math.e
OMEGA_CLIMADA = 7.29e-5      # trop_cyclone_windfields.py V_ANG_EARTH
OMEGA_ADCIRC = 7.29212e-5    # src/constants.F90 omega


def coriolis(lat, omega):
    return 2 * omega * math.sin(math.radians(abs(lat)))


def grad_B_form(r, rmax, B, dp_pa, rho, f):
    """Holland (1980) gradient wind written with B/rho*dp (CLIMADA _stat_holland_1980)."""
    x = (rmax / np.maximum(1.0, r)) ** B
    c = 0.5 * r * f
    return np.sqrt(np.maximum(0, B / rho * x * dp_pa * np.exp(-x) + c * c)) - c


def grad_V_form(r, rmax, B, vm, f):
    """Same profile written with vm^2 (ADCIRC NWS8 HollandGet, GeoClaw holland80)."""
    x = (rmax / r) ** B
    c = 0.5 * r * f
    return np.sqrt(x * np.exp(1 - x) * vm * vm + c * c) - c


# --- CLIMADA cc0b21516a15...: trop_cyclone_windfields.py -------------------------
def climada_h1980_recipe(vmax, pcen, penv, rmax_km, lat, vt, radii_km, rho=1.15, gsw=0.9):
    """_vgrad (l.92-95), _B_holland_1980 (l.501-508, clip (1.0,2.5)), x gsw (l.201)."""
    dp = (penv - pcen) * 100
    vg = max(0.0, vmax - vt) / gsw
    B = min(max(vg * vg * E * rho / dp, 1.0), 2.5)
    f = coriolis(lat, OMEGA_CLIMADA)
    return grad_B_form(np.asarray(radii_km) * 1e3, rmax_km * 1e3, B, dp, rho, f) * gsw


def holland2008_bs(dp_hpa, dpdt_hpa_per_h, lat, vt):
    x = 0.6 * (1 - dp_hpa / 215)
    return (-4.4e-5 * dp_hpa ** 2 + 0.01 * dp_hpa + 0.03 * dpdt_hpa_per_h
            - 0.014 * abs(lat) + 0.15 * vt ** x + 1.0)


def climada_h08_recipe(vmax, pcen, penv, rmax_km, lat, vt, radii_km, rho=1.15, gsw=0.9):
    """_bs_holland_2008 (l.411-434; clip (1.0,2.5)*gsw**2 = (0.81,2.025)); vmax unused."""
    dp_hpa = penv - pcen
    B = holland2008_bs(dp_hpa, 0.0, lat, vt)
    B = min(max(B, 1.0 * gsw ** 2), 2.5 * gsw ** 2)
    f = coriolis(lat, OMEGA_CLIMADA)
    return grad_B_form(np.asarray(radii_km) * 1e3, rmax_km * 1e3, B, dp_hpa * 100, rho, f)


# --- ADCIRC ae33c51ffc29...: src/nws08.F90 HollandGet (l.613-702), constants.F90 ---
def adcirc_nws8_recipe(vmax, pcen, rmax_km, lat, vt, radii_km, bladj=0.9,
                       rho=1.293, one2ten=0.8928, p_amb=1013.0):
    """BCalc='limited'; ambient pressure is PRBCKGRND (1013 hPa), not the track's.
    BLAdj comes from the run's input file (no code default other than 1.0); 0.9 used here."""
    dp = max(p_amb * 100 - pcen * 100, 100.0)
    spd = (vmax - 1.0 * vt) / bladj
    B = min(max(rho * E * spd * spd / dp, 1.0), 2.5)
    f = coriolis(lat, OMEGA_ADCIRC)
    v = grad_V_form(np.asarray(radii_km) * 1e3, rmax_km * 1e3, B, spd, f)
    return v * bladj * one2ten, B


def adcirc_nws19_uvp_factor(vm_ms, lat, radii_km):
    """vortex.F uvp l.695-719: speed is rescaled by Vmax/speedAtRmax where speedAtRmax's
    Coriolis term uses the node distance `dist`, not `rmx`; returns that rescale factor."""
    f = coriolis(lat, OMEGA_ADCIRC)
    c = 0.5 * np.asarray(radii_km) * 1e3 * f
    return vm_ms / (np.sqrt(vm_ms * vm_ms + c * c) - c)


# --- GeoClaw 091b28d19ecb...: parametric_met_forcing_module.f90 -----------------------
def geoclaw_h80_recipe(vmax, pcen, rmax_km, lat, vt, radii_km, rho=1.15, p_amb=1013.0):
    """adjust_max_wind (l.455-466, /0.9), get_holland_b (l.582-584), wind (l.662-664),
    post_process (l.512-514: x0.9 then x0.88 'sampling_time')."""
    dp = max(p_amb * 100 - pcen * 100, 100.0)
    mod = max(vmax - vt, 0.0) / 0.9
    B = min(max(rho * E * mod * mod / dp, 1.0), 2.5)
    f = coriolis(lat, 7.2921e-5)
    v = grad_V_form(np.asarray(radii_km) * 1e3, rmax_km * 1e3, B, mod, f)
    return v * 0.9 * 0.88, B


def geoclaw_h08_recipe(pcen, rmax_km, lat, vt, radii_km, rho=1.15, p_amb=1013.0, units="as_coded"):
    """set_holland_2008_fields (l.711-736): dp in Pa is passed to get_holland_b_2008
    (l.591-602), whose coefficients assume hPa; units='hPa' shows the intended value."""
    dp_pa = max(p_amb * 100 - pcen * 100, 100.0)
    dp_arg = dp_pa if units == "as_coded" else dp_pa / 100
    x = 0.6 * (1 - dp_arg / 215)
    B = -4.4e-5 * dp_arg ** 2 + 0.01 * dp_arg - 0.014 * abs(lat) + 0.15 * vt ** x + 1.0
    B = min(max(B, 1.0), 2.5)
    mod = math.sqrt(B / (rho * E) * dp_pa)
    f = coriolis(lat, 7.2921e-5)
    v = grad_V_form(np.asarray(radii_km) * 1e3, rmax_km * 1e3, B, mod, f)
    return v * 0.88, B, mod


if __name__ == "__main__":
    VMAX, PCEN, PENV, RMAX, LAT, VT = 50.0, 950.0, 1010.0, 40.0, 25.0, 5.0
    radii = np.array([20, 40, 60, 80, 120, 200, 300], dtype=float)
    print(f"Reference storm: Vmax(1-min,10 m)={VMAX} m/s, pc={PCEN} hPa, penv={PENV} hPa "
          f"(CLIMADA only), Rmax={RMAX} km, lat={LAT}, vt={VT} m/s")
    print("r_km                     " + " ".join(f"{r:7.0f}" for r in radii))
    rows = []
    v = climada_h1980_recipe(VMAX, PCEN, PENV, RMAX, LAT, VT, radii); rows.append(("CLIMADA H1980 [1-min]", v))
    v = climada_h08_recipe(VMAX, PCEN, PENV, RMAX, LAT, VT, radii); rows.append(("CLIMADA H08   [1-min]", v))
    v, b8 = adcirc_nws8_recipe(VMAX, PCEN, RMAX, LAT, VT, radii); rows.append(("ADCIRC NWS8   [10-min]", v))
    v, bg = geoclaw_h80_recipe(VMAX, PCEN, RMAX, LAT, VT, radii); rows.append(("GeoClaw h80   [10-min]", v))
    v, bq, mq = geoclaw_h08_recipe(PCEN, RMAX, LAT, VT, radii); rows.append(("GeoClaw h08 coded[10m]", v))
    v2, bq2, mq2 = geoclaw_h08_recipe(PCEN, RMAX, LAT, VT, radii, units="hPa"); rows.append(("GeoClaw h08 hPa [10m]", v2))
    for name, v in rows:
        print(f"{name:25s}" + " ".join(f"{x:7.2f}" for x in v))
    print(f"B: ADCIRC NWS8={b8:.4f} GeoClaw h80={bg:.4f} GeoClaw h08 as coded={bq:.4f} "
          f"(Vmax_s={mq:.2f}) vs hPa={bq2:.4f} (Vmax_s={mq2:.2f})")
    print("Same table with 10-min outputs divided by their own 1-min->10-min factor:")
    for name, v in rows:
        fac = 0.8928 if "ADCIRC" in name else (0.88 if "GeoClaw" in name else 1.0)
        print(f"{name:25s}" + " ".join(f"{x / fac:7.2f}" for x in v))

    print("\nB-clamp interaction (vt=0): B = rho*e*Vg^2/dp, Vg = Vmax/0.9, dp=60 hPa, rho=1.15")
    for vm in (40.0, 50.0, 60.0, 70.0):
        vg = vm / 0.9
        braw = 1.15 * E * vg * vg / 6000
        bcl = min(max(braw, 1.0), 2.5)
        peak_Bform = math.sqrt(bcl * 6000 / (1.15 * E)) * 0.9
        print(f"Vmax={vm:5.1f} B_raw={braw:6.3f} B_used={bcl:5.3f} "
              f"cyclostrophic peak, B/rho*dp form x0.9 = {peak_Bform:6.2f} m/s; Vm^2 form x0.9 = {vg*0.9:6.2f} m/s")

    print("\nAir-density choice: B is linear in rho -> B(1.293)/B(1.15) = %.4f" % (1.293 / 1.15))
    va, ba = adcirc_nws8_recipe(VMAX, PCEN, RMAX, LAT, VT, radii, rho=1.293)
    vb, bb_ = adcirc_nws8_recipe(VMAX, PCEN, RMAX, LAT, VT, radii, rho=1.15)
    print(f"ADCIRC NWS8 recipe, rhoAir 1.293 (B={ba:.4f}) vs 1.15 (B={bb_:.4f}); ratio of 10-m winds:")
    print("r_km " + " ".join(f"{r:7.0f}" for r in radii))
    print("rat  " + " ".join(f"{x:7.4f}" for x in va / vb))
    print("Stress elasticity with ADCIRC Garratt drag Cd=1e-3*(0.75+0.067U), cap 0.0035 (U*=41.04 m/s):")
    for U in (20.0, 30.0, 40.0, 45.0):
        cd = 1e-3 * (0.75 + 0.067 * U)
        el = 2 + (0.067 * U / (0.75 + 0.067 * U) if cd < 0.0035 else 0.0)
        print(f"  U={U:4.1f} m/s  d ln(tau)/d ln(U) = {el:.3f}  -> 0.8928 vs 0.88 averaging factor: "
              f"stress ratio {(0.8928 / 0.88) ** el:.4f}")

    print("\nADCIRC NWS19 uvp rescale factor Vmax/speedAtRmax (Vmax_BL=55.6 m/s, lat 25):")
    rr = np.array([40, 80, 120, 200, 300, 400], dtype=float)
    fac = adcirc_nws19_uvp_factor(50 / 0.9, LAT, rr)
    print("r_km " + " ".join(f"{r:7.0f}" for r in rr))
    print("fac  " + " ".join(f"{x:7.4f}" for x in fac))
