#!/usr/bin/env python3
"""Derived checks of constants in SNOWPACK's stability code (no SNOWPACK build needed).

1. Skier-induced shear stress term of getLayerSkierStability()
   (Source/snowpack/snowpack/StabilityAlgorithms.cc): with skier_weight = 85 kg,
   ski_length = 1.7 m, g = Constants::g = 9.80665 m s-2 (Constants.h),
   alpha_max = 54.3 deg and psi_ref = 38 deg,
       delta_tau(z) = 2 * load * cos(a) * sin(a)^2 * sin(a + psi) / (pi * z * cos(psi)) / 1000  [kPa]
   The source comment states "around 0.1523 kPa / layer_depth".
2. Skier penetration depth prefactor: compPenetrationDepth() returns
   min(0.8 * 43.3 / rho_mean_top_30cm, HS/cos(slope) - top_crust); 0.8 * 43.3 is compared
   with the 34.6 / rho_30 form used as a feature definition by Mayer et al. (2022).
"""
import math

load = 85.0 * 9.80665 / 1.7
a = math.radians(54.3)
psi = math.radians(38.0)
coef = 2 * load * math.cos(a) * math.sin(a) ** 2 * math.sin(a + psi) / (math.pi * math.cos(psi)) / 1000.0
print(f"load per unit ski length = {load:.4f} N/m")
print(f"delta_tau * depth = {coef:.5f} kPa m  (source comment: ~0.1523)")
for z in (0.3, 0.5, 1.0):
    print(f"  delta_tau at effective depth {z:.1f} m = {coef / z:.4f} kPa")
print(f"0.8 * 43.3 = {0.8 * 43.3:.2f} (kg m-2 numerator of Pk = .../rho)")
