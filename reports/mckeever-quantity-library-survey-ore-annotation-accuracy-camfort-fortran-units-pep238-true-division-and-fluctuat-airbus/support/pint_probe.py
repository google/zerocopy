"""pint run-time quantity probe: which unit mistakes are caught and which are not.

Run (pint installed from the pinned revision into a virtualenv):
  python3 pint_probe.py
Each line: label -> result or raised exception class and message (truncated).
"""
import math
import pint

ureg = pint.UnitRegistry()
Q_ = ureg.Quantity


def show(label, fn):
    try:
        r = fn()
        print(f"{label} -> {r!r}")
    except Exception as e:  # noqa: BLE001
        msg = str(e).replace("\n", " ")[:110]
        print(f"{label} -> raises {type(e).__name__}: {msg}")


print("pint", pint.__version__)
# 1. Caught: incompatible dimensions.
show("1 m + 1 s", lambda: Q_(1, "m") + Q_(1, "s"))
show("(1 m).to('kg')", lambda: Q_(1, "m").to("kg"))
show("1 m < 1 s", lambda: Q_(1, "m") < Q_(1, "s"))
# 2. Converted silently (correct): same dimension, different unit.
show("1 m + 1 ft", lambda: Q_(1, "m") + Q_(1, "ft"))
# 3. Not caught: dimensionally identical but semantically different.
show("1 Hz + 1 Bq", lambda: Q_(1, "Hz") + Q_(1, "Bq"))
show("1 Gy + 1 Sv", lambda: Q_(1, "Gy") + Q_(1, "Sv"))
show("1 N*m (torque) + 1 J (energy)", lambda: Q_(1, "N*m") + Q_(1, "J"))
show("1 rad + 1 (plain number)", lambda: Q_(1, "rad") + 1)
show("1 rad/s + 1 Hz", lambda: (Q_(1, "rad/s") + Q_(1, "Hz")))
show("math.sin(Q_(90, 'deg'))", lambda: math.sin(Q_(90, "deg")))
# 4. Special case: plain zero/NaN added to a dimensioned quantity skips the unit check.
show("1 m + 0 (plain)", lambda: Q_(1, "m") + 0)
show("1 m + nan (plain)", lambda: Q_(1, "m") + float("nan"))
show("1 m + 1 (plain)", lambda: Q_(1, "m") + 1)
# 5. Equality across dimensions returns False instead of raising.
show("1 m == 1 s", lambda: Q_(1, "m") == Q_(1, "s"))
show("0 m == 0 s", lambda: Q_(0, "m") == Q_(0, "s"))
# 6. Escape hatches lose the unit.
show("float(1 m)", lambda: float(Q_(1, "m")))
show("(1 m).magnitude + 1", lambda: Q_(1, "m").magnitude + 1)
show("(5 km).m_as('m')", lambda: Q_(5, "km").m_as("m"))
# 7. Offset (affine) units.
show("10 degC + 10 degC", lambda: Q_(10, "degC") + Q_(10, "degC"))
show("10 degC - 5 degC", lambda: Q_(10, "degC") - Q_(5, "degC"))
show("(10 degC).to('degF')", lambda: Q_(10, "degC").to("degF"))
show("2 * 10 degC", lambda: 2 * Q_(10, "degC"))
# 8. Numeric kind is orthogonal to unit: integer magnitudes and true division.
show("Q_(7, 'm') / 2", lambda: Q_(7, "m") / 2)
show("Q_(7, 'm') // Q_(2, 'm')", lambda: Q_(7, "m") // Q_(2, "m"))
show("Q_(7, 'm') // 2", lambda: Q_(7, "m") // 2)
show("type(Q_(7, 'm').magnitude)", lambda: type(Q_(7, "m").magnitude).__name__)
show("type((Q_(7, 'm') / Q_(2, 'm')).magnitude)", lambda: type((Q_(7, "m") / Q_(2, "m")).magnitude).__name__)
