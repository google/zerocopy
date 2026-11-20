"""Python numeric-kind probe: PEP 238 division semantics and int/float mixing.

Run: python3 py_division_probe.py
Prints one line per case: expression, repr(result), type name.
"""
import math
import sys

cases = [
    ("7 / 2", lambda: 7 / 2),
    ("7 // 2", lambda: 7 // 2),
    ("-7 // 2", lambda: -7 // 2),
    ("int(-7 / 2)", lambda: int(-7 / 2)),
    ("-7 % 2", lambda: -7 % 2),
    ("2 / 1", lambda: 2 / 1),
    ("3.5 // 2.0", lambda: 3.5 // 2.0),
    ("7.0 // 2", lambda: 7.0 // 2),
    ("(2**53 + 1) / 1", lambda: (2**53 + 1) / 1),
    ("(2**53 + 1) // 1", lambda: (2**53 + 1) // 1),
    ("float(2**53 + 1) == 2**53 + 1", lambda: float(2**53 + 1) == 2**53 + 1),
    ("(10**400) / (10**399)", lambda: (10**400) / (10**399)),
    ("1 / (10**400)", lambda: 1 / (10**400)),
    ("0.1 + 0.2 == 0.3", lambda: 0.1 + 0.2 == 0.3),
    ("1 == 1.0", lambda: 1 == 1.0),
    ("hash(1) == hash(1.0)", lambda: hash(1) == hash(1.0)),
    ("True + True", lambda: True + True),
    ("mean_int_args: (1 + 2) / 2", lambda: (1 + 2) / 2),
]


def err_case(label, fn):
    try:
        r = fn()
        return f"{label} -> {r!r} ({type(r).__name__})"
    except Exception as e:  # noqa: BLE001 - we want the exception class
        return f"{label} -> raises {type(e).__name__}: {e}"


print("python", sys.version.split()[0])
for label, fn in cases:
    print(err_case(label, fn))
print(err_case("float(10**400)", lambda: float(10**400)))
print(err_case("(10**400) / 1", lambda: (10**400) / 1))
print(err_case("(1+2j) // 1", lambda: (1 + 2j) // 1))
print(err_case("int(float('nan'))", lambda: int(float("nan"))))
print(err_case("int(float('inf'))", lambda: int(float("inf"))))
print(err_case("math.isqrt(2**64)", lambda: math.isqrt(2**64)))
