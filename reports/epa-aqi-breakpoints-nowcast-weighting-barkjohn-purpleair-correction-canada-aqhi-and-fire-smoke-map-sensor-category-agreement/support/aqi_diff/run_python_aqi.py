#!/usr/bin/env python3
"""Evaluate python-aqi (hrbonz/python-aqi, EPA_2015 and EPA_2024 classes) on grid.csv.
Usage: python3 run_python_aqi.py <outdir>   (expects <outdir>/grid.csv)
Output: <outdir>/pyaqi.csv with columns pollutant,conc,py2015,py2015_x,py2024,py2024_x
(_x = extrapolate=True). Errors are recorded by exception class name.
"""
import csv
import sys

from aqi.algos.epa import EPA_2015, EPA_2024
from aqi.constants import (POLLUTANT_CO_8H, POLLUTANT_NO2_1H, POLLUTANT_O3_1H, POLLUTANT_O3_8H,
                           POLLUTANT_PM10, POLLUTANT_PM25, POLLUTANT_SO2_1H)

ELEM = {"pm25": POLLUTANT_PM25, "pm10": POLLUTANT_PM10, "co": POLLUTANT_CO_8H, "so2": POLLUTANT_SO2_1H,
        "no2": POLLUTANT_NO2_1H, "o3_8h": POLLUTANT_O3_8H, "o3_1h": POLLUTANT_O3_1H}


def ev(algo, elem, s, x):
    try:
        v = algo.iaqi(elem, s, extrapolate=x)
        return str(int(v)) if v is not None else "None"
    except Exception as e:  # noqa: BLE001 - record the class of the refusal
        return type(e).__name__


def main(outdir):
    a15, a24 = EPA_2015(), EPA_2024()
    with open(f"{outdir}/grid.csv") as f, open(f"{outdir}/pyaqi.csv", "w", newline="") as g:
        r = csv.DictReader(f)
        w = csv.writer(g)
        w.writerow(["pollutant", "conc", "py2015", "py2015_x", "py2024", "py2024_x"])
        for row in r:
            e = ELEM[row["pollutant"]]
            s = row["conc"]
            w.writerow([row["pollutant"], s, ev(a15, e, s, False), ev(a15, e, s, True),
                        ev(a24, e, s, False), ev(a24, e, s, True)])


if __name__ == "__main__":
    main(sys.argv[1])
