#!/usr/bin/env python3
"""Python port of AirMonitor .nowcast(x, numHrs=12, weightFactorMin=0.5, includeShortTerm=TRUE)
followed by trunc(x*10)/10, validated against the R original on a subset, then applied to all
sensors of USEPA/FASM-sensor-AQI-analysis data/purpleair_data.csv.

Port notes (R semantics reproduced):
  for i = n..2 (1-based): window = x[i], x[i-1], ..., x[max(1, i-11)] (raw values; x is updated
  in place from the end backwards, so earlier entries are still raw when used);
  if >= 2 of the first 3 window entries are NA (an entry beyond the window start counts as NA): NA;
  else w = 1 - (max - min)/max over non-NA window values; w = min(w, 1); w = max(w, 0.5, 0)
  (NaN from 0/0 is dropped by na.rm in min(w, 1, na.rm = TRUE), leaving w = 1); NowCast = sum(c_j w^j)/sum(w^j) over non-NA.
  x[1] = NA.
Usage: fasm_port.py <purpleair_data.csv> <r_nowcast_subset.csv> <n_subset>
"""
import sys

import numpy as np
import pandas as pd


def nowcast_col(x):
    n = len(x)
    out = np.full(n, np.nan)
    for i in range(n - 1, 0, -1):  # 0-based i = n-1 .. 1  (R: n .. 2)
        lo = max(0, i - 11)
        win = x[lo:i + 1][::-1]  # most recent first
        first3 = list(win[:3]) + [np.nan] * (3 - len(win[:3]))
        if sum(np.isnan(v) for v in first3) >= 2:
            continue
        vals = win[~np.isnan(win)]
        mn, mx = vals.min(), vals.max()
        with np.errstate(divide="ignore", invalid="ignore"):
            w = 1 - (mx - mn) / mx
        cands = [v for v in (w,) if not np.isnan(v)]
        w = min(cands + [1.0]) if cands else 1.0
        w = max([w, 0.5, 0.0])
        js = np.arange(len(win))
        m = ~np.isnan(win)
        wts = w ** js[m]
        out[i] = np.sum(win[m] * wts) / np.sum(wts)
    return np.trunc(out * 10) / 10


def nowcast_matrix(X):
    """Column-vectorized version of nowcast_col (same semantics), for all sensors at once."""
    n, m = X.shape
    out = np.full((n, m), np.nan)
    for i in range(n - 1, 0, -1):
        lo = max(0, i - 11)
        win = X[lo:i + 1][::-1]  # (k, m), most recent first
        k = win.shape[0]
        first3 = np.full((3, m), np.nan)
        first3[:min(3, k)] = win[:3]
        bad = np.isnan(first3).sum(axis=0) >= 2
        valid = ~np.isnan(win)
        with np.errstate(all="ignore"):
            mx = np.nanmax(np.where(valid, win, -np.inf), axis=0)
            mn = np.nanmin(np.where(valid, win, np.inf), axis=0)
            w = 1 - (mx - mn) / mx
        w = np.where(np.isnan(w), 1.0, np.minimum(w, 1.0))
        w = np.maximum(np.maximum(w, 0.5), 0.0)
        js = np.arange(k)[:, None]
        wts = np.where(valid, w[None, :] ** js, 0.0)
        with np.errstate(all="ignore"):
            res = np.nansum(np.where(valid, win, 0.0) * wts, axis=0) / wts.sum(axis=0)
        out[i] = np.where(bad, np.nan, res)
    return np.trunc(out * 10) / 10


def tad_cat(v):
    return np.select([v <= 9.0, v <= 35.4, v <= 55.4, v <= 125.4, v <= 225.4], [1, 2, 3, 4, 5], 6)


def fasm_cat(v):
    # .bincode(x, c(-Inf, 9.0, 35.5, 55.5, 125.5, 225.5, Inf)), right = TRUE: (a, b]
    return np.select([v <= 9.0, v <= 35.5, v <= 55.5, v <= 125.5, v <= 225.5], [1, 2, 3, 4, 5], 6)


def main(data_csv, r_csv, nsub):
    d = pd.read_csv(data_csv)
    X = d.drop(columns=["datetime"]).to_numpy(dtype=float)
    R = pd.read_csv(r_csv).to_numpy(dtype=float)
    P = np.column_stack([nowcast_col(X[:, j]) for j in range(nsub)])
    same = (np.isnan(P) & np.isnan(R)) | (P == R)
    print(f"port vs R on {nsub} sensors: identical cells {same.sum()} of {same.size}; max|diff| "
          f"{np.nanmax(np.abs(P - R)):.3g}")
    NC = nowcast_matrix(X)
    sub = NC[:, :nsub]
    same2 = (np.isnan(sub) & np.isnan(R)) | (sub == R)
    print(f"vectorized port vs R on {nsub} sensors: identical cells {same2.sum()} of {same2.size}")
    ok = ~np.isnan(NC)
    v = NC[ok]
    t, f = tad_cat(v), fasm_cat(v)
    print("all sensors:", X.shape[1], "hours:", X.shape[0], "valid NowCast sensor-hours:", ok.sum())
    print("FASM category != TAD category:", int((t != f).sum()))
    for b in (35.5, 55.5, 125.5, 225.5):
        print(f"NowCast exactly {b}: {int((v == b).sum())}")
    print("TAD category counts (1..6):", [int((t == k).sum()) for k in range(1, 7)])
    print("sensor-hours with NowCast >= 225.5:", int((v >= 225.5).sum()), " >= 1000:", int((v >= 1000).sum()))
    print("sensors with any NowCast >= 1000:", int((np.nan_to_num(NC, nan=0) >= 1000).any(axis=0).sum()))
    print("negative NowCast sensor-hours:", int((v < 0).sum()))


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]))
