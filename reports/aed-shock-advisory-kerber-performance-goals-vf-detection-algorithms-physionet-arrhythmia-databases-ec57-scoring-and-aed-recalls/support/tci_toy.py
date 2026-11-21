#!/usr/bin/env python3
"""Python port of the threshold-crossing-interval (TCI) feature as implemented
in FelipeURJC/ohca-vs-public-dbs at 4d799e936fea095db4aba3d08bfdc0aabffc29be,
file "ecg parameters computation/parameters/calculate_TCI.m" (lines 27-143),
which follows Thakor et al. 1990 and Amann et al. 2005:

  per 1-s stage: subtract the stage mean, threshold at 0.2 * stage maximum,
  binarize; for each 3-s window (stages 1..3) count pulses N in stage 2 and
  measure t1..t4 at the stage boundaries; then
      TCI = 1000 / ((N - 1) + t2/(t1 + t2) + t3/(t3 + t4))   [ms]
  and average over the (wL - 2) windows of a wL-second segment.

TOY MODEL: inputs are synthetic sinusoids and Gaussian pulse trains, not ECG.
Outputs characterize the TCI formula, not any detector's clinical accuracy.
numpy is the only dependency.
"""
import numpy as np


def tci(xf, fs, wL):
    wl = int(fs)
    L = wL - 3 + 1
    vals = []
    for j in range(L):
        becg = []
        for k in range(3):
            st = xf[(j + k) * wl:(j + k + 1) * wl]
            st = st - st.mean()
            th = 0.2 * st.max()
            becg.append((st > th).astype(int))
        becg = np.concatenate(becg)
        aux = np.concatenate(([0], np.diff(becg)))
        s1 = np.nonzero(aux[0:wl] == -1)[0] + 1          # MATLAB 1-based
        t1 = 1.0 if s1.size == 0 else (wl - s1[-1]) / fs
        seg = aux[wl:2 * wl]
        index = np.nonzero(seg)[0] + 1                     # MATLAB 1-based
        pulses = seg[index - 1]
        if pulses.size == 0:
            # calculate_TCI.m line 68 evaluates pulses(1) unconditionally;
            # on an empty array MATLAB raises an index error.
            raise IndexError("no threshold crossing in the middle 1-s stage")
        if pulses[0] == -1 and pulses[-1] == -1:
            t2, t3, N = 0.0, (wl - index[-1]) / fs, (pulses.size + 1) / 2
        elif pulses[0] == 1 and pulses[-1] == 1:
            t2, t3, N = index[0] / fs, 0.0, (pulses.size + 1) / 2
        elif pulses[0] == -1 and pulses[-1] == 1:
            t2, t3, N = 0.0, 0.0, (pulses.size + 2) / 2
        else:
            t2, t3, N = index[0] / fs, (wl - index[-1]) / fs, pulses.size / 2
        s4 = np.nonzero(aux[2 * wl:3 * wl] == 1)[0] + 1
        t4 = 1.0 if s4.size == 0 else s4[0] / fs
        vals.append(1000.0 / ((N - 1) + t2 / (t1 + t2) + t3 / (t3 + t4)))
    return float(np.mean(vals))


def main():
    fs, wL = 250, 8
    t = np.arange(wL * fs) / fs
    print("TCI toy model (fs=%d Hz, %d-s segments); Thakor/Amann rule: TCI < 400 ms -> VF/VT branch" % (fs, wL))
    print("sinusoids (phase 0.3 rad):")
    for f in (1.0, 1.5, 2.0, 2.4, 2.5, 2.6, 3.0, 4.0, 5.0):
        x = np.sin(2 * np.pi * f * t + 0.3)
        v = tci(x, fs, wL)
        print("  f=%.1f Hz (%3.0f/min): TCI=%6.1f ms  1000/f=%6.1f  -> %s" % (
            f, 60 * f, v, 1000 / f, "VF/VT branch" if v < 400 else "SR"))
    print("Gaussian pulse trains (sigma 12 ms), i.e. narrow regular 'beats':")
    for bpm in (60, 100, 150, 180, 240):
        period = 60.0 / bpm
        x = np.zeros_like(t)
        for c in np.arange(0.2, wL, period):
            x += np.exp(-0.5 * ((t - c) / 0.012) ** 2)
        v = tci(x, fs, wL)
        print("  %3d/min: TCI=%6.1f ms -> %s" % (bpm, v, "VF/VT branch" if v < 400 else "SR"))
    print("flat (constant) 8-s segment:")
    try:
        print("  TCI=", tci(np.zeros_like(t), fs, wL))
    except IndexError as e:
        print("  IndexError:", e)


if __name__ == "__main__":
    main()
