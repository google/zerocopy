#!/usr/bin/env python3
"""Toy model: single-analyte cutoff vs covariate-adjusted cutoff vs two-marker score vs a
second-tier classifier with a 'keep every true positive' threshold.

THIS IS A TOY MODEL. The population, analytes, covariate effects, prevalence and disease
shift are invented to expose mechanisms (covariate-driven false positives, matched-FPR
comparisons, optimism of thresholds chosen on evaluation data). No number printed here is a
property of any real screening programme, analyte, disorder, CLIR tool or published classifier.

Usage: python3 nbs_cutoff_toy.py [--seeds 5]
Requires: Python 3.10+, numpy.
"""
import argparse, json, math
import numpy as np


def cohort(rng, n_unaff, prev):
    n_aff = rng.binomial(n_unaff, prev)
    n = n_unaff + n_aff
    aff = np.zeros(n, bool); aff[:n_aff] = True
    low_bw = rng.random(n) < 0.08                       # 8 % low birth weight (toy)
    bw = np.where(low_bw, rng.normal(1.8, 0.4, n), rng.normal(3.3, 0.5, n)).clip(0.5, 5.5)   # kg
    aac = np.where(rng.random(n) < 0.05, rng.uniform(6, 24, n), rng.uniform(24, 72, n))      # hours
    # log analyte X and partner analyte Y; X rises with low BW and early collection (toy covariate effects)
    zx = rng.normal(0, 0.25, n); zy = 0.6 * zx + rng.normal(0, 0.25, n)
    lx = 0.0 + 0.30 * (3.3 - bw).clip(0, None) + 0.004 * (48 - aac) + zx
    ly = 1.0 + 0.10 * (3.3 - bw).clip(0, None) + zy
    shift = rng.normal(1.6, 0.5, n)                    # heterogeneous disease effect on log X (toy)
    lx = lx + np.where(aff, shift, 0.0)
    ly = ly - np.where(aff, 0.15 * shift, 0.0)           # partner moves the other way (ratio informative)
    return dict(aff=aff, bw=bw, aac=aac, lx=lx, ly=ly, low_bw=low_bw)


def design(c):
    return np.column_stack([np.ones(len(c['bw'])), (3.3 - c['bw']).clip(0, None), 48 - c['aac']])


def fit_ls(Xd, y):
    return np.linalg.lstsq(Xd, y, rcond=None)[0]


def logistic_fit(X, y, iters=400, lr=0.5, l2=1e-3):
    mu, sd = X.mean(0), X.std(0) + 1e-12
    Z = np.column_stack([np.ones(len(X)), (X - mu) / sd]); w = np.zeros(Z.shape[1])
    for _ in range(iters):
        p = 1 / (1 + np.exp(-Z @ w)); g = Z.T @ (p - y) / len(y) + l2 * np.r_[0, w[1:]]
        w -= lr * g
    return lambda Xn: 1 / (1 + np.exp(-np.column_stack([np.ones(len(Xn)), (Xn - mu) / sd]) @ w))


def run(seed, n_unaff=1_000_000, prev=5e-5):
    rng = np.random.default_rng(seed)
    c = cohort(rng, n_unaff, prev)
    aff = c['aff']; un = ~aff
    out = {'n_total': int(len(aff)), 'n_affected': int(aff.sum())}
    # A: fixed cutoff on raw log X at the 99.5th percentile of the unaffected population
    cutA = np.quantile(c['lx'][un], 0.995)
    posA = c['lx'] >= cutA
    # B: covariate-adjusted cutoff on residuals (regression fitted on all specimens, as a programme would)
    beta = fit_ls(design(c), c['lx']); rx = c['lx'] - design(c) @ beta
    cutB = np.quantile(rx[un], 0.995); posB = rx >= cutB
    # C: two-marker score = adjusted X residual minus adjusted Y residual (log ratio), cutoff chosen to match A's sensitivity
    by = fit_ls(design(c), c['ly']); ry = c['ly'] - design(c) @ by
    score = rx - ry
    sensA = posA[aff].mean()
    cutC = np.quantile(score[aff], 1 - sensA) if aff.sum() else np.inf
    posC = score >= cutC
    for nm, pos in (('A_raw_cutoff', posA), ('B_covariate_adjusted_cutoff', posB), ('C_two_marker_score_matched_sens', posC)):
        tp = int((pos & aff).sum()); fp = int((pos & un).sum())
        out[nm] = {'sensitivity': tp / max(1, int(aff.sum())), 'false_positives': fp, 'fpr_pct': 100 * fp / un.sum(),
                   'ppv_pct': 100 * tp / max(1, tp + fp),
                   'fp_share_low_bw_pct': 100 * float((pos & un & c['low_bw']).sum()) / max(1, fp)}
    # D: second-tier logistic classifier among A-positives; threshold keeps every TP
    idx = np.where(posA)[0]
    X = np.column_stack([rx[idx], ry[idx], c['bw'][idx], c['aac'][idx]]); y = aff[idx].astype(float)
    folds = rng.permutation(len(idx)) % 10; cv = np.zeros(len(idx))
    for k in range(10):
        tr, te = folds != k, folds == k
        cv[te] = logistic_fit(X[tr], y[tr])(X[te])
    thr_in = cv[y == 1].min()                           # threshold chosen on the same held-out scores it is judged on
    keep_in = cv >= thr_in
    model = logistic_fit(X, y)
    # independent next-year cohort, same generating process, first-tier cutoff cutA reused
    c2 = cohort(rng, n_unaff, prev); aff2 = c2['aff']
    rx2 = c2['lx'] - design(c2) @ beta; ry2 = c2['ly'] - design(c2) @ by
    pos2 = c2['lx'] >= cutA; idx2 = np.where(pos2)[0]
    s2 = model(np.column_stack([rx2[idx2], ry2[idx2], c2['bw'][idx2], c2['aac'][idx2]]))
    thr_train = model(X)[y == 1].min()                  # 'keep every TP' threshold fixed on training cohort (in-sample)
    keep2 = s2 >= thr_train
    y2 = aff2[idx2]
    out['D_second_tier_classifier'] = {
        'first_tier_positives': int(len(idx)), 'first_tier_tp': int(y.sum()),
        'cv_threshold_fp_reduction_pct': 100 * (1 - (keep_in & (y == 0)).sum() / max(1, (y == 0).sum())),
        'cv_threshold_sensitivity_among_screen_pos': float(keep_in[y == 1].mean()),
        'next_cohort_first_tier_tp': int(y2.sum()),
        'next_cohort_fp_reduction_pct': 100 * (1 - (keep2 & ~y2).sum() / max(1, (~y2).sum())),
        'next_cohort_sensitivity_among_screen_pos': float(keep2[y2].mean()) if y2.sum() else None,
        'next_cohort_missed_tp': int((~keep2 & y2).sum()),
    }
    return out


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--seeds', type=int, default=5)
    a = ap.parse_args()
    res = {f'seed{s}': run(s) for s in range(a.seeds)}
    summ = {}
    for grp in ('A_raw_cutoff', 'B_covariate_adjusted_cutoff', 'C_two_marker_score_matched_sens', 'D_second_tier_classifier'):
        keys = res['seed0'][grp].keys()
        summ[grp] = {k: {'median': float(np.median([r[grp][k] for r in res.values() if r[grp][k] is not None])),
                         'min': float(np.min([r[grp][k] for r in res.values() if r[grp][k] is not None])),
                         'max': float(np.max([r[grp][k] for r in res.values() if r[grp][k] is not None]))} for k in keys}
    summ['D_second_tier_classifier']['seeds_with_any_missed_tp_next_cohort'] = int(sum(1 for r in res.values() if r['D_second_tier_classifier']['next_cohort_missed_tp'] > 0))
    summ['seeds'] = a.seeds
    print(json.dumps({'summary': summ, 'per_seed': res}, indent=1, default=float))
