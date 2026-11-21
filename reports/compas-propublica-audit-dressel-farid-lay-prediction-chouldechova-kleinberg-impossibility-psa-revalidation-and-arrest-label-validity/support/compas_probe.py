#!/usr/bin/env python3
"""Standalone probe over the public COMPAS audit data (stdlib only, Python 3.10+).

Input: compas-scores-two-years.csv from propublica/compas-analysis at revision
bafff5da3f2e45eca6c2d5055faad269defd135a (expected SHA-256
c451db85908b2f7fef1d83203bedf6b71ecda0d5af468d82ae62178f91d0cc7d).

Fetch:
  curl -sSL -o /tmp/compas-scores-two-years.csv \
    https://raw.githubusercontent.com/propublica/compas-analysis/bafff5da3f2e45eca6c2d5055faad269defd135a/compas-scores-two-years.csv
Run:
  python3 compas_probe.py /tmp/compas-scores-two-years.csv

What it computes (all on the published file; nothing here re-implements COMPAS):
  1. The audit's cohort filter (|days_b_screening_arrest| <= 30, is_recid != -1,
     c_charge_degree != 'O', score_text != 'N/A') and the unfiltered file.
  2. Per-group confusion matrices for "Medium or High" (decile_score >= 5,
     equivalently score_text != 'Low') versus two_year_recid.
  3. Chouldechova's identity FPR = p/(1-p) * (1-PPV)/PPV * (1-FNR) per group.
  4. Kleinberg et al. conditions: per-decile observed rates by group
     (calibration within groups) and mean decile among non-recidivists and
     recidivists (balance for the negative and positive class).
  5. AUC of decile_score per group (Mann-Whitney with ties).
  6. Group metrics following fairlearn's definitions (equalized-odds difference
     = max(|TPR gap|, |FPR gap|); demographic-parity difference = selection-rate
     gap) -- re-implemented here, fairlearn itself is not executed.
  7. Simple baselines: logistic regression on (age, priors_count) and the
     CORELS README rule list, evaluated by 10-fold cross-validation (logistic)
     or directly (rule list), with percentile-bootstrap 95% intervals.
  8. Consistency of the file's `age` column with age at the screening date.
"""
import csv
import hashlib
import math
import random
import sys
import time
from datetime import date

T0 = time.perf_counter()
path = sys.argv[1]
raw = open(path, 'rb').read()
print('sha256', hashlib.sha256(raw).hexdigest())

with open(path, newline='') as f:
    reader = csv.reader(f)
    header = next(reader)
    rows_raw = list(reader)
# The header repeats some names (decile_score, priors_count); keep the first.
idx = {}
for i, h in enumerate(header):
    idx.setdefault(h, i)
rows = [{h: r[i] for h, i in idx.items()} for r in rows_raw]
print('rows_in_file', len(rows))


def audit_filter(r):
    d = r['days_b_screening_arrest']
    if d == '':
        return False  # R's filter() drops NA comparisons
    d = int(float(d))
    return (-30 <= d <= 30 and r['is_recid'] != '-1'
            and r['c_charge_degree'] != 'O' and r['score_text'] != 'N/A')


cohorts = {'filtered': [r for r in rows if audit_filter(r)], 'unfiltered': rows}
for k, v in cohorts.items():
    print(f'cohort {k}: n={len(v)}')

AA, CA = 'African-American', 'Caucasian'


def conf(rs, pred):
    tp = fp = tn = fn = 0
    for r in rs:
        y = r['two_year_recid'] == '1'
        p = pred(r)
        if y and p:
            tp += 1
        elif y:
            fn += 1
        elif p:
            fp += 1
        else:
            tn += 1
    return tp, fp, tn, fn


def rates(tp, fp, tn, fn):
    n = tp + fp + tn + fn
    p = (tp + fn) / n
    fpr = fp / (fp + tn)
    fnr = fn / (fn + tp)
    ppv = tp / (tp + fp)
    npv = tn / (tn + fn)
    acc = (tp + tn) / n
    sel = (tp + fp) / n
    return dict(n=n, prev=p, fpr=fpr, fnr=fnr, tpr=1 - fnr, ppv=ppv, npv=npv,
                acc=acc, sel=sel)


def med_high(r):
    return int(r['decile_score']) >= 5


def auc(rs):
    pos = [int(r['decile_score']) for r in rs if r['two_year_recid'] == '1']
    neg = [int(r['decile_score']) for r in rs if r['two_year_recid'] == '0']
    cnt_neg = {}
    for s in neg:
        cnt_neg[s] = cnt_neg.get(s, 0) + 1
    tot = 0.0
    for s in pos:
        for t, c in cnt_neg.items():
            if s > t:
                tot += c
            elif s == t:
                tot += 0.5 * c
    return tot / (len(pos) * len(neg))


for cname, rs in cohorts.items():
    print(f'\n== cohort {cname} ==')
    assert all((int(r['decile_score']) >= 5) == (r['score_text'] != 'Low')
               for r in rs if r['score_text'] in ('Low', 'Medium', 'High'))
    groups = {'all': rs, AA: [r for r in rs if r['race'] == AA],
              CA: [r for r in rs if r['race'] == CA]}
    res = {}
    for g, grs in groups.items():
        c = conf(grs, med_high)
        m = rates(*c)
        res[g] = m
        print(f'{g:18s} n={m["n"]:5d} TP={c[0]} FP={c[1]} TN={c[2]} FN={c[3]} '
              f'prev={m["prev"]:.4f} FPR={m["fpr"]:.4f} FNR={m["fnr"]:.4f} '
              f'PPV={m["ppv"]:.4f} NPV={m["npv"]:.4f} acc={m["acc"]:.4f} '
              f'sel={m["sel"]:.4f} AUC={auc(grs):.4f}')
        # Chouldechova identity
        p = m['prev']
        rhs = p / (1 - p) * (1 - m['ppv']) / m['ppv'] * (1 - m['fnr'])
        print(f'   chouldechova: FPR={m["fpr"]:.6f} identity_rhs={rhs:.6f}')
    a, w = res[AA], res[CA]
    print(f'FPR ratio AA/CA={a["fpr"]/w["fpr"]:.4f}  FNR ratio CA/AA={w["fnr"]/a["fnr"]:.4f}')
    print(f'fairlearn-style equalized_odds_difference(AA vs CA)='
          f'{max(abs(a["tpr"]-w["tpr"]), abs(a["fpr"]-w["fpr"])):.4f} '
          f'demographic_parity_difference={abs(a["sel"]-w["sel"]):.4f} '
          f'PPV gap={abs(a["ppv"]-w["ppv"]):.4f}')
    # Kleinberg conditions
    print('decile  n_AA  rate_AA  n_CA  rate_CA')
    for d in range(1, 11):
        ga = [r for r in groups[AA] if int(r['decile_score']) == d]
        gw = [r for r in groups[CA] if int(r['decile_score']) == d]
        ra = sum(r['two_year_recid'] == '1' for r in ga) / len(ga) if ga else float('nan')
        rw = sum(r['two_year_recid'] == '1' for r in gw) / len(gw) if gw else float('nan')
        print(f'{d:6d} {len(ga):5d} {ra:8.3f} {len(gw):5d} {rw:8.3f}')
    for g in (AA, CA):
        neg = [int(r['decile_score']) for r in groups[g] if r['two_year_recid'] == '0']
        pos = [int(r['decile_score']) for r in groups[g] if r['two_year_recid'] == '1']
        print(f'{g}: mean decile | no recid = {sum(neg)/len(neg):.3f} (n={len(neg)}); '
              f'| recid = {sum(pos)/len(pos):.3f} (n={len(pos)})')

# --- 8. age column consistency -------------------------------------------
def years_between(b, d):
    return d.year - b.year - ((d.month, d.day) < (b.month, b.day))

diffs = {}
for r in cohorts['unfiltered']:
    b = date.fromisoformat(r['dob'])
    s = date.fromisoformat(r['compas_screening_date'])
    a_scr = years_between(b, s)
    diffs[int(r['age']) - a_scr] = diffs.get(int(r['age']) - a_scr, 0) + 1
print('\nage column minus age at screening date (unfiltered):', dict(sorted(diffs.items())))


def age_cat(a):
    return 'Less than 25' if a < 25 else ('Greater than 45' if a > 45 else '25 - 45')

mis = sum(age_cat(years_between(date.fromisoformat(r['dob']), date.fromisoformat(r['compas_screening_date']))) != r['age_cat']
          for r in cohorts['filtered'])
print('filtered rows whose age_cat differs from the category of age at screening:', mis)

# --- 7. simple baselines ---------------------------------------------------
rs = cohorts['filtered']
X = [(float(r['age']), float(r['priors_count'])) for r in rs]
Y = [1 if r['two_year_recid'] == '1' else 0 for r in rs]
race = [r['race'] for r in rs]


def fit_logit(xs, ys, iters=25):
    # Newton-Raphson on standardized features; returns predictor closure.
    k = len(xs[0])
    mu = [sum(x[j] for x in xs) / len(xs) for j in range(k)]
    sd = [math.sqrt(sum((x[j] - mu[j]) ** 2 for x in xs) / len(xs)) for j in range(k)]
    Z = [[1.0] + [(x[j] - mu[j]) / sd[j] for j in range(k)] for x in xs]
    b = [0.0] * (k + 1)
    for _ in range(iters):
        g = [0.0] * (k + 1)
        H = [[0.0] * (k + 1) for _ in range(k + 1)]
        for z, y in zip(Z, ys):
            eta = sum(bi * zi for bi, zi in zip(b, z))
            pr = 1 / (1 + math.exp(-eta))
            w = pr * (1 - pr)
            for i in range(k + 1):
                g[i] += (y - pr) * z[i]
                for j in range(k + 1):
                    H[i][j] += w * z[i] * z[j]
        # solve H d = g (Gaussian elimination)
        A = [row[:] + [gi] for row, gi in zip(H, g)]
        n = k + 1
        for c in range(n):
            piv = max(range(c, n), key=lambda r_: abs(A[r_][c]))
            A[c], A[piv] = A[piv], A[c]
            for r_ in range(n):
                if r_ != c:
                    f_ = A[r_][c] / A[c][c]
                    for cc in range(c, n + 1):
                        A[r_][cc] -= f_ * A[c][cc]
        d = [A[i][n] / A[i][i] for i in range(n)]
        b = [bi + di for bi, di in zip(b, d)]
    def pred(x):
        z = [1.0] + [(x[j] - mu[j]) / sd[j] for j in range(k)]
        return 1 / (1 + math.exp(-sum(bi * zi for bi, zi in zip(b, z))))
    return pred, b

rng = random.Random(20261121)
order = list(range(len(rs)))
rng.shuffle(order)
folds = [order[i::10] for i in range(10)]
cv_pred = [None] * len(rs)
for f_ in folds:
    test = set(f_)
    tr = [i for i in range(len(rs)) if i not in test]
    pred, _ = fit_logit([X[i] for i in tr], [Y[i] for i in tr])
    for i in f_:
        cv_pred[i] = 1 if pred(X[i]) >= 0.5 else 0
compas_pred = [1 if int(r['decile_score']) >= 5 else 0 for r in rs]
_, coef = fit_logit(X, Y)


def auc_scores(scores, ys):
    pairs = sorted(zip(scores, ys))
    # rank-based Mann-Whitney with average ranks for ties
    ranks = [0.0] * len(pairs)
    i = 0
    while i < len(pairs):
        j = i
        while j + 1 < len(pairs) and pairs[j + 1][0] == pairs[i][0]:
            j += 1
        for k in range(i, j + 1):
            ranks[k] = (i + j) / 2 + 1
        i = j + 1
    npos = sum(y for _, y in pairs); nneg = len(pairs) - npos
    rpos = sum(r for r, (_, y) in zip(ranks, pairs) if y)
    return (rpos - npos * (npos + 1) / 2) / (npos * nneg)

# Same CV folds, keeping probabilities, with the file's `age` column and with
# age recomputed at the screening date.
X_scr = [(float(years_between(date.fromisoformat(r['dob']), date.fromisoformat(r['compas_screening_date']))),
          float(r['priors_count'])) for r in rs]
for label, XX in (('age column', X), ('age at screening', X_scr)):
    prob = [None] * len(rs)
    for f_ in folds:
        test = set(f_)
        tr = [i for i in range(len(rs)) if i not in test]
        pred, _ = fit_logit([XX[i] for i in tr], [Y[i] for i in tr])
        for i in f_:
            prob[i] = pred(XX[i])
    accv = sum((prob[i] >= 0.5) == bool(Y[i]) for i in range(len(rs))) / len(rs)
    print(f'logit(age,priors) [{label}] 10-fold CV acc={accv:.4f} AUC={auc_scores(prob, Y):.4f}')
print(f'COMPAS decile AUC on same cohort={auc_scores([int(r["decile_score"]) for r in rs], Y):.4f}')
print('\nlogit(age, priors) full-data standardized coefficients [b0, age, priors]:',
      [round(c, 4) for c in coef])


def rule_list(r):
    # CORELS README example rule list; age at screening date as in
    # processing/compas.py (age bins 18-20, 21-22, 23-25, 26-45, >45).
    a = years_between(date.fromisoformat(r['dob']), date.fromisoformat(r['compas_screening_date']))
    p = int(r['priors_count'])
    if 23 <= a <= 25 and 2 <= p <= 3:
        return 1
    if a <= 20:
        return 1
    if r['sex'] == 'Male' and 21 <= a <= 22:
        return 1
    if p > 3:
        return 1
    return 0

rule_pred = [rule_list(r) for r in rs]


def rule_list_jmlr(r):
    # Rule list printed as Figure 1 of Angelino et al. (JMLR 18(234), 2018):
    # (age 18-20 and male) -> yes; (age 21-23 and priors 2-3) -> yes;
    # (priors > 3) -> yes; else no.  Age at screening date.
    a = years_between(date.fromisoformat(r['dob']), date.fromisoformat(r['compas_screening_date']))
    p = int(r['priors_count'])
    if a <= 20 and r['sex'] == 'Male':
        return 1
    if 21 <= a <= 23 and 2 <= p <= 3:
        return 1
    if p > 3:
        return 1
    return 0

rule2_pred = [rule_list_jmlr(r) for r in rs]


def acc(pr, ix):
    return sum(pr[i] == Y[i] for i in ix) / len(ix)


def grp_rates(pr, g):
    ix = [i for i in range(len(rs)) if race[i] == g]
    tp = sum(1 for i in ix if pr[i] and Y[i]); fp = sum(1 for i in ix if pr[i] and not Y[i])
    tn = sum(1 for i in ix if not pr[i] and not Y[i]); fn = sum(1 for i in ix if not pr[i] and Y[i])
    return rates(tp, fp, tn, fn)

allix = list(range(len(rs)))
for name, pr in (('COMPAS decile>=5', compas_pred), ('logit(age,priors) 10-fold CV', cv_pred),
                 ('CORELS README rule list', rule_pred), ('Angelino et al. Fig. 1 rule list', rule2_pred)):
    a, w = grp_rates(pr, AA), grp_rates(pr, CA)
    print(f'{name:30s} acc={acc(pr, allix):.4f}  AA: FPR={a["fpr"]:.4f} FNR={a["fnr"]:.4f} PPV={a["ppv"]:.4f}'
          f'  CA: FPR={w["fpr"]:.4f} FNR={w["fnr"]:.4f} PPV={w["ppv"]:.4f}')

B = 1000
brng = random.Random(7)
d_logit, d_rule, d_rule2, a_comp = [], [], [], []
n = len(rs)
for _ in range(B):
    s = [brng.randrange(n) for _ in range(n)]
    ac = sum(compas_pred[i] == Y[i] for i in s) / n
    al = sum(cv_pred[i] == Y[i] for i in s) / n
    ar = sum(rule_pred[i] == Y[i] for i in s) / n
    ar2 = sum(rule2_pred[i] == Y[i] for i in s) / n
    a_comp.append(ac); d_logit.append(al - ac); d_rule.append(ar - ac); d_rule2.append(ar2 - ac)


def pct(v, q):
    v = sorted(v)
    return v[int(q * (len(v) - 1))]

print(f'bootstrap B={B}: COMPAS acc 95% [{pct(a_comp,0.025):.4f}, {pct(a_comp,0.975):.4f}]; '
      f'logit-COMPAS diff 95% [{pct(d_logit,0.025):+.4f}, {pct(d_logit,0.975):+.4f}]; '
      f'rule-COMPAS diff 95% [{pct(d_rule,0.025):+.4f}, {pct(d_rule,0.975):+.4f}]; '
      f'fig1rule-COMPAS diff 95% [{pct(d_rule2,0.025):+.4f}, {pct(d_rule2,0.975):+.4f}]')
print(f'elapsed_seconds {time.perf_counter()-T0:.2f}')
