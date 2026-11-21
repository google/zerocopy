#!/usr/bin/env python3
"""Retrospective + hindcast probe for a Stock Synthesis (SS3) model.

Standard library only.  Usage:

    python3 ss3_retro_probe.py <ss3_executable> <model_dir> <work_dir> [peels]

For each peel k in 0, -1, ..., -peels the script copies <model_dir> to
<work_dir>/retro<k>, sets `retro_yr = k` and `init_values_src = 0` in
starter.ss, applies the same year shifts that r4ss::retro() applies by
default (adjustments = recdevs, biasadj, blocks, forecast, benchmarks; see
r4ss R/retro.R), runs SS3 with no extra arguments (r4ss::run() default
extras = ""), and records wall time and peak RSS via /usr/bin/time -v.

It then parses DERIVED_QUANTITIES (SSB_yyyy, F_yyyy, Recr_yyyy, Bratio_yyyy)
and INDEX_2 (Fleet, Yr, Obs, Exp, Use) from each Report.sso and computes:

  * the three Mohn's rho variants returned by r4ss::SSmohnsrho()
    (transcribed from r4ss R/SSmohnsrho.R; r4ss itself is NOT executed);
  * ss3diags::SShcbias() rho and one-step-ahead forecast rho
    (transcribed from ss3diags R/SShcbias.R);
  * ss3diags::SSmase() MASE per index (transcribed from ss3diags R/SSmase.R,
    default MAE.base.adj = 0.1).

Transcriptions are re-implementations; agreement with the R packages has not
been checked by running R.
"""
import json
import os
import re
import shutil
import subprocess
import sys
import time


def edit_value_line(lines, comment_regex, new_value_fn):
    """Replace the leading value token(s) of the first line matching regex."""
    rx = re.compile(comment_regex)
    for i, ln in enumerate(lines):
        if rx.search(ln):
            body, sep, comment = ln.partition('#')
            toks = body.split()
            new_toks = new_value_fn(toks)
            lines[i] = ' ' + ' '.join(str(t) for t in new_toks) + ' ' + sep + comment
            return True
    raise RuntimeError('pattern not found: ' + comment_regex)


def shift_interval_pairs(vals, pair_starts, endyr, mean_year, delta):
    """Port of r4ss retro.R shift_interval_pairs (1-based pair_starts)."""
    vals = list(vals)
    for i in pair_starts:
        j = i - 1
        val = vals[j]
        if val <= 0:
            val = val + endyr
        if val < mean_year:
            vals[j + 1] = vals[j + 1] + delta
        else:
            vals[j] = vals[j] + delta
            vals[j + 1] = vals[j + 1] + delta
    return vals


def read_dat_years(datfile):
    styr = endyr = None
    with open(datfile) as f:
        for ln in f:
            if '#_StartYr' in ln:
                styr = int(ln.split()[0])
            elif '#_EndYr' in ln:
                endyr = int(ln.split()[0])
            if styr is not None and endyr is not None:
                return styr, endyr
    raise RuntimeError('styr/endyr not found')


def prepare_peel(model_dir, run_dir, k, starter_names):
    if os.path.exists(run_dir):
        shutil.rmtree(run_dir)
    shutil.copytree(model_dir, run_dir)
    st_path = os.path.join(run_dir, 'starter.ss')
    with open(st_path) as f:
        st = f.read().splitlines()
    datfile = st_names = None
    # data and control file names are the first two non-comment tokens
    toks = [ln.split()[0] for ln in st if ln.strip() and not ln.lstrip().startswith('#')]
    datfile, ctlfile = toks[0], toks[1]
    edit_value_line(st, r'#_retro_yr', lambda t: [k])
    edit_value_line(st, r'#_init_values_src', lambda t: [0])
    with open(st_path, 'w') as f:
        f.write('\n'.join(st) + '\n')
    styr, endyr = read_dat_years(os.path.join(run_dir, datfile))
    mean_year = (styr + endyr) / 2.0
    retro_endyr = endyr + k
    # control-file adjustments (r4ss: recdevs, biasadj)
    ctl_path = os.path.join(run_dir, ctlfile)
    with open(ctl_path) as f:
        ctl = f.read().splitlines()
    edit_value_line(ctl, r'last year of main recr_devs', lambda t: [int(t[0]) + k])
    edit_value_line(ctl, r'#_last_yr_fullbias_adj_in_MPD', lambda t: [float(t[0]) + k])
    edit_value_line(ctl, r'#_end_yr_for_ramp_in_MPD', lambda t: [float(t[0]) + k])
    with open(ctl_path, 'w') as f:
        f.write('\n'.join(ctl) + '\n')
    # forecast-file adjustments (r4ss: forecast, benchmarks), legacy vector format
    fc_path = os.path.join(run_dir, 'forecast.ss')
    with open(fc_path) as f:
        fc = f.read().splitlines()
    out = []
    state = None
    for ln in fc:
        s = ln.strip()
        if s.startswith('# Bmark_years'):
            state = 'bmark'
            out.append(ln)
            continue
        if s.startswith('#_Fcast_years'):
            state = 'fcast'
            out.append(ln)
            continue
        if state and s and not s.startswith('#'):
            vals = [int(float(x)) for x in s.split('#')[0].split()]
            if state == 'bmark':
                vals = shift_interval_pairs(vals, [1, 3, 5, 7, 9], endyr, mean_year, k)
            else:
                vals = shift_interval_pairs(vals, [1, 3, 5], endyr, mean_year, k)
            ln = ' ' + ' '.join(str(v) for v in vals)
            state = None
        out.append(ln)
    with open(fc_path, 'w') as f:
        f.write('\n'.join(out) + '\n')
    return styr, endyr, retro_endyr


def run_ss3(exe, run_dir):
    t0 = time.time()
    p = subprocess.run(['/usr/bin/time', '-v', exe], cwd=run_dir, capture_output=True, text=True)
    wall = time.time() - t0
    rss = None
    m = re.search(r'Maximum resident set size \(kbytes\): (\d+)', p.stderr)
    if m:
        rss = int(m.group(1))
    return p.returncode, wall, rss


def parse_report(path):
    with open(path, errors='replace') as f:
        lines = f.read().splitlines()
    dq = {}
    idx = []
    endyr = None
    i = 0
    n = len(lines)
    while i < n:
        ln = lines[i]
        if ln.startswith('DERIVED_QUANTITIES'):
            i += 1
            while i < n and not ln.startswith('Label'):
                ln = lines[i]
                i += 1
            while i < n and lines[i].strip():
                t = lines[i].split()
                try:
                    dq[t[0]] = float(t[1])
                except (ValueError, IndexError):
                    pass
                i += 1
            continue
        if ln.startswith('INDEX_2'):
            i += 1
            while i < n and not lines[i].startswith('Fleet '):
                i += 1
            hdr = lines[i].split()
            i += 1
            while i < n and lines[i].strip():
                t = lines[i].split()
                if len(t) == len(hdr):
                    idx.append(dict(zip(hdr, t)))
                i += 1
            continue
        m = re.match(r'^Data_File|^Start_time', ln)
        i += 1
    return dq, idx


def series(dq, prefix):
    out = {}
    rx = re.compile('^' + prefix + r'_(\d{4})$')
    for k, v in dq.items():
        m = rx.match(k)
        if m:
            out[int(m.group(1))] = v
    return out


def ssmohnsrho(models, endyrvec, startyr):
    """Transcription of r4ss SSmohnsrho(). models[0] is the reference."""
    N = len(models)
    res = {}
    for q in ('SSB', 'Recr', 'Bratio', 'F'):
        terminal = []
        allyrs = []
        for i in range(1, N):
            y = endyrvec[i]
            ref = models[0][q]
            ret = models[i][q]
            terminal.append((ret[y] - ref[y]) / ref[y])
            y0 = startyr if q == 'F' else startyr + 1
            yrs = [yy for yy in range(y0, y + 1) if yy in ref and yy in ret]
            allyrs.append(sum((ret[yy] - ref[yy]) / ref[yy] for yy in yrs) / len(yrs))
        res[q] = {
            'Mohn1999_sum': sum(terminal),
            'WoodsHole_all_sum_over_peels': sum(allyrs),
            'AFSC_Hurtado_mean': sum(terminal) / len(terminal),
            'per_peel_terminal': terminal,
        }
    return res


def sshcbias(models, endyrvec, q):
    """Transcription of ss3diags SShcbias() for one quantity."""
    ref = models[0][q]
    rho_i, fc_i = [], []
    for i in range(1, len(models)):
        y = endyrvec[i]
        ret = models[i][q]
        rho_i.append((ret[y] - ref[y]) / ref[y])
        fc_i.append((ret[y + 1] - ref[y + 1]) / ref[y + 1])
    return {'rho_mean': sum(rho_i) / len(rho_i), 'forecast_rho_mean': sum(fc_i) / len(fc_i),
            'rho_i': rho_i, 'forecast_rho_i': fc_i}


def ssmase(index_by_model, endyrvec, fleet, mae_base_adj=0.1):
    """Transcription of ss3diags SSmase() inner mase() for one index fleet.

    index_by_model[i] is a list of dict rows (Fleet, Yr, Obs, Exp, Use) for model i.
    Rows used in the reference run (model 0, Use==1) define which (fleet, time)
    pairs are kept.  Only one season is assumed.
    """
    def rows(i):
        return [r for r in index_by_model[i] if int(r['Fleet']) == fleet]
    ref_used = {int(r['Yr']) for r in rows(0) if float(r['Use']) == 1}
    yr_ref = sorted(ref_used)
    obs_by_year = {int(r['Yr']): float(r['Obs']) for r in rows(0) if int(r['Yr']) in ref_used}
    yr_eval = sorted(endyrvec)
    pe_eval = [j for j, y in enumerate(yr_eval) if y in ref_used]
    # mirror: if(length(which(yr.eval%in%yr))-length(pe.eval)<1) pe.eval = pe.eval[-1]
    if len(pe_eval) - len(pe_eval) < 1:
        pe_eval = pe_eval[1:]
    npe = len(pe_eval)
    obs_eval = [obs_by_year.get(y) for y in yr_eval]
    if not (any(y in ref_used for y in endyrvec) and sum(1 for y in yr_eval if y in ref_used) > 1):
        return {'MASE': None, 'n.eval': 0}
    xmin = min(endyrvec) - 5
    pred = []
    for i in range(1, len(endyrvec)):
        if endyrvec[i - 1] in ref_used:
            sub = [r for r in rows(i) if int(r['Yr']) in ref_used and int(r['Yr']) <= endyrvec[i] + 1 and int(r['Yr']) >= xmin]
            sub.sort(key=lambda r: int(r['Yr']))
            last = sub[-1]
            pred.append(__import__('math').log(float(last['Exp'])) - __import__('math').log(float(last['Obs'])))
    if len(pred) > len(pe_eval):
        pred = pred[1:]
    import math
    maepr = sum(abs(x) for x in pred) / len(pred)
    nonna = [o for o in obs_eval if o is not None]
    naive = [math.log(obs_eval[j]) - math.log(nonna[m]) for m, j in enumerate(pe_eval)]
    scaler = sum(abs(x) for x in naive) / len(naive)
    return {'MASE': maepr / scaler, 'MAE.PR': maepr, 'MAE.base': scaler,
            'MASE.adj': maepr / max(scaler, mae_base_adj), 'n.eval': npe,
            'pred_resid': pred, 'naive_resid': naive,
            'eval_years': [yr_eval[j] for j in pe_eval]}


def main():
    exe, model_dir, work_dir = sys.argv[1], sys.argv[2], sys.argv[3]
    peels = int(sys.argv[4]) if len(sys.argv) > 4 else 5
    os.makedirs(work_dir, exist_ok=True)
    runs = []
    models = []
    indices = []
    for k in range(0, -peels - 1, -1):
        rd = os.path.join(work_dir, 'retro%d' % k)
        if os.environ.get('REUSE') == '1':
            # re-parse existing runs without re-running SS3
            st_toks = [ln.split()[0] for ln in open(os.path.join(rd, 'starter.ss')).read().splitlines()
                       if ln.strip() and not ln.lstrip().startswith('#')]
            styr, endyr = read_dat_years(os.path.join(rd, st_toks[0]))
            retro_endyr = endyr + k
            rc, wall, rss = None, None, None
        else:
            styr, endyr, retro_endyr = prepare_peel(model_dir, rd, k, None)
            rc, wall, rss = run_ss3(exe, rd)
        dq, idx = parse_report(os.path.join(rd, 'Report.sso'))
        models.append({'SSB': series(dq, 'SSB'), 'F': series(dq, 'F'),
                       'Recr': series(dq, 'Recr'), 'Bratio': series(dq, 'Bratio')})
        indices.append(idx)
        runs.append({'peel': k, 'returncode': rc, 'wall_s': (round(wall, 3) if wall is not None else None), 'max_rss_kb': rss,
                     'retro_endyr': retro_endyr})
        print(json.dumps(runs[-1]), flush=True)
    endyrvec = [endyr + k for k in range(0, -peels - 1, -1)]
    out = {'runs': runs, 'endyrvec': endyrvec,
           'SSmohnsrho': ssmohnsrho(models, endyrvec, styr),
           'SShcbias_SSB': sshcbias(models, endyrvec, 'SSB'),
           'SShcbias_F': sshcbias(models, endyrvec, 'F'),
           'terminal_SSB_by_peel': {str(endyrvec[i]): models[i]['SSB'][endyrvec[i]] for i in range(len(models))},
           'reference_SSB_at_peel_years': {str(y): models[0]['SSB'][y] for y in endyrvec}}
    fleets = sorted({int(r['Fleet']) for r in indices[0]})
    out['SSmase'] = {}
    for fl in fleets:
        try:
            out['SSmase'][str(fl)] = ssmase(indices, endyrvec, fl)
        except Exception as e:  # report, do not hide
            out['SSmase'][str(fl)] = {'error': repr(e)}
    print(json.dumps(out, indent=1))


if __name__ == '__main__':
    main()
