#!/usr/bin/env python3
"""Sweep: vcfeval max path complexity vs number of equivalent het deletions in a homopolymer.

For k in KS, truth carries k unphased het 1-bp deletions in a poly-A run and the
query carries k het 1-bp deletions at different offsets in the same run (an
equivalent haplotype set). Reports vcfeval's logged maximum path complexity,
wall time, max RSS and GA4GH decisions at the default path cap.
Usage: python3 complexity_sweep.py --rtg-dir DIR --work DIR
"""
import argparse, gzip, json, os, random, re, shutil, subprocess, time
p = argparse.ArgumentParser(); p.add_argument('--rtg-dir', required=True); p.add_argument('--work', required=True)
a = p.parse_args()
W = os.path.abspath(a.work); shutil.rmtree(W, ignore_errors=True); os.makedirs(W)
JAVA = os.path.join(a.rtg_dir, 'jre', 'bin', 'java'); JAR = os.path.join(a.rtg_dir, 'RTG.jar')
def rtg(*args):
    t0 = time.time()
    r = subprocess.run(['/usr/bin/time', '-v', JAVA, '-Dtalkback=false', '-Dusage=false', '-Xmx4g', '-jar', JAR] + list(args), capture_output=True, text=True)
    rss = re.search(r'Maximum resident set size \(kbytes\): (\d+)', r.stderr)
    return r, round(time.time() - t0, 3), int(rss.group(1)) if rss else None
rng = random.Random(11)
RUN = 200
ref = ''.join(rng.choice('CGT') for _ in range(200)) + 'A' * RUN + ''.join(rng.choice('CGT') for _ in range(200))
CH = 'chrS'
with open(os.path.join(W, 'ref.fa'), 'w') as fh:
    fh.write(f'>{CH}\n' + '\n'.join(ref[i:i + 60] for i in range(0, len(ref), 60)) + '\n')
rtg('format', '-o', os.path.join(W, 'ref.sdf'), os.path.join(W, 'ref.fa'))
def vcf(path, poss):
    with open(path, 'w') as fh:
        fh.write(f'##fileformat=VCFv4.2\n##contig=<ID={CH},length={len(ref)}>\n##FORMAT=<ID=GT,Number=1,Type=String,Description="Genotype">\n')
        fh.write('#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\tS\n')
        for q in sorted(poss):
            fh.write(f'{CH}\t{q}\t.\tAA\tA\t50\tPASS\t.\tGT\t0/1\n')
out = {}
for k in (4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 28, 32):
    step = RUN // (k + 1)
    tpos = [201 + step * (i + 1) - 3 for i in range(k)]
    qpos = [x + step // 2 for x in tpos]
    d = os.path.join(W, f'k{k}'); os.makedirs(d)
    vcf(os.path.join(d, 'truth.vcf'), tpos); vcf(os.path.join(d, 'query.vcf'), qpos)
    for nm in ('truth.vcf', 'query.vcf'):
        rtg('bgzip', '-f', os.path.join(d, nm)); rtg('index', '-f', 'vcf', os.path.join(d, nm + '.gz'))
    r, dt, rss = rtg('vcfeval', '-b', os.path.join(d, 'truth.vcf.gz'), '-c', os.path.join(d, 'query.vcf.gz'), '-t', os.path.join(W, 'ref.sdf'),
                     '-o', os.path.join(d, 'out'), '--output-mode', 'ga4gh')
    log = open(os.path.join(d, 'out', 'vcfeval.log')).read() if os.path.exists(os.path.join(d, 'out', 'vcfeval.log')) else ''
    mpc = [int(x) for x in re.findall(r'had maximum path complexity of (\d+)', log)]
    dec = {}
    ov = os.path.join(d, 'out', 'output.vcf.gz')
    if os.path.exists(ov):
        for line in gzip.open(ov, 'rt'):
            if line.startswith('#'): continue
            f = line.rstrip('\n').split('\t'); fmt = f[8].split(':')
            for col, side in ((9, 'truth'), (10, 'query')):
                if f[col] == '.': continue
                dd = dict(zip(fmt, f[col].split(':')))
                key = f"{side}:{dd.get('BD')}" + (f":{dd['BI']}" if 'BI' in dd else '')
                dec[key] = dec.get(key, 0) + 1
    warn = [l for l in (r.stdout + r.stderr + log).splitlines() if 'too complex' in l]
    out[k] = {'rc': r.returncode, 'wall_s': dt, 'max_rss_kb': rss, 'max_path_complexity': max(mpc) if mpc else None, 'decisions': dec, 'too_complex_warnings': len(warn)}
    print(k, out[k], flush=True)
json.dump(out, open(os.path.join(W, 'sweep_results.json'), 'w'), indent=1)
