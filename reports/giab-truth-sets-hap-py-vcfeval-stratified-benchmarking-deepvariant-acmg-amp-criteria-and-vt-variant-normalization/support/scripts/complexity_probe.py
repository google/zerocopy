#!/usr/bin/env python3
"""Exercise vcfeval's path-complexity cap (real RTG Tools binary).

A 1-contig synthetic reference carries an 80-bp poly-A run. The truth places ten
unphased heterozygous 1-bp deletions inside the run; the query places ten
heterozygous 1-bp deletions at different offsets in the same run. Any split of
the deletions between the two haplotypes that gives equal per-haplotype counts
describes the same haplotype pair, so the path search must keep many partial
haplotype assignments alive until the run ends. vcfeval is
run with the default cap and with progressively lower caps set through the
experimental --XXcom.rtg.vcf.eval.max-paths flag; when the cap is exceeded the
region is skipped ("Evaluation too complex") and its variants receive GA4GH
decision N (BI=tooHard) instead of TP/FP/FN.

Usage: python3 complexity_probe.py --rtg-dir DIR --work DIR
"""
import argparse, gzip, json, os, random, re, shutil, subprocess, time

p = argparse.ArgumentParser(); p.add_argument('--rtg-dir', required=True); p.add_argument('--work', required=True)
a = p.parse_args()
W = os.path.abspath(a.work)
shutil.rmtree(W, ignore_errors=True); os.makedirs(W)
JAVA = os.path.join(a.rtg_dir, 'jre', 'bin', 'java'); JAR = os.path.join(a.rtg_dir, 'RTG.jar')
rng = random.Random(7)
left = ''.join(rng.choice('CGT') for _ in range(200))
right = ''.join(rng.choice('CGT') for _ in range(200))
ref = left + 'A' * 80 + right                  # 80-bp homopolymer at 201..280
CH = 'chrQ'
alt_of = {'A': 'C', 'C': 'G', 'G': 'T', 'T': 'A'}
truth_pos = list(range(205, 275, 7))           # 10 het 1-bp deletions inside the A80 run
extra_pos = list(range(208, 278, 7))           # query: 10 het 1-bp deletions at other offsets (same haplotype set)
def vcf(path, poss, dels=True):
    with open(path, 'w') as fh:
        fh.write('##fileformat=VCFv4.2\n')
        fh.write(f'##contig=<ID={CH},length={len(ref)}>\n##FORMAT=<ID=GT,Number=1,Type=String,Description="Genotype">\n')
        fh.write('#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\tS\n')
        for q in sorted(poss):
            r = ref[q - 1:q + 1]
            fh.write(f'{CH}\t{q}\t.\t{r}\t{r[0]}\t50\tPASS\t.\tGT\t0/1\n')
with open(os.path.join(W, 'ref.fa'), 'w') as fh:
    fh.write(f'>{CH}\n' + '\n'.join(ref[i:i + 60] for i in range(0, len(ref), 60)) + '\n')
vcf(os.path.join(W, 'truth.vcf'), truth_pos)
vcf(os.path.join(W, 'query.vcf'), extra_pos)

def rtg(*args):
    t0 = time.time()
    r = subprocess.run(['/usr/bin/time', '-v', JAVA, '-Dtalkback=false', '-Dusage=false', '-Xmx1g', '-jar', JAR] + list(args), capture_output=True, text=True)
    rss = re.search(r'Maximum resident set size \(kbytes\): (\d+)', r.stderr)
    return r, round(time.time() - t0, 3), int(rss.group(1)) if rss else None

rtg('format', '-o', os.path.join(W, 'ref.sdf'), os.path.join(W, 'ref.fa'))
for nm in ('truth.vcf', 'query.vcf'):
    rtg('bgzip', '-f', os.path.join(W, nm)); rtg('index', '-f', 'vcf', os.path.join(W, nm + '.gz'))
res = {'truth_dels': len(truth_pos), 'query_dels': len(extra_pos), 'runs': {}}
for cap in (None, 10000, 1000, 100, 10):
    od = os.path.join(W, f'out_{cap or "default"}')
    args = ['vcfeval', '-b', os.path.join(W, 'truth.vcf.gz'), '-c', os.path.join(W, 'query.vcf.gz'), '-t', os.path.join(W, 'ref.sdf'),
            '-o', od, '--output-mode', 'ga4gh']
    if cap:
        args.append(f'--XXcom.rtg.vcf.eval.max-paths={cap}')
    r, dt, rss = rtg(*args)
    dec = {}
    outv = os.path.join(od, 'output.vcf.gz')
    if os.path.exists(outv):
        with gzip.open(outv, 'rt') as fh:
            for line in fh:
                if line.startswith('#'):
                    continue
                f = line.rstrip('\n').split('\t')
                fmt = f[8].split(':')
                for col, side in ((9, 'truth'), (10, 'query')):
                    if f[col] == '.':
                        continue
                    d = dict(zip(fmt, f[col].split(':')))
                    key = f"{side}:{d.get('BD')}" + (f":{d['BI']}" if 'BI' in d else '')
                    dec[key] = dec.get(key, 0) + 1
    warn = [l for l in (r.stdout + r.stderr).splitlines() if 'too complex' in l]
    res['runs'][str(cap or 'default(50000)')] = {'rc': r.returncode, 'wall_s': dt, 'max_rss_kb': rss, 'decisions': dec, 'warnings': warn[:3]}
json.dump(res, open(os.path.join(W, 'complexity_results.json'), 'w'), indent=1)
print(json.dumps(res, indent=1))
