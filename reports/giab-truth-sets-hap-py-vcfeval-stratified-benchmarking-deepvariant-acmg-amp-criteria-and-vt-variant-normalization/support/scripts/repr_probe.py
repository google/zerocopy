#!/usr/bin/env python3
"""Representation-sensitivity probe for small-variant benchmarking.

Builds a synthetic 1-contig reference and truth/query VCFs whose records encode
the SAME haplotypes in different (equally valid) VCF representations, then
compares them three ways:

  1. naive record matcher (a toy written here: exact CHROM/POS/REF/ALT/GT match);
  2. RTG Tools vcfeval (real upstream binary), several modes;
  3. after normalising the query with vt normalize (real upstream binary).

Usage:
  python3 repr_probe.py --rtg-dir DIR --vt BIN --work DIR

DIR/RTG.jar and DIR/jre/bin/java must exist (the rtg-tools linux-x64 release
zip layout). All outputs go under --work.
"""
import argparse, gzip, json, os, random, re, shutil, subprocess, sys, time

p = argparse.ArgumentParser()
p.add_argument('--rtg-dir', required=True)
p.add_argument('--vt', required=True)
p.add_argument('--work', required=True)
a = p.parse_args()

W = os.path.abspath(a.work)
if os.path.exists(W):
    shutil.rmtree(W)
os.makedirs(W)
JAVA = os.path.join(a.rtg_dir, 'jre', 'bin', 'java')
JAR = os.path.join(a.rtg_dir, 'RTG.jar')
CHROM = 'chrP'
rng = random.Random(20261120)

def spacer(n):
    return ''.join(rng.choice('ACGT') for _ in range(n))

# ---------------------------------------------------------------- reference
segs = []  # (label, seq)
def add(label, seq):
    segs.append((label, seq))

add('lead', spacer(60))
add('A_homopolymer', 'TG' + 'AAAAAA' + 'CT')        # 1-bp deletion in A6
add('sp1', spacer(80))
add('B_dinuc', 'GT' + 'CACACACA' + 'GG')            # CA insertion in (CA)4
add('sp2', spacer(80))
add('C_mnp', 'TTGCAATT')                            # 2-bp MNP GC->AT at offsets 2,3
add('sp3', spacer(80))
add('D_complex', 'CGTACGAT')                         # delins
add('sp4', spacer(80))
add('E_gt', 'TTTGTTT')                               # SNP, zygosity differs
add('sp5', spacer(80))
add('F_hapnorm', 'GGC' + 'AAAA' + 'TGG')             # SNP + del in A4 on same haplotype
add('sp6', spacer(80))
add('G_fp', 'CCCTCCC')                               # query-only SNP
add('sp7', spacer(80))
add('H_fn', 'GGGAGGG')                               # truth-only SNP
add('sp8', spacer(80))
add('I_tp', 'AACAA')                                 # identical SNP
add('sp9', spacer(80))
add('J_outside', 'TTTCTTT')                          # query-only SNP outside eval regions
add('tail', spacer(60))

ref = ''
starts = {}
for label, s in segs:
    starts[label] = len(ref) + 1  # 1-based start of segment
    ref += s

def base(pos):
    return ref[pos - 1]

def seg(label):
    return starts[label]

recs_truth, recs_query = [], []
def T(pos, r, alt, gt, case):
    assert ref[pos - 1:pos - 1 + len(r)] == r, (case, pos, r, ref[pos - 1:pos - 1 + len(r)])
    recs_truth.append((pos, r, alt, gt, case))
def Q(pos, r, alt, gt, case):
    assert ref[pos - 1:pos - 1 + len(r)] == r, (case, pos, r, ref[pos - 1:pos - 1 + len(r)])
    recs_query.append((pos, r, alt, gt, case))

# A: TG AAAAAA CT ; delete one A. truth left-aligned, query right-most.
g = seg('A_homopolymer') + 1             # the G
T(g, 'GA', 'G', '0/1', 'A')
Q(g + 5, 'AA', 'A', '0/1', 'A')
# B: GT CACACACA GG ; insert CA. truth anchored on T (left), query anchored on last A (right).
t = seg('B_dinuc') + 1                   # the T
T(t, 'T', 'TCA', '1/1', 'B')
Q(t + 8, 'A', 'ACA', '1/1', 'B')
# C: TTGCAATT ; GC->AT. truth one MNP record, query two SNPs.
c = seg('C_mnp') + 2                     # the G
T(c, 'GC', 'AT', '1/1', 'C')
Q(c, 'G', 'A', '1/1', 'C')
Q(c + 1, 'C', 'T', '1/1', 'C')
# D: CGTACGAT ; haplotype = C + T + GAT? truth: one delins REF CGTAC -> CTC? Use:
#   ref  C G T A C G A T ; alt haplotype: C [del G T] [A->T] C G A T  => C T C G A T
d = seg('D_complex')
T(d, 'CGTA', 'CT', '1/1', 'D')                       # one complex record
Q(d, 'CGT', 'C', '1/1', 'D')                         # 2-bp deletion
Q(d + 3, 'A', 'T', '1/1', 'D')                       # adjacent SNP
# E: genotype mismatch, same allele
e = seg('E_gt') + 3
T(e, 'G', 'C', '0/1', 'E')
Q(e, 'G', 'C', '1/1', 'E')
# F: GGC AAAA TGG ; haplotype: SNP first A->G and delete one of remaining A's.
f = seg('F_hapnorm') + 3                 # first A
T(f, 'A', 'G', '1/1', 'F')
T(f + 1, 'AA', 'A', '1/1', 'F')                       # deletes the A at f+2
Q(f, 'A', 'G', '1/1', 'F')
Q(f + 2, 'AA', 'A', '1/1', 'F')                       # deletes the A at f+3 (equivalent)
# G: FP
gg = seg('G_fp') + 3
Q(gg, 'T', 'A', '0/1', 'G')
# H: FN
h = seg('H_fn') + 3
T(h, 'A', 'T', '0/1', 'H')
# I: identical
i = seg('I_tp') + 2
T(i, 'C', 'G', '0/1', 'I')
Q(i, 'C', 'G', '0/1', 'I')
# J: query-only SNP outside evaluation regions
j = seg('J_outside') + 3
Q(j, 'C', 'G', '0/1', 'J')

# ---------------------------------------------------------------- write inputs
def write_fa(path):
    with open(path, 'w') as fh:
        fh.write(f'>{CHROM}\n')
        for k in range(0, len(ref), 60):
            fh.write(ref[k:k + 60] + '\n')

def write_vcf(path, recs):
    with open(path, 'w') as fh:
        fh.write('##fileformat=VCFv4.2\n')
        fh.write(f'##contig=<ID={CHROM},length={len(ref)}>\n')
        fh.write('##INFO=<ID=CASE,Number=1,Type=String,Description="Probe case label">\n')
        fh.write('##FORMAT=<ID=GT,Number=1,Type=String,Description="Genotype">\n')
        fh.write('#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO\tFORMAT\tS\n')
        for pos, r, alt, gt, case in sorted(recs):
            fh.write(f'{CHROM}\t{pos}\t.\t{r}\t{alt}\t50\tPASS\tCASE={case}\tGT\t{gt}\n')

write_fa(os.path.join(W, 'ref.fa'))
with open(os.path.join(W, 'ref.fa.fai'), 'w') as fh:
    # name, length, offset, linebases, linewidth
    fh.write(f'{CHROM}\t{len(ref)}\t{len(CHROM) + 2}\t60\t61\n')
write_vcf(os.path.join(W, 'truth.vcf'), recs_truth)
write_vcf(os.path.join(W, 'query.vcf'), recs_query)
# evaluation regions: whole contig except the J segment
js = seg('J_outside') - 1
je = js + len(dict(segs)['J_outside'])
with open(os.path.join(W, 'conf.bed'), 'w') as fh:
    fh.write(f'{CHROM}\t0\t{js}\n{CHROM}\t{je}\t{len(ref)}\n')

# ---------------------------------------------------------------- helpers
def timed(cmd, log):
    t0 = time.time()
    r = subprocess.run(['/usr/bin/time', '-v'] + cmd, capture_output=True, text=True)
    dt = time.time() - t0
    rss = re.search(r'Maximum resident set size \(kbytes\): (\d+)', r.stderr)
    with open(os.path.join(W, log), 'w') as fh:
        fh.write('$ ' + ' '.join(cmd) + '\n' + r.stdout + '\n--- stderr ---\n' + r.stderr)
    return {'cmd': ' '.join(os.path.basename(x) if x.startswith('/') and os.path.exists(x) and x in (JAVA, JAR, a.vt) else x for x in cmd),
            'rc': r.returncode, 'wall_s': round(dt, 3), 'max_rss_kb': int(rss.group(1)) if rss else None}

def rtg(*args, log):
    return timed([JAVA, '-Dtalkback=false', '-Dusage=false', '-Xmx1g', '-jar', JAR] + list(args), log)

def read_vcf(path):
    op = gzip.open if path.endswith('.gz') else open
    out = []
    with op(path, 'rt') as fh:
        for line in fh:
            if line.startswith('#'):
                continue
            f = line.rstrip('\n').split('\t')
            out.append(f)
    return out

def naive(truth_path, query_path):
    """Toy comparator: exact (POS, REF, ALT, GT) match, records outside conf.bed ignored."""
    def key(f):
        return (int(f[1]), f[3], f[4], f[9].split(':')[0])
    def inside(pos):
        return pos <= js or pos > je
    tr = {key(f) for f in read_vcf(truth_path) if inside(int(f[1]))}
    qr = {key(f) for f in read_vcf(query_path) if inside(int(f[1]))}
    return {'TP': len(tr & qr), 'FP': len(qr - tr), 'FN': len(tr - qr), 'truth_records': len(tr), 'query_records': len(qr)}

results = {'reference_length': len(ref), 'cases': {}, 'runs': {}}
for pos, r, alt, gt, case in recs_truth:
    results['cases'].setdefault(case, {'truth': [], 'query': []})['truth'].append(f'{pos} {r}>{alt} {gt}')
for pos, r, alt, gt, case in recs_query:
    results['cases'].setdefault(case, {'truth': [], 'query': []})['query'].append(f'{pos} {r}>{alt} {gt}')

# ---------------------------------------------------------------- vt normalize
results['runs']['vt_normalize_query'] = timed([a.vt, 'normalize', '-r', os.path.join(W, 'ref.fa'), '-o', os.path.join(W, 'query.vtnorm.vcf'), os.path.join(W, 'query.vcf')], 'vt_normalize_query.log')
results['runs']['vt_normalize_truth'] = timed([a.vt, 'normalize', '-r', os.path.join(W, 'ref.fa'), '-o', os.path.join(W, 'truth.vtnorm.vcf'), os.path.join(W, 'truth.vcf')], 'vt_normalize_truth.log')
# vt's ordered writer may emit an unsorted-but-valid file; sort for downstream tools
for nm in ('query.vtnorm.vcf', 'truth.vtnorm.vcf'):
    path = os.path.join(W, nm)
    with open(path) as fh:
        lines = fh.readlines()
    hdr = [l for l in lines if l.startswith('#')]
    body = sorted((l for l in lines if not l.startswith('#')), key=lambda l: (l.split('\t')[0], int(l.split('\t')[1])))
    with open(path, 'w') as fh:
        fh.writelines(hdr + body)

results['vt_query_records'] = ['\t'.join(f[1:5] + [f[7], f[9]]) for f in read_vcf(os.path.join(W, 'query.vtnorm.vcf'))]
results['vt_truth_records'] = ['\t'.join(f[1:5] + [f[7], f[9]]) for f in read_vcf(os.path.join(W, 'truth.vtnorm.vcf'))]

# ---------------------------------------------------------------- naive comparisons (toy)
results['naive_raw'] = naive(os.path.join(W, 'truth.vcf'), os.path.join(W, 'query.vcf'))
results['naive_after_vt_both'] = naive(os.path.join(W, 'truth.vtnorm.vcf'), os.path.join(W, 'query.vtnorm.vcf'))

# ---------------------------------------------------------------- RTG
results['runs']['rtg_format'] = rtg('format', '-o', os.path.join(W, 'ref.sdf'), os.path.join(W, 'ref.fa'), log='rtg_format.log')
for nm in ('truth.vcf', 'query.vcf', 'query.vtnorm.vcf', 'truth.vtnorm.vcf'):
    results['runs'][f'rtg_bgzip_{nm}'] = rtg('bgzip', '-f', os.path.join(W, nm), log=f'rtg_bgzip_{nm}.log')
    results['runs'][f'rtg_index_{nm}'] = rtg('index', '-f', 'vcf', os.path.join(W, nm + '.gz'), log=f'rtg_index_{nm}.log')

def summary(outdir):
    path = os.path.join(W, outdir, 'summary.txt')
    if not os.path.exists(path):
        return None
    return open(path).read()

modes = {
    'vcfeval_default': ['--squash-ploidy'] if False else [],
    'vcfeval_squash_ploidy': ['--squash-ploidy'],
    'vcfeval_ga4gh': ['--output-mode', 'ga4gh'],
}
for name, extra in modes.items():
    results['runs'][name] = rtg('vcfeval', '-b', os.path.join(W, 'truth.vcf.gz'), '-c', os.path.join(W, 'query.vcf.gz'),
                               '-t', os.path.join(W, 'ref.sdf'), '-e', os.path.join(W, 'conf.bed'), '-o', os.path.join(W, name), *extra,
                               log=name + '.log')
    results['runs'][name]['summary'] = summary(name)
name = 'vcfeval_query_vtnorm'
results['runs'][name] = rtg('vcfeval', '-b', os.path.join(W, 'truth.vcf.gz'), '-c', os.path.join(W, 'query.vtnorm.vcf.gz'),
                           '-t', os.path.join(W, 'ref.sdf'), '-e', os.path.join(W, 'conf.bed'), '-o', os.path.join(W, name), log=name + '.log')
results['runs'][name]['summary'] = summary(name)
name = 'vcfeval_ga4gh_query_vtnorm'
results['runs'][name] = rtg('vcfeval', '-b', os.path.join(W, 'truth.vcf.gz'), '-c', os.path.join(W, 'query.vtnorm.vcf.gz'),
                           '-t', os.path.join(W, 'ref.sdf'), '-e', os.path.join(W, 'conf.bed'), '-o', os.path.join(W, name), '--output-mode', 'ga4gh', log=name + '.log')
results['runs'][name]['summary'] = summary(name)

# per-record GA4GH decisions
for name in ('vcfeval_ga4gh', 'vcfeval_ga4gh_query_vtnorm'):
    out = os.path.join(W, name, 'output.vcf.gz')
    rows = []
    if os.path.exists(out):
        for f in read_vcf(out):
            rows.append('\t'.join([f[1], f[3], f[4], f[7], f[8], f[9], f[10]]))
    results[name + '_records'] = rows

# SDF footprint
sz = 0
for root, _, files in os.walk(os.path.join(W, 'ref.sdf')):
    for fn in files:
        sz += os.path.getsize(os.path.join(root, fn))
results['sdf_bytes'] = sz
results['fasta_bytes'] = os.path.getsize(os.path.join(W, 'ref.fa'))

with open(os.path.join(W, 'results.json'), 'w') as fh:
    json.dump(results, fh, indent=1)
print(json.dumps({k: v for k, v in results.items() if k not in ('runs',)}, indent=1))
for k, v in results['runs'].items():
    s = v.get('summary')
    print(f"== {k}: rc={v['rc']} wall={v['wall_s']}s maxrss={v['max_rss_kb']}kB")
    if s:
        print(s)
