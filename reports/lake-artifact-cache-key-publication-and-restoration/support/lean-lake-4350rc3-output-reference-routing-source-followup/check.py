#!/usr/bin/env python3
"""Offline structural and retained-byte checks for this source follow-up."""

import argparse
import csv
import hashlib
import io
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
REF = 'ba4556c30835b56d108b0a6854a760bccf8438c5'
MATRIX = 'reports/anneal-3730-3731-final-coverage-audit-2026-10-01-v90/support/version-coverage-matrix-20261001-v90.csv'
LEAN_OLD = '5045d0056413266e57c625dcd7c365b10e377c52'
LEAN_RC = '470d5ce1400764999581fd26d5d72b00d990b0f4'
LEAN_TIP = '193c3589a4fc16c4059261ab38cfa365eb24f323'
COMMON = 'src/lake/Lake/Build/Common.lean'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def read(repo, rev, path):
    return (HERE/'raw'/repo/rev/path).read_bytes()

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--reference-root', required=True, type=Path)
    args=ap.parse_args()
    report=json.loads((HERE/'REPORT.json').read_text())
    assert set(report)=={'topics','subjects','observed_at'}
    assert report['topics']==['lean','lean/lake','anneal/version-review']
    assert report['observed_at']=='2026-10-03'
    assert [x['identity']['revision'] for x in report['subjects']]==[LEAN_OLD,LEAN_RC]
    manifest=json.loads((HERE/'support/verification-manifest.json').read_text())
    assert manifest['schema']==1 and manifest['reference_commit']==REF
    assert manifest['source_result']=='narrow_source_delta'
    assert manifest['runtime_result']=='unexecuted' and manifest['matrix_rows']==['R414']
    assert manifest['matrix_effect']=='indexed_source_only_in_v91_no_runtime_or_issue_status_change'
    assert manifest['source_versions']['lean_4_34_1']==LEAN_OLD
    assert manifest['source_versions']['lean_4_35_0_rc3']==LEAN_RC
    assert manifest['source_versions']['lean_main_tip']==LEAN_TIP
    assert set(manifest['sha256'])=={'REPORT.md','REPORT.json','COHORT-NOTE.md','upstream_refs.json','mapped_source_results.json'}
    for name, expected in manifest['sha256'].items():
        assert sha((HERE/name).read_bytes())==expected, name
    refs=json.loads((HERE/'upstream_refs.json').read_text())['rows']
    observed={x['repo']:x['stdout'] for x in refs}
    assert f'{LEAN_OLD}\trefs/tags/v4.34.1' in observed['leanprover/lean4']
    assert f'{LEAN_RC}\trefs/tags/v4.35.0-rc3' in observed['leanprover/lean4']
    assert f'{LEAN_TIP}\tHEAD' in observed['leanprover/lean4']
    assert 'd13f23b723b8a846827a245b89c10fc7d3f11612\trefs/tags/v4.34.1' in observed['leanprover-community/mathlib4']
    assert 'c55e6e786f49471c72fbddbec5415808896aec1e\trefs/tags/v4.35.0-rc3' in observed['leanprover-community/mathlib4']
    rows=json.loads((HERE/'mapped_source_results.json').read_text())
    assert len(rows)==52
    assert sum(x.get('same_as_previous') is True for x in rows)==48
    assert sum(x.get('same_as_previous') is False for x in rows)==4
    assert not [x for x in rows if x.get('error') or x.get('previous_error')]
    for x in rows:
        assert x['tip'] in observed[x['repo']]
        if x.get('same_as_previous') is False:
            assert sha((HERE/x['tip_snapshot']).read_bytes())==x['tip_sha256']
    old=read('leanprover/lean4',LEAN_OLD,COMMON).decode()
    rc=read('leanprover/lean4',LEAN_RC,COMMON).decode()
    tip=read('leanprover/lean4',LEAN_TIP,COMMON).decode()
    assert sha(old.encode())=='03c6017c49303720287e76e7c31decea54f1fddec5d0d7fd358e036e3b48575c'
    assert sha(rc.encode())=='ac4245ce6f64078d0204503c0340d27572e331c2a3df452b29432b463fe2fccd'
    assert sha(tip.encode())=='653f29fa0b07ef75ee9f097f76d7183d2f508dfca1343c40cb648df7b11896e6'
    assert 'if pkg.isRoot then\n      if let some outputsRef := (← getBuildContext).outputsRef? then' in old
    assert 'if pkg.wsIdx = ctx.outputsIdx then ctx.outputsRef? else none' in rc
    assert 'if let some ref ← Internal.getOutputsRef? pkg then\n      ref.insert inputHash art.descr platformIndependent' in rc
    assert 'if pkg.wsIdx = ctx.outputsIdx then ctx.outputsRef? else none' in tip
    for x in (old,rc,tip):
        assert '(← getLakeCache).writeOutputs pkg.cacheScope inputHash art.descr' in x
    for rev in (LEAN_OLD,LEAN_RC,LEAN_TIP):
        req=read('leanprover/lean4',rev,'src/Lean/Server/FileWorker/RequestHandling.lean')
        assert b'if p.version ' in req and 'if p.version ≤ doc.meta.version'.encode() in req
    assert read('leanprover-community/mathlib4','d13f23b723b8a846827a245b89c10fc7d3f11612','lean-toolchain').strip()==b'leanprover/lean4:v4.34.1'
    assert read('leanprover-community/mathlib4','c55e6e786f49471c72fbddbec5415808896aec1e','lean-toolchain').strip()==b'leanprover/lean4:v4.35.0-rc3'
    raw=subprocess.check_output(['git','-C',args.reference_root,'show',f'{REF}:{MATRIX}'])
    matrix=list(csv.DictReader(io.StringIO(raw.decode())))
    assert len(matrix)==651
    by_id={x['inventory_id']:x for x in matrix}
    assert 'lake-artifact-cache-publication-restoration' in by_id['R414']['report_path']
    assert 'lean-lsp-cross-version-goal-completion' in by_id['R462']['report_path']
    print('OK: 651 frozen rows, 52 mapped comparisons, official refs, retained source hashes and predicates')

if __name__=='__main__': main()
