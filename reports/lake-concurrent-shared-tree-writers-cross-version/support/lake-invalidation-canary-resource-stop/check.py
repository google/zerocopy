#!/usr/bin/env python3
"""Offline, relocatable verification of the guarded R428 Lake canary stop."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
TOOLS={
 'old':('v4.30.0-rc2','3dc1a08','9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb'),
 'new':('v4.34.1','5045d00','c8c24f1398162ab4004e2a869952d8469f54293651151feaad4526f2b8474c6e'),
}
FIXTURE={
 'consumer/Core.lean':'0b27ffb285fb439814312032273008727f90544f40cd69b5bc34a2f8c7b53e46',
 'consumer/Main.lean':'e3894c80f4b2a5bab80f01fe77b9b659445818d88fb611a0b4aa85c860f41c57',
 'consumer/lakefile.lean':'2e1a83822f3363d0df76133db306b0ce739f3050cbbf058836ff44c74a32871b',
 'dep/Dep.lean':'15bbf60d162408dade43c6e618dd0d09b28c8fdeb7528c80e40329908f12b7a2',
 'dep/lakefile.lean':'2f25e76df523b12c1cbb64e2fd9701e6eca8d501a630e70e5a9f3c82fbcef3ad',
}
def sha(data):return hashlib.sha256(data).hexdigest()
def validate_tree(base,recorded):
    actual={str(p.relative_to(base)):p for p in base.rglob('*') if p.is_file()}
    assert set(actual)==set(recorded),(base,set(actual)^set(recorded))
    for rel,p in actual.items():
        m=recorded[rel];b=p.read_bytes()
        assert len(b)==m['size'] and sha(b)==m['sha256'],(base,rel)
        assert isinstance(m['mtime_ns'],int) and m['mtime_ns']>0
def validate_streams(base,record):
    for stream in ('stdout','stderr'):
        p=base/f'build.{stream}'
        b=p.read_bytes()
        assert len(b)==record[f'{stream}_bytes'] and sha(b)==record[f'{stream}_sha256']
def validate_gate(r):
    gate=r['admission'];pages=gate['pages']
    assert set(pages)=={'free','inactive','speculative'}
    assert abs(gate['reclaimable_percent']-100*gate['page_bytes']*sum(pages.values())/gate['memory_bytes'])<1e-9
    assert gate['reclaimable_percent']>20 and gate['disk_free_bytes']>10*1024**3 and gate['owned_bytes']<100_000_000
    assert 0<r['elapsed_s']<30 and r['rss_polls']>0
def main():
    for rel,digest in FIXTURE.items():assert sha((ROOT/'fixture'/rel).read_bytes())==digest
    for role,(version,commit,digest) in TOOLS.items():
        r=json.loads((ROOT/'raw'/role/'record.json').read_text())
        assert r['role']==role and r['lake_sha256']==digest
        assert f'{commit} (Lean version {version[1:]})' in r['lake_version']
        argv=r['argv'];assert len(argv)==6 and argv[0].endswith(f'/leanprover--lean4---{version}/bin/lake')
        assert argv[1:]==['--no-cache','-v','build','Core','Main']
        assert r['cwd'].endswith(f'/runs/{role}/consumer')
        assert r['env']['LAKE_ARTIFACT_CACHE']=='false'
        assert r['env']['LAKE_CACHE_DIR'].endswith(f'/raw/{role}/lake-cache')
        assert r['env']['PATH_prefix'].endswith(f'/leanprover--lean4---{version}/bin')
        validate_gate(r)
        validate_streams(ROOT/'raw'/role,r)
        assert set(r['before'])==set(FIXTURE)
        for rel,d in FIXTURE.items():assert r['before'][rel]['sha256']==d
        validate_tree(ROOT/'runs'/role,r['after'])
        if role=='old':
            assert r['exit_code']==0 and r['terminated'] is None
            assert r['sampled_peak_group_rss_kib']<1_048_576
            assert len(r['after'])==34 and 'Build completed successfully (7 jobs).' in (ROOT/'raw'/role/'build.stdout').read_text()
            for module in ('Dep','Core','Main'):
                prefix='dep' if module=='Dep' else 'consumer'
                for suffix in ('olean','ilean','trace'):
                    assert f'{prefix}/.lake/build/lib/lean/{module}.{suffix}' in r['after']
        else:
            assert r['exit_code']==-9 and r['terminated']=='process-group RSS >1 GiB'
            assert r['sampled_peak_group_rss_kib']>1_048_576
            assert len(r['after'])==11
            assert not any(p.endswith(('.olean','.ilean','.trace')) and '/build/lib/lean/' in p for p in r['after'])
    pre=ROOT/'preliminary/old-unregistered-core'
    p=json.loads((pre/'raw/record.json').read_text())
    assert p['role']=='old' and p['exit_code']==1 and p['terminated'] is None
    validate_gate(p);validate_streams(pre/'raw',p)
    validate_tree(pre/'runs',p['after'])
    assert "unknown module prefix 'Core'" in (pre/'raw/build.stdout').read_text()
    assert 'lean_lib Core' not in (pre/'runs/consumer/lakefile.lean').read_text()
    assert 'lean_lib Core' in (ROOT/'fixture/consumer/lakefile.lean').read_text()
    a=json.loads((ROOT/'analysis.json').read_text())
    assert a['corrected_old_build_succeeded'] and a['corrected_new_build_killed_at_rss_cap']
    assert a['invalidation_matrix_cases_executed']==0
    print('PASS: exact canary identities, gates, streams, artifacts, preliminary exclusion, and no invalidation matrix')
if __name__=='__main__':main()
