#!/usr/bin/env python3
"""Offline, relocatable replay of the bounded R470 Lean omega matrix."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
TOOL={'old':('v4.30.0-rc2','3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc','b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997'),
      'new':('v4.34.1','5045d0056413266e57c625dcd7c365b10e377c52','1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554')}
FIX={'linear':'20b47047b9712876485d8cbbed533695adcb8efb7cd1f2c579b66dda1058b15e',
     'nonlinear':'257341ff35951efd818a0fc09e8f3e56356bdffcd0cb4798994d38cb9349d8f4',
     'no-constraints':'c8f1c996c894646b1216d386616f22712dff9dcffb43bc57ac942b34b2783f0a'}
def sha(b):return hashlib.sha256(b).hexdigest()
def main():
    r=json.loads((ROOT/'results.json').read_text())
    assert r['schema']==1 and r['fixtures']==FIX
    assert set(r['tools'])==set(TOOL)
    assert set(r['cells'])=={f'{role}/{case}' for role in TOOL for case in FIX}
    for case,digest in FIX.items():assert sha((ROOT/'fixture'/f'{case}.lean').read_bytes())==digest
    actual=set();outputs={}
    for role,(version,commit,digest) in TOOL.items():
        t=r['tools'][role]
        assert t['sha256']==digest and t['executable'].endswith(f'/leanprover--lean4---{version}/bin/lean')
        assert f'version {version[1:]}, ' in t['version'] and f'commit {commit}, ' in t['version']
        for case in FIX:
            c=r['cells'][f'{role}/{case}']
            assert c['argv']==[t['executable'],'--json',f'fixture/{case}.lean']
            g=c['admission'];pages=g['pages']
            assert set(pages)=={'free','inactive','speculative'}
            assert abs(g['reclaimable_percent']-100*g['page_bytes']*sum(pages.values())/g['memory_bytes'])<1e-9
            assert g['reclaimable_percent']>20 and g['disk_free_bytes']>1_073_741_824 and g['owned_bytes']<100_000_000
            assert c['terminated'] is None and 0<c['elapsed_s']<30 and 0<=c['sampled_peak_rss_kib']<1_048_576
            assert c['exit_code']==(0 if case=='linear' else 1)
            for stream in ('stdout','stderr'):
                rel=f'raw/{role}/{case}.{stream}'
                b=(ROOT/rel).read_bytes()
                assert len(b)==c[f'{stream}_bytes'] and sha(b)==c[f'{stream}_sha256']
                outputs[(role,case,stream)]=b;actual.add(rel)
            assert outputs[(role,case,'stderr')]==b''
            if case=='linear':assert outputs[(role,case,'stdout')]==b''
            else:
                x=json.loads(outputs[(role,case,'stdout')]);assert x['severity']=='error'
                assert x['fileName']==f'fixture/{case}.lean'
                assert 'omega could not prove the goal:' in x['data']
                if case=='nonlinear':assert '↑b * ↑a' in x['data'] and '↑a * ↑b' in x['data']
                if case=='no-constraints':assert 'No usable constraints found' in x['data']
    assert actual=={str(p.relative_to(ROOT)) for p in (ROOT/'raw').rglob('*') if p.is_file()}
    for case in FIX:
        for stream in ('stdout','stderr'):assert outputs[('old',case,stream)]==outputs[('new',case,stream)]
    a=json.loads((ROOT/'analysis.json').read_text())
    assert a['all_three_stdout_pairs_identical'] and a['all_six_exit_codes_expected']
    print('PASS: six guarded cells, exact identities, fixture/raw hashes, omega outcomes, relocation')
if __name__=='__main__':main()
