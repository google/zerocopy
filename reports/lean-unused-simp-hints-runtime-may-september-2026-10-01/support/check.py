#!/usr/bin/env python3
"""Offline, relocatable replay of R488 linter warning and hint differences."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
TOOL={'old':('v4.30.0-rc2','3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc','b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997'),
      'new':('v4.34.1','5045d0056413266e57c625dcd7c365b10e377c52','1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554')}
FIX={'ordinary':'3960443aaafbf8017327e17eb18f62f7a5ed228f0b8ed28865ac72862549cc1d',
     'options':'5d59e763970de603f392a98bce51550ac20e6c40c1ba31fd35f20b21c8f0c01e',
     'no-progress':'215dcb16cd07ca6c02c9ff963e08ae1e4954a1bebd33b9d7951961fbdd5313a3',
     'no-progress-relaxed':'1c28fb245e65fc6375454502088cbe49992e4ba3f03d4d83af8a8a8745077b66'}
WARNING_LINES={'ordinary':[5,10],'options':[10],'no-progress':[],'no-progress-relaxed':[6]}
SOURCE_DIFF='4332852cd21d2908dbef35d4c4470eacb330832813b2283bc68ae3eff86326a2'
def sha(b):return hashlib.sha256(b).hexdigest()
def messages(raw):return [json.loads(line) for line in raw.decode().splitlines()]
def strip_hint(data):
    lead,tail=data.split('Hint: Omit it from the simp argument list.\n  ',1)
    hint,note=tail.split('\n\nNote: ',1)
    return lead,note,hint
def main():
    r=json.loads((ROOT/'results.json').read_text())
    assert r['schema']==1 and r['fixtures']==FIX
    assert set(r['tools'])==set(TOOL)
    assert set(r['cells'])=={f'{role}/{case}' for role in TOOL for case in FIX}
    for case,digest in FIX.items():assert sha((ROOT/'fixture'/f'{case}.lean').read_bytes())==digest
    diff=(ROOT/'support/source-diff.patch').read_bytes()
    assert sha(diff)==SOURCE_DIFF and b'diffGranularity := .none' in diff
    actual=set();out={}
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
            assert c['exit_code']==(1 if case.startswith('no-progress') else 0)
            for stream in ('stdout','stderr'):
                rel=f'raw/{role}/{case}.{stream}';b=(ROOT/rel).read_bytes()
                assert len(b)==c[f'{stream}_bytes'] and sha(b)==c[f'{stream}_sha256']
                out[(role,case,stream)]=b;actual.add(rel)
            assert out[(role,case,'stderr')]==b''
            m=messages(out[(role,case,'stdout')])
            warns=[x for x in m if x['kind']=='linter.unusedSimpArgs']
            assert [x['pos']['line'] for x in warns]==WARNING_LINES[case]
            assert all(x['severity']=='warning' and x['fileName']==f'fixture/{case}.lean' for x in warns)
            if case=='no-progress':
                assert len(m)==1 and m[0]['severity']=='error' and m[0]['data']=='`simp` made no progress'
            if case=='no-progress-relaxed':
                assert len(m)==2 and m[0]['severity']=='error' and m[0]['data'].startswith('unsolved goals')
    assert actual=={str(p.relative_to(ROOT)) for p in (ROOT/'raw').rglob('*') if p.is_file()}
    assert out[('old','no-progress','stdout')]==out[('new','no-progress','stdout')]
    for case in FIX:
        a=messages(out[('old',case,'stdout')]);b=messages(out[('new',case,'stdout')])
        assert len(a)==len(b)
        for x,y in zip(a,b):
            if x['kind']!='linter.unusedSimpArgs':assert x==y;continue
            a_data=x.pop('data');b_data=y.pop('data')
            assert x==y
            a_lead,a_note,a_hint=strip_hint(a_data);b_lead,b_note,b_hint=strip_hint(b_data)
            assert a_lead==b_lead and a_note==b_note
            assert '̵' in a_hint and '[apply] simp' in b_hint and '̵' not in b_hint
            if case=='no-progress-relaxed':assert b_hint=='[apply] simp -failIfUnchanged'
            else:assert b_hint=='[apply] simp'
    analysis=json.loads((ROOT/'analysis.json').read_text())
    assert analysis['cell_count']==8 and analysis['warning_positions_per_version']==WARNING_LINES
    assert analysis['warning_shape_equal_except_hint_rendering'] and analysis['no_progress_failure_transcript_equal']
    print('PASS: eight guarded cells, exact identities/hashes, warning positions, hint delta and source diff, relocation')
if __name__=='__main__':main()
