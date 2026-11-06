#!/usr/bin/env python3
"""Offline and relocation-safe R522 cfg evidence replay."""
import hashlib
import json
from pathlib import Path
from analyze import derive

ROOT=Path(__file__).resolve().parent.parent
R=json.loads((ROOT/'results.json').read_text())
A=json.loads((ROOT/'analysis.json').read_text())
CASES={'neither':(), 'feature':('feature="a"',),
       'custom':('custom_from_build',), 'both':('feature="a"','custom_from_build')}
TOOLS={
    'old':('2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc',
           'rustc 1.98.0-nightly (f8a08b688 2026-05-30)',
           'f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1'),
    'new':('29f8ccc9aa7b0d8798eda854fa7f0e4ba3867c8c336b87d52dbb3b24b3f0878d',
           'rustc 1.101.0-nightly (5c543b0b8 2026-09-29)',
           '5c543b0b8c73c7b72bc8284ced4fb22ead15734d'),
}
FIXTURES={
    'main.rs':'1e5ccfa163d05bce4c3c7185274d6a7ff3ba1cc9884161375e86297883dc5494',
    'selected_a.rs':'2cd82ec92567fdfda984134b3827b46a3b2a9f19be76a1bb505d8f59fd19b900',
    'selected_b.rs':'53667466532f3893a889c6f531ff3b72457a157dc33a77ba21a68b7db1f642f3',
}

def read(path):return (ROOT/path).read_bytes()
def sha(data):return hashlib.sha256(data).hexdigest()

assert R['schema']==1 and set(R['tools'])==set(TOOLS) and R['fixtures']==FIXTURES
for name,expected in FIXTURES.items():assert sha(read(f'fixture/{name}'))==expected
assert b'#[cfg_attr(feature = "a", path = "selected_a.rs")]' in read('fixture/main.rs')
assert b'#[cfg_attr(not(feature = "a"), path = "selected_b.rs")]' in read('fixture/main.rs')
for role,(expected_sha,version,commit) in TOOLS.items():
    tool=R['tools'][role]
    assert Path(tool['executable']).name=='rustc' and tool['sha256']==expected_sha
    lines=tool['version_verbose'].splitlines()
    assert lines[0]==version and f'commit-hash: {commit}' in lines
    assert 'host: aarch64-apple-darwin' in lines

expected={f'{role}/{case}/{mode}' for role in TOOLS for case in CASES for mode in ('hir','mir')}
C=R['cells'];assert len(C)==16 and set(C)==expected
for key,c in C.items():
    role,case,mode=key.split('/')
    assert (c['role'],c['case'],c['mode'])==(role,case,mode)
    argv=[R['tools'][role]['executable'],'--crate-name','cfg_probe','--crate-type','lib','--edition','2024']
    for cfg in CASES[case]:argv.extend(['--cfg',cfg])
    if mode=='hir':argv.append('-Zunpretty=hir-tree')
    else:argv.extend(['-Zmir-opt-level=0','--emit=mir','-o',str(ROOT/'raw'/role/f'{case}.mir')])
    argv.append('fixture/main.rs')
    assert c['argv'][:6]==argv[:6]
    assert c['argv'][-1]=='fixture/main.rs'
    if mode=='hir':assert c['argv']==argv
    else:
        # The original absolute artifact path is retained when the package moves.
        assert c['argv'][:-2]==argv[:-2]
        assert c['argv'][-2].endswith(f'/raw/{role}/{case}.mir')
    assert c['exit_code']==0 and c['terminated'] is None and 0<c['elapsed_s']<30
    assert 0<=c['sampled_peak_rss_kib']<1_048_576 and c['rss_polls']>=0
    gate=c['admission'];assert gate['page_bytes']>0 and gate['memory_bytes']>0
    assert set(gate['pages'])=={'free','inactive','speculative'}
    pct=100*gate['page_bytes']*sum(gate['pages'].values())/gate['memory_bytes']
    assert abs(pct-gate['reclaimable_percent'])<1e-10
    assert pct>20 and gate['disk_free_bytes']>1_073_741_824 and gate['owned_bytes']<100_000_000
    stem=f'raw/{role}/{case}--{mode}'
    for stream in ('stdout','stderr'):
        data=read(f'{stem}.{stream}')
        assert sha(data)==c[f'{stream}_sha256'] and len(data)==c[f'{stream}_bytes']
    assert c['stderr_bytes']==0
    if mode=='hir':
        assert c['stdout_bytes']>80_000 and c['artifact_sha256'] is None and c['artifact_bytes'] is None
    else:
        assert c['stdout_bytes']==0
        data=read(f'raw/{role}/{case}.mir')
        assert sha(data)==c['artifact_sha256'] and len(data)==c['artifact_bytes']

assert A==derive()
common_hir={'', 'std', '{use#0}', 'selected', 'selected::value',
            'emit_cfg_item', 'cfg_control', 'selected_value'}
common_mir={'value','cfg_control','selected_value'}
for role in TOOLS:
    for case in CASES:
        x=A['cells'][f'{role}/{case}']
        feature=case in ('feature','both');custom=case in ('custom','both')
        selected='a' if feature else 'b'
        expect_hir=common_hir | {
            'feature_a_only' if feature else 'feature_off_only',
            'custom_cfg_only' if custom else 'no_custom_cfg_only',
            f'selected::selected_{selected}_only',
            'macro_a_only' if feature else 'macro_off_only',
        }
        expect_mir=common_mir | {
            'feature_a_only' if feature else 'feature_off_only',
            'custom_cfg_only' if custom else 'no_custom_cfg_only',
            f'selected_{selected}_only',
            'macro_a_only' if feature else 'macro_off_only',
        }
        assert len(x['hir_owners'])==12 and set(x['hir_owners'])==expect_hir
        assert len(x['mir_functions'])==7 and set(x['mir_functions'])==expect_mir
        assert x['selected_value_constant']==(101 if feature else 201)
        assert (x['selected_a_source_spans']>0)==feature
        assert (x['selected_b_source_spans']>0)==(not feature)
        assert x['cfg_control_boolean']==['true' if feature else 'false']
        assert x['mir_has_both_cfg_control_arms'] is True
        assert read(f'raw/old/{case}.mir')==read(f'raw/new/{case}.mir')
        assert read(f'raw/old/{case}--hir.stdout')!=read(f'raw/new/{case}--hir.stdout')

print('PASS: reconstructed fixture, exact rustc identities, 16 gated cells, cfg HIR/MIR matrix, and portable raw evidence')
