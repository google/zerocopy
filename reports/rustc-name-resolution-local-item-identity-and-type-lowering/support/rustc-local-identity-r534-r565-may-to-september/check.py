#!/usr/bin/env python3
"""Offline, relocation-safe replay of retained Rust identity evidence."""
import hashlib
import json
import re
from pathlib import Path
from analyze import extract

ROOT=Path(__file__).resolve().parent.parent
R=json.loads((ROOT/'results.json').read_text())
A=json.loads((ROOT/'analysis.json').read_text())
I=json.loads((ROOT/'support'/'initial-devnull-results.json').read_text())
SHA={
    'original':'bb1204b54f7fd536e5b1c4875cf2440dc3005f14dd5c64f3fdf30fa549a36691',
    'repaired':'60b03585f4dfaa34992882ba373ed38ab6a2cf495aee5d6c3ef685252eb4563b',
    'shifted':'2216a525340fd405a744ed7967a8641c3c6cde6743fd4cdd57f94153298b725e',
}
TOOLS={
    'old':('2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc',
           'rustc 1.98.0-nightly (f8a08b688 2026-05-30)','f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1'),
    'new':('29f8ccc9aa7b0d8798eda854fa7f0e4ba3867c8c336b87d52dbb3b24b3f0878d',
           'rustc 1.101.0-nightly (5c543b0b8 2026-09-29)','5c543b0b8c73c7b72bc8284ced4fb22ead15734d'),
}
def sha(data):return hashlib.sha256(data).hexdigest()
def read(path):return (ROOT/path).read_bytes()

assert R['schema']==1 and set(R['tools'])==set(TOOLS) and R['fixtures']==SHA
assert sha(read('fixture/original-local.rs'))==SHA['original']
assert read('fixture/original-local.rs').startswith(b'\\\n')
assert read('fixture/repaired-local.rs')==read('fixture/original-local.rs')[2:]
needle=b'    let c1 = || inner::<u8>();\n'
insertion=b'    let earlier_closure = || 0u32;\n    let earlier_const = const { 0usize };\n    let _ = (earlier_closure(), earlier_const);\n'
assert read('fixture/repaired-local.rs').count(needle)==1
assert read('fixture/shifted-local.rs')==read('fixture/repaired-local.rs').replace(needle,insertion+needle)
for variant,expected in SHA.items():assert sha(read(f'fixture/{variant}-local.rs'))==expected

for role,(expected_sha,first_line,commit) in TOOLS.items():
    tool=R['tools'][role]
    assert tool['sha256']==expected_sha
    assert tool['version_verbose'].splitlines()[0]==first_line
    assert f'commit-hash: {commit}' in tool['version_verbose'].splitlines()
    assert 'host: aarch64-apple-darwin' in tool['version_verbose'].splitlines()
    assert Path(tool['executable']).name=='rustc'

expected={(role,variant,phase) for role in TOOLS for variant in SHA
          for phase in (('hir',) if variant=='original' else ('hir','metadata'))}
assert len(R['cells'])==10
assert {(c['role'],c['variant'],c['phase']) for c in R['cells']}==expected
maps={}
for c in R['cells']:
    role,variant,phase=c['role'],c['variant'],c['phase']
    stem=f'{role}--{variant}--{phase}'
    assert c['argv'][:4]==[R['tools'][role]['executable'],'--crate-name','local_identity','--edition=2024']
    assert c['argv'][-1].endswith(f'/fixture/{variant}-local.rs')
    if phase=='hir':assert c['argv'][4:-1]==['-Zunpretty=hir-tree']
    else:assert c['argv'][4:-1]==['--emit=metadata','-o',c['argv'][6]] and c['argv'][6].endswith(f'/raw/{stem}.rmeta')
    assert c['exit_code']==(1 if variant=='original' else 0)
    assert 0<c['elapsed_s']<20
    a=c['admission'];assert a['page_bytes']>0 and a['memory_bytes']>0
    assert set(a['pages'])=={'free','inactive','speculative'}
    assert abs(a['reclaimable_percent']-100*a['page_bytes']*sum(a['pages'].values())/a['memory_bytes'])<1e-10
    assert a['reclaimable_percent']>20 and a['disk_free_bytes']>1_073_741_824 and a['owned_raw_bytes']<100_000_000
    for stream in ('stdout','stderr'):
        data=read(f'raw/{stem}.{stream}')
        assert sha(data)==c[f'{stream}_sha256'] and len(data)==c[f'{stream}_bytes']
    stderr=read(f'raw/{stem}.stderr')
    if variant=='original':assert b'error: unknown start of token: \\' in stderr
    else:assert b'error:' not in stderr
    if phase=='hir':
        data=read(f'raw/{stem}.stdout')
        assert len(data)>100_000
        if variant!='original':maps[(role,variant)]=extract(data)
        assert c['artifact_sha256'] is None and c['artifact_bytes'] is None
    else:
        data=read(f'raw/{stem}.rmeta')
        assert sha(data)==c['artifact_sha256'] and len(data)==c['artifact_bytes']
        assert read(f'raw/{stem}.stdout')==b''

assert A['schema']==1
for role in TOOLS:
    for variant in ('repaired','shifted'):
        assert A['maps'][role][variant]==maps[(role,variant)]
assert len(maps[('old','repaired')])==len(maps[('new','repaired')])==23
assert len(maps[('old','shifted')])==len(maps[('new','shifted')])==25
for variant in ('repaired','shifted'):
    assert set(maps[('old',variant)])==set(maps[('new',variant)])
    assert {k:v['index'] for k,v in maps[('old',variant)].items()}=={k:v['index'] for k,v in maps[('new',variant)].items()}
assert maps[('old','repaired')]['<crate>']['crate_display']=='18ae'
assert maps[('new','repaired')]['<crate>']['crate_display']=='fcc1'
assert maps[('old','shifted')]['<crate>']['crate_display']=='18ae'
assert maps[('new','shifted')]['<crate>']['crate_display']=='fcc1'
for role in TOOLS:
    rep=maps[(role,'repaired')];shift=maps[(role,'shifted')]
    assert {k for k in rep if '{closure#' in k}=={'outer_a::{closure#0}','outer_a::{closure#1}'}
    assert {k for k in shift if '{closure#' in k}=={'outer_a::{closure#0}','outer_a::{closure#1}','outer_a::{closure#2}'}
    assert {k for k in rep if '{constant#' in k}=={'outer_a::{constant#0}','outer_a::{constant#1}','outer_a::{constant#2}'}
    assert {k for k in shift if '{constant#' in k}=={'outer_a::{constant#0}','outer_a::{constant#1}','outer_a::{constant#2}','outer_a::{constant#3}'}
    assert rep['outer_b']['index']==18 and shift['outer_b']['index']==20
    assert rep['main']['index']==20 and shift['main']['index']==22
assert A['same_display_paths_across_versions'] is True
assert A['same_defid_indices_across_versions'] is True
assert A['same_crate_display_across_versions'] is False

# Preserve the four excluded setup-attempt failures caused by placing rustc's
# temporary metadata next to /dev/null. They are not target-version results.
assert len(I['cells'])==10
for c in I['cells']:
    if c['phase']!='metadata':continue
    assert c['exit_code']==1 and c['argv'][-3:-1]==['-o','/dev/null']
    stem=f"{c['role']}--{c['variant']}--metadata-devnull"
    for stream in ('stdout','stderr'):
        data=read(f'raw/{stem}.{stream}')
        assert sha(data)==c[f'{stream}_sha256'] and len(data)==c[f'{stream}_bytes']
    assert b"couldn't create a temp dir" in read(f'raw/{stem}.stderr')

print('PASS: exact fixtures, 10 corrected cells, four setup attempts, identities, resources, and portable raw evidence')
