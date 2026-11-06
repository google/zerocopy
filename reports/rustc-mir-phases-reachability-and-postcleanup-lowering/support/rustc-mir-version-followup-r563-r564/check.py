#!/usr/bin/env python3
"""Offline, relocatable verification of the retained R563/R564 MIR matrix."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SHA = {
    'old': ('2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc',
            'f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1', '1.98.0-nightly'),
    'new': ('29f8ccc9aa7b0d8798eda854fa7f0e4ba3867c8c336b87d52dbb3b24b3f0878d',
            '5c543b0b8c73c7b72bc8284ced4fb22ead15734d', '1.101.0-nightly'),
}
FIXTURES = {
    'r563': '503640d29885c906d2a51bfd5ae6c8134638441086969e825d5497d79a5a307b',
    'r564': 'fc3992f976b1cfed1439bcaffd600c64d0d4017bb01c1ce2d2cf8f063bd0ea4d',
}
MODES = {'r563': ('opt0', 'opt2', 'simplify-dump'),
         'r564': ('opt0', 'opt2', 'intrinsic-dump')}

def digest(data): return hashlib.sha256(data).hexdigest()
def retained(relative, expected_sha, expected_bytes):
    path = ROOT / relative
    assert path.is_file(), relative
    data = path.read_bytes()
    assert len(data) == expected_bytes and digest(data) == expected_sha, relative
    return data

def body(mir, function):
    match = re.search(r'(?m)^fn '+re.escape(function)+r'\([^\n]*\)(?: -> [^\n]+)? \{', mir)
    assert match, function
    next_fn = re.search(r'(?m)^fn ', mir[match.end():])
    return mir[match.start():match.end()+next_fn.start()] if next_fn else mir[match.start():]

def main():
    data = json.loads((ROOT/'results.json').read_text())
    assert data['schema'] == 1 and data['fixtures'] == FIXTURES
    assert set(data['tools']) == set(SHA)
    assert set(data['cells']) == {f'{role}/{suite}/{mode}' for role in SHA for suite in MODES for mode in MODES[suite]}
    assert set(p.name for p in (ROOT/'fixture').iterdir()) == {'r563.rs', 'r564.rs'}
    for suite, sha in FIXTURES.items():
        assert digest((ROOT/'fixture'/f'{suite}.rs').read_bytes()) == sha
    for role, (exe_sha, commit, release) in SHA.items():
        tool=data['tools'][role]
        assert tool['sha256'] == exe_sha
        assert tool['executable'].endswith(f'/nightly-{("2026-05-31" if role=="old" else "2026-09-30")}-aarch64-apple-darwin/bin/rustc')
        vv=tool['version_verbose']
        assert f'commit-hash: {commit}\n' in vv and f'release: {release}\n' in vv
        assert 'host: aarch64-apple-darwin\n' in vv
    actual=set()
    mirs={}
    for key, cell in data['cells'].items():
        role,suite,mode=key.split('/')
        assert (cell['role'],cell['suite'],cell['mode'])==(role,suite,mode)
        argv=cell['argv']; assert argv[0]==data['tools'][role]['executable']
        assert argv[1:7]==['--crate-name',suite,'--crate-type','lib','--edition','2024']
        assert argv[7:10]==['-Adead_code','-Aunreachable_code','-Zmir-opt-level='+('2' if mode=='opt2' else '0')]
        assert argv[10:12]==['--emit=mir','-o']
        assert argv[12].endswith(f'/raw/{role}/{suite}/{mode}.mir')
        if mode.endswith('-dump'):
            selector='SimplifyCfg' if suite=='r563' else 'LowerIntrinsics'
            assert argv[13]=='-Zdump-mir='+selector
            assert argv[14].endswith(f'/raw/{role}/{suite}/{mode}-dumps') and argv[14].startswith('-Zdump-mir-dir=')
            assert argv[15:]==[f'fixture/{suite}.rs']
        else: assert argv[13:]==[f'fixture/{suite}.rs']
        gate=cell['admission']; pages=gate['pages']
        assert set(pages)=={'free','inactive','speculative'}
        assert gate['page_bytes']>0 and gate['memory_bytes']>0
        assert abs(gate['reclaimable_percent'] - 100*gate['page_bytes']*sum(pages.values())/gate['memory_bytes']) < 1e-9
        assert gate['reclaimable_percent']>20 and gate['disk_free_bytes']>1_073_741_824 and gate['owned_bytes']<100_000_000
        assert cell['terminated'] is None and cell['exit_code']==0
        assert 0 <= cell['sampled_peak_rss_kib'] < 1_048_576 and 0 < cell['elapsed_s'] < 30
        for stream in ('stdout','stderr'):
            rel=f'raw/{role}/{suite}/{mode}.{stream}'
            retained(rel,cell[f'{stream}_sha256'],cell[f'{stream}_bytes']);actual.add(rel)
        rel=f'raw/{role}/{suite}/{mode}.mir'
        mir=retained(rel,cell['artifact_sha256'],cell['artifact_bytes']).decode();actual.add(rel)
        mirs[key]=mir
        files=cell['dump_files']; assert len(files)==(48 if suite=='r563' else 8) if mode.endswith('-dump') else not files
        for path,meta in files.items():
            assert path.startswith(f'raw/{role}/{suite}/{mode}-dumps/') and '..' not in Path(path).parts
            retained(path,meta['sha256'],meta['bytes']);actual.add(path)
    assert actual=={str(p.relative_to(ROOT)) for p in (ROOT/'raw').rglob('*') if p.is_file()}
    for suite,modes in MODES.items():
        for mode in modes: assert mirs[f'old/{suite}/{mode}']==mirs[f'new/{suite}/{mode}']
    for suite,mode in (('r563','simplify-dump'),('r564','intrinsic-dump')):
        normalized=[]
        for role in SHA:
            files=data['cells'][f'{role}/{suite}/{mode}']['dump_files']
            normalized.append({re.sub(r'\.\d+-\d+-\d+\.', '.PASS.', Path(p).name):v['sha256']
                               for p,v in files.items()})
        assert len(normalized[0])==(48 if suite=='r563' else 8)
        assert normalized[0]==normalized[1]
    for role in SHA:
        a=mirs[f'{role}/r563/opt0']; b=mirs[f'{role}/r563/opt2']
        assert 'switchInt' in body(a,'constant_branch') and 'marker()' in body(a,'constant_branch')
        assert 'switchInt' not in body(b,'constant_branch') and 'marker()' not in body(b,'constant_branch')
        assert 'marker()' in body(a,'dynamic_branch') and 'marker()' in body(b,'dynamic_branch')
        assert 'switchInt' in body(b,'dynamic_branch')
        assert 'marker()' not in body(a,'after_return') and 'marker()' not in body(a,'after_diverge')
        dumps=data['cells'][f'{role}/r563/simplify-dump']['dump_files']
        for function in ('after_return','after_diverge'):
            before=[p for p in dumps if f'.{function}.' in p and 'SimplifyCfg-initial.before.mir' in p]
            after=[p for p in dumps if f'.{function}.' in p and 'SimplifyCfg-initial.after.mir' in p]
            assert len(before)==len(after)==1
            assert 'marker()' in (ROOT/before[0]).read_text() and 'marker()' not in (ROOT/after[0]).read_text()
        c=mirs[f'{role}/r564/opt0']; d=mirs[f'{role}/r564/opt2']
        operation=body(c,'operations')
        assert '&raw const (*_2)' in operation and 'copy (*_1)' in operation
        assert 'Bits { word:' in operation and re.search(r'copy \(_\d+\.0: u32\)',operation)
        assert 'unsafe_add(' in operation and 'asm!("nop"' in operation and 'static: COUNTER' in c
        assert 'asm!("nop"' in body(d,'operations')
        assert 'std::ptr::copy_nonoverlapping::<u8>' in body(c,'copy_one')
        intrinsic=data['cells'][f'{role}/r564/intrinsic-dump']['dump_files']
        before=[p for p in intrinsic if '.copy_one.' in p and 'LowerIntrinsics.before.mir' in p]
        after=[p for p in intrinsic if '.copy_one.' in p and 'LowerIntrinsics.after.mir' in p]
        assert len(before)==len(after)==1
        assert 'std::ptr::copy_nonoverlapping::<u8>' in (ROOT/before[0]).read_text()
        assert 'std::ptr::copy_nonoverlapping::<u8>' in (ROOT/after[0]).read_text()
    summary=json.loads((ROOT/'analysis.json').read_text())
    assert summary['schema']==1
    assert summary['all_12_exit_zero'] and summary['six_emitted_mir_pairs_equal']
    assert summary['r563_48_stage_dump_pairs_equal_after_pass_number_normalization']
    assert summary['r564_8_stage_dump_pairs_equal']
    assert all(summary['r563'].values()) and all(summary['r564'].values())
    print('PASS: exact identities, 12 guarded cells, raw hashes, MIR claims, and relocation')

if __name__=='__main__':main()
