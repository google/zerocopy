#!/usr/bin/env python3
"""Offline, relocatable validation of the retained R530 host-layout probe."""
import difflib, hashlib, json, re
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent
TOOLS={'old':('nightly-2026-05-31','2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc','f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1','1.98.0-nightly'),
       'new':('nightly-2026-09-30','29f8ccc9aa7b0d8798eda854fa7f0e4ba3867c8c336b87d52dbb3b24b3f0878d','5c543b0b8c73c7b72bc8284ced4fb22ead15734d','1.101.0-nightly')}
FIXTURE='1614b1015dd9323d5c445eb11f6d9d3e36c94843c9d2aa42ef3c52a7ccb9fede'
EXPECTED_RUN='''Reordered size=16 align=8 offsets=10,0,8
CControl size=24 align=8 offsets=0,8,16
CUnion size=8 align=8
Payload size=16 align=8
OptionRef size=8 align=8
RefU8 size=8 align=8
slice_pointer size=16 align=8
str_pointer size=16 align=8
trait_pointer size=16 align=8
slice_value size=6 align=2
str_value size=3 align=1
trait_value size=4 align=4 value=7
'''
def sha(data):return hashlib.sha256(data).hexdigest()
def checked(path,digest,size):
    assert path.is_file(),path
    data=path.read_bytes();assert len(data)==size and sha(data)==digest,path
    return data
def main():
    data=json.loads((ROOT/'results.json').read_text())
    assert data['schema']==1 and data['fixture_sha256']==FIXTURE
    assert sha((ROOT/'fixture/layout.rs').read_bytes())==FIXTURE
    assert set(data['tools'])==set(TOOLS)
    assert set(data['cells'])=={f'{role}/{kind}' for role in TOOLS for kind in ('compile','run')}
    actual=set();outputs={}
    for role,(date,exe_sha,commit,release) in TOOLS.items():
        tool=data['tools'][role]
        assert tool['sha256']==exe_sha and tool['executable'].endswith(f'/{date}-aarch64-apple-darwin/bin/rustc')
        vv=tool['version_verbose']
        assert f'commit-hash: {commit}\n' in vv and f'release: {release}\n' in vv and 'host: aarch64-apple-darwin\n' in vv
        binary=ROOT/'raw'/role/'layout-probe'
        compile_argv=[tool['executable'],'--crate-name','layout_probe','--edition','2024','-C','opt-level=0','-Zprint-type-sizes','-o',str(binary),'fixture/layout.rs']
        for kind in ('compile','run'):
            cell=data['cells'][f'{role}/{kind}']
            if kind=='compile':
                assert cell['argv'][:9]==compile_argv[:9]
                assert cell['argv'][9].endswith(f'/raw/{role}/layout-probe')
                assert cell['argv'][10:]==compile_argv[10:]
            else:assert len(cell['argv'])==1 and cell['argv'][0].endswith(f'/raw/{role}/layout-probe')
            gate=cell['admission'];pages=gate['pages']
            assert set(pages)=={'free','inactive','speculative'}
            assert abs(gate['reclaimable_percent']-100*gate['page_bytes']*sum(pages.values())/gate['memory_bytes'])<1e-9
            assert gate['reclaimable_percent']>20 and gate['disk_free_bytes']>1_073_741_824 and gate['owned_bytes']<100_000_000
            assert cell['exit_code']==0 and cell['terminated'] is None
            assert 0<=cell['sampled_peak_rss_kib']<1_048_576 and 0<cell['elapsed_s']<30
            for stream in ('stdout','stderr'):
                rel=f'raw/{role}/{kind}.{stream}'
                outputs[(role,kind,stream)]=checked(ROOT/rel,cell[f'{stream}_sha256'],cell[f'{stream}_bytes']).decode()
                actual.add(rel)
        comp=data['cells'][f'{role}/compile']
        checked(binary,comp['binary_sha256'],comp['binary_bytes']);actual.add(f'raw/{role}/layout-probe')
        assert outputs[(role,'compile','stderr')]=='' and outputs[(role,'run','stderr')]==''
        assert outputs[(role,'run','stdout')]==EXPECTED_RUN
        c=outputs[(role,'compile','stdout')]
        for line in ('`Reordered`: 16 bytes, alignment: 8 bytes','`CControl`: 24 bytes, alignment: 8 bytes',
                     '`CUnion`: 8 bytes, alignment: 8 bytes','`Payload`: 16 bytes, alignment: 8 bytes',
                     '`std::option::Option<&u8>`: 8 bytes, alignment: 8 bytes',
                     '`std::ptr::DynMetadata<dyn Trait>`: 8 bytes, alignment: 8 bytes'):
            assert line in c
        assert re.search(r'`Reordered`.*\n(?:.*\n)*?print-type-size     field `\.b`: 8 bytes\nprint-type-size     field `\.c`: 2 bytes\nprint-type-size     field `\.a`: 1 bytes',c)
    assert actual=={str(p.relative_to(ROOT)) for p in (ROOT/'raw').rglob('*') if p.is_file()}
    old=outputs[('old','compile','stdout')].splitlines()
    new=outputs[('new','compile','stdout')].splitlines()
    diff=list(difflib.unified_diff(old,new))
    assert len(old)==len(new)==98
    assert len([line for line in diff if line.startswith('-') and not line.startswith('---')])==1
    assert len([line for line in diff if line.startswith('+') and not line.startswith('+++')])==1
    assert '-print-type-size type: `unwind::libunwind::_Unwind_Reason_Code`: 4 bytes, alignment: 4 bytes' in diff
    assert '+print-type-size type: `unwind::types::_Unwind_Reason_Code`: 4 bytes, alignment: 4 bytes' in diff
    analysis=json.loads((ROOT/'analysis.json').read_text())
    assert analysis['run_stdout_byte_equal'] and analysis['selected_host_layout_equal']
    assert analysis['compiler_stdout_line_count_per_version']==98 and analysis['compiler_stdout_differing_lines']==1
    print('PASS: 4 guarded cells, exact identities and hashes, selected layout equality, one compiler-print name delta, relocation')
if __name__=='__main__':main()
