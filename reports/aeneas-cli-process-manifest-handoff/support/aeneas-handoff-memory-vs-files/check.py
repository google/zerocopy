#!/usr/bin/env python3
"""Validate retained I086 component and wrapper handoff observations."""
import hashlib,json
from pathlib import Path
here=Path(__file__).resolve().parent;work=here/'work'
r=json.loads((here/'results.json').read_text());assert r['schema']==1 and len(r['commands'])==27
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for path,digest in r['tools'].items():assert sha(path)==digest
assert sha(work/'source.rs')==r['source_sha256']
assert sha(work/'source.llbc')==r['llbc_sha256'] and (work/'source.llbc').stat().st_size==r['llbc_bytes']
assert r['transfer']['copied_sha256']==r['transfer']['target_sha256']==r['llbc_sha256']
assert r['transfer']['repetitions']==16 and r['transfer']['python_tracemalloc_peak_bytes']>r['llbc_bytes']
assert r['buffer_stage']['input_sha256']==sha(work/'buffer-stage/source.llbc')==r['llbc_sha256']
assert r['buffer_stage']['python_peak_bytes']>=r['llbc_bytes']
for mode,gen in [('file',work/'generated-file'),('buffer',work/'generated-buffer')]:
    x=r[mode];assert x['aeneas']['rc']==0 and x['lean']['chain_rc']==[0,0,0] and x['lean']['oracle_rc']==0
    assert x['aeneas']['peak_sampled_rss_kib'] and x['aeneas']['rss_sample_count']>0
    for name,m in x['generated'].items():
        p=gen/name;assert p.stat().st_size==m['bytes'] and sha(p)==m['sha256']
assert r['file']['generated']==r['buffer']['generated']
for m in ('Source/Types.olean','Source/Funs.olean','Source.olean'):
    assert r['file']['lean']['compiled_inventory'][m]['sha256']==r['buffer']['lean']['compiled_inventory'][m]['sha256']
s=r['stdin'];assert s['chain_rc']==[0,0,0] and s['consumer_rc']==0
assert s['context_equivalence_proven'] is False and not any(s['olean_hash_equal_to_file'].values())
assert s['diagnostic_path_control']['file_rc']!=0 and s['diagnostic_path_control']['stdin_rc']!=0
assert not s['diagnostic_path_control']['diagnostics_byte_equal']
assert 'CheckWrong.lean:' in s['diagnostic_path_control']['file_stdout']
assert '<stdin>:' in s['diagnostic_path_control']['stdin_stdout']
assert r['source_map']['has_errors'] is False and r['source_map']['source_path_in_generated']
assert any('source.rs' in line for line in r['source_map']['generated_source_lines'])
assert r['source_map']['llbc_functions']
for label in ('truncated','corrupt'):
    x=r['input_errors'][label]
    assert x['rc']!=0 and x['generated']=={}
    assert sha(work/f'{label}-llbc/source.llbc')==x['input_sha256']
assert r['generated_text_errors']['truncated']['compile_rcs'][-1]!=0
assert r['generated_text_errors']['semantic_mutation']['compile_rcs']==[0,0,0]
assert r['generated_text_errors']['semantic_mutation']['oracle_rc']!=0
for label in ('file','buffer'):
    x=r['cancellation'][label]
    assert x['rc']==-15 and x['members_before'] and not x['members_after']
    assert x['partial_inventory'].keys()=={'Types.lean'} and x['retry_rc']==0
    assert {'Types.lean','Funs.lean','Source.lean'}<=x['retry_inventory'].keys()
assert r['boundary'].startswith('Python bytes around one-shot Aeneas CLI')
print('I086 retained-result checks passed')
