#!/usr/bin/env python3
"""Validate retained local mapping and direct Lean protocol observations."""
import hashlib,json
from pathlib import Path
here=Path(__file__).resolve().parent;work=here/'work'
r=json.loads((here/'results.json').read_text());assert r['schema']==1
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(work/'host.rs')==r['rust_sha256']
assert sha(work/'Projected.lean')==r['projected_lean_sha256']
assert sha(work/'host.rmeta')==r['rustc']['rmeta_sha256']
assert sha(r['rustc']['argv'][0])==r['rustc_sha256'] and r['rustc']['rc']==0
assert sha('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')==r['lean_sha256']
m=r['mapping']
assert m['rust_line_to_lean_line']=={'2':2,'3':3,'4':4}
assert m['projected_helper_position']=={'line':3,'character':52}
assert m['unicode_bytes_before_helper']==55 and m['unicode_utf16_before_helper']==52
assert m['invalid_utf8_interior_rejected'] and m['surrogate_half_reverse'] is None
assert m['scaffold_only_reverse'] is None and m['ordinary_rust_forward'] is None and m['marker_forward'] is None
rust=work/'host.rs';assert rust.read_bytes()[m['rust_byte_range']['start']:m['rust_byte_range']['end']]==b'helper'
s=r['states'];assert set(s)=={'initial','reopen','restart'}
assert s['initial']['pid']==s['reopen']['pid']!=s['restart']['pid']
for k in s:
    row=s[k]
    assert 'h : n = 7' in row['plain_goal']['result']['rendered']
    goals=row['rich_goal']['result']['goals'];assert len(goals)==1
    assert [['n'],['h']]==[h['names'] for h in goals[0]['hyps']]
assert len(s['initial']['definition']['result'])==1
assert len(s['initial']['references']['result'])==2
assert len(s['initial']['opened_hyperlinks'])==3
for link in s['initial']['opened_hyperlinks']:
    assert link['rust_file_opened']==str(rust)
    offset=link['rust_source']['rust_byte_offset']
    assert rust.read_bytes()[offset:offset+6]==b'helper'
assert s['initial']['opened_hyperlinks'][0]['rust_source']['rust_line']==2
assert s['initial']['opened_hyperlinks'][2]['rust_source']['rust_line']==3
assert s['reopen']['old_session_after_close']['error']['code']==-32801
assert s['restart']['old_worker_session_before_connect']['error']['code']==-32900
assert not s['reopen']['local_old_handle_accepted_for_routing']
assert not s['restart']['local_old_worker_handle_accepted_for_routing']
assert all(e['rc']==0 for e in r['transcript'] if e['kind']=='stop')
assert any(e['kind']=='client' and e['message'].get('method')=='$/lean/rpc/call' for e in r['transcript'])
print('I061 retained-result checks passed')
