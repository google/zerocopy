#!/usr/bin/env python3
"""Offline integrity and oracle check for the preserved one-shot matrix."""
import hashlib,json
from pathlib import Path

HERE=Path(__file__).resolve().parent
x=json.loads((HERE/'raw-results.json').read_text())
assert 'fatal' not in x
assert set(x['translations'])=={'base','reorder','shrink','error'}
for case,trans in x['translations'].items():
    assert trans['charon_rc']==0
    assert (trans['aeneas_rc']!=0)==(case=='error')
    source=HERE/'inputs'/case/'trait_probe.rs';llbc=HERE/'inputs'/case/'trait_probe.llbc'
    assert hashlib.sha256(source.read_bytes()).hexdigest()==x['inventories'][case]['source_sha256']
    assert hashlib.sha256(llbc.read_bytes()).hexdigest()==x['inventories'][case]['llbc_sha256']
    for name,record in x['inventories'][case]['files'].items():
        p=HERE/'outputs'/case/name
        assert p.stat().st_size==record['bytes']
        assert hashlib.sha256(p.read_bytes()).hexdigest()==record['sha256']
    m=x['manifests'][case]
    assert m['proven_rust_to_lean_mapping'] is None and m['editable_proof_ranges'] is None
    for decl in m['lean_declarations']:
        raw=(HERE/'outputs'/case/decl['file']).read_bytes()
        lo,hi=decl['byte_range'];assert 0<=lo<hi<=len(raw)
        assert decl['head'] in raw[lo:hi].decode()
        assert decl['authenticated_charon_link'] is None
base=set(x['inventories']['base']['files']);shrink=set(x['inventories']['shrink']['files'])
assert 'FunsExternal_Template.lean' in base-shrink
assert 'FunsExternal_Template.lean' in x['reused_after_shrink']
assert x['inventories']['base']['files']['Funs.lean']['sha256']!=x['inventories']['reorder']['files']['Funs.lean']['sha256']
for case in ['base','reorder','shrink']:
    assert x['consumers'][case]['check_rc']==0
    assert all(rc==0 for rc in x['consumers'][case]['compile'])
assert x['consumers']['shrink-removed']['rc']!=0
assert x['consumers']['base-concrete']['rc']==0 and 'does not depend on any axioms' in x['consumers']['base-concrete']['stdout']
assert x['consumers']['error']['rc']==0 and 'sorryAx' in x['consumers']['error']['stdout']
assert any(e['kind']=='command' and e['label']=='error:aeneas' and e['rc']!=0 for e in x['events'])
print(f"OK: four Charon/Aeneas cases, fresh Lean consumers, exact file/range hashes, stale-output and sorry controls; {len(x['events'])} events")
