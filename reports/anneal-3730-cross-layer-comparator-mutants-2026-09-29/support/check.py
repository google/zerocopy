#!/usr/bin/env python3
"""Check acquired R12 fixture bytes, comparator controls, and manifest."""
import hashlib,json,pathlib,re,subprocess
P=pathlib.Path(__file__).resolve().parent;W=P/'work'
R=json.loads((P/'results.json').read_text());M=json.loads((P/'comparison-manifest.json').read_text())
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def inv(root):return {p.relative_to(root).as_posix():{'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(root.rglob('*')) if p.is_file()}
assert len(R['commands'])==52
assert len(R['cases'])==5
assert [x['theorem'] for x in M['required_obligations']]==['obl_inc','obl_twice','obl_choose']
for name,c in R['cases'].items():
    root=W/name
    assert sha(root/'source.rs')==c['source_sha256']
    assert sha(root/'Source.llbc')==c['llbc_sha256']
    assert inv(root/'generated')==c['generated']
    assert M['cases'][name]['source_sha256']==c['source_sha256']
    assert M['cases'][name]['llbc_sha256']==c['llbc_sha256']
    if name!='external':
        assert c['rust_oracle']['exit']==0
        assert sha(root/'RustOracle.rs')==c['rust_oracle']['source_sha256']
        consumer=W/('consumer-'+name)
        actual=inv(consumer)
        assert all(actual[k]==v for k,v in c['consumer'].items())
        assert c['proof_stdout'].count('depends on axioms: [propext, Classical.choice, Quot.sound]')==3
        assert 'sorryAx' not in c['proof_stdout']
        assert M['cases'][name]['imported_funs_olean_sha256']==c['consumer']['Source/Funs.olean']['sha256']
C=R['controls']
assert C['strong']['lean_exit']==0 and C['strong']['manifest']['accepted']
for name in ('weaker_proposition','missing_obligation','admitted_claim','stale_source'):
    assert C[name]['lean_exit']==0 and not C[name]['manifest']['accepted']
assert 'obligation/proposition mismatch' in C['weaker_proposition']['manifest']['reasons']
assert 'obligation/proposition mismatch' in C['missing_obligation']['manifest']['reasons']
assert 'admission axiom' in C['admitted_claim']['manifest']['reasons']
assert 'source generation mismatch' in C['stale_source']['manifest']['reasons']
assert C['swapped_import']['old_proof_exit']!=0 and C['swapped_import']['weak_proof_exit']==0
assert 'imported model mismatch' in C['swapped_import']['manifest']['reasons']
assert C['swapped_import']['base_import_sha256']!=C['swapped_import']['swapped_import_sha256']
E=C['external_model']
assert E['generated_equal'] and E['axiom_exit']==E['concrete_exit']==0
assert E['axiom_model_source_sha256']!=E['concrete_model_source_sha256']
assert E['axiom_import_sha256']!=E['concrete_import_sha256']
assert '[external_double]' in E['axiom_stdout'] and 'does not depend on any axioms' in E['concrete_stdout']
assert M['external_models']['axiom_model_source_sha256']==E['axiom_model_source_sha256']
assert M['proven_item_to_lean_range'] is None
Q=R['comparison']
assert Q['base_vs_reorder_source_bytes_equal'] is False
assert Q['base_vs_reorder_llbc_bytes_equal'] is False
assert Q['base_vs_reorder_funs_bytes_equal'] is False
assert Q['base_vs_reorder_selected_proof_stdout_equal'] is True
assert Q['base_vs_clean_source_bytes_equal'] is True
assert Q['base_vs_clean_selected_proof_stdout_equal'] is True
print('OK: five exact artifact inventories, 52 process records, four positive Rust/Lean oracles and seven controls')
