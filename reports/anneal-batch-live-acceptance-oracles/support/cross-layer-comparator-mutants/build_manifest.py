#!/usr/bin/env python3
"""Derive the intentionally manual comparator contract from preserved R12 results."""
import json,pathlib
P=pathlib.Path(__file__).resolve().parent
R=json.loads((P/'results.json').read_text())
expected={'obl_inc':('inc',1),'obl_twice':('twice',2),'obl_choose':('choose',3)}
manifest={'basis':'fixture-authored contract plus executed output inventory; not Anneal producer metadata',
 'subjects':R['subjects'],
 'required_obligations':[{'theorem':n,'rust_function':fn,'required_lean_proposition':f'comparator_probe.{fn} 0#u32 = .ok {v}#u32'} for n,(fn,v) in expected.items()],
 'cases':{},'external_models':{},'proven_item_to_lean_range':None,
 'trust_rules':['exact expected proposition and complete theorem-name list','captured Rust source generation identity','compiled imported model identity','no sorryAx in claim axiom inventory']}
for name,c in R['cases'].items():
    entry={'source_sha256':c['source_sha256'],'llbc_sha256':c['llbc_sha256'],
      'generated':c['generated'],'declarations':R['model_manifest'][name]['rows']}
    if 'consumer' in c:
        entry['imported_funs_olean_sha256']=c['consumer']['Source/Funs.olean']['sha256']
        entry['proof_sha256']=c['consumer']['Proof.lean']['sha256']
        entry['batch_axiom_and_type_output']=c['proof_stdout']
        entry['rust_selected_value_oracle']=c['rust_oracle']
    manifest['cases'][name]=entry
ext=R['controls']['external_model']
manifest['external_models']={'generated_source_set_sha256':{n:v['sha256'] for n,v in R['cases']['external']['generated'].items()},
 'axiom_model_source_sha256':ext['axiom_model_source_sha256'],
 'concrete_model_source_sha256':ext['concrete_model_source_sha256'],
 'axiom_import_olean_sha256':ext['axiom_import_sha256'],
 'concrete_import_olean_sha256':ext['concrete_import_sha256'],
 'axiom_inventory':ext['axiom_stdout'],'concrete_inventory':ext['concrete_stdout']}
(P/'comparison-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('OK: five provenance cases, three manual obligations, two external-model assumptions')
