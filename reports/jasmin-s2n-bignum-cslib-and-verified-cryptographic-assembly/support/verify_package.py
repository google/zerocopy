#!/usr/bin/env python3
"""Read-only retained-evidence validation; never runs an upstream program."""
import argparse,hashlib,json,re
from pathlib import Path
ap=argparse.ArgumentParser()
ap.add_argument('--out',type=Path)
args=ap.parse_args()
r=Path(__file__).resolve().parent
package=r.parent
if args.out:
    dest=args.out.resolve()
    if dest==package or package in dest.parents or dest.exists():
        raise SystemExit('STOP: optional output must be new and outside frozen package')
manifest=json.loads((package/'package-manifest.json').read_text())
listed=set()
for row in manifest['files']:
    rel=row['path'];listed.add(rel);b=(package/rel).read_bytes()
    if len(b)!=row['bytes'] or hashlib.sha256(b).hexdigest()!=row['sha256']:
        raise SystemExit('STOP: manifest mismatch '+rel)
actual={str(p.relative_to(package)) for p in package.rglob('*') if p.is_file() and p.name!='package-manifest.json'}
if actual!=listed:raise SystemExit('STOP: package file keyset mismatch')
metadata=json.loads((package/'REPORT.json').read_text())
if set(metadata)!={'topics','subjects','observed_at'}:raise SystemExit('STOP: report metadata fields')
source_index=json.loads((r/'source-census-preserved.json').read_text())
for row in source_index:
    b=(r/'sources'/row['path']).read_bytes()
    if len(b)!=row['bytes'] or hashlib.sha256(b).hexdigest()!=row['sha256']:
        raise SystemExit('STOP: preserved original source mismatch')
census=json.loads((r/'logs/selected-census.stdout').read_text())
for part in ['hol_core','selected']:
    for row in census[part]['inputs']:
        name=row['path']
        if name.startswith('/home/opam/anneal-cross-sources/'):
            src=r/'sources'/name[len('/home/opam/anneal-cross-sources/'):]
        elif name.startswith('/home/opam/anneal-cross-output/audit/'):
            src=r/'audit'/Path(name).name
        else:raise SystemExit('STOP: unknown source path')
        b=src.read_bytes()
        if hashlib.sha256(b).hexdigest()!=row['sha256'] or hashlib.md5(b).hexdigest()!=row['md5']:
            raise SystemExit('STOP: actual inclusion source identity mismatch')
results=json.loads((r/'results.json').read_text())
if hashlib.sha256((r/'artifacts/selected.native').read_bytes()).hexdigest()!=results['native_program']['sha256']:
    raise SystemExit('STOP: native artifact identity mismatch')
for row,name in zip(results['elfs'],['bignum_add.o','bignum_add.obj']):
    if hashlib.sha256((r/'artifacts'/name).read_bytes()).hexdigest()!=row['sha256']:
        raise SystemExit('STOP: ELF artifact identity mismatch')
receipt=json.loads((r/'logs/positive.json').read_text())
if receipt['returncode']!=0:
    raise SystemExit('STOP: positive nonzero; parent diagnosis required')
raw=(r/'logs/positive.stdout').read_bytes()
if hashlib.sha256(raw).hexdigest()!=receipt['stdout_sha256']:
    raise SystemExit('STOP: stream hash discrepancy')
lines=raw.decode().splitlines()
theorems={};active=None;body=[]
before=[];after=[];none=[];lengths=[];axioms=[]
for line in lines:
    if line.startswith('ANNEAL_THEOREM_BEGIN '):
        if active is not None:raise SystemExit('STOP: nested theorem markers')
        active=line[len('ANNEAL_THEOREM_BEGIN '):];body=[]
    elif line.startswith('ANNEAL_THEOREM_END '):
        name=line[len('ANNEAL_THEOREM_END '):]
        if active!=name or name in theorems:raise SystemExit('STOP: theorem marker mismatch')
        theorems[name]='\n'.join(body);active=None;body=[]
    elif active is not None:
        body.append(line)
    elif line.startswith('ANNEAL_LOADED '):
        stage,rest=line[len('ANNEAL_LOADED '):].split(' ',1)
        name,digest=rest.rsplit(' ',1)
        row=(json.loads(name),digest)
        if stage=='core_before_proof':before.append(row)
        elif stage=='after_inner_audit':after.append(row)
        else:raise SystemExit('STOP: unknown ledger stage')
    elif line.startswith('ANNEAL_DECODE_ARRAY_LENGTH '):
        lengths.append(int(line.split()[-1]))
    elif line.startswith('ANNEAL_DECODE_NONE '):
        none.append(int(line.split()[-1]))
    elif line.startswith('ANNEAL_GLOBAL_AXIOM '):
        axioms.append(line[len('ANNEAL_GLOBAL_AXIOM '):])

fixed=['bignum_add_mc','bignum_add_tmc','BIGNUM_ADD_EXEC.length_theorem',
       'bignum_add_windows_mc','bignum_add_windows_tmc','BIGNUM_ADD_CORRECT',
       'BIGNUM_ADD_NOIBT_SUBROUTINE_CORRECT','BIGNUM_ADD_SUBROUTINE_CORRECT',
       'BIGNUM_ADD_WINDOWS_CORRECT','BIGNUM_ADD_NOIBT_WINDOWS_SUBROUTINE_CORRECT',
       'BIGNUM_ADD_WINDOWS_SUBROUTINE_CORRECT','ANNEAL_ONE_LIMB_SUBROUTINE_CORRECT']
decoded={int(name.split('_')[-1]):name for name in theorems if name.startswith('BIGNUM_ADD_EXEC.decode_')}
census=json.loads((r/'logs/selected-census.stdout').read_text())
core=[(x['basename'],x['md5']) for x in reversed(census['hol_core']['digest_completion_order'])]
selected=census['selected']['digest_completion_order']
expected_after=[(x['basename'],x['md5']) for x in reversed(selected[:-1])]+core
checks={
 'exit0':receipt['returncode']==0,
 'no_incomplete_theorem':active is None,
 'exact_fixed12_plus_actual_decode_names':set(theorems)==set(fixed)|set(decoded.values()),
 'all_statements_have_closed_sequent_print':all(s.lstrip().startswith('|-') for s in theorems.values()),
 'one_decode_length181':lengths==[181],
 'every_decode_offset_exactly_once':len(decoded)+len(none)==181 and set(decoded)|set(none)==set(range(181)) and not set(decoded)&set(none) and len(none)==len(set(none)),
 'core47_runtime_ledger_exact':before==core,
 'after_inner83_runtime_ledger_exact':after==expected_after,
 'three_global_axiom_headers':len(axioms)==3,
 'inner_check_marker_once':lines.count('ANNEAL_CHECK_AXIOMS_PASS')==1,
 'outer_check_marker_once':lines.count('ANNEAL_CHECK_AXIOMS_OUTER_PASS')==1,
 'inner_end_once':lines.count('ANNEAL_AUDIT_INNER_FINISHED')==1,
 'outer_end_once':lines.count('ANNEAL_AUDIT_FINISHED')==1}
result={'checks':checks,'fixed_theorems':fixed,'theorem_count':len(theorems),
        'decode_some_offsets':sorted(decoded),'decode_none_offsets':sorted(none),
        'runtime_core_ledger_count':len(before),'runtime_after_inner_count':len(after),
        'global_axiom_headers':axioms,
        'explicit_hypothesis_check':'Original reviewed audit checks original hyp th=[] before every theorem print; successful completion and closed sequent prints observed.',
        'per_theorem_axiom_dependencies':'Not provided by this HOL audit; global policy differs.'}
if result != json.loads((r/'positive-verification.json').read_text()):
    raise SystemExit('STOP: recomputed positive verification differs')
if theorems != json.loads((r/'theorem-statements.json').read_text()):
    raise SystemExit('STOP: recomputed theorem statements differ')
summary={'status':'PASS retained-evidence validation only; no theorem/proof runtime executed','manifest_files':len(manifest['files']),'source_files':len(source_index),'theorem_count':result['theorem_count'],'decode_some':len(result['decode_some_offsets']),'decode_none':len(result['decode_none_offsets']),'checks':checks}
if args.out:
    args.out.write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
if not all(checks.values()):raise SystemExit('STOP: positive acceptance discrepancy; parent diagnosis required')
