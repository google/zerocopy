"""Read-only binding check. Does not execute Rocq or establish a new theorem result."""
from pathlib import Path
import hashlib,json,re
p=Path(__file__).resolve().parent.parent;s=p/'support'
def require(ok,message):
 if not ok:raise SystemExit('FAIL: '+message)
def sha(b):return hashlib.sha256(b).hexdigest()
def load(f):return json.loads(f.read_text())
m=load(p/'package-manifest.json');expected={x['path']:x for x in m['files']}
actual={q.relative_to(p).as_posix():q for q in p.rglob('*') if q.is_file() and q!=p/'package-manifest.json'}
require(set(actual)==set(expected),'package path set')
for name,q in actual.items():
 require(not q.is_symlink(),'symlink '+name);b=q.read_bytes();x=expected[name]
 require(len(b)==x['bytes'] and sha(b)==x['sha256'],'package bytes '+name)
require(set(load(p/'REPORT.json'))=={'topics','subjects','observed_at'},'metadata fields')
for file,digest in [('simuliris.tar.gz','06dbeeb1ddda80ffe93b26fd20d8597f9c9a63767ae2a7e74e4dae696952fb9b'),('simuliris-iris.tar.gz','3b45252c8b915dcee1149dd0d185391898cc836619b7c4e1fc1f636acb23057b'),('simuliris-stdpp.tar.gz','e9588be3a78ad1b54a045a3237e5ae2ca7e0db8aebf1e0cfe8e90a6a64e0e6f2')]:require(sha((s/'inputs'/file).read_bytes())==digest,'input archive '+file)
x=load(s/'actual-results.json');rows=x['selected_constants'];require(len(rows)==24,'24constants')
require(x['assumption_groups']=={'closed':19,'classic_and_indefinite_description':5},'assumption groups')
trace=(s/'logs/recursive-native-checker.stderr').read_text();argv=load(s/'logs/recursive-native-checker.json')['argv']
require('-admit' not in argv and '-norec' not in argv,'recursive checker bypass')
require('Modules were successfully checked' in trace,'checker success marker')
require(load(s/'logs/recursive-native-checker.json')['exit_code']==0,'checker exit')
paths=re.findall(r'^\[intern (/.+?) \.\.\.$',trace,re.M);libs=re.findall(r'^Checking library: (.+)$',trace,re.M)
require(len(paths)==len(set(paths))==len(libs)==len(set(libs))==517,'native loaded/checked sets')
require((s/'logs/loaded-object-hashes-during-check.stdout').read_bytes()==(s/'logs/loaded-object-hashes-after-check.stdout').read_bytes(),'object hash stability')
require(len((s/'logs/loaded-object-hashes-after-check.stdout').read_text().splitlines())==517,'object hashes517')
for z in rows:require('  checking cst:'+z['constant']+'\n' in trace,'native constant '+z['constant'])
require(len(x['recursive_checker']['global_axioms'])==3,'global context3')
for label in ['generic-corrected','tree-borrows-core','protected-and-unprotected-examples','sequential-read-reordering','audit-PlannedAuditFramework','audit-PlannedAuditResources','audit-PlannedAuditExamples']:
 require(load(s/'logs'/(label+'.json'))['exit_code']==0,'phase '+label)
require(load(s/'logs/generic-build.json')['exit_code']==2,'preserved initial setup failure')
flags=load(s/'corrected-mapping-regression.json')['checks'];require(all(flags.values()),'corrected mapping')
require('-R . Top' in (s/'binding-failure-artifacts/Makefile.rocq.conf').read_text(),'preserved failed flags')
fixed=(s/'checked-project/Makefile.rocq.conf').read_text();require('-Q theories simuliris' in fixed and '-R . Top' not in fixed,'fixed flags')
inv=load(s/'historical-plan/archive-inventory.json')['files'];prefix='simuliris-e3abfcdc301f92250d4227fc03c00463bf57b982/'
require(len(inv)==185,'original185')
for z in inv:require(sha((s/'checked-project'/z['path'][len(prefix):]).read_bytes())==z['sha256'],'original '+z['path'])
copy=load(s/'copied-project-file-manifest.json');require(len(copy)==591,'copied591')
for z in copy:require(sha((s/'checked-project'/z['path']).read_bytes())==z['sha256'],'copied '+z['path'])
for label in ['initial-source-check','post-failure-original-source-check','final-source-check']:
 require(len((s/'logs'/(label+'.stdout')).read_text().splitlines())==185 and load(s/'logs'/(label+'.json'))['exit_code']==0,'source check '+label)
for z in load(s/'namespace-rebuild-bindings.json'):
 require(sha((s/'binding-failure-artifacts'/z['source_object'].replace('/','_')).read_bytes())==z['failed_mapping_sha256'],'failed object binding')
 require(sha((s/'checked-project'/z['source_object']).read_bytes())==z['corrected_mapping_sha256'],'corrected object binding')
 require(z['failed_mapping_sha256']!=z['corrected_mapping_sha256'],'distinct rebuilt object')
for q in (s/'logs').glob('*.json'):
 z=load(q)
 for stream in ['stdout','stderr']:
  b=q.with_suffix('.'+stream).read_bytes()
  require(z[stream+'_sha256']==sha(b),'stream hash '+q.name+':'+stream)
  if stream+'_bytes' in z:require(z[stream+'_bytes']==len(b),'stream size '+q.name+':'+stream)
  else:require(q.name=='binding-failure-diagnosis.json','unrecognized receipt schema '+q.name)
for z in load(s/'public-path-projection.json')['records']:require(sha((s/z['path']).read_bytes())==z['public_sha256'],'projection '+z['path'])
print(json.dumps({'result':'PASS','manifest_files':len(actual),'original_sources':185,'copied_project_files':591,'selected_constants':24,'closed_constants':19,'classical_constants':5,'native_libraries':517,'global_axioms':3,'kernel_replayed_by_this_script':False},indent=2))
