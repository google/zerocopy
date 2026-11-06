"""Derive checked bindings from preserved execution, without executing proof tools."""
from pathlib import Path
import json,re,hashlib,collections
r=Path(__file__).resolve().parent
h=lambda b:hashlib.sha256(b).hexdigest()
plan=json.loads((r.parent/'simuliris-plan/TARGETS.json').read_text())['constants'];rows=[]
for audit in ['PlannedAuditFramework.v','PlannedAuditResources.v','PlannedAuditExamples.v']:
 text=(r/'logs'/('audit-'+audit[:-2]+'.stdout')).read_text().split('ANNEAL_PHASE_RESULT',1)[0]
 headers=list(re.finditer(r"(?m)^@?([A-Za-z_][\w']*)\n     :",text));targets=[x for x in plan if x['annotation']==audit]
 if len(headers)!=len(targets):raise SystemExit('Audit header count mismatch: '+audit)
 for j,(m,t) in enumerate(zip(headers,targets)):
  block=text[m.start():headers[j+1].start() if j+1<len(headers) else len(text)].strip()
  if m[1]!=t['constant'].split('.')[-1]:raise SystemExit('Audit order/name mismatch')
  if '\nAxioms:\n' in block:
   typ,asm=block.split('\nAxioms:\n',1)
   axioms=re.findall(r'(?m)^([A-Za-z_][\w.]*) :',asm)
   if len(axioms)!=2 or set(axioms)!={'IndefiniteDescription.constructive_indefinite_description','Classical_Prop.classic'}:raise SystemExit('Unexpected selected assumptions')
  elif block.endswith('Closed under the global context'):
   typ=block.removesuffix('Closed under the global context').rstrip();asm='Closed under the global context';axioms=[]
  else:raise SystemExit('Unrecognized assumption result')
  rows.append({**{k:v for k,v in t.items() if k!='status'},'status':'actual Check and Print Assumptions passed; body recursively kernel checked','printed_type':typ,'axioms':axioms,'raw_assumption_text':asm})
trace=(r/'logs/recursive-native-checker.stderr').read_text();native=json.loads((r/'logs/recursive-native-checker.json').read_text())
paths=re.findall(r'^\[intern (/.+?) \.\.\.$',trace,re.M);libs=re.findall(r'^Checking library: (.+)$',trace,re.M)
if len(paths)!=len(set(paths)) or len(libs)!=len(set(libs)) or len(libs)!=len(paths):raise SystemExit('Loaded/checked library count mismatch')
for x in rows:
 x['recursive_checker_constant_seen']=('  checking cst:'+x['constant']+'\n') in trace
 if not x['recursive_checker_constant_seen']:raise SystemExit('Missing kernel constant: '+x['constant'])
if native['exit_code']!=0 or 'Modules were successfully checked' not in trace:raise SystemExit('Native checker did not pass')
if any(x in native['argv'] for x in ['-admit','-norec']):raise SystemExit('Dependency bypass present')
ctx=trace.split('CONTEXT SUMMARY',1)[1];global_axioms=[x.strip() for x in ctx.split('* Axioms:',1)[1].split('* Constants/',1)[0].splitlines() if x.strip()]
objhash={z.split('  ',1)[1]:z.split('  ',1)[0] for z in (r/'logs/final-proof-artifact-inventory.stdout').read_text().splitlines()}
copy=r/'checked-project';copy_verified=[]
for p in sorted(copy.rglob('*')):
 if p.is_symlink():raise SystemExit('Unexpected symlink in project copy')
 if p.is_file():
  rel=p.relative_to(copy).as_posix();actual=h(p.read_bytes());expected=objhash['./'+rel]
  if actual!=expected:raise SystemExit('Project copy hash mismatch: '+rel)
  copy_verified.append({'path':rel,'bytes':p.stat().st_size,'sha256':actual})
if len(copy_verified)!=len(objhash):raise SystemExit('Project copy set mismatch')
original=json.loads((r.parent/'simuliris-plan/archive-inventory.json').read_text())['files'];prefix='simuliris-e3abfcdc301f92250d4227fc03c00463bf57b982/'
for x in original:
 if h((copy/x['path'][len(prefix):]).read_bytes())!=x['sha256']:raise SystemExit('Original source bytes changed')
phases=[]
for label in ['generic-build','generic-corrected','tree-borrows-core','protected-and-unprotected-examples','sequential-read-reordering','audit-PlannedAuditFramework','audit-PlannedAuditResources','audit-PlannedAuditExamples','recursive-native-checker']:
 x=json.loads((r/'logs'/(label+'.json')).read_text());s=(r/'logs'/(label+'.stdout')).read_text();m=re.search(r'ANNEAL_PHASE_RESULT returncode=(\d+) stop=(\S+) elapsed_seconds=(\d+) start_bytes=(\d+) peak_bytes=(\d+) final_bytes=(\d+)',s)
 if not m:raise SystemExit('Phase receipt missing')
 phases.append({'label':label,'exit_code':x['exit_code'],'wall_seconds':x['elapsed_seconds'],'phase_receipt':dict(zip(['returncode','stop','elapsed_seconds','start_bytes','peak_bytes','final_bytes'],m.groups()))})
result={'subject_revision':'e3abfcdc301f92250d4227fc03c00463bf57b982','selected_original_seeds':6,'observation_audits':3,'selected_constants':rows,'assumption_groups':{'closed':sum(not x['axioms'] for x in rows),'classic_and_indefinite_description':sum(bool(x['axioms']) for x in rows)},'recursive_checker':{'exit_code':native['exit_code'],'libraries_loaded_and_checked':len(libs),'original_simuliris_libraries':sum(x.startswith('simuliris.') for x in libs),'observation_libraries':sum(x.startswith('PlannedAudit') for x in libs),'global_axioms':global_axioms,'context_summary':'CONTEXT SUMMARY'+ctx,'max_heap_kbytes':int(re.search(r'total heap size = (\d+) kbytes',(r/'logs/recursive-native-checker.stdout').read_text())[1]),'no_admit_or_norec':True,'every_selected_constant_seen':True,'loaded_objects_sha256_stable':True},'phases':phases,'source_identity':{'original_files':len(original),'all_original_bytes_unchanged':True,'copied_project_files':len(copy_verified),'copied_project_files_sha256_verified':True}}
(r/'actual-results.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
(r/'copied-project-file-manifest.json').write_text(json.dumps(copy_verified,indent=2)+'\n')
print(json.dumps({'groups':result['assumption_groups'],'kernel_libraries':len(libs),'project_libraries':result['recursive_checker']['original_simuliris_libraries'],'copied_files':len(copy_verified),'selected_constants':len(rows)}))
