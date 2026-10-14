"""Read-only package evidence reconciliation; does not perform a Coq replay."""
from pathlib import Path
from collections import Counter
import hashlib,json,re,tarfile,zipfile,io
S=Path(__file__).resolve().parent
P=S.parent
def require(ok,message):
 if not ok:raise ValueError(message)
def sha(b):return hashlib.sha256(b).hexdigest()
a=json.loads((S/'source-identity-proposal.json').read_text())
zbytes=(S/'the_artifact.zip').read_bytes()
require(sha(zbytes)==a['archive_sha256'],'source archive hash')
with zipfile.ZipFile(io.BytesIO(zbytes)) as z:
 for row in a['file_manifest']:
  b=z.read('the_artifact/'+row['path'])
  require(len(b)==row['bytes'] and sha(b)==row['sha256'],row['path'])
with zipfile.ZipFile(io.BytesIO(zbytes)) as z:
 for row in json.loads((S/'source-coordinates.json').read_text()):
  b=z.read('the_artifact/'+row['artifact_path'])
  require(sha(b)==row['source_sha256'],'source coordinate file hash')
  line=b.decode().splitlines()[row['definition_line']-1]
  tokens=re.findall(r"[A-Za-z_][A-Za-z_0-9']*",line)
  require(row['constant'].rsplit('.',1)[1] in tokens,'exact source declaration '+row['constant'])
expected={line.split('  ',1)[1].removeprefix('./'):line.split('  ',1)[0] for line in (S/'logs/post-hashes.stdout').read_text().splitlines()}
with tarfile.open(S/'completed-task-tree.tar.gz','r:gz') as t:
 members=t.getmembers()
 require(all(m.isfile() for m in members),'transport contains only regular files')
 got={m.name:sha(t.extractfile(m).read()) for m in members}
 require(got==expected,'captured task tree hashes')
 for row in a['file_manifest']:
  if row['path'].startswith('iris-itree/'):
   require(got[row['path'][11:]]==row['sha256'],'original source changed')
 for f in ['AuditCore.v','AuditHeapLang.v','AuditIslaris.v']:
  require(got[f]==sha((S/f).read_bytes()),f)
rows=json.loads((S/'actual-assumptions.json').read_text())['rows']
require(len(rows)==28,'25 results plus 3 explicit axioms')
summary=Counter()
for row in rows[3:]:
 group=[]
 for name in row['reported_axioms']:
  if name.endswith('bisimulation_is_eq'):group.append('B')
  elif name.endswith('Ax.eq_rect_eq'):group.append('U')
  elif name.endswith('AxChoice'):group.append('C')
  else:raise ValueError('unclassified reported axiom '+name)
 summary[','.join(sorted(group)) or 'closed']+=1
require(summary==Counter({'closed':6,'B':3,'B,U':12,'B,C,U':4}),'per-result assumptions')
trace=(S/'logs/recursive-coqchk.stderr').read_text()
require(trace.count('Modules were successfully checked')==1,'native checker success')
require(len(re.findall(r'^Checking library:',trace,re.M))==542,'recursive library count')
receipt=json.loads((S/'logs/recursive-coqchk.json').read_text())
require(receipt['exit_code']==0,'native checker exit')
require('-admit' not in receipt['argv'] and '-norec' not in receipt['argv'],'no checking bypass')
require(sha(trace.encode())==receipt['stderr_sha256'],'native checker trace hash')
for category in ['type-in-type','unsafe (co)fixpoints','positivity']:
 require(any(category in line and '<none>' in line for line in trace.splitlines()),category)
context=json.loads((S/'kernel-context.json').read_text())
require(len(context['axiom_or_primitive_declarations'])==62,'global context declaration count')
meta=json.loads((P/'REPORT.json').read_text())
require(set(meta)=={'topics','subjects','observed_at'},'REPORT metadata shape')
for subject in meta['subjects']:
 require(set(subject)=={'name','identity'},'subject shape')
require((P/'REPORT.md').read_text().count("Authored by an AI agent acting on joshlf's behalf.")==1,'authorship notice')
for target in re.findall(r'\]\(([^)]+)\)',(P/'REPORT.md').read_text()):
 if not target.startswith(('https://','http://')):require((P/target).is_file(),'missing local link '+target)
manifest=P/'package-manifest.json'
if manifest.exists():
 data=json.loads(manifest.read_text())
 for row in data['files']:
  b=(P/row['path']).read_bytes()
  require(len(b)==row['bytes'] and sha(b)==row['sha256'],'package manifest '+row['path'])
print(json.dumps({'status':'PASS','source_files':476,'captured_task_files':len(expected),'captured_vo_files':sum(n.endswith('.vo') for n in expected),'selected_result_constants':25,'assumption_groups':dict(summary),'recursively_checked_libraries':542,'meaning':'Preserved evidence integrity/reconciliation only; fresh Coq replay requires REPLAY.md.'},sort_keys=True))
