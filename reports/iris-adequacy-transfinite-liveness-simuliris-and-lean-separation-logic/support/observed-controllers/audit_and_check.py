"""Run only the three approved unchanged observation audits and recursive checker.
The cumulative wall-clock allocation of this driver is at most 1200 seconds.
"""
from pathlib import Path
import json,hashlib,subprocess,sys,time
r=Path(__file__).resolve().parent
for label in ['generic-corrected','tree-borrows-core','protected-and-unprotected-examples','sequential-read-reordering']:
 x=json.loads((r/'logs'/(label+'.json')).read_text())
 if x['exit_code']!=0:raise SystemExit('Not ready: '+label)
flags=json.loads((r/'audit-command-flags.json').read_text())['command_prefix']
if flags[-3:]!=['-Q','theories','simuliris'] or '-R' in flags:raise SystemExit('Mapping mismatch')
audits=['PlannedAuditFramework','PlannedAuditResources','PlannedAuditExamples']
for name in audits:
 if (r/(name+'.v')).read_bytes()!=(r.parent/'simuliris-plan'/(name+'.v')).read_bytes():raise SystemExit('Annotation bytes changed')
start=time.monotonic();outcomes=[]
def phase(label,command):
 remaining=int(1200-(time.monotonic()-start)-2)
 if remaining<=0:raise SystemExit('Cumulative audit/checker cap exhausted')
 p=subprocess.run([sys.executable,'-B',str(r/'run_selected.py'),'phase',label,str(remaining)]+command,cwd=r)
 outcomes.append({'label':label,'controller_exit':p.returncode,'remaining_seconds_at_start':remaining})
 (r/'audit-checker-driver-status.json').write_text(json.dumps({'allocation_seconds':1200,'elapsed_seconds':round(time.monotonic()-start,3),'outcomes':outcomes},indent=2)+'\n')
 if p.returncode:raise SystemExit('Stop: '+label)
for name in audits:phase('audit-'+name,flags+[name+'.v'])
seeds=['simuliris.simulation.adequacy','simuliris.tree_borrows.adequacy','simuliris.tree_borrows.examples.lib','simuliris.tree_borrows.examples.protected.mutable_reorder_write_up_activated_paper','simuliris.tree_borrows.examples.unprotected.shared_delete_read_escaped','simuliris.tree_borrows.read_read_reorder.read_reorder']
phase('recursive-native-checker',['rocq','check','-Q','theories','simuliris','-o','-m']+seeds+audits)
