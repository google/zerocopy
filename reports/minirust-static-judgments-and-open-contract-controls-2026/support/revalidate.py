"""Run only in an owned/disposable package; all outputs stay beside this file."""
from pathlib import Path
import hashlib,json,subprocess,sys
here=Path(__file__).resolve().parent;out=here/'runs';out.mkdir(exist_ok=True);rows=[]
def run(name,argv):
    r=subprocess.run(argv,capture_output=True,cwd=here,timeout=60)
    for key,data in [('stdout',r.stdout),('stderr',r.stderr)]:(out/(name+'.'+key)).write_bytes(data)
    rows.append({'name':name,'argv':argv,'exit':r.returncode})
    (out/'commands.json').write_text(json.dumps(rows,indent=2)+'\n')
    if r.returncode:raise SystemExit('Stopped after failure: '+name)
    return r.stdout.decode(),r.stderr.decode()
run('python-version',['python3','--version']);run('rust-version',['rustc','-vV'])
model=json.loads(run('owned-model',['python3','contract_model.py'])[0])
(out/'owned-model.json').write_text(json.dumps(model,indent=2)+'\n')
observations={}
for name,flags,expected_len in [('default',[],2),('flipped',['--cfg','feature_flip'],99)]:
    run(name+'-build',['rustc','--edition=2024','-C','opt-level=0','-C','panic=unwind',*flags,'open_contract.rs','--emit=link=runs/'+name+',mir=runs/'+name+'.mir'])
    stdout,stderr=run(name+'-run',['./runs/'+name])
    required=['family=3','instances=11,21','resolved_len='+str(expected_len),'macro_word=8',
      'temporary_drops=[10, 1, 2, 20]','pattern_drops=[30, 3, 40, 4, 50, 60]',
      'callback_retained=1,bytes=[9, 1, 2, 3, 8, 5]','panic_restored=true,retained=2',
      'capacity_overflow_preserves=true','pending_future_drops=1']
    if stdout.splitlines()!=required or 'owned expected callback panic' not in stderr:
        raise SystemExit('Unexpected control result; stop and inspect')
    observations[name]=stdout.splitlines()
result={'observations':observations,'same_source_configuration_pair':True,
 'expected_panic':'Both executions deliberately panic inside catch_unwind; default hook retained, exit0 and guard restoration checked.',
 'input_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in here.iterdir() if p.is_file()}}
(out/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'commands':len(rows),'configurations':2,'result':'runs/results.json'}))
