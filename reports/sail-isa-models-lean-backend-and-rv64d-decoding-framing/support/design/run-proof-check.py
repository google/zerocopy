import sys,json,subprocess,hashlib
from pathlib import Path
hostroot=Path(__file__).resolve().parent
source=hostroot/sys.argv[1]
check=sys.argv[2];module=sys.argv[3]
assert check in [f'{n:02}' for n in range(1,7)]
assert module in ['Proof','Controls']
payload={'source':source.read_text(),'check':check,'module':module,'accepted_proof':sys.argv[4] if len(sys.argv)>4 else None}
remote=r'''
import json,sys,subprocess,time,resource,hashlib,os,shutil
from pathlib import Path
x=json.load(sys.stdin)
base=Path('/home/opam/anneal-sail-output/proof-development')
base.mkdir(exist_ok=True)
root=base/('check-'+x['check']);root.mkdir(exist_ok=False)
name=x['module'];src=root/(name+'.lean');src.write_text(x['source'])
if x['accepted_proof']:
 prior=base/x['accepted_proof']/'Proof.olean'
 shutil.copyfile(prior,root/'Proof.olean')
lean='/home/opam/anneal-sail-tools/lean-4.29.0-linux_aarch64/bin/lean'
argv=['timeout','--signal=TERM','--kill-after=5','120',lean,'-j1','-M4500','--tstack=400000','-R',str(root),'-o',str(root/(name+'.olean')),str(src)]
env=dict(os.environ);env['LEAN_PATH']='/home/opam/anneal-sail-output/serial-build-integration/olean:'+str(root)
start=time.monotonic()
with (root/'stdout').open('wb') as out,(root/'stderr').open('wb') as err:
 result=subprocess.run(argv,env=env,stdout=out,stderr=err)
res={'status':result.returncode,'seconds':time.monotonic()-start,'maxrss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'argv':argv,'lean_path':env['LEAN_PATH'],'files':{}}
for p in sorted(root.iterdir()):
 if p.is_file():
  b=p.read_bytes();res['files'][p.name]={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
(root/'result.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({'result':res,'stdout':(root/'stdout').read_text(),'stderr':(root/'stderr').read_text()}))
'''
result=subprocess.run(['docker','exec','-i','0af066858d96349334304f51ea631ea4c2496694952ea17f7dca1b5e8ecf6715','python3','-c',remote],input=json.dumps(payload),text=True,capture_output=True)
p=hostroot/('native-check-'+check+'.json')
p.write_text(result.stdout)
(hostroot/('native-check-'+check+'-driver.stderr')).write_text(result.stderr)
if result.returncode:print('driverfailed',result.returncode,result.stderr);sys.exit(result.returncode)
x=json.loads(result.stdout)
print(json.dumps(x['result'],indent=2))
print(x['stdout'][:6000]);print(x['stderr'])
