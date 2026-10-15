import json, pathlib, hashlib, subprocess, base64
root=pathlib.Path(__file__).resolve().parent
work=root.parents[2]
author=work/'execution/jasmin-execution-plan/machine-decode-proof-final'
source=(author/'MachineDecodeFinal2.lean').read_bytes()
assert hashlib.sha256(source).hexdigest()=='fe89f0f6f1bf36db7877a9848e9c68d81d8ed130c354a9f6f7e2c7dee6c96965'
artifact=(author/'MachineDecodeFinal2.olean').read_bytes()
assert len(artifact)==2470904 and hashlib.sha256(artifact).hexdigest()=='c8401aabc472b3a5c367a32b5248f7a5310957aeec8be745002ca99f6d49bcae'
(root/'MachineDecodeFinal2.lean').write_bytes(source)
freeze=json.loads((work/'execution/sail-runtime/integration-build-freeze.json').read_text())
payload={'source':base64.b64encode(source).decode(),'artifacts':freeze['artifacts']}
remote=r'''
import sys, json, pathlib, hashlib, base64, subprocess, time, resource, os, shutil
x=json.load(sys.stdin)
root=pathlib.Path('/home/opam/anneal-sail-output/machine-independent')
root.mkdir(exist_ok=False)
imports=pathlib.Path('/home/opam/anneal-sail-output/serial-build-integration')
lean=pathlib.Path('/home/opam/anneal-sail-tools/lean-4.29.0-linux_aarch64/bin/lean')
proof=pathlib.Path('/home/opam/anneal-sail-output/proof-development/check-05')
controls=pathlib.Path('/home/opam/anneal-sail-output/controls-parent-1')
author=pathlib.Path('/home/opam/anneal-sail-output/machine-decode-proof-final')
checks=[(lean,'e215cbe9eab0914b49761e9e486d388e2e701cf876d1079d1ba733c48edb2d7b',13824),
 (proof/'Proof.lean','f62057489d30152c39dcfab87c5b7ecbb43dd2e6bbe14d0368c4cbc832b6f2d4',3744),
 (proof/'Proof.olean','a37ef2b0d8f2ed3613a85ae666e89771464e2453df0929f9f80fb44397faa3bf',297080),
 (controls/'Controls.lean','7c9301d8c6080cd8cd1cf1a4ae356532b92de8378e416fd7ed48f35945d5635b',9930),
 (controls/'Controls.olean','b2fbb76b44f7eb0ad57ca724d959a62dc0ddd7594df0db0a4b26b129fe9aa0b7',254400),
 (author/'MachineDecodeFinal2.lean','fe89f0f6f1bf36db7877a9848e9c68d81d8ed130c354a9f6f7e2c7dee6c96965',4626),
 (author/'MachineDecodeFinal2.olean','c8401aabc472b3a5c367a32b5248f7a5310957aeec8be745002ca99f6d49bcae',2470904)]
byte=pathlib.Path('/home/opam/anneal-sail-output/byte-diagnostic-proof')
checks += [(byte/'ByteDiagnostic5.lean','5a71c58874e82df4788df8e1f9489567f70e38d14d8b6dde112dfd5f0ae16446',8161),(byte/'ByteDiagnostic5.olean','b0ace1a1595a984ae81b48d9c47b38c6769136597a529efaa8d13894375dc35e',1995952)]
if len(x['artifacts'])!=143:raise RuntimeError('import count mismatch')
checks += [(imports/q['path'],q['sha256'],q['bytes']) for q in x['artifacts']]
pre=[]
for p,h,n in checks:
 b=p.read_bytes();pre.append({'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'ok':len(b)==n and hashlib.sha256(b).hexdigest()==h})
 if not pre[-1]['ok']:
  (root/'preflight.json').write_text(json.dumps(pre,indent=2));raise RuntimeError('identity failure '+str(p))
for q in x['artifacts']:
 dst=root/'imports'/pathlib.Path(q['path']).relative_to('olean');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(imports/q['path'],dst)
 b=dst.read_bytes()
 if len(b)!=q['bytes'] or hashlib.sha256(b).hexdigest()!=q['sha256']:raise RuntimeError('copy identity failure')
for src in [proof/'Proof.lean',proof/'Proof.olean',controls/'Controls.lean',controls/'Controls.olean',byte/'ByteDiagnostic5.lean',byte/'ByteDiagnostic5.olean']:
 shutil.copyfile(src,root/src.name)
source=base64.b64decode(x['source'])
if source!=(author/'MachineDecodeFinal2.lean').read_bytes():raise RuntimeError('source copy mismatch')
(root/'MachineDecodeFinal2.lean').write_bytes(source)
(root/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
argv=['timeout','--signal=TERM','--kill-after=5','120',str(lean),'-j1','-M4500','--tstack=400000','-t0','-R',str(root),'-o',str(root/'MachineDecodeFinal2.olean'),str(root/'MachineDecodeFinal2.lean')]
env=dict(os.environ);env['LEAN_PATH']=str(root/'imports')+':'+str(root);env['LEAN_NUM_THREADS']='1'
started=time.monotonic()
with (root/'stdout').open('wb') as out,(root/'stderr').open('wb') as err:
 completed=subprocess.run(argv,cwd=root,env=env,stdout=out,stderr=err)
result={'argv':argv,'cwd':str(root),'lean_path':env['LEAN_PATH'],'lean_num_threads':env['LEAN_NUM_THREADS'],'status':completed.returncode,'seconds':time.monotonic()-started,'maxrss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'verified_originals':len(pre),'verified_import_copies':143,'files':{}}
for name in ['MachineDecodeFinal2.lean','MachineDecodeFinal2.olean','stdout','stderr','preflight.json','Proof.lean','Proof.olean','Controls.lean','Controls.olean','ByteDiagnostic5.lean','ByteDiagnostic5.olean']:
 p=root/name
 if p.is_file():
  b=p.read_bytes();result['files'][name]={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
result['matches_author_artifact']=result['files'].get('MachineDecodeFinal2.olean',{}).get('sha256')=='c8401aabc472b3a5c367a32b5248f7a5310957aeec8be745002ca99f6d49bcae'
(root/'result.json').write_text(json.dumps(result,indent=2)+'\n')
response={'result':result,'preflight':pre,'stdout':(root/'stdout').read_text(),'stderr':(root/'stderr').read_text()}
if (root/'MachineDecodeFinal2.olean').is_file():response['artifact_base64']=base64.b64encode((root/'MachineDecodeFinal2.olean').read_bytes()).decode()
print(json.dumps(response))
'''
proc=subprocess.run(['docker','exec','-i','0af066858d96349334304f51ea631ea4c2496694952ea17f7dca1b5e8ecf6715','python3','-c',remote],input=json.dumps(payload),text=True,capture_output=True)
(root/'driver.stdout').write_text(proc.stdout);(root/'driver.stderr').write_text(proc.stderr)
if proc.returncode:raise RuntimeError('driver failed '+str(proc.returncode)+' '+proc.stderr)
r=json.loads(proc.stdout)
for name in ['stdout','stderr']:(root/name).write_text(r[name])
for name in ['result','preflight']:(root/(name+'.json')).write_text(json.dumps(r[name],indent=2)+'\n')
if 'artifact_base64' in r:
 b=base64.b64decode(r['artifact_base64']);(root/'MachineDecodeFinal2.olean').write_bytes(b)
 assert hashlib.sha256(b).hexdigest()==r['result']['files']['MachineDecodeFinal2.olean']['sha256']
print(json.dumps(r['result'],indent=2))
