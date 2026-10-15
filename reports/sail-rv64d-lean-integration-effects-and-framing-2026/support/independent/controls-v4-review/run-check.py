from pathlib import Path
import subprocess, json, hashlib, sys

host = Path(__file__).resolve().parent
name = sys.argv[1]
assert name.endswith('.lean') and '/' not in name
source = (host / name).read_bytes()
expected = hashlib.sha256(source).hexdigest()
script = r'''
from pathlib import Path
import os, subprocess, time, resource, json, hashlib, shutil
root=Path('/home/opam/anneal-sail-output/independent-controls-v4')
name=NAME
source=bytes.fromhex(SOURCE_HEX)
assert hashlib.sha256(source).hexdigest()==EXPECTED_HASH
lean=Path('/home/opam/anneal-sail-tools/lean-4.29.0-linux_aarch64/bin/lean')
assert hashlib.sha256(lean.read_bytes()).hexdigest()=='e215cbe9eab0914b49761e9e486d388e2e701cf876d1079d1ba733c48edb2d7b'
if name=='Controls.lean':
    records=json.loads(Path('/home/opam/anneal-sail-output/serial-build-integration/results.json').read_text())
    complete=json.loads(Path('/home/opam/anneal-sail-output/serial-build-integration/complete.json').read_text())
    assert complete['status']==0 and complete['modules']==143 and len(records)==143
    for row in records:
        p=Path('/home/opam/anneal-sail-output/serial-build-integration/olean')/Path(*row['module'].split('.')).with_suffix('.olean')
        assert row['status']==0 and p.stat().st_size==row['olean_bytes'] and hashlib.sha256(p.read_bytes()).hexdigest()==row['olean_sha256']
    original=Path('/home/opam/anneal-sail-output/controls-parent-1')
    assert hashlib.sha256((original/'Controls.lean').read_bytes()).hexdigest()==EXPECTED_HASH
    assert hashlib.sha256((original/'Controls.olean').read_bytes()).hexdigest()=='b2fbb76b44f7eb0ad57ca724d959a62dc0ddd7594df0db0a4b26b129fe9aa0b7'
    root.mkdir()
    for f,h in [('Proof.lean','f62057489d30152c39dcfab87c5b7ecbb43dd2e6bbe14d0368c4cbc832b6f2d4'),('Proof.olean','a37ef2b0d8f2ed3613a85ae666e89771464e2453df0929f9f80fb44397faa3bf')]:
        p=Path('/home/opam/anneal-sail-output/independent-proof')/f
        assert hashlib.sha256(p.read_bytes()).hexdigest()==h
        shutil.copyfile(p,root/f)
    (root/'identity.json').write_text(json.dumps({'compiler_sha256':hashlib.sha256(lean.read_bytes()).hexdigest(),'verified_integration_modules':len(records),'proof_source_sha256':hashlib.sha256((root/'Proof.lean').read_bytes()).hexdigest(),'proof_olean_sha256':hashlib.sha256((root/'Proof.olean').read_bytes()).hexdigest()},indent=2)+'\n')
with (root/name).open('xb') as f:f.write(source)
stem=Path(name).stem
argv=['timeout','--signal=TERM','--kill-after=5','120',str(lean),'-j1','-M4500','--tstack=400000','-t0','-R',str(root),'-o',str(root/(stem+'.olean')),str(root/name)]
env=os.environ.copy();env['LEAN_PATH']='/home/opam/anneal-sail-output/serial-build-integration/olean:'+str(root);env['LEAN_NUM_THREADS']='1'
start=time.monotonic()
with (root/(stem+'.stdout')).open('xb') as so,(root/(stem+'.stderr')).open('xb') as se:
    result=subprocess.run(argv,cwd=root,env=env,stdout=so,stderr=se)
u=resource.getrusage(resource.RUSAGE_CHILDREN)
files={}
for f in [name,stem+'.olean',stem+'.stdout',stem+'.stderr']:
    p=root/f
    if p.exists():files[f]={'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
rec={'argv':argv,'cwd':str(root),'lean_path':env['LEAN_PATH'],'status':result.returncode,'seconds':time.monotonic()-start,'maxrss_kib':u.ru_maxrss,'user_seconds':u.ru_utime,'system_seconds':u.ru_stime,'files':files}
(root/(stem+'-check.json')).write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps({'result':rec,'stdout':(root/(stem+'.stdout')).read_text(),'stderr':(root/(stem+'.stderr')).read_text()}))
'''.replace('NAME', repr(name)).replace('SOURCE_HEX', repr(source.hex())).replace('EXPECTED_HASH', repr(expected))
argv = ['docker','exec','0af066858d96349334304f51ea631ea4c2496694952ea17f7dca1b5e8ecf6715','python3','-c',script]
r = subprocess.run(argv, capture_output=True, text=True)
(host / (Path(name).stem+'-native.json')).write_text(r.stdout)
(host / (Path(name).stem+'-docker.stderr')).write_text(r.stderr)
print('docker_status',r.returncode,'source_sha256',expected)
if r.returncode == 0:
    d=json.loads(r.stdout)
    print(json.dumps(d['result'],indent=2))
    lines=d['stdout'].splitlines()
    for i,line in enumerate(lines):
        if ': error:' in line:print('\n'.join(lines[i:i+14]))
    if d['stderr']:print(d['stderr'])
else:
    print(r.stderr)
