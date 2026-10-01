import json
import os
import re
import select
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path

root = Path(__file__).resolve().parent
version = sys.argv[1]
consumer = sys.argv[2] if len(sys.argv) > 2 else 'fresh-seeded'
cwd = (root / 'work' / version / consumer).resolve()
toolroot = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains')
binroot = toolroot / ('leanprover--lean4---v' + version) / 'bin'
cmd = [str(binroot/'lake'),'--keep-toolchain','--no-cache','serve']
env = os.environ.copy()
env.update(ELAN_TOOLCHAIN='leanprover/lean4:v'+version, PATH=str(binroot)+':'+env.get('PATH',''),
           LEAN_NUM_THREADS='1', LAKE_ARTIFACT_CACHE='false',
           LAKE_CACHE_DIR=str(root/'cache'/version), MATHLIB_NO_CACHE_ON_UPDATE='1',
           HOME=str(root/'home'))

def sample(pgid):
    mp = subprocess.check_output(['memory_pressure','-Q'], text=True)
    free = int(re.search(r'System-wide memory free percentage:\s*(\d+)%',mp).group(1))
    ps = subprocess.check_output(['ps','-axo','pgid=,rss='],text=True)
    rss = sum(int(a[1]) for line in ps.splitlines() if (a:=line.split()) and len(a)==2 and int(a[0])==pgid)
    return {'memory_pressure_free_pct':free,'disk_free_bytes':shutil.disk_usage(root).free,'rss_kib':rss}

admission = sample(-1)
if admission['memory_pressure_free_pct'] < 10 or admission['disk_free_bytes'] <= 10*1024**3:
    raise SystemExit('Admission gate failed: '+json.dumps(admission))
p = subprocess.Popen(cmd,cwd=cwd,env=env,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
t0=time.monotonic()
wire_in=[]; wire_out=bytearray(); stderr=bytearray(); samples=[]; abort=None
def send(obj):
    raw=json.dumps(obj,separators=(',',':')).encode()
    frame=b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw
    p.stdin.write(frame); p.stdin.flush(); wire_in.append(frame.decode())
def check():
    global abort
    s=sample(p.pid); s['seconds']=round(time.monotonic()-t0,3); samples.append(s)
    if s['rss_kib']*1024 >= 2*1024**3: abort='process-group RSS reached 2 GiB'
    elif s['memory_pressure_free_pct'] < 10: abort='memory_pressure free below 10%'
    elif s['disk_free_bytes'] <= 10*1024**3: abort='disk free at or below 10 GiB'
    if abort: os.killpg(p.pid,signal.SIGKILL)

uri=(cwd/'Generated.lean').as_uri()
send({'jsonrpc':'2.0','id':1,'method':'initialize','params':{'processId':None,'rootUri':cwd.as_uri(),'capabilities':{},'workspaceFolders':None}})
send({'jsonrpc':'2.0','method':'initialized','params':{}})
send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{'uri':uri,'languageId':'lean4','version':1,'text':(cwd/'Generated.lean').read_text()}}})
while time.monotonic()-t0 < 8 and p.poll() is None:
    check()
    if abort: break
    ready,_,_=select.select([p.stdout,p.stderr],[],[],0.25)
    for f in ready:
        chunk=os.read(f.fileno(),65536)
        if f is p.stdout: wire_out.extend(chunk)
        else: stderr.extend(chunk)
if p.poll() is None and not abort:
    send({'jsonrpc':'2.0','id':2,'method':'shutdown','params':None})
    send({'jsonrpc':'2.0','method':'exit','params':None})
    p.stdin.close()
    try: p.wait(timeout=3)
    except subprocess.TimeoutExpired:
        abort='server shutdown deadline'; os.killpg(p.pid,signal.SIGKILL); p.wait()
for f,b in ((p.stdout,wire_out),(p.stderr,stderr)):
    rest=f.read()
    if rest: b.extend(rest)
rec={'version':version,'cmd':cmd,'cwd':str(cwd),'env':{k:env[k] for k in ('ELAN_TOOLCHAIN','LEAN_NUM_THREADS','LAKE_ARTIFACT_CACHE','LAKE_CACHE_DIR','MATHLIB_NO_CACHE_ON_UPDATE','HOME')},'admission':admission,'samples':samples,'seconds':round(time.monotonic()-t0,3),'exit':p.returncode,'abort':abort,'wire_in':wire_in,'wire_out':wire_out.decode(errors='replace'),'stderr':stderr.decode(errors='replace')}
(root/('server-'+version+'-'+consumer+'.json')).write_text(json.dumps(rec,indent=2)+'\n')
print(version,'exit',p.returncode,'abort',abort,'seconds',rec['seconds'],'wire_bytes',len(wire_out),'stderr_bytes',len(stderr),'diagnostics',b'publishDiagnostics' in wire_out)
print(rec['stderr'][-600:])
if abort: sys.exit(1)
