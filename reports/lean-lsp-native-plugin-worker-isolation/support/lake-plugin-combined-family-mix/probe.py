#!/usr/bin/env python3
"""Pinned, scratch-only Lake-discovered plugin/artifact mix probe."""
import hashlib, json, os, select, shutil, subprocess, time
from pathlib import Path

HERE=Path(__file__).resolve().parent
SCRATCH=Path('/Users/josh/Codex/Meta/Data/20260929-issue-3730-3731/r21-work')
BIN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
LAKE=BIN.with_name('lake')
ENV=dict(os.environ,ELAN_TOOLCHAIN='leanprover/lean4:v4.30.0-rc2',LEAN_NUM_THREADS='1',LAKE_ARTIFACT_CACHE='false',MATHLIB_NO_CACHE_ON_UPDATE='1')
ENV['PATH']=str(BIN.parent)+os.pathsep+ENV.get('PATH','')
LOG=[]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(kind,**kw):LOG.append(dict(kind=kind,**kw))
def run(label,argv,cwd,env=None,timeout=35):
    t=time.monotonic();p=subprocess.run([str(x) for x in argv],cwd=cwd,env=env or ENV,capture_output=True,text=True,timeout=timeout)
    row=dict(label=label,argv=[str(x) for x in argv],cwd=str(cwd),rc=p.returncode,seconds=round(time.monotonic()-t,3),stdout=p.stdout,stderr=p.stderr)
    rec('command',**row);return row
def make_pair(name,value,tag,options=False):
    root=SCRATCH/name;producer=root/'producer';consumer=root/'consumer';producer.mkdir(parents=True);consumer.mkdir()
    (producer/'lakefile.toml').write_text('name = "plugin_probe"\n[[lean_lib]]\nname = "Dep"\n[[lean_lib]]\nname = "Plugin"\n')
    (producer/'Dep.lean').write_text('import Lean\nsyntax "probe_tac" : tactic\nmacro_rules | `(tactic| probe_tac) => `(tactic| decide)\ndef selected : Nat := '+str(value)+'\n')
    (producer/'Plugin.lean').write_text('import Lean\ninitialize do\n  let p := (← IO.getEnv "PLUGIN_MARKER").getD ""\n  if !p.isEmpty then IO.FS.writeFile p "plugin-'+tag+'"\n')
    config='name = "probe_app"\n'
    if options:config+='leanOptions = [{name = "pp.universes", value = true}]\n'
    config+='plugins = ["@plugin_probe/+Plugin:dynlib"]\n[[require]]\nname = "plugin_probe"\npath = "../producer"\n'
    (consumer/'lakefile.toml').write_text(config)
    (consumer/'Proof.lean').write_text('import Dep\ntheorem checked : selected = '+str(value)+' := by\n  probe_tac\n#eval selected\n')
    for p in (producer,consumer):(p/'lean-toolchain').write_text('leanprover/lean4:v4.30.0-rc2\n')
    r=run('build-'+name,[LAKE,'--keep-toolchain','--no-cache','build','Dep','+Plugin:dynlib'],producer)
    if r['rc']!=0:raise RuntimeError(r)
    r=run('setup-'+name,[LAKE,'--keep-toolchain','--no-cache','setup-file','Proof.lean'],consumer)
    if r['rc']!=0:raise RuntimeError(r)
    return root
def paths(root):
    base=root/'producer/.lake/build'
    return {'olean':base/'lib/lean/Dep.olean','ilean':base/'lib/lean/Dep.ilean','c':base/'ir/Dep.c','plugin':base/'lib/lean/plugin__probe_Plugin.dylib','setup':root/'consumer/lakefile.toml','source':root/'producer/Dep.lean'}
def inventory(label,root):
    d={k:dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size) for k,p in paths(root).items()}
    rec('inventory',label=label,artifacts=d);return d
def server(label,root):
    consumer=root/'consumer';marker=root/'marker.txt';marker.unlink(missing_ok=True)
    env=dict(ENV,PLUGIN_MARKER=str(marker));argv=[str(LAKE),'--keep-toolchain','--no-cache','serve']
    p=subprocess.Popen(argv,cwd=consumer,env=env,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
    rec('server_start',label=label,argv=argv,pid=p.pid)
    buf=b'';messages=[];diags=[]
    def send(m):
        raw=json.dumps(m,separators=(',',':')).encode();p.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw);p.stdin.flush()
        rec('client',label=label,message=m)
    def read(timeout=20):
        nonlocal buf
        until=time.monotonic()+timeout
        while time.monotonic()<until:
            if b'\r\n\r\n' in buf:
                header,body=buf.split(b'\r\n\r\n',1)
                sizes=[int(x.split(b':',1)[1]) for x in header.split(b'\r\n') if x.lower().startswith(b'content-length:')]
                if sizes and len(body)>=sizes[0]:
                    raw,buf=body[:sizes[0]],body[sizes[0]:]
                    m=json.loads(raw);messages.append(m);rec('server',label=label,message=m)
                    if m.get('method')=='textDocument/publishDiagnostics':diags.append(m['params'])
                    if 'method' in m and 'id' in m:send(dict(jsonrpc='2.0',id=m['id'],result=None))
                    return m
            rd,_,_=select.select([p.stdout],[],[],min(.1,max(0,until-time.monotonic())))
            if rd:
                x=os.read(p.stdout.fileno(),65536)
                if not x:break
                buf+=x
        raise TimeoutError(label+' LSP read')
    def until_id(rid):
        for _ in range(100):
            m=read()
            if m.get('id')==rid and 'method' not in m:return m
        raise TimeoutError(str(rid))
    outcome={}
    try:
        send(dict(jsonrpc='2.0',id=1,method='initialize',params=dict(processId=os.getpid(),rootUri=consumer.as_uri(),capabilities={},initializationOptions={'hasWidgets':False})))
        outcome['initialize']=until_id(1)
        send(dict(jsonrpc='2.0',method='initialized',params={}))
        uri=(consumer/'Proof.lean').as_uri()
        send(dict(jsonrpc='2.0',method='textDocument/didOpen',params={'textDocument':dict(uri=uri,languageId='lean',version=1,text=(consumer/'Proof.lean').read_text())}))
        send(dict(jsonrpc='2.0',id=2,method='textDocument/waitForDiagnostics',params=dict(uri=uri,version=1)))
        outcome['wait']=until_id(2)
        send(dict(jsonrpc='2.0',id=3,method='$/lean/plainGoal',params=dict(textDocument=dict(uri=uri),position=dict(line=2,character=3))))
        outcome['goal']=until_id(3)
        outcome['marker']=marker.read_text() if marker.exists() else None
        outcome['diagnostics']=diags
    except Exception as e:outcome['error']=repr(e)
    finally:
        if p.poll() is None:
            try:
                send(dict(jsonrpc='2.0',id=99,method='shutdown',params=None));until_id(99);send(dict(jsonrpc='2.0',method='exit'));p.wait(timeout=5)
            except Exception:p.kill();p.wait()
        outcome['rc']=p.returncode;outcome['stderr']=p.stderr.read().decode(errors='replace')
        rec('server_outcome',label=label,**outcome)
    return outcome
def main():
    if SCRATCH.exists():shutil.rmtree(SCRATCH)
    SCRATCH.mkdir()
    rec('subject',lean_sha256=sha(BIN),lake_sha256=sha(LAKE),version=run('version',[BIN,'--version'],SCRATCH)['stdout'].strip(),uname=run('uname',['uname','-a'],SCRATCH)['stdout'].strip())
    v1=make_pair('v1',7,'v1');v2=make_pair('v2',9,'v2',True)
    inventory('v1',v1);inventory('v2',v2)
    for name,root in [('v1',v1),('v2',v2)]:
        r=run('batch-'+name,[LAKE,'--keep-toolchain','--no-cache','env',BIN,'Proof.lean'],root/'consumer')
        rec('batch_outcome',label=name,rc=r['rc'],stdout=r['stdout'])
        server(name,root)
    mix=SCRATCH/'mix';shutil.copytree(v1,mix);pm=paths(mix);pv2=paths(v2)
    # Keep v1 source, OLean and ILean; mix in independently valid v2 plugin,
    # native C family and v2 setup options. No artifact is byte-corrupted.
    for key in ('plugin','c'):shutil.copy2(pv2[key],pm[key])
    pm['setup'].write_text(pv2['setup'].read_text())
    inventory('mix-before',mix)
    r=run('setup-mix',[LAKE,'--keep-toolchain','--no-cache','setup-file','Proof.lean'],mix/'consumer')
    rec('setup_json',label='mix',parsed=json.loads(r['stdout']) if r['rc']==0 else None)
    inventory('mix-after-setup',mix)
    server('mix',mix)
    inventory('mix-after-server',mix)
    r=run('batch-mix',[LAKE,'--keep-toolchain','--no-cache','env',BIN,'Proof.lean'],mix/'consumer')
    rec('batch_outcome',label='mix',rc=r['rc'],stdout=r['stdout'])
    archive=HERE/'artifacts'
    if archive.exists():shutil.rmtree(archive)
    retained={}
    for label,root in [('v1',v1),('v2',v2),('mix',mix)]:
        target=archive/label;target.mkdir(parents=True)
        retained[label]={}
        for key,path in paths(root).items():
            dst=target/key;shutil.copy2(path,dst)
            retained[label][key]=dict(sha256=sha(dst),bytes=dst.stat().st_size)
        (target/'proof').write_bytes((root/'consumer/Proof.lean').read_bytes())
        retained[label]['proof']=dict(sha256=sha(target/'proof'),bytes=(target/'proof').stat().st_size)
    rec('retained',inventory=retained)
    (HERE/'transcript.json').write_text(json.dumps(LOG,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(events=len(LOG),transcript_sha256=sha(HERE/'transcript.json')),indent=2))
if __name__=='__main__':main()
