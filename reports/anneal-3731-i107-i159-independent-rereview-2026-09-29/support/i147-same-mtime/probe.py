#!/usr/bin/env python3
"""Sequential direct/Lake Lean server refresh matrix; tiny disposable fixtures."""
import hashlib
import json
import os
import re
import select
import shutil
import subprocess
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parent
WORK=ROOT/"work"
LEAN=Path(os.environ["LEAN_BIN"]).resolve()
LAKE=LEAN.with_name("lake")
TOOLCHAIN="leanprover/lean4:v4.30.0-rc2"
ENV=dict(os.environ,ELAN_TOOLCHAIN=TOOLCHAIN,LEAN_NUM_THREADS="1",LAKE_CACHE_DIR="",
         LAKE_ARTIFACT_CACHE="false",MATHLIB_NO_CACHE_ON_UPDATE="1")
ENV["PATH"]=str(LAKE.parent)+os.pathsep+ENV.get("PATH","")
PROOF="import Dep\n#eval selected\ntheorem checked : selected = 7 := by\n  rfl\ntheorem scratch : selected = 7 := by\n  exact ?_\n"
MISSING=PROOF.replace("import Dep","import Missing")
START=time.monotonic();EVENTS=[];SERVERS=[]
RSS_CAP=3*1024**3

def sha(x):
    if isinstance(x,Path):x=x.read_bytes()
    if isinstance(x,str):x=x.encode()
    return hashlib.sha256(x).hexdigest()
def log(kind,**kw):EVENTS.append(dict(seq=len(EVENTS),ms=round((time.monotonic()-START)*1000,1),kind=kind,**kw))
def command(label,args,cwd,env=None,timeout=20):
    t=time.monotonic()
    p=subprocess.run([str(a) for a in args],cwd=cwd,env=env or ENV,
                     capture_output=True,text=True,timeout=timeout)
    record=dict(label=label,args=[str(a) for a in args],cwd=str(cwd),rc=p.returncode,
                stdout=p.stdout,stderr=p.stderr,elapsed_ms=round((time.monotonic()-t)*1000,1))
    log("command",**record);return p
def tree(root):
    p=subprocess.run(["ps","-axo","pid=,ppid=,rss=,comm="],capture_output=True,text=True,timeout=4)
    rows={}
    for line in p.stdout.splitlines():
        xs=line.split(maxsplit=3)
        if len(xs)!=4:continue
        try:pid,ppid,rss=map(int,xs[:3])
        except ValueError:continue
        rows[pid]=dict(pid=pid,ppid=ppid,rss_bytes=rss*1024,comm=xs[3])
    seen={root}
    while True:
        add={pid for pid,row in rows.items() if row["ppid"] in seen}
        if add<=seen:break
        seen|=add
    found=[rows[pid] for pid in sorted(seen) if pid in rows]
    return dict(count=len(found),rss_bytes=sum(r["rss_bytes"] for r in found),processes=found)
def artifact(root):
    p=root/".lake/build/lib/lean/Dep.olean"
    h=p.with_name("Dep.olean.hash")
    return dict(sha256=sha(p) if p.exists() else None,
                bytes=p.stat().st_size if p.exists() else None,
                mtime_ns=p.stat().st_mtime_ns if p.exists() else None,
                hash_sidecar=h.read_text() if h.exists() else None)
def make(root):
    root.mkdir(parents=True,exist_ok=False)
    (root/"lakefile.lean").write_text("import Lake\nopen Lake DSL\npackage refresh_probe\n@[default_target]\nlean_lib Dep\n")
    (root/"lean-toolchain").write_text(TOOLCHAIN+"\n")
    (root/"Dep.lean").write_text("def selected : Nat := 7\n")
    (root/"Proof.lean").write_text(PROOF)
    (root/"New.lean").write_text(PROOF)
    (root/"Bad.lean").write_text(MISSING)
    p=command("initial-lake-build",[LAKE,"--keep-toolchain","--no-cache","build","Dep"],root)
    if p.returncode:raise RuntimeError("initial Lake build failed")
    log("fixture",root=str(root),source_sha256=sha(root/"Dep.lean"),
        proof_sha256=sha(PROOF),artifact=artifact(root))

class Server:
    def __init__(self,label,root,mode):
        self.label=label;self.root=root;self.mode=mode;self.buf=b"";self.n=10;self.diags={}
        env=dict(ENV)
        if mode=="direct":
            env["LEAN_PATH"]=str(root/".lake/build/lib/lean")
            argv=[str(LEAN),"--server"]
        elif mode=="lake-env":
            argv=[str(LAKE),"--keep-toolchain","--no-cache","env",str(LEAN),"--server"]
        else:
            argv=[str(LAKE),"--keep-toolchain","--no-cache","serve"]
        self.p=subprocess.Popen(argv,cwd=root,env=env,stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
        SERVERS.append(self)
        log("launch",label=label,mode=mode,argv=argv,pid=self.p.pid,root=str(root))
        self.send(dict(jsonrpc="2.0",id=1,method="initialize",params=dict(
            processId=os.getpid(),rootUri=root.as_uri(),capabilities={},
            initializationOptions={"hasWidgets":False})))
        self.until(1,15)
        self.send(dict(jsonrpc="2.0",method="initialized",params={}))
    def send(self,msg):
        raw=json.dumps(msg,separators=(",",":")).encode()
        self.p.stdin.write(b"Content-Length: "+str(len(raw)).encode()+b"\r\n\r\n"+raw)
        self.p.stdin.flush();log("client",label=self.label,message=msg)
    def read(self,timeout=10):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            if b"\r\n\r\n" in self.buf:
                header,body=self.buf.split(b"\r\n\r\n",1)
                lengths=[int(x.split(b":",1)[1]) for x in header.split(b"\r\n")
                         if x.lower().startswith(b"content-length:")]
                if lengths and len(body)>=lengths[0]:
                    raw,self.buf=body[:lengths[0]],body[lengths[0]:]
                    msg=json.loads(raw);log("server",label=self.label,message=msg)
                    if msg.get("method")=="textDocument/publishDiagnostics":
                        self.diags[msg["params"]["uri"]]=msg["params"]
                    if msg.get("method")=="client/registerCapability" and "id" in msg:
                        self.send(dict(jsonrpc="2.0",id=msg["id"],result=None))
                    return msg
            ready,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
            if ready:
                b=os.read(self.p.stdout.fileno(),65536)
                if not b:break
                self.buf+=b
        raise TimeoutError(f"{self.label}: read")
    def until(self,rid,timeout=10):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            msg=self.read(max(.1,end-time.monotonic()))
            if msg.get("id")==rid:return msg
        raise TimeoutError(f"{self.label}: request {rid}")
    def request(self,method,params,timeout=10):
        rid=self.n;self.n+=1;t=time.monotonic()
        self.send(dict(jsonrpc="2.0",id=rid,method=method,params=params))
        try:result=self.until(rid,timeout)
        except Exception as exc:result=dict(transport_error=repr(exc),id=rid)
        log("request_latency",label=self.label,method=method,rid=rid,
            elapsed_ms=round((time.monotonic()-t)*1000,1))
        return result
    def open(self,name,text=PROOF,version=1):
        uri=(self.root/name).as_uri()
        self.send(dict(jsonrpc="2.0",method="textDocument/didOpen",params={
            "textDocument":dict(uri=uri,languageId="lean",version=version,text=text)}))
        return self.request("textDocument/waitForDiagnostics",dict(uri=uri,version=version),12)
    def close(self,name):
        self.send(dict(jsonrpc="2.0",method="textDocument/didClose",params={
            "textDocument":dict(uri=(self.root/name).as_uri())}))
    def edit(self,name,text,version):
        uri=(self.root/name).as_uri()
        self.send(dict(jsonrpc="2.0",method="textDocument/didChange",params={
            "textDocument":dict(uri=uri,version=version),"contentChanges":[dict(text=text)]}))
        return self.request("textDocument/waitForDiagnostics",dict(uri=uri,version=version),12)
    def goal(self,name,line,col):
        return self.request("$/lean/plainGoal",dict(textDocument=dict(uri=(self.root/name).as_uri()),
            position=dict(line=line,character=col)))
    def watched(self,filename):
        self.send(dict(jsonrpc="2.0",method="workspace/didChangeWatchedFiles",params={
            "changes":[dict(uri=(self.root/filename).as_uri(),type=2)]}))
    def stop(self):
        if self.p.poll() is not None:return
        try:
            self.send(dict(jsonrpc="2.0",id=99,method="shutdown",params=None))
            self.until(99,5);self.send(dict(jsonrpc="2.0",method="exit"))
            self.p.wait(timeout=5)
        except Exception as exc:
            log("stop_error",label=self.label,error=repr(exc))
            if self.p.poll() is None:self.p.kill();self.p.wait()
        log("stop",label=self.label,rc=self.p.returncode,pid=self.p.pid,
            stderr=self.p.stderr.read().decode(errors="replace"))

def sample(s,phase,name="Proof.lean",wait=None):
    uri=(s.root/name).as_uri();before=tree(s.p.pid)
    if before["rss_bytes"]>RSS_CAP:raise MemoryError("server tree RSS cap")
    positions=[("rfl-start",3,2),("rfl-end",3,5),("exact-start",5,2),
               ("exact-inside",5,4),("exact-end",5,10),("eof",6,0)]
    goals={tag:s.goal(name,line,col) for tag,line,col in positions}
    diags=s.diags.get(uri)
    out=dict(label=s.label,phase=phase,name=name,wait=wait,goals=goals,
             diagnostics=diags,artifact=artifact(s.root),source_sha256=sha(s.root/"Dep.lean"),
             tree=before)
    log("sample",**out)
    return out

def session(mode,variant):
    q=subprocess.run(["memory_pressure","-Q"],capture_output=True,text=True,timeout=5)
    free=re.search(r"System-wide memory free percentage: (\d+)%",q.stdout)
    log("pressure_before_session",mode=mode,variant=variant,
        free_percent=int(free.group(1)) if free else None)
    if free is None or int(free.group(1))<25:raise RuntimeError("session free-memory floor")
    root=WORK/(mode+"-"+variant);make(root)
    label=mode+"-"+variant
    s=Server(label,root,mode)
    try:
        sample(s,"baseline",wait=s.open("Proof.lean"))
        if variant=="source":
            (root/"Dep.lean").write_text("def selected : Nat := 9\n")
            log("source_only_change",label=label,artifact=artifact(root),source_sha256=sha(root/"Dep.lean"))
            s.watched("Dep.lean")
        else:
            dst=root/".lake/build/lib/lean/Dep.olean"
            original=dst.stat()
            shutil.copy2(dst,ROOT/"baseline-Dep.olean")
            shutil.copy2(WORK/"prebuilt9"/"Dep.olean",dst)
            os.utime(dst,ns=(original.st_atime_ns,original.st_mtime_ns))
            assert dst.stat().st_mtime_ns==original.st_mtime_ns
            log("olean_only_change",label=label,artifact=artifact(root),source_sha256=sha(root/"Dep.lean"),original_mtime_ns=original.st_mtime_ns)
            s.watched(".lake/build/lib/lean/Dep.olean")
        sample(s,"old-open")
        sample(s,"new-open","New.lean",wait=s.open("New.lean"))
        sample(s,"old-after-new")
        s.close("Proof.lean")
        sample(s,"reopened","Proof.lean",wait=s.open("Proof.lean",PROOF,1))
        if variant=="olean":
            wrong=s.edit("Proof.lean",MISSING,2)
            sample(s,"missing-import","Proof.lean",wait=wrong)
    finally:s.stop()
    if variant=="olean":
        # Fresh watchdog over the artifact left by the first server.
        fresh=Server(label+"-fresh",root,mode)
        try:sample(fresh,"fresh-server",wait=fresh.open("Proof.lean",PROOF,1))
        finally:fresh.stop()
    # setup-file is a separate post-session control because it can rebuild imports.
    for name in (["Proof.lean"] if variant=="source" else ["Proof.lean","Bad.lean"]):
        before=artifact(root)
        p=command("setup-file-"+name,[LAKE,"--keep-toolchain","--no-cache","setup-file",name],root)
        log("setup_file",label=label,name=name,rc=p.returncode,
            before=before,after=artifact(root),stdout=p.stdout,stderr=p.stderr)
    if variant=="olean":
        # Proof.lean on disk still imports Dep, but this supplied unsaved header does not.
        missing_header={"imports":[{"module":"Missing","importAll":False,
            "isExported":True,"isMeta":False}],"isModule":False}
        before=artifact(root)
        p=command("setup-file-unsaved-header",[LAKE,"--keep-toolchain","--no-cache",
            "setup-file","Proof.lean",json.dumps(missing_header,separators=(",",":"))],root)
        log("setup_file_header_override",label=label,header=missing_header,rc=p.returncode,
            before=before,after=artifact(root),stdout=p.stdout,stderr=p.stderr)
        before=artifact(root)
        p=command("setup-file-rehash",[LAKE,"--keep-toolchain","--no-cache",
            "--rehash","setup-file","Proof.lean"],root)
        log("setup_file_rehash",label=label,rc=p.returncode,
            before=before,after=artifact(root),stdout=p.stdout,stderr=p.stderr)
    env=dict(ENV,LEAN_PATH=str(root/".lake/build/lib/lean"))
    p=command("batch-after",[LEAN,"--json","Proof.lean"],root,env)
    log("batch_after",label=label,rc=p.returncode,stdout=p.stdout,stderr=p.stderr,
        artifact=artifact(root),source_sha256=sha(root/"Dep.lean"))

def main():
    assert WORK.parent==ROOT and WORK.name=="work"
    if WORK.exists():shutil.rmtree(WORK)
    WORK.mkdir()
    ver=command("lean-version",[LEAN,"--version"],WORK)
    q=subprocess.run(["memory_pressure","-Q"],capture_output=True,text=True,timeout=5)
    free=re.search(r"System-wide memory free percentage: (\d+)%",q.stdout)
    log("subject",lean_version=ver.stdout.strip(),lean_sha256=sha(LEAN),lake_sha256=sha(LAKE),
        host_ram_bytes=int(subprocess.check_output(["sysctl","-n","hw.memsize"],text=True).strip()),
        free_percent=int(free.group(1)) if free else None,rss_cap_bytes=RSS_CAP,
        proof_sha256=sha(PROOF),missing_sha256=sha(MISSING))
    if free is None or int(free.group(1))<25:raise RuntimeError("host free-memory floor")
    for value in (7,9):
        root=WORK/f"prebuilt{value}";root.mkdir()
        source=f"def selected : Nat := {value}\n"
        (root/"Dep.lean").write_text(source)
        p=command(f"prebuild-{value}",[LEAN,"-o","Dep.olean","Dep.lean"],root)
        if p.returncode:raise RuntimeError("prebuild failed")
        log("prebuilt",value=value,source_sha256=sha(source),artifact_sha256=sha(root/"Dep.olean"))
    for mode in ("direct",):
        for variant in ("olean",):
            session(mode,variant)
    q=subprocess.run(["memory_pressure","-Q"],capture_output=True,text=True,timeout=5)
    free=re.search(r"System-wide memory free percentage: (\d+)%",q.stdout)
    log("pressure_end",free_percent=int(free.group(1)) if free else None,raw=q.stdout)
    log("completed")

try:main()
except Exception as exc:log("fatal",error=repr(exc));raise
finally:
    for s in SERVERS:
        if s.p.poll() is None:s.p.kill();s.p.wait();log("cleanup_kill",label=s.label,pid=s.p.pid)
    raw=json.dumps(EVENTS,indent=2)+"\n"
    raw=raw.replace(WORK.as_uri(),"$WORK_URI").replace(str(WORK),"$WORK")
    raw=raw.replace(str(LEAN),"$LEAN_BIN").replace(str(LAKE),"$LAKE_BIN")
    (ROOT/"transcript.json").write_text(raw)
