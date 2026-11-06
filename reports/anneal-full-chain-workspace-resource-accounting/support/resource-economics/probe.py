#!/usr/bin/env python3
"""Bounded 1/2 Lake-consumer and direct-server resource probe on macOS."""
import hashlib
import json
import os
import re
import select
import shutil
import signal
import subprocess
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parent
WORK=ROOT/"work"
LEAN=Path(os.environ["LEAN_BIN"]).resolve()
LAKE=LEAN.with_name("lake")
TOOLCHAIN="leanprover/lean4:v4.30.0-rc2"
RSS_GUARD=4600*1024*1024
FREE_FLOOR=20
START=time.monotonic()
EVENTS=[]
ENV=dict(os.environ,ELAN_TOOLCHAIN=TOOLCHAIN,LEAN_NUM_THREADS="1",LAKE_CACHE_DIR="",
         LAKE_ARTIFACT_CACHE="false",MATHLIB_NO_CACHE_ON_UPDATE="1")
ENV["PATH"]=str(LAKE.parent)+os.pathsep+ENV.get("PATH","")

def sha(x):
    if isinstance(x,Path):x=x.read_bytes()
    if isinstance(x,str):x=x.encode()
    return hashlib.sha256(x).hexdigest()
def log(kind,**kw):EVENTS.append(dict(seq=len(EVENTS),ms=round((time.monotonic()-START)*1000,1),kind=kind,**kw))
def cmd(argv,**kw):return subprocess.run(argv,capture_output=True,text=True,timeout=kw.pop("timeout",10),**kw)
def pressure():
    p=cmd(["memory_pressure","-Q"])
    m=re.search(r"System-wide memory free percentage: (\d+)%",p.stdout)
    return dict(free_percent=int(m.group(1)) if m else None,raw=p.stdout,rc=p.returncode)
def swap():return cmd(["sysctl","vm.swapusage"]).stdout.strip()
def df():
    p=cmd(["df","-Pk",str(WORK)])
    parts=p.stdout.splitlines()[-1].split()
    return dict(raw=p.stdout,available_kib=int(parts[3]))
def inv(root):
    files=[];dirs=0;symlinks=[]
    if not root.exists():return dict(files=0,dirs=0,logical_bytes=0,blocks_bytes=0,unique_inodes=0,temp=[],symlinks=[])
    for p in root.rglob("*"):
        if p.is_symlink():symlinks.append(str(p.relative_to(root)));continue
        if p.is_dir():dirs+=1;continue
        if p.is_file():
            st=p.stat();files.append((p,st))
    return dict(files=len(files),dirs=dirs,logical_bytes=sum(st.st_size for _,st in files),
        blocks_bytes=sum(st.st_blocks*512 for _,st in files),
        unique_inodes=len({(st.st_dev,st.st_ino) for _,st in files}),
        temp=[str(p.relative_to(root)) for p,_ in files if any(t in p.name.lower() for t in (".tmp",".temp","~"))],
        symlinks=symlinks,
        classes={suffix:sum(1 for p,_ in files if p.suffix==suffix) for suffix in (".olean",".ilean",".trace",".c",".o")})
def ps_tree(roots):
    p=cmd(["ps","-axo","pid=,ppid=,rss=,comm="],timeout=4)
    rows={}
    for line in p.stdout.splitlines():
        xs=line.strip().split(maxsplit=3)
        if len(xs)!=4:continue
        try:pid,ppid,rss=map(int,xs[:3])
        except ValueError:continue
        rows[pid]=dict(pid=pid,ppid=ppid,rss_bytes=rss*1024,comm=xs[3])
    seen=set(roots)
    while True:
        more={pid for pid,row in rows.items() if row["ppid"] in seen}
        if more<=seen:break
        seen|=more
    found=[rows[pid] for pid in sorted(seen) if pid in rows]
    return dict(count=len(found),rss_bytes=sum(x["rss_bytes"] for x in found),processes=found)
def footprint(pid):
    try:
        p=cmd(["footprint","--pid",str(pid),"--noCategories","--format","bytes"],timeout=8)
        m=re.search(r"phys_footprint:\s*(\d+) B",p.stdout)
        return dict(pid=pid,rc=p.returncode,phys_footprint_bytes=int(m.group(1)) if m else None,
                    output=p.stdout,stderr=p.stderr)
    except Exception as exc:return dict(pid=pid,error=repr(exc))
def write_fixture(root,value):
    root.mkdir(parents=True,exist_ok=False)
    (root/"lakefile.lean").write_text("import Lake\nopen Lake DSL\npackage resource_probe\n@[default_target]\nlean_lib Generated\n")
    (root/"lean-toolchain").write_text(TOOLCHAIN+"\n")
    source=f"def selected : Nat := {value}\ntheorem claim : selected = {value} := by decide\n#eval selected\n"
    (root/"Generated.lean").write_text(source)
    scratch=f"import Generated\n#eval selected\ntheorem scratch : selected = {value} := by\n  exact ?_\n"
    (root/"Scratch.lean").write_text(scratch)
    return dict(root=str(root.relative_to(WORK)),value=value,source_sha256=sha(source),scratch_sha256=sha(scratch))

def group(label,roots):
    argv=[str(LAKE),"--keep-toolchain","--no-cache","build","Generated"]
    begins=time.monotonic();procs=[]
    for root in roots:
        p=subprocess.Popen(argv,cwd=root,env=ENV,stdout=subprocess.PIPE,stderr=subprocess.PIPE,
                           text=True,start_new_session=True)
        procs.append(p)
    peak=dict(count=0,rss_bytes=0,processes=[])
    disk_peak=0;disk_peak_files=0;temp_seen=set();samples=0;floor_seen=None;guard_polls=0
    footprint_sample=[];footprint_taken=False;aborted=None
    while any(p.poll() is None for p in procs):
        tree=ps_tree([p.pid for p in procs]);samples+=1
        if tree["rss_bytes"]>peak["rss_bytes"]:peak=tree
        bills=[inv(root) for root in roots]
        disk_peak=max(disk_peak,sum(b["blocks_bytes"] for b in bills))
        disk_peak_files=max(disk_peak_files,sum(b["files"] for b in bills))
        for b in bills:temp_seen.update(b["temp"])
        if not footprint_taken and tree["rss_bytes"]>1000*1024*1024:
            # One bounded sample, not a high-frequency monitor.
            footprint_sample=[footprint(x["pid"]) for x in tree["processes"]]
            footprint_taken=True
        if samples%5==0:
            q=pressure()
            if q["free_percent"] is not None:
                floor_seen=q["free_percent"] if floor_seen is None else min(floor_seen,q["free_percent"])
            guard_polls+=1
            if q["free_percent"] is not None and q["free_percent"]<FREE_FLOOR:
                aborted=f"memory free below {FREE_FLOOR}%"
        if tree["rss_bytes"]>RSS_GUARD:aborted=f"summed RSS above {RSS_GUARD}"
        if aborted:
            for p in procs:
                if p.poll() is None:os.killpg(p.pid,signal.SIGKILL)
            break
        time.sleep(.07)
    results=[]
    for root,p in zip(roots,procs):
        try:out,err=p.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(p.pid,signal.SIGKILL);out,err=p.communicate(timeout=5)
        results.append(dict(root=str(root.relative_to(WORK)),pid=p.pid,rc=p.returncode,
                            stdout=out,stderr=err,inventory=inv(root),
                            olean_sha256=sha(root/".lake/build/lib/lean/Generated.olean") if (root/".lake/build/lib/lean/Generated.olean").exists() else None))
    disk_peak=max(disk_peak,sum(r["inventory"]["blocks_bytes"] for r in results))
    disk_peak_files=max(disk_peak_files,sum(r["inventory"]["files"] for r in results))
    result=dict(label=label,consumers=len(roots),elapsed_ms=round((time.monotonic()-begins)*1000,1),
                peak=peak,peak_blocks_bytes=disk_peak,peak_files=disk_peak_files,
                temp_seen=sorted(temp_seen),samples=samples,guard_polls=guard_polls,
                min_free_percent_sampled=floor_seen,
                footprint_sample=footprint_sample,aborted=aborted,results=results)
    log("group",**result)
    if aborted:raise RuntimeError(aborted)
    return result

class Server:
    def __init__(self,label,root):
        self.label=label;self.root=root;self.buf=b"";self.n=10;self.last_diags=None
        e=dict(ENV,LEAN_PATH=str(root/".lake/build/lib/lean"))
        self.p=subprocess.Popen([str(LEAN),"--server"],cwd=root,env=e,stdin=subprocess.PIPE,
                                stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
        log("server_start",label=label,pid=self.p.pid)
        self.send(dict(jsonrpc="2.0",id=1,method="initialize",params=dict(processId=os.getpid(),
            rootUri=root.as_uri(),capabilities={},initializationOptions={"hasWidgets":False})))
        self.until(1);self.send(dict(jsonrpc="2.0",method="initialized",params={}))
    def send(self,msg):
        raw=json.dumps(msg,separators=(",",":")).encode()
        self.p.stdin.write(b"Content-Length: "+str(len(raw)).encode()+b"\r\n\r\n"+raw)
        self.p.stdin.flush();log("client",label=self.label,message=msg)
    def read(self,timeout=15):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            if b"\r\n\r\n" in self.buf:
                h,body=self.buf.split(b"\r\n\r\n",1)
                ls=[int(x.split(b":",1)[1]) for x in h.split(b"\r\n") if x.lower().startswith(b"content-length:")]
                if ls and len(body)>=ls[0]:
                    raw,self.buf=body[:ls[0]],body[ls[0]:]
                    msg=json.loads(raw);log("server",label=self.label,message=msg)
                    if msg.get("method")=="textDocument/publishDiagnostics":self.last_diags=msg["params"]
                    if msg.get("method")=="client/registerCapability" and "id" in msg:
                        self.send(dict(jsonrpc="2.0",id=msg["id"],result=None))
                    return msg
            ready,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
            if ready:
                b=os.read(self.p.stdout.fileno(),65536)
                if not b:break
                self.buf+=b
        raise TimeoutError(self.label)
    def until(self,rid):
        end=time.monotonic()+15
        while time.monotonic()<end:
            msg=self.read(max(.1,end-time.monotonic()))
            if msg.get("id")==rid:return msg
        raise TimeoutError(f"{self.label} {rid}")
    def request(self,method,params):
        rid=self.n;self.n+=1;t=time.monotonic()
        self.send(dict(jsonrpc="2.0",id=rid,method=method,params=params))
        result=self.until(rid)
        log("latency",label=self.label,method=method,rid=rid,ms_elapsed=round((time.monotonic()-t)*1000,1))
        return result
    def open(self,text,version=1):
        uri=(self.root/"Scratch.lean").as_uri();t=time.monotonic()
        self.send(dict(jsonrpc="2.0",method="textDocument/didOpen",params={"textDocument":dict(
            uri=uri,languageId="lean",version=version,text=text)}))
        wait=self.request("textDocument/waitForDiagnostics",dict(uri=uri,version=version))
        log("server_open",label=self.label,version=version,source_sha256=sha(text),
            elapsed_ms=round((time.monotonic()-t)*1000,1),wait=wait,diagnostics=self.last_diags)
    def change(self,text,version):
        uri=(self.root/"Scratch.lean").as_uri()
        self.send(dict(jsonrpc="2.0",method="textDocument/didChange",params={
            "textDocument":dict(uri=uri,version=version),"contentChanges":[dict(text=text)]}))
        return self.request("textDocument/waitForDiagnostics",dict(uri=uri,version=version))
    def goal(self):
        uri=(self.root/"Scratch.lean").as_uri()
        return self.request("$/lean/plainGoal",dict(textDocument=dict(uri=uri),
            position=dict(line=3,character=2)))
    def close(self):
        self.send(dict(jsonrpc="2.0",method="textDocument/didClose",params={
            "textDocument":dict(uri=(self.root/"Scratch.lean").as_uri())}))
    def stop(self):
        if self.p.poll() is not None:return
        try:
            self.send(dict(jsonrpc="2.0",id=99,method="shutdown",params=None));self.until(99)
            self.send(dict(jsonrpc="2.0",method="exit"));self.p.wait(timeout=5)
        finally:
            if self.p.poll() is None:self.p.kill();self.p.wait()
            log("server_stop",label=self.label,pid=self.p.pid,rc=self.p.returncode,
                stderr=self.p.stderr.read().decode(errors="replace"))

def server_soak(a,b):
    servers=[]
    try:
        for label,root,value in [("a",a,7),("b",b,9)]:
            s=Server(label,root);servers.append(s)
            text=(root/"Scratch.lean").read_text();s.open(text)
            goal=s.goal();log("sentinel",label=label,phase="initial",expected=value,goal=goal,
                diagnostics=s.last_diags)
        snapshot=ps_tree([s.p.pid for s in servers])
        feet=[footprint(x["pid"]) for x in snapshot["processes"]]
        log("server_resource",phase="initial",tree=snapshot,footprints=feet)
        for round_no in range(1,5):
            # Alternate order to expose accidental cross-workspace reuse.
            order=servers if round_no%2 else list(reversed(servers))
            for s in order:
                value=7 if s.label=="a" else 9
                source=(s.root/"Scratch.lean").read_text()
                edited=source.replace("exact ?_", "rfl" if round_no%2 else "exact ?_")
                wait=s.change(edited,round_no+1)
                goal=s.goal()
                log("soak",round=round_no,label=s.label,expected=value,
                    source_sha256=sha(edited),wait=wait,goal=goal,diagnostics=s.last_diags)
            log("server_resource",phase=f"edit-{round_no}",tree=ps_tree([s.p.pid for s in servers]))
        for s in reversed(servers):s.close()
        for s in reversed(servers):
            source=(s.root/"Scratch.lean").read_text();s.open(source,1)
            log("sentinel",label=s.label,phase="reopen",expected=7 if s.label=="a" else 9,
                goal=s.goal(),diagnostics=s.last_diags)
        snapshot=ps_tree([s.p.pid for s in servers])
        log("server_resource",phase="reopen",tree=snapshot,
            footprints=[footprint(x["pid"]) for x in snapshot["processes"]])
    finally:
        for s in servers:s.stop()
        log("server_resource",phase="after-stop",tree=ps_tree([s.p.pid for s in servers]))

def main():
    assert WORK.parent==ROOT and WORK.name=="work"
    if WORK.exists():shutil.rmtree(WORK)
    WORK.mkdir()
    host=dict(hw_mem_bytes=int(cmd(["sysctl","-n","hw.memsize"]).stdout.strip()),
              pressure_start=pressure(),swap_start=swap(),df_start=df(),
              filesystem=cmd(["diskutil","info","/System/Volumes/Data"]).stdout)
    log("subject",lean_version=cmd([str(LEAN),"--version"]).stdout.strip(),
        lean_sha256=sha(LEAN),lake_sha256=sha(LAKE),host=host,
        rss_guard_bytes=RSS_GUARD,free_floor_percent=FREE_FLOOR)
    if host["hw_mem_bytes"]<8*1024**3 or host["pressure_start"]["free_percent"]<30:
        raise RuntimeError("host did not meet conservative start guard")
    serial=[WORK/"serial-a",WORK/"serial-b"]
    parallel=[WORK/"parallel-a",WORK/"parallel-b"]
    for r,v in zip(serial+parallel,[7,9,7,9]):log("fixture",**write_fixture(r,v))
    group("cold-serial-a",[serial[0]])
    group("cold-serial-b",[serial[1]])
    group("cold-parallel-two",parallel)
    group("warm-parallel-two",parallel)
    # One proof-only rebuild and subsequent no-change warm call.
    for root in parallel:
        p=root/"Generated.lean";p.write_text(p.read_text().replace("by decide","by rfl"))
        log("proof_edit",root=str(root.relative_to(WORK)),sha256=sha(p))
    group("proof-edit-parallel-two",parallel)
    group("warm-after-edit-two",parallel)
    log("inventory",serial={r.name:inv(r) for r in serial},
        parallel={r.name:inv(r) for r in parallel})
    server_soak(parallel[0],parallel[1])
    log("host_end",pressure=pressure(),swap=swap(),df=df())
    log("completed")

try:main()
except Exception as exc:log("fatal",error=repr(exc));raise
finally:
    raw=json.dumps(EVENTS,indent=2)+"\n"
    raw=raw.replace(WORK.as_uri(),"$WORK_URI").replace(str(WORK),"$WORK")
    raw=raw.replace(str(LEAN),"$LEAN_BIN").replace(str(LAKE),"$LAKE_BIN")
    (ROOT/"transcript.json").write_text(raw)
