#!/usr/bin/env python3
"""Bounded macOS Lean server resource and cross-file sentinel probe."""
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

HERE = Path(__file__).resolve().parent
WORK = HERE / "work"
OUT = HERE.parent / "transcript.json"
LEAN = Path(os.environ["LEAN_BIN"]).resolve()
RSS_LIMIT = 3200 * 1024 * 1024
DISK_LIMIT = 30 * 1024 * 1024
PROCESS_LIMIT = 6
FREE_FLOOR = 30
MAX_SECONDS = 180
START = time.monotonic()
EVENTS = []
ENV = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(WORK))

def sha(data):
    if isinstance(data, Path): data = data.read_bytes()
    if isinstance(data, str): data = data.encode()
    return hashlib.sha256(data).hexdigest()

def log(kind, **kw):
    EVENTS.append(dict(seq=len(EVENTS), t_ms=round((time.monotonic()-START)*1000,1), kind=kind, **kw))

def command(argv, timeout=10, **kw):
    return subprocess.run(argv, capture_output=True, text=True, timeout=timeout, **kw)

def free_percent():
    p=command(["memory_pressure","-Q"])
    m=re.search(r"System-wide memory free percentage: (\d+)%",p.stdout)
    return int(m.group(1)) if m else None

def swap(): return command(["sysctl","vm.swapusage"]).stdout.strip()

def inventory():
    fs=[p for p in WORK.rglob("*") if p.is_file() and not p.is_symlink()]
    st=[p.stat() for p in fs]
    return dict(files=len(fs), unique_inodes=len({(s.st_dev,s.st_ino) for s in st}),
                logical_bytes=sum(s.st_size for s in st), blocks_bytes=sum(s.st_blocks*512 for s in st),
                suffixes={x:sum(p.suffix==x for p in fs) for x in [".lean",".olean",".ilean"]},
                temporary=[str(p.relative_to(WORK)) for p in fs if any(x in p.name.lower() for x in [".tmp",".temp","~"])])

def tree(root):
    p=command(["ps","-axo","pid=,ppid=,rss=,comm="],timeout=5)
    rows={}
    for line in p.stdout.splitlines():
        a=line.strip().split(maxsplit=3)
        if len(a)!=4: continue
        try: pid,ppid,rss=map(int,a[:3])
        except ValueError: continue
        rows[pid]=dict(pid=pid,ppid=ppid,rss_bytes=rss*1024,comm=a[3])
    found={root}
    while True:
        nxt=found|{pid for pid,r in rows.items() if r["ppid"] in found}
        if nxt==found:break
        found=nxt
    ps=[rows[x] for x in sorted(found) if x in rows]
    return dict(count=len(ps),summed_rss_bytes=sum(x["rss_bytes"] for x in ps),processes=ps)

def footprint(pid):
    try:
        p=command(["footprint","--pid",str(pid),"--noCategories","--format","bytes"],timeout=8)
        m=re.search(r"phys_footprint:\s*(\d+) B",p.stdout)
        return dict(pid=pid,rc=p.returncode,phys_footprint_bytes=int(m.group(1)) if m else None,raw=p.stdout,stderr=p.stderr)
    except Exception as e:return dict(pid=pid,error=repr(e))

def guard(pid,phase):
    t=tree(pid); i=inventory(); f=free_percent()
    reasons=[]
    if t["summed_rss_bytes"]>RSS_LIMIT:reasons.append("tree RSS limit")
    if t["count"]>PROCESS_LIMIT:reasons.append("process count limit")
    if i["blocks_bytes"]>DISK_LIMIT:reasons.append("disk allocation limit")
    if f is None or f<FREE_FLOOR:reasons.append("free memory floor or unavailable")
    if time.monotonic()-START>MAX_SECONDS:reasons.append("duration limit")
    log("guard",phase=phase,tree=t,inventory=i,free_percent=f,reasons=reasons)
    if reasons:raise RuntimeError("; ".join(reasons))
    return t,f

class Server:
    def __init__(self):
        self.p=subprocess.Popen([str(LEAN),"--server"],cwd=WORK,env=ENV,stdin=subprocess.PIPE,
                                stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0,start_new_session=True)
        self.buf=b"";self.nextid=10;self.diags={}
        self.send(dict(jsonrpc="2.0",id=1,method="initialize",params=dict(processId=os.getpid(),rootUri=WORK.as_uri(),capabilities={},initializationOptions={"hasWidgets":False})))
        self.until(1);self.send(dict(jsonrpc="2.0",method="initialized",params={}))
        log("server_start",pid=self.p.pid)
    def send(self,m):
        b=json.dumps(m,separators=(",",":")).encode(); self.p.stdin.write(b"Content-Length: "+str(len(b)).encode()+b"\r\n\r\n"+b);self.p.stdin.flush();log("client",message=m)
    def read(self,timeout=15):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            if b"\r\n\r\n" in self.buf:
                h,body=self.buf.split(b"\r\n\r\n",1)
                sizes=[int(x.split(b":",1)[1]) for x in h.split(b"\r\n") if x.lower().startswith(b"content-length:")]
                if sizes and len(body)>=sizes[0]:
                    raw,self.buf=body[:sizes[0]],body[sizes[0]:];m=json.loads(raw);log("server",message=m)
                    if m.get("method")=="textDocument/publishDiagnostics":self.diags[m["params"]["uri"]]=m["params"]
                    if m.get("method")=="client/registerCapability" and "id" in m:self.send(dict(jsonrpc="2.0",id=m["id"],result=None))
                    return m
            ready,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
            if ready:
                b=os.read(self.p.stdout.fileno(),65536)
                if not b:break
                self.buf+=b
        raise TimeoutError("server response")
    def until(self,rid):
        end=time.monotonic()+20
        while time.monotonic()<end:
            m=self.read(max(.1,end-time.monotonic()))
            if m.get("id")==rid:return m
        raise TimeoutError(f"request {rid}")
    def request(self,method,params):
        rid=self.nextid;self.nextid+=1;start=time.monotonic()
        self.send(dict(jsonrpc="2.0",id=rid,method=method,params=params));r=self.until(rid)
        log("latency",method=method,id=rid,elapsed_ms=round((time.monotonic()-start)*1000,1))
        return r
    def uri(self,n):return (WORK/f"Scratch{n}.lean").as_uri()
    def open(self,n,text):
        self.send(dict(jsonrpc="2.0",method="textDocument/didOpen",params={"textDocument":dict(uri=self.uri(n),languageId="lean",version=1,text=text)}))
        return self.request("textDocument/waitForDiagnostics",dict(uri=self.uri(n),version=1))
    def edit(self,n,text,version):
        self.send(dict(jsonrpc="2.0",method="textDocument/didChange",params={"textDocument":dict(uri=self.uri(n),version=version),"contentChanges":[dict(text=text)]}))
        return self.request("textDocument/waitForDiagnostics",dict(uri=self.uri(n),version=version))
    def goal(self,n):return self.request("$/lean/plainGoal",dict(textDocument=dict(uri=self.uri(n)),position=dict(line=2,character=8)))
    def close(self,n):self.send(dict(jsonrpc="2.0",method="textDocument/didClose",params={"textDocument":dict(uri=self.uri(n))}))
    def stop(self):
        if self.p.poll() is not None:return
        try:
            self.send(dict(jsonrpc="2.0",id=999,method="shutdown",params=None));self.until(999)
            self.send(dict(jsonrpc="2.0",method="exit"));self.p.wait(timeout=5)
        except Exception:pass
        finally:
            if self.p.poll() is None:os.killpg(self.p.pid,signal.SIGKILL);self.p.wait(timeout=5)
            log("server_stop",rc=self.p.returncode,stderr=self.p.stderr.read().decode(errors="replace"))

def source(n,roundno=0):
    return f"import Dep\ntheorem claim{n} : probe{n} = {7+2*n} := by\n  exact ?_\n-- edit {roundno}\n"

def check_goal(goal,n):
    s=json.dumps(goal,sort_keys=True)
    return f"probe{n} = {7+2*n}" in s and all(f"probe{k} = {7+2*k}" not in s for k in range(4) if k!=n)

def main():
    if WORK.exists():shutil.rmtree(WORK)
    WORK.mkdir()
    host=dict(memory_bytes=int(command(["sysctl","-n","hw.memsize"]).stdout.strip()),
              free_start=free_percent(),swap_start=swap(),df=command(["df","-Pk",str(WORK)]).stdout,
              filesystem=command(["diskutil","info","/System/Volumes/Data"]).stdout)
    log("setup",lean_version=command([str(LEAN),"--version"]).stdout.strip(),lean_sha256=sha(LEAN),host=host,
        limits=dict(rss_bytes=RSS_LIMIT,disk_bytes=DISK_LIMIT,processes=PROCESS_LIMIT,free_percent=FREE_FLOOR,seconds=MAX_SECONDS))
    if host["memory_bytes"]<8*1024**3 or host["free_start"] is None or host["free_start"]<40:
        for n in [1,2,4]:log("cell",workers=n,status="skipped",reason="start guard")
        return
    dep="\n".join(f"def probe{n} : Nat := {7+2*n}" for n in range(4))+"\n"
    (WORK/"Dep.lean").write_text(dep)
    c=command([str(LEAN),"-o",str(WORK/"Dep.olean"),str(WORK/"Dep.lean")],timeout=30,env=ENV,cwd=WORK)
    log("compile_import",source_sha256=sha(dep),rc=c.returncode,stdout=c.stdout,stderr=c.stderr,olean_sha256=sha(WORK/"Dep.olean") if (WORK/"Dep.olean").exists() else None,inventory=inventory())
    if c.returncode:raise RuntimeError("import compilation failed")
    server=None;opened=[];baseline=None;one=None;two=None
    try:
        server=Server()
        for workers in [1,2,4]:
            if workers==4:
                free=free_percent();tr=tree(server.p.pid)
                # Extrapolate the two added file workers using observed 1->2 delta.
                predicted=tr["summed_rss_bytes"]+2*max(0,two["summed_rss_bytes"]-one["summed_rss_bytes"]) if one and two else None
                allow=predicted is not None and predicted<RSS_LIMIT*0.8 and free is not None and free>=40
                log("four_worker_admission",free_percent=free,current=tr,predicted_rss_bytes=predicted,allowed=allow)
                if not allow:
                    log("cell",workers=4,status="skipped",reason="two-worker extrapolation or free-memory admission guard")
                    continue
            start=time.monotonic();checks=[]
            for n in range(len(opened),workers):
                txt=source(n);(WORK/f"Scratch{n}.lean").write_text(txt)
                wait=server.open(n,txt);opened.append(n);guard(server.p.pid,f"open-{n}")
                goal=server.goal(n);ok=check_goal(goal,n)
                checks.append(dict(stage="open",file=n,wait=wait,goal=goal,goal_ok=ok,diagnostics=server.diags.get(server.uri(n))))
                if not ok:raise RuntimeError(f"sentinel mismatch open {n}")
            if workers==1:one=tree(server.p.pid)
            if workers==2:two=tree(server.p.pid)
            stable=tree(server.p.pid)
            feet=[footprint(p["pid"]) for p in stable["processes"]]
            log("resource",workers=workers,phase="stable",tree=stable,footprints=feet,free_percent=free_percent(),inventory=inventory())
            for roundno in range(1,4):
                for n in (range(workers) if roundno%2 else reversed(range(workers))):
                    txt=source(n,roundno);wait=server.edit(n,txt,roundno+1);guard(server.p.pid,f"edit-{workers}-{roundno}-{n}")
                    goal=server.goal(n);ok=check_goal(goal,n)
                    checks.append(dict(stage="edit",round=roundno,file=n,source_sha256=sha(txt),wait=wait,goal=goal,goal_ok=ok,diagnostics=server.diags.get(server.uri(n))))
                    if not ok:raise RuntimeError(f"sentinel mismatch edit {n}")
                log("resource",workers=workers,phase=f"round-{roundno}",tree=tree(server.p.pid),free_percent=free_percent(),inventory=inventory())
            log("cell",workers=workers,status="completed",elapsed_ms=round((time.monotonic()-start)*1000,1),checks=checks)
        for n in reversed(opened):server.close(n)
        log("resource",phase="after_close",tree=tree(server.p.pid),free_percent=free_percent())
    finally:
        if server:server.stop();log("resource",phase="after_stop",tree=tree(server.p.pid),free_percent=free_percent())
    log("finished",swap_end=swap(),inventory=inventory())

try:main()
except Exception as exc:log("fatal",error=repr(exc));raise
finally:
    raw=json.dumps(EVENTS,indent=2)+"\n"
    raw=raw.replace(WORK.as_uri(),"$WORK_URI").replace(str(WORK),"$WORK").replace(str(LEAN),"$LEAN_BIN")
    OUT.write_text(raw)
