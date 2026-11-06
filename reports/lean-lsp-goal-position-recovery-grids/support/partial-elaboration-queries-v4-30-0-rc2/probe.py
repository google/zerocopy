#!/usr/bin/env python3
"""Direct batch/LSP partial-elaboration matrix for Lean 4.30.0-rc2."""
import hashlib
import json
import os
import select
import subprocess
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parent
WORK=ROOT/"work"
LEAN=Path(os.environ["LEAN_BIN"]).resolve()
T0=time.monotonic()
EVENTS=[]
PRE="import Lean\n\ntheorem before : True := by\n  trivial\n#print axioms before\n\n"
POST="\ntheorem after : True := by\n  trivial\n#print axioms after\n"
BODY={
    "unfinished":"theorem broken : True := by\n  exact ?_\n",
    "unknown_tactic":"theorem broken : True := by\n  tactic_that_does_not_exist\n",
    "heartbeat":"set_option maxHeartbeats 1 in\ntheorem broken (n : Nat) : n + 1 = n + 1 := by\n  omega\n",
    "syntax":"theorem broken : True := by\n  )\n",
}
SOURCES={k:PRE+v+POST for k,v in BODY.items()}
EDIT2=PRE+"theorem broken : False := by\n  tactic_that_does_not_exist\n"+POST

def sha(x):return hashlib.sha256(x if isinstance(x,bytes) else x.encode()).hexdigest()
def log(kind,**kw):EVENTS.append(dict(seq=len(EVENTS),ms=round((time.monotonic()-T0)*1000,1),kind=kind,**kw))
def pos(text,needle,occurrence=0,offset=2):
    matches=[(i,line) for i,line in enumerate(text.splitlines()) if needle in line]
    i,line=matches[occurrence]
    return dict(line=i,character=min(len(line),line.index(needle)+offset))

class Server:
    def __init__(self):
        self.buf=b"";self.n=10
        self.p=subprocess.Popen([str(LEAN),"--server"],cwd=WORK,
            env=dict(os.environ,LEAN_NUM_THREADS="1"),stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
        log("start",pid=self.p.pid)
        self.send(dict(jsonrpc="2.0",id=1,method="initialize",params=dict(
            processId=os.getpid(),rootUri=WORK.as_uri(),capabilities={},
            initializationOptions={"hasWidgets":False})))
        self.until(1)
        self.send(dict(jsonrpc="2.0",method="initialized",params={}))
    def send(self,msg):
        b=json.dumps(msg,separators=(",",":")).encode()
        self.p.stdin.write(b"Content-Length: "+str(len(b)).encode()+b"\r\n\r\n"+b)
        self.p.stdin.flush();log("client",message=msg)
    def read(self,timeout=15):
        deadline=time.monotonic()+timeout
        while time.monotonic()<deadline:
            if b"\r\n\r\n" in self.buf:
                header,body=self.buf.split(b"\r\n\r\n",1)
                sizes=[int(x.split(b":",1)[1]) for x in header.split(b"\r\n") if x.lower().startswith(b"content-length:")]
                if sizes and len(body)>=sizes[0]:
                    raw,self.buf=body[:sizes[0]],body[sizes[0]:]
                    msg=json.loads(raw);log("server",message=msg)
                    if msg.get("method")=="client/registerCapability" and "id" in msg:
                        self.send(dict(jsonrpc="2.0",id=msg["id"],result=None))
                    return msg
            ready,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,deadline-time.monotonic())))
            if ready:
                chunk=os.read(self.p.stdout.fileno(),65536)
                if not chunk:break
                self.buf+=chunk
        raise TimeoutError("server read")
    def until(self,rid,timeout=15):
        deadline=time.monotonic()+timeout
        while time.monotonic()<deadline:
            m=self.read(max(.1,deadline-time.monotonic()))
            if m.get("id")==rid:return m
        raise TimeoutError(f"request {rid}")
    def request(self,method,params):
        rid=self.n;self.n+=1
        t=time.monotonic();self.send(dict(jsonrpc="2.0",id=rid,method=method,params=params))
        response=self.until(rid)
        log("latency",rid=rid,method=method,elapsed_ms=round((time.monotonic()-t)*1000,1))
        return response
    def open(self,path,text,version=1):
        self.send(dict(jsonrpc="2.0",method="textDocument/didOpen",params={
            "textDocument":dict(uri=path.as_uri(),languageId="lean",version=version,text=text)}))
        return self.wait(path.as_uri(),version)
    def close(self,uri):
        self.send(dict(jsonrpc="2.0",method="textDocument/didClose",params={"textDocument":dict(uri=uri)}))
    def edit(self,uri,text,version):
        self.send(dict(jsonrpc="2.0",method="textDocument/didChange",params={
            "textDocument":dict(uri=uri,version=version),"contentChanges":[dict(text=text)]}))
    def wait(self,uri,version):
        return self.request("textDocument/waitForDiagnostics",dict(uri=uri,version=version))
    def goal(self,uri,position,version=None):
        doc=dict(uri=uri)
        if version is not None:doc["version"]=version
        return self.request("$/lean/plainGoal",dict(textDocument=doc,position=position))
    def stop(self):
        if self.p.poll() is not None:return
        try:
            self.send(dict(jsonrpc="2.0",id=99,method="shutdown",params=None));self.until(99,5)
            self.send(dict(jsonrpc="2.0",method="exit"));self.p.wait(timeout=5)
        finally:
            if self.p.poll() is None:self.p.kill();self.p.wait()
            log("stop",pid=self.p.pid,rc=self.p.returncode,stderr=self.p.stderr.read().decode(errors="replace"))

def run():
    WORK.mkdir(exist_ok=True)
    log("subject",lean_version=subprocess.check_output([str(LEAN),"--version"],text=True).strip(),
        binary_sha256=sha(LEAN.read_bytes()),source_sha256={k:sha(v) for k,v in SOURCES.items()},
        edit2_sha256=sha(EDIT2))
    for name,text in SOURCES.items():
        file=WORK/(name+".lean");file.write_text(text)
        t=time.monotonic()
        p=subprocess.run([str(LEAN),"--json",str(file)],cwd=WORK,capture_output=True,text=True,
            env=dict(os.environ,LEAN_NUM_THREADS="1"),timeout=20)
        log("batch",case=name,rc=p.returncode,stdout=p.stdout,stderr=p.stderr,
            wall_ms=round((time.monotonic()-t)*1000,1),source_sha256=sha(text))
    s=Server()
    try:
        for name,text in SOURCES.items():
            file=WORK/(name+".lean");uri=file.as_uri()
            wait=s.open(file,text)
            before=pos(text,"trivial",0)
            failed=pos(text,{"unfinished":"exact ?_","unknown_tactic":"tactic_that_does_not_exist",
                "heartbeat":"omega","syntax":")"}[name])
            after=pos(text,"trivial",1)
            samples={"before_start":s.goal(uri,dict(line=before["line"],character=2)),
                "before_inside":s.goal(uri,before),
                "before_end":s.goal(uri,dict(line=before["line"],character=len(text.splitlines()[before["line"]]))),
                "failure":s.goal(uri,failed),
                "after_start":s.goal(uri,dict(line=after["line"],character=2)),
                "after_inside":s.goal(uri,after),
                "after_end":s.goal(uri,dict(line=after["line"],character=len(text.splitlines()[after["line"]])))}
            # A request after the completed wait still sees diagnostics and goals as separate things.
            log("case",case=name,source_sha256=sha(text),wait=wait,
                positions=dict(before=before,failure=failed,after=after),samples=samples)
            s.close(uri)
        # Same URI and position, distinct failure text/goals; query before and after readiness.
        path=WORK/"Edit.lean";path.write_text(SOURCES["unfinished"])
        uri=path.as_uri();s.open(path,SOURCES["unfinished"])
        oldpos=pos(SOURCES["unfinished"],"exact ?_")
        oldgoal=s.goal(uri,oldpos)
        newpos=pos(EDIT2,"tactic_that_does_not_exist")
        s.edit(uri,EDIT2,2)
        immediate=s.goal(uri,newpos,version=1)
        ready=s.wait(uri,2)
        oldwait=s.wait(uri,1)
        late_v1=s.goal(uri,newpos,version=1)
        late_v2=s.goal(uri,newpos,version=2)
        log("edit_case",old=oldgoal,immediate=immediate,ready=ready,oldwait=oldwait,
            late_v1=late_v1,late_v2=late_v2,position=newpos,
            v1_sha256=sha(SOURCES["unfinished"]),v2_sha256=sha(EDIT2))
        s.close(uri)
        log("completed")
    finally:s.stop()

try:run()
except Exception as exc:
    log("fatal",error=repr(exc));raise
finally:
    raw=json.dumps(EVENTS,indent=2)+"\n"
    raw=raw.replace(WORK.as_uri(),"$WORK_URI").replace(str(WORK),"$WORK")
    raw=raw.replace(str(LEAN),"$LEAN_BIN")
    (ROOT/"transcript.json").write_text(raw)
