#!/usr/bin/env python3
"""Direct Lean LSP plus hash-polling build loop; no editor integration."""
import argparse,hashlib,json,os,select,shutil,signal,subprocess,time
from pathlib import Path

HERE=Path(__file__).resolve().parent;LEAN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
RUSTFMT=Path('/opt/homebrew/bin/rustfmt');OUT=HERE/'results.json';ART=HERE/'artifacts'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def htext(s):return hashlib.sha256(s.encode()).hexdigest()
def source(tactic,blank=False):return f'theorem demo (n : Nat) : n + 0 = n := by\n  {tactic}\n'+('\n' if blank else '')
def pointer(work):
    p=work/'CURRENT_ARTIFACT.json'
    if not p.exists():return None
    x=json.loads(p.read_text());root=work/'builds'/x['generation']
    assert sha(root/'Generated.olean')==x['olean_sha256']
    assert sha(root/'Generated.ilean')==x['ilean_sha256']
    return x

class PollBuilder:
    def __init__(self,work):self.work=work;self.last_seen=None;self.pending_cancel=False;self.count=0;self.events=[]
    def scan(self,label,cancel=False):
        source_file=self.work/'Generated.lean';digest=sha(source_file);before=pointer(self.work)
        if digest==self.last_seen and not self.pending_cancel:
            row={'label':label,'event':'duplicate_suppressed','source_sha256':digest,'consumed':before}
            self.events.append(row);return row
        self.count+=1;name=f'b{self.count:02d}-{label}';stage=self.work/'builds'/name;stage.mkdir(parents=True)
        command=[str(LEAN),'-o',str(stage/'Generated.olean'),'-i',str(stage/'Generated.ilean'),str(source_file)]
        env=dict(os.environ,LEAN_PATH=str(self.work),LEAN_NUM_THREADS='1')
        if cancel:
            p=subprocess.Popen(command,cwd=self.work,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,start_new_session=True)
            os.killpg(p.pid,signal.SIGSTOP);os.killpg(p.pid,signal.SIGKILL)
            stdout,stderr=p.communicate(timeout=5)
            status={'exit':p.returncode,'stdout':stdout,'stderr':stderr,'cancelled':True}
            assert p.returncode==-9
            self.pending_cancel=True
        else:
            p=subprocess.run(command,cwd=self.work,env=env,capture_output=True,text=True,timeout=20)
            status={'exit':p.returncode,'stdout':p.stdout.replace(str(self.work),'$WORK'),
                    'stderr':p.stderr.replace(str(self.work),'$WORK'),'cancelled':False}
            self.last_seen=digest;self.pending_cancel=False
        after=before
        if status['exit']==0 and all((stage/n).exists() for n in ('Generated.olean','Generated.ilean')):
            after={'generation':name,'source_sha256':digest,'olean_sha256':sha(stage/'Generated.olean'),
                   'ilean_sha256':sha(stage/'Generated.ilean')}
            tmp=self.work/'CURRENT_ARTIFACT.tmp';tmp.write_text(json.dumps(after,sort_keys=True)+'\n');os.replace(tmp,self.work/'CURRENT_ARTIFACT.json')
        row={'label':label,'event':'build' if not cancel else 'cancelled_build','source_sha256':digest,
             'status':status,'stage_files':{p.name:sha(p) for p in stage.iterdir() if p.is_file()},
             'consumed_before':before,'consumed_after':after}
        self.events.append(row);return row

class Lsp:
    def __init__(self,work):
        self.work=work;self.file=work/'Generated.lean';self.uri=self.file.as_uri();self.events=[];self.buf=b'';self.started=time.monotonic()
        self.p=subprocess.Popen([str(LEAN),'--server'],cwd=work,env=dict(os.environ,LEAN_SERVER_LOG_DIR=str(work),LEAN_NUM_THREADS='1'),
                                stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
    def send(self,m):
        raw=json.dumps(m,separators=(',',':')).encode();self.p.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw);self.p.stdin.flush()
        self.events.append({'ms':round((time.monotonic()-self.started)*1000),'side':'client','message':m})
    def receive(self,pred,timeout=15):
        deadline=time.monotonic()+timeout
        while time.monotonic()<deadline:
            while b'\r\n\r\n' in self.buf:
                head,rest=self.buf.split(b'\r\n\r\n',1);length=None
                for line in head.split(b'\r\n'):
                    if line.lower().startswith(b'content-length:'):length=int(line.split(b':',1)[1])
                if length is None or len(rest)<length:break
                raw,self.buf=rest[:length],rest[length:];m=json.loads(raw)
                self.events.append({'ms':round((time.monotonic()-self.started)*1000),'side':'server','message':m})
                if m.get('method')=='client/registerCapability' and 'id' in m:self.send({'jsonrpc':'2.0','id':m['id'],'result':None})
                if pred(m):return m
            ready,_,_=select.select([self.p.stdout],[],[],max(0,deadline-time.monotonic()))
            if not ready:break
            chunk=os.read(self.p.stdout.fileno(),65536)
            if not chunk:break
            self.buf+=chunk
        raise TimeoutError('LSP response')
    def req(self,id_,method,params):
        self.send({'jsonrpc':'2.0','id':id_,'method':method,'params':params});return self.receive(lambda m:m.get('id')==id_)
    def wait(self,id_,version):return self.req(id_,'textDocument/waitForDiagnostics',{'uri':self.uri,'version':version})
    def latest_diag(self,version):
        pubs=[e['message']['params'] for e in self.events if e['side']=='server' and e['message'].get('method')=='textDocument/publishDiagnostics']
        matching=[p for p in pubs if p.get('uri')==self.uri and p.get('version')==version]
        return matching[-1]['diagnostics'] if matching else None
    def close(self):
        self.req(99,'shutdown',None);self.send({'jsonrpc':'2.0','method':'exit'})
        try:self.p.wait(timeout=3)
        except subprocess.TimeoutExpired:self.p.kill();self.p.wait(timeout=3)
        return {'exit':self.p.returncode,'stderr':self.p.stderr.read().decode(errors='replace')}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);args=ap.parse_args();work=args.work.resolve()
    assert not work.exists(),'choose absent owned work path'
    assert shutil.disk_usage(work.parent).free>=15*(1<<30),'15 GiB free-disk guard'
    work.mkdir();(work/'builds').mkdir();ART.mkdir(exist_ok=True)
    shutil.copyfile(HERE/'fixture/Generated.lean',work/'Generated.lean');shutil.copyfile(HERE/'fixture/Source.rs',work/'Source.rs')
    for p in ART.iterdir():
        if p.is_file():p.unlink()
    build=PollBuilder(work);observations=[]
    initial=build.scan('initial');assert initial['status']['exit']==0
    first=pointer(work);shutil.copyfile(work/'Generated.lean',ART/'v1-Generated.lean')
    shutil.copyfile(work/'builds'/first['generation']/'Generated.olean',ART/'v1-Generated.olean')
    lsp=Lsp(work)
    init=lsp.req(1,'initialize',{'processId':os.getpid(),'rootUri':work.as_uri(),'capabilities':{},
                                 'initializationOptions':{'hasWidgets':False,'logCfg':{'logDir':str(work)}}})
    lsp.send({'jsonrpc':'2.0','method':'initialized','params':{}})
    lsp.send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{'uri':lsp.uri,'languageId':'lean','version':1,'text':source('simp')}}})
    lsp.wait(2,1);d1=lsp.latest_diag(1)
    dirty=source('skip')
    lsp.send({'jsonrpc':'2.0','method':'textDocument/didChange','params':{'textDocument':{'uri':lsp.uri,'version':2},'contentChanges':[{'text':dirty}]}})
    lsp.wait(3,2);d2=lsp.latest_diag(2)
    assert sha(work/'Generated.lean')==first['source_sha256']
    no_disk=build.scan('dirty-buffer-poll');assert no_disk['event']=='duplicate_suppressed'
    observations.append({'step':'dirty_unsaved','lsp_version':2,'diagnostics':d2,'disk_source_sha256':sha(work/'Generated.lean'),
                         'consumed':pointer(work)})
    (work/'Generated.lean').write_text(dirty)
    saved=build.scan('save-invalid');assert saved['status']['exit']!=0 and pointer(work)==first
    duplicate=build.scan('duplicate-save-event');assert duplicate['event']=='duplicate_suppressed'
    observations.append({'step':'save_invalid','diagnostics':d2,'build_exit':saved['status']['exit'],'consumed':pointer(work)})
    external=source('exact Nat.add_zero n');(work/'Generated.lean').write_text(external)
    extbuild=build.scan('external-overwrite');assert extbuild['status']['exit']==0
    third=pointer(work);assert third['source_sha256']==sha(work/'Generated.lean')
    lsp.wait(4,2);still_d2=lsp.latest_diag(2)
    assert still_d2==d2
    observations.append({'step':'external_disk_while_open','lsp_open_version':2,'diagnostics':still_d2,
                         'disk_source_sha256':sha(work/'Generated.lean'),'consumed':third})
    lsp.send({'jsonrpc':'2.0','method':'textDocument/didClose','params':{'textDocument':{'uri':lsp.uri}}})
    lsp.send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{'uri':lsp.uri,'languageId':'lean','version':3,'text':external}}})
    lsp.wait(5,3);d3=lsp.latest_diag(3)
    observations.append({'step':'reopen_external','lsp_version':3,'diagnostics':d3,'consumed':pointer(work)})
    rust_before=sha(work/'Source.rs')
    fmt=subprocess.run([str(RUSTFMT),str(work/'Source.rs')],cwd=work,capture_output=True,text=True,timeout=20)
    assert fmt.returncode==0 and sha(work/'Source.rs')!=rust_before
    marker=next(line for line in (work/'Source.rs').read_text().splitlines() if line.startswith('// lean-proof:'))
    assert marker=='// lean-proof: simp'
    generated_from_marker=source(marker.split(':',1)[1].strip())
    assert generated_from_marker==source('simp')
    observations.append({'step':'rustfmt','rust_before_sha256':rust_before,'rust_after_sha256':sha(work/'Source.rs'),
                         'model_generated_sha256':htext(generated_from_marker),'lean_disk_unchanged':sha(work/'Generated.lean'),
                         'consumed':pointer(work),'rustfmt_exit':fmt.returncode})
    shutil.copyfile(work/'Source.rs',ART/'formatted-Source.rs')
    formatted=source('exact Nat.add_zero n',blank=True);(work/'Generated.lean').write_text(formatted)
    formbuild=build.scan('lean-format-edit');assert formbuild['status']['exit']==0
    lsp.send({'jsonrpc':'2.0','method':'textDocument/didChange','params':{'textDocument':{'uri':lsp.uri,'version':4},'contentChanges':[{'text':formatted}]}})
    lsp.wait(6,4);d4=lsp.latest_diag(4)
    observations.append({'step':'lean_format_edit','lsp_version':4,'diagnostics':d4,'consumed':pointer(work)})
    before_cancel=pointer(work);new=source('simp only [Nat.add_zero]');(work/'Generated.lean').write_text(new)
    cancelled=build.scan('cancelled-rebuild',cancel=True);assert pointer(work)==before_cancel
    retry=build.scan('retry-after-cancel');assert retry['status']['exit']==0 and pointer(work)!=before_cancel
    lsp.send({'jsonrpc':'2.0','method':'textDocument/didChange','params':{'textDocument':{'uri':lsp.uri,'version':5},'contentChanges':[{'text':new}]}})
    lsp.wait(7,5);d5=lsp.latest_diag(5)
    observations.append({'step':'cancel_retry','lsp_version':5,'diagnostics':d5,'cancel_exit':cancelled['status']['exit'],
                         'consumed_before':before_cancel,'consumed_after':pointer(work)})
    final=pointer(work);shutil.copyfile(work/'Generated.lean',ART/'final-Generated.lean')
    shutil.copyfile(work/'builds'/final['generation']/'Generated.olean',ART/'final-Generated.olean')
    lsp_end=lsp.close();assert lsp_end['exit']==0
    diag_versions={'v1':d1,'v2':d2,'v3':d3,'v4':d4,'v5':d5}
    result={'lean_sha256':sha(LEAN),'rustfmt_sha256':sha(RUSTFMT),
            'fixture_sha256':{'lean':sha(HERE/'fixture/Generated.lean'),'rust':sha(HERE/'fixture/Source.rs')},
            'initialize':init,'lsp_events':lsp.events,'lsp_exit':lsp_end,
            'watch_events':build.events,'observations':observations,'diagnostic_versions':diag_versions,'final':final,
            'artifact_sha256':{p.name:sha(p) for p in ART.iterdir() if p.is_file()}}
    OUT.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
    assert d1==[] and d2 and any(x.get('severity')==1 for x in d2),repr(diag_versions)
    assert d3==[] and d4==[] and d5==[],repr(diag_versions)
    print(json.dumps({'watch':[{'label':e['label'],'event':e['event'],'exit':e.get('status',{}).get('exit')} for e in build.events],
                      'diagnostic_counts':[len(x or []) for x in (d1,d2,d3,d4,d5)],'final':final},indent=2))
if __name__=='__main__':main()
