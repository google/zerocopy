#!/usr/bin/env python3
"""I061 local Rust comment-position adapter plus direct Lean LSP/RPC probes."""
import hashlib,json,os,select,signal,subprocess,time
from pathlib import Path

HERE=Path(__file__).resolve().parent;WORK=HERE/'work'
LEAN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
RUSTC=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin/rustc')
RUST='''pub fn inc(x: u32) -> u32 { x + 1 }
//%lean-begin
// def helper (n : Nat) : Nat := n + 1
// theorem demo (n : Nat) (h : n = 7) : (/- café 🦀 -/ helper n) = 8 := by
//   exact ?_
//%lean-end
'''
SCAFFOLD=['import Lean','']
TRANSCRIPT=[];T0=time.monotonic()
def write(p,s):p=Path(p);p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def log(kind,**kw):TRANSCRIPT.append({'seq':len(TRANSCRIPT),'ms':round((time.monotonic()-T0)*1000,1),'kind':kind,**kw})
def utf16(s):return len(s.encode('utf-16-le'))//2
def loc_line_col(text,byte_offset):
    raw=text.encode();assert 0<=byte_offset<=len(raw)
    prefix=raw[:byte_offset].decode('utf-8') # reject offsets inside UTF-8 codepoints
    line=prefix.count('\n');col=len(prefix.rsplit('\n',1)[-1].encode())
    return line,col
def project(rust,byte_offset,mapping):
    line,col=loc_line_col(rust,byte_offset)
    if line not in mapping:return None
    lean_line=mapping[line];raw_line=rust.splitlines()[line].encode()
    if col<3 or not raw_line.startswith(b'// '):return None
    content=raw_line[3:col].decode('utf-8')
    return {'line':lean_line,'character':utf16(content)}
def reverse(rust,line,utf16_col,mapping):
    inverse={v:k for k,v in mapping.items()}
    if line not in inverse:return None
    rust_line=inverse[line];content=rust.splitlines()[rust_line][3:]
    cp=0
    for i in range(len(content)+1):
        if utf16(content[:i])==utf16_col:cp=i;break
    else:return None
    prefix='\n'.join(rust.splitlines()[:rust_line])
    line_start=len((prefix+'\n').encode()) if rust_line else 0
    offset=line_start+len(('// '+content[:cp]).encode())
    return {'rust_line':rust_line,'rust_byte_offset':offset,'opened_text':rust.encode()[offset:offset+32].decode(errors='replace')}
def fixture():
    WORK.mkdir(exist_ok=True);rust=WORK/'host.rs';lean=WORK/'Projected.lean'
    write(rust,RUST)
    lines=RUST.splitlines();assert lines[1]=='//%lean-begin' and lines[5]=='//%lean-end'
    mapping={i:len(SCAFFOLD)+(i-2) for i in (2,3,4)}
    generated='\n'.join(SCAFFOLD+[lines[i][3:] for i in (2,3,4)])+'\n'
    write(lean,generated)
    theorem=lines[3];needle='helper n) = 8';source_bytes=RUST.encode()
    # Locate the use, not the definition. The e-acute and crab precede it.
    rust_offset=source_bytes.index(needle.encode())
    helper_pos=project(RUST,rust_offset,mapping)
    goal_offset=source_bytes.index(b'exact ?_')+len(b'exact ')
    goal_pos=project(RUST,goal_offset,mapping)
    assert helper_pos=={'line':3,'character':utf16(theorem[3:theorem.index(needle)])}
    assert helper_pos['character']<len(theorem[3:theorem.index(needle)].encode())
    assert project(RUST,source_bytes.index(b'pub fn'),mapping) is None
    assert project(RUST,source_bytes.index(b'//%lean-begin'),mapping) is None
    assert reverse(RUST,0,0,mapping) is None
    return rust,lean,generated,mapping,rust_offset,helper_pos,goal_offset,goal_pos

class Server:
    def __init__(self,label):
        self.label=label;self.n=10;self.buf=b''
        self.p=subprocess.Popen([str(LEAN),'--server'],cwd=WORK,
          env=dict(os.environ,LEAN_NUM_THREADS='1'),stdin=subprocess.PIPE,
          stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0,start_new_session=True)
        log('start',server=label,pid=self.p.pid)
        self.send(dict(jsonrpc='2.0',id=1,method='initialize',params=dict(processId=os.getpid(),
          rootUri=WORK.as_uri(),capabilities={},initializationOptions={'hasWidgets':False})))
        self.until(1);self.send(dict(jsonrpc='2.0',method='initialized',params={}))
    def send(self,msg):
        raw=json.dumps(msg,separators=(',',':')).encode()
        self.p.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw)
        self.p.stdin.flush();log('client',server=self.label,message=msg)
    def read(self,timeout=15):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            if b'\r\n\r\n' in self.buf:
                header,body=self.buf.split(b'\r\n\r\n',1)
                sizes=[int(x.split(b':',1)[1]) for x in header.split(b'\r\n') if x.lower().startswith(b'content-length:')]
                if sizes and len(body)>=sizes[0]:
                    raw,self.buf=body[:sizes[0]],body[sizes[0]:]
                    msg=json.loads(raw);log('server',server=self.label,message=msg)
                    if msg.get('method')=='client/registerCapability' and 'id' in msg:
                        self.send(dict(jsonrpc='2.0',id=msg['id'],result=None))
                    return msg
            ready,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
            if ready:
                chunk=os.read(self.p.stdout.fileno(),65536)
                if not chunk:break
                self.buf+=chunk
        raise TimeoutError(f'{self.label} read')
    def until(self,rid,timeout=15):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            msg=self.read(max(.1,end-time.monotonic()))
            if msg.get('id')==rid:return msg
        raise TimeoutError(f'{self.label} id={rid}')
    def req(self,method,params,rid=None):
        if rid is None:rid=self.n;self.n+=1
        self.send(dict(jsonrpc='2.0',id=rid,method=method,params=params))
        return self.until(rid)
    def open(self,path,text,version=1):
        uri=path.as_uri();self.send(dict(jsonrpc='2.0',method='textDocument/didOpen',params={
          'textDocument':dict(uri=uri,languageId='lean',version=version,text=text)}))
        return self.req('textDocument/waitForDiagnostics',dict(uri=uri,version=version))
    def close(self,uri):self.send(dict(jsonrpc='2.0',method='textDocument/didClose',params=dict(textDocument=dict(uri=uri))))
    def goal(self,uri,pos):return self.req('$/lean/plainGoal',dict(textDocument=dict(uri=uri),position=pos))
    def connect(self,uri):return self.req('$/lean/rpc/connect',dict(uri=uri))
    def rich(self,uri,pos,sid):
        return self.req('$/lean/rpc/call',dict(textDocument=dict(uri=uri),position=pos,
          sessionId=sid,method='Lean.Widget.getInteractiveGoals',
          params=dict(textDocument=dict(uri=uri),position=pos)))
    def stop(self):
        try:
            self.req('shutdown',None,rid=999);self.send(dict(jsonrpc='2.0',method='exit'))
            self.p.wait(timeout=5)
        except Exception as exc:
            log('stop_error',server=self.label,error=repr(exc))
            if self.p.poll() is None:os.killpg(self.p.pid,signal.SIGKILL);self.p.wait(timeout=5)
        log('stop',server=self.label,pid=self.p.pid,rc=self.p.returncode,
            stderr=self.p.stderr.read().decode(errors='replace'))
def locations(result):
    value=result.get('result')
    if value is None:return []
    if isinstance(value,dict):return [value]
    if isinstance(value,list):return value
    return []
def target(loc):
    if 'targetUri' in loc:return loc['targetUri'],loc['targetSelectionRange']['start']
    return loc['uri'],loc['range']['start']
def run():
    assert LEAN.is_file() and RUSTC.is_file()
    rust,lean,text,mapping,use_offset,use_pos,goal_offset,goal_pos=fixture();uri=lean.as_uri()
    host_text=rust.read_text()
    rustc_argv=[str(RUSTC),'--crate-name','host_probe','--crate-type','lib',
      '--emit','metadata','-o',str(WORK/'host.rmeta'),str(rust)]
    rustc=subprocess.run(rustc_argv,cwd=WORK,capture_output=True,text=True,timeout=30)
    rustc_record={'argv':rustc_argv,'rc':rustc.returncode,'stdout':rustc.stdout,'stderr':rustc.stderr,
                  'rmeta_sha256':sha(WORK/'host.rmeta') if rustc.returncode==0 else None}
    assert rustc.returncode==0,rustc_record
    crab_offset=RUST.encode().index('🦀'.encode())
    try:project(RUST,crab_offset+1,mapping)
    except UnicodeDecodeError:unicode_interior_rejected=True
    else:unicode_interior_rejected=False
    assert unicode_interior_rejected
    theorem_content=RUST.splitlines()[3][3:]
    surrogate_interior=utf16(theorem_content[:theorem_content.index('🦀')])+1
    assert reverse(RUST,3,surrogate_interior,mapping) is None
    states={};s=Server('incarnation-1')
    try:
        wait=s.open(lean,text,1);goal=s.goal(uri,goal_pos)
        assert 'error' not in goal and 'h' in json.dumps(goal) and 'helper' in json.dumps(goal),goal
        connected=s.connect(uri);sid=connected['result']['sessionId']
        rich=s.rich(uri,goal_pos,sid)
        assert rich.get('result',{}).get('goals'),rich
        definition=s.req('textDocument/definition',dict(textDocument=dict(uri=uri),position=use_pos))
        references=s.req('textDocument/references',dict(textDocument=dict(uri=uri),position=use_pos,
          context=dict(includeDeclaration=True)))
        hover=s.req('textDocument/hover',dict(textDocument=dict(uri=uri),position=use_pos))
        defs=locations(definition);refs=locations(references)
        opened=[]
        for loc in defs+refs:
            dst,pos=target(loc)
            mapped=reverse(host_text,pos['line'],pos['character'],mapping) if dst==uri else None
            opened.append({'lean_uri':dst,'lean_position':pos,'rust_file_opened':str(rust),
                           'rust_source':mapped})
        states['initial']={'pid':s.p.pid,'wait':wait,'plain_goal':goal,'session_id':sid,
          'rich_goal':rich,'definition':definition,'references':references,'hover':hover,
          'opened_hyperlinks':opened}
        s.close(uri)
        # A closed-document session is locally fenced even if the server still
        # accepts the old RPC id. Preserve the component's actual response.
        after_close=s.rich(uri,goal_pos,sid)
        wait2=s.open(lean,text,1);goal2=s.goal(uri,goal_pos)
        sid2=s.connect(uri)['result']['sessionId'];rich2=s.rich(uri,goal_pos,sid2)
        states['reopen']={'pid':s.p.pid,'old_session_after_close':after_close,
          'wait':wait2,'plain_goal':goal2,'session_id':sid2,'rich_goal':rich2,
          'local_old_handle_accepted_for_routing':False}
    finally:s.stop()
    post=Server('incarnation-2')
    try:
        post.open(lean,text,1)
        # Before any new connect, try the prior worker's session ID.
        stale=post.rich(uri,goal_pos,sid2)
        goal3=post.goal(uri,goal_pos)
        sid3=post.connect(uri)['result']['sessionId'];rich3=post.rich(uri,goal_pos,sid3)
        states['restart']={'pid':post.p.pid,'old_worker_session_before_connect':stale,
          'plain_goal':goal3,'session_id':sid3,'rich_goal':rich3,
          'local_old_worker_handle_accepted_for_routing':False}
    finally:post.stop()
    assert states['initial']['pid']!=states['restart']['pid']
    assert states['reopen']['rich_goal'].get('result',{}).get('goals')
    assert states['restart']['rich_goal'].get('result',{}).get('goals')
    result={'schema':1,'observed_at_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
      'lean_sha256':sha(LEAN),'rustc_sha256':sha(RUSTC),'rustc':rustc_record,
      'rust_sha256':sha(rust),'projected_lean_sha256':sha(lean),
      'mapping':{'rust_line_to_lean_line':mapping,'rust_byte_range':{'start':use_offset,'end':use_offset+len(b'helper')},
         'projected_helper_position':use_pos,'goal_rust_byte_offset':goal_offset,'goal_position':goal_pos,
         'unicode_bytes_before_helper':len(RUST.splitlines()[3][3:][:RUST.splitlines()[3][3:].index('helper')].encode()),
         'unicode_utf16_before_helper':use_pos['character'],'scaffold_only_reverse':reverse(RUST,0,0,mapping),
         'ordinary_rust_forward':project(RUST,RUST.encode().index(b'pub fn'),mapping),
         'marker_forward':project(RUST,RUST.encode().index(b'//%lean-begin'),mapping),
         'invalid_utf8_interior_rejected':unicode_interior_rejected,
         'surrogate_half_reverse':reverse(RUST,3,surrogate_interior,mapping)},
      'states':states,'transcript':TRANSCRIPT,
      'host_kind':'local Python position adapter over Rust comments; no Anneal UI or extension'}
    write(HERE/'results.json',json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'ok':True,'definitions':len(defs),'references':len(refs),'opened':len(opened),
      'initial_goals':len(rich['result']['goals']),'restart_goals':len(rich3['result']['goals'])}))
if __name__=='__main__':run()
