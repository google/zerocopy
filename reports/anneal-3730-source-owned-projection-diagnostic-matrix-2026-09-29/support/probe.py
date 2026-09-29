#!/usr/bin/env python3
"""Pinned rustc/Charon/Aeneas/Lean ranges and a separate source-owned edit model."""
import argparse,hashlib,json,os,pathlib,platform,re,select,shutil,subprocess,sys,time

HERE=pathlib.Path(__file__).resolve().parent;ART=HERE/'artifacts';RAW=HERE/'results.json'
TOOLS=pathlib.Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
RBIN=TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
RLIB=TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/lib'
RUSTC=RBIN/'rustc';CHARON=TOOLS/'bin/charon';AENEAS=TOOLS/'bin/aeneas'
BASE=TOOLS/'elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin';LEAN=BASE/'lean';LAKE=BASE/'lake'
AENEAS_PROJECT=TOOLS/'aeneas-release/backends/lean';AENEAS_LIB=AENEAS_PROJECT/'.lake/build/lib/lean/Aeneas.olean'

def sha(x):
    if isinstance(x,pathlib.Path):x=x.read_bytes()
    if isinstance(x,str):x=x.encode()
    return hashlib.sha256(x).hexdigest()
def norm(s,work):return s.replace(str(HERE),'$REPORT').replace(str(work),'$WORK').replace(str(TOOLS),'$LOCAL_TOOLS')
def env_base():
    e=dict(os.environ);e.update({'RUSTUP_HOME':str(TOOLS/'rustup'),'CARGO_HOME':str(TOOLS/'cargo'),
      'CHARON_TOOLCHAIN_IS_IN_PATH':'1','ELAN_TOOLCHAIN':'leanprover/lean4:v4.30.0-rc2',
      'LEAN_NUM_THREADS':'1','PATH':str(RBIN)+os.pathsep+str(TOOLS/'bin')+os.pathsep+e.get('PATH',''),
      'DYLD_LIBRARY_PATH':str(RLIB)+os.pathsep+str(RLIB/'rustlib/aarch64-apple-darwin/lib')})
    return e
def run(records,label,argv,cwd,work,env=None,timeout=35):
    t=time.monotonic();p=subprocess.run([str(x) for x in argv],cwd=cwd,env=env or env_base(),
        capture_output=True,text=True,timeout=timeout)
    rec={'label':label,'argv':[norm(str(x),work) for x in argv],'cwd':norm(str(cwd),work),
         'exit':p.returncode,'seconds':round(time.monotonic()-t,4),
         'stdout':norm(p.stdout,work),'stderr':norm(p.stderr,work)}
    records.append(rec);return rec
def inventory(root):
    return {str(p.relative_to(root)):{'sha256':sha(p),'bytes':p.stat().st_size}
            for p in sorted(root.rglob('*')) if p.is_file()}

def project(src):
    """Illustrative exact-byte `///| ` copier, not Anneal annotation syntax."""
    lines=src.encode().splitlines(keepends=True);groups=[];current=[];offset=0
    for line in lines:
        if line.startswith(b'///| '):current.append((offset+5,offset+len(line),line[5:]))
        elif current:groups.append(current);current=[]
        offset+=len(line)
    if current:groups.append(current)
    assert len(groups)==2 and [len(g) for g in groups]==[2,2]
    out=bytearray();maps=[]
    def add(s):out.extend(s.encode())
    def copy(g,obligation):
        for s,e,b in groups[g]:
            start=len(out);out.extend(b);maps.append({'source':[s,e],'generated':[start,len(out)],
                'owner':f'doc-{g}','obligation':obligation,'authority':'exact-copied-bytes'})
    add('import Source.Funs\nrun_cmd do IO.sleep 1000\n\n')
    add('theorem left : True := ');copy(0,'left');add('\n')
    add('theorem right : True := ');copy(0,'right');add('\n')
    add('theorem second : True := ');copy(1,'second')
    return {'text':out.decode(),'maps':maps,'source_sha256':sha(src),'text_sha256':sha(bytes(out))}
def within_map(p,needle,obligation):
    data=p['text'].encode();key=needle.encode();at=0
    while (at:=data.find(key,at))>=0:
        end=at+len(key)
        for m in p['maps']:
            if m['obligation']==obligation and m['generated'][0]<=at and end<=m['generated'][1]:
                return [at,end]
        at=end
    raise AssertionError((needle,obligation))
def apply(src,p,version,action):
    if action['version']!=version or action['source_sha256']!=sha(src) or action['projection_sha256']!=p['text_sha256']:
        return None,'stale-source-or-projection'
    changes={}
    for e in action['edits']:
        if e.get('version',version)!=version:return None,'mixed-generation'
        if e['uri']!='projection://source-proof':return None,'read-only-or-external-uri'
        gs,ge=e['range'];match=[m for m in p['maps'] if m['generated'][0]<=gs and ge<=m['generated'][1]
                     and (gs!=ge or m['generated'][0]<gs<m['generated'][1])]
        if len(match)!=1:return None,'no-exact-authored-segment'
        m=match[0];s=m['source'][0]+gs-m['generated'][0];z=s+ge-gs
        if src.encode()[s:z]!=p['text'].encode()[gs:ge]:return None,'byte-mismatch'
        key=(s,z);v=e['new'].encode()
        if key in changes and changes[key]!=v:return None,'conflicting-duplicate-origin'
        changes[key]=v
    spans=sorted((s,z,v) for (s,z),v in changes.items())
    if any(spans[i][1]>spans[i+1][0] for i in range(len(spans)-1)):
        return None,'overlap'
    b=src.encode()
    for s,z,v in reversed(spans):b=b[:s]+v+b[z:]
    return b.decode(),'applied'
def action(src,p,version,edits):return {'version':version,'source_sha256':sha(src),
                                        'projection_sha256':p['text_sha256'],'edits':edits}
def edit(span,new,uri='projection://source-proof',version=None):
    e={'uri':uri,'range':span,'new':new}
    if version is not None:e['version']=version
    return e
def coord(text,byte):
    b=text.encode();prefix=b[:byte].decode();last=prefix.rsplit('\n',1)[-1]
    line=prefix.count('\n');return {'line_zero':line,'byte_column':len(last.encode()),
            'scalar_column':len(last),'utf16_column':len(last.encode('utf-16-le'))//2}
def parse_json_lines(s):return [json.loads(x) for x in s.splitlines() if x.startswith('{')]

def lsp(path,env,work,source_on_disk,patch_action,source_projection):
    """Open projected Lean v1, request diagnostics, then delete owning Rust text in flight."""
    proc=subprocess.Popen([str(LEAN),'--server'],cwd=path.parent,env=env,
         stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    messages=[];buffer=b'';uri=path.as_uri();text=path.read_text();nextid=1
    def send(msg):
        raw=json.dumps(msg,ensure_ascii=False,separators=(',',':')).encode()
        proc.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw);proc.stdin.flush()
        messages.append({'direction':'client','message':msg})
    def receive(pred,timeout=18):
        nonlocal buffer
        deadline=time.monotonic()+timeout
        while time.monotonic()<deadline:
            while b'\r\n\r\n' in buffer:
                header,tail=buffer.split(b'\r\n\r\n',1)
                length=next((int(v.split(b':',1)[1]) for v in header.split(b'\r\n')
                            if v.lower().startswith(b'content-length:')),None)
                if length is None or len(tail)<length:break
                raw,buffer=tail[:length],tail[length:];msg=json.loads(raw)
                messages.append({'direction':'server','message':msg})
                if msg.get('method')=='client/registerCapability' and 'id' in msg:
                    send({'jsonrpc':'2.0','id':msg['id'],'result':None})
                if pred(msg):return msg
            ready,_,_=select.select([proc.stdout],[],[],min(.2,max(0,deadline-time.monotonic())))
            if ready:
                chunk=os.read(proc.stdout.fileno(),65536)
                if not chunk:break
                buffer+=chunk
        raise TimeoutError('Lean LSP response')
    def request(method,params):
        nonlocal nextid
        rid=nextid;nextid+=1;send({'jsonrpc':'2.0','id':rid,'method':method,'params':params})
        return receive(lambda msg:msg.get('id')==rid and 'method' not in msg)
    try:
        init=request('initialize',{'processId':os.getpid(),'rootUri':path.parent.as_uri(),
                      'capabilities':{},'initializationOptions':{'hasWidgets':False}})
        send({'jsonrpc':'2.0','method':'initialized','params':{}})
        send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{
             'uri':uri,'languageId':'lean','version':1,'text':text}}})
        wait_id=nextid;nextid+=1
        send({'jsonrpc':'2.0','id':wait_id,'method':'textDocument/waitForDiagnostics',
              'params':{'uri':uri,'version':1}})
        wait_sent_at=time.monotonic()
        # This deletion is a canonical Rust edit. The Lean server still owns v1 text.
        before=source_on_disk.read_text();deleted=before.replace('///|   /- 🦀 é -/ missingProof\n','',1)
        assert deleted!=before;source_on_disk.write_text(deleted)
        deleted_ms=round((time.monotonic()-wait_sent_at)*1000,2)
        stale_src,status=apply(deleted,source_projection,2,patch_action)
        assert stale_src is None and status=='stale-source-or-projection'
        settled=receive(lambda msg:msg.get('id')==wait_id and 'method' not in msg)
        settled_ms=round((time.monotonic()-wait_sent_at)*1000,2)
        assert deleted_ms<settled_ms
        # A v2 projected buffer is intentionally omitted: the authored owner was deleted.
        request('shutdown',None);send({'jsonrpc':'2.0','method':'exit'});proc.wait(timeout=3)
        return {'initialize':init,'settled':settled,'messages':messages,
                'source_hash_before':sha(before),'source_hash_after':sha(deleted),
                'patch_rejection':status,'old_version':1,'new_source_version':2,
                'source_deleted_ms_after_request':deleted_ms,
                'server_settled_ms_after_request':settled_ms,
                'server_exit':proc.returncode,'stderr':norm(proc.stderr.read().decode(errors='replace'),work)}
    finally:
        if proc.poll() is None:proc.kill();proc.wait()

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--work',type=pathlib.Path,required=True);a=ap.parse_args()
    work=a.work.resolve()
    if work.exists():raise SystemExit('choose absent owned --work path')
    if shutil.disk_usage(work.parent).free<15*(1<<30):raise SystemExit('15 GiB free-disk guard')
    work.mkdir(parents=True)
    if ART.exists():shutil.rmtree(ART)
    ART.mkdir();records=[];src=(HERE/'source.rs').read_text();env=env_base()
    source=HERE/'source.rs';rmeta=ART/'source.rmeta';llbc=ART/'source.llbc'
    rust=run(records,'rustc',[RUSTC,'--crate-type','lib','--edition','2021','--crate-name','source_owned_probe',
              '--emit','metadata','--error-format','json',source,'-o',rmeta],HERE,work,env)
    char=run(records,'charon',[CHARON,'rustc','--preset','aeneas','--dest-file',llbc,'--',source,
              '--crate-type','lib','--crate-name','source_owned_probe','--edition','2021'],HERE,work,env)
    assert rust['exit']==char['exit']==0
    bad_rust=ART/'rustc-error.rs';bad_rust.write_text(src.replace('x.wrapping_add(1)','"wrong"',1))
    rust_bad=run(records,'rustc-error',[RUSTC,'--crate-type','lib','--edition','2021','--crate-name','source_owned_probe',
              '--emit','metadata','--error-format','json',bad_rust,'-o',ART/'bad.rmeta'],HERE,work,env)
    assert rust_bad['exit']!=0
    rust_json=[json.loads(x) for x in rust_bad['stderr'].splitlines() if x.startswith('{')]
    primary=[s for d in rust_json for s in d.get('spans',[]) if s.get('is_primary')]
    assert primary
    ll=json.loads(llbc.read_text());assert ll['has_errors'] is False
    items=[]
    for x in ll['translated']['fun_decls']:
        if not x or not x['item_meta'].get('is_local'):continue
        m=x['item_meta'];items.append({'id':x['def_id'],'name':'::'.join(y['Ident'][0] for y in m['name'] if 'Ident' in y),
                       'span':m['span']['data'],'source_text':m.get('source_text'),
                       'generated_from_span':m.get('generated_from_span')})
    assert {x['name'].split('::')[-1] for x in items}=={'step','select','macro_generated'}
    model=ART/'aeneas';model.mkdir()
    aen=run(records,'aeneas',[AENEAS,'-backend','lean','-no-progress-bar','-sequential',
           '-split-files','-gen-lib-entry','-dest',model,llbc],HERE,work,env)
    assert aen['exit']==0 and (model/'Funs.lean').exists()
    funs=(model/'Funs.lean').read_text();candidates=[]
    for x in items:
        name=x['name'].split('::')[-1]
        candidates.append({'rust_item':x['name'],'llbc_id':x['id'],
          'funs_comment_lines':[i for i,line in enumerate(funs.splitlines(),1) if f'[{x["name"]}]' in line],
          'funs_decl_lines':[i for i,line in enumerate(funs.splitlines(),1) if re.match(r'^def '+re.escape(name)+r'\b',line)],
          'evidence':'lexical printed name/comment only','editable':False})
    assert all(x['funs_comment_lines'] and x['funs_decl_lines'] for x in candidates)
    path_cmd=run(records,'aeneas-lean-path',[LAKE,'env','printenv','LEAN_PATH'],AENEAS_PROJECT,work,env)
    assert path_cmd['exit']==0
    resolved_lean_path=path_cmd['stdout'].replace('$LOCAL_TOOLS',str(TOOLS)).replace('$REPORT',str(HERE)).replace('$WORK',str(work)).strip()
    lean_env=dict(env,LEAN_PATH=resolved_lean_path+os.pathsep+str(ART/'compiled'))
    compiled=ART/'compiled/Source';compiled.mkdir(parents=True)
    for name in ('Types','Funs'):
        shutil.copyfile(model/(name+'.lean'),compiled/(name+'.lean'))
        z=run(records,'lean-compile-'+name,[LEAN,'-o',compiled/(name+'.olean'),compiled/(name+'.lean')],
              ART,work,lean_env,timeout=45)
        assert z['exit']==0,z
    p=project(src);good=ART/'Proof-good.lean';good.write_text(p['text'])
    good_batch=run(records,'lean-good-batch',[LEAN,'--json',good],ART,work,lean_env);assert good_batch['exit']==0
    first=within_map(p,'trivial','left');second=within_map(p,'trivial','second')
    patch=action(src,p,1,[edit(first,'simp'),edit(second,'simp')])
    patched,status=apply(src,p,1,patch);assert status=='applied' and patched!=src
    patched_file=ART/'Proof-patched.lean';patched_file.write_text(project(patched)['text'])
    assert run(records,'lean-patched-batch',[LEAN,'--json',patched_file],ART,work,lean_env)['exit']==0
    checks={}
    def reject(name,base,proj,version,act,expected):
        n,reason=apply(base,proj,version,act);assert n is None and reason==expected,(name,reason)
        checks[name]=reason
    reject('generated-model-uri',src,p,1,action(src,p,1,[edit(first,'simp'),edit(first,'simp',uri='file:///Source/Funs.lean')]),'read-only-or-external-uri')
    reject('synthetic-header',src,p,1,action(src,p,1,[edit([0,6],'import')]),'no-exact-authored-segment')
    right=within_map(p,'trivial','right')
    reject('conflicting-duplicate',src,p,1,action(src,p,1,[edit(first,'simp'),edit(right,'aesop')]),'conflicting-duplicate-origin')
    reject('mixed-generation',src,p,1,action(src,p,1,[edit(first,'simp'),edit(second,'simp',version=2)]),'mixed-generation')
    reject('A-B-A-version',src,p,3,patch,'stale-source-or-projection')
    # Real Lean batch/live diagnostics against identical projected bytes.
    bad_src=src.replace('///|   /- 🦀 é -/ trivial','///|   /- 🦀 é -/ missingProof',1)
    bad_p=project(bad_src);bad_file=ART/'Proof-error.lean';bad_file.write_text(bad_p['text'])
    bad_batch=run(records,'lean-error-batch',[LEAN,'--json',bad_file],ART,work,lean_env)
    assert bad_batch['exit']!=0
    batch_msgs=parse_json_lines(bad_batch['stdout']);assert any('unknown tactic' in x.get('data','') for x in batch_msgs)
    bad_span=within_map(bad_p,'missingProof','left');position=coord(bad_p['text'],bad_span[0])
    assert position['utf16_column']>position['scalar_column'] and position['byte_column']>position['utf16_column']
    live_source=work/'source-active.rs';live_source.write_text(bad_src)
    correction=action(bad_src,bad_p,1,[edit(bad_span,'trivial')])
    live=lsp(bad_file,lean_env,work,live_source,correction,bad_p)
    published=[m['message'] for m in live['messages'] if m['direction']=='server' and m['message'].get('method')=='textDocument/publishDiagnostics']
    settled_nonempty=[m for m in published if m['params'].get('version')==1 and m['params'].get('diagnostics')]
    assert settled_nonempty
    live_all=settled_nonempty[-1]['params']['diagnostics']
    assert sorted(x['message'] for x in live_all)==sorted(x['data'] for x in batch_msgs)
    final_diag=[d for d in live_all if 'unknown tactic' in d.get('message','')]
    assert len(final_diag)==2 and any(d['range']['start']['character']==position['utf16_column']+1 for d in final_diag)
    assert any(x['pos']['line']==position['line_zero']+1 and x['pos']['column']==position['scalar_column']+1
               for x in batch_msgs if 'unknown tactic' in x.get('data',''))
    # Error in generated Aeneas source: preserve original Lean location, no Rust-edit license.
    generated_error=ART/'generated-error-Funs.lean'
    assert 'ok (core.num.U32.wrapping_add x 1#u32)' in funs
    generated_error.write_text(funs.replace('ok (core.num.U32.wrapping_add x 1#u32)','missingGeneratedModelName',1))
    model_error=run(records,'lean-generated-model-error',[LEAN,'--json',generated_error],ART,work,lean_env)
    assert model_error['exit']!=0
    # Distinct rustc and generated-model ranges are explanation-only for this edit model.
    matrix={'rustc_primary':primary,'charon_items':items,'aeneas_candidates':candidates,
            'projected_maps':p['maps'],'unicode_position':position,
            'batch_messages':batch_msgs,'live_settled_diagnostics':live_all,
            'live_final_unknown_tactic':final_diag,
            'generated_model_messages':parse_json_lines(model_error['stdout']),
            'edit_checks':checks,'patch_status':status,'patched_source_sha256':sha(patched),
            'deletion_while_query':{'old_server_version':live['old_version'],
              'new_source_version':live['new_source_version'],
              'old_source_sha256':live['source_hash_before'],'new_source_sha256':live['source_hash_after'],
              'source_deleted_ms_after_request':live['source_deleted_ms_after_request'],
              'server_settled_ms_after_request':live['server_settled_ms_after_request'],
              'stale_patch_rejection':live['patch_rejection']}}
    result={'environment':{'platform':platform.platform(),'python':sys.version,
            'rustc_sha256':sha(RUSTC),'charon_sha256':sha(CHARON),'aeneas_sha256':sha(AENEAS),
            'lean_sha256':sha(LEAN),'aeneas_lib_olean_sha256':sha(AENEAS_LIB)},
            'source_sha256':sha(source),'artifacts':inventory(ART),'records':records,'matrix':matrix,
            'lsp':live}
    RAW.write_text(json.dumps(result,indent=2,ensure_ascii=False,sort_keys=True)+'\n')
    print(json.dumps({'rustc_primary':len(primary),'charon_items':len(items),
           'aeneas_edges':len(candidates),'projection_segments':len(p['maps']),
           'patch_controls':len(checks),'batch_errors':len(batch_msgs),
           'lsp_error_rows':len(final_diag),'stale_rejected':live['patch_rejection']},sort_keys=True))

if __name__=='__main__':main()
