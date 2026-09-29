#!/usr/bin/env python3
"""Direct Lean LSP two-file rename, code actions, hints and completion fixture."""
import argparse,hashlib,json,os,select,shutil,subprocess,time
from pathlib import Path

HERE=Path(__file__).resolve().parent;FIX=HERE/'fixture';OUT=HERE/'transcript.json'
LEAN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
FILES={p.name:p.read_text() for p in FIX.glob('*.lean')}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def utf16(s):return len(s.encode('utf-16-le'))//2
def pos(text,line,needle,inside=0):
    prefix=text.splitlines()[line].split(needle,1)[0]
    return {'line':line,'character':utf16(prefix)+inside}
def offset(text,p):
    lines=text.splitlines(keepends=True);prefix=''.join(lines[:p['line']]);units=0
    for i,ch in enumerate(lines[p['line']]):
        if units==p['character']:return len(prefix)+i
        units+=2 if ord(ch)>0xffff else 1
        if units>p['character']:raise ValueError('surrogate split')
    if units==p['character']:return len(prefix)+len(lines[p['line']])
    raise ValueError('column beyond line')
def apply(text,edits):
    rows=[]
    for e in edits:
        a=offset(text,e['range']['start']);b=offset(text,e['range']['end']);rows.append((a,b,e['newText']))
    rows.sort(reverse=True)
    for i,(a,b,new) in enumerate(rows):
        if i and b>rows[i-1][0]:raise ValueError('overlapping edits')
        text=text[:a]+new+text[b:]
    return text
def workspace_edits(value):
    out={}
    if not isinstance(value,dict):return out
    for uri,edits in value.get('changes',{}).items():out.setdefault(uri,[]).extend(edits)
    for row in value.get('documentChanges',[]):
        uri=row.get('textDocument',{}).get('uri')
        if uri:out.setdefault(uri,[]).extend(row.get('edits',[]))
    return out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);args=ap.parse_args();work=args.work.resolve()
    assert not work.exists(),'choose absent owned work directory';work.mkdir(parents=True)
    for name,content in FILES.items():(work/name).write_text(content)
    env=dict(os.environ,LEAN_PATH=str(work),LEAN_SRC_PATH=str(work),LEAN_NUM_THREADS='1',LEAN_SERVER_LOG_DIR=str(work))
    pre=subprocess.run([str(LEAN),'-o',str(work/'Helper.olean'),'-i',str(work/'Helper.ilean'),str(work/'Helper.lean')],cwd=work,env=env,capture_output=True,text=True,timeout=20)
    assert pre.returncode==0,pre.stderr
    p=subprocess.Popen([str(LEAN),'--server'],cwd=work,env=env,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
    events=[];responses={};buf=b'';start=time.monotonic()
    uris={n:(work/n).as_uri() for n in FILES}
    def record(side,msg):events.append({'ms':round((time.monotonic()-start)*1000),'side':side,'message':msg})
    def send(msg):
        raw=json.dumps(msg,separators=(',',':')).encode();p.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw);p.stdin.flush();record('client',msg)
    def recv(pred,timeout=25):
        nonlocal buf
        deadline=time.monotonic()+timeout
        while time.monotonic()<deadline:
            while b'\r\n\r\n' in buf:
                head,rest=buf.split(b'\r\n\r\n',1);length=None
                for line in head.split(b'\r\n'):
                    if line.lower().startswith(b'content-length:'):length=int(line.split(b':',1)[1])
                if length is None or len(rest)<length:break
                raw,buf=rest[:length],rest[length:];msg=json.loads(raw);record('server',msg)
                if msg.get('method')=='client/registerCapability' and 'id' in msg:send({'jsonrpc':'2.0','id':msg['id'],'result':None})
                if pred(msg):return msg
            ready,_,_=select.select([p.stdout],[],[],max(0,deadline-time.monotonic()))
            if not ready:break
            part=os.read(p.stdout.fileno(),65536)
            if not part:break
            buf+=part
        raise TimeoutError('LSP wait timeout')
    def req(i,name,method,params):
        send({'jsonrpc':'2.0','id':i,'method':method,'params':params});responses[name]=recv(lambda m:m.get('id')==i);return responses[name]
    try:
        caps={'general':{'positionEncodings':['utf-16','utf-8']},'textDocument':{
          'completion':{'completionItem':{'snippetSupport':True,'resolveSupport':{'properties':['documentation','detail','additionalTextEdits']}}},
          'codeAction':{'codeActionLiteralSupport':{'codeActionKind':{'valueSet':['quickfix','refactor','source.organizeImports']}}},
          'rename':{'prepareSupport':True},'inlayHint':{'dynamicRegistration':False},'signatureHelp':{'signatureInformation':{'parameterInformation':{'labelOffsetSupport':True}}}}}
        req(1,'initialize','initialize',{'processId':os.getpid(),'rootUri':work.as_uri(),'capabilities':caps,
            'initializationOptions':{'hasWidgets':False,'logCfg':{'logDir':str(work)}}})
        send({'jsonrpc':'2.0','method':'initialized','params':{}})
        for n in ('Helper.lean','Main.lean','Action.lean','Completion.lean'):
            send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{'uri':uris[n],'languageId':'lean','version':1,'text':FILES[n]}}})
        for i,n in enumerate(('Helper.lean','Main.lean','Action.lean','Completion.lean'),2):
            req(i,'wait-'+n,'textDocument/waitForDiagnostics',{'uri':uris[n],'version':1})
        nav={'textDocument':{'uri':uris['Main.lean']},'position':pos(FILES['Main.lean'],2,'αhelper',1)}
        req(10,'rename','textDocument/rename',{**nav,'newName':'βhelper'})
        req(11,'references','textDocument/references',{**nav,'context':{'includeDeclaration':True}})
        for j,col in enumerate(range(30,37)):
            req(30+j,f'signature-{col}','textDocument/signatureHelp',{'textDocument':{'uri':uris['Main.lean']},
                'position':{'line':7,'character':col},'context':{'triggerKind':1,'isRetrigger':False}})
        req(13,'inlay','textDocument/inlayHint',{'textDocument':{'uri':uris['Main.lean']},
            'range':{'start':{'line':0,'character':0},'end':{'line':8,'character':0}}})
        comp=req(14,'completion','textDocument/completion',{'textDocument':{'uri':uris['Completion.lean']},
            'position':{'line':1,'character':utf16(FILES['Completion.lean'].splitlines()[1])},'context':{'triggerKind':1}})
        val=comp.get('result');items=val.get('items',[]) if isinstance(val,dict) else (val or [])
        item=next((x for x in items if x.get('label')=='αhelper'),None)
        if item:req(15,'completionResolve','completionItem/resolve',item)
        pubs=[e['message']['params'] for e in events if e['side']=='server' and e['message'].get('method')=='textDocument/publishDiagnostics']
        action_diags=[d for pub in pubs if pub.get('uri')==uris['Action.lean'] for d in pub.get('diagnostics',[]) if 'αhelper' in d.get('message','')]
        arange=action_diags[-1]['range'] if action_diags else {'start':{'line':0,'character':7},'end':{'line':0,'character':14}}
        req(16,'actionQuickfix','textDocument/codeAction',{'textDocument':{'uri':uris['Action.lean']},
            'range':arange,'context':{'diagnostics':action_diags[-1:] if action_diags else [],'only':['quickfix']}})
        req(17,'actionSource','textDocument/codeAction',{'textDocument':{'uri':uris['Action.lean']},
            'range':arange,'context':{'diagnostics':action_diags[-1:] if action_diags else [],'only':['source.organizeImports']}})
        actions=(responses['actionQuickfix'].get('result') or [])+(responses['actionSource'].get('result') or [])
        chosen=next((a for a in actions if a.get('edit')),None) or (actions[0] if actions else None)
        if chosen and chosen.get('data'):req(18,'actionResolve','codeAction/resolve',chosen)
        req(99,'shutdown','shutdown',None);send({'jsonrpc':'2.0','method':'exit'})
    except Exception as exc:responses['exception']=repr(exc)
    finally:
        try:p.wait(timeout=3)
        except subprocess.TimeoutExpired:p.kill();p.wait(timeout=3)
        stderr=p.stderr.read().decode(errors='replace')
    result={'lean_sha256':sha(LEAN),'source_sha256':{n:hashlib.sha256(s.encode()).hexdigest() for n,s in FILES.items()},
            'uri_by_name':uris,'prebuild':{'exit':pre.returncode,'stdout':pre.stdout,'stderr':pre.stderr,
                                         'olean_sha256':sha(work/'Helper.olean'),'ilean_sha256':sha(work/'Helper.ilean')},
            'events':events,'responses':responses,'server_exit':p.returncode,'server_stderr':stderr}
    OUT.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
    summary={k:(v.get('result') if isinstance(v,dict) else v) for k,v in responses.items() if k in
        ('rename','references','inlay','actionQuickfix','actionSource','actionResolve','completionResolve') or k.startswith('signature-')}
    print(json.dumps({'server_exit':p.returncode,'exception':responses.get('exception'),'summary':summary,
                      'completion_count':len(items) if 'items' in locals() else None},indent=2,ensure_ascii=False)[:10000])

if __name__=='__main__':main()
