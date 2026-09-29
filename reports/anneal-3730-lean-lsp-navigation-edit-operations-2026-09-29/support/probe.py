#!/usr/bin/env python3
"""Direct Lean LSP navigation/edit requests with explicit client edit application."""
import hashlib,json,os,select,subprocess,time
from pathlib import Path

HERE=Path(__file__).resolve().parent
LEAN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
SOURCE=(HERE/'UnicodeOps.lean').read_text()
WORK=Path('/Users/josh/Codex/Meta/Data/20260929-issue-3730-3731/r14-lsp')
OUT=HERE/'transcript.json'

def sha_text(s):return hashlib.sha256(s.encode()).hexdigest()

def offset(text,pos):
    lines=text.splitlines(keepends=True);line=pos['line'];col=pos['character']
    assert 0<=line<len(lines)
    prefix=''.join(lines[:line]);s=lines[line];units=0
    for i,ch in enumerate(s):
        if units==col:return len(prefix)+i
        units+=2 if ord(ch)>0xffff else 1
        if units>col:raise ValueError('inside UTF-16 surrogate pair')
    if units==col:return len(prefix)+len(s)
    raise ValueError('column out of range')

def apply_edits(text,edits):
    prepared=[]
    for e in edits:
        a=offset(text,e['range']['start']);b=offset(text,e['range']['end']);assert a<=b
        prepared.append((a,b,e['newText']))
    prepared.sort(reverse=True)
    for i,(a,b,new) in enumerate(prepared):
        if i and b>prepared[i-1][0]:raise ValueError('overlapping edits')
        text=text[:a]+new+text[b:]
    return text

def run():
    WORK.mkdir(parents=True,exist_ok=True)
    source_file=WORK/'UnicodeOps.lean';source_file.write_text(SOURCE)
    env=dict(os.environ,LEAN_SERVER_LOG_DIR=str(WORK))
    p=subprocess.Popen([str(LEAN),'--server'],cwd=WORK,env=env,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
    events=[];responses={};buffer=b'';start=time.monotonic()
    def record(side,msg):events.append({'elapsed_ms':round((time.monotonic()-start)*1000),'side':side,'message':msg})
    def send(msg):
        raw=json.dumps(msg,separators=(',',':')).encode()
        p.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw);p.stdin.flush();record('client',msg)
    def receive(pred,timeout=18):
        nonlocal buffer
        deadline=time.monotonic()+timeout
        while time.monotonic()<deadline:
            while b'\r\n\r\n' in buffer:
                hdr,rest=buffer.split(b'\r\n\r\n',1);length=None
                for line in hdr.split(b'\r\n'):
                    if line.lower().startswith(b'content-length:'):length=int(line.split(b':',1)[1])
                if length is None or len(rest)<length:break
                raw,buffer=rest[:length],rest[length:];msg=json.loads(raw);record('server',msg)
                if msg.get('method')=='client/registerCapability' and 'id' in msg:
                    send({'jsonrpc':'2.0','id':msg['id'],'result':None})
                if pred(msg):return msg
            ready,_,_=select.select([p.stdout],[],[],max(0,deadline-time.monotonic()))
            if not ready:break
            part=os.read(p.stdout.fileno(),65536)
            if not part:break
            buffer+=part
        raise TimeoutError('LSP response timeout')
    def request(id_,method,params,name):
        send({'jsonrpc':'2.0','id':id_,'method':method,'params':params})
        responses[name]=receive(lambda m:m.get('id')==id_)
        return responses[name]
    uri=source_file.as_uri();doc={'uri':uri}
    try:
        caps={'general':{'positionEncodings':['utf-16','utf-8']},'textDocument':{
            'completion':{'completionItem':{'snippetSupport':True,'resolveSupport':{'properties':['documentation','detail','additionalTextEdits']}}},
            'codeAction':{'codeActionLiteralSupport':{'codeActionKind':{'valueSet':['quickfix','refactor','source.organizeImports']}}},
            'rename':{'prepareSupport':True},'semanticTokens':{'requests':{'full':True,'range':True},
              'tokenTypes':['keyword','variable','function','comment','string','number'],
              'tokenModifiers':['declaration','definition']}}}
        request(1,'initialize',{'processId':os.getpid(),'rootUri':WORK.as_uri(),'capabilities':caps,
                'initializationOptions':{'hasWidgets':False,'logCfg':{'logDir':str(WORK)}}},'initialize')
        send({'jsonrpc':'2.0','method':'initialized','params':{}})
        send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{'uri':uri,'languageId':'lean','version':1,'text':SOURCE}}})
        request(2,'textDocument/waitForDiagnostics',{'uri':uri,'version':1},'wait')
        nav={'textDocument':doc,'position':{'line':3,'character':10}}
        request(3,'textDocument/definition',nav,'definition')
        request(4,'textDocument/references',{**nav,'context':{'includeDeclaration':True}},'references')
        request(5,'textDocument/prepareRename',nav,'prepareRename')
        request(6,'textDocument/rename',{**nav,'newName':'renamed_demo'},'rename')
        request(7,'textDocument/semanticTokens/full',{'textDocument':doc},'semanticTokens')
        completion=request(8,'textDocument/completion',{'textDocument':doc,'position':{'line':6,'character':5},'context':{'triggerKind':1}},'completion')
        value=completion.get('result');items=value.get('items',[]) if isinstance(value,dict) else (value or [])
        exact=next((item for item in items if item.get('label')=='exact'),None)
        if exact:request(9,'completionItem/resolve',exact,'completionResolve')
        publications=[e['message']['params']['diagnostics'] for e in events if e['side']=='server' and e['message'].get('method')=='textDocument/publishDiagnostics']
        tactic=[d for ds in publications for d in ds if 'unknown tactic' in d.get('message','')]
        range_=tactic[-1]['range'] if tactic else {'start':{'line':6,'character':2},'end':{'line':6,'character':5}}
        request(10,'textDocument/codeAction',{'textDocument':doc,'range':range_,
                 'context':{'diagnostics':tactic[-1:] if tactic else []}},'codeAction')
        request(99,'shutdown',None,'shutdown')
        send({'jsonrpc':'2.0','method':'exit'})
    except Exception as exc:responses['exception']=repr(exc)
    finally:
        try:p.wait(timeout=3)
        except subprocess.TimeoutExpired:p.kill();p.wait(timeout=3)
        stderr=p.stderr.read().decode(errors='replace')
    # Retain the server's actual workspace edit separately from a client fallback
    # for completion items that carry only a label and no textEdit.
    applied=SOURCE;applications=[]
    rename=responses.get('rename',{}).get('result')
    rename_edits=[]
    if isinstance(rename,dict):
        rename_edits.extend(rename.get('changes',{}).get(uri,[]))
        for change in rename.get('documentChanges',[]):
            if change.get('textDocument',{}).get('uri')==uri:
                rename_edits.extend(change.get('edits',[]))
    if rename_edits:
        applied=apply_edits(applied,rename_edits)
        applications.append({'origin':'server rename WorkspaceEdit','edits':rename_edits,'sha256':sha_text(applied)})
    resolved=responses.get('completionResolve',{}).get('result',{})
    completion_edits=[]
    if isinstance(resolved,dict):
        edit=resolved.get('textEdit')
        if edit and 'range' in edit:completion_edits.append({'range':edit['range'],'newText':edit.get('newText','')})
        completion_edits.extend(resolved.get('additionalTextEdits',[]))
    if completion_edits:
        applied=apply_edits(applied,completion_edits)
        applications.append({'origin':'server completion TextEdit','edits':completion_edits,'sha256':sha_text(applied)})
    elif resolved.get('label')=='exact':
        # LSP insertText fallback is client behavior, not a returned Lean edit.
        client_edit={'range':{'start':{'line':6,'character':2},'end':{'line':6,'character':5}},'newText':'exact'}
        assert applied.splitlines()[6].startswith('  exa hβ')
        applied=apply_edits(applied,[client_edit])
        applications.append({'origin':'illustrative client word replacement from completion label','edits':[client_edit],'sha256':sha_text(applied)})
    applied_file=HERE/'Applied.lean';applied_file.write_text(applied)
    batch=subprocess.run([str(LEAN),'--json',str(applied_file)],cwd=HERE,capture_output=True,text=True,timeout=20)
    result={'lean_sha256':hashlib.sha256(LEAN.read_bytes()).hexdigest(),'source_sha256':sha_text(SOURCE),
            'source_uri':uri,'events':events,'responses':responses,'server_exit':p.returncode,'server_stderr':stderr,
            'applications':applications,'applied_sha256':sha_text(applied),
            'batch':{'argv':['$LEAN','--json','$REPORT/support/Applied.lean'],'exit':batch.returncode,
                     'stdout':batch.stdout,'stderr':batch.stderr}}
    OUT.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({'server_exit':p.returncode,'exception':responses.get('exception'),
          'definition':responses.get('definition',{}).get('result'),'references':responses.get('references',{}).get('result'),
          'prepareRename':responses.get('prepareRename',{}).get('result'),
          'rename':responses.get('rename',{}).get('result'),'semantic_count':len(responses.get('semanticTokens',{}).get('result',{}).get('data',[])),
          'completion_count':len(items),'resolved':resolved,'codeAction':responses.get('codeAction',{}).get('result'),
          'applications':applications,'batch_exit':batch.returncode},indent=2,ensure_ascii=False))

if __name__=='__main__':run()
