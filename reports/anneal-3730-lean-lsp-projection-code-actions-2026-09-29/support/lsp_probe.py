#!/usr/bin/env python3
"""Direct Lean 4.30.0-rc2 LSP capability, encoding and request probe."""
import hashlib,json,os,select,subprocess,time
from pathlib import Path

HERE=Path(__file__).resolve().parent
LEAN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
SOURCE=(HERE/'Unicode.lean').read_text()
OUT=HERE/'lsp-transcript.json'

def session(offered, tag):
    work=Path('/Users/josh/Codex/Meta/Data/20260929-issue-3730-3731')/('r13-lsp-'+tag)
    work.mkdir(parents=True,exist_ok=True)
    file=work/'Unicode.lean';file.write_text(SOURCE)
    env=dict(os.environ,LEAN_SERVER_LOG_DIR=str(work))
    p=subprocess.Popen([str(LEAN),'--server'],cwd=work,env=env,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
    events=[];buf=b'';start=time.monotonic()
    def record(side,msg):events.append({'ms':round((time.monotonic()-start)*1000),'side':side,'message':msg})
    def send(msg):
        raw=json.dumps(msg,separators=(',',':')).encode()
        p.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw);p.stdin.flush();record('client',msg)
    def recv_until(pred,timeout=18):
        nonlocal buf
        deadline=time.monotonic()+timeout
        while time.monotonic()<deadline:
            while b'\r\n\r\n' in buf:
                header,rest=buf.split(b'\r\n\r\n',1)
                length=None
                for line in header.split(b'\r\n'):
                    if line.lower().startswith(b'content-length:'):length=int(line.split(b':',1)[1])
                if length is None or len(rest)<length:break
                raw,buf=rest[:length],rest[length:]
                msg=json.loads(raw);record('server',msg)
                if msg.get('method')=='client/registerCapability' and 'id' in msg:
                    send({'jsonrpc':'2.0','id':msg['id'],'result':None})
                if pred(msg):return msg
            ready,_,_=select.select([p.stdout],[],[],max(0,deadline-time.monotonic()))
            if not ready:break
            part=os.read(p.stdout.fileno(),65536)
            if not part:break
            buf+=part
        raise TimeoutError('LSP response timeout')
    uri=file.as_uri()
    responses={}
    try:
        caps={'general':{'positionEncodings':offered},'textDocument':{'completion':{'completionItem':{}},'codeAction':{'codeActionLiteralSupport':{'codeActionKind':{'valueSet':['quickfix','refactor','source']}}}}}
        send({'jsonrpc':'2.0','id':1,'method':'initialize','params':{'processId':os.getpid(),'rootUri':work.as_uri(),'capabilities':caps,'initializationOptions':{'hasWidgets':False,'logCfg':{'logDir':str(work)}}}})
        responses['initialize']=recv_until(lambda m:m.get('id')==1)
        send({'jsonrpc':'2.0','method':'initialized','params':{}})
        send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{'uri':uri,'languageId':'lean','version':1,'text':SOURCE}}})
        send({'jsonrpc':'2.0','id':2,'method':'textDocument/waitForDiagnostics','params':{'uri':uri,'version':1}})
        responses['wait']=recv_until(lambda m:m.get('id')==2)
        diagnostics=[e['message'] for e in events if e['side']=='server' and e['message'].get('method')=='textDocument/publishDiagnostics']
        # Drain the most recent available diagnostic publication after elaboration.
        diag=diagnostics[-1]['params']['diagnostics'] if diagnostics else []
        unknown=[d for d in diag if 'unknownName' in d.get('message','')]
        action_range=unknown[0]['range'] if unknown else {'start':{'line':3,'character':0},'end':{'line':3,'character':30}}
        send({'jsonrpc':'2.0','id':3,'method':'textDocument/completion','params':{'textDocument':{'uri':uri},'position':{'line':6,'character':5},'context':{'triggerKind':1}}})
        responses['completion']=recv_until(lambda m:m.get('id')==3)
        send({'jsonrpc':'2.0','id':4,'method':'textDocument/codeAction','params':{'textDocument':{'uri':uri},'range':action_range,'context':{'diagnostics':unknown,'only':['quickfix']}}})
        responses['codeAction']=recv_until(lambda m:m.get('id')==4)
        send({'jsonrpc':'2.0','id':5,'method':'textDocument/hover','params':{'textDocument':{'uri':uri},'position':{'line':1,'character':8}}})
        responses['hover']=recv_until(lambda m:m.get('id')==5)
        send({'jsonrpc':'2.0','id':9,'method':'shutdown','params':None})
        responses['shutdown']=recv_until(lambda m:m.get('id')==9)
        send({'jsonrpc':'2.0','method':'exit'})
    except Exception as exc:
        responses['exception']=repr(exc)
    finally:
        try:p.wait(timeout=3)
        except subprocess.TimeoutExpired:p.kill();p.wait(timeout=3)
        stderr=p.stderr.read().decode(errors='replace')
    return {'offered':offered,'source_sha256':hashlib.sha256(SOURCE.encode()).hexdigest(),
            'lean_sha256':hashlib.sha256(LEAN.read_bytes()).hexdigest(),'responses':responses,
            'events':events,'exit':p.returncode,'stderr':stderr}

def main():
    result={'utf16_first':session(['utf-16','utf-8'],'utf16'),
            'utf8_first':session(['utf-8','utf-16'],'utf8')}
    OUT.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
    for key,val in result.items():
        caps=val['responses'].get('initialize',{}).get('result',{}).get('capabilities',{})
        comp=val['responses'].get('completion',{})
        action=val['responses'].get('codeAction',{})
        diags=[e['message']['params']['diagnostics'] for e in val['events'] if e['side']=='server' and e['message'].get('method')=='textDocument/publishDiagnostics']
        print(key,'exit',val['exit'],'encoding',caps.get('positionEncoding'),'completion',len(comp.get('result',{}).get('items',[])) if isinstance(comp.get('result'),dict) else type(comp.get('result')).__name__,'codeAction',action.get('result'),'diagPublications',len(diags),'exception',val['responses'].get('exception'))

if __name__=='__main__':main()
