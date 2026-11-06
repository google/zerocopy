#!/usr/bin/env python3
"""Synthetic typed Lean generator: identical plan, file and live LSP sinks."""
from __future__ import annotations
from dataclasses import dataclass
from pathlib import Path
from typing import Literal
import hashlib,json,os,select,shutil,subprocess,time

HERE=Path(__file__).resolve().parent
WORK=Path('/Users/josh/Codex/Meta/Data/20260929-issue-3730-3731/i028-work')
LEAN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
ENV=dict(os.environ,ELAN_TOOLCHAIN='leanprover/lean4:v4.30.0-rc2',LEAN_NUM_THREADS='1')
def sha(data:bytes)->str:return hashlib.sha256(data).hexdigest()
def filehash(p:Path)->str:return sha(p.read_bytes())
def utf16_col(text:str)->int:return sum(2 if ord(ch)>0xffff else 1 for ch in text)
def lsp_pos(text:str,at:int)->dict:
    before=text[:at];line=before.count('\n');tail=before.rsplit('\n',1)[-1]
    return {'line':line,'character':utf16_col(tail)}
@dataclass(frozen=True)
class Input:
    name:str
    module:Literal['Base','Alt']
    annotation:str
@dataclass(frozen=True)
class Segment:
    kind:Literal['header','annotation','footer']
    text:str
@dataclass(frozen=True)
class Plan:
    source:Input
    segments:tuple[Segment,...]
    def text(self)->str:return ''.join(x.text for x in self.segments)
    def source_map(self)->dict:
        header=self.segments[0].text;source=self.source.annotation;full=self.text()
        points=[]
        for i in range(len(source)+1):
            prefix=source[:i];gchar=len(header)+i
            points.append({'source_utf8':len(prefix.encode()),'generated_utf8':len((header+prefix).encode()),
                           'source_utf16':lsp_pos(source,i),'generated_utf16':lsp_pos(full,gchar)})
        return {'source_text_sha256':sha(source.encode()),'generated_text_sha256':sha(full.encode()),
                'source_span_utf8':[0,len(source.encode())],
                'generated_span_utf8':[len(header.encode()),len((header+source).encode())],
                'points':points}
def construct(source:Input)->Plan:
    assert source.module in ('Base','Alt')
    return Plan(source,(
        Segment('header',f'import {source.module}\nnamespace Generated\n'),
        Segment('annotation',source.annotation),
        Segment('footer','end Generated\n#check Generated.checked\n#print axioms Generated.checked\n')))
class FileSink:
    def __init__(self,path:Path):self.path=path;self.file=path.open('wb')
    def emit(self,s:Segment)->None:self.file.write(s.text.encode())
    def finish(self)->bytes:
        self.file.close();return self.path.read_bytes()
class LSP:
    def __init__(self,root:Path):
        self.root=root;self.p=subprocess.Popen([str(LEAN),'--server'],cwd=root,env=dict(ENV,LEAN_PATH=str(root)),stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
        self.buf=b'';self.messages=[];self.diags=[]
        self.send(dict(jsonrpc='2.0',id=1,method='initialize',params={'processId':os.getpid(),'rootUri':root.as_uri(),'capabilities':{},'initializationOptions':{'hasWidgets':False}}))
        self.until(1);self.send(dict(jsonrpc='2.0',method='initialized',params={}))
    def send(self,m:dict)->None:
        data=json.dumps(m,separators=(',',':'),ensure_ascii=False).encode()
        self.p.stdin.write(b'Content-Length: '+str(len(data)).encode()+b'\r\n\r\n'+data);self.p.stdin.flush()
        self.messages.append({'direction':'client','message':m})
    def read(self,timeout=15)->dict:
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            if b'\r\n\r\n' in self.buf:
                head,body=self.buf.split(b'\r\n\r\n',1)
                lengths=[int(x.split(b':',1)[1]) for x in head.split(b'\r\n') if x.lower().startswith(b'content-length:')]
                if lengths and len(body)>=lengths[0]:
                    raw,self.buf=body[:lengths[0]],body[lengths[0]:]
                    m=json.loads(raw);self.messages.append({'direction':'server','message':m})
                    if m.get('method')=='textDocument/publishDiagnostics':self.diags.append(m['params'])
                    if 'method' in m and 'id' in m:self.send(dict(jsonrpc='2.0',id=m['id'],result=None))
                    return m
            r,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
            if r:
                b=os.read(self.p.stdout.fileno(),65536)
                if not b:break
                self.buf+=b
        raise TimeoutError('Lean LSP response')
    def until(self,id:int)->dict:
        for _ in range(100):
            m=self.read()
            if m.get('id')==id and 'method' not in m:return m
        raise TimeoutError('Lean LSP id '+str(id))
    def close(self)->dict:
        if self.p.poll() is None:
            try:
                self.send(dict(jsonrpc='2.0',id=99,method='shutdown',params=None));self.until(99)
                self.send(dict(jsonrpc='2.0',method='exit'));self.p.wait(timeout=5)
            except Exception:self.p.kill();self.p.wait()
        return {'rc':self.p.returncode,'stderr':self.p.stderr.read().decode(errors='replace')}
class StreamingSink:
    def __init__(self,server:LSP,uri:str):self.server=server;self.uri=uri;self.parts=[];self.version=0
    def emit(self,s:Segment)->None:
        self.parts.append(s.text);self.version+=1;text=''.join(self.parts)
        if self.version==1:
            self.server.send(dict(jsonrpc='2.0',method='textDocument/didOpen',params={'textDocument':{'uri':self.uri,'languageId':'lean','version':self.version,'text':text}}))
        else:
            self.server.send(dict(jsonrpc='2.0',method='textDocument/didChange',params={'textDocument':{'uri':self.uri,'version':self.version},'contentChanges':[{'text':text}]}))
    def finish(self)->bytes:
        self.server.send(dict(jsonrpc='2.0',id=2,method='textDocument/waitForDiagnostics',params={'uri':self.uri,'version':self.version}))
        self.wait=self.server.until(2);return ''.join(self.parts).encode()
def cmd(label,argv,cwd,env=ENV):
    p=subprocess.run([str(x) for x in argv],cwd=cwd,env=env,capture_output=True,text=True,timeout=20)
    return {'label':label,'argv':[str(x) for x in argv],'rc':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
def diagnostics_json(output:str)->list:
    return [json.loads(line) for line in output.splitlines() if line.strip()]
def main():
    assert LEAN.is_file()
    if WORK.exists():shutil.rmtree(WORK)
    WORK.mkdir()
    cases=[
      Input('valid','Base','theorem checked : depValue = 7 := by\n  decide\n'),
      Input('incomplete','Base','theorem checked : depValue = 7 := by\n  skip\n'),
      Input('import-edit','Alt','theorem checked : depValue = 7 := by\n  decide\n'),
      Input('unicode-crlf','Base','theorem checked : depValue = 7 := by\r\n  -- λ😀 note\r\n  decide\r\n'),
    ]
    out={'schema':1,'subject':{'lean_sha256':filehash(LEAN),'version':cmd('version',[LEAN,'--version'],WORK)['stdout'].strip()},'cases':{}}
    archive=HERE/'artifacts'
    if archive.exists():shutil.rmtree(archive)
    for source in cases:
        plan=construct(source);root=WORK/source.name;file_root=root/'file';stream_root=root/'stream';file_root.mkdir(parents=True);stream_root.mkdir()
        module_text='def depValue : Nat := '+('7' if source.module=='Base' else '9')+'\n'
        for r in (file_root,stream_root):
            (r/(source.module+'.lean')).write_text(module_text)
            build=cmd('build-import',[LEAN,'-o',source.module+'.olean',source.module+'.lean'],r)
            assert build['rc']==0,build
        assert filehash(file_root/(source.module+'.olean'))==filehash(stream_root/(source.module+'.olean'))
        fs=FileSink(file_root/'Generated.lean')
        for seg in plan.segments:fs.emit(seg)
        file_bytes=fs.finish()
        server=LSP(stream_root)
        try:
            ss=StreamingSink(server,(stream_root/'Generated.lean').as_uri())
            for seg in plan.segments:ss.emit(seg)
            stream_bytes=ss.finish()
            virtual_file_absent_at_final=not (stream_root/'Generated.lean').exists()
            # Persist the exact streamed final text only after the live query.
            (stream_root/'Generated.lean').write_bytes(stream_bytes)
            live={'wait':ss.wait,'diagnostics':[d for d in server.diags if d.get('version')==ss.version],
                  'versions':ss.version,'virtual_file_absent_at_final':virtual_file_absent_at_final,
                  'messages':server.messages}
        finally:live['process']=server.close()
        fbatch=cmd('file-batch',[LEAN,'--json','Generated.lean'],file_root,dict(ENV,LEAN_PATH=str(file_root)))
        sbatch=cmd('stream-batch',[LEAN,'--json','Generated.lean'],stream_root,dict(ENV,LEAN_PATH=str(stream_root)))
        assert file_bytes==stream_bytes==plan.text().encode()
        m=plan.source_map();a=archive/source.name;a.mkdir(parents=True)
        (a/'annotation').write_bytes(source.annotation.encode());(a/'import.lean').write_text(module_text)
        (a/'file.lean').write_bytes(file_bytes);(a/'stream.lean').write_bytes(stream_bytes)
        (a/'map.json').write_text(json.dumps(m,indent=2,ensure_ascii=False)+'\n')
        out['cases'][source.name]={
          'input':{'module':source.module,'annotation_sha256':sha(source.annotation.encode()),'annotation_bytes':len(source.annotation.encode())},
          'segments':[{'kind':s.kind,'sha256':sha(s.text.encode()),'bytes':len(s.text.encode())} for s in plan.segments],
          'file_sha256':sha(file_bytes),'stream_sha256':sha(stream_bytes),'file_bytes':len(file_bytes),
          'import_source_sha256':filehash(a/'import.lean'),'import_olean_sha256':filehash(file_root/(source.module+'.olean')),
          'source_map_sha256':filehash(a/'map.json'),
          'batch_file':{**fbatch,'diagnostics':diagnostics_json(fbatch['stdout'])},
          'batch_stream':{**sbatch,'diagnostics':diagnostics_json(sbatch['stdout'])},
          'live':live}
    (HERE/'results.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({'cases':list(out['cases']),'results_sha256':filehash(HERE/'results.json')},indent=2))
if __name__=='__main__':main()
