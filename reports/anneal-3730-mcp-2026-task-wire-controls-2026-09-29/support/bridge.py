#!/usr/bin/env python3
"""Deterministic local MCP wire-shape model; no SDK or Anneal implementation."""
import json
import sys
import threading
import time
from datetime import datetime, timezone

MODE=sys.argv[1]
VERSION='2026-07-28'
LEGACY='2025-11-25'
EXT='io.modelcontextprotocol/tasks'
lock=threading.Lock();tasks={};counter=0;initialized=False

def stamp():return datetime.now(timezone.utc).isoformat().replace('+00:00','Z')
def emit(obj):
    sys.stdout.write(json.dumps(obj,separators=(',',':'))+'\n');sys.stdout.flush()
def answer(req,result=None,error=None):
    obj={'jsonrpc':'2.0','id':req.get('id')}
    if error is None:obj['result']=result
    else:obj['error']=error
    emit(obj)
def err(code,message,data=None):
    x={'code':code,'message':message}
    if data is not None:x['data']=data
    return x
def meta(req):return (req.get('params') or {}).get('_meta') or {}
def finish(task):
    task['gate'].wait(5)
    with lock:
        if task['cancel_requested']:
            task['status']='cancelled';task['statusMessage']='cancelled after cooperative gate'
        elif task['scenario']=='rpc_failure':
            task['status']='failed';task['statusMessage']='injected JSON-RPC failure'
            task['error']=err(-32603,'injected JSON-RPC failure')
        else:
            task['status']='completed';task['statusMessage']='finished'
            task['result']={'resultType':'complete','content':[{'type':'text','text':'fixture result'}],
                            'isError':task['scenario']=='tool_error'}
        task['lastUpdatedAt']=stamp()
def public(task):
    keys=['taskId','status','statusMessage','createdAt','lastUpdatedAt','ttlMs','pollIntervalMs','result','error']
    return {'resultType':'complete',**{k:task[k] for k in keys if k in task}}
def task_lookup(req):
    tid=(req.get('params') or {}).get('taskId')
    with lock:
        task=tasks.get(tid)
        if task and time.monotonic()>=task['expires_mono']:return None,err(-32602,'Failed to retrieve task: Task has expired')
        if not task:return None,err(-32602,'Failed to retrieve task: Task not found')
    return task,None
def modern(req):
    global counter
    method=req.get('method');m=meta(req)
    version=m.get('io.modelcontextprotocol/protocolVersion')
    if version!=VERSION:
        if version is None:answer(req,error=err(-32602,'Missing protocol version'));return
        answer(req,error=err(-32022,'Unsupported protocol version',{'supported':[VERSION],'requested':version}));return
    if method=='server/discover':
        answer(req,{'resultType':'complete','supportedVersions':[VERSION],
            'capabilities':{'tools':{},'extensions':{EXT:{}}},
            '_meta':{'io.modelcontextprotocol/serverInfo':{'name':'local-wire-model','version':'1'}}});return
    if method=='initialize':answer(req,error=err(-32601,'initialize unsupported in modern era'));return
    if method=='tools/call':
        params=req.get('params') or {}
        if params.get('name')!='probe':answer(req,error=err(-32602,'unknown tool'));return
        caps=m.get('io.modelcontextprotocol/clientCapabilities') or {}
        if EXT not in caps.get('extensions',{}):
            answer(req,{'resultType':'complete','content':[{'type':'text','text':'sync fallback'}],'isError':False});return
        scenario=(params.get('arguments') or {}).get('scenario','success')
        if scenario not in ('success','tool_error','rpc_failure'):answer(req,error=err(-32602,'unknown scenario'));return
        with lock:
            counter+=1;tid=f'task-{counter}';now=stamp();task={'taskId':tid,'status':'working',
                'statusMessage':'waiting at test gate','createdAt':now,'lastUpdatedAt':now,
                'ttlMs':350,'pollIntervalMs':10,'expires_mono':time.monotonic()+.35,
                'cancel_requested':False,'scenario':scenario,'gate':threading.Event()}
            tasks[tid]=task
        threading.Thread(target=finish,args=(task,),daemon=True).start()
        answer(req,{'resultType':'task',**{k:task[k] for k in
            ['taskId','status','statusMessage','createdAt','lastUpdatedAt','ttlMs','pollIntervalMs']}});return
    if method=='tasks/get':
        task,e=task_lookup(req)
        if e:answer(req,error=e)
        else:
            with lock:answer(req,public(task))
        return
    if method=='tasks/cancel':
        task,e=task_lookup(req)
        if e:answer(req,error=e)
        else:
            with lock:task['cancel_requested']=True
            answer(req,{'resultType':'complete'})
        return
    if method=='test/release':
        task,e=task_lookup(req)
        if e:answer(req,error=e)
        else:task['gate'].set();answer(req,{'resultType':'complete'})
        return
    answer(req,error=err(-32601,'Method not found'))
def legacy(req):
    global initialized
    method=req.get('method')
    if method=='server/discover':answer(req,error=err(-32601,'Method not found'));return
    if method=='initialize':
        initialized=True
        answer(req,{'protocolVersion':LEGACY,'capabilities':{'tools':{}},'serverInfo':{'name':'legacy-model','version':'1'}});return
    if not initialized:answer(req,error=err(-32000,'not initialized'));return
    if method=='tools/call':answer(req,{'content':[{'type':'text','text':'legacy sync fallback'}],'isError':False});return
    answer(req,error=err(-32601,'Method not found'))

for line in sys.stdin:
    if not line.strip():continue
    try:req=json.loads(line)
    except json.JSONDecodeError:emit({'jsonrpc':'2.0','id':None,'error':err(-32700,'Parse error')});continue
    if 'id' not in req:
        # This model accepts no client notification with task-cancellation effect.
        continue
    (modern if MODE=='modern' else legacy)(req)
