#!/usr/bin/env python3
"""Raw JSON-RPC stdio client for a local MCP wire-shape model."""
import json
import os
from pathlib import Path
import select
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent
VERSION='2026-07-28';LEGACY='2025-11-25';EXT='io.modelcontextprotocol/tasks'

class Client:
    def __init__(self,mode):
        self.mode=mode;self.log=[];self.next_id=1;self.buffer=b''
        self.p=subprocess.Popen([sys.executable,str(HERE/'bridge.py'),mode],stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
    def send(self,message):
        self.log.append({'direction':'client','message':message})
        self.p.stdin.write((json.dumps(message,separators=(',',':'))+'\n').encode());self.p.stdin.flush()
    def read(self):
        end=time.monotonic()+4
        while time.monotonic()<end:
            if b'\n' in self.buffer:
                line,self.buffer=self.buffer.split(b'\n',1)
                msg=json.loads(line);self.log.append({'direction':'server','message':msg});return msg
            ready,_,_=select.select([self.p.stdout],[],[],.1)
            if ready:
                chunk=os.read(self.p.stdout.fileno(),65536)
                if not chunk:break
                self.buffer+=chunk
        raise TimeoutError(self.mode)
    def request(self,method,params=None,version=VERSION,capability=False):
        p=dict(params or {})
        if version is not False:
            m={'io.modelcontextprotocol/protocolVersion':version,
               'io.modelcontextprotocol/clientInfo':{'name':'local-raw-client','version':'1'},
               'io.modelcontextprotocol/clientCapabilities':{'extensions':{EXT:{}}} if capability else {}}
            p['_meta']=m
        ident=self.next_id;self.next_id+=1
        self.send({'jsonrpc':'2.0','id':ident,'method':method,'params':p})
        reply=self.read();assert reply['id']==ident,(ident,reply)
        return reply
    def notify(self,method,params):self.send({'jsonrpc':'2.0','method':method,'params':params})
    def close(self):
        self.p.stdin.close();self.p.wait(timeout=4)
        return {'pid':self.p.pid,'exit':self.p.returncode,'stderr':self.p.stderr.read().decode(errors='replace')}

def poll(client,tid,terminal):
    states=[];end=time.monotonic()+2
    while time.monotonic()<end:
        r=client.request('tasks/get',{'taskId':tid},capability=True)
        assert 'result' in r,r
        states.append(r['result']['status'])
        if states[-1]==terminal:return r,states
        time.sleep(.012)
    raise TimeoutError((tid,states))
def run():
    modern=Client('modern');cells={}
    try:
        cells['wrong_version_discover']=modern.request('server/discover',version='1900-01-01')
        assert cells['wrong_version_discover']['error']['code']==-32022
        cells['discover']=modern.request('server/discover')
        assert cells['discover']['result']['supportedVersions']==[VERSION]
        assert EXT in cells['discover']['result']['capabilities']['extensions']
        cells['missing_version']=modern.request('tools/call',{'name':'probe'},version=False)
        assert cells['missing_version']['error']['code']==-32602
        cells['modern_initialize']=modern.request('initialize')
        assert 'error' in cells['modern_initialize']
        cells['no_opt_in']=modern.request('tools/call',{'name':'probe','arguments':{}})
        assert cells['no_opt_in']['result']['resultType']=='complete'
        cells['start']=modern.request('tools/call',{'name':'probe','arguments':{'scenario':'success'}},capability=True)
        assert cells['start']['result']['resultType']=='task'
        tid=cells['start']['result']['taskId']
        cells['immediate_get']=modern.request('tasks/get',{'taskId':tid},capability=True)
        assert cells['immediate_get']['result']['status']=='working'
        cells['obsolete_result_method']=modern.request('tasks/result',{'taskId':tid},capability=True)
        assert cells['obsolete_result_method']['error']['code']==-32601
        cells['wrong_version_get']=modern.request('tasks/get',{'taskId':tid},version='1900-01-01',capability=True)
        assert cells['wrong_version_get']['error']['code']==-32022
        modern.request('test/release',{'taskId':tid},capability=True)
        cells['completed'],cells['completion_states']=poll(modern,tid,'completed')
        assert cells['completed']['result']['result']['isError'] is False
        time.sleep(.38)
        cells['expired']=modern.request('tasks/get',{'taskId':tid},capability=True)
        assert cells['expired']['error']['code']==-32602
        cells['unknown']=modern.request('tasks/get',{'taskId':'task-missing'},capability=True)
        assert cells['unknown']['error']['code']==-32602
        cells['tool_error_start']=modern.request('tools/call',{'name':'probe','arguments':{'scenario':'tool_error'}},capability=True)
        te=cells['tool_error_start']['result']['taskId'];modern.request('test/release',{'taskId':te},capability=True)
        cells['tool_error'],_=poll(modern,te,'completed')
        assert cells['tool_error']['result']['result']['isError'] is True
        cells['rpc_failure_start']=modern.request('tools/call',{'name':'probe','arguments':{'scenario':'rpc_failure'}},capability=True)
        rf=cells['rpc_failure_start']['result']['taskId'];modern.request('test/release',{'taskId':rf},capability=True)
        cells['rpc_failure'],_=poll(modern,rf,'failed')
        assert cells['rpc_failure']['result']['error']['code']==-32603
        cells['cancel_start']=modern.request('tools/call',{'name':'probe','arguments':{}},capability=True)
        ct=cells['cancel_start']['result']['taskId']
        modern.notify('notifications/cancelled',{'requestId':cells['cancel_start']['id']})
        cells['after_wrong_cancel']=modern.request('tasks/get',{'taskId':ct},capability=True)
        assert cells['after_wrong_cancel']['result']['status']=='working'
        cells['cancel_ack']=modern.request('tasks/cancel',{'taskId':ct},capability=True)
        assert cells['cancel_ack']['result']=={'resultType':'complete'}
        cells['after_cancel_ack']=modern.request('tasks/get',{'taskId':ct},capability=True)
        assert cells['after_cancel_ack']['result']['status']=='working'
        modern.request('test/release',{'taskId':ct},capability=True)
        cells['cancelled'],cells['cancel_states']=poll(modern,ct,'cancelled')
        cells['cancel_unknown']=modern.request('tasks/cancel',{'taskId':'task-missing'},capability=True)
        assert 'error' in cells['cancel_unknown']
    finally:modern_close=modern.close()
    legacy=Client('legacy');old={}
    try:
        old['discover']=legacy.request('server/discover')
        assert old['discover']['error']['code']==-32601
        old['initialize']=legacy.request('initialize',{'protocolVersion':LEGACY,'capabilities':{},
            'clientInfo':{'name':'local-raw-client','version':'1'}},version=False)
        assert old['initialize']['result']['protocolVersion']==LEGACY
        legacy.notify('notifications/initialized',{})
        old['sync']=legacy.request('tools/call',{'name':'probe','arguments':{}},version=False)
        assert old['sync']['result']['content'][0]['text']=='legacy sync fallback'
        old['tasks_get']=legacy.request('tasks/get',{'taskId':'x'},version=False)
        assert old['tasks_get']['error']['code']==-32601
    finally:old_close=legacy.close()
    result={'scope':'stdlib local test bridge; no SDK, Anneal or Lean','spec_revision':VERSION,
        'modern':cells,'modern_transcript':modern.log,'modern_process':modern_close,
        'legacy':old,'legacy_transcript':legacy.log,'legacy_process':old_close,
        'inferences':{'recognized_modern_error_retried_without_initialize':True,
            'legacy_nonmodern_error_fell_back_to_initialize':True,
            'task_progress_polled_not_progress_notification':True,
            'expired_error_is_this_bridge_policy_not_required_timing':True}}
    assert all('id' in row['message'] for row in modern.log if row['direction']=='server')
    assert all(row['message'].get('method')!='notifications/progress' for row in modern.log if row['direction']=='server')
    (HERE/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    return result
if __name__=='__main__':
    x=run();print(json.dumps({'modern_events':len(x['modern_transcript']),
        'legacy_events':len(x['legacy_transcript']),'task_statuses':['completed','completed','failed','cancelled']}))
