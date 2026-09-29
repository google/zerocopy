#!/usr/bin/env python3
"""Check retained local MCP wire-shape model transcript; no SDK invocation."""
import json
from pathlib import Path

x=json.loads((Path(__file__).parent/'results.json').read_text())
assert x['spec_revision']=='2026-07-28'
m=x['modern'];old=x['legacy']
assert m['wrong_version_discover']['error']['code']==-32022
assert m['wrong_version_discover']['error']['data']['supported']==['2026-07-28']
assert m['discover']['result']['resultType']=='complete'
assert 'io.modelcontextprotocol/tasks' in m['discover']['result']['capabilities']['extensions']
assert m['missing_version']['error']['code']==-32602
assert m['modern_initialize']['error']['code']==-32601
assert m['no_opt_in']['result']['resultType']=='complete'
assert m['start']['result']['resultType']=='task'
assert m['immediate_get']['result']['status']=='working'
assert m['completed']['result']['resultType']=='complete'
assert m['completed']['result']['status']=='completed'
assert m['completed']['result']['result']['isError'] is False
assert m['obsolete_result_method']['error']['code']==-32601
assert m['expired']['error']['code']==-32602 and m['unknown']['error']['code']==-32602
assert m['tool_error']['result']['status']=='completed' and m['tool_error']['result']['result']['isError'] is True
assert m['rpc_failure']['result']['status']=='failed' and m['rpc_failure']['result']['error']['code']==-32603
assert m['after_wrong_cancel']['result']['status']=='working'
assert m['cancel_ack']['result']=={'resultType':'complete'}
assert m['after_cancel_ack']['result']['status']=='working'
assert m['cancelled']['result']['status']=='cancelled'
assert m['cancel_unknown']['error']['code']==-32602
assert old['discover']['error']['code']==-32601
assert old['initialize']['result']['protocolVersion']=='2025-11-25'
assert old['sync']['result']['content'][0]['text']=='legacy sync fallback'
assert old['tasks_get']['error']['code']==-32601
assert x['modern_process']['exit']==0 and x['legacy_process']['exit']==0
modern_server=[row['message'] for row in x['modern_transcript'] if row['direction']=='server']
assert all('id' in msg and 'method' not in msg for msg in modern_server)
modern_client=[row['message'] for row in x['modern_transcript'] if row['direction']=='client']
assert sum('params' in msg and '_meta' not in msg['params'] for msg in modern_client if 'id' in msg)==1
print('PASS: modern version/task wire controls, negative cases and legacy fallback')
