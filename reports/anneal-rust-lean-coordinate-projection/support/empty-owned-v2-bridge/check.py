#!/usr/bin/env python3
"""Offline evidence check for the one-shot owned-empty-line bridge."""
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def line_start(raw, line):
    lines = raw.splitlines(keepends=True)
    assert 0 <= line < len(lines)
    return sum(len(x) for x in lines[:line])

def utf16_to_byte(raw, line, col):
    body = raw.splitlines(keepends=True)[line].removesuffix(b'\r\n').removesuffix(b'\n')
    text = body.decode('utf-8')
    units = 0
    for index, char in enumerate(text):
        if units == col:
            return line_start(raw, line) + len(text[:index].encode())
        units += 2 if ord(char) > 0xffff else 1
        if units > col:
            raise ValueError('surrogate interior')
    if units == col:
        return line_start(raw, line) + len(body)
    raise ValueError('column past line')

def main():
    oracle_raw = (HERE/'oracle.json').read_bytes()
    o = json.loads(oracle_raw)
    r = json.loads((HERE/'results.json').read_text())
    host = (HERE/'fixture/Host.rs').read_bytes()
    v1 = (HERE/'fixture/ProjectedV1.lean').read_bytes()
    v2 = (HERE/'fixture/ProjectedV2.lean').read_bytes()
    for key, raw in [('Host.rs',host),('ProjectedV1.lean',v1),('ProjectedV2.lean',v2)]:
        assert sha(raw) == o['sha256'][key]
    assert r['oracle_prelaunch_sha256'] == sha(oracle_raw)
    assert r['fixture_sha256'] == {'host':sha(host),'original':sha(v1),'patched':sha(v2)}
    assert r['status'] == 'completed' and r['stop_reason'] is None
    assert r['rust']['status'] == 'completed' and r['rust']['exit'] == 0
    s = r['sessions']['utf16']
    assert s['status'] == 'completed' and s['exit'] == 0
    assert s['disk_sha256_after_v2'] == sha(v1)
    assert r['batch']['original']['status'] == r['batch']['patched']['status'] == 'completed'
    assert (r['batch']['original']['exit'],r['batch']['patched']['exit']) == (0,1)
    assert r['cleanup']['work_exists_after'] is False
    for record in [r['rust'],s,*r['batch'].values()]:
        assert record['samples']
        assert min(x['host']['estimated_reclaimable_percent'] for x in record['samples']) >= 20
        assert min(x['host']['free_disk_bytes'] for x in record['samples']) >= 10*1024**3
        assert max(x['scratch_bytes'] for x in record['samples']) <= 100*1024**2
        limit = 512*1024 if record is r['rust'] else 1200*1024
        assert max(x['process_group_rss_kib'] for x in record['samples']) <= limit
        assert max(x['elapsed_seconds'] for x in record['samples']) <= 30
    assert r['preflight']['host']['estimated_reclaimable_percent'] > 30
    assert r['preflight']['host']['free_disk_bytes'] > 10*1024**3
    a,b = o['owned_segments']
    assert host[a['host_start']:a['host_end']] == v1[a['projected_start']:a['projected_end']]
    assert a['projected_end'] < b['projected_start']
    assert b['host_start'] == b['host_end'] and b['projected_start'] == b['projected_end']
    assert host[b['host_start']:b['host_start']+2] == v1[b['projected_start']:b['projected_start']+2] == b'\r\n'
    assert v2 == v1[:b['projected_start']] + o['edit']['text'].encode() + v1[b['projected_start']:]
    assert utf16_to_byte(v1, 3, 0) == b['projected_start']
    assert o['points']['host_empty_insertion']['byte_offset'] == b['host_start']
    assert o['points']['projected_empty_insertion']['byte_offset'] == b['projected_start']

    def map_insert(offset, version, source_hash, projection_hash):
        if version != 1 or source_hash != sha(host) or projection_hash != sha(v1):
            raise ValueError('stale identity')
        if offset != b['projected_start']:
            raise ValueError('not the owned empty insertion')
        return b['host_start']

    assert map_insert(b['projected_start'],1,sha(host),sha(v1)) == b['host_start']
    rejected = {}
    for label, offset, version in [
        ('synthetic_header',0,1), ('synthetic_blank_line',len(b'import Lean\r\n'),1),
        ('crlf_interior',b['projected_start']+1,1),
        ('wrong_document_version',b['projected_start'],2)]:
        try: map_insert(offset,version,sha(host),sha(v1))
        except ValueError: rejected[label]=True
    try: utf16_to_byte(v1,2,9)  # after '#check "' and inside emoji's surrogate pair
    except ValueError: rejected['utf16_surrogate_interior']=True
    assert set(rejected) == set(o['negative_controls'])

    messages = [e['message'] for e in s['events']]
    edits = [m for m in messages if m.get('method')=='textDocument/didChange']
    assert len(edits)==1
    edit = edits[0]['params']
    assert edit['textDocument']['version']==2 and edit['contentChanges']==[{'range':o['edit']['range'],'text':o['edit']['text']}]
    for key,id_ in [('before',2),('after',3)]:
        response = s[key]['wait_response']
        assert response.get('id')==id_ and 'result' in response and 'method' not in response
    before = s['before']['last']
    after = s['after']['last']
    assert not any('missingEmpty' in d['message'] for d in before)
    errors = [d for d in after if 'Unknown identifier `missingEmpty`' in d['message']]
    assert len(errors)==1
    expected_range = {'start':{'line':3,'character':16},'end':{'line':3,'character':28}}
    assert errors[0]['range'] == expected_range
    batch = [json.loads(x) for x in (HERE/'raw/batch-patched.stdout').read_text().splitlines() if x.startswith('{')]
    berr = [x for x in batch if 'Unknown identifier `missingEmpty`' in x.get('data','')]
    assert len(berr)==1 and berr[0]['pos']=={'line':4,'column':15} and berr[0]['endPos']=={'line':4,'column':27}
    assert sha((HERE/'raw/batch-patched.stdout').read_bytes()) == r['batch']['patched']['stdout_sha256']
    assert sha((HERE/'raw/batch-original.stdout').read_bytes()) == r['batch']['original']['stdout_sha256']
    for tag in ['rust','batch-original','batch-patched']:
        entry = r['rust'] if tag=='rust' else r['batch'][tag.split('-',1)[1]]
        assert sha((HERE/'raw'/f'{tag}.stdout').read_bytes())==entry['stdout_sha256']
        assert sha((HERE/'raw'/f'{tag}.stderr').read_bytes())==entry['stderr_sha256']
    assert sha((HERE/'raw/utf16.client-wire').read_bytes())==s['wire_sha256']['client']
    assert sha((HERE/'raw/utf16.server-wire').read_bytes())==s['wire_sha256']['server']
    attempt = json.loads((HERE/'attempt1/results.json').read_text())
    assert attempt['status']=='completed' and attempt['sessions']['utf16']['before']['last']==[] and attempt['sessions']['utf16']['after']['last']==[]
    assert not any('missingEmpty' in d.get('message','') for event in attempt['sessions']['utf16']['events'] if event['side']=='server' and event['message'].get('method')=='textDocument/publishDiagnostics' for d in event['message']['params']['diagnostics'])
    summary = {'status':'pass','host_empty_byte':b['host_start'],'projected_empty_byte':b['projected_start'],
               'lsp_error_range':expected_range,'batch_error':{'pos':berr[0]['pos'],'endPos':berr[0]['endPos']},
               'negative_controls':rejected,'first_attempt':'excluded_protocol_harness_fault',
               'peaks_kib':{key:max(x['process_group_rss_kib'] for x in val['samples']) for key,val in [('rust',r['rust']),('server',s),*r['batch'].items()]}}
    if len(sys.argv)>1 and sys.argv[1]=='--write-comparison':
        (HERE/'comparison.json').write_text(json.dumps(summary,indent=2,ensure_ascii=False)+'\n')
    else:
        assert json.loads((HERE/'comparison.json').read_text())==summary
    print(json.dumps(summary,ensure_ascii=False))

if __name__=='__main__':
    main()
