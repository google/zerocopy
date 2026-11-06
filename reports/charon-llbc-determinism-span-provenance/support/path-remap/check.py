#!/usr/bin/env python3
"""Offline verification of retained raw rustc JSON and Charon LLBC evidence."""
import copy, hashlib, json, re
from pathlib import Path

HERE=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def load(name):return json.loads((HERE/name).read_text())
def decoded(raw):
    d=json.loads(raw);tr=d['translated']
    files=[{'id':f['id'],'name':f['name'],'crate_name':f['crate_name'],'contents':f['contents'],
            'contents_sha256':sha(f['contents'].encode()) if f['contents'] is not None else None} for f in tr['files']]
    items=[]
    for kind,decls in (('function',tr['fun_decls']),('global',tr['global_decls']),('type',tr['type_decls'])):
        for decl in decls:
            m=decl.get('item_meta',{})
            if not m.get('is_local'):continue
            name='::'.join(p['Ident'][0] for p in m['name'] if 'Ident' in p)
            items.append({'kind':kind,'def_id':decl.get('def_id'),'name':name,'file_id':m['span']['data']['file_id'],
                          'span':m['span'],'source_text':m.get('source_text')})
    return {'sha256':sha(raw),'bytes':len(raw),'has_errors':d['has_errors'],'crate_name':tr['crate_name'],
            'dest_file':tr['options']['dest_file'],'files':files,'local_items':items,'item_names':tr['item_names']}
def diff(x,y,path='$'):
    if type(x)!=type(y):return [(path,'type')]
    if isinstance(x,dict):
        out=[]
        for key in sorted(set(x)|set(y)):
            out+=([(path+'.'+key,'missing')] if key not in x or key not in y else diff(x[key],y[key],path+'.'+key))
        return out
    if isinstance(x,list):
        if len(x)!=len(y):return [(path,'length')]
        return [z for i,(a,b) in enumerate(zip(x,y)) for z in diff(a,b,f'{path}[{i}]')]
    return [] if x==y else [(path,'value')]
def typed_short_names(doc):
    return {json.dumps(x['key'],sort_keys=True):x['value'] for x in doc['translated']['short_names']}
def diagnostic_filename(label,token):
    lines=(HERE/'raw'/f'{label}.stderr').read_text().splitlines()
    entries=[json.loads(line) for line in lines if line.startswith('{')]
    hits=[d for d in entries if token in d.get('message','')]
    assert len(hits)==1 and len(hits[0]['spans'])==1
    return hits[0]['spans'][0]['file_name']
def main():
    o=load('oracle.json');r=load('results.json')
    assert sha((HERE/'oracle.json').read_bytes())==r['oracle_prelaunch_sha256']
    assert {n:sha((HERE/'fixture'/n).read_bytes()) for n in o['fixture_sha256']}==o['fixture_sha256']
    assert r['status']=='completed' and r['stop_reason'] is None and not r['cleanup']['work_exists_after']
    assert list(r['runs'])==['rustc_plain','rustc_remap','charon_plain','charon_remap']
    assert all(x['status']=='completed' and x['stop_reason'] is None for x in r['runs'].values())
    assert [r['runs'][k]['exit'] for k in r['runs']]==[1,1,0,0]
    lim=r['limits']
    for k,x in r['runs'].items():
        assert x['preflight']['host']['estimated_reclaimable_percent']>lim['minimum_start_reclaimable_percent']
        assert x['preflight']['host']['free_disk_bytes']>lim['minimum_disk_bytes']
        assert x['postrun_group_rss_kib']==0
        assert x['samples']
        for s in x['samples']:
            assert s['host']['estimated_reclaimable_percent']>=lim['minimum_live_reclaimable_percent']
            assert s['host']['free_disk_bytes']>=lim['minimum_disk_bytes']
            assert s['process_group_rss_kib']<=lim['maximum_process_group_rss_kib']
            assert s['scratch_kib']<=lim['maximum_scratch_kib']
            assert s['elapsed_seconds']<=lim['timeout_seconds_per_process']
        for ext in ('stdout','stderr'):
            assert sha((HERE/'raw'/f'{k}.{ext}').read_bytes())==x[f'{ext}_sha256']
    token=o['diagnostic_token']
    plain_file=diagnostic_filename('rustc_plain',token)
    remap_file=diagnostic_filename('rustc_remap',token)
    assert plain_file=='src/error.rs'
    assert remap_file==o['expected_remapped_error_filename']
    assert r['runs']['rustc_remap']['argv'][-2:]==[o['remap_flag'],'src/error.rs']
    assert o['remap_flag'] not in r['runs']['rustc_plain']['argv']
    stderr_plain=(HERE/'raw'/'charon_plain.stderr').read_text()
    stderr_remap=(HERE/'raw'/'charon_remap.stderr').read_text()
    assert o['remap_flag'] not in stderr_plain
    assert re.search(r'Running `[^\n]*'+re.escape(o['remap_flag'])+r'[^\n]*`',stderr_remap)
    assert r['runs']['charon_remap']['environment']['RUSTFLAGS']==o['remap_flag']
    assert r['runs']['charon_plain']['environment']['RUSTFLAGS'] is None
    docs={}
    for k in ('charon_plain','charon_remap'):
        raw=(HERE/'artifacts'/f'{k}.llbc').read_bytes()
        x=r['runs'][k]
        assert x['dest_exists'] and decoded(raw)==x['decoded']
        assert x['decoded']['dest_file']==x['argv'][x['argv'].index('--dest-file')+1]
        assert x['decoded']['has_errors'] is False
        docs[k]=json.loads(raw)
    a,b=docs.values()
    observed=diff(a,b)
    expected=['$.translated.options.dest_file',
              '$.translated.short_names[0].value[0].Ident[0]',
              '$.translated.short_names[0].key.Fun',
              '$.translated.short_names[2].value[0].Ident[0]',
              '$.translated.short_names[2].key.Fun']
    assert sorted(p for p,_ in observed)==sorted(expected),(observed,expected)
    assert typed_short_names(a)==typed_short_names(b)
    files=r['runs']['charon_plain']['decoded']['files']
    assert r['runs']['charon_remap']['decoded']['files']==files
    assert [(f['id'],f['name']) for f in files[:3]]==[(i,{'Local':name}) for i,name in enumerate(o['expected_local_files'])]
    assert [f['contents_sha256'] for f in files[:3]]==[o['fixture_sha256'][p] for p in o['expected_local_files']]
    items=r['runs']['charon_plain']['decoded']['local_items']
    assert r['runs']['charon_remap']['decoded']['local_items']==items
    assert {i['name']:i['file_id'] for i in items}=={'symlink_module_probe::combine':0,
     'symlink_module_probe::left::step':1,'symlink_module_probe::right::step':2}
    # In-memory negative controls: a remapped LLBC filename and switched item ownership fail the exact assertions.
    bad=copy.deepcopy(files);bad[1]['name']={'Local':'/virtual/anneal-src/left/common.rs'}
    assert bad!=files
    wrong=copy.deepcopy(items);wrong[-1]['file_id']=1
    assert wrong!=items
    summary={'status':'PASS','rustc_diagnostic_paths':{'plain':plain_file,'remap':remap_file},
      'charon_driver_remap_flag_observed':True,'charon_local_file_paths':[f['name'] for f in files[:3]],
      'charon_local_item_file_ids':{i['name']:i['file_id'] for i in items},
      'raw_llbc_differing_leaf_paths':sorted(p for p,_ in observed),
      'typed_short_names_equal':True,'negative_controls':['remapped_llbc_file_path','switched_item_file_id']}
    (HERE/'comparison.json').write_text(json.dumps(summary,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps(summary))
if __name__=='__main__':main()
