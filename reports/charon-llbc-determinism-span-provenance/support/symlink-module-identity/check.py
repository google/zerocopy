#!/usr/bin/env python3
"""Offline Charon lexical-alias/file-ID comparison with negative controls."""
import copy
import hashlib
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
def sha(raw):return hashlib.sha256(raw).hexdigest()
def short_map(doc):
    return {json.dumps(x['key'],sort_keys=True):json.dumps(x['value'],sort_keys=True,ensure_ascii=False)
            for x in doc['translated']['short_names']}
def different(a,b,path=''):
    if type(a)!=type(b):yield path;return
    if isinstance(a,dict):
        for k in sorted(set(a)|set(b)):
            if k not in a or k not in b:yield path+'/'+k
            else:yield from different(a[k],b[k],path+'/'+k)
    elif isinstance(a,list):
        if len(a)!=len(b):yield path+'/length'
        for i,(x,y) in enumerate(zip(a,b)):yield from different(x,y,path+f'/{i}')
    elif a!=b:yield path

def main():
    oracle_raw=(HERE/'oracle.json').read_bytes();o=json.loads(oracle_raw)
    r=json.loads((HERE/'results.json').read_text())
    assert r['oracle_prelaunch_sha256']==sha(oracle_raw)
    assert r['status']=='completed' and r['stop_reason'] is None
    assert r['cleanup']['work_exists_after'] is False
    assert r['initial_preflight']['host']['estimated_reclaimable_percent']>30
    assert r['initial_preflight']['host']['free_disk_bytes']>10*1024**3
    for name,h in o['fixture_sha256'].items():
        assert sha((HERE/'fixture'/name).read_bytes())==h
    source=bytes.fromhex(o['shared_source_hex'])
    assert sha(source)==o['fixture_sha256']['src/shared.rs']
    a,b=r['layouts']['alias']['entries'],r['layouts']['copy']['entries']
    for entries,expected_link in ((a,True),(b,False)):
        assert [x['relative_path'] for x in entries]==o['module_relative_paths']
        assert all(x['is_symlink']==expected_link for x in entries)
        assert all(x['source_sha256']==sha(source) for x in entries)
    assert a[0]['target_dev']==a[1]['target_dev'] and a[0]['target_inode']==a[1]['target_inode']
    assert a[0]['resolved_path']==a[1]['resolved_path']
    assert all(x['link_text']==o['alias_target'] for x in a)
    assert b[0]['target_dev']==b[1]['target_dev'] and b[0]['target_inode']!=b[1]['target_inode']
    assert all(x['link_text'] is None for x in b)
    decoded={}
    for kind in ('alias','copy'):
        run=r['runs'][kind]
        assert run['status']=='completed' and run['exit']==0 and run['stop_reason'] is None
        assert run['postrun_group_rss_kib']==0
        assert run['preflight']['host']['estimated_reclaimable_percent']>30
        assert run['preflight']['host']['free_disk_bytes']>10*1024**3
        assert run['samples']
        assert min(x['host']['estimated_reclaimable_percent'] for x in run['samples'])>=20
        assert min(x['host']['free_disk_bytes'] for x in run['samples'])>=10*1024**3
        assert max(x['process_group_rss_kib'] for x in run['samples'])<=512*1024
        assert max(x['scratch_kib'] for x in run['samples'])<=100*1024
        assert max(x['elapsed_seconds'] for x in run['samples'])<=15
        for suffix in ('stdout','stderr'):
            assert sha((HERE/'raw'/f'{kind}.{suffix}').read_bytes())==run[f'{suffix}_sha256']
        path=HERE/'artifacts'/f'{kind}.llbc';raw=path.read_bytes();doc=json.loads(raw)
        assert sha(raw)==run['decoded']['sha256']
        assert run['decoded']['bytes']==len(raw)
        raw_files=[{'id':f['id'],'name':f['name'],'crate_name':f['crate_name'],
                    'contents':f['contents'],
                    'contents_sha256':sha(f['contents'].encode()) if f['contents'] is not None else None}
                   for f in doc['translated']['files']]
        assert run['decoded']['files']==raw_files
        raw_items=[]
        for type_name,decls in (('function',doc['translated']['fun_decls']),
                                ('global',doc['translated']['global_decls']),
                                ('type',doc['translated']['type_decls'])):
            for decl in decls:
                meta=decl.get('item_meta',{})
                if not meta.get('is_local'):continue
                raw_items.append({'kind':type_name,'def_id':decl.get('def_id'),
                    'name':'::'.join(part['Ident'][0] for part in meta['name'] if 'Ident' in part),
                    'file_id':meta['span']['data']['file_id'],'span':meta['span'],
                    'source_text':meta.get('source_text')})
        assert run['decoded']['local_items']==raw_items
        assert run['decoded']['item_names']==doc['translated']['item_names']
        assert run['decoded']['has_errors'] is False and doc['has_errors'] is False
        assert run['decoded']['crate_name']==doc['translated']['crate_name']=='symlink_module_probe'
        assert run['argv'][4]=='--dest-file' and run['decoded']['dest_file']==run['argv'][5]
        local_files={f['id']:f for f in run['decoded']['files'] if f['crate_name']=='symlink_module_probe'}
        assert list(local_files)==[0,1,2]
        assert local_files[0]['name']=={'Local':'src/lib.rs'}
        assert local_files[0]['contents_sha256']==o['fixture_sha256']['src/lib.rs']
        for id_,rel in ((1,'src/left/common.rs'),(2,'src/right/common.rs')):
            f=local_files[id_]
            assert f['name']=={'Local':rel} and f['contents']==source.decode('utf-8')
            assert f['contents_sha256']==sha(source)
        items={x['name']:x for x in run['decoded']['local_items']}
        assert set(items)=={'symlink_module_probe::combine',*o['expected_logical_names']}
        assert items['symlink_module_probe::combine']['file_id']==0
        for name,id_ in zip(o['expected_logical_names'],(1,2)):
            assert items[name]['file_id']==id_ and items[name]['source_text'] in source.decode('utf-8')
            assert items[name]['span']['data']['file_id']==id_
        decoded[kind]=doc
    assert decoded['alias']['translated']['files']==decoded['copy']['translated']['files']
    assert decoded['alias']['translated']['item_names']==decoded['copy']['translated']['item_names']
    assert short_map(decoded['alias'])==short_map(decoded['copy'])
    differences=list(different(decoded['alias'],decoded['copy']))
    assert differences and all(p=='/translated/options/dest_file' or p.startswith('/translated/short_names/') for p in differences)
    assert len(differences)==7 and '/translated/options/dest_file' in differences
    invalid=copy.deepcopy(decoded['alias'])
    invalid['translated']['files'][2]['name']={'Local':'src/left/common.rs'}
    assert invalid['translated']['files']!=decoded['copy']['translated']['files']
    invalid=copy.deepcopy(decoded['alias'])
    for decl in invalid['translated']['fun_decls']:
        if decl['item_meta']['is_local'] and any(part.get('Ident',[''])[0]=='right' for part in decl['item_meta']['name']):
            decl['item_meta']['span']['data']['file_id']=1
    assert list(different(invalid,decoded['copy']))!=differences
    summary={'status':'pass','same_inode_aliases':True,'distinct_inode_copies':True,
             'alias_local_file_ids':[0,1,2],'copy_local_file_ids':[0,1,2],
             'item_file_ids':{name:id_ for name,id_ in zip(o['expected_logical_names'],(1,2))},
             'decoded_difference_paths':differences,
             'negative_controls':['duplicate_file_path','wrong_right_item_file_id'],
             'sampled_peak_rss_kib':{kind:max(s['process_group_rss_kib'] for s in r['runs'][kind]['samples']) for kind in ('alias','copy')}}
    if len(sys.argv)>1 and sys.argv[1]=='--write-comparison':
        (HERE/'comparison.json').write_text(json.dumps(summary,indent=2,ensure_ascii=False)+'\n')
    else:assert json.loads((HERE/'comparison.json').read_text())==summary
    print(json.dumps(summary,ensure_ascii=False))

if __name__=='__main__':main()
