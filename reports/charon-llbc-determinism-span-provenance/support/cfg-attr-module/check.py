#!/usr/bin/env python3
"""Offline verifier for corrected cfg_attr(path) Charon LLBC pair."""
import copy,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads((HERE/p).read_text())
def decode(raw):
    doc=json.loads(raw);tr=doc['translated']
    files=[{'id':f['id'],'name':f['name'],'crate_name':f['crate_name'],'contents':f['contents'],
            'contents_sha256':sha(f['contents'].encode()) if f['contents'] is not None else None} for f in tr['files']]
    items=[]
    for kind,decls in (('function',tr['fun_decls']),('global',tr['global_decls']),('type',tr['type_decls'])):
        for d in decls:
            m=d.get('item_meta',{})
            if not m.get('is_local'):continue
            name='::'.join(p['Ident'][0] for p in m['name'] if 'Ident' in p)
            items.append({'kind':kind,'def_id':d.get('def_id'),'name':name,'file_id':m['span']['data']['file_id'],
                          'span':m['span'],'source_text':m.get('source_text')})
    return {'sha256':sha(raw),'bytes':len(raw),'has_errors':doc['has_errors'],'crate_name':tr['crate_name'],
            'dest_file':tr['options']['dest_file'],'files':files,'local_items':items,'item_names':tr['item_names']}
def diff(x,y,path='$'):
    if type(x)!=type(y):return [path]
    if isinstance(x,dict):
        return [z for k in sorted(set(x)|set(y)) for z in
                ([path+'.'+k] if k not in x or k not in y else diff(x[k],y[k],path+'.'+k))]
    if isinstance(x,list):
        if len(x)!=len(y):return [path]
        return [z for i,(a,b) in enumerate(zip(x,y)) for z in diff(a,b,f'{path}[{i}]')]
    return [] if x==y else [path]
def check_selection(label,projection,oracle):
    spec=oracle['runs'][label]
    files=projection['files'];assert len(files)>=2
    assert [(f['id'],f['name']) for f in files[:2]]==[(0,{'Local':'src/lib.rs'}),(1,{'Local':spec['selected_file']})]
    assert all(f['name']!={'Local':spec['excluded_file']} for f in files)
    assert files[0]['contents_sha256']==oracle['fixture_sha256']['src/lib.rs']
    assert files[1]['contents_sha256']==oracle['fixture_sha256'][spec['selected_file']]
    items=projection['local_items'];m={i['name']:i for i in items}
    assert set(m)=={'cfg_attr_module_probe::read',oracle['logical_item_name']}
    assert m['cfg_attr_module_probe::read']['file_id']==0
    marker=m[oracle['logical_item_name']]
    assert marker['file_id']==1
    assert marker['span']['data']=={'file_id':1,'beg':{'line':1,'col':0},'end':{'line':1,'col':29}}
    assert marker['source_text']==f"pub fn marker() -> u32 {{ {spec['marker_literal']} }}"
    return marker
def main():
    o=load('oracle.json');r=load('results.json')
    assert sha((HERE/'oracle.json').read_bytes())==r['oracle_prelaunch_sha256']
    assert {n:sha((HERE/'fixture'/n).read_bytes()) for n in o['fixture_sha256']}==o['fixture_sha256']
    assert r['status']=='completed' and r['stop_reason'] is None and r['cleanup']=={'work_exists_after':False}
    assert list(r['runs'])==['default','alternate']
    assert o['runs']['default']['cargo_flags']==['--no-default-features']
    assert o['runs']['alternate']['cargo_flags']==['--no-default-features','--features','alternate']
    lim=r['limits'];docs={};projections={}
    for label,spec in o['runs'].items():
        x=r['runs'][label]
        assert x['status']=='completed' and x['stop_reason'] is None and x['exit']==0
        assert x['preflight']['host']['estimated_reclaimable_percent']>lim['minimum_start_reclaimable_percent']
        assert x['preflight']['host']['free_disk_bytes']>lim['minimum_disk_bytes']
        assert x['postrun_group_rss_kib']==0 and x['samples']
        for s in x['samples']:
            assert s['host']['estimated_reclaimable_percent']>=lim['minimum_live_reclaimable_percent']
            assert s['host']['free_disk_bytes']>=lim['minimum_disk_bytes']
            assert s['process_group_rss_kib']<=lim['maximum_process_group_rss_kib']
            assert s['scratch_kib']<=lim['maximum_scratch_kib']
            assert s['elapsed_seconds']<=lim['timeout_seconds_per_process']
        assert x['argv'][-len(spec['cargo_flags']):]==spec['cargo_flags']
        for ext in ('stdout','stderr'):
            assert sha((HERE/'raw'/f'{label}.{ext}').read_bytes())==x[f'{ext}_sha256']
        stderr=(HERE/'raw'/f'{label}.stderr').read_text()
        driver=[line for line in stderr.splitlines() if 'Running `' in line and 'charon-driver rustc' in line]
        assert len(driver)==1
        assert ('--cfg \'feature="alternate"\'' in driver[0])==(label=='alternate')
        assert '--cfg \'feature="default"\'' not in driver[0]
        raw=(HERE/'artifacts'/f'{label}.llbc').read_bytes();proj=decode(raw)
        assert x['dest_exists'] and x['decoded']==proj
        assert proj['dest_file']==x['argv'][x['argv'].index('--dest-file')+1]
        assert proj['has_errors'] is False
        check_selection(label,proj,o)
        docs[label]=json.loads(raw);projections[label]=proj
    marker_default=check_selection('default',projections['default'],o)
    marker_alternate=check_selection('alternate',projections['alternate'],o)
    assert marker_default['name']==marker_alternate['name']
    assert marker_default['span']==marker_alternate['span']
    leaves=sorted(diff(docs['default'],docs['alternate']))
    expected=sorted(['$.translated.files[1].contents','$.translated.files[1].name.Local',
      '$.translated.fun_decls[1].body.Structured.body.statements[0].kind.Assign[1].Use[0].Const.kind.Literal.Scalar.Unsigned[1]',
      '$.translated.fun_decls[1].item_meta.source_text','$.translated.options.dest_file'])
    assert leaves==expected,(leaves,expected)
    # Negative controls exercise the same selection oracle against in-memory mutations.
    bad=copy.deepcopy(projections['alternate']);bad['files'][1]['name']={'Local':'src/default.rs'}
    try:check_selection('alternate',bad,o);assert False,'wrong selected file was accepted'
    except AssertionError as e:
        assert str(e)!='wrong selected file was accepted'
    bad=copy.deepcopy(projections['alternate']);bad['local_items'][1]['file_id']=0
    try:check_selection('alternate',bad,o);assert False,'wrong marker ownership was accepted'
    except AssertionError as e:
        assert str(e)!='wrong marker ownership was accepted'
    preliminary=load('preliminary/results.json')
    assert preliminary['status']=='completed'
    assert preliminary['runs']['alternate']['argv'][-2:]==['--features','alternate']
    assert sha((HERE/'preliminary/results.json').read_bytes())!=sha((HERE/'results.json').read_bytes())
    summary={'status':'PASS','corrected_pair_only':True,'preliminary_excluded':True,
      'selected_files':{k:v['files'][1]['name'] for k,v in projections.items()},
      'marker_file_id':1,'marker_name':o['logical_item_name'],
      'differing_leaf_paths':leaves,'negative_controls':['wrong_selected_file','wrong_item_file_id']}
    (HERE/'comparison.json').write_text(json.dumps(summary,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps(summary))
if __name__=='__main__':main()
