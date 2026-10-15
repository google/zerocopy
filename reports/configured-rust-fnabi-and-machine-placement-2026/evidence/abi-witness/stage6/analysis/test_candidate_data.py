from pathlib import Path
import sys,json,copy,subprocess,os
out=Path(__file__).resolve().parent;root=out.parents[1]
sys.dont_write_bytecode=True
launches=[]
def trap(*a,**kw):launches.append(str(a));raise RuntimeError('PROCESS LAUNCH FORBIDDEN')
subprocess.Popen=trap;os.system=trap;os.posix_spawn=trap;os.posix_spawnp=trap
sys.path.insert(0,str(root/'stage5'));import e33_data_windows as D
req=D.load_request(root,'windows-subjects-opt2');raw=(root/'stage5/windows-runs/capture-subjects-o2-01/reference.json').read_bytes();base=D.parse(raw)
rows={r['selection']['path'].split('::')[-1]:i for i,r in enumerate(base['selected'])}
cases=[]
def add(name,mut,path):
 x=copy.deepcopy(base);mut(x);cases.append((name,x,path))
add('stale-target',lambda x:x.__setitem__('target_triple_debug','TargetTuple("aarch64-apple-darwin")'),'target_triple_debug')
add('stale-generic-instance',lambda x:x['selected'][20]['selection'].__setitem__('type_args',['u64']),'selected/20/selection/type_args')
i=rows['abi_c_big'];add('hidden-result-size',lambda x:x['selected'][i]['fn_abi']['ret']['mode']['attrs'].__setitem__('pointee_size_bytes',16),f'selected/{i}/fn_abi/ret/mode/attrs/pointee_size_bytes')
i=rows['abi_track'];add('omit-hidden-caller',lambda x:x['selected'][i]['fn_abi']['args'].pop(),f'selected/{i}/fn_abi/args/1')
i=next(i for i,r in enumerate(base['selected']) if r['selection']['path'].endswith('VarC') and r['selection']['extra_args']);add('omit-variadic-extra',lambda x:x['selected'][i]['fn_abi']['args'].pop(),f'selected/{i}/fn_abi/args/3')
add('change-selected-variadic-extra',lambda x:x['selected'][i]['selection']['extra_args'].__setitem__(1,'u64'),f'selected/{i}/selection/extra_args/1')
i=rows['abi_c_narrow'];add('narrow-extension',lambda x:x['selected'][i]['fn_abi']['args'][0]['mode']['attrs'].__setitem__('extension','None'),f'selected/{i}/fn_abi/args/0/mode/attrs/extension')
i=rows['abi_shared'];add('reference-attribute-bits',lambda x:x['selected'][i]['fn_abi']['args'][0]['mode']['attrs'].__setitem__('regular_bits',128),f'selected/{i}/fn_abi/args/0/mode/attrs/regular_bits')
add('opaque-layout',lambda x:x['selected'][i]['fn_abi']['args'][0]['layout'].__setitem__('full_layout_debug',x['selected'][i]['fn_abi']['args'][0]['layout']['full_layout_debug']+' changed'),f'selected/{i}/fn_abi/args/0/layout/full_layout_debug')
add('opaque-target',lambda x:x.__setitem__('target_spec_debug',x['target_spec_debug']+' changed'),'target_spec_debug')
results=[]
D.compare_data(raw,raw,req)
for name,x,path in cases:
 b=(json.dumps(x,indent=2)+'\n').encode();(out/(name+'.json')).write_bytes(b)
 try:D.validate_observation(D.parse(b),req);grammar='pass'
 except D.Reject as e:grammar='reject: '+str(e)
 try:D.compare_data(b,raw,req)
 except D.Reject as e:results.append({'name':name,'changed_path':path,'grammar':grammar,'comparison':'reject','reason':str(e)})
 else:raise AssertionError('mutant accepted: '+name)
assert not launches
(out/'candidate-data-results.json').write_text(json.dumps({'scope':'Offline comparison to retained actual capture only, NOT fresh compiler acceptance/check. No consumer check invoked.','positive_equal':1,'mutant_rejections':results,'process_launch_attempts':launches},indent=2)+'\n')
print('offline positive 1; mutant rejections '+str(len(results))+'; launch attempts 0')
