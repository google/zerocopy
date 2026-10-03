"""Masked read-only SDK failures, with no artifact content duplicated."""
import json,shutil,stat
from native_lake import plugin_config
from real_sdk_lake import SDK,RC2,ROOT,AENEAS,env
from probes import snapshot
from guard import run

VIEW=ROOT/'sdk-missing'
def prepare():
    VIEW.mkdir(exist_ok=False)
    for p in SDK.iterdir():
        if p.name not in ('bin','lib'):
            (VIEW/p.name).symlink_to(p,target_is_directory=p.is_dir())
    (VIEW/'bin').mkdir()
    for p in (SDK/'bin').iterdir():
        dst=VIEW/'bin'/p.name
        if p.name in ('lean','lake'):
            shutil.copyfile(p.resolve(),dst);dst.chmod(0o555)
        else:dst.symlink_to(p)
    (VIEW/'lib/lean').mkdir(parents=True)
    for p in (SDK/'lib').iterdir():
        if p.name!='lean':(VIEW/'lib'/p.name).symlink_to(p,target_is_directory=p.is_dir())
    for p in (SDK/'lib/lean').iterdir():
        if p.name!='Aeneas.olean':(VIEW/'lib/lean'/p.name).symlink_to(p,target_is_directory=p.is_dir())
    for p in [VIEW/'bin',VIEW/'lib/lean',VIEW/'lib',VIEW]:p.chmod(0o555)
    w=ROOT/'work/sdk-missing';w.mkdir(exist_ok=False)
    (w/'lean-toolchain').write_text('leanprover/lean4:v4.30.0-rc2\n')
    (w/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage missing_sdk\n@[default_target] lean_lib Missing\n')
    (w/'Missing.lean').write_text('import Aeneas\nexample : True := by trivial\n')
    n=ROOT/'work/sdk-missing-native';n.mkdir(exist_ok=False)
    (n/'lean-toolchain').write_text('leanprover/lean4:v4.30.0-rc2\n')
    from native_lake import PLUGIN,SMOKE
    (n/'lakefile.lean').write_text(plugin_config('missing_native_sdk','@[default_target] lean_lib Smoke\n').replace(str(PLUGIN),str(VIEW/'lib/missing-prebuilt.dylib')))
    (n/'Smoke.lean').write_text(SMOKE)

def invoke(label,w,args):
    e=env(label);e['LEAN_SYSROOT']=str(VIEW);e['PATH']=str(VIEW/'bin')+':'+e['PATH'];e['PROBE_IMMUTABLE_ROOTS']=f'{VIEW}:{SDK}:{AENEAS}:{RC2}'
    r=run(label,[str(VIEW/'bin/lake'),'--keep-toolchain','--no-cache','--verbose',*args],w,e,timeout=60,rss_mib=2048,admission_memory_pct=30,memory_floor_pct=25)
    events=[json.loads(x) for x in (ROOT/'records'/(label+'.events.jsonl')).read_text().splitlines()]
    c={'case':label,'exit':r['exit'],'abort':r['abort'],'elapsed_s':r['elapsed_s'],'shared_attempts':[x for x in events if x['kind']=='mutation' and x['blocked']],'network_attempts':[x for x in events if x['kind']=='network'],'loads':[x for x in events if x['kind']=='load'],'events':len(events)}
    with (ROOT/'cells.jsonl').open('a') as f:f.write(json.dumps(c)+'\n')
    print('MASKED_SDK',json.dumps(c),flush=True)
    assert r['exit']==1 and r['abort'] is None and not c['shared_attempts'] and not c['network_attempts'],c

if __name__=='__main__':
    if not VIEW.exists():prepare()
    before=snapshot('masked-sdk-before',root=VIEW,content=True)
    invoke('sdk-missing-stock-lake',ROOT/'work/sdk-missing',['build','+Missing:olean'])
    invoke('sdk-missing-native-stock-lake',ROOT/'work/sdk-missing-native',['build','+Smoke:olean'])
    after=snapshot('masked-sdk-after',root=VIEW,content=True)
    assert before==after
