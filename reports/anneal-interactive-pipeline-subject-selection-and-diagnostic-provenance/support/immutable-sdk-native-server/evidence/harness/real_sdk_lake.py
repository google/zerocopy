"""Scratch-only immutable sysroot overlay; no installed toolchain is modified."""
import json,os,stat,shutil
from pathlib import Path
from probes import *
from sdk_probe import LIBS

SDK=ROOT/'sdk-install'
def prepare():
    SDK.mkdir(exist_ok=True)
    for p in RC2.iterdir():
        if p.name=='lib':continue
        if not (SDK/p.name).is_symlink():
            (SDK/p.name).symlink_to(p,target_is_directory=p.is_dir())
    (SDK/'lib/lean').mkdir(parents=True,exist_ok=True)
    for p in (RC2/'lib').iterdir():
        if p.name=='lean':continue
        if not (SDK/'lib'/p.name).is_symlink():
            (SDK/'lib'/p.name).symlink_to(p,target_is_directory=p.is_dir())
    providers=[RC2/'lib/lean',*LIBS]
    sources={}
    for provider in providers:
        if not provider.is_dir():continue
        for p in provider.iterdir():
            target=SDK/'lib/lean'/p.name
            if target.exists() or target.is_symlink():
                if target.resolve()!=p.resolve():
                    raise RuntimeError(f'Duplicate artifact provider: {p.name}: {target.resolve()} versus {p}')
            else:
                target.symlink_to(p,target_is_directory=p.is_dir())
                sources[p.name]=str(p)
    (SDK/'providers.json').write_text(json.dumps(sources,indent=2)+'\n')
    for p in [SDK/'providers.json',SDK/'lib/lean',SDK/'lib',SDK]:
        p.chmod(stat.S_IMODE(p.stat().st_mode)&~0o222)
    print('SDK_OVERLAY_READY',len(sources),'top-level symlinks',flush=True)
def env(case):
    e=environment(RC2,case,immutable=f'{SDK}:{AENEAS}:{RC2}')
    e['LEAN_SYSROOT']=str(SDK)
    e['LAKE_OVERRIDE_LEAN']='true'
    e['PATH']=str(SDK/'bin')+':'+e['PATH']
    return e
def invoke(case,args,w,rss_mib=3072,admission_memory_pct=30):
    binary=SDK/'bin/lean' if args[0]=='lean' else RC2/'bin'/args[0]
    r=run(case,[str(binary),*args[1:]],w,env(case),timeout=120,rss_mib=rss_mib,admission_memory_pct=admission_memory_pct,memory_floor_pct=25)
    p=ROOT/'records'/(case+'.events.jsonl')
    events=[json.loads(l) for l in p.read_text().splitlines()] if p.exists() else []
    c={'case':case,'exit':r['exit'],'abort':r['abort'],'elapsed_s':r['elapsed_s'],'shared_attempts':[e for e in events if e['kind']=='mutation' and e['blocked']],'network_attempts':[e for e in events if e['kind']=='network'],'loads':[e for e in events if e['kind']=='load'],'events':len(events)}
    with (ROOT/'cells.jsonl').open('a') as f:f.write(json.dumps(c)+'\n')
    print('REAL_SDK',json.dumps(c),flush=True)
    return c
def workspace(name):
    w=fixture(name,seed=False)
    lakefile=w/'lakefile.lean'
    lakefile.write_text(lakefile.read_text().replace(f'require aeneas from "{BACKEND}"\n',''))
    # Experimental SDK identity enters the normal local-module import trace.
    (w/'anneal/SdkIdentity.lean').write_text('def annealSdkIdentity : String := "b4e0a5b420eb441e37564c365f06c215f61a3b825fc3df37293da7c3010d2b81"\n')
    lakefile.write_text(lakefile.read_text().replace('roots := #[`Config, `Anneal]','roots := #[`Config, `SdkIdentity, `Anneal]'))
    for p in [w/'anneal/Config.lean',w/'anneal/Anneal.lean',w/f'generated/{SLUG}/Types.lean',w/f'generated/{SLUG}/Funs.lean',w/'generated/Generated.lean']:
        p.write_text('import SdkIdentity\n'+p.read_text())
    return w
def build(w,label):
    for module in ['SdkIdentity','Config',SLUG+'.Types',SLUG+'.Funs','Anneal','Generated']:
        c=invoke(label+'-'+module,['lake','--keep-toolchain','--no-cache','--verbose','build','+'+module+':olean'],w)
        if c['exit']!=0:return False
    return True
if __name__=='__main__':
    if not SDK.exists():prepare()
    before=snapshot('real-sdk-before',content=True)
    sdk_before=snapshot('real-sdk-overlay-before',root=SDK,content=True)
    w=workspace('real-sdk-a')
    invoke('real-sdk-prefix',['lean','--print-prefix'],w)
    if build(w,'real-sdk-a-build'):
        invoke('real-sdk-a-noop',['lake','--keep-toolchain','--no-cache','--verbose','build','Generated','Anneal'],w)
        spec=(w/f'generated/{SLUG}/Specs.lean').read_text()
        (w/'Audit.lean').write_text(spec+'\n#print axioms expand_output.foo.spec\n')
        invoke('real-sdk-a-positive',['lake','--keep-toolchain','--no-cache','env','lean','--json','Audit.lean'],w)
        invoke('real-sdk-a-setup',['lake','--keep-toolchain','--no-cache','setup-file','Audit.lean','-'],w)
    after=snapshot('real-sdk-after',content=True)
    sdk_after=snapshot('real-sdk-overlay-after',root=SDK,content=True)
    assert before==after and sdk_before==sdk_after
