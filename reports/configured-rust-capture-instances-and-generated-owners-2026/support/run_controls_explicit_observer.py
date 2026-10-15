"""Create caller selections, produce observations, then test untrusted candidates serially."""
from pathlib import Path
import argparse,copy,hashlib,json,os,subprocess,sys,time
from packet_schema import load,semantic

ROOT=Path(__file__).resolve().parent
ARGUMENTS=argparse.ArgumentParser();ARGUMENTS.add_argument('--toolchain',type=Path,required=True);ARGUMENTS.add_argument('--observer',type=Path,required=True);ARGUMENTS.add_argument('--matrix',default='final-matrix');ARGS=ARGUMENTS.parse_args()
TOOL=ARGS.toolchain.resolve(strict=True)
OBSERVER=ARGS.observer.absolute()
CASE_ROOT=ROOT/ARGS.matrix
BASE=load(ROOT/'requests/base/request.json')
SOURCE=(ROOT/'requests/base/probe.rs').read_text()
RESULTS=[]

def dump(path,value):
    with path.open('x') as f:json.dump(value,f,indent=2);f.write('\n')
def select(name,text,**changes):
    directory=CASE_ROOT/'requests'/name;directory.mkdir(parents=True);(directory/'probe.rs').write_text(text)
    request=copy.deepcopy(BASE);request.update(changes);request['files']=[{'path':'probe.rs','sha256':hashlib.sha256(text.encode()).hexdigest()}]
    dump(directory/'request.json',request);return directory/'request.json'
def invoke(label,action,request,candidate=None,expected=0):
    out=CASE_ROOT/'controls'/label;out.parent.mkdir(exist_ok=True)
    argv=[sys.executable,'-B',str(ROOT/'capture.py'),action,'--request',str(request),'--toolchain',str(TOOL),'--observer',str(OBSERVER),'--output',str(out)]
    if candidate is not None:argv.extend(['--candidate',str(candidate)])
    before=time.monotonic_ns();p=subprocess.run(argv,cwd=ROOT,capture_output=True,timeout=70)
    (CASE_ROOT/'controls'/(label+'.stdout')).write_bytes(p.stdout);(CASE_ROOT/'controls'/(label+'.stderr')).write_bytes(p.stderr)
    verdict=load(out/'verdict.json') if (out/'verdict.json').exists() else None
    row={'label':label,'argv':argv,'exit':p.returncode,'expected_exit':expected,'elapsed_ns':time.monotonic_ns()-before,'verdict':verdict,'compiler_ran':(out/'compiler-status.json').exists(),'implementation_sha256':{name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in ['capture.py','packet_schema.py','capture_observer.rs','run_controls_explicit_observer.py']}}
    RESULTS.append(row);dump(CASE_ROOT/'controls'/(label+'.json'),row)
    if p.returncode!=expected:raise RuntimeError('unexpected control result '+label+': '+p.stdout.decode()+p.stderr.decode())
    if any(s in p.stdout+p.stderr for s in [b'panicked at',b'Assertion failed',b'assertion failed',b'internal compiler error']):raise RuntimeError('panic/assertion stop '+label)
    print(label,p.returncode,verdict['status'] if verdict else 'no verdict',flush=True)
    return out/'independent-capture.json'
def mutated(name,change):
    value=copy.deepcopy(load(ROOT/'producer-base/independent-capture.json'));change(value)
    path=CASE_ROOT/'candidates'/name;dump(path,value);return path

def main():
    CASE_ROOT.mkdir();(CASE_ROOT/'candidates').mkdir()
    flip=select('flip',SOURCE,features=['flip'])
    changed=select('changed-body',SOURCE.replace('pub fn selected(x:u8)->u8 { x ^ 2 }','pub fn selected(x:u8)->u8 { x ^ 7 }'))
    inst=SOURCE.replace('pub fn generic<T: Step>', 'impl Step for u16 { const SHIFT:u8=4; fn step(self)->u8 { (self as u8) ^ Self::SHIFT } }\npub fn generic<T: Step>')
    inst=inst.replace('generic::<u8>(selected(x))','generic::<u16>(selected(x) as u16)')
    instance=select('changed-instance',inst)
    decoy=select('decoy',SOURCE,root_item='decoy')
    external=select('unsupported-external','#![no_std]\npub fn root(x:u8)->u8 { x.wrapping_add(1) }\n')
    floating=select('unsupported-float','#![no_std]\npub fn root(x:u8)->u8 { x }\npub fn hidden(x:f32)->f32 { x }\n')
    dynamic=select('unsupported-dynamic','#![no_std]\ntrait D { fn f(&self)->u8; }\nstruct V(u8);\nimpl D for V { fn f(&self)->u8{self.0} }\npub fn root(x:u8)->u8 { let v=V(x); let d:&dyn D=&v; d.f() }\n')
    asynchronous=select('unsupported-async','#![no_std]\npub async fn future()->u8 {3}\npub fn root(x:u8)->u8{x}\n')
    generic=select('unsupported-generic-root',SOURCE,root_item='generic')
    split=CASE_ROOT/'requests/split';split.mkdir();(split/'lib.rs').write_text('#![no_std]\nmod part;\npub fn root(x:u8)->u8{part::value(x)}\n');(split/'part.rs').write_text('pub const MASK:u8=3;\npub fn value(x:u8)->u8{x ^ MASK}\n')
    split_request=copy.deepcopy(BASE);split_request['root_file']='lib.rs';split_request['files']=[{'path':name,'sha256':hashlib.sha256((split/name).read_bytes()).hexdigest()} for name in ['lib.rs','part.rs']];dump(split/'request.json',split_request)
    producers={}
    for name,request in [('flip',flip),('changed-body',changed),('changed-instance',instance),('decoy',decoy),('split',split/'request.json')]:
        candidate=invoke('produce-'+name,'capture',request);producers[name]=candidate
        invoke('accept-'+name,'check',request,candidate)
    base=ROOT/'requests/base/request.json';candidate=ROOT/'producer-base/independent-capture.json'
    invoke('accept-baseline','check',base,candidate)
    def check_mutant(name,change):invoke('reject-'+name,'check',base,mutated(name+'.json',change),expected=2)
    check_mutant('wrong-item',lambda x:x['semantic'].__setitem__('root','decoy'))
    check_mutant('wrong-cfg',lambda x:x['semantic']['effective_cfg'].append('(\"feature\", Some(\"flip\"))'))
    check_mutant('wrong-target',lambda x:x['semantic'].__setitem__('target','x86_64-forged-target'))
    check_mutant('wrong-instance',lambda x:next(i for i in x['semantic']['instances'] if i['definition']=='generic').__setitem__('arguments','[u16]'))
    def body_change(x):
        i=next(i for i in x['semantic']['instances'] if i['definition']=='generated')
        s=next(s for b in i['body']['blocks'] for s in b['statements'] if s['operation']['kind']=='assign' and s['operation']['value']['kind']=='binary')
        s['operation']['value']['operator']='BitOr'
    check_mutant('wrong-body',body_change)
    def omit_unreachable(x):
        x['semantic']['local_definitions']=[d for d in x['semantic']['local_definitions'] if d['path']!='decoy']
        x['semantic']['local_body_templates']=[t for t in x['semantic']['local_body_templates'] if t['definition']!='decoy']
    check_mutant('omitted-uncalled-owner',omit_unreachable)
    def omit_macro(x):x['semantic']['local_definitions']=[d for d in x['semantic']['local_definitions'] if d['path']!='generated']
    check_mutant('omitted-macro-owner',omit_macro)
    def erase_drop(x):
        sem=x['semantic'];root=next(i for i in sem['instances'] if i['definition']=='root');drop=next(b for b in root['body']['blocks'] if b['terminator']['kind']=='drop');target=drop['terminator']['target'];drop['terminator']={'kind':'goto','target':target}
        erased={i['id'] for i in sem['instances'] if i['kind'].startswith('DropGlue(') or i['definition']=='<Guard as core::ops::Drop>::drop'}
        sem['instances']=[i for i in sem['instances'] if i['id'] not in erased];sem['edges']=[e for e in sem['edges'] if e['kind']!='drop' and e['from'] not in erased and e['to'] not in erased]
    check_mutant('coherently-erased-drop',erase_drop)
    check_mutant('missing-edge',lambda x:x['semantic']['edges'].pop())
    check_mutant('unknown-field',lambda x:x['semantic'].__setitem__('admitted',True))
    for name in ['flip','changed-body','changed-instance','decoy']:
        value=load(producers[name]);value['request']=copy.deepcopy(BASE);path=CASE_ROOT/'candidates'/('rebound-'+name+'.json');dump(path,value)
        invoke('reject-actual-rebound-'+name,'check',base,path,expected=2)
    split_packet=load(producers['split']);split_packet['semantic']['sources']=[s for s in split_packet['semantic']['sources'] if s['name'].endswith('/lib.rs')];path=CASE_ROOT/'candidates/omitted-source-file.json';dump(path,split_packet)
    invoke('reject-omitted-source-file','check',split/'request.json',path,expected=2)
    duplicate=CASE_ROOT/'candidates/duplicate-key.json';duplicate.write_text(candidate.read_text().replace('{','{"schema":"owned-bound-capture-v1",',1));invoke('reject-duplicate-key','check',base,duplicate,expected=2)
    for name,request in [('external',external),('float',floating),('dynamic',dynamic),('async',asynchronous),('generic-root',generic)]:invoke('reject-unsupported-'+name,'capture',request,expected=2)
    bad=CASE_ROOT/'requests/unsupported-config';bad.mkdir();(bad/'probe.rs').write_text(SOURCE);req=copy.deepcopy(BASE);req['edition']='2024';dump(bad/'request.json',req);invoke('reject-unsupported-config','capture',bad/'request.json',expected=2)
    bad=CASE_ROOT/'requests/wrong-tool-artifact';bad.mkdir();(bad/'probe.rs').write_text(SOURCE);req=copy.deepcopy(BASE);req['toolchain']['driver_file']='bin/rustc';req['toolchain']['driver_sha256']=req['toolchain']['rustc_sha256'];dump(bad/'request.json',req);invoke('reject-wrong-tool-artifact','capture',bad/'request.json',expected=2)
    summary={'controls':RESULTS,'all_expected_statuses_match':True,'valid_Rust_subjects_only':True,'native_fixture_execution':False,'unsafe_source_theorem':False,'one_compiler_at_a_time':True}
    dump(CASE_ROOT/'control-results.json',summary)
    print('complete',len(RESULTS),'controls',flush=True)

if __name__=='__main__':main()
