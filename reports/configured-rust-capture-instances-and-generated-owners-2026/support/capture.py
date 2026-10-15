"""Caller-bound compiler capture/check. Trusted observer; untrusted data candidate.

This is a cooperative local prototype, not OS isolation or a Rust safety proof.
"""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json,os,subprocess,sys,time
from packet_schema import Rejected,need,fields,load,packet,semantic

COMMIT='f53b654a8882fd5fc036c4ca7a4ff41ce32497a6'
def sha(data):return hashlib.sha256(data).hexdigest()
def file_sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda:f.read(1024**2),b''):h.update(block)
    return h.hexdigest()
def dump(path,value):
    with path.open('x') as f:json.dump(value,f,indent=2);f.write('\n')
def physical(path):
    need(path.resolve(strict=True)==path.absolute() and not any(p.is_symlink() for p in [path,*path.parents]),'physical non-symlink path required')
    return path
def relative(name):
    need(type(name) is str and name and len(name)<128,'relative path required');p=PurePosixPath(name)
    need(not p.is_absolute() and '..' not in p.parts and '.' not in p.parts and str(p)==name,'noncanonical relative path');return p

def request(path,tool,observer):
    req=load(path)
    fields(req,'schema files root_file root_item root_signature crate_name edition target target_cpu features source_namespace toolchain observer_sha256')
    need(req['schema']=='owned-source-request-v1','unsupported request schema')
    need(req['crate_name']=='capture' and req['edition']=='2021' and req['target']=='aarch64-apple-darwin' and req['target_cpu']=='apple-m1' and req['source_namespace']=='/owned-source','unsupported compiler configuration')
    need(req['features'] in [[],['flip']],'unsupported cfg features')
    need(req['root_signature']=={'arguments':['u8'],'return':'u8'},'unsupported root signature')
    need(type(req['root_item']) is str and 0<len(req['root_item'])<128,'invalid root item')
    need(type(req['files']) is list and 1<=len(req['files'])<=4,'source graph size')
    source={}
    for row in req['files']:
        fields(row,'path sha256');name=str(relative(row['path']));need(name.endswith('.rs') and name not in source,'source path duplicate/extension')
        q=physical((path.parent/name).absolute());raw=q.read_bytes();need(len(raw)<=65536 and sha(raw)==row['sha256'],'source differs from caller selection')
        try:text=raw.decode('utf-8')
        except UnicodeError as e:raise Rejected('source must be UTF-8') from e
        need(not text.startswith('\ufeff') and '\r' not in text,'only LF source encoding admitted');source[name]=raw
    need(req['root_file'] in source,'root file not selected')
    identity=req['toolchain'];fields(identity,'rustc_commit rustc_sha256 driver_file driver_sha256 core_file core_sha256')
    need(identity['rustc_commit']==COMMIT,'wrong compiler commit request')
    need(identity['driver_file']=='lib/librustc_driver-16d1e96e5b674978.dylib','wrong compiler-driver artifact selection')
    cores=list((tool/'lib/rustlib/aarch64-apple-darwin/lib').glob('libcore-*.rlib'))
    need(len(cores)==1 and identity['core_file']==cores[0].relative_to(tool).as_posix(),'wrong target-core artifact selection')
    expected={tool/'bin/rustc':identity['rustc_sha256'],tool/str(relative(identity['driver_file'])):identity['driver_sha256'],tool/str(relative(identity['core_file'])):identity['core_sha256'],observer:req['observer_sha256']}
    for q,h in expected.items():physical(q);need(file_sha(q)==h,'tool/observer identity differs')
    return req,source,expected

def observe(req,sources,identities,tool,observer,out):
    snapshot=out/'source';snapshot.mkdir();(out/'tmp').mkdir();(out/'compiler-output').mkdir()
    for name,raw in sources.items():
        q=snapshot/name;q.parent.mkdir(parents=True,exist_ok=True)
        with q.open('xb') as f:f.write(raw)
        q.chmod(0o400)
    argv=[str(observer),req['root_item'],str(out/'semantic.json'),'--',str(snapshot/req['root_file']),'--sysroot',str(tool),'--crate-name',req['crate_name'],'--crate-type','lib','--edition='+req['edition'],'--target',req['target'],'-C','target-cpu='+req['target_cpu'],'-C','opt-level=0','-C','panic=abort','-C','debuginfo=0','-Z','mir-opt-level=0','--remap-path-prefix',str(snapshot)+'='+req['source_namespace'],'--out-dir',str(out/'compiler-output')]
    for feature in req['features']:argv.extend(['--cfg','feature="'+feature+'"'])
    env={'PATH':os.environ.get('PATH','/usr/bin:/bin'),'TMPDIR':str(out/'tmp'),'CLANG_MODULE_CACHE_PATH':str(out/'clang-cache')}
    before=time.monotonic_ns()
    try:
        with (out/'compiler.stdout').open('xb') as stdout,(out/'compiler.stderr').open('xb') as stderr:
            process=subprocess.run(argv,cwd=out,env=env,stdout=stdout,stderr=stderr,timeout=60)
    except subprocess.TimeoutExpired as error:
        dump(out/'compiler-status.json',{'status':'operational-timeout','limit_seconds':60,'argv':argv});raise RuntimeError('compiler timeout; capture unusable') from error
    record={'argv':argv,'exit':process.returncode,'elapsed_ns':time.monotonic_ns()-before,'stdout_sha256':file_sha(out/'compiler.stdout'),'stderr_sha256':file_sha(out/'compiler.stderr'),'observer_sha256':file_sha(observer)}
    dump(out/'compiler-status.json',record)
    text=(out/'compiler.stdout').read_bytes()+(out/'compiler.stderr').read_bytes()
    if any(word in text for word in [b'panicked at',b'assertion failed',b'Assertion failed',b'internal compiler error']):raise RuntimeError('unexpected compiler/observer panic/assertion; stop affected path')
    for q,h in identities.items():
        if file_sha(q)!=h:raise RuntimeError('tool identity changed during observation')
    for name,raw in sources.items():
        if (snapshot/name).read_bytes()!=raw:raise RuntimeError('source snapshot changed during observation')
    if process.returncode==65:
        rejection=load(out/'semantic.json');raise Rejected('unsupported source capture: '+str(rejection.get('reason')))
    if process.returncode!=0:raise RuntimeError('compiler/observer operational failure '+str(process.returncode))
    data=load(out/'semantic.json');semantic(data)
    need(data['root']==req['root_item'] and data['crate_name']==req['crate_name'],'actual selected root/crate mismatch')
    expected_sources={req['source_namespace']+'/'+name:raw.decode() for name,raw in sources.items()}
    need({s['name']:s['compiler_source'] for s in data['sources']}==expected_sources,'compiler source graph differs or has an omitted/unrequested source')
    need(data['codegen_target_cpu']=='Some("'+req['target_cpu']+'")','actual target cpu differs')
    root=[i for i in data['instances'] if i['definition']==req['root_item'] and i['arguments']=='[]']
    need(len(root)==1,'selected root closure mismatch');body=root[0]['body']
    need(body['argument_count']==1 and body['locals'][0]['type']=='u8' and body['locals'][1]['type']=='u8','actual root signature differs')
    return {'schema':'owned-bound-capture-v1','request':req,'semantic':data},record

def main():
    ap=argparse.ArgumentParser();ap.add_argument('action',choices=['capture','check']);ap.add_argument('--request',type=Path,required=True);ap.add_argument('--candidate',type=Path);ap.add_argument('--toolchain',type=Path,required=True);ap.add_argument('--observer',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    out=a.output.absolute();need(not out.exists() and out.resolve()==out and out.parent.resolve()==out.parent,'fresh physical output required');out.mkdir()
    try:
        physical(a.request.absolute());tool=physical(a.toolchain.absolute());observer=physical(a.observer.absolute())
        req,sources,identities=request(a.request.absolute(),tool,observer)
        candidate=None
        if a.action=='check':
            need(a.candidate is not None,'candidate required');candidate=load(a.candidate);packet(candidate)
            need(candidate['request']==req,'candidate binding differs from caller-owned request')
        captured,record=observe(req,sources,identities,tool,observer,out)
        packet(captured);dump(out/'independent-capture.json',captured)
        if candidate is not None:need(candidate==captured,'candidate semantic capture differs from independently selected compiler observation')
        verdict={'status':'accepted' if a.action=='check' else 'captured','request_sha256':file_sha(a.request),'packet_sha256':file_sha(out/'independent-capture.json'),'instances':len(captured['semantic']['instances']),'local_definitions':len(captured['semantic']['local_definitions']),'body_templates':len(captured['semantic']['local_body_templates']),'edges':len(captured['semantic']['edges']),'compiler_exit':record['exit'],'semantic_theorem':False}
        dump(out/'verdict.json',verdict);print(json.dumps(verdict));return 0
    except Rejected as error:
        verdict={'status':'rejected','reason':str(error)};dump(out/'verdict.json',verdict);print(json.dumps(verdict));return 2
    except (OSError,RuntimeError,ValueError,KeyError,TypeError,IndexError) as error:
        verdict={'status':'operational-failure','reason':str(error)};dump(out/'verdict.json',verdict);print(json.dumps(verdict));return 70

if __name__=='__main__':raise SystemExit(main())
