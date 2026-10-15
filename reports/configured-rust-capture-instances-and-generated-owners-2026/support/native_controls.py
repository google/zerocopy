"""Compile only caller-selected valid Rust, then observe every u8 input serially."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,time
from packet_schema import load
ROOT=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--toolchain',type=Path,required=True);a=ap.parse_args();tool=a.toolchain.resolve(strict=True)
    out=ROOT/'native-controls'
    if out.exists():raise ValueError('fresh native root required')
    out.mkdir();(out/'tmp').mkdir();rows=[]
    env=os.environ.copy();env['TMPDIR']=str(out/'tmp');env['CLANG_MODULE_CACHE_PATH']=str(out/'clang-cache')
    def execute(label,args):
        before=time.monotonic_ns();p=subprocess.run(args,cwd=out,env=env,capture_output=True,timeout=60)
        (out/(label+'.stdout')).write_bytes(p.stdout);(out/(label+'.stderr')).write_bytes(p.stderr)
        row={'label':label,'argv':args,'exit':p.returncode,'elapsed_ns':time.monotonic_ns()-before,'stdout_sha256':hashlib.sha256(p.stdout).hexdigest(),'stderr_sha256':hashlib.sha256(p.stderr).hexdigest()};rows.append(row)
        (out/(label+'.json')).write_text(json.dumps(row,indent=2)+'\n')
        if p.returncode or any(s in p.stdout+p.stderr for s in [b'panicked at',b'assertion failed',b'Assertion failed',b'internal compiler error']):raise RuntimeError('native control failure/panic; stop '+label)
        return p.stdout
    cases=[('baseline',ROOT/'requests/base/request.json',lambda x:4),('flip',ROOT/'final-matrix/requests/flip/request.json',lambda x:7),('changed-body',ROOT/'final-matrix/requests/changed-body/request.json',lambda x:1),('changed-instance',ROOT/'final-matrix/requests/changed-instance/request.json',lambda x:3),('decoy',ROOT/'final-matrix/requests/decoy/request.json',lambda x:x^9)]
    observations=[]
    for name,path,expected in cases:
        req=load(path);case=out/name;case.mkdir();lib=case/'libcapture.rlib'
        for entry in req['files']:
            raw=(path.parent/entry['path']).read_bytes()
            if hashlib.sha256(raw).hexdigest()!=entry['sha256']:raise ValueError('selected native source changed')
        common=[str(tool/'bin/rustc'),'--sysroot',str(tool),'--edition=2021','--target','aarch64-apple-darwin','-C','target-cpu=apple-m1','-C','opt-level=0','-C','panic=abort','-C','debuginfo=0','-Z','mir-opt-level=0']
        command=common+[str(path.parent/req['root_file']),'--crate-name','capture','--crate-type','rlib','--remap-path-prefix',str(path.parent)+'=/owned-source','-o',str(lib)]
        for feature in req['features']:command.extend(['--cfg','feature="'+feature+'"'])
        execute(name+'-library',command)
        wrapper=case/'main.rs';wrapper.write_text('extern crate capture;\nfn main() { let mut out=Vec::new(); for x in 0u16..=255 { out.push(capture::'+req['root_item']+'(x as u8)); } println!("{:?}",out); }\n')
        binary=case/'observe';execute(name+'-wrapper',common+[str(wrapper),'--extern','capture='+str(lib),'-o',str(binary)])
        raw=execute(name+'-run',[str(binary)]);values=json.loads(raw)
        if values!=[expected(x) for x in range(256)]:raise RuntimeError('native all-byte oracle mismatch '+name)
        observations.append({'case':name,'request_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'inputs':256,'outputs':values,'expected_outputs_match':True,'binary_sha256':hashlib.sha256(binary.read_bytes()).hexdigest(),'library_sha256':hashlib.sha256(lib.read_bytes()).hexdigest()})
        print(name,'all256 matched',flush=True)
    result={'observations':observations,'commands':rows,'all_expected_statuses_zero':True,'valid_safe_Rust_fixture_execution':True,'compiler_or_source_safety_theorem':False,'scope':'Finite native corroboration for caller-selected source variants; does not prove MIR capture correctness, ABI refinement or arbitrary-execution safety.'}
    (out/'results.json').write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__':main()
