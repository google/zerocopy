"""Replay owned pilot files with caller-selected tools and an already built Kraken.

Creates one new output directory, installs nothing, and never executes the
separate false-contract source. This runner is not a verified proof checker.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import time

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--lean',required=True)
    ap.add_argument('--kraken-lib',required=True)
    ap.add_argument('--rustc',default='rustc')
    ap.add_argument('--out',required=True)
    args=ap.parse_args()
    if platform.system()!='Darwin' or platform.machine() not in ['arm64','aarch64']:
        raise SystemExit('native pilot requires the recorded Darwin arm64 domain')
    here=Path(__file__).resolve().parent
    out=Path(args.out);out.parent.resolve(strict=True);out.mkdir()
    out=out.resolve(strict=True)
    for name in ['pilot.rs','KrakenPilot.lean','macho_binding.py']:
        shutil.copyfile(here/name,out/name)
    rows=[]
    def run(label,actual,display,env=None):
        t=time.perf_counter()
        r=subprocess.run(actual,cwd=out,env=env,capture_output=True)
        (out/(label+'.stdout')).write_bytes(r.stdout)
        (out/(label+'.stderr')).write_bytes(r.stderr)
        row={'phase':label,'command':display,'exit':r.returncode,'seconds':time.perf_counter()-t,
             'stdout_sha256':hashlib.sha256(r.stdout).hexdigest(),
             'stderr_sha256':hashlib.sha256(r.stderr).hexdigest()}
        rows.append(row)
        (out/'results.json').write_text(json.dumps(rows,indent=2)+'\n')
        if r.returncode: raise SystemExit(label+' failed: '+str(r.returncode))
        return r
    run('rustc-version',[args.rustc,'--version','--verbose'],['rustc','--version','--verbose'])
    run('lean-version',[args.lean,'--version'],['lean','--version'])
    env=dict(os.environ);env['LEAN_PATH']=str(Path(args.kraken_lib).resolve(strict=True))
    proof=run('kraken-proof',[args.lean,'KrakenPilot.lean'],['lean','KrakenPilot.lean'],env)
    if b'sorryAx' in proof.stdout or b'_native.' in proof.stdout:
        raise SystemExit('unexpected theorem dependency')
    for opt in ['0','3']:
        name='pilot-opt'+opt
        argv=[args.rustc,'--edition=2024','-C','opt-level='+opt,'-C','panic=abort','pilot.rs','-o',name]
        run('compile-'+opt,argv,['rustc',*argv[1:]])
        r=run('native-'+opt,[str(out/name)],[name])
        observed=json.loads(r.stdout)
        expected={'arithmetic_inputs':8292,'arithmetic_implementations':2,
                  'byte_load_inputs':256,'store_inputs':10,'host':'aarch64-apple-darwin'}
        if observed!=expected: raise SystemExit('native outcome mismatch')
    argv=[args.rustc,'--edition=2024','--crate-type=lib','--emit=llvm-ir,asm,obj','-C','opt-level=3','-C','panic=abort','pilot.rs']
    run('object',argv,['rustc',*argv[1:]])
    import sys
    r=run('binding',[sys.executable,'macho_binding.py','pilot.o','pilot-opt0','pilot-opt3'],
          ['python3','macho_binding.py','pilot.o','pilot-opt0','pilot-opt3'])
    (out/'binding-results.json').write_bytes(r.stdout)
    print(json.dumps({'phases':len(rows),'all_exit_zero':True,'output':out.name}))

if __name__=='__main__': main()
