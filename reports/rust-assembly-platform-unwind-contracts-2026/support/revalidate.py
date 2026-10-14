#!/usr/bin/env python3
"""Compile-only cross-target/host unwind specimens; run no native code."""
import argparse,hashlib,json,os
from pathlib import Path
import re,subprocess,time,sys

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--clang',default='clang');ap.add_argument('--rustc',default='rustc');args=ap.parse_args()
 root=Path(__file__).resolve().parent;os.chdir(root);commands=[]
 def run(argv,label,log):
  start=time.monotonic();p=subprocess.run(argv,text=True,capture_output=True)
  (root/log).write_text(p.stdout+p.stderr)
  commands.append({'argv':label,'cwd':'.','exit':p.returncode,'elapsed_seconds':time.monotonic()-start,'log':log,'log_sha256':hashlib.sha256((root/log).read_bytes()).hexdigest()})
  if p.returncode!=0:raise RuntimeError('command failed; diagnose '+str(label))
  if re.search(r'panic(?:ked)?|assertion failed',p.stderr,re.I):raise RuntimeError('unexpected process diagnostic; stop')
 run([args.clang,'--version'],['clang','--version'],'clang-version.log')
 run([args.rustc,'--version','--verbose'],['rustc','--version','--verbose'],'rustc-version.log')
 base=['--target=x86_64-pc-windows-msvc','-O1','-fno-omit-frame-pointer','-funwind-tables']
 for emit,name in [('-S','specimen.s'),('-c','specimen.obj')]:
  tail=base+[emit,'specimen.c','-o',name]
  run([args.clang]+tail,['clang']+tail,name+'.build.log')
 tail=['--edition=2024','--crate-type=lib','--emit=asm','-Copt-level=1','-Cpanic=unwind','cleanup.rs','-o','cleanup.s']
 run([args.rustc]+tail,['rustc']+tail,'cleanup.build.log')
 asm=(root/'cleanup.s').read_text()
 for required in ['_rust_cleanup:', '.cfi_personality', '.cfi_lsda', '.cfi_def_cfa', 'blr', '__Unwind_Resume', '__gcc_except_tab']:
  if required not in asm:raise RuntimeError('different Apple AArch64 cleanup assembly: '+required)
 run([sys.executable,'check_unwind.py'],['python3','check_unwind.py'],'check-unwind.log')
 result={'status':'passed','native_execution':False,'commands':commands,'owned_source_hashes':{n:hashlib.sha256((root/n).read_bytes()).hexdigest() for n in ['specimen.c','cleanup.rs','check_unwind.py','revalidate.py']},'outputs':{n:hashlib.sha256((root/n).read_bytes()).hexdigest() for n in ['specimen.s','specimen.obj','cleanup.s','unwind-results.json']}}
 (root/'execution.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'passed','native_execution':False,'commands':len(commands)}))
if __name__=='__main__':main()
