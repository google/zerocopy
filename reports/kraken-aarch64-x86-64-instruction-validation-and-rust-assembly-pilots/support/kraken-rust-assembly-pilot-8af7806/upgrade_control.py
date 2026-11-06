"""Compile-only source-change control; never runs the changed function.

The old byte claim must fail. Updating bytes would require a new semantic proof.
"""
import argparse,hashlib,json,platform,subprocess,time,sys
from pathlib import Path
sys.dont_write_bytecode=True
from macho_binding import EXPECTED,functions

def main():
 p=argparse.ArgumentParser();p.add_argument('--out',required=True);p.add_argument('--rustc',default='rustc');a=p.parse_args()
 if platform.system()!='Darwin' or platform.machine() not in ['arm64','aarch64']:raise SystemExit('requires Darwin arm64')
 out=Path(a.out);out.parent.resolve(strict=True);out.mkdir();out=out.resolve(strict=True)
 source=Path(__file__).with_name('pilot.rs').read_bytes()
 old=b'naked_asm!("add x0, x0, x1", "ret");';new=b'naked_asm!("sub x0, x0, x1", "ret");'
 if source.count(old)!=1:raise SystemExit('source identity changed; reassess control')
 changed=source.replace(old,new);(out/'changed.rs').write_bytes(changed)
 argv=['--edition=2024','--crate-type=lib','--emit=obj','-C','opt-level=3','-C','panic=abort','changed.rs']
 t=time.perf_counter();r=subprocess.run([a.rustc,*argv],cwd=out,capture_output=True)
 (out/'compile.stdout').write_bytes(r.stdout);(out/'compile.stderr').write_bytes(r.stderr)
 record={'command':['rustc',*argv],'exit':r.returncode,'seconds':time.perf_counter()-t,'original_source_sha256':hashlib.sha256(source).hexdigest(),'changed_source_sha256':hashlib.sha256(changed).hexdigest()}
 if r.returncode:raise SystemExit('compile failed; no binding verdict')
 blob=(out/'changed.o').read_bytes();bound=functions(blob,EXPECTED)
 if bound['_naked_add']['matches'] or not bound['_naked_store']['matches']:raise SystemExit('unexpected change scope; inspect before continuing')
 record.update({'old_add_claim_rejected':True,'unchanged_store_claim_matches':True,'changed_object_sha256':hashlib.sha256(blob).hexdigest(),'selected_ranges':bound,'native_execution':False,'new_semantic_proof':False})
 (out/'result.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({'old_add_claim_rejected':True,'unchanged_store_claim_matches':True}))
if __name__=='__main__':main()
