#!/usr/bin/env python3
"""Pin tiny Rust fixture and path-remap hypotheses before tool launch."""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
FILES=('Cargo.toml','Cargo.lock','src/lib.rs','src/left/common.rs','src/right/common.rs','src/error.rs')
def sha(raw):return hashlib.sha256(raw).hexdigest()
def main():
    p=HERE/'oracle.json';assert not p.exists()
    f={name:sha((HERE/'fixture'/name).read_bytes()) for name in FILES}
    assert f['src/left/common.rs']==f['src/right/common.rs']
    o={'schema':1,'fixture_sha256':f,'remap_flag':'--remap-path-prefix=src=/virtual/anneal-src',
       'diagnostic_token':'missingForRemap','expected_remapped_error_filename':'/virtual/anneal-src/error.rs',
       'expected_local_files':['src/lib.rs','src/left/common.rs','src/right/common.rs'],
       'hypotheses':{'rustc_diagnostic':'remapped source pathname when flag applies',
                     'charon_file_table':'inspect whether Local source paths are remapped or retained'}}
    p.write_text(json.dumps(o,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({'oracle_sha256':sha(p.read_bytes()),'fixture_sha256':f}))
if __name__=='__main__':main()
