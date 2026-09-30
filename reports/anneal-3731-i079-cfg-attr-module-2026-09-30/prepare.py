#!/usr/bin/env python3
"""Predeclare cfg_attr(path) source-selection predictions."""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
FILES=('Cargo.toml','Cargo.lock','src/lib.rs','src/default.rs','src/alternate.rs')
def sha(x):return hashlib.sha256(x).hexdigest()
def main():
    p=HERE/'oracle.json';assert not p.exists()
    hashes={n:sha((HERE/'fixture'/n).read_bytes()) for n in FILES}
    assert hashes['src/default.rs']!=hashes['src/alternate.rs']
    o={'schema':1,'fixture_sha256':hashes,'logical_module':'selected',
       'logical_item_name':'cfg_attr_module_probe::selected::marker',
       'runs':{'default':{'cargo_flags':['--no-default-features'],
                           'selected_file':'src/default.rs','excluded_file':'src/alternate.rs','marker_literal':17},
               'alternate':{'cargo_flags':['--no-default-features','--features','alternate'],
                             'selected_file':'src/alternate.rs','excluded_file':'src/default.rs','marker_literal':29}},
       'hypotheses':{'physical_file_selection':'LLBC should expose selected module source only',
                     'logical_identity':'same logical marker item name under either cfg'}}
    p.write_text(json.dumps(o,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({'oracle_sha256':sha(p.read_bytes()),'fixture_sha256':hashes}))
if __name__=='__main__':main()
