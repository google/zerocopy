#!/usr/bin/env python3
"""Freeze the source-byte and logical-name predictions before extraction."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
FILES = ('Cargo.toml','Cargo.lock','src/lib.rs','src/shared.rs')

def sha(raw): return hashlib.sha256(raw).hexdigest()

def main():
    out = HERE/'oracle.json'
    assert not out.exists()
    fixture = HERE/'fixture'
    files = {f:sha((fixture/f).read_bytes()) for f in FILES}
    source = (fixture/'src/shared.rs').read_bytes()
    assert source.count('🙂'.encode()) == 1
    assert source.count('e\u0301'.encode()) == 1
    obj = {'schema':1,'fixture_sha256':files,'alias_target':'../shared.rs',
           'module_relative_paths':['src/left/common.rs','src/right/common.rs'],
           'expected_logical_names':['symlink_module_probe::left::step',
                                     'symlink_module_probe::right::step'],
           'shared_source_hex':source.hex(),
           'hypotheses':{
             'lexical_path_distinct':'two Local file-table entries and distinct item file IDs',
             'canonical_file_coalesced':'one Local file-table entry and one shared item file ID'
           }}
    out.write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({'oracle_sha256':sha(out.read_bytes()),'files':files},ensure_ascii=False))

if __name__=='__main__':main()
