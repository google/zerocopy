#!/usr/bin/env python3
"""Derive displayed HIR DefId maps from retained rustc output."""
import json
import re
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent
PAT=re.compile(r'DefId\(0:(\d+) ~ local_identity\[([0-9a-f]+)\](?:::(.*?))?\)')

def extract(data):
    result={}
    crate_hashes=set()
    for index,crate_hash,path in PAT.findall(data.decode()):
        path=path or '<crate>'
        crate_hashes.add(crate_hash)
        item={'index':int(index),'crate_display':crate_hash}
        if path in result:
            assert result[path]==item, (path,result[path],item)
        else:
            result[path]=item
    assert len(crate_hashes)==1
    return result

def main():
    maps={}
    for role in ('old','new'):
        maps[role]={}
        for variant in ('repaired','shifted'):
            data=(ROOT/'raw'/f'{role}--{variant}--hir.stdout').read_bytes()
            maps[role][variant]=extract(data)
    result={'schema':1,'maps':maps,
            'same_display_paths_across_versions':all(set(maps['old'][v])==set(maps['new'][v]) for v in ('repaired','shifted')),
            'same_defid_indices_across_versions':all({k:x['index'] for k,x in maps['old'][v].items()}=={k:x['index'] for k,x in maps['new'][v].items()} for v in ('repaired','shifted')),
            'same_crate_display_across_versions':all(maps['old'][v]['<crate>']['crate_display']==maps['new'][v]['<crate>']['crate_display'] for v in ('repaired','shifted'))}
    (ROOT/'analysis.json').write_text(json.dumps(result,indent=2)+'\n')
    print('paths',len(maps['old']['repaired']),len(maps['old']['shifted']))
    print('cross-version paths',result['same_display_paths_across_versions'],'indices',result['same_defid_indices_across_versions'],'crate display',result['same_crate_display_across_versions'])

if __name__=='__main__':main()
