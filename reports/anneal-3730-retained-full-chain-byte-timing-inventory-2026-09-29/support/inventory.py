#!/usr/bin/env python3
"""Read-only inventory of the retained R48 one-worker full-chain evidence."""
import hashlib
import json
import os
from pathlib import Path

HERE=Path(__file__).resolve().parent
REPORTS=HERE.parents[1]
SOURCE=REPORTS/'anneal-3730-full-lake-server-chain-2026-09-29'/'support'
WORK=SOURCE/'work'/'one'/'u0'

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def family(relative):
    p=relative.parts
    if p[0]=='crate':return 'rust_crate_and_target'
    if p[0]=='generated':return 'aeneas_generated_source'
    if p[0]=='consumer':return 'direct_lean_consumer_and_artifacts'
    if p[0]=='lake':
        if len(p)>1 and p[1]=='.lake':
            return 'lake_symlink_or_local_build'
        return 'lake_project_source_and_config'
    if p[0]=='current.llbc':return 'charon_llbc'
    return 'other_retained'

def main():
    assert WORK.is_dir() and (SOURCE/'results.json').is_file()
    rows=[]
    for path in sorted(WORK.rglob('*')):
        if path.is_dir() and not path.is_symlink():continue
        rel=path.relative_to(WORK)
        stat=path.lstat()
        row={'path':rel.as_posix(),'family':family(rel),'mode':'symlink' if path.is_symlink() else 'regular',
             'inode':stat.st_ino,'device':stat.st_dev,'links':stat.st_nlink,
             'logical_bytes':stat.st_size,'allocated_bytes':stat.st_blocks*512}
        if path.is_symlink():row['link_target']=os.readlink(path)
        else:row['sha256']=sha(path)
        rows.append(row)
    grouped={}
    for row in rows:
        g=grouped.setdefault(row['family'],{'regular_files':0,'symlinks':0,'logical_bytes':0,'allocated_bytes':0,'unique_inodes':set()})
        g['regular_files' if row['mode']=='regular' else 'symlinks']+=1
        g['logical_bytes']+=row['logical_bytes'];g['allocated_bytes']+=row['allocated_bytes']
        g['unique_inodes'].add((row['device'],row['inode']))
    for g in grouped.values():g['unique_inodes']=len(g['unique_inodes'])
    original=json.loads((SOURCE/'results.json').read_text())
    by_hash={}
    for row in rows:
        if row['mode']=='regular':by_hash.setdefault(row['sha256'],[]).append(row)
    duplicates=[{'sha256':digest,'logical_bytes_each':same[0]['logical_bytes'],
                 'paths':[r['path'] for r in same],
                 'extra_logical_bytes':same[0]['logical_bytes']*(len(same)-1)}
                for digest,same in sorted(by_hash.items()) if len(same)>1]
    cell=original['cells'][0]
    unit=cell['units'][0]
    timing={'one_worker_wall_seconds':cell['wall_seconds'],
            'direct_rust_through_lean_seconds':unit['direct']['seconds'],
            'lake_build_seconds':unit['lake']['seconds'],
            'fresh_batch_seconds':unit['fresh']['seconds'],
            'server_goal_no_independent_elapsed':True,
            'unattributed_or_overlapping_wall_seconds':round(cell['wall_seconds']-unit['direct']['seconds']-unit['lake']['seconds']-unit['fresh']['seconds'],3),
            'sampled_peak_rss_kib':cell['sampled_peak_rss_kib']}
    result={'source_report':'anneal-3730-full-lake-server-chain-2026-09-29',
            'source_results_sha256':sha(SOURCE/'results.json'),
            'inventory_root':'support/work/one/u0',
            'rows':rows,'grouped':grouped,'duplicate_content_groups':duplicates,'timing':timing,
            'totals':{'files':sum(r['mode']=='regular' for r in rows),'symlinks':sum(r['mode']=='symlink' for r in rows),
                      'logical_bytes':sum(r['logical_bytes'] for r in rows),
                      'allocated_bytes':sum(r['allocated_bytes'] for r in rows),
                      'unique_inodes':len({(r['device'],r['inode']) for r in rows})}}
    (HERE/'results.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'totals':result['totals'],'grouped':grouped,'timing':timing},indent=2,sort_keys=True))

if __name__=='__main__':main()
