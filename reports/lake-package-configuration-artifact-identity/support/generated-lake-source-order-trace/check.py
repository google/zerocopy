#!/usr/bin/env python3
"""Validate retained Lake logs, exact source variants, artifact deltas, and final archive."""
import collections
import difflib
import gzip
import hashlib
import json
import re
import tarfile
from pathlib import Path

ROOT=Path(__file__).resolve().parent
data=json.loads((ROOT/'results.json').read_text())
sha=lambda blob:hashlib.sha256(blob).hexdigest()
assert '4.30.0-rc2' in data['tools']['lean_version']
assert '4.30.0-rc2' in data['tools']['lake_version']
assert data['schema']==1

for variant in ('base','reorder'):
    for name,record in data['source_fixture'][variant].items():
        raw=(ROOT/'fixture'/variant/name).read_bytes()
        assert sha(raw)==record['sha256'] and len(raw)==record['bytes']
base=data['source_fixture']['base'];reorder=data['source_fixture']['reorder']
assert base['Source/Types.lean']['sha256']==reorder['Source/Types.lean']['sha256']
assert base['Source.lean']['sha256']==reorder['Source.lean']['sha256']
assert base['Source/Funs.lean']['sha256']!=reorder['Source/Funs.lean']['sha256']
left=(ROOT/'fixture/base/Source/Funs.lean').read_text().splitlines()
right=(ROOT/'fixture/reorder/Source/Funs.lean').read_text().splitlines()
changed=[line for line in difflib.ndiff(left,right) if line.startswith(('- ','+ '))]
assert len(changed)==6 and all(line[2:].lstrip().startswith('Source: ') for line in changed)

labels=('fresh-base','fresh-reorder','same-base','same-noop','same-mtime-only',
        'same-reorder','same-reorder-noop','same-restore-base','same-restore-noop')
builds=data['builds']
assert tuple(b['label'] for b in builds)==labels
b={row['label']:row for row in builds}
for row in builds:
    label=row['label']
    assert row['returncode']==0
    assert len(row['local_job_lines'])==4
    for stream in ('stdout','stderr'):
        raw=gzip.decompress((ROOT/'logs'/(label+'.'+stream+'.gz')).read_bytes())
        assert sha(raw)==row[stream+'_sha256']
        if stream=='stdout':
            text=raw.decode()
            assert all(line in text for line in row['local_job_lines'])
    local={path:item for path,item in row['files'].items() if path.startswith('.lake/build/')}
    assert len(local)==32
    assert collections.Counter(item['family'] for item in local.values())=={
        '.hash':12,'.json':4,'.c':4,'.trace':4,'.olean':4,'.ilean':4}

def differences(a,c,attribute='sha256',prefix='.lake/build/'):
    x,y=b[a]['files'],b[c]['files']
    return {name for name in x.keys()&y.keys() if name.startswith(prefix)
            and x[name][attribute]!=y[name][attribute]}

for a,c in [('same-base','same-noop'),('same-noop','same-mtime-only'),
            ('same-reorder','same-reorder-noop'),('same-restore-base','same-restore-noop')]:
    assert differences(a,c)==set()
    assert differences(a,c,'mtime_ns')==set()
assert differences('same-noop','same-mtime-only',prefix='')==set()
assert differences('same-noop','same-mtime-only','mtime_ns',prefix='')=={'Source/Funs.lean'}
assert differences('same-mtime-only','same-reorder')=={
    '.lake/build/lib/lean/Source/Funs.olean.hash',
    '.lake/build/lib/lean/Source/Funs.olean',
    '.lake/build/lib/lean/Source/Funs.trace',
    '.lake/build/lib/lean/Source.trace',
    '.lake/build/lib/lean/Consumer.trace'}
assert differences('same-base','same-restore-base')==set()
def jobs(label):
    matches=[re.search(r'\b(Built|Replayed) (\S+)',line) for line in b[label]['local_job_lines']]
    assert all(matches)
    return {match[2]:match[1] for match in matches}
assert all(jobs(label)['Source.Types']=='Replayed' for label in labels[3:])
assert jobs('same-reorder')=={'Source.Types':'Replayed','Source.Funs':'Built',
                              'Source':'Built','Consumer':'Built'}
assert jobs('same-mtime-only')=={module:'Replayed' for module in
                                  ('Source.Types','Source.Funs','Source','Consumer')}
for a,c in [('fresh-base','same-base'),('fresh-reorder','same-reorder')]:
    assert not differences(a,c,prefix='.lake/build/lib/lean/',attribute='sha256')-{p for p in b[a]['files']
        if p.endswith('.trace')}

final={'fresh-base':'fresh-base','fresh-reorder':'fresh-reorder','same':'same-restore-noop'}
with tarfile.open(ROOT/'work.tar.gz','r:gz') as archive:
    members={m.name:m for m in archive.getmembers()}
    assert all(not m.issym() and not m.islnk() for m in members.values())
    for folder,label in final.items():
        for name,record in b[label]['files'].items():
            member=members['work/'+folder+'/'+name]
            raw=archive.extractfile(member).read()
            assert len(raw)==record['bytes'] and sha(raw)==record['sha256'],(folder,name)
print('PASS: 9 Lake runs, real Aeneas source-order comments, 32-artifact inventories, no-op/mtime replay, rebuild/restore, archived bytes')
