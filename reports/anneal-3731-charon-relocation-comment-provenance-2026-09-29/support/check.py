#!/usr/bin/env python3
"""Read-only verifier for retained Charon/Aeneas relocation specimens."""
import hashlib
import json
from pathlib import Path
import re

from probe import BASE, COMMENT, diff, normalized, sha

HERE = Path(__file__).resolve().parent
record = json.loads((HERE / 'results.json').read_text())
docs = {}
lean_text = {}
for name in ('origin', 'relocated', 'comment', 'repeat'):
    case = record['cases'][name]
    llbc = HERE / 'artifacts' / name / 'probe.llbc'
    raw = llbc.read_bytes()
    assert sha(raw) == case['llbc_sha256'] and len(raw) == case['llbc_bytes']
    doc = json.loads(raw)
    assert doc['charon_version'] == '0.1.210'
    assert doc['has_errors'] is False and case['has_errors'] is False
    assert doc['translated']['crate_name'] == 'probe'
    assert doc['translated']['options']['preset'] == 'Aeneas'
    # The artifact records its extraction-time absolute path; the package may
    # later be checked from a different checkout directory.
    recorded_dest = doc['translated']['options']['dest_file']
    assert recorded_dest.endswith(f'/support/artifacts/{name}/probe.llbc')
    assert f'Imported: {recorded_dest}\n' in case['aeneas']['stdout']
    local = next(f for f in doc['translated']['files'] if f['crate_name'] == 'probe')
    expected = COMMENT if name == 'comment' else BASE
    assert local['contents'] == expected
    assert case['source_sha256'] == sha(expected.encode())
    assert case['source_bytes'] == len(expected.encode())
    assert local == case['local_file']
    assert local['name']['Local'].endswith('/src/lib.rs')
    assert case['charon']['returncode'] == case['aeneas']['returncode'] == 0
    lean_dir = HERE / 'artifacts' / name / 'lean'
    assert [p.name for p in lean_dir.iterdir()] == ['Probe.lean']
    lean = (lean_dir / 'Probe.lean').read_bytes()
    assert case['lean_files'] == {'Probe.lean': {'bytes': len(lean), 'sha256': sha(lean)}}
    docs[name] = normalized(doc)
    lean_text[name] = lean.decode()

origin_path = record['cases']['origin']['local_file']['name']['Local']
assert record['cases']['comment']['local_file']['name']['Local'] == origin_path
assert record['cases']['repeat']['local_file']['name']['Local'] == origin_path
relocated_path = record['cases']['relocated']['local_file']['name']['Local']
assert relocated_path != origin_path
assert origin_path.endswith('/origin-root/src/lib.rs')
assert relocated_path.endswith('/other-root/src/lib.rs')

expected_diffs = {
    'origin_relocated': ['$.translated.files[0].name.Local'],
    'origin_comment': ['$.translated.files[0].contents'],
    'origin_repeat': [],
}
actual_diffs = {
    'origin_relocated': sorted(diff(docs['origin'], docs['relocated'])),
    'origin_comment': sorted(diff(docs['origin'], docs['comment'])),
    'origin_repeat': sorted(diff(docs['origin'], docs['repeat'])),
}
assert actual_diffs == expected_diffs == record['normalized_diff_paths']
assert lean_text['origin'] == lean_text['comment'] == lean_text['repeat']
assert lean_text['origin'] != lean_text['relocated']
source_line = re.compile(r"^    Source: '.*', lines 1:0-1:48$", re.M)
assert source_line.findall(lean_text['origin']) == [f"    Source: '{origin_path}', lines 1:0-1:48"]
assert source_line.findall(lean_text['relocated']) == [f"    Source: '{relocated_path}', lines 1:0-1:48"]
assert source_line.sub('    Source: <SOURCE>', lean_text['origin']) == source_line.sub('    Source: <SOURCE>', lean_text['relocated'])
assert record['lean_equal'] == {
    'origin_relocated': False, 'origin_comment': True, 'origin_repeat': True}
print('PASS: four pinned output specimens, exact normalized LLBC diffs, and Lean provenance-only path diff')
