#!/usr/bin/env python3
"""Offline replay of R444/R448 evidence; works after relocating the package."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
R = json.loads((ROOT / 'results.json').read_text())
C = R['cells']
OLD = '3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc'
NEW = '5045d0056413266e57c625dcd7c365b10e377c52'
TOOL_SHA = {'old': 'b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997',
            'new': '1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554'}
SOURCE_MAP_SHA = '84046bd81a9d4b1cd0e3a26a34121c43d31568e2cd39def49d7e946a38347841'
SOURCE_DIFF_SHA = '9501d5c3a96f8d782bc8c677ee0a3cb97d5657776d59f8d677d06a069c922bb5'
FIXTURE_SHA = {
    'support/r444/a/Probe.lean': '64eeaea07df037e4679fff14ff544f6604fd2524d228e24d8c09c4ce19c69f86',
    'support/r444/b/Probe.lean': '64eeaea07df037e4679fff14ff544f6604fd2524d228e24d8c09c4ce19c69f86',
    'support/r444/c/Probe.lean': '3974640f916786d464f12e5e11bf72ab57c9f05c5193f4024636f74f38200b9b',
    'support/r444/d/Probe.lean': 'c70ff66c97d23f6c1be7e1b562d1f175f7778d4ced55a7d2bbece8930dba9c91',
    'support/r444/e/Probe.lean': '5e30cbb6d51a6c77eb9490f8af4d7899a0b39fdcb5a659fa57c0c212cbe3ec5f',
    'support/r444/query/Query.lean': '9c065a638be5a096fa4a2243e2c6f8e08bf68c2ae11b1983ba056df3942d057b',
    'support/r448/Format.lean': '214a929edd5af9a7ca6d5d83a4fa90bc1015d700266045076df436d6c6c012f0',
}
FORMAT = {
    'default-text': ((), False), 'default-json': ((), True),
    'width10-off': (('pp.oneline=false', 'format.width=10'), True),
    'width120-off': (('pp.oneline=false', 'format.width=120'), True),
    'width10-on': (('pp.oneline=true', 'format.width=10'), True),
    'width120-on': (('pp.oneline=true', 'format.width=120'), True),
    'indent2': (('format.indent=2',), True), 'indent8': (('format.indent=8',), True),
    'unicode-fun-default': (('pp.unicode=true', 'pp.unicode.fun=false'), True),
    'ascii-fun-default': (('pp.unicode=false', 'pp.unicode.fun=false'), True),
    'unicode-fun-arrow': (('pp.unicode=true', 'pp.unicode.fun=true'), True),
    'ascii-fun-arrow': (('pp.unicode=false', 'pp.unicode.fun=true'), True),
    'mvars-false': (('pp.mvars.anonymous=false',), True),
    'mvars-true': (('pp.mvars.anonymous=true',), True),
    'fvars-false': (('pp.fvars.anonymous=false',), True),
    'fvars-true': (('pp.fvars.anonymous=true',), True),
    'endpos-false-text': (('printMessageEndPos=false',), False),
    'endpos-false-json': (('printMessageEndPos=false',), True),
    'endpos-true-text': (('printMessageEndPos=true',), False),
    'endpos-true-json': (('printMessageEndPos=true',), True),
}

def sha(data): return hashlib.sha256(data).hexdigest()
def read(path): return (ROOT / path).read_bytes()
def cell(role, suite, name): return C[f'{role}/{suite}/{name}']
def out(role, suite, name): return read(f'raw/{suite}/{role}/{name}.stdout')
def messages(role, suite, name):
    return [json.loads(line) for line in out(role, suite, name).splitlines() if line]
def normalized(role, name):
    result = []
    for m in messages(role, 'r444', name):
        assert m['fileName'] == f'support/r444/{name}/Probe.lean'
        result.append({**m, 'fileName': '<same-source-file>/Probe.lean'})
    return result

assert R['schema'] == 1 and set(R['tools']) == set(TOOL_SHA)
for path, expected in FIXTURE_SHA.items(): assert sha(read(path)) == expected
assert sha(read('support/source-map.json')) == SOURCE_MAP_SHA
source = json.loads(read('support/source-map.json'))
assert source['revisions'] == {'old': OLD, 'new': NEW}
assert source['diff_sha256'] == SOURCE_DIFF_SHA
assert sha(read('support/source-diff.patch')) == SOURCE_DIFF_SHA
assert source['blobs']['tests/elab/ppOneline.lean']['old'] == source['blobs']['tests/elab/ppOneline.lean']['new']
assert source['blobs']['tests/elab/ppUnicode.lean']['old'] == source['blobs']['tests/elab/ppUnicode.lean']['new']

expected = {f'{role}/r444/{name}' for role in TOOL_SHA for name in
            ('a', 'a-consumer', 'b', 'b-consumer', 'c', 'c-consumer', 'd', 'e',
             'e-consumer', 'a-repeat', 'a-output-only')}
expected |= {f'{role}/r448/{name}' for role in TOOL_SHA for name in FORMAT}
assert set(C) == expected and len(C) == 62
for role, expected_sha in TOOL_SHA.items():
    tool = R['tools'][role]
    assert tool['sha256'] == expected_sha
    assert Path(tool['executable']).name == 'lean'
    assert ('4.30.0-rc2' if role == 'old' else '4.34.1') in tool['version']
    assert (OLD if role == 'old' else NEW) in tool['version']

for key, c in C.items():
    role, suite, name = key.split('/')
    assert c['role'] == role and c['suite'] == suite and c['name'] == name
    argv = c['argv']
    assert argv[0] == R['tools'][role]['executable']
    if suite == 'r448':
        opts, json_mode = FORMAT[name]
        assert argv == [argv[0]] + (['--json'] if json_mode else []) + ['-D' + x for x in opts] + ['support/r448/Format.lean']
        assert c['exit_code'] == 1 and c['artifact'] is None
        assert c['env_LEAN_PATH'] is None
    elif name.endswith('-consumer'):
        case = name[0]
        assert case in 'abce'
        assert argv == [argv[0], '--json', 'support/r444/query/Query.lean']
        assert c['env_LEAN_PATH'].endswith(f'/raw/r444/{role}/{case}')
        assert c['exit_code'] == 0 and c['artifact'] is None
    else:
        case = name if name in 'abcde' else 'a'
        assert argv[:3] == [argv[0], '--json', '-o']
        assert argv[-1] == f'support/r444/{case}/Probe.lean'
        assert argv[3].endswith('/Probe.olean')
        assert c['env_LEAN_PATH'] is None
        assert c['exit_code'] == (1 if name == 'd' else 0)
    a = c['admission']
    assert a['page_bytes'] > 0 and a['memory_bytes'] > 0
    assert set(a['pages']) == {'free', 'inactive', 'speculative'}
    calculated = 100 * a['page_bytes'] * sum(a['pages'].values()) / a['memory_bytes']
    assert abs(a['reclaimable_percent'] - calculated) < 1e-10
    assert calculated > 20 and a['disk_free_bytes'] > 1_073_741_824 and a['owned_bytes'] < 100_000_000
    assert c['sampled_peak_rss_kib'] <= 1_048_576 and 0 < c['elapsed_s'] < 30
    for stream in ('stdout', 'stderr'):
        data = read(f'raw/{suite}/{role}/{name}.{stream}')
        assert sha(data) == c[stream + '_sha256'] and len(data) == c[stream + '_bytes']
    assert c['stderr_bytes'] == 0
    if c['artifact'] is not None:
        assert c['artifact'] == argv[3]
        data = read(c['artifact'])
        assert sha(data) == c['artifact_sha256'] and len(data) == c['artifact_bytes']
    else:
        assert c['artifact_sha256'] is None and c['artifact_bytes'] is None

for role in TOOL_SHA:
    assert sha(read(f'raw/r444/{role}/a-first.olean')) == cell(role, 'r444', 'a')['artifact_sha256']
    m = {case: normalized(role, case) for case in 'abcde'}
    raw = lambda name: messages(role, 'r444', name)
    h = lambda name: cell(role, 'r444', name)['artifact_sha256']
    cons = lambda name: out(role, 'r444', name + '-consumer')
    assert raw('a') != raw('b') and m['a'] == m['b']
    assert h('a') != h('b') and cons('a') == cons('b')
    assert m['a'] != m['c']
    actionable = lambda ms: [x for x in ms if x['severity'] in ('error', 'warning')]
    assert actionable(m['a']) == actionable(m['c']) and cons('a') == cons('c')
    assert cell(role, 'r444', 'd')['artifact_sha256'] is None
    assert m['a'] == m['e'] and h('a') != h('e') and cons('a') != cons('e')
    assert h('a') == h('a-repeat') == h('a-output-only')
    assert '1 + 1 = 2' in cons('a').decode() and '2 + 2 = 4' in cons('e').decode()
    f = lambda name: out(role, 'r448', name)
    assert f('default-json') == f('width10-off') == f('width120-off')
    assert f('width10-on') != f('width120-on')
    assert f('indent2') != f('indent8')
    assert f('unicode-fun-default') != f('ascii-fun-default')
    assert f('unicode-fun-default') != f('unicode-fun-arrow')
    assert f('ascii-fun-default') == f('ascii-fun-arrow')
    assert f('mvars-false') != f('mvars-true')
    assert f('fvars-false') == f('fvars-true')
    assert f('default-text') == f('endpos-false-text')
    assert f('default-json') == f('endpos-false-json')
    assert f('default-text') != f('endpos-true-text')
    assert f('default-json') == f('endpos-true-json')
    default = messages(role, 'r448', 'default-json')
    assert len(default) == 7 and default[-1]['severity'] == 'error'
    assert '?m.1' in default[2]['data']
    assert '?_' in messages(role, 'r448', 'mvars-false')[2]['data']
    assert ' [...]' in messages(role, 'r448', 'width10-on')[0]['data']
    assert ':10:7-10:35:' in f('endpos-true-text').decode()

for suite in ('r444', 'r448'):
    names = {c['name'] for c in C.values() if c['suite'] == suite}
    for name in names:
        assert out('old', suite, name) == out('new', suite, name)
for case in ('a', 'b', 'c', 'e'):
    assert cell('old', 'r444', case)['artifact_sha256'] != cell('new', 'r444', case)['artifact_sha256']

print('PASS: exact revisions and source blobs, 62 bounded cells, R444 relations, R448 option matrix, and relocated raw evidence')
