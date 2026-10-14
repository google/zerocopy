"""Static source inventory, not an elaborated theorem-axiom checker.

Usage: python3 -B audit_source.py /path/to/pinned/iris-lean/Iris
Prints JSON to stdout; does not modify the examined source tree.
"""
import json
import re
import sys
from pathlib import Path


def strip_comments_and_strings(source):
    result = []
    i = 0
    depth = 0
    line_comment = False
    string = False
    while i < len(source):
        pair = source[i:i + 2]
        char = source[i]
        if depth:
            if pair in ('/-', '-/'):
                depth += 1 if pair == '/-' else -1
                result.extend('  ')
                i += 2
                continue
            result.append('\n' if char == '\n' else ' ')
            i += 1
            continue
        if line_comment:
            if char == '\n':
                line_comment = False
            result.append('\n' if char == '\n' else ' ')
            i += 1
            continue
        if string:
            result.append('\n' if char == '\n' else ' ')
            if char == '\\' and i + 1 < len(source):
                result.append('\n' if source[i + 1] == '\n' else ' ')
                i += 2
                continue
            if char == '"':
                string = False
            i += 1
            continue
        if pair in ('/-', '--'):
            depth = 1 if pair == '/-' else 0
            line_comment = pair == '--'
            result.extend('  ')
            i += 2
            continue
        if char == '"':
            string = True
            result.append(' ')
            i += 1
            continue
        result.append(char)
        i += 1
    return ''.join(result)


root = Path(sys.argv[1])
files = {'.'.join(p.relative_to(root).with_suffix('').parts): p
         for p in root.rglob('*.lean')}
imports = {}
candidates = []
for module, path in files.items():
    clean = strip_comments_and_strings(path.read_text())
    imports[module] = []
    for number, line in enumerate(clean.splitlines(), 1):
        match = re.match(r'^\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?(.+)', line)
        if match:
            imports[module].extend(match.group(1).split())
        if re.search(r'\bsorry\b|\baxiom\b|^\s*unsafe\s|\bnative_decide\b|\bimplemented_by\b|\bextern\b', line):
            candidates.append({'module': module, 'line': number,
                               'source': line.strip()})
seeds = ['Iris.ProgramLogic.Adequacy', 'Iris.ProgramLogic.TotalAdequacy']
seen = set()
external = set()
pending = seeds.copy()
while pending:
    module = pending.pop()
    if module in seen:
        continue
    seen.add(module)
    for imported in imports.get(module, []):
        if imported in files:
            pending.append(imported)
        else:
            external.add(imported)
print(json.dumps({
    'revision': '81bc35088ba67d465db008f5261a9b341eb6cf6c',
    'scan': 'Nested comments and strings stripped; static imports, including import all. Not elaborated theorem dependency closure.',
    'modules_scanned': len(files), 'seeds': seeds,
    'local_import_closure': sorted(seen), 'external_imports': sorted(external),
    'active_candidates': candidates,
    'closure_candidates': [c for c in candidates if c['module'] in seen],
}, indent=2))
