#!/usr/bin/env python3
"""Run python-jsonschema against the JSON-Schema-Test-Suite `validation/` tree.

Classifies every disagreement with the suite's expected result as
  FALSE_ACCEPT  (suite says invalid, validator accepted  -> fail-open)
  FALSE_REJECT  (suite says valid,   validator rejected -> fail-closed)
  CRASH         (validator raised an exception)
Usage: run_jsts.py <suite_root> <dialect: 4|6|7|2019|2020> [--include-optional] [--format-mode tags|off|on]
  --format-mode tags : honour the suite's format-assertion / format-annotation tags (default)
  --format-mode off  : never enable format assertion (run every case, including format-assertion ones)
  --format-mode on   : always enable format assertion
"""
import json, sys, pathlib, collections, argparse, time
import jsonschema
from referencing import Registry, Resource
from referencing.jsonschema import specification_with

DIALECTS = {
    '4': ('http://json-schema.org/draft-04/schema#', jsonschema.Draft4Validator),
    '6': ('http://json-schema.org/draft-06/schema#', jsonschema.Draft6Validator),
    '7': ('http://json-schema.org/draft-07/schema#', jsonschema.Draft7Validator),
    '2019': ('https://json-schema.org/draft/2019-09/schema', jsonschema.Draft201909Validator),
    '2020': ('https://json-schema.org/draft/2020-12/schema', jsonschema.Draft202012Validator),
}

def is_compatible(compat, v):
    """Literal transcription of the suite README's isCompatible pseudocode."""
    if compat is None:
        return True
    ok = True
    for c in str(compat).split(','):
        c = c.strip()
        if c.startswith('<='):
            op, ver = '<=', int(c[2:])
        elif c.startswith('='):
            op, ver = '=', int(c[1:])
        else:
            op, ver = '', int(c)
        if op == '':
            ok = v >= ver
        elif op == '<=':
            ok = v <= ver
        else:
            ok = v == ver
        if v <= ver:
            break
    return ok

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('root'); ap.add_argument('dialect')
    ap.add_argument('--include-optional', action='store_true')
    ap.add_argument('--format-mode', default='tags', choices=['tags', 'off', 'on'])
    a = ap.parse_args()
    meta, V = DIALECTS[a.dialect]
    vnum = int(a.dialect)
    tests = pathlib.Path(a.root) / 'validation' / 'tests'
    files = sorted(p for p in tests.glob('*.json'))
    if a.include_optional:
        files += sorted((tests / 'optional').rglob('*.json'))
    counts = collections.Counter(); bad = []
    t0 = time.perf_counter()
    for f in files:
        doc = json.loads(f.read_text())
        cases = doc['tests'] if isinstance(doc, dict) else doc
        for case in cases:
            if not is_compatible(case.get('compatibility'), vnum):
                counts['skipped_incompatible'] += 1; continue
            tags = set(case.get('tags', []))
            if a.format_mode == 'tags':
                fmt = 'format-assertion' in tags
            else:
                fmt = (a.format_mode == 'on')
            schema = case['schema']
            if isinstance(schema, dict) and '$schema' not in schema:
                schema = dict(schema, **{'$schema': meta})
            reg = Registry()
            for uri, ext in (case.get('externalSchemas') or {}).items():
                spec = specification_with(meta)
                reg = reg.with_resource(uri, Resource(contents=ext, specification=spec))
            kw = {'registry': reg}
            if fmt:
                kw['format_checker'] = V.FORMAT_CHECKER
            for t in case['tests']:
                counts['run'] += 1
                try:
                    got = V(schema, **kw).is_valid(t['data'])
                except Exception as e:
                    counts['CRASH'] += 1
                    bad.append(('CRASH', f.name, case['description'], t['description'], type(e).__name__))
                    continue
                if got == t['valid']:
                    counts['agree'] += 1
                elif t['valid'] is False:
                    counts['FALSE_ACCEPT'] += 1
                    bad.append(('FALSE_ACCEPT', f.name, case['description'], t['description'], ''))
                else:
                    counts['FALSE_REJECT'] += 1
                    bad.append(('FALSE_REJECT', f.name, case['description'], t['description'], ''))
    el = time.perf_counter() - t0
    print(json.dumps({'dialect': a.dialect, 'optional': a.include_optional, 'format_mode': a.format_mode,
                      'files': len(files), 'counts': counts, 'seconds': round(el, 2)}, sort_keys=True))
    byfile = collections.Counter((k, f) for k, f, *_ in bad)
    for (k, f), n in sorted(byfile.items()):
        print(f'  {k:12s} {n:4d}  {f}')
    for row in bad[:400]:
        print('   ', ' | '.join(row))

if __name__ == '__main__':
    main()
