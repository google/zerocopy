#!/usr/bin/env python3
"""Parse rocq dev/doc/critical-bugs.md into entries and count them by section.

Rules: every '####' heading is an entry. A '###' heading is an entry iff the
next non-blank line starts with '- ' (a field list); otherwise it is a
category. '##' headings are top-level groups. The Table of Contents is skipped.
Usage: count_critical_bugs.py path/to/critical-bugs.md
"""
import re, sys, collections
lines = open(sys.argv[1], encoding='utf-8').read().split('\n')
def next_nonblank(i):
    j = i + 1
    while j < len(lines) and not lines[j].strip():
        j += 1
    return lines[j] if j < len(lines) else ''
group = cat = None
entries = []
for i, l in enumerate(lines):
    m = re.match(r'^(#{2,4}) (.*)$', l)
    if not m:
        continue
    lvl, title = len(m.group(1)), m.group(2).strip()
    if title == 'Table of Contents':
        continue
    if lvl == 2:
        group, cat = title, None
        continue
    if lvl == 4 or next_nonblank(i).startswith('- '):
        fields = {}
        j = i + 1
        while j < len(lines) and not re.match(r'^#{2,4} ', lines[j]):
            fm = re.match(r'^- ([^:]+):\s*(.*)$', lines[j])
            if fm:
                fields.setdefault(fm.group(1).strip(), fm.group(2).strip())
            j += 1
        entries.append(dict(line=i + 1, level=lvl, group=group, category=cat, title=title, fields=fields))
    else:
        cat = title
print('TOTAL ENTRIES', len(entries))
seen = []
by = collections.Counter()
for e in entries:
    k = (e['group'], e['category'])
    by[k] += 1
    if k not in seen:
        seen.append(k)
for k in seen:
    print(f'{by[k]:3d}  {k[0]} / {k[1]}')
print('MIS-LEVELED (### used for an entry):', [(e['line'], e['title']) for e in entries if e['level'] == 3])
kw = re.compile(r'print assumptions|coqchk|rocqchk|roqchk|unsafe|typing flag|universe checking|guard checking', re.I)
print('ENTRIES WHOSE TITLE MENTIONS AN AUDIT/CHECKER/UNSAFE-FLAG KEYWORD:')
for e in entries:
    if kw.search(e['title']):
        print(f"  L{e['line']}: {e['title']}  || impacted coqchk versions: {e['fields'].get('impacted coqchk versions', '(field absent)')}")
vm = [e for e in entries if re.search(r'\bvm\b|native', e['fields'].get('component', ''), re.I)]
print('ENTRIES WHOSE component FIELD MENTIONS VM or native:', len(vm))
nochk = [e for e in entries if re.match(r'none', e['fields'].get('impacted coqchk versions', ''), re.I)]
print('ENTRIES WITH "impacted coqchk versions" STARTING "none":', len(nochk))
absent = [e for e in entries if 'impacted coqchk versions' not in e['fields']]
print('ENTRIES WITHOUT an "impacted coqchk versions" FIELD:', len(absent))
