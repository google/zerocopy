#!/usr/bin/env python3
"""Revalidate report/section identities and exact original research questions."""
import hashlib,json,re
from pathlib import Path
here=Path(__file__).resolve().parent
corpus=here.parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
original=corpus/'reports/anneal-research-agenda-2026-10-14/research-questions.json'
data=json.loads((here/'question-crosswalk.json').read_text())
assert sha(original)==data['original_question_sha256']
questions={q['id']:q for q in json.loads(original.read_text())}
entries=data['entries'];assert len(entries)==364 and {e['id'] for e in entries}==set(questions)
bindings=0
for e in entries:
    q=questions[e['id']]
    for k in ['id','title','question','rationale','issue']:assert e[k]==q[k],(e['id'],k)
    assert e['assessment'] in ['bounded_research_answer','investigated_boundary'],e['id']
    assert not e['remaining_research'],e['id']
    assert e['findings'],e['id']
    for ref in e['findings']+e['boundaries']:
        p=corpus/ref['path'];assert p.is_file() and sha(p)==ref['report_sha256'],ref
        lines=p.read_text().splitlines(keepends=True)
        start=ref['line']-1;end=ref['end_line']
        match=re.match(r'^(#{1,6}) (.*?)\s*$',lines[start]);assert match and match[2]==ref['heading']
        assert hashlib.sha256(''.join(lines[start+1:end]).encode()).hexdigest()==ref['section_body_sha256'],ref
        bindings+=1
index=json.loads((here/'report-index.json').read_text());assert len(index)==90
for row in index:assert sha(corpus/row['path'])==row['report_sha256'],row
assert sum(row['kind']=='research' for row in index)==89
print(json.dumps({'status':'pass','questions':len(entries),'section_bindings':bindings,'research_reports':89,'agenda_reports':1}))
