#!/usr/bin/env python3
"""Validate retained claim-relative Lean caller taint and stale artifact control."""
import json
from pathlib import Path

d=json.loads((Path(__file__).resolve().parent/'results.json').read_text())
assert d['lean_sha256']=='b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997'
r={x['label']:x for x in d['records']}
assert set(r)=={'axiom','concrete-source-stale-axiom-olean','concrete','admitted'}
for x in r.values():
    assert x['check']['exit']==0
    assert "'independent' does not depend on any axioms" in x['check']['stdout']
assert "'caller' depends on axioms: [model]" in r['axiom']['check']['stdout']
assert r['axiom']['artifact_sha256']==r['concrete-source-stale-axiom-olean']['artifact_sha256']
assert r['concrete-source-stale-axiom-olean']['source_sha256']==r['concrete']['source_sha256']
assert "'caller' depends on axioms: [model]" in r['concrete-source-stale-axiom-olean']['check']['stdout']
assert r['concrete']['artifact_sha256']!=r['axiom']['artifact_sha256']
assert "'caller' does not depend on any axioms" in r['concrete']['check']['stdout']
assert "'caller' depends on axioms: [sorryAx]" in r['admitted']['check']['stdout']
assert r['admitted']['artifact_sha256']!=r['concrete']['artifact_sha256']
print('I130 retained claim-relative caller/artifact taint controls passed')
