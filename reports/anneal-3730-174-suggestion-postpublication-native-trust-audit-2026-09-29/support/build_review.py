#!/usr/bin/env python3
"""Derive the individually checked suggestion table from retained live text and v24."""
import csv
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
V24 = REPORTS / 'anneal-3730-3731-final-coverage-audit-2026-09-29-v24/support'
I145_LINKS = {'A01', 'A02', 'A08', 'C01', 'F05', 'G01', 'G02', 'G12', 'L01', 'O03'}
COMPLETE = {'C04', 'C13', 'N11'}
HARD_LOCAL_GATES = {
    'E01': 'Same-process Aeneas runtime unavailable: no local OCaml/Dune/opam or callable library host.',
    'E02': 'Same-process Aeneas runtime unavailable: no local OCaml/Dune/opam or callable library host.',
    'E03': 'Same-process Aeneas runtime unavailable: no local OCaml/Dune/opam or callable library host.',
    'F03': 'No cached Lean/Lake revision later than 4.30.0-rc2 for the requested comparison.',
    'F04': 'No built actual Anneal omnibus archive in the scoped local-tools/checkout inventory.',
    'G03': 'No installed real MCP SDK/client plus Anneal task broker; raw-wire toy is already covered.',
    'G15': 'No producer-authenticated map, Anneal navigation client, or consented agent task interface.',
    'L09': 'No existing Lean MCP adapter and two real clients; raw bridge is already covered.',
    'L10': 'Same-process Aeneas runtime unavailable: no local OCaml/Dune/opam or callable library host.',
}
G09_GATE = ('The cached native-plugin initializer and Lake configuration now each wrote an owned '
            'outside-workspace marker when allowed and failed under targeted macOS write denial. '
            'Anneal MCP read/mutate tiers, user trust authorization before workspace execution, '
            'broad containment/resource limits, and generated-to-authored edit authority remain.')

def sha_bytes(data):
    return hashlib.sha256(data).hexdigest()

def rows(path):
    with path.open(newline='') as stream:
        return list(csv.DictReader(stream))

def main():
    issue = (HERE / 'live-issue-body.md').read_text()
    comment = (HERE / 'live-3731-crosswalk-comment.md').read_text()
    v24 = {row['3730_id']: row for row in rows(V24 / '3730-crosswalk-final-v24.csv')}
    headings = list(re.finditer(r'(?m)^### ([A-O]\d{2})\. ([^\n]+)$', issue))
    cross = {item: (title.strip(), set(re.findall(r'I\d{3}', destinations)))
             for item, title, destinations in re.findall(
                 r'(?m)^\| ([A-O]\d{2}) \| ([^|]+) \| ([^|]+) \|', comment)}
    assert len(headings) == len(v24) == len(cross) == 174
    assert sum(len(dest) for _, dest in cross.values()) == 345
    package_fields = [key for key in next(iter(v24.values()))
                      if key.endswith(('_experiment_packages', '_evidence_packages', '_review_package'))]
    out = []
    for n, match in enumerate(headings):
        item, original_heading = match.groups()
        assert item in v24
        end = headings[n + 1].start() if n + 1 < len(headings) else issue.index('\n---\n\n## Suggested sequencing', match.end())
        requested = issue[match.start():end].strip()
        row = v24[item]
        title, destinations = cross[item]
        assert title == row['suggestion']
        assert destinations == set(row['3731_destinations'].split(';'))
        cited = sorted({name for field in package_fields for name in row[field].split(';') if name})
        assert cited and all((REPORTS / name / 'REPORT.md').is_file() for name in cited)
        status = row['v24_status']
        assert status in ('complete', 'partial', 'not-run', 'conditional')
        assert (status == 'complete') == (item in COMPLETE)
        relation = ('new native-plugin I126 control, directly linked' if item == 'G09'
                    else 'v24 I076 control directly linked' if item == 'D07'
                    else 'v24 I076→I145 cross-slice witness only' if item in I145_LINKS
                    else 'I005/I127 have no direct #3730 destination; no new linked component')
        if item == 'G09':
            local = 'new bounded native-plugin control executed; entire G09 scope remains open'
            gate = G09_GATE
        elif item in HARD_LOCAL_GATES:
            local = HARD_LOCAL_GATES[item]
            gate = row['v24_specific_remaining_delta']
        else:
            local = 'No distinct remaining cached-only trial identified for this exact scope after cited component review.'
            gate = row['v24_specific_remaining_delta']
        if status == 'complete':
            assessment = 'Original falsification/direct-tool method answered at its explicitly pinned fixture scope; no broader Anneal acceptance inferred.'
        elif status == 'not-run':
            assessment = 'The distinguishing original method has no matching execution; cited work covers narrower components only.'
        elif status == 'conditional':
            assessment = 'The original optional same-process method remains conditional on an unavailable callable Aeneas library surface.'
        else:
            assessment = 'Cited experiments cover bounded components; the entire requested original method is not supported.'
        out.append({
            'id': item,
            'original_heading': original_heading,
            'consolidation_title': title,
            'requested_text_sha256': sha_bytes(requested.encode()),
            'requested_text': requested,
            'destinations': ';'.join(sorted(destinations)),
            'v24_status': status,
            'audit_status': status,
            'entire_requested_scope_supported': 'true' if item in COMPLETE else 'false',
            'scope_assessment': assessment,
            'new_evidence_relation': relation,
            'cached_only_decision': local,
            'remaining_gate': gate,
            'next_prerequisite': row['v24_next_prerequisite'],
            'cited_packages': ';'.join(cited),
        })
    path = HERE / 'row-decisions.csv'
    with path.open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(out[0]), lineterminator='\n')
        writer.writeheader()
        writer.writerows(out)
    cited = sorted({name for row in out for name in row['cited_packages'].split(';') if name})
    with (HERE / 'cited-package-inventory.csv').open('w', newline='') as stream:
        writer = csv.writer(stream, lineterminator='\n')
        writer.writerow(('package', 'report_md_sha256', 'report_json_sha256'))
        for name in cited:
            root = REPORTS / name
            writer.writerow((name, *(sha_bytes((root / file).read_bytes())
                                     for file in ('REPORT.md', 'REPORT.json'))))
    print(f'{len(out)} suggestions, {sum(len(row["destinations"].split(";")) for row in out)} links, {len(cited)} cited packages')

if __name__ == '__main__':
    main()
