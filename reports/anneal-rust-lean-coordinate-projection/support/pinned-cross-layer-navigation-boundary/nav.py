#!/usr/bin/env python3
"""Hash-gated navigation over a derived, deliberately unauthenticated join manifest."""
from __future__ import annotations

import hashlib
from pathlib import Path


class StaleArtifact(ValueError):
    pass


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _generation(manifest: dict, case: str, rust_path: Path) -> dict:
    generation = manifest['generations'][case]
    if digest(rust_path) != generation['artifacts']['rust_source']['sha256']:
        raise StaleArtifact('Rust source digest differs from selected generation')
    return generation


def forward(manifest: dict, case: str, rust_path: Path, byte_offset: int) -> list[dict]:
    generation = _generation(manifest, case, rust_path)
    if byte_offset < 0 or byte_offset >= rust_path.stat().st_size:
        return []
    result = []
    for entry in generation['entries']:
        if not (entry['rust_item']['byte_range'][0] <= byte_offset < entry['rust_item']['byte_range'][1]):
            continue
        target = {'rust_item': entry['rust_item']['qualified_name'],
                  'charon_def_id': entry['charon']['def_id'],
                  'obligation': entry['obligation']['name'],
                  'proof_line': entry['obligation']['proof_line']}
        if 'declarations' in entry['aeneas']:
            target['generated_decls'] = [
                {'name': d['qualified_lean_name'], 'role': d['role'], 'lines': d['declaration_lines']}
                for d in entry['aeneas']['declarations']]
        else:
            target['generated_decl'] = entry['aeneas']['qualified_lean_name']
            target['generated_lines'] = entry['aeneas']['declaration_lines']
        result.append(target)
    return result


def reverse(manifest: dict, case: str, rust_path: Path, lean_path: Path,
            role: str, line: int) -> list[dict]:
    generation = _generation(manifest, case, rust_path)
    expected = generation['artifacts'][role]['sha256']
    if digest(lean_path) != expected:
        raise StaleArtifact(f'{role} digest differs from selected generation')
    if role == 'generated_funs':
        selected = [(e, d['declaration_lines']) for e in generation['entries']
                    for d in e['aeneas'].get('declarations', [e['aeneas']])]
    elif role in ('proof', 'lean_check'):
        selected = [(e, [e['obligation']['proof_line'], e['obligation']['proof_line']])
                    for e in generation['entries']]
    elif role == 'goal_attempt':
        selected = [(e, [e['obligation']['goal_trace_line'], e['obligation']['goal_trace_line']])
                    for e in generation['entries']]
    elif role == 'goal_probe':
        selected = [(e, [e['obligation']['goal_trace_line'], e['obligation']['goal_trace_line']])
                    for e in generation['entries']]
    else:
        raise ValueError('unsupported role')
    return [{'rust_item': entry['rust_item']['qualified_name'],
             'rust_byte_range': entry['rust_item']['byte_range'],
             'charon_def_id': entry['charon']['def_id'],
             'evidence_class': entry['cross_stage_join_class']}
            for entry, (start, end) in selected if start <= line <= end]
