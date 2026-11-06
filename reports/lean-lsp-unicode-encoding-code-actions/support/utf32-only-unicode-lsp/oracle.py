#!/usr/bin/env python3
"""Freeze independent Unicode LSP coordinates before launching Lean."""

import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ORIGINAL = '#check ("😀é", unknownName)\n'
PATCHED = '#check ("😀é", Nat.zero)\n'
TOKEN = 'unknownName'
assert ORIGINAL.count(TOKEN) == 1
start = ORIGINAL.index(TOKEN)
end = start + len(TOKEN)
assert ORIGINAL[:start] + 'Nat.zero' + ORIGINAL[end:] == PATCHED


def coords(prefix):
    return {
        'unicode_scalars': len(prefix),
        'utf16_code_units': len(prefix.encode('utf-16-le')) // 2,
        'utf8_bytes': len(prefix.encode('utf-8')),
    }


orig = HERE / 'fixture/Encoding.lean'
patched = HERE / 'fixture/EncodingPatched.lean'
orig.write_bytes(ORIGINAL.encode('utf-8'))
patched.write_bytes(PATCHED.encode('utf-8'))
data = {
    'schema': 1,
    'original_sha256': hashlib.sha256(orig.read_bytes()).hexdigest(),
    'patched_sha256': hashlib.sha256(patched.read_bytes()).hexdigest(),
    'token': TOKEN,
    'line_zero_based': 0,
    'begin': coords(ORIGINAL[:start]),
    'end': coords(ORIGINAL[:end]),
    'replacement': 'Nat.zero',
    'source_scalar_range': [start, end],
    'utf32_only_change_range': {
        'start': {'line': 0, 'character': coords(ORIGINAL[:start])['unicode_scalars']},
        'end': {'line': 0, 'character': coords(ORIGINAL[:end])['unicode_scalars']},
    },
    'utf8_only_change_range': {
        'start': {'line': 0, 'character': coords(ORIGINAL[:start])['utf8_bytes']},
        'end': {'line': 0, 'character': coords(ORIGINAL[:end])['utf8_bytes']},
    },
    'utf16_only_change_range': {
        'start': {'line': 0, 'character': coords(ORIGINAL[:start])['utf16_code_units']},
        'end': {'line': 0, 'character': coords(ORIGINAL[:end])['utf16_code_units']},
    },
}
assert len(set(data['begin'].values())) == 3
(HERE / 'oracle.json').write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n')
print(json.dumps(data, ensure_ascii=False))
