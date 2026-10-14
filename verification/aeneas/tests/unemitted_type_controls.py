# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Run the actual omitted-type audit with independent malformed dispositions.

The compiler snapshots remain read-only. Each temporary Lean fixture contains
exactly the production helper and disposition branch, with a minimal table.
"""

import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


def check(work):
    root = Path(__file__).resolve().parents[3]
    source = (root / 'verification/aeneas/lean/Check.lean').read_text()
    helper = source.split('private def checkUnemittedNativeType', 1)[1].split('run_elab do\n', 1)[0]
    helper = 'private def checkUnemittedNativeType' + helper
    branch = source.split('    if category == "unemitted-uninhabited" then\n', 1)[1].split(
        '    let .ok raw := row.getObjValAs? String "raw"', 1)[0]
    branch = '    if category == "unemitted-uninhabited" then\n' + branch
    manifest = json.loads((work / 'bindings.json').read_text())
    rows = [r for r in manifest['type_image'] if r['category'] == 'unemitted-uninhabited']
    if len(rows) != 1:
        raise AssertionError('Control requires one actual native uninhabited omission')
    baseline = rows[0]
    lean = Path(os.environ['AENEAS_TOOLCHAIN_DIR']) / 'lean/bin/lean'
    prefix = ('import Lean\nopen Lean Elab Command\n'
        'instance [BEq α] [BEq β] : BEq (Except α β) := ⟨fun a b => match a, b with '
        '| .ok x, .ok y => x == y | .error x, .error y => x == y | _, _ => false⟩\n')
    results = []

    def run(label, row, *, bound=False, compiled=False, expected=None):
        table = {row['rust']: {}} if bound else {}
        table_literal = json.dumps(json.dumps(table), ensure_ascii=False)
        row_literal = json.dumps(json.dumps(row, ensure_ascii=False), ensure_ascii=False)
        text = prefix + helper
        if compiled:
            text += 'opaque ' + row['expected_raw'] + ' : Type\n'
        text += ('run_elab do\n'
            '  let .ok table := Json.parse ' + table_literal + ' | throwError "bad test table"\n'
            '  let .ok entries := table.getObj? | throwError "bad test table"\n'
            '  let .ok specimen := Json.parse ' + row_literal + ' | throwError "bad test row"\n'
            '  let mode := "verified-live"\n'
            '  let env ← getEnv\n'
            '  let mut imageRust : Array String := #[]\n'
            '  for row in #[specimen] do\n'
            '    let .ok rust := row.getObjValAs? String "rust" | throwError "bad test Rust name"\n'
            '    let .ok category := row.getObjValAs? String "category" | throwError "bad test category"\n'
            '    let .ok parameterCount := row.getObjValAs? Nat "parameters" | throwError "bad test parameters"\n'
            + branch)
        with tempfile.TemporaryDirectory(prefix='aeneas-unemitted-type-') as tmp:
            fixture = Path(tmp) / 'Control.lean'
            fixture.write_text(text)
            result = subprocess.run([str(lean), str(fixture)], cwd=work,
                                    text=True, capture_output=True)
        diagnostic = result.stdout + result.stderr
        if expected is None:
            if result.returncode != 0:
                raise AssertionError(f'{label}: baseline failed: {diagnostic}')
        elif result.returncode == 0 or expected not in diagnostic:
            raise AssertionError(f'{label}: expected {expected}: {diagnostic}')
        results.append({'case': label, 'exit': result.returncode})

    run('actual native omission baseline', baseline)
    bad = copy.deepcopy(baseline); bad['raw'] = bad['expected_raw']
    run('pretend raw omission', bad, expected='malformed disposition')
    bad = copy.deepcopy(baseline); bad['parameters'] = 1
    run('pretend generic omission', bad, expected='malformed disposition')
    bad = copy.deepcopy(baseline); bad['native']['kind'] = {'Struct': []}
    run('pretend inhabited omission', bad, expected='compiler declaration')
    bad = copy.deepcopy(baseline); bad['native']['item_meta']['started_from'] = True
    run('pretend annotated compiler owner', bad, expected='compiler declaration')
    bad = copy.deepcopy(baseline); bad['expected_raw'] += 'Other'
    run('renamed raw disposition', bad, expected='changed its Rust identity')
    run('hidden source model claim', baseline, bound=True, expected='model claim')
    run('existing raw declaration', baseline, compiled=True, expected='compiled raw declaration')
    run('restored native omission baseline', baseline)
    return results


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit('usage: unemitted_type_controls.py VERIFICATION_DIR')
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
