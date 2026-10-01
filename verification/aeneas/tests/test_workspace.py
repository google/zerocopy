# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import contextlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import workspace


class WorkspaceTests(unittest.TestCase):
    def test_fresh_projects_copy_proof_submodules_and_remove_stale_files(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sources = root / 'verification/aeneas/lean'
            for relative in ('Proofs.lean', 'Proofs/Util.lean', 'Specs.lean',
                             'Required.lean', 'lakefile.lean', 'Zerocopy/Funs.lean',
                             '.lake/packages/Dependency.lean'):
                path = sources / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(relative)
            backend = root / 'backend'
            backend.mkdir()
            (backend / 'lean-toolchain').write_text('leanprover/lean4:v4.31.0')
            work = root / 'target/aeneas/verification'
            work.mkdir(parents=True)
            (work / 'RemovedProof.lean').write_text('stale')
            workspace.initialize(root, work, backend)
            self.assertEqual({str(path.relative_to(work))
                              for path in work.rglob('*') if path.is_file()},
                             {'Proofs.lean', 'Proofs/Util.lean', 'lean-toolchain'})
            with self.assertRaises(ValueError):
                workspace.initialize(root, sources, backend)
            self.assertTrue((sources / 'Proofs/Util.lean').exists())

    def test_diagnostics_preserve_lean_output_and_add_rust_location_on_failure(self):
        for module, kind in [('Specs', 'specification'), ('Invariants', 'invariant')]:
            with self.subTest(module=module), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                work = root / 'project'
                work.mkdir()
                (work / f'{module}.source-map.json').write_text(json.dumps({
                    '17': {'file': 'zerocopy/src/layout.rs', 'line': 42}}))
                output = io.StringIO()
                message = f'{module}.lean:17:9: error: unknown identifier'
                command = [sys.executable, '-c',
                           f'print({message!r}); raise SystemExit(1)']
                with contextlib.redirect_stdout(output), self.assertRaises(
                        subprocess.CalledProcessError):
                    workspace.run_checked(command, root, work)
                self.assertIn(message, output.getvalue())
                self.assertIn(f'Inline {kind}: {root}/zerocopy/src/layout.rs:42',
                              output.getvalue())


if __name__ == '__main__':
    unittest.main()
