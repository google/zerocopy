# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Require a fresh kernel proof before ignoring an empty conditional drop.

This driver never calculates ownership events. Lean reads the complete frozen
compiler snapshot and checks its own strict projection and ownership analysis.
The driver binds that proof to the exact body the admission traversal visits.
"""

import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

import toolchain


def body_digest(body):
    return hashlib.sha256(json.dumps(body, sort_keys=True).encode()).hexdigest()


def contains_drop(value):
    """Find candidates, without using this search to decide their safety.

    Searching every nested node includes unwind paths. The existing syntax
    audit still rejects unknown executable constructs independently of Lean.
    """
    if isinstance(value, dict):
        return 'Drop' in value or any(contains_drop(v) for v in value.values())
    if isinstance(value, list):
        return any(contains_drop(v) for v in value)
    return False


class KernelDrops:
    """One fresh checker build, shared by this inspection's two snapshots."""

    MODULES = ('DropOwnership', 'DropJson', 'DropAudit')

    def __init__(self, root, work):
        self.root = root.resolve()
        self.parent = work.resolve()
        self.work = None
        self.snapshots = {}
        self.proofs = {}

    def freeze(self, stage, contents):
        # This is the exact buffer parsed by Admission, not a second file read.
        self.snapshots[stage] = contents

    def initialize(self):
        if self.work is not None:
            return
        tools = Path(os.environ.get('AENEAS_TOOLCHAIN_DIR',
                                   self.root / 'target/aeneas/toolchain')).resolve()
        metadata, _ = toolchain.validate(self.root, tools)
        self.work = Path(tempfile.mkdtemp(prefix='empty-drops-', dir=self.parent))
        self.lean = tools / 'lean/bin/lean'
        self.env = toolchain.runtime_env(tools)
        # Do not inherit another project's modules or accept stale witnesses.
        self.env['LEAN_PATH'] = str(self.work)
        self.metadata = metadata
        for module in self.MODULES:
            shutil.copyfile(self.root / 'verification/aeneas/lean' / (module + '.lean'),
                            self.work / (module + '.lean'))
            self.run(module)

    def run(self, module, env=None):
        command = [str(self.lean), '-o', module + '.olean', module + '.lean']
        log = self.work / (module + '.log')
        with log.open('w') as output:
            result = subprocess.run(command, cwd=self.work, env=env or self.env,
                                    stdout=output, stderr=subprocess.STDOUT)
        if result.returncode:
            raise ValueError(f'Kernel rejected empty-drop admission; see {log}:\n'
                             + log.read_text()[-6000:])

    def certify(self, stage, function):
        self.initialize()
        index = function['def_id']
        if type(index) is not int or index < 0:
            raise ValueError('Drop admission requires a native function index')
        contents = self.snapshots[stage]
        data = json.loads(contents)
        matches = [f for f in data['translated']['fun_decls']
                   if f and f.get('def_id') == index]
        if len(matches) != 1 or matches[0]['body'] != function['body']:
            raise ValueError('Drop proof input differs from the inspected compiler body')
        snapshot = self.work / (stage + '.json')
        if snapshot.exists():
            if snapshot.read_bytes() != contents:
                raise ValueError('Frozen drop-admission snapshot changed')
        else:
            snapshot.write_bytes(contents)
        module = f'DropWitness_{stage}_{index}'
        witness = self.work / (module + '.lean')
        source = (
            'import DropAudit\n'
            'set_option maxRecDepth 100000\n'
            'set_option maxHeartbeats 20000000\n'
            f'certify_empty_drops {index}\n')
        witness.write_text(source)
        env = dict(self.env, AENEAS_DROP_SNAPSHOT=str(snapshot))
        self.run(module, env)
        # An editor must not repair a temporary proof input while Lean runs
        # and leave a certificate attributed to the original compiler body.
        if snapshot.read_bytes() != contents or witness.read_text() != source:
            raise ValueError('Drop proof inputs changed during kernel checking')
        record = {'function_def_id': index,
                  'body_sha256': body_digest(function['body']),
                  'snapshot_sha256': hashlib.sha256(contents).hexdigest(),
                  'proof_module': module,
                  'proof_sha256': hashlib.sha256(
                      (self.work / (module + '.olean')).read_bytes()).hexdigest()}
        self.proofs[stage, index] = record
        return record
