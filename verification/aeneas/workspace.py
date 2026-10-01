#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Prepare fresh CI projects and check native Lean sources with Rust locations."""

import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess

import golden

GENERATED = {'Specs.lean', 'Invariants.lean', 'Required.lean', 'lakefile.lean'} | {
    'Zerocopy/' + name for name in golden.FILES
}


def handwritten(root):
    sources = root / 'verification/aeneas/lean'
    return sorted(path.relative_to(sources) for path in sources.rglob('*.lean')
                  if '.lake' not in path.relative_to(sources).parts
                  and str(path.relative_to(sources)) not in GENERATED)


def initialize(root, work, backend):
    # Only the two disposable CI projects may be replaced. The developer's
    # project contains checked-in proof sources and must never be removed.
    expected = root / 'target/aeneas'
    if work.parent.resolve() != expected.resolve() or work.name not in {
            'verification', 'golden-verification'}:
        raise ValueError('Fresh CI workspaces must be the disposable Aeneas projects')
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    for relative in handwritten(root):
        destination = work / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / 'verification/aeneas/lean' / relative, destination)
    shutil.copyfile(backend / 'lean-toolchain', work / 'lean-toolchain')


def run_checked(command, root, work):
    locations = {}
    for module in ('Specs', 'Invariants'):
        mapping = work / f'{module}.source-map.json'
        locations[module] = json.loads(mapping.read_text()) if mapping.exists() else {}
    with subprocess.Popen(command, cwd=work, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, text=True) as process:
        for line in process.stdout:
            print(line, end='', flush=True)
            match = re.search(r'(?:^|[ /])(Specs|Invariants)\.lean:(\d+):\d+:', line)
            if match and (location := locations[match[1]].get(match[2])):
                kind = 'specification' if match[1] == 'Specs' else 'invariant'
                print(f'Inline {kind}: {root / location["file"]}:{location["line"]}',
                      flush=True)
        status = process.wait()
    if status:
        raise subprocess.CalledProcessError(status, command)


def check(root, work):
    run_checked(['lake', 'build'], root, work)
    # Lake checks every native module with package-wide warnings as errors.
    # Fresh CI initialization removes local artifacts; development keeps its
    # own dependency cache and lets Lake invalidate changed modules.
    # The audit also writes the proof graph; run it even when Lake caches imports.
    run_checked(['lake', 'env', 'lean', '-DwarningAsError=true', 'Check.lean'], root, work)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['initialize', 'check'])
    parser.add_argument('work', type=Path)
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--backend', type=Path)
    args = parser.parse_args()
    root, work = args.root.resolve(), args.work.resolve()
    if args.command == 'initialize':
        if args.backend is None:
            parser.error('initialize requires --backend')
        initialize(root, work, args.backend.resolve())
    else:
        check(root, work)


if __name__ == '__main__':
    main()
