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

GENERATED = {'Specs.lean', 'ModelShapes.lean', 'Models.lean', 'Invariants.lean', 'Required.lean', 'lakefile.lean'} | {
    'Zerocopy/' + name for name in golden.FILES
}


def module_name(relative):
    """Keep file components identical to their resolved Lean Name segments."""
    components = (*relative.parts[:-1], relative.stem)
    if any(not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', part) for part in components):
        raise ValueError(f'Handwritten Lean module paths require simple identifier components: {relative}')
    return '.'.join(components)


def handwritten(root):
    sources = root / 'verification/aeneas/lean'
    paths = sorted(path.relative_to(sources) for path in sources.rglob('*.lean')
                   if '.lake' not in path.relative_to(sources).parts
                   and str(path.relative_to(sources)) not in GENERATED)
    for path in paths:
        module_name(path)
    return paths


def retire_generated(work):
    """Remove only recognized artifacts of the retired invariant generator."""
    old = work / 'Invariants.lean'
    mapping = work / 'Invariants.source-map.json'
    if old.exists():
        text = old.read_text()
        if not (text.startswith(golden.HEADER) and 'public import DeriveValidity\n' in text
                and 'namespace Zerocopy.Invariants\n' in text):
            raise ValueError('Refusing to retire unrecognized Invariants.lean; preserve or relocate this file before regeneration')
    if mapping.exists():
        locations = json.loads(mapping.read_text())
        if not isinstance(locations, dict) or any(
                not isinstance(key, str) or not key.isdecimal()
                or not isinstance(value, dict) or set(value) != {'file', 'line'}
                or not isinstance(value['file'], str) or not isinstance(value['line'], int)
                for key, value in locations.items()):
            raise ValueError('Refusing to retire unrecognized Invariants.source-map.json')
    if old.exists():
        old.unlink()
    if mapping.exists():
        mapping.unlink()


def model_support(root):
    """Discover support modules; Check audits their compiled import closure."""
    return sorted(name for path in handwritten(root)
                  if (name := module_name(path)) == 'ModelSupport' or name.startswith('ModelSupport.'))


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
    for module in ('Specs', 'ModelShapes', 'Models'):
        mapping = work / f'{module}.source-map.json'
        locations[module] = json.loads(mapping.read_text()) if mapping.exists() else {}
    with subprocess.Popen(command, cwd=work, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, text=True) as process:
        for line in process.stdout:
            print(line, end='', flush=True)
            match = re.search(r'(?:^|[ /])(Specs|ModelShapes|Models)\.lean:(\d+):\d+:', line)
            if match and (location := locations[match[1]].get(match[2])):
                kind = 'specification' if match[1] == 'Specs' else 'model'
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
