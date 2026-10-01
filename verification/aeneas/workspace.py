#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Manage disposable CI projects and protect persistent development edits.

Native Lean imports determine compilation order. This module copies handwritten
sources into fresh CI projects, preserves development projections unless their
baseline matches, and adds Rust locations to Lean diagnostics. Inspection reads
the existing compiled subject; it never implies that edited sources were rebuilt.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

import golden
from copy_back import MODULES as PROJECTIONS, STATE as PROJECTION_STATE

GENERATED = {'Specs.lean', 'ModelShapes.lean', 'Models.lean', 'Invariants.lean', 'Required.lean', 'lakefile.lean'} | {
    'Zerocopy/' + name for name in golden.FILES
}


def protect_projections(work):
    """Fail before development regeneration can destroy an edited projection."""
    state_path = work / PROJECTION_STATE
    state = json.loads(state_path.read_text()) if state_path.exists() else None
    if state is not None and (not isinstance(state, dict) or state.get('version') not in (1, 2) or
            set(state.get('sha256', {})) != set(PROJECTIONS)):
        raise ValueError(f'Invalid projection baseline: {state_path}; preserve projections before removing it')
    if state is not None and state['version'] == 2:
        import copy_back
        copy_back.validate(state)
    changed = []
    for module in PROJECTIONS:
        path = work / f'{module}.lean'
        if not path.exists():
            continue
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        if state is None or state['sha256'][module] != digest:
            changed.append(module)
    if changed:
        details = '\n'.join(f'  {work / (name + ".lean")} -> '
                            f'{work / (name + ".source-map.json")}' for name in changed)
        raise ValueError('Refusing to overwrite edited or unbaselined inline projections:\n' + details +
            '\nUse dev.sh --copy-back FULL_RUST_OWNER --dry-run to preview a version 2 baseline, '
            'then omit --dry-run to apply. Copy each authored fragment back to the Rust aeneas doc fence at its source-map '
            'file/line (shape fields from ModelShapes, decode/decode? body from Models, '
            'spec clauses from Specs). Do not copy generated imports, for targets, or derive/check '
            'commands. Preserve the edited projections and baseline until copying back is complete. '
            'Unannotated structural projections have no authored fragment; change the Rust type '
            'or generator instead. Rust comments remain authoritative.')


def record_projections(work, annotations=None):
    """Record full editing authority when available, or a legacy hash baseline.

    A legacy baseline can protect files from regeneration but cannot authorize
    reverse edits, because it contains no owned source spans or saved payloads.
    """
    if annotations is not None:
        import copy_back
        copy_back.record(work, annotations)
        return
    state = {'version': 1, 'sha256': {module: hashlib.sha256(
        (work / f'{module}.lean').read_bytes()).hexdigest() for module in PROJECTIONS}}
    (work / PROJECTION_STATE).write_text(json.dumps(state, indent=2) + '\n')


def module_name(relative):
    """Keep file components identical to their resolved Lean Name segments."""
    components = (*relative.parts[:-1], relative.stem)
    if any(not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', part) for part in components):
        raise ValueError(f'Handwritten Lean module paths require simple identifier components: {relative}')
    return '.'.join(components)


def handwritten(root):
    """Discover native modules while excluding generated files and Lake caches.

    Validate each path before returning it: a filename containing a literal dot
    must not silently become the same Lean name as a nested directory path.
    """
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
    """Replace a named disposable CI project with fresh handwritten sources.

    Check the destination before deletion. Development sources and their editing
    baseline never belong to this replacement path, even if they look generated.
    """
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
    """Stream Lean output unchanged and append any mapped Rust diagnostic.

    Source maps explain generated locations; they do not grant editing authority.
    Preserve the command's failing status even when a diagnostic was mapped.
    """
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
    """Build native modules, then refresh the audit even when Lake caches imports."""
    run_checked(['lake', 'build'], root, work)
    # Lake checks every native module with package-wide warnings as errors.
    # Fresh CI initialization removes local artifacts; development keeps its
    # own dependency cache and lets Lake invalidate changed modules.
    # The audit also writes the proof graph; run it even when Lake caches imports.
    run_checked(['lake', 'env', 'lean', '-DwarningAsError=true', 'Check.lean'], root, work)


def inspect_spec(root, work, spec):
    """Report one compiled contract and its existing binding without rebuilding.

    Validate command identifiers before constructing Lean source. Metadata and
    fingerprints describe the available project, so report their limitations
    explicitly rather than treating inspection as a fresh verification result.
    """
    name = spec if spec.startswith('Zerocopy.Specs.') else 'Zerocopy.Specs.' + spec
    if not re.fullmatch(r'Zerocopy\.Specs\.[A-Za-z_][A-Za-z_0-9]*', name):
        raise ValueError('Inspection requires a simple compiled specification name')
    bindings = json.loads((work / 'bindings.json').read_text())
    entries = [entry for entry in bindings['bindings'].values()
               if entry.get('kind') == 'function' and entry.get('spec') == name.rsplit('.', 1)[1]]
    if len(entries) != 1:
        raise ValueError('Inspection requires exactly one existing Rust/spec binding')
    entry = entries[0]
    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', entry['raw']):
        raise ValueError('Invalid extracted declaration in existing binding')
    print(f'Project: {work} ({bindings["mode"]}); Rust owner: {entry["file"]}:{entry["open_line"]}', flush=True)
    print(f'Binding source/model fingerprints: {bindings["sources"]} / {bindings["model"]}', flush=True)
    print(f'Pinned toolchain/configuration: {root / "verification/aeneas/toolchain.sh"}; '
          f'extraction driver: {root / "verification/aeneas/run.sh"}', flush=True)
    toolchain = work / 'lean-toolchain'
    print('Project toolchain: ' + (toolchain.read_text().strip() if toolchain.exists() else 'unavailable'), flush=True)
    llbc = work / 'zerocopy.llbc'
    if llbc.exists():
        print(f'Available extraction file: {llbc}', flush=True)
        translated = json.loads(llbc.read_text())['translated']
        targets = [{'target': item['key'], **{key: value for key, value in item['value'].items()
                    if key != 'primitive_alignments'}} for item in translated['target_information']]
        options = {key: value for key, value in translated['options'].items()
                   if key not in {'start_from', 'dest_file'}}
        print('Available extraction target metadata: ' + json.dumps(targets), flush=True)
        print('Available extraction options: ' + json.dumps(options), flush=True)
        print('LLBC metadata describes this file; legacy bindings do not certify its identity with compiled imports.', flush=True)
    else:
        print('Extraction target/configuration metadata unavailable in this project; no target is inferred from the host.', flush=True)
    premises = root / 'verification/aeneas/SEMANTICS.md'
    if premises.is_file():
        print(f'External Rust/ABI premises: {premises} (Explicit Rust premise); '
              'compiler/target layout correspondence and Rust safety remain assumptions.', flush=True)
    else:
        print('Detailed Rust/ABI premise document unavailable in this stage. '
              f'Available scope and translation trust boundary: {root / "verification/aeneas/README.md"}', flush=True)
    graph = work / 'proof-dependencies.json'
    if graph.exists():
        theorem = 'Zerocopy.Proofs.' + name.rsplit('.', 1)[1]
        print('Existing audited proof graph: ' + json.dumps([item for item in json.loads(graph.read_text())
              if item['theorem'] == theorem]), flush=True)
    # Reuse the native imported .olean files. A temporary command file outside
    # the project cannot overwrite its sources or trigger a second Lake build.
    source = (root / 'verification/aeneas/lean/InspectSpec.lean').read_text()
    with tempfile.TemporaryDirectory(prefix='aeneas-inspect-') as directory:
        path = Path(directory) / 'Inspect.lean'
        count = len(entry['generics']) + len(entry['inputs'])
        path.write_text(source + f'\ncheck_spec_binding {name} for {entry["raw"]} with {count}\n' +
                        'inspect_spec ' + name + '\n')
        run_checked(['lake', 'env', 'lean', '-DwarningAsError=true', str(path)], root, work)
    print('Inspection reads compiled declarations; run dev.sh --check to refresh and audit edited sources.', flush=True)


def main():
    """Keep preview/apply editing, regeneration protection, and inspection explicit."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['initialize', 'check', 'protect', 'inspect', 'copy-back'])
    parser.add_argument('work', type=Path)
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--backend', type=Path)
    parser.add_argument('--spec', help='Short or qualified compiled specification name')
    parser.add_argument('--owner', help='Full Rust annotation owner for copy-back')
    parser.add_argument('--apply', action='store_true', help='Apply the previewed copy-back plan')
    args = parser.parse_args()
    if args.command == 'copy-back':
        if not args.owner:
            parser.error('copy-back requires --owner')
        import copy_back
        try:
            copy_back.copy_back(args.root, args.work, args.owner, apply=args.apply)
        except (ValueError, OSError, UnicodeError) as error:
            parser.exit(1, f'Copy-back failed: {error}\n')
        return
    if args.owner or args.apply:
        parser.error('--owner and --apply require copy-back')
    root, work = args.root.resolve(), args.work.resolve()
    if args.command == 'initialize':
        if args.backend is None:
            parser.error('initialize requires --backend')
        initialize(root, work, args.backend.resolve())
    elif args.command == 'protect':
        protect_projections(work)
    elif args.command == 'inspect':
        if not args.spec:
            parser.error('inspect requires --spec')
        inspect_spec(root, work, args.spec)
    else:
        check(root, work)


if __name__ == '__main__':
    main()
