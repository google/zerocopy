#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Freeze positive CI models and run failure controls in private build trees.

A baseline is built and audited before its consumers start. Each mutable package
and build directory belongs to exactly one family. Immutable installed packages
retain their archive paths. Completed command logs and exact statuses survive
sandbox removal. Failure does not prevent collection of other family results.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time

FAMILIES = ('authoring', 'trait-rounding', 'coverage', 'abi',
            'contracts', 'dependencies', 'admission', 'semantics')
MODELS = ('golden-verification', 'verification')
FIXTURES = ('NegativeControl.lean', 'WeakOutcome.lean',
            'RoundingConstructorControl.lean', 'RoundingDomainControl.lean',
            'Zerocopy/ScopeControl.lean', 'Zerocopy/ShapeControl.lean',
            'Zerocopy/ModelControl.lean', 'Proofs/WitnessOwnerControl.lean',
            'Proofs/PaddingDependencyControl.lean')
MUTABLE = ('rust_model', 'rust_model_aeneas')


def shell_status(status):
    return status if status >= 0 else 128 - status


def clear_mutable_outputs(project, modules=()):
    """Remove outputs, never source bytes or the immutable dependency archives."""
    if modules:
        # Leaf well-formedness checks retain the independent compiled audit and
        # rebuild the explicit subjects. Whole proof builds below clear all.
        for module in modules:
            relative = Path(*module.split('.'))
            for root in (project / '.lake/build/lib/lean', project / '.lake/build/ir'):
                for artifact in root.glob(str(relative) + '.*'):
                    if artifact.is_file():
                        artifact.unlink()
        return
    paths = [project / '.lake/build']
    manifest = json.loads((project / 'lake-manifest.json').read_text())
    private = project.parent / 'rust-model'
    for package in manifest['packages']:
        if package['name'] in MUTABLE:
            source = Path(package['dir']).resolve()
            if not source.is_relative_to(private.resolve()):
                raise ValueError(f'Mutable package is not private: {source}')
            paths.append(source / '.lake/build')
    for path in paths:
        if path.is_symlink():
            raise ValueError(f'Mutable build directory is a symlink: {path}')
        if path.exists():
            shutil.rmtree(path)


def subject_identity(subject, logs):
    """Record exact local source bytes in command evidence, excluding outputs."""
    if not (subject / 'lake-manifest.json').is_file():
        return None
    files = [path for path in subject.rglob('*.lean')
             if '.lake' not in path.relative_to(subject).parts
             and not path.is_relative_to(logs)]
    files.extend(path for name in ('bindings.json', '.inline-projections.json')
                 if (path := subject / name).is_file())
    return {str(path.relative_to(subject)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(files)}


class Cancellation:
    """Own direct child groups across preflight, baseline, and family phases."""
    def __init__(self, grace=2):
        self.signal = None
        self.when = None
        self.grace = grace
        self.children = set()

    def __enter__(self):
        self.previous = {sig: signal.signal(sig, self.interrupt)
                         for sig in (signal.SIGINT, signal.SIGTERM)}
        return self

    def interrupt(self, signum, frame):
        if self.signal is None:
            self.signal, self.when = signum, time.monotonic()
        for process in list(self.children):
            self.send(process, signal.SIGTERM)

    @staticmethod
    def send(process, signum):
        try:
            os.killpg(process.pid, signum)
        except ProcessLookupError:
            pass

    def launch(self, argv, **kwargs):
        if self.signal is not None:
            return None
        process = subprocess.Popen(argv, start_new_session=True, **kwargs)
        self.children.add(process)
        # A signal can arrive between creation and registration.
        if self.signal is not None:
            self.send(process, signal.SIGTERM)
        return process

    def poll(self, process):
        status = process.poll()
        if status is None and self.signal is not None and time.monotonic() - self.when >= self.grace:
            self.send(process, signal.SIGKILL)
            status = process.poll()
        return status

    def finish(self, process):
        # Reap the leader and stop any descendants that outlived it. This also
        # covers an unexpected caller error before the normal wait completed.
        self.send(process, signal.SIGTERM)
        deadline = time.monotonic() + self.grace
        while time.monotonic() < deadline:
            process.poll()
            try:
                os.killpg(process.pid, 0)
            except ProcessLookupError:
                break
            time.sleep(0.01)
        self.send(process, signal.SIGKILL)
        process.wait()
        self.children.discard(process)

    def __exit__(self, *exception):
        try:
            for process in list(self.children):
                self.finish(process)
        finally:
            for sig, handler in self.previous.items():
                signal.signal(sig, handler)


def command(logs, argv, *, cwd=None, fresh=False, cancellation=None, record=None):
    """Capture bytes and exact child status, including interrupted commands."""
    if cancellation is None:
        # Nested command wrappers finish their child groups before the outer
        # suite's longer TERM grace expires.
        with Cancellation(grace=0.5) as owned:
            return command(logs, argv, cwd=cwd, fresh=fresh,
                           cancellation=owned, record=record)
    logs = logs.resolve()
    logs.mkdir(parents=True, exist_ok=True)
    descriptor, filename = tempfile.mkstemp(prefix='command-', suffix='.log', dir=logs)
    os.close(descriptor)
    raw = Path(filename)
    token = raw.stem
    started = time.monotonic()
    status = None
    error = None
    sources = None
    process = None
    subject = Path(cwd or Path.cwd()).resolve()
    before = subject_identity(subject, logs)
    try:
        with raw.open('wb') as output:
            try:
                if fresh and cancellation.signal is None:
                    targets = argv[3:] if argv[:3] == ['lake', '--old', 'build'] else []
                    modules = [target[1:] for target in targets] if targets and all(target.startswith('+') for target in targets) else []
                    clear_mutable_outputs(subject, modules)
                env = dict(os.environ)
                if Path(argv[0]).name == 'lake':
                    env.pop('CI', None)
                process = cancellation.launch(argv, cwd=cwd, env=env, stdout=output,
                                              stderr=subprocess.STDOUT)
                if process is not None:
                    while cancellation.poll(process) is None:
                        time.sleep(0.01)
                    status = process.returncode
            except (OSError, ValueError) as caught:
                error = str(caught)
                output.write((error + '\n').encode())
            finally:
                if process is not None:
                    cancellation.finish(process)
                    status = process.returncode
        if status and (subject / 'lake-manifest.json').is_file():
            inputs = [path for path in subject.rglob('*.lean')
                      if '.lake' not in path.relative_to(subject).parts
                      and not path.is_relative_to(logs)]
            sources = logs / (token + '.sources')
            sources.mkdir()
            for path in inputs:
                destination = sources / path.relative_to(subject)
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(path, destination)
            if (subject / 'bindings.json').is_file():
                shutil.copyfile(subject / 'bindings.json', sources / 'bindings.json')
    finally:
        row = {
            'argv': argv, 'cwd': str(subject), 'returncode': status,
            'state': 'completed' if process is not None else
                     'launch-failed' if error else 'cancelled',
            'error': error, 'cancelled_by': cancellation.signal,
            'elapsed_seconds': time.monotonic() - started, 'log': str(raw),
            'sources': str(sources) if sources else None,
            'input_sha256_before': before,
            'input_sha256_after': subject_identity(subject, logs),
        }
        (logs / (token + '.json')).write_text(json.dumps(row, indent=2) + '\n')
        if record is not None:
            record.update(row)
    with raw.open('rb') as output:
        shutil.copyfileobj(output, sys.stdout.buffer)
    if cancellation.signal is not None:
        return 128 + cancellation.signal
    return 127 if error else shell_status(status)

def clone_project(source, destination, mutable_source):
    """Copy mutable sources/caches; only installed archive packages are shared."""
    destination.mkdir(parents=True)
    project = destination / 'project'
    # Project files and caches must be ordinary private copies, never hardlinks.
    # Do not follow a project symlink into somebody else's mutable build tree.
    for tree in (source, mutable_source):
        for path in tree.rglob('*'):
            if path.is_symlink():
                raise ValueError(f'Unexpected symlink in mutable control input: {path}')
    shutil.copytree(source, project)
    private = destination / 'rust-model'
    shutil.copytree(mutable_source, private,
                    ignore=shutil.ignore_patterns('.git', 'target'))
    manifest_path = project / 'lake-manifest.json'
    manifest = json.loads(manifest_path.read_text())
    lakefile = project / 'lakefile.lean'
    text = lakefile.read_text()
    for package in manifest['packages']:
        if package['name'] in MUTABLE:
            old = package['dir']
            new = private if package['name'] == 'rust_model' else private / 'aeneas'
            text = text.replace(json.dumps(old), json.dumps(str(new)))
            package['dir'] = str(new)
    manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
    lakefile.write_text(text)
    # Package relocation changes Lake configuration, independently of proof bytes.
    for package in (project, private, private / 'aeneas'):
        config = package / '.lake/config'
        if config.exists():
            shutil.rmtree(config)
        for path in (package / '.lake').glob('lakefile.*'):
            if path.is_file():
                path.unlink()
    return project


def preflight(root, source):
    import workspace
    if source.is_symlink() or not source.is_dir():
        raise ValueError(f'Expected an ordinary generated CI project: {source}')
    for fixture in FIXTURES:
        path = source / fixture
        if path.exists() or path.is_symlink():
            raise ValueError(f'Negative control fixture already exists: {path}')
    manifest = json.loads((source / 'bindings.json').read_text())
    if manifest.get('mode') != 'verified-live':
        raise ValueError('Failure controls require verified-live CI bindings')
    import copy_back
    state_path = source / copy_back.STATE
    # CI assembly has no editor projection record. If one is present, preserve
    # its edit fence rather than admitting an edited development projection.
    if state_path.exists():
        state = json.loads(state_path.read_text())
        if (not isinstance(state, dict) or state.get('version') not in (1, 2)
                or not isinstance(state.get('sha256'), dict)
                or set(state['sha256']) != set(copy_back.MODULES)):
            raise ValueError(f'Invalid generated projection baseline: {source}')
        if state['version'] == 2:
            copy_back.validate(state)
        # Native trait laws are valid CI output. Copy-back's separate trait-law
        # prohibition is an editing boundary, not a CI baseline predicate.
        for module in copy_back.MODULES:
            path = source / (module + '.lean')
            if hashlib.sha256(path.read_bytes()).hexdigest() != state['sha256'][module]:
                raise ValueError(f'Edited generated projection: {path}; run fresh extraction')
    workspace.check_source_copies(root, source)


def task_row(name):
    return {'family': name, 'state': 'not-started', 'returncode': None,
            'elapsed_seconds': None, 'log': None}


def save_task(run, row):
    logs = run / row['family']
    logs.mkdir(parents=True, exist_ok=True)
    (logs / 'status.json').write_text(json.dumps(row, indent=2) + '\n')


def mark_unstarted(records, run, state, reason, cancelled_by=None):
    for row in records.values():
        if row['state'] == 'not-started':
            row.update(state=state, reason=reason, cancelled_by=cancelled_by)
            save_task(run, row)


def run_families(tasks, jobs, run, *, cancellation=None, records=None):
    """Bound active sandboxes and retain the complete task roster on every exit."""
    if cancellation is None:
        with Cancellation() as owned:
            return run_families(tasks, jobs, run, cancellation=owned, records=records)
    tasks = list(tasks)
    names = [task[0] for task in tasks]
    if len(set(names)) != len(names):
        raise ValueError('Control task names must be unique')
    if records is None:
        records = {name: task_row(name) for name in names}
    for name in names:
        save_task(run, records[name])
    active = {}
    next_task = 0
    try:
        while active or next_task < len(tasks):
            while cancellation.signal is None and next_task < len(tasks) and len(active) < jobs:
                name, prepare, argv, env = tasks[next_task]
                next_task += 1
                logs = run / name
                started = time.monotonic()
                output = (logs / 'family.log').open('wb')
                sandbox = None
                try:
                    sandbox = prepare()
                    process = cancellation.launch(argv, cwd=sandbox, env=env(sandbox, logs),
                                                  stdout=output, stderr=subprocess.STDOUT)
                    if process is None:
                        output.write(b'Cancelled before family launch\n')
                        output.close()
                        records[name].update(state='cancelled', cancelled_by=cancellation.signal,
                                             log=str(logs / 'family.log'))
                        save_task(run, records[name])
                        shutil.rmtree(sandbox.parent)
                        continue
                except (OSError, ValueError) as error:
                    output.write((str(error) + '\n').encode())
                    output.close()
                    records[name].update(state='launch-failed', error=str(error),
                        elapsed_seconds=time.monotonic() - started, log=str(logs / 'family.log'))
                    save_task(run, records[name])
                    if sandbox is not None:
                        shutil.rmtree(sandbox.parent)
                    continue
                active[process] = (name, sandbox, output, started)
            if cancellation.signal is not None:
                mark_unstarted({name: records[name] for name in names}, run, 'cancelled',
                               'suite interrupted before launch', cancellation.signal)
                next_task = len(tasks)
            for process, (name, sandbox, output, started) in list(active.items()):
                status = cancellation.poll(process)
                if status is None:
                    continue
                cancellation.finish(process)
                output.close()
                records[name].update(state='completed', returncode=process.returncode,
                    cancelled_by=cancellation.signal, elapsed_seconds=time.monotonic() - started,
                    log=str(run / name / 'family.log'))
                save_task(run, records[name])
                print(f'{name}: status={shell_status(status)} elapsed={records[name]["elapsed_seconds"]:.2f}s', flush=True)
                del active[process]
                shutil.rmtree(sandbox.parent)
            if active:
                time.sleep(0.05)
    finally:
        # Stop all owned writers before the caller retires its private trees.
        for process, (name, sandbox, output, started) in list(active.items()):
            cancellation.finish(process)
            output.close()
            records[name].update(state='completed', returncode=process.returncode,
                cancelled_by=cancellation.signal, elapsed_seconds=time.monotonic() - started,
                log=str(run / name / 'family.log'))
            save_task(run, records[name])
        mark_unstarted({name: records[name] for name in names}, run,
                       'cancelled' if cancellation.signal else 'blocked',
                       'suite interrupted' if cancellation.signal else 'supervisor did not launch task',
                       cancellation.signal)
    results = [records[name] for name in names]
    status = 128 + cancellation.signal if cancellation.signal is not None else int(any(
        row['state'] != 'completed' or row['returncode'] != 0 for row in results))
    return results, status


def suite(args, *, root=None):
    root = Path(root) if root is not None else Path(__file__).resolve().parents[2]
    models = (args.model,) if args.model else MODELS
    baseline_models = tuple(dict.fromkeys((*models, 'verification')))
    os.environ.setdefault('LEAN_NUM_THREADS', '2')
    started = time.monotonic()
    roster = {'extraction': task_row('extraction')}
    roster.update((model + '/' + family, task_row(model + '/' + family))
                  for model in models for family in FAMILIES)
    baseline_rows = {model: task_row(model + '/baseline') for model in baseline_models}
    status = 1
    error = None
    with Cancellation() as cancellation:
        logs = root / 'target/aeneas/control-logs'
        logs.mkdir(parents=True, exist_ok=True)
        run = Path(tempfile.mkdtemp(prefix='run-', dir=logs))
        print(f'Negative control evidence: {run}', flush=True)
        def summary():
            (run / 'summary.json').write_text(json.dumps({'returncode': status,
                'cancelled_by': cancellation.signal, 'error': error,
                'elapsed_seconds': time.monotonic() - started,
                'baselines': list(baseline_rows.values()),
                'families': list(roster.values())}, indent=2) + '\n')
        summary()
        try:
            # Even golden-only invocation retains the original live extraction controls.
            for model in baseline_models:
                if cancellation.signal is not None:
                    return 128 + cancellation.signal
                preflight(root, root / 'target/aeneas' / model)
            with tempfile.TemporaryDirectory(prefix='control-sandboxes-', dir=root / 'target/aeneas') as scratch:
                scratch = Path(scratch)
                baselines = {}
                # Strict independent positive baselines precede mutant consumers.
                for model in baseline_models:
                    if cancellation.signal is not None:
                        return 128 + cancellation.signal
                    source = root / 'target/aeneas' / model
                    project = clone_project(source, scratch / model, root / 'anneal/lean')
                    preflight(root, project)
                    status = command(run / model / 'baseline', [sys.executable, '-B',
                        str(root / 'verification/aeneas/workspace.py'), 'verify',
                        str(project), '--root', str(root)], cwd=project,
                        cancellation=cancellation, record=baseline_rows[model])
                    save_task(run, baseline_rows[model])
                    summary()
                    if status:
                        return status
                    baselines[model] = project
                producers = scratch / 'producer-fixtures'
                producers.mkdir()
                extraction = [('extraction', lambda: clone_project(baselines['verification'],
                    scratch / 'extraction', baselines['verification'].parent / 'rust-model'),
                    ['bash', str(root / 'verification/aeneas/negative-control-extraction.sh')],
                    lambda p, l: {**os.environ, 'AENEAS_CONTROL_REPO': str(root),
                        'AENEAS_CONTROL_PROJECT': str(p), 'AENEAS_CONTROL_LOG_DIR': str(l),
                        'AENEAS_CONTROL_PRODUCER_DIR': str(producers)})]
                # Generation is shared; model-specific kernel replay follows only
                # after all extraction producer gates have completed successfully.
                _, status = run_families(extraction, 1, run, cancellation=cancellation, records=roster)
                # Preserve generated source fixtures and compiler evidence, while
                # retiring the producer's reproducible Rust build directory.
                retained = run / 'extraction/producer-fixtures'
                retained.mkdir()
                for name in ('Controls', 'controls.before.ullbc', 'controls.llbc'):
                    source = producers / name
                    if source.is_dir():
                        shutil.copytree(source, retained / name)
                    elif source.is_file():
                        shutil.copyfile(source, retained / name)
                producers = retained
                roster['extraction']['fixtures'] = str(retained)
                save_task(run, roster['extraction'])
                summary()
                if status:
                    return status
                tasks = []
                for model in models:
                    for family in FAMILIES:
                        name = model + '/' + family
                        def prepare(model=model, family=family):
                            return clone_project(baselines[model], scratch / (model + '-' + family),
                                                 baselines[model].parent / 'rust-model')
                        def env(p, l, model=model, family=family):
                            return {**os.environ, 'AENEAS_CONTROL_REPO': str(root),
                                'AENEAS_CONTROL_PROJECT': str(p), 'AENEAS_CONTROL_LOG_DIR': str(l),
                                'AENEAS_CONTROL_MODEL': model, 'AENEAS_CONTROL_FAMILY': family,
                                'AENEAS_CONTROL_PRODUCER_DIR': str(producers)}
                        tasks.append((name, prepare,
                            ['bash', str(root / 'verification/aeneas/negative-control-family.sh')], env))
                _, status = run_families(tasks, args.jobs, run, cancellation=cancellation, records=roster)
                return status
        except BaseException as caught:
            status = 1
            error = str(caught)
            raise
        finally:
            if cancellation.signal is not None:
                status = 128 + cancellation.signal
            disposition = 'cancelled' if cancellation.signal else 'blocked'
            reason = 'suite interrupted before launch' if cancellation.signal else 'prerequisite failed before launch'
            mark_unstarted(roster, run, disposition, reason, cancellation.signal)
            mark_unstarted(baseline_rows, run, disposition, reason, cancellation.signal)
            summary()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='action', required=True)
    action = commands.add_parser('suite')
    action.add_argument('model', nargs='?', choices=MODELS)
    action.add_argument('--jobs', type=int, default=os.environ.get('AENEAS_CONTROL_JOBS', '2'))
    action = commands.add_parser('command')
    action.add_argument('logs', type=Path)
    action.add_argument('--fresh', action='store_true')
    action.add_argument('argv', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.action == 'suite':
        if not 1 <= args.jobs <= 4:
            parser.error('--jobs/AENEAS_CONTROL_JOBS must be between 1 and 4')
        return suite(args)
    argv = args.argv[1:] if args.argv[:1] == ['--'] else args.argv
    if not argv:
        parser.error('command requires an executable')
    return command(args.logs, argv, fresh=args.fresh)


if __name__ == '__main__':
    sys.exit(main())
