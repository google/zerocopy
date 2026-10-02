# Copyright 2026 The Fuchsia Authors
# SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT

"""Record exact native capability failures without modifying extracted ASTs."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time


CASES = {
    'known-layout': 'known_layout_probe::layout,known_layout_probe::slice_u32_layout',
    'known-layout-unconstrained': 'known_layout_probe::layout_unconstrained',
    'known-layout-concrete': 'known_layout_probe::slice_u32_layout_direct',
    'owned-transmute': 'owned_transmute_probe::to_bytes,owned_transmute_probe::from_bytes',
    'invalid-transmute': 'owned_transmute_negative::to_bool',
    'std-transmute': 'std_transmute_probe::to_bytes,std_transmute_probe::from_bytes,std_transmute_probe::guarded_bool',
    'raw-pointers': 'raw_pointer_probe::cast,raw_pointer_probe::with_len,raw_pointer_probe::nonnull',
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('case', choices=CASES)
    parser.add_argument('--runtime', type=Path, required=True)
    parser.add_argument('--cargo-home', type=Path, required=True)
    parser.add_argument('--work', type=Path, required=True)
    parser.add_argument('--cargo-target', type=Path, required=True)
    args = parser.parse_args()
    runtime, work = args.runtime.resolve(), args.work.resolve()
    root = Path(__file__).resolve().parents[4]
    sys.path.insert(0, str(root / 'verification/aeneas'))
    import toolchain
    metadata, charon_version = toolchain.validate(root, runtime)
    fixture_case = ('known-layout' if args.case.startswith('known-layout')
                    else args.case)
    fixture = Path(__file__).resolve().parent / fixture_case
    work.mkdir(parents=True, exist_ok=False)
    (work / 'native').mkdir(exist_ok=True)
    environment = toolchain.runtime_env(runtime)
    environment.update({
        'RUSTUP_TOOLCHAIN': metadata['rust-toolchain-version'],
        'CARGO_HOME': str(args.cargo_home.resolve()),
        'CARGO_TARGET_DIR': str(args.cargo_target.resolve()),
        'CARGO_BUILD_JOBS': '2', 'CARGO_NET_OFFLINE': 'true',
        'CHARON_ADMISSION_SNAPSHOT': str(work / 'probe.before.ullbc'),
    })
    commands = [
        ('charon', [str(runtime / 'charon'), 'cargo', '--preset=aeneas',
                    '--sysroot', 'default', '--start-from', CASES[args.case],
                    '--mir', 'promoted', '--no-dedup-serialized-ast',
                    '--dest-file', str(work / 'probe.llbc'), '--abort-on-error',
                    '--error-on-warnings', '--', '--lib', '--locked', '--offline']),
        ('aeneas', [str(runtime / 'aeneas'), '-backend', 'lean', '-namespace',
                    'Probe', '-dest', str(work / 'native'), '-split-files',
                    '-emit-json', '-abort-on-error', '-warnings-as-errors',
                    '-no-progress-bar', '-use-tuple-structs', 'false',
                    str(work / 'probe.llbc')]),
    ]
    sources = sorted((root / 'zerocopy/src').rglob('*.rs')) + [
        root / 'zerocopy/build.rs', root / 'zerocopy/Cargo.toml',
        root / 'zerocopy/Cargo.lock', fixture / 'src/lib.rs',
        fixture / 'Cargo.toml', fixture / 'Cargo.lock', Path(__file__).resolve(),
    ]
    evidence = {'case': args.case, 'fixture': str(fixture),
                'runtime': str(runtime), 'runtime_metadata': metadata,
                'charon_version': charon_version,
                'repository_head': subprocess.check_output(
                    ['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
                'repository_status': subprocess.check_output(
                    ['git', 'status', '--porcelain'], cwd=root, text=True),
                'source_sha256': {str(path.relative_to(root)):
                    hashlib.sha256(path.read_bytes()).hexdigest()
                    for path in sources}, 'steps': []}
    for name, command in commands:
        log_path = work / (name + '.log')
        started = time.monotonic()
        with log_path.open('w') as log:
            result = subprocess.run(command, cwd=fixture, env=environment,
                                    stdout=log, stderr=subprocess.STDOUT)
        evidence['steps'].append({'name': name, 'command': command,
                                  'exit_code': result.returncode,
                                  'seconds': round(time.monotonic() - started, 2),
                                  'log': str(log_path)})
        (work / 'evidence.json').write_text(json.dumps(evidence, indent=2) + '\n')
        print(name, result.returncode, log_path, flush=True)
        if result.returncode:
            return result.returncode
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
