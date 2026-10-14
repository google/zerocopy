"""Execute safe public APIs from an exact private Git archive, offline."""
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile

HERE = Path(__file__).resolve().parent
REV = 'cce761ad53785973ec2f4a6b13715b770b340c87'
clone = Path(sys.argv[1]).resolve()
archive = subprocess.run(['git', '-C', str(clone), 'archive', REV, 'zerocopy'],
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60)
if archive.returncode:
    raise SystemExit('Exact source archive unavailable; no fallback to a moving checkout')
records = []
with tempfile.TemporaryDirectory(prefix='zerocopy-byte-controls-') as directory:
    root = Path(directory)
    source = root / 'source'
    source.mkdir()
    with tarfile.open(fileobj=io.BytesIO(archive.stdout)) as contents:
        contents.extractall(source, filter='data')
    probe = root / 'probe'
    (probe / 'src').mkdir(parents=True)
    (probe / 'Cargo.toml').write_text('''[package]
name = "anneal-byte-controls"
version = "0.0.0"
edition = "2024"
[workspace]
[dependencies]
zerocopy = { path = "../source/zerocopy" }
''')
    (probe / 'src/main.rs').write_bytes((HERE / 'main.rs').read_bytes())
    env = dict(os.environ)
    env['CARGO_TARGET_DIR'] = str(root / 'target')
    env['CARGO_TERM_COLOR'] = 'never'
    for name, argv in [('rust-version', ['rustc', '-vV']),
                       ('cargo-run', ['cargo', 'run', '--offline', '--quiet'])]:
        result = subprocess.run(argv, cwd=probe, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60)
        # Cargo diagnostics may name the private extraction directory. Retain
        # their text while making the transient path portable.
        for stream, output in [('stdout', result.stdout), ('stderr', result.stderr)]:
            (HERE / (name + '.' + stream + '.txt')).write_bytes(output.replace(str(root).encode(), b'<private-extraction>'))
        records.append({'name': name, 'argv': argv, 'returncode': result.returncode})
        if result.returncode:
            break
    lock = probe / 'Cargo.lock'
    if lock.exists():
        (HERE / 'Cargo.lock').write_bytes(lock.read_bytes())
result = {'revision': REV, 'source_archive_sha256': hashlib.sha256(archive.stdout).hexdigest(),
          'input_sha256': hashlib.sha256((HERE / 'main.rs').read_bytes()).hexdigest(),
          'commands': records, 'source_selection': 'git archive REV zerocopy',
          'network': 'Cargo offline', 'unsafe_operations_in_owned_probe': False}
(HERE / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
if len(records) != 2 or any(row['returncode'] for row in records):
    raise SystemExit('Execution incomplete; inspect streams, not a program-domain negative result')
