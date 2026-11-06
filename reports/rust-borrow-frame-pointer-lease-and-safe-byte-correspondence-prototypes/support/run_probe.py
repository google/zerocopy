"""Read exact Git source objects; compile only in private temporary scratch."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

REV = 'cce761ad53785973ec2f4a6b13715b770b340c87'
HERE = Path(__file__).resolve().parent
clone = Path(sys.argv[1]).resolve()
if len(sys.argv) > 2:
    lean_binary = Path(sys.argv[2]).resolve()
    LEAN = [str(lean_binary)]
    lean_record = ['selected-lean-binary']
else:
    LEAN = ['elan', 'run', 'leanprover/lean4:v4.34.1', 'lean']
    lean_record = LEAN
OUT = HERE / ('lean431' if len(sys.argv) > 2 else 'lean434')
OUT.mkdir(exist_ok=True)
observations = []
source_hashes = {}

def run(name, argv, cwd, env=None):
    result = subprocess.run(argv, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60)
    (OUT / (name + '.stdout.txt')).write_bytes(result.stdout)
    (OUT / (name + '.stderr.txt')).write_bytes(result.stderr)
    recorded_argv = lean_record + argv[len(LEAN):] if argv[:len(LEAN)] == LEAN else argv
    observations.append({'name': name, 'argv': recorded_argv, 'returncode': result.returncode,
                         'stdout': name + '.stdout.txt', 'stderr': name + '.stderr.txt'})
    if result.returncode:
        save()
        raise SystemExit(f'Operation failed: {name}; retained streams are not domain-negative evidence')

def save():
    data = {'revision': REV, 'source_sha256': source_hashes, 'commands': observations}
    (OUT / 'results.json').write_text(json.dumps(data, indent=2) + '\n')

with tempfile.TemporaryDirectory(prefix='model-boundary-') as directory:
    temporary = Path(directory)
    source = temporary / 'input'
    build = temporary / 'build'
    source.mkdir()
    build.mkdir()
    modules = ['Rust/Layout', 'Rust/Memory', 'Rust/Bytes', 'Rust/Storage', 'Rust/Arithmetic',
               'Rust', 'RustTests', 'RustBytesTests', 'RustStorageTests']
    for module in modules:
        repository_path = 'anneal/lean/' + module + '.lean'
        read = subprocess.run(['git', '-C', str(clone), 'show', REV + ':' + repository_path],
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
        if read.returncode:
            raise SystemExit(f'Immutable Git object unavailable: {repository_path}; no source fallback')
        source_hashes[repository_path] = hashlib.sha256(read.stdout).hexdigest()
        destination = source / (module + '.lean')
        destination.parent.mkdir(exist_ok=True, parents=True)
        destination.write_bytes(read.stdout)
    (source / 'BoundaryProbe.lean').write_bytes((HERE / 'BoundaryProbe.lean').read_bytes())
    (source / 'layout_probe.rs').write_bytes((HERE / 'layout_probe.rs').read_bytes())
    env = dict(os.environ)
    env['LEAN_PATH'] = '../build'
    run('lean-version', LEAN + ['--version'], source, env)
    run('rust-version', ['rustc', '-vV'], source)
    for module in modules:
        destination = build / (module + '.olean')
        destination.parent.mkdir(exist_ok=True, parents=True)
        run(module.replace('/', '-'), LEAN + ['-j2', '-DwarningAsError=true', '-o', '../build/' + module + '.olean', module + '.lean'], source, env)
    run('owned-boundary', LEAN + ['-j2', '-DwarningAsError=true', 'BoundaryProbe.lean'], source, env)
    run('rust-build', ['rustc', '--edition=2024', '-C', 'opt-level=0', 'layout_probe.rs', '-o', '../build/layout-probe'], source)
    run('rust-layout', ['../build/layout-probe'], source)
save()
print(json.dumps({'commands': len(observations), 'all_success': True, 'upstream_modules': len(modules)}))
