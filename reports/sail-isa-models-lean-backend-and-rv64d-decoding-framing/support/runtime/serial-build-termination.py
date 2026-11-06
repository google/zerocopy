# Fixed build adapter for the pinned official Sail/Lean sources. No semantic translation.
from pathlib import Path
from graphlib import TopologicalSorter
import hashlib, json, re, subprocess, time, resource, os, sys

OUT = Path('/home/opam/anneal-sail-output')
LEAN = Path('/home/opam/anneal-sail-tools/lean-4.29.0-linux_aarch64/bin/lean')
CORE = LEAN.parent.parent / 'lib/lean'
ROOTS = [OUT / 'termination-generated/Lean_RV64D', Path('/home/opam/anneal-sail-sources/lean-sail')]
EXPECTED = 'e215cbe9eab0914b49761e9e486d388e2e701cf876d1079d1ba733c48edb2d7b'

def fail(message):
    raise SystemExit('STOP: ' + message)

if hashlib.sha256(LEAN.read_bytes()).hexdigest() != EXPECTED:
    fail('compiler identity differs')
modules = {}
for root in ROOTS:
    for path in sorted(root.rglob('*.lean')):
        if '.lake' in path.parts:
            fail('unexpected prior build directory')
        name = '.'.join(path.relative_to(root).with_suffix('').parts)
        if name in modules:
            fail('duplicate module ' + name)
        data = path.read_bytes()
        imports = []
        for line in data.decode().splitlines():
            # Actual inspected inputs contain only simple, single-line imports.
            if re.match(r'^\s*(?:public |meta )?import\b', line):
                if not re.fullmatch(r'import [A-Za-z0-9_.]+', line):
                    fail('unsupported import syntax in ' + name)
                imports.append(line[7:])
        modules[name] = {'source': str(path), 'root': str(root),
                         'sha256': hashlib.sha256(data).hexdigest(), 'imports': imports}
needed = {}
def visit(name):
    if name in needed:
        return
    if name not in modules:
        if name.split('.')[0] not in ('Init', 'Lean', 'Std'):
            fail('unresolved non-toolchain import ' + name)
        if not (CORE / (name.replace('.', '/') + '.olean')).is_file():
            fail('unresolved toolchain import ' + name)
        return
    needed[name] = modules[name]
    for dep in modules[name]['imports']:
        visit(dep)
for target in ('LeanRV64D', 'Sail.ArchSemSequential'):
    visit(target)
graph = {name: [dep for dep in row['imports'] if dep in needed] for name, row in needed.items()}
order = list(TopologicalSorter(graph).static_order())
plan = {'compiler': str(LEAN), 'compiler_sha256': EXPECTED, 'targets': ['LeanRV64D', 'Sail.ArchSemSequential'],
        'order': order, 'modules': needed, 'implicit_core': 'official Lean installation',
        'adapter_scope': 'dependency ordering only; actual Lean checks every import and definition'}
if len(sys.argv) == 1 or sys.argv[1] != 'execute':
    print(json.dumps(plan, indent=2))
    sys.exit(0)
BUILD = OUT / 'serial-build-termination'
BUILD.mkdir()  # Create-only: never overwrite/reuse a partial build.
(BUILD / 'plan.json').write_text(json.dumps(plan, indent=2) + '\n')
ARTS = BUILD / 'olean'
ARTS.mkdir()
env = os.environ.copy()
env['LEAN_PATH'] = str(ARTS)
env['LEAN_NUM_THREADS'] = '1'
start = time.monotonic()
records = []
for index, name in enumerate(order):
    row = needed[name]
    if hashlib.sha256(Path(row['source']).read_bytes()).hexdigest() != row['sha256']:
        fail('source changed before compilation ' + name)
    if time.monotonic() - start >= 1800:
        fail('overall 30-minute build budget reached between modules')
    dest = ARTS / (name.replace('.', '/') + '.olean')
    dest.parent.mkdir(parents=True, exist_ok=True)
    argv = ['timeout', '--foreground', '--signal=TERM', '--kill-after=10', '300', str(LEAN), '-j1', '-M4500',
            '--tstack=400000', '-R', row['root'], '-o', str(dest), row['source']]
    tick = time.monotonic()
    with (BUILD / (str(index) + '.stdout')).open('xb') as so, (BUILD / (str(index) + '.stderr')).open('xb') as se:
        result = subprocess.run(argv, cwd=row['root'], env=env, stdout=so, stderr=se)
    rec = {'index': index, 'module': name, 'argv': argv, 'status': result.returncode,
           'seconds': time.monotonic()-tick}
    if dest.exists():
        rec['olean_bytes'] = dest.stat().st_size
        rec['olean_sha256'] = hashlib.sha256(dest.read_bytes()).hexdigest()
    records.append(rec)
    (BUILD / 'results.json').write_text(json.dumps(records, indent=2) + '\n')
    print(json.dumps(rec), flush=True)
    if result.returncode != 0:
        fail('nonzero compiler/timeout status; classify exact streams before dependent work')
    if not dest.is_file():
        fail('zero compiler status without required olean: ' + name)
usage = resource.getrusage(resource.RUSAGE_CHILDREN)
(BUILD / 'complete.json').write_text(json.dumps({'status': 0, 'modules': len(records),
    'seconds': time.monotonic()-start, 'child_maxrss_kib': usage.ru_maxrss,
    'child_user_seconds': usage.ru_utime, 'child_system_seconds': usage.ru_stime}, indent=2) + '\n')
