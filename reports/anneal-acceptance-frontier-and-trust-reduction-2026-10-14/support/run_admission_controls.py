"""Run the pinned admission fixture suite from private immutable Git objects."""
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile

REV = 'cce761ad53785973ec2f4a6b13715b770b340c87'
HERE = Path(__file__).resolve().parent
archive = subprocess.run(['git', '-C', str(Path(sys.argv[1]).resolve()), 'archive', REV,
                          'verification/aeneas'], stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, timeout=60)
if archive.returncode:
    raise SystemExit('Immutable admission source archive unavailable')
with tempfile.TemporaryDirectory(prefix='admission-controls-') as directory:
    root = Path(directory)
    with tarfile.open(fileobj=io.BytesIO(archive.stdout)) as contents:
        contents.extractall(root, filter='data')
    argv = [sys.executable, '-B', '-m', 'unittest', 'discover', '-s',
            'verification/aeneas/tests', '-p', 'test_admission.py', '-v']
    result = subprocess.run(argv, cwd=root, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, timeout=30)
    for name, stream in [('stdout', result.stdout), ('stderr', result.stderr)]:
        (HERE / ('admission.' + name + '.txt')).write_bytes(stream.replace(str(root).encode(), b'<private-source>'))
    hashes = {}
    for name in ['admission.py', 'source_inventory.py', 'external.json',
                 'tests/test_admission.py', 'tests/admission/boolean.before.ullbc']:
        path = root / 'verification/aeneas' / name
        hashes[name] = hashlib.sha256(path.read_bytes()).hexdigest()
data = {'revision': REV, 'archive_sha256': hashlib.sha256(archive.stdout).hexdigest(),
        'source_sha256': hashes, 'python_version': sys.version,
        'argv': ['selected-python', *argv[1:]], 'returncode': result.returncode}
(HERE / 'admission-results.json').write_text(json.dumps(data, indent=2) + '\n')
print(json.dumps({'returncode': result.returncode, 'retained': 'admission-results.json'}))
if result.returncode:
    raise SystemExit('Admission suite failed; inspect complete retained streams')
