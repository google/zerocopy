import hashlib, json, os, subprocess, sys
from pathlib import Path

root = Path('/home/opam/anneal-cross-sources')
out = Path('/home/opam/anneal-cross-output')
if out.exists():
    raise SystemExit('STOP: output root must be fresh')
out.mkdir()
mirror = out / 'signature-mirror'
mirror.mkdir()
# The host appends the exact frozen list of 690 source identities as CENSUS.
copied = []
for item in CENSUS:
    src = root / item['path']
    b = src.read_bytes()
    if hashlib.sha256(b).hexdigest() != item['sha256']:
        raise SystemExit('STOP: signature input hash mismatch: ' + item['path'])
    rel = Path(item['path']).relative_to('s2n-bignum')
    dest = mirror / rel
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(b)
    copied.append({'path':str(rel), 'bytes':len(b), 'sha256':hashlib.sha256(b).hexdigest()})
src = root / 's2n-bignum/tools/collect-signatures.py'
script = src.read_bytes()
(mirror / 'tools').mkdir()
(mirror / 'tools/collect-signatures.py').write_bytes(script)
for arch in ('arm','x86'):
    (mirror / arch / 'proofs').mkdir()
proc = subprocess.run([sys.executable, '-B', 'tools/collect-signatures.py'],
    cwd=mirror, capture_output=True, timeout=280)
(out / 'signature.stdout').write_bytes(proc.stdout)
(out / 'signature.stderr').write_bytes(proc.stderr)
result = {'argv':[sys.executable,'-B','tools/collect-signatures.py'],
          'cwd':str(mirror), 'returncode':proc.returncode,
          'generator_sha256':hashlib.sha256(script).hexdigest(),
          'copied_inputs':copied, 'outputs':[]}
for arch in ('arm','x86'):
    rel=arch+'/proofs/subroutine_signatures.ml'
    p=mirror/rel
    if not p.is_file():
        result['outputs'].append({'path':rel,'exists':False})
        continue
    b=p.read_bytes(); original=(root/'s2n-bignum'/rel).read_bytes()
    result['outputs'].append({'path':rel,'exists':True,'bytes':len(b),
      'sha256':hashlib.sha256(b).hexdigest(),
      'original_sha256':hashlib.sha256(original).hexdigest(),
      'byte_equal_to_original':b==original})
(out/'signature-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='copied_inputs'},indent=2))
if proc.returncode or not all(x.get('byte_equal_to_original') for x in result['outputs']):
    raise SystemExit('STOP: signature status or output discrepancy; preserved')
