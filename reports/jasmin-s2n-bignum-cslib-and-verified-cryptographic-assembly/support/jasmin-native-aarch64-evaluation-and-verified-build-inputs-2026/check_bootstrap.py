"""Data-only typed identity guard, not image/build correctness."""
from pathlib import Path
import hashlib,json,copy
MANIFEST='71f0139a696ef851a52bebc0b8facfd20e728e0b92f7b0251480979614e24558'
CONFIG='42e5940896b215eb0fb4a0ec3705e7e09b195428636af98294d1b50120d46a87'
def guard(manifest_bytes,config_bytes,runtime,expected_manifest=MANIFEST,expected_config=CONFIG,arch='arm64'):
 m=json.loads(manifest_bytes);c=json.loads(config_bytes)
 return (hashlib.sha256(manifest_bytes).hexdigest()==expected_manifest
  and hashlib.sha256(config_bytes).hexdigest()==expected_config
  and m['config']['digest']=='sha256:'+expected_config
  and runtime['Id']=='sha256:'+expected_manifest
  and runtime['Architecture']==c['architecture']==arch
  and runtime['Os']==c['os']=='linux'
  and runtime['RootFS']['Layers']==c['rootfs']['diff_ids'])
if __name__=='__main__':
 p=Path(__file__).resolve().parent/'support/bootstrap'
 m=(p/'verified-platform-manifest.json').read_bytes();c=(p/'verified-config.json').read_bytes();r=json.loads((p/'image-inspect.json').read_text())
 results={'valid':guard(m,c,r),'wrong_manifest_rejected':not guard(m,c,r,expected_manifest='0'*64),'wrong_config_rejected':not guard(m,c,r,expected_config='0'*64),'wrong_architecture_rejected':not guard(m,c,r,arch='amd64')}
 if not all(results.values()):raise SystemExit('identity guard regression failed')
 print(json.dumps(results,indent=2))
