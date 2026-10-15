"""PREPARATION ONLY. Prepare a new copied-log fixture; never run a proof.

Inputs: frozen positive package root, NEW owned fixture directory. Neither the
frozen original stream nor its receipt is changed. Tests marker logic after
explicitly binding the copied truncated stream's own SHA and asserted exit0.
"""
import hashlib,json,sys
from pathlib import Path
package=Path(sys.argv[1]).resolve();dest=Path(sys.argv[2]).resolve()
if dest.exists() or dest==package or package in dest.parents:
    raise SystemExit('fixture destination must be new/outside frozen package')
dest.mkdir();(dest/'logs').mkdir()
source=package/'support';raw=(source/'logs/positive.stdout').read_bytes()
tail=b'ANNEAL_AUDIT_FINISHED\n'
if not raw.endswith(tail):raise SystemExit('frozen log tail differs')
truncated=raw[:-len(tail)]
(dest/'logs/positive.stdout').write_bytes(truncated)
receipt=json.loads((source/'logs/positive.json').read_text())
receipt['stdout_sha256']=hashlib.sha256(truncated).hexdigest()
receipt['stdout_bytes']=len(truncated);receipt['returncode']=0
(dest/'logs/positive.json').write_text(json.dumps(receipt,indent=2)+'\n')
(dest/'logs/selected-census.stdout').write_bytes((source/'logs/selected-census.stdout').read_bytes())
(dest/'verify_positive.py').write_bytes((source/'observer/verify_positive.py').read_bytes())
(dest/'fixture-receipt.json').write_text(json.dumps({'original_sha256':hashlib.sha256(raw).hexdigest(),'truncated_sha256':hashlib.sha256(truncated).hexdigest(),'removed_tail':tail.decode(),'claimed_exit0':True,'original_stream_not_modified':(source/'logs/positive.stdout').read_bytes()==raw},indent=2)+'\n')
print('ANNEAL_TRUNCATED_LOG_FIXTURE_PREPARED; checker not invoked')
