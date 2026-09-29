#!/usr/bin/env python3
"""Pinned Lean caller taint through deliberately reused compiled imports."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

HERE=Path(__file__).resolve().parent
LEAN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
PROOF='import Dep\ntheorem caller : depValue = 7 := base\ntheorem independent : True := trivial\n#print axioms caller\n#print axioms independent\n'
SOURCES={
 'axiom':'def depValue : Nat := 7\naxiom model : depValue = 7\ntheorem base : depValue = 7 := model\n',
 'concrete':'def depValue : Nat := 7\ntheorem base : depValue = 7 := by decide\n',
 'admitted':'def depValue : Nat := 7\ntheorem base : depValue = 7 := by sorry\n',
}
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def run(argv,root,env):
    p=subprocess.run([str(x) for x in argv],cwd=root,env=env,text=True,capture_output=True,timeout=15)
    return dict(argv=[str(x) for x in argv],exit=p.returncode,stdout=p.stdout,stderr=p.stderr)
def main():
    assert LEAN.exists()
    records=[]
    with tempfile.TemporaryDirectory(prefix='anneal-taint-') as tmp:
        root=Path(tmp);env=dict(os.environ,LEAN_PATH=str(root),LEAN_NUM_THREADS='1')
        (root/'Proof.lean').write_text(PROOF)
        for label in ('axiom','concrete','admitted'):
            (root/'Dep.lean').write_text(SOURCES[label])
            build=run([LEAN,'-o','Dep.olean','Dep.lean'],root,env)
            assert build['exit']==0,build
            check=run([LEAN,'Proof.lean'],root,env)
            assert check['exit']==0,check
            records.append(dict(label=label,source_sha256=sha(root/'Dep.lean'),
                                artifact_sha256=sha(root/'Dep.olean'),build=build,check=check))
            if label=='axiom':
                (root/'Dep.lean').write_text(SOURCES['concrete'])
                stale=run([LEAN,'Proof.lean'],root,env)
                assert stale['exit']==0
                records.append(dict(label='concrete-source-stale-axiom-olean',
                                    source_sha256=sha(root/'Dep.lean'),
                                    artifact_sha256=sha(root/'Dep.olean'),check=stale))
        assert records[0]['artifact_sha256']==records[1]['artifact_sha256']
        assert records[1]['source_sha256']==records[2]['source_sha256']
        assert records[1]['artifact_sha256']!=records[2]['artifact_sha256']
    result=dict(lean_sha256=sha(LEAN),lean_version=run([LEAN,'--version'],HERE,dict(os.environ))['stdout'].strip(),
                proof_sha256=hashlib.sha256(PROOF.encode()).hexdigest(),records=records)
    (HERE/'results.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps([{r['label']:r['check']['stdout'].strip()} for r in records],indent=2))
if __name__=='__main__':main()
