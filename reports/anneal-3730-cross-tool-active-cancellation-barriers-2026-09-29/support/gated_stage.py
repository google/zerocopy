#!/usr/bin/env python3
"""Synthetic stage-completion gate around the real one-shot Aeneas CLI."""
import json, subprocess, sys, time
from pathlib import Path
binary,llbc,dest,entered,release,authority,decision,generation=map(Path,sys.argv[1:])
cmd=[str(binary),'-backend','lean','-no-progress-bar','-sequential','-split-files','-gen-lib-entry',
     '-dest',str(dest),str(llbc)]
p=subprocess.run(cmd,capture_output=True,text=True,timeout=90)
if p.returncode: raise SystemExit(f'Aeneas rc={p.returncode}: {p.stderr}')
entered.write_text(json.dumps({'aeneas_rc':p.returncode,'argv':cmd,
                               'stdout':p.stdout,'stderr':p.stderr},indent=2))
for _ in range(3000):
    if release.exists():break
    time.sleep(.01)
else:raise SystemExit('release timeout')
owner=json.loads(authority.read_text())
decision.write_text(json.dumps({'job_generation':int(str(generation)),'authority_generation':owner['generation'],
                               'publish':owner['generation']==int(str(generation)),
                               'aeneas_rc':p.returncode},indent=2))
