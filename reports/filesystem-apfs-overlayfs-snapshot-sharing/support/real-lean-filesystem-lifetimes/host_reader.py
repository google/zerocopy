#!/usr/bin/env python3
"""Hold both an open fd and read-only mmap over a real Lean artifact."""
import hashlib
import json
import mmap
from pathlib import Path
import sys
import time

path, root = Path(sys.argv[1]), Path(sys.argv[2])
def wait(p):
    until=time.monotonic()+12
    while not p.exists():
        if time.monotonic()>until: raise TimeoutError(str(p))
        time.sleep(.01)
with path.open('rb') as f:
    mapping=mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ)
    (root/'host-ready').write_text('ready')
    for phase in (1,2):
        wait(root/f'host-go{phase}')
        f.seek(0)
        data=f.read()
        result={'phase':phase,'fd_sha256':hashlib.sha256(data).hexdigest(),
                'map_sha256':hashlib.sha256(mapping[:]).hexdigest(),
                'path_exists':path.exists(),
                'path_sha256':hashlib.sha256(path.read_bytes()).hexdigest() if path.exists() else None}
        (root/f'host-phase{phase}.json').write_text(json.dumps(result,sort_keys=True)+'\n')
        (root/f'host-ack{phase}').write_text('ack')
    mapping.close()
