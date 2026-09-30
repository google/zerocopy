#!/usr/bin/env python3
"""Forced-restart v1 mapping after the retained v2 worker hit the RSS guard."""
import json
from pathlib import Path
import re
import shutil
import subprocess
import threading

import probe

S = Path(__file__).resolve().parent
WORK = S / 'run/live'

def main():
    prior = json.loads((S/'guard-abort.json').read_text())
    assert prior['reason'] == 'process-tree RSS cap exceeded'
    assert WORK.is_dir() and not (S/'restart-transcript.json').exists()
    rows = probe.process_rows()
    for old in prior['tree']:
        assert not any(r['pid'] == old['pid'] and 'i125-plugin-mapped-workers' in r['command'] for r in rows)
    raw = subprocess.check_output(['memory_pressure','-Q'], text=True)
    m = re.search(r'System-wide memory free percentage: (\d+)%',raw)
    assert m and int(m.group(1)) >= 30
    assert shutil.disk_usage(S).free > 10 * 1024**3
    assert probe.sha(probe.plugin(WORK)) == probe.sha(S/'artifacts/plugin-v2.dylib')
    probe.GUARD_ABORT_PATH = S/'restart-guard-abort.json'
    probe.LOG.clear()
    probe.PEAK_RSS_KIB = 0
    probe.SAMPLES = 0
    probe.MONITOR_STOP.clear()
    probe.ev('recovery_subject',prior_abort=prior,free_memory_percent=int(m.group(1)),
             v1_sha256=probe.sha(S/'artifacts/plugin-v1.dylib'),
             v2_sha256=probe.sha(S/'artifacts/plugin-v2.dylib'))
    probe.replace(WORK,'v1','forced-restart-v2-to-v1')
    (WORK/'marker.txt').unlink(missing_ok=True)
    watcher=threading.Thread(target=probe.monitor,daemon=True)
    watcher.start()
    fresh=probe.Server('forced_restart',WORK)
    try:
        probe.phase(fresh,'v1-after-forced-restart','P2.lean')
        probe.mapping('forced-restart-v1',fresh)
    finally:
        pids=[r['pid'] for r in probe.process_tree(fresh.p.pid,probe.process_rows())]
        fresh.stop();probe.ACTIVE_SERVER_PID=None
        probe.MONITOR_STOP.set();watcher.join(timeout=2)
    probe.ev('after_shutdown',remaining=[r for r in probe.process_rows() if r['pid'] in pids])
    probe.ev('resources',peak_process_tree_rss_kib=probe.PEAK_RSS_KIB,
             samples=probe.SAMPLES,cap_kib=probe.CAP_KIB)
    (S/'restart-transcript.json').write_text(json.dumps(probe.LOG,indent=2)+'\n')
    assert not probe.GUARD_ABORT_PATH.exists()
    print('PASS: forced-restart v1 mapped under RSS cap')

if __name__=='__main__':main()
