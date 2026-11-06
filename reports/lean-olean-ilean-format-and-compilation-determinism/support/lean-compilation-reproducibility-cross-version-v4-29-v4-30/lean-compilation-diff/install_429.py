"""Bound one local elan install attempt to 30 seconds and size limits."""
import json
import os
import shutil
import signal
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
TOOLS = ROOT.parents[1]
ELAN = TOOLS / "elan/bin/elan"
TARGET = TOOLS / "elan/toolchains/leanprover--lean4---v4.29.0"
TMP = ROOT / "tmp"
TMP.mkdir(exist_ok=True)

def bytes_under(path):
    if not path.exists(): return 0
    return sum(p.stat().st_size for p in path.rglob("*") if p.is_file())

free = shutil.disk_usage(ROOT).free
if free < 4*1024**3:
    raise SystemExit("free space below 4 GiB install margin")
asset = json.loads((ROOT / "upstream-asset.json").read_text())
if asset["asset_download_bytes"] > 600_000_000:
    raise SystemExit("upstream archive exceeds 600 MB")
env = os.environ.copy()
env.update({"ELAN_HOME":str(TOOLS/"elan"),"TMPDIR":str(TMP),
            "PATH":str(TOOLS/"elan/bin")+os.pathsep+env.get("PATH","")})
command = [str(ELAN),"toolchain","install","leanprover/lean4:v4.29.0"]
start=time.monotonic()
with (ROOT/"install-429.log").open("ab") as log:
    proc=subprocess.Popen(command,env=env,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,
                          start_new_session=True)
    reason=None
    while proc.poll() is None:
        elapsed=time.monotonic()-start
        install_bytes=bytes_under(TARGET)
        scratch_bytes=bytes_under(ROOT)
        if elapsed>29:
            reason="30-second child limit"
        elif install_bytes>3*1024**3:
            reason="3 GiB expanded toolchain limit"
        elif scratch_bytes>1024**3:
            reason="1 GiB scratch limit"
        if reason:
            os.killpg(proc.pid,signal.SIGKILL)
            break
        time.sleep(0.5)
    proc.wait()
result={"command":command,"elapsed_s":round(time.monotonic()-start,3),
        "returncode":proc.returncode,"reason":reason,"target_bytes":bytes_under(TARGET),
        "scratch_bytes":bytes_under(ROOT),"free_bytes_after":shutil.disk_usage(ROOT).free}
(ROOT/"install-429.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
