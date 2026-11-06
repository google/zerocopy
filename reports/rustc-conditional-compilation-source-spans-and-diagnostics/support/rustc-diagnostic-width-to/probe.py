#!/usr/bin/env python3
"""Bounded local rustc diagnostic-width matrix on a reconstructed specimen."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/"fixture/Width.rs"
VERSIONS=("nightly-2026-05-31","stable-1.98.1","nightly-2026-09-30")
EXPECTED={"nightly-2026-05-31":"2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc",
          "stable-1.98.1":"2814fb55fb9cfb3eef5848a8104d77e3de7fd95394661144a12ee90cd4405340",
          "nightly-2026-09-30":"29f8ccc9aa7b0d8798eda854fa7f0e4ba3867c8c336b87d52dbb3b24b3f0878d"}
MIN_MEM=.20;MIN_DISK=1024**3;MAX_SCRATCH=100*1024**2;TIMEOUT=10
def sha(data):return hashlib.sha256(data).hexdigest()
def sample():
    vm=subprocess.check_output(["vm_stat"],text=True)
    page=int(re.search(r"page size of (\d+) bytes",vm).group(1))
    vals={k:int(v.replace(".","")) for k,v in re.findall(r"Pages ([\w ]+):\s+(\d+\.)",vm)}
    total=int(subprocess.check_output(["sysctl","-n","hw.memsize"]))
    scratch=sum(p.stat().st_size for p in ROOT.rglob("*") if p.is_file() and not p.is_symlink())
    return {"reclaimable_fraction":page*sum(vals[k] for k in ("free","inactive","speculative"))/total,
            "disk_free_bytes":shutil.disk_usage(ROOT).free,"scratch_bytes":scratch}
def main():
    ap=argparse.ArgumentParser()
    for version in VERSIONS:ap.add_argument("--"+version,type=Path,required=True)
    a=ap.parse_args();bins={v:getattr(a,v.replace("-","_")) for v in VERSIONS}
    for v,p in bins.items():assert p.is_file() and sha(p.read_bytes())==EXPECTED[v],v
    initial=sample()
    result={"schema":1,"status":"prepared","fixture_status":"reconstructed_not_original_ui_bytes",
            "fixture_sha256":sha(SOURCE.read_bytes()),"compiler_sha256":EXPECTED,
            "compiler_versions":{v:subprocess.check_output([str(p),"-Vv"],text=True,timeout=5) for v,p in bins.items()},
            "compiler_paths":{v:str(p.resolve()) for v,p in bins.items()},
            "guard":{"min_memory_fraction":MIN_MEM,"min_disk_bytes":MIN_DISK,"max_scratch_bytes":MAX_SCRATCH,"timeout_s":TIMEOUT},
            "initial_admission":initial,"cells":[]}
    (ROOT/"results.json").write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    if initial["reclaimable_fraction"]<=MIN_MEM or initial["disk_free_bytes"]<=MIN_DISK or initial["scratch_bytes"]>MAX_SCRATCH:
        result["status"]="admission_denied";(ROOT/"results.json").write_text(json.dumps(result,indent=2,sort_keys=True)+"\n");return
    raw=ROOT/"raw";out=ROOT/"out"
    for p in (raw,out):
        if p.exists():shutil.rmtree(p)
        p.mkdir()
    result["status"]="running"
    for version,binary in bins.items():
        for mode,width in (("json",40),("json",100),("human",40),("human",100),("json-short",100)):
            admission=sample()
            if admission["reclaimable_fraction"]<=MIN_MEM or admission["disk_free_bytes"]<=MIN_DISK or admission["scratch_bytes"]>MAX_SCRATCH:
                raise RuntimeError(f"prelaunch guard {version}/{mode}/{width}: {admission}")
            output_dir=out/f"{version}-{mode}-w{width}";output_dir.mkdir()
            fmt="json" if mode.startswith("json") else "human"
            args=[str(binary),str(SOURCE),"--crate-name","width_probe","--edition=2021","--emit=metadata",
                  "--out-dir",str(output_dir),f"--error-format={fmt}",f"--diagnostic-width={width}"]
            if mode=="human":args.append("--color=never")
            if mode=="json-short":args.append("--json=diagnostic-short")
            start=time.monotonic()
            p=subprocess.run(args,cwd=ROOT,capture_output=True,timeout=TIMEOUT)
            stem=f"{version}-{mode}-w{width}"
            (raw/f"{stem}.stdout").write_bytes(p.stdout)
            (raw/f"{stem}.stderr").write_bytes(p.stderr)
            row={"version":version,"mode":mode,"width":width,"argv":args,"returncode":p.returncode,
                 "elapsed_seconds":round(time.monotonic()-start,5),"admission":admission,
                 "stdout_path":f"raw/{stem}.stdout","stdout_sha256":sha(p.stdout),
                 "stderr_path":f"raw/{stem}.stderr","stderr_sha256":sha(p.stderr),
                 "output_files":{str(q.relative_to(out)):sha(q.read_bytes()) for q in output_dir.rglob("*") if q.is_file()}}
            result["cells"].append(row)
            (ROOT/"results.json").write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
            print(stem,p.returncode,flush=True)
    result["status"]="completed"
    (ROOT/"results.json").write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
if __name__=="__main__":main()
