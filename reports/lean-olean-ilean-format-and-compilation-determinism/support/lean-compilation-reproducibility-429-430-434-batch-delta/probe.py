#!/usr/bin/env python3
"""Sequential batch-only Lean/Lake replay of the published R447 two-module fixture."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "fixture"
MIN_START_MEM = .20
MIN_LIVE_MEM = .18
MIN_DISK = 10 * 1024**3
MAX_SCRATCH = 100 * 1024**2
MAX_RSS_KIB = 1200 * 1024
TIMEOUT = 30
VERSIONS = ("v4.29.0", "v4.30.0-rc2", "v4.34.1")
LEAN_HASH = {
    "v4.29.0": "2974847fff2e2621502841f4c2dbac4035b4847d6060a4f2087cbc0d04005e37",
    "v4.30.0-rc2": "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997",
    "v4.34.1": "1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554",
}
FIXTURE_HASH = {
    "lakefile.lean": "ba744b92c5524c6c8096aaa38f57da7c1944d7162546945300206027ba7a3674",
    "lake-manifest.json": "e00985d61f56efe3f912003a1628166119c495ce8c94ede0f09b56436e896072",
    "Probe/Base.lean": "353b9ceb04f5f739703468c468023da3d3c201a9d3a5398dae5bfa0119b57088",
    "Probe.lean": "1c6efbb5aafdec02b3f8c876307a6ac18fa59c18875960411ae2d22d932564ba",
    "Goal.lean": "ca72613130b63f3ceedde54104312a54adc4949b1295b2ae0ee6f2f545799ced",
}
GOAL_V2 = "import Probe\ntheorem demo (n : Nat) (h : n = 0) : n + 0 = 0 := by\n  simpa using h\n"

def sha(data): return hashlib.sha256(data).hexdigest()
def file_hash(path): return sha(path.read_bytes())

def resource():
    vm = subprocess.check_output(["vm_stat"], text=True)
    page = int(re.search(r"page size of (\d+) bytes", vm).group(1))
    pages = {k: int(v.replace(".", "")) for k,v in re.findall(r"Pages ([\w ]+):\s+(\d+\.)", vm)}
    total = int(subprocess.check_output(["sysctl", "-n", "hw.memsize"]))
    scratch = sum(p.stat().st_size for p in ROOT.rglob("*") if p.is_file() and not p.is_symlink())
    return {"reclaimable_fraction": page * sum(pages[k] for k in ("free","inactive","speculative")) / total,
            "disk_free_bytes": shutil.disk_usage(ROOT).free, "scratch_bytes": scratch}

def group_rss(pgid):
    ps = subprocess.check_output(["ps", "-axo", "pgid=,rss="], text=True)
    return sum(int(parts[1]) for line in ps.splitlines()
               if (parts := line.split()) and len(parts) == 2 and parts[0].isdigit() and int(parts[0]) == pgid)

def snapshot(tree):
    return {str(p.relative_to(tree)): {"sha256": file_hash(p), "bytes": p.stat().st_size}
            for p in sorted(tree.rglob("*")) if p.is_file() and not p.is_symlink()} if tree.exists() else {}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--toolchains-root", type=Path, required=True)
    args = parser.parse_args()
    tc_root = args.toolchains_root.resolve()
    for path, expected in FIXTURE_HASH.items():
        assert file_hash(FIXTURE / path) == expected, path
    toolchains = {v: tc_root / f"leanprover--lean4---{v}" for v in VERSIONS}
    identities = {}
    for v, tc in toolchains.items():
        lean, lake = tc / "bin/lean", tc / "bin/lake"
        assert lean.is_file() and lake.is_file(), v
        assert file_hash(lean) == LEAN_HASH[v], v
        identities[v] = {"lean_path": str(lean), "lake_path": str(lake),
                         "lean_sha256": file_hash(lean), "lake_sha256": file_hash(lake)}
    start = resource()
    record = {"schema":1,"status":"running","guard":{"start_memory":MIN_START_MEM,"live_memory":MIN_LIVE_MEM,
              "disk_bytes":MIN_DISK,"scratch_bytes":MAX_SCRATCH,"rss_kib":MAX_RSS_KIB,"timeout_s":TIMEOUT},
              "initial_admission":start,"fixture_sha256":FIXTURE_HASH,"identities":identities,"versions":{},"calls":[]}
    (ROOT / "results.json").write_text(json.dumps(record,indent=2,sort_keys=True)+"\n")
    if start["reclaimable_fraction"] <= MIN_START_MEM or start["disk_free_bytes"] <= MIN_DISK:
        record["status"] = "admission_denied"
        (ROOT / "results.json").write_text(json.dumps(record,indent=2,sort_keys=True)+"\n")
        return
    runs = ROOT / "runs"
    if runs.exists(): shutil.rmtree(runs)
    runs.mkdir()
    def save(): (ROOT / "results.json").write_text(json.dumps(record,indent=2,sort_keys=True)+"\n")
    def command(v,label,argv,cwd,env):
        sample=resource()
        if sample["reclaimable_fraction"] <= MIN_START_MEM or sample["disk_free_bytes"] <= MIN_DISK or sample["scratch_bytes"] > MAX_SCRATCH:
            raise RuntimeError(f"prelaunch guard {v}/{label}: {sample}")
        started=time.monotonic()
        p=subprocess.Popen([str(x) for x in argv],cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
        samples=[];abort=None
        while True:
            try:
                out,err=p.communicate(timeout=.12)
                break
            except subprocess.TimeoutExpired:
                s=resource();s["group_rss_kib"]=group_rss(p.pid);samples.append(s)
                if s["reclaimable_fraction"] < MIN_LIVE_MEM: abort="memory"
                elif s["disk_free_bytes"] <= MIN_DISK: abort="disk"
                elif s["scratch_bytes"] > MAX_SCRATCH: abort="scratch"
                elif s["group_rss_kib"] > MAX_RSS_KIB: abort="rss"
                elif time.monotonic()-started > TIMEOUT: abort="timeout"
                if abort:
                    os.killpg(p.pid,signal.SIGKILL)
                    out,err=p.communicate(timeout=3)
                    break
        row={"version":v,"label":label,"argv":[str(x) for x in argv],"cwd":str(cwd),
             "returncode":p.returncode,"abort":abort,"elapsed_s":round(time.monotonic()-started,4),
             "admission":sample,"live_samples":samples,"stdout":out.decode(errors="replace"),"stderr":err.decode(errors="replace"),
             "stdout_sha256":sha(out),"stderr_sha256":sha(err)}
        record["calls"].append(row);save();print(v,label,p.returncode,abort,flush=True)
        if abort: raise RuntimeError(f"live guard {v}/{label}: {abort}")
        return row
    for v, tc in toolchains.items():
        tag=v.replace(".","_").replace("-","_")
        base=runs/tag;project=base/"project";cache=base/"cache";artifacts=base/"artifacts"
        project.mkdir(parents=True)
        for name in FIXTURE_HASH:
            target=project/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(FIXTURE/name,target)
        (project/"lean-toolchain").write_text(f"leanprover/lean4:{v}\n")
        env=os.environ.copy();env.update({"ELAN_HOME":str(tc_root.parent),"ELAN_TOOLCHAIN":f"leanprover/lean4:{v}",
            "PATH":str(tc/"bin")+os.pathsep+env.get("PATH",""),"LEAN_NUM_THREADS":"1","LAKE_JOBS":"1","LAKE_NO_NET":"1"})
        lake=tc/"bin/lake";lean=tc/"bin/lean"
        cells={}
        for cell in ("clean-1","clean-2","cache-seed","cache-reuse-1","cache-reuse-2"):
            shutil.rmtree(project/".lake",ignore_errors=True)
            cached=cell.startswith("cache")
            mode=env.copy();mode.update({"LAKE_ARTIFACT_CACHE":"true" if cached else "false",
                                         "LAKE_CACHE_DIR":str(cache) if cached else ""})
            args=[lake,"--keep-toolchain"]+([] if cached else ["--no-cache"])+["--old","build","Probe"]
            built=command(v,cell,args,project,mode)
            snap=snapshot(project/".lake/build")
            dest=artifacts/cell
            if (project/".lake/build").exists(): shutil.copytree(project/".lake/build",dest)
            cells[cell]={"build_returncode":built["returncode"],"artifacts":snap}
            if built["returncode"] != 0: break
            command(v,cell+"-setup",[lake,"--keep-toolchain","setup-file","Probe.lean"],project,mode)
            command(v,cell+"-probe-json",[lake,"--keep-toolchain","env","lean","--json","Probe.lean"],project,mode)
        record["versions"][v]={"build_cells":cells,"cache_snapshot":snapshot(cache)};save()
        if len(cells)!=5: continue
        cached=env.copy();cached.update({"LAKE_ARTIFACT_CACHE":"true","LAKE_CACHE_DIR":str(cache)})
        command(v,"cache-goal-json",[lake,"--keep-toolchain","env","lean","--json","Goal.lean"],project,cached)
        uncached=env.copy();uncached.update({"LAKE_ARTIFACT_CACHE":"false","LAKE_CACHE_DIR":""})
        materialized=command(v,"materialize",[lake,"--keep-toolchain","--no-cache","--old","build","Probe"],project,uncached)
        msnap=snapshot(project/".lake/build");record["versions"][v]["materialized_artifacts"]=msnap
        if (project/".lake/build").exists(): shutil.copytree(project/".lake/build",artifacts/"materialized")
        save()
        if materialized["returncode"] == 0:
            command(v,"materialized-probe-json",[lake,"--keep-toolchain","env","lean","--json","Probe.lean"],project,uncached)
            command(v,"materialized-goal-v1-json",[lake,"--keep-toolchain","env","lean","--json","Goal.lean"],project,uncached)
            (project/"Goal.lean").write_text(GOAL_V2)
            try: command(v,"materialized-goal-v2-json",[lake,"--keep-toolchain","env","lean","--json","Goal.lean"],project,uncached)
            finally: shutil.copyfile(FIXTURE/"Goal.lean",project/"Goal.lean")
    record["status"]="completed";save()

if __name__ == "__main__": main()
