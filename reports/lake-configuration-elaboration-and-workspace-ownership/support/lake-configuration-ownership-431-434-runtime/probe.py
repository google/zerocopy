#!/usr/bin/env python3
"""Serial local-dependency Lake config ownership probe for exact 4.31/4.34 tools."""
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

ROOT=Path(__file__).resolve().parents[1]
FIXTURE=ROOT/"fixture"
VERSIONS=("v4.31.0","v4.34.1")
LAKE_SHA={"v4.31.0":"58261a1a2fa1a362376c71e02ca854a093e71cc5e6ea64b287a931cb2565273d",
          "v4.34.1":"c8c24f1398162ab4004e2a869952d8469f54293651151feaad4526f2b8474c6e"}
LEAN_SHA="1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554"
MEM_START=.20; MEM_LIVE=.18; DISK=10*1024**3; RSS_KIB=1200*1024; SCRATCH=100*1024**2; TIMEOUT=20
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def memory():
    text=subprocess.check_output(["vm_stat"],text=True)
    page=int(re.search(r"page size of (\d+) bytes",text).group(1))
    vals={k:int(v.replace(".","")) for k,v in re.findall(r"Pages ([\w ]+):\s+(\d+\.)",text)}
    total=int(subprocess.check_output(["sysctl","-n","hw.memsize"]))
    return page*sum(vals[k] for k in ("free","inactive","speculative"))/total
def sample():
    return {"reclaimable_fraction":memory(),"disk_free_bytes":shutil.disk_usage(ROOT).free,
            "scratch_bytes":sum(p.stat().st_size for p in ROOT.rglob("*") if p.is_file() and not p.is_symlink())}
def rss(pgid):
    raw=subprocess.check_output(["ps","-axo","pgid=,rss="],text=True)
    return sum(int(parts[1]) for line in raw.splitlines()
               if (parts:=line.split()) and len(parts)==2 and parts[0].isdigit() and int(parts[0])==pgid)
def tree(path):
    if not path.exists(): return {}
    out={}
    for p in sorted(path.rglob("*")):
        if p.is_symlink(): continue
        stat=p.stat()
        out[str(p.relative_to(path))]={"type":"dir" if p.is_dir() else "file",
            "size":stat.st_size,"mtime_ns":stat.st_mtime_ns,"ctime_ns":stat.st_ctime_ns,"inode":stat.st_ino,
            "sha256":None if p.is_dir() else sha(p)}
    return out
def manifest(root):
    cfg=root/".lake/config"
    return {str(p.relative_to(root)):json.loads(p.read_text()) for p in cfg.rglob("*.trace")} if cfg.exists() else {}
def save(r): (ROOT/"results.json").write_text(json.dumps(r,indent=2,sort_keys=True)+"\n")
def main():
    ap=argparse.ArgumentParser();ap.add_argument("--toolchains-root",type=Path,required=True);a=ap.parse_args()
    tc_root=a.toolchains_root.resolve()
    source={str(p.relative_to(FIXTURE)):sha(p) for p in FIXTURE.rglob("*") if p.is_file()}
    toolchains={v:tc_root/f"leanprover--lean4---{v}" for v in VERSIONS}
    identities={}
    for v,tc in toolchains.items():
        lake=tc/"bin/lake";lean=tc/"bin/lean"
        assert lake.is_file() and lean.is_file() and sha(lake)==LAKE_SHA[v] and sha(lean)==LEAN_SHA,v
        identities[v]={"lake_path":str(lake),"lean_path":str(lean),"lake_sha256":sha(lake),"lean_sha256":sha(lean),
            "lake_version":subprocess.check_output([str(lake),"--version"],text=True,timeout=5).strip(),
            "lean_version":subprocess.check_output([str(lean),"--version"],text=True,timeout=5).strip()}
    result={"schema":1,"status":"prepared","fixture_sha256":source,"identities":identities,
        "guard":{"start_memory_fraction":MEM_START,"live_memory_fraction":MEM_LIVE,"min_disk_bytes":DISK,
                 "max_rss_kib":RSS_KIB,"max_scratch_bytes":SCRATCH,"timeout_seconds":TIMEOUT},
        "initial_admission":sample(),"calls":[],"snapshots":{}}
    save(result)
    if result["initial_admission"]["reclaimable_fraction"]<=MEM_START or result["initial_admission"]["disk_free_bytes"]<=DISK:
        result["status"]="admission_denied";save(result);return
    runs=ROOT/"runs"
    if runs.exists():shutil.rmtree(runs)
    runs.mkdir()
    def command(version,label,argv,cwd,env):
        admission=sample()
        if admission["reclaimable_fraction"]<=MEM_START or admission["disk_free_bytes"]<=DISK or admission["scratch_bytes"]>SCRATCH:
            raise RuntimeError(f"prelaunch guard {version}/{label}: {admission}")
        start=time.monotonic();p=subprocess.Popen([str(x) for x in argv],cwd=cwd,env=env,
                                                  stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
        live=[];locks=set();abort=None
        while True:
            try:out,err=p.communicate(timeout=.1);break
            except subprocess.TimeoutExpired:
                s=sample();s["group_rss_kib"]=rss(p.pid);live.append(s)
                locks.update(str(z.relative_to(cwd.parent)) for z in cwd.parent.rglob("*.lock") if z.is_file())
                if s["reclaimable_fraction"]<MEM_LIVE:abort="memory"
                elif s["disk_free_bytes"]<=DISK:abort="disk"
                elif s["scratch_bytes"]>SCRATCH:abort="scratch"
                elif s["group_rss_kib"]>RSS_KIB:abort="rss"
                elif time.monotonic()-start>TIMEOUT:abort="timeout"
                if abort:
                    os.killpg(p.pid,signal.SIGKILL);out,err=p.communicate(timeout=3);break
        row={"version":version,"label":label,"argv":[str(x) for x in argv],"cwd":str(cwd),
             "returncode":p.returncode,"abort":abort,"elapsed_seconds":round(time.monotonic()-start,4),
             "admission":admission,"live_samples":live,"observed_lock_paths":sorted(locks),
             "stdout":out.decode(errors="replace"),"stderr":err.decode(errors="replace")}
        result["calls"].append(row);save(result);print(version,label,p.returncode,abort,flush=True)
        if abort:raise RuntimeError(f"live guard: {version}/{label}: {abort}")
        return row
    result["status"]="running";save(result)
    for version,tc in toolchains.items():
        vruns=runs/version.replace(".","_")
        vruns.mkdir()
        for name in ("shared","filler","a","b","t"):
            dst=vruns/name;shutil.copytree(FIXTURE/name,dst)
            (dst/"lean-toolchain").write_text(f"leanprover/lean4:{version}\n")
        env=os.environ.copy();env.update({"ELAN_HOME":str(tc_root.parent),"ELAN_TOOLCHAIN":f"leanprover/lean4:{version}",
            "PATH":str(tc/"bin")+os.pathsep+env.get("PATH",""),"LEAN_NUM_THREADS":"1","LAKE_JOBS":"1","LAKE_NO_NET":"1"})
        lake=tc/"bin/lake"
        snapshots={"before":{"a":tree(vruns/"a"),"b":tree(vruns/"b"),"t":tree(vruns/"t"),"shared":tree(vruns/"shared")}}
        for label,workspace,extra in (("load-a","a",[]),("load-b","b",[]),("reload-a","a",[]),("load-toml","t",["-f","lakefile.toml"])):
            command(version,label,[lake,"--keep-toolchain",*extra,"update"],vruns/workspace,env)
            snapshots[label]={n:tree(vruns/n) for n in ("a","b","t","shared","filler")}
            snapshots[label+"-traces"]={n:manifest(vruns/n) for n in ("a","b","t","shared","filler")}
            result["snapshots"][version]=snapshots;save(result)
    result["status"]="completed";save(result)
if __name__=="__main__":main()
