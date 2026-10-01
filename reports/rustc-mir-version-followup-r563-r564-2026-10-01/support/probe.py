#!/usr/bin/env python3
"""Guarded, serial rustc MIR stage probe; no Charon, Cargo, or network."""
import hashlib
import json
import re
import shutil
import subprocess
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent
TOOLCHAINS=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/rustup/toolchains')
BINS={
    'old':TOOLCHAINS/'nightly-2026-05-31-aarch64-apple-darwin/bin/rustc',
    'new':TOOLCHAINS/'nightly-2026-09-30-aarch64-apple-darwin/bin/rustc',
}
SHAS={
    'old':'2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc',
    'new':'29f8ccc9aa7b0d8798eda854fa7f0e4ba3867c8c336b87d52dbb3b24b3f0878d',
}
CASES={
    'r563':('opt0','opt2','simplify-dump'),
    'r564':('opt0','opt2','intrinsic-dump'),
}

def sha(data):return hashlib.sha256(data).hexdigest()
def admission():
    vm=subprocess.check_output(['vm_stat'],text=True)
    page=int(re.search(r'page size of (\d+) bytes',vm).group(1))
    pages={k:int(re.search(r'Pages '+k+r':\s+(\d+)',vm).group(1)) for k in ('free','inactive','speculative')}
    mem=int(subprocess.check_output(['sysctl','-n','hw.memsize'],text=True))
    pct=100*page*sum(pages.values())/mem
    disk=shutil.disk_usage(ROOT).free
    owned=sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file())
    record={'page_bytes':page,'pages':pages,'memory_bytes':mem,
            'reclaimable_percent':pct,'disk_free_bytes':disk,'owned_bytes':owned}
    if pct<=20 or disk<=1_073_741_824 or owned>=100_000_000:
        raise RuntimeError(f'admission rejected: {record}')
    return record

def run(role,suite,mode):
    root=ROOT/'raw'/role/suite;root.mkdir(parents=True,exist_ok=True)
    artifact=root/f'{mode}.mir';dump=root/f'{mode}-dumps'
    argv=[str(BINS[role]),'--crate-name',suite,'--crate-type','lib','--edition','2024',
          '-Adead_code','-Aunreachable_code','-Zmir-opt-level='+('2' if mode=='opt2' else '0'),
          '--emit=mir','-o',str(artifact)]
    if mode.endswith('-dump'):
        dump.mkdir(exist_ok=True)
        selector='SimplifyCfg' if suite=='r563' else 'LowerIntrinsics'
        argv.extend(['-Zdump-mir='+selector,'-Zdump-mir-dir='+str(dump)])
    argv.append(f'fixture/{suite}.rs')
    gate=admission();start=time.monotonic()
    proc=subprocess.Popen(argv,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    peak=0;polls=0;terminated=None
    while True:
        try:stdout,stderr=proc.communicate(timeout=.025);break
        except subprocess.TimeoutExpired:
            ps=subprocess.run(['ps','-o','rss=','-p',str(proc.pid)],capture_output=True,text=True)
            try:rss=int(ps.stdout.strip())
            except ValueError:rss=0
            peak=max(peak,rss);polls+=1
            if peak>1_048_576 or time.monotonic()-start>30:
                terminated='sampled RSS over 1 GiB' if peak>1_048_576 else '30-second timeout'
                proc.kill();stdout,stderr=proc.communicate();break
    elapsed=time.monotonic()-start
    (root/f'{mode}.stdout').write_bytes(stdout)
    (root/f'{mode}.stderr').write_bytes(stderr)
    art=artifact.read_bytes() if artifact.exists() else None
    dump_files={str(p.relative_to(ROOT)):{'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size}
                for p in sorted(dump.rglob('*')) if p.is_file()} if dump.exists() else {}
    return {'role':role,'suite':suite,'mode':mode,'argv':argv,'admission':gate,
            'exit_code':proc.returncode,'terminated':terminated,'elapsed_s':elapsed,
            'rss_polls':polls,'sampled_peak_rss_kib':peak,
            'stdout_sha256':sha(stdout),'stdout_bytes':len(stdout),
            'stderr_sha256':sha(stderr),'stderr_bytes':len(stderr),
            'artifact_sha256':sha(art) if art is not None else None,
            'artifact_bytes':len(art) if art is not None else None,
            'dump_files':dump_files}

def main():
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('--role',choices=BINS)
    args=ap.parse_args();roles=(args.role,) if args.role else tuple(BINS)
    path=ROOT/'results.json'
    result=json.loads(path.read_text()) if path.exists() else {'schema':1,'fixtures':{},'tools':{},'cells':{}}
    for suite in CASES:result['fixtures'][suite]=sha((ROOT/'fixture'/f'{suite}.rs').read_bytes())
    for role in roles:
        exe=BINS[role];assert sha(exe.read_bytes())==SHAS[role]
        result['tools'][role]={'executable':str(exe),'sha256':SHAS[role],
                               'version_verbose':subprocess.check_output([str(exe),'-Vv'],text=True)}
        path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
        for suite,modes in CASES.items():
            for mode in modes:
                key=f'{role}/{suite}/{mode}'
                if key in result['cells']:continue
                cell=run(role,suite,mode);result['cells'][key]=cell
                path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
                print(key,cell['exit_code'],cell['artifact_bytes'],len(cell['dump_files']),round(cell['admission']['reclaimable_percent'],2),flush=True)
                if cell['terminated'] or cell['exit_code']!=0:raise RuntimeError(f'probe failed: {key}: {cell}')

if __name__=='__main__':main()
