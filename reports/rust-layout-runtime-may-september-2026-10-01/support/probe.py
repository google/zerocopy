#!/usr/bin/env python3
"""Run two installed host rustc binaries serially, with per-child admission."""
import hashlib, json, re, shutil, subprocess, time
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent
TC=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/rustup/toolchains')
BINS={'old':TC/'nightly-2026-05-31-aarch64-apple-darwin/bin/rustc',
      'new':TC/'nightly-2026-09-30-aarch64-apple-darwin/bin/rustc'}
SHAS={'old':'2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc',
      'new':'29f8ccc9aa7b0d8798eda854fa7f0e4ba3867c8c336b87d52dbb3b24b3f0878d'}
def sha(b):return hashlib.sha256(b).hexdigest()
def gate():
    vm=subprocess.check_output(['vm_stat'],text=True)
    page=int(re.search(r'page size of (\d+) bytes',vm).group(1))
    pages={k:int(re.search(r'Pages '+k+r':\s+(\d+)',vm).group(1)) for k in ('free','inactive','speculative')}
    mem=int(subprocess.check_output(['sysctl','-n','hw.memsize'],text=True))
    disk=shutil.disk_usage(ROOT).free
    owned=sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file())
    pct=100*page*sum(pages.values())/mem
    row={'page_bytes':page,'pages':pages,'memory_bytes':mem,'reclaimable_percent':pct,'disk_free_bytes':disk,'owned_bytes':owned}
    if pct<=20 or disk<=1_073_741_824 or owned>=100_000_000:raise RuntimeError(f'admission refused: {row}')
    return row
def child(argv,role,kind):
    admission=gate();start=time.monotonic()
    p=subprocess.Popen(argv,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    peak=polls=0;terminated=None
    while True:
        try:stdout,stderr=p.communicate(timeout=.025);break
        except subprocess.TimeoutExpired:
            ps=subprocess.run(['ps','-o','rss=','-p',str(p.pid)],capture_output=True,text=True)
            try:rss=int(ps.stdout.strip())
            except ValueError:rss=0
            peak=max(peak,rss);polls+=1
            if peak>1_048_576 or time.monotonic()-start>30:
                terminated='sampled RSS over 1 GiB' if peak>1_048_576 else '30-second timeout'
                p.kill();stdout,stderr=p.communicate();break
    prefix=ROOT/'raw'/role/kind
    prefix.parent.mkdir(parents=True,exist_ok=True)
    (prefix.with_suffix('.stdout')).write_bytes(stdout)
    (prefix.with_suffix('.stderr')).write_bytes(stderr)
    return {'argv':argv,'admission':admission,'exit_code':p.returncode,'terminated':terminated,
            'elapsed_s':time.monotonic()-start,'rss_polls':polls,'sampled_peak_rss_kib':peak,
            'stdout_sha256':sha(stdout),'stdout_bytes':len(stdout),'stderr_sha256':sha(stderr),'stderr_bytes':len(stderr)}
def main():
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('--role',choices=BINS)
    args=parser.parse_args();roles=(args.role,) if args.role else tuple(BINS)
    path=ROOT/'results.json'
    result=json.loads(path.read_text()) if path.exists() else {'schema':1,'fixture_sha256':sha((ROOT/'fixture/layout.rs').read_bytes()),'tools':{},'cells':{}}
    for role in roles:
        exe=BINS[role];assert sha(exe.read_bytes())==SHAS[role]
        result['tools'][role]={'executable':str(exe),'sha256':SHAS[role],
                               'version_verbose':subprocess.check_output([str(exe),'-Vv'],text=True)}
        out=ROOT/'raw'/role/'layout-probe'
        out.parent.mkdir(parents=True,exist_ok=True)
        compile_argv=[str(exe),'--crate-name','layout_probe','--edition','2024','-C','opt-level=0','-Zprint-type-sizes','-o',str(out),'fixture/layout.rs']
        if f'{role}/compile' not in result['cells']:
            row=child(compile_argv,role,'compile');result['cells'][f'{role}/compile']=row
            path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
            print(role,'compile',row['exit_code'],row['stderr_bytes'],round(row['admission']['reclaimable_percent'],2),flush=True)
            if row['exit_code'] or row['terminated']:raise RuntimeError(f'{role} compile failed')
        binary=out.read_bytes();result['cells'][f'{role}/compile']['binary_sha256']=sha(binary)
        result['cells'][f'{role}/compile']['binary_bytes']=len(binary)
        path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
        if f'{role}/run' not in result['cells']:
            row=child([str(out)],role,'run');result['cells'][f'{role}/run']=row
            path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
            print(role,'run',row['exit_code'],row['stdout_bytes'],round(row['admission']['reclaimable_percent'],2),flush=True)
            if row['exit_code'] or row['terminated']:raise RuntimeError(f'{role} run failed')
if __name__=='__main__':main()
