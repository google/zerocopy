#!/usr/bin/env python3
"""Small serial Lean unused-simp-args linter matrix with child caps."""
import hashlib,json,re,shutil,subprocess,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
TC=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains')
BINS={'old':TC/'leanprover--lean4---v4.30.0-rc2/bin/lean',
      'new':TC/'leanprover--lean4---v4.34.1/bin/lean'}
SHAS={'old':'b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997',
      'new':'1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554'}
CASES=('ordinary','options','no-progress','no-progress-relaxed')
def sha(b):return hashlib.sha256(b).hexdigest()
def admission():
    vm=subprocess.check_output(['vm_stat'],text=True)
    page=int(re.search(r'page size of (\d+) bytes',vm).group(1))
    pages={k:int(re.search(r'Pages '+k+r':\s+(\d+)',vm).group(1)) for k in ('free','inactive','speculative')}
    mem=int(subprocess.check_output(['sysctl','-n','hw.memsize'],text=True))
    disk=shutil.disk_usage(ROOT).free
    owned=sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file())
    pct=100*page*sum(pages.values())/mem
    result={'page_bytes':page,'pages':pages,'memory_bytes':mem,'reclaimable_percent':pct,'disk_free_bytes':disk,'owned_bytes':owned}
    if pct<=20 or disk<=1_073_741_824 or owned>=100_000_000:raise RuntimeError(f'admission failed: {result}')
    return result
def run(role,case):
    argv=[str(BINS[role]),'--json',f'fixture/{case}.lean']
    gate=admission();start=time.monotonic()
    proc=subprocess.Popen(argv,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    peak=polls=0;terminated=None
    while True:
        try:stdout,stderr=proc.communicate(timeout=.05);break
        except subprocess.TimeoutExpired:
            ps=subprocess.run(['ps','-o','rss=','-p',str(proc.pid)],capture_output=True,text=True)
            try:rss=int(ps.stdout.strip())
            except ValueError:rss=0
            peak=max(peak,rss);polls+=1
            if peak>1_048_576 or time.monotonic()-start>30:
                terminated='sampled RSS >1 GiB' if peak>1_048_576 else 'elapsed >30s'
                proc.kill();stdout,stderr=proc.communicate();break
    elapsed=time.monotonic()-start
    base=ROOT/'raw'/role;base.mkdir(parents=True,exist_ok=True)
    (base/f'{case}.stdout').write_bytes(stdout);(base/f'{case}.stderr').write_bytes(stderr)
    return {'argv':argv,'admission':gate,'exit_code':proc.returncode,'terminated':terminated,'elapsed_s':elapsed,
            'rss_polls':polls,'sampled_peak_rss_kib':peak,'stdout_sha256':sha(stdout),'stdout_bytes':len(stdout),
            'stderr_sha256':sha(stderr),'stderr_bytes':len(stderr)}
def main():
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--role',choices=BINS);a=p.parse_args()
    roles=(a.role,) if a.role else BINS
    out=ROOT/'results.json'
    result=json.loads(out.read_text()) if out.exists() else {'schema':1,'fixtures':{},'tools':{},'cells':{}}
    for case in CASES:result['fixtures'][case]=sha((ROOT/'fixture'/f'{case}.lean').read_bytes())
    for role in roles:
        exe=BINS[role];assert sha(exe.read_bytes())==SHAS[role]
        result['tools'][role]={'executable':str(exe),'sha256':SHAS[role],
                               'version':subprocess.check_output([str(exe),'--version'],text=True)}
        out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
        for case in CASES:
            key=f'{role}/{case}'
            if key in result['cells']:continue
            c=run(role,case);result['cells'][key]=c
            out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
            print(key,c['exit_code'],c['sampled_peak_rss_kib'],round(c['admission']['reclaimable_percent'],2),flush=True)
            if c['terminated']:raise RuntimeError(f'child cap: {key}')
if __name__=='__main__':main()
