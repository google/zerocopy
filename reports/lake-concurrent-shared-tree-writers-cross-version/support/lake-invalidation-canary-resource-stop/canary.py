#!/usr/bin/env python3
"""Guarded, offline Lake canary; all scratch stays inside this package."""
import hashlib,json,os,re,shutil,signal,subprocess,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
TC=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains')
BINS={'old':TC/'leanprover--lean4---v4.30.0-rc2/bin/lake',
      'new':TC/'leanprover--lean4---v4.34.1/bin/lake'}
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
    if pct<=20 or disk<=10*1024**3 or owned>=100_000_000:raise RuntimeError(f'Lake admission refused: {result}')
    return result
def group_rss(pgid):
    ps=subprocess.run(['ps','-axo','pgid=,rss='],capture_output=True,text=True)
    total=0
    for line in ps.stdout.splitlines():
        fields=line.split()
        if len(fields)==2 and int(fields[0])==pgid:total+=int(fields[1])
    return total
def manifest(root):
    result={}
    for p in sorted(root.rglob('*')):
        if p.is_file():
            stat=p.stat();result[str(p.relative_to(root))]={'sha256':sha(p.read_bytes()),'size':stat.st_size,'mtime_ns':stat.st_mtime_ns}
    return result
def run(role):
    work=ROOT/'runs'/role
    if not work.exists():shutil.copytree(ROOT/'fixture',work)
    consumer=work/'consumer';out=ROOT/'raw'/role;out.mkdir(parents=True,exist_ok=True)
    env=os.environ.copy();env['PATH']=str(BINS[role].parent)+os.pathsep+env.get('PATH','')
    env['LAKE_ARTIFACT_CACHE']='false';env['LAKE_CACHE_DIR']=str(out/'lake-cache')
    argv=[str(BINS[role]),'--no-cache','-v','build','Core','Main']
    gate=admission();before=manifest(work)
    start=time.monotonic()
    proc=subprocess.Popen(argv,cwd=consumer,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
    peak=polls=0;terminated=None
    while True:
        try:stdout,stderr=proc.communicate(timeout=.05);break
        except subprocess.TimeoutExpired:
            rss=group_rss(proc.pid);peak=max(peak,rss);polls+=1
            if rss>1_048_576 or time.monotonic()-start>30:
                terminated='process-group RSS >1 GiB' if rss>1_048_576 else 'elapsed >30s'
                os.killpg(proc.pid,signal.SIGKILL);stdout,stderr=proc.communicate();break
    elapsed=time.monotonic()-start
    (out/'build.stdout').write_bytes(stdout);(out/'build.stderr').write_bytes(stderr)
    after=manifest(work)
    result={'role':role,'argv':argv,'cwd':str(consumer),'env':{'PATH_prefix':str(BINS[role].parent),'LAKE_ARTIFACT_CACHE':'false','LAKE_CACHE_DIR':env['LAKE_CACHE_DIR']},
            'lake_sha256':sha(BINS[role].read_bytes()),'lake_version':subprocess.check_output([str(BINS[role]),'--version'],text=True).strip(),
            'admission':gate,'exit_code':proc.returncode,'terminated':terminated,'elapsed_s':elapsed,'sampled_peak_group_rss_kib':peak,'rss_polls':polls,
            'stdout_sha256':sha(stdout),'stdout_bytes':len(stdout),'stderr_sha256':sha(stderr),'stderr_bytes':len(stderr),
            'before':before,'after':after}
    (out/'record.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(role,proc.returncode,terminated,'rss_kib',peak,'seconds',round(elapsed,3),'gate_ram',round(gate['reclaimable_percent'],3),'gate_disk',gate['disk_free_bytes'],'before_files',len(before),'after_files',len(after),flush=True)
    if terminated or proc.returncode!=0:raise RuntimeError(f'{role} canary failed')
def main():
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--role',choices=BINS,required=True);a=p.parse_args()
    run(a.role)
if __name__=='__main__':main()
