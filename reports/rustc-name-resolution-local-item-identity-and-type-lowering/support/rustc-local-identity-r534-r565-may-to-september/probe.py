#!/usr/bin/env python3
"""Small, offline Rust local-item HIR probe with per-child resource admission."""
import hashlib
import json
import re
import shutil
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TOOLCHAINS = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/rustup/toolchains')
BINS = {
    'old': TOOLCHAINS / 'nightly-2026-05-31-aarch64-apple-darwin/bin/rustc',
    'new': TOOLCHAINS / 'nightly-2026-09-30-aarch64-apple-darwin/bin/rustc',
}
VARIANTS = ('original', 'repaired', 'shifted')

def sha(data): return hashlib.sha256(data).hexdigest()

def admission():
    vm = subprocess.check_output(['vm_stat'], text=True)
    page = int(re.search(r'page size of (\d+) bytes', vm).group(1))
    pages = {k: int(re.search(r'Pages '+k+r':\s+(\d+)', vm).group(1))
             for k in ('free', 'inactive', 'speculative')}
    total = int(subprocess.check_output(['sysctl', '-n', 'hw.memsize'], text=True))
    pct = 100 * page * sum(pages.values()) / total
    disk = shutil.disk_usage(ROOT).free
    raw = sum(p.stat().st_size for p in (ROOT/'raw').glob('*') if p.is_file())
    result = {'page_bytes':page,'pages':pages,'memory_bytes':total,
              'reclaimable_percent':pct,'disk_free_bytes':disk,'owned_raw_bytes':raw}
    if pct <= 20 or disk <= 1_073_741_824 or raw >= 100_000_000:
        raise RuntimeError(f'admission rejected: {result}')
    return result

def run(role, variant, phase):
    exe = BINS[role]
    source = ROOT/'fixture'/f'{variant}-local.rs'
    stem=f'{role}--{variant}--{phase}'
    artifact=ROOT/'raw'/f'{stem}.rmeta'
    cmd = [str(exe),'--crate-name','local_identity','--edition=2024']
    cmd += ['-Zunpretty=hir-tree'] if phase == 'hir' else ['--emit=metadata','-o',str(artifact)]
    cmd += [str(source)]
    resource = admission()
    start = time.monotonic()
    proc = subprocess.run(cmd,cwd=ROOT,capture_output=True,timeout=20)
    elapsed = time.monotonic()-start
    (ROOT/'raw'/f'{stem}.stdout').write_bytes(proc.stdout)
    (ROOT/'raw'/f'{stem}.stderr').write_bytes(proc.stderr)
    artifact_data=artifact.read_bytes() if artifact.exists() else None
    return {'role':role,'variant':variant,'phase':phase,'argv':cmd,'admission':resource,
            'exit_code':proc.returncode,'elapsed_s':elapsed,
            'stdout_sha256':sha(proc.stdout),'stderr_sha256':sha(proc.stderr),
            'stdout_bytes':len(proc.stdout),'stderr_bytes':len(proc.stderr),
            'artifact_sha256':sha(artifact_data) if artifact_data is not None else None,
            'artifact_bytes':len(artifact_data) if artifact_data is not None else None}

def main():
    from argparse import ArgumentParser
    parser=ArgumentParser();parser.add_argument('--role',choices=('old','new'))
    args=parser.parse_args()
    roles=(args.role,) if args.role else ('old','new')
    path=ROOT/'results.json'
    result=json.loads(path.read_text()) if path.exists() else {'schema':1,'fixtures':{},'tools':{},'cells':[]}
    for variant in VARIANTS:
        result['fixtures'][variant]=sha((ROOT/'fixture'/f'{variant}-local.rs').read_bytes())
    for role in roles:
        exe=BINS[role]
        result['tools'][role]={'executable':str(exe),'sha256':sha(exe.read_bytes()),
                               'version_verbose':subprocess.check_output([str(exe),'-Vv'],text=True)}
        for variant in VARIANTS:
            for phase in (('hir',) if variant=='original' else ('hir','metadata')):
                if any(c['role']==role and c['variant']==variant and c['phase']==phase for c in result['cells']):
                    continue
                cell=run(role,variant,phase)
                result['cells'].append(cell)
                path.write_text(json.dumps(result,indent=2)+'\n')
                print(role,variant,phase,cell['exit_code'],cell['stdout_bytes'],cell['stderr_bytes'],flush=True)

if __name__=='__main__':main()
