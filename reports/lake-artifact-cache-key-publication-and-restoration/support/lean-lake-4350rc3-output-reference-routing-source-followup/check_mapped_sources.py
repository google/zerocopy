#!/usr/bin/env python3
"""Read only the frozen claim maps and official commit-pinned raw files."""

import hashlib
import json
import os
import subprocess
from pathlib import Path
from urllib.parse import quote

HERE = Path(__file__).resolve().parent
REPO = Path(os.environ.get('REFERENCE_ROOT', '/Users/josh/Codex/Projects/zerocopy'))
REF = 'ba4556c30835b56d108b0a6854a760bccf8438c5'

TIPS = {
    'llvm/llvm-project': '1f1a5b38374af3fc5afb52d91c91c0203b5edcdf',
    'golang/tools': '3f3efb7c3b31192232c67403b23a00bfcdbc3eec',
    'rust-lang/rust-analyzer': '3332931d313fad08166571c05d7237d3a4d77ac2',
    'dotnet/roslyn': '8d2c75f24c88ea99a01a8579ecb67e303d566670',
    'rocq-community/rocq-lsp': '6ff2d0723547eb84352892cd546f87824d9a9f18',
    'haskell/haskell-language-server': '1cd039d9e3916264724071068f8eb38c5ee7fa85',
    'JetBrains/kotlin': '9b80c8ff99f3a63fcf578010bb2712697f4886aa',
    'swiftlang/sourcekit-lsp': '46d33b124af55647b8329b694373c8479ccb0a85',
    'swiftlang/swift': 'c5fe44b279ba711339330853a14be3b6516511e8',
    'microsoft/TypeScript': 'f9f8d01292562242b6e7c7142e46ed7e470926f9',
    'leanprover/lean4': '193c3589a4fc16c4059261ab38cfa365eb24f323',
    'leanprover-community/mathlib4': '302343bb9a029d4edab4f736703f0736896c1b64',
}

def frozen_json(path):
    return json.loads(subprocess.check_output(['git', '-C', str(REPO), 'show', f'{REF}:reports/{path}']))

def mapped():
    items = {}
    def add(repo, path, previous, old_sha=None):
        items[(repo, path)] = {'repo':repo, 'path':path, 'previous':previous, 'old_sha256':old_sha}
    x=frozen_json('editor-engines-current-source-review/support/official-source-observation.json')
    for repo in x['repositories']:
        for f in repo['mapped_files']:
            add(repo['repository'], f['path'], repo['selected_current_commit'], f['new']['sha256_content'])
    x=frozen_json('kotlin-swift-current-source-review/support/official-source-observation.json')
    for repo in x['repositories']:
        for f in repo['mapped_files']:
            add(repo['repository'], f['path'], repo['selected_current_commit'], f['new']['content_sha256'])
    x=frozen_json('rocq-serapi-fleche-current-source-review/support/official-source-observation.json')
    for repo in x['repositories']:
        if repo['repository'] in TIPS:
            for f in repo['files']:
                add(repo['repository'], f['path'], repo['current_commit'], f['content_sha256'])
    x=frozen_json('haskell-hls-hie-bios-current-source-review/support/official-source-observation.json')
    for repo in x['repositories']:
        if repo['repository'] in TIPS:
            for f in repo['mapped_sources']:
                add(repo['repository'], f['path'], repo['default_branch_commit'])
    x=frozen_json('roslyn-current-source-review/support/matrix.json')
    for clause in x['clauses']:
        for path in clause['mapped_paths']:
            add('dotnet/roslyn',path,x['current_main_commit'])
    for path in (
        'src/lake/Lake/Config/Cache.lean',
        'src/lake/Lake/Build/Common.lean',
        'src/lake/Lake/Load/Config.lean',
        'src/Lean/Data/Lsp/Extra.lean',
        'src/Lean/Server/FileWorker/RequestHandling.lean',
        'src/Lean/Data/Lsp/Basic.lean',
    ):
        add('leanprover/lean4', path, '5045d0056413266e57c625dcd7c365b10e377c52')
    add('leanprover-community/mathlib4','lean-toolchain','d13f23b723b8a846827a245b89c10fc7d3f11612')
    return list(items.values())

def fetch(repo, commit, path):
    url=f'https://raw.githubusercontent.com/{repo}/{commit}/{quote(path)}'
    p=subprocess.run(['curl','--fail','--silent','--show-error','--location','--max-time','25',url],capture_output=True)
    if p.returncode:
        return None, p.stderr.decode('utf-8','replace').strip(), url
    return p.stdout, None, url

def main():
    rows=[]
    for item in mapped():
        repo=item['repo']; path=item['path']; tip=TIPS[repo]
        data,error,url=fetch(repo,tip,path)
        row={**item,'tip':tip,'tip_url':url,'error':error}
        if data is not None:
            row['tip_sha256']=hashlib.sha256(data).hexdigest()
            row['tip_git_blob_sha1']=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
            row['tip_size']=len(data)
            if item['old_sha256']:
                row['same_as_previous']=row['tip_sha256']==item['old_sha256']
            else:
                old,old_error,old_url=fetch(repo,item['previous'],path)
                row['previous_url']=old_url
                row['previous_error']=old_error
                if old is not None:
                    row['previous_sha256']=hashlib.sha256(old).hexdigest()
                    row['same_as_previous']=row['previous_sha256']==row['tip_sha256']
            if row.get('same_as_previous') is False:
                dest=HERE/'raw'/repo/tip/path
                dest.parent.mkdir(parents=True,exist_ok=True)
                dest.write_bytes(data)
                row['tip_snapshot']=str(dest.relative_to(HERE))
        rows.append(row)
        print(repo,path,row.get('same_as_previous'),error or '',flush=True)
    (HERE/'mapped_source_results.json').write_text(json.dumps(rows,indent=2)+'\n')

if __name__=='__main__': main()
