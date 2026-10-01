#!/usr/bin/env python3
"""Read default upstream HEAD refs; no repository clone or checkout writes."""
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
rows = json.loads((HERE / 'evidence/review-map-83.json').read_text())
repos = set()
for row in rows:
    for subject in row['pinned_subjects']:
        identity = subject['identity']
        for key, value in identity.items():
            if (key == 'repository' or key.endswith('_repository') or key.endswith('-repository')) and isinstance(value, str) and '/' in value and not value.startswith(('http:', 'https:')):
                repos.add(value)

def get(repo):
    cmd = (['git', 'ls-remote', 'https://fuchsia.googlesource.com/fuchsia', 'refs/heads/main']
           if repo == 'fuchsia/fuchsia' else
           ['git', 'ls-remote', 'https://llvm.googlesource.com/llvm-project', 'refs/heads/main']
           if repo == 'llvm/llvm-project' else
           ['git', 'ls-remote', f'https://github.com/{repo}.git', 'HEAD'])
    try:
        p = subprocess.run(cmd, text=True, capture_output=True, timeout=20)
        line = p.stdout.strip().splitlines()
        expected = '\trefs/heads/main' if repo in ('fuchsia/fuchsia', 'llvm/llvm-project') else '\tHEAD'
        matched = [item.split('\t')[0] for item in line if item.endswith(expected)]
        sha = matched[0] if p.returncode == 0 and len(matched) == 1 else None
        return repo, {'command': cmd, 'exit': p.returncode, 'head': sha,
                      'stderr': p.stderr.strip()[:500]}
    except subprocess.TimeoutExpired:
        return repo, {'command': cmd, 'exit': None, 'head': None, 'stderr': 'timeout after 20 seconds'}

results = {}
with ThreadPoolExecutor(max_workers=8) as pool:
    for future in as_completed([pool.submit(get, repo) for repo in sorted(repos)]):
        repo, result = future.result()
        results[repo] = result
output = {'observed_at_utc': datetime.now(timezone.utc).isoformat(),
          'repository_count': len(repos), 'refs': {k: results[k] for k in sorted(results)}}
(HERE / 'evidence/default-heads.json').write_text(json.dumps(output, indent=2, sort_keys=True) + '\n')
print(json.dumps({'repositories': len(repos), 'resolved': sum(bool(r['head']) for r in results.values()),
                  'unresolved': [k for k,v in results.items() if not v['head']]}, sort_keys=True))
