#!/usr/bin/env python3
"""Bounded copied-byte inventory for a tiny direct Lean project (J02)."""
import argparse
import csv
import hashlib
import json
import os
import shutil
import subprocess
from pathlib import Path

DEP = 'def depValue : Nat := 7\n'
PROOF = 'import Dep\n\ntheorem workerProof : depValue = 7 := by\n  rfl\n'
CONFIG = 'name = "tiny-worker"\nversion = "0.1.0"\n'
TOOLCHAIN = 'leanprover/lean4:v4.30.0-rc2\n'


def digest(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(data)


def byte_copy(src, dst):
    dst.parent.mkdir(parents=True, exist_ok=True)
    with open(src, 'rb') as a, open(dst, 'wb') as b:
        while chunk := a.read(1 << 20):
            b.write(chunk)


def run_lean(lean, cwd, source, dep_path=None, outputs=True):
    env = os.environ.copy()
    env['LEAN_NUM_THREADS'] = '1'
    if dep_path:
        env['LEAN_PATH'] = str(dep_path)
    cmd = [str(lean), '--json']
    if outputs:
        stem = source.stem
        cmd += ['-o', str(cwd / 'build' / (stem + '.olean')),
                '-i', str(cwd / 'build' / (stem + '.ilean')),
                '-c', str(cwd / 'build' / (stem + '.c'))]
    cmd.append(str(source))
    (cwd / 'build').mkdir(exist_ok=True)
    p = subprocess.run(cmd, cwd=cwd, env=env, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
    return {'argv': cmd, 'exit': p.returncode, 'stdout': p.stdout, 'stderr': p.stderr}


def classify(rel):
    parts = rel.parts
    if not parts:
        return 'case-root'
    if parts[0] == 'shared':
        role = parts[-1]
        if role.endswith(('.olean', '.ilean', '.c')):
            return 'shared-dependency-artifact'
        if role.endswith('.lean'):
            return 'shared-dependency-source'
        return 'shared-dependency-config-or-directory'
    if parts[0].startswith('worker-'):
        if len(parts) > 1 and parts[1] == 'deps':
            role = parts[-1]
            if role.endswith(('.olean', '.ilean', '.c')):
                return 'worker-dependency-artifact-or-link'
            if role.endswith('.lean'):
                return 'worker-dependency-source-or-link'
            return 'worker-dependency-directory-or-link'
        if len(parts) > 1 and parts[1] == 'build':
            return 'worker-private-build-product-or-directory'
        if parts[-1] == 'Proof.lean':
            return 'worker-generated-source'
        if parts[-1] in ('lakefile.toml', 'lean-toolchain', 'anneal-manifest.json'):
            return 'worker-local-config'
        if len(parts) == 1:
            return 'worker-directory'
    raise ValueError(f'unclassified entry: {rel}')


def inventory(root):
    rows = []
    paths = [root]
    for dirpath, dirs, files in os.walk(root, followlinks=False):
        dirs.sort()
        files.sort()
        for name in dirs + files:
            paths.append(Path(dirpath) / name)
    for p in paths:
        rel = p.relative_to(root)
        s = p.lstat()
        kind = 'symlink' if p.is_symlink() else ('directory' if p.is_dir() else 'file')
        rows.append({'path': str(rel) or '.', 'role': classify(rel), 'kind': kind,
                     'logical_bytes': s.st_size, 'allocated_charge_bytes': s.st_blocks * 512,
                     'device': s.st_dev, 'inode': s.st_ino, 'nlink': s.st_nlink,
                     'sha256': digest(p) if kind == 'file' else None,
                     'link_target': os.readlink(p) if kind == 'symlink' else None})
    return rows


def summarize(rows):
    files = [r for r in rows if r['kind'] == 'file']
    seen = {}
    for r in rows:
        seen[(r['device'], r['inode'])] = r
    def total(rs, field):
        return sum(r[field] for r in rs)
    copied = [r for r in files if r['role'].startswith('worker-dependency-')]
    local = [r for r in files if r['role'] in ('worker-generated-source', 'worker-local-config',
                                               'worker-private-build-product-or-directory')]
    shared = [r for r in files if r['role'].startswith('shared-dependency-')]
    worker_detail = {}
    for r in files:
        prefix = r['path'].split('/')[0]
        if prefix.startswith('worker-'):
            item = worker_detail.setdefault(prefix, {'files': 0, 'copied_dependency_files': 0,
                'copied_dependency_payload_bytes': 0, 'copied_dependency_allocated_charge_bytes': 0,
                'private_payload_bytes': 0, 'private_allocated_charge_bytes': 0})
            item['files'] += 1
            if r['role'].startswith('worker-dependency-'):
                item['copied_dependency_files'] += 1
                item['copied_dependency_payload_bytes'] += r['logical_bytes']
                item['copied_dependency_allocated_charge_bytes'] += r['allocated_charge_bytes']
            else:
                item['private_payload_bytes'] += r['logical_bytes']
                item['private_allocated_charge_bytes'] += r['allocated_charge_bytes']
    return {'entries': len(rows), 'regular_files': len(files), 'distinct_inodes': len(seen),
            'regular_payload_bytes': total(files, 'logical_bytes'),
            'regular_allocated_charge_bytes': total(files, 'allocated_charge_bytes'),
            'unique_inode_allocated_charge_bytes': total(seen.values(), 'allocated_charge_bytes'),
            'worker_copied_dependency_payload_bytes': total(copied, 'logical_bytes'),
            'worker_private_payload_bytes': total(local, 'logical_bytes'),
            'shared_payload_bytes': total(shared, 'logical_bytes'),
            'symlinks': sum(r['kind'] == 'symlink' for r in rows),
            'directories': sum(r['kind'] == 'directory' for r in rows),
            'workers': worker_detail}


def make_shared(lean, root):
    shared = root / 'shared'
    shared.mkdir(parents=True)
    write(shared / 'Dep.lean', DEP)
    write(shared / 'lean-toolchain', TOOLCHAIN)
    result = run_lean(lean, shared, shared / 'Dep.lean')
    assert result['exit'] == 0, result
    # Flatten the module artifacts for a direct LEAN_PATH import.
    for p in (shared / 'build').iterdir():
        p.rename(shared / p.name)
    (shared / 'build').rmdir()
    return shared, result


def make_worker(lean, root, idx, mode, shared):
    worker = root / f'worker-{idx}'
    worker.mkdir(parents=True)
    deps = worker / 'deps'
    if mode == 'symlink':
        deps.symlink_to(shared, target_is_directory=True)
    else:
        deps.mkdir()
        for src in sorted(shared.iterdir()):
            dst = deps / src.name
            if mode == 'copy':
                byte_copy(src, dst)
            elif mode == 'hardlink':
                os.link(src, dst)
            elif mode == 'clone':
                subprocess.run(['/bin/cp', '-c', str(src), str(dst)], check=True,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=10)
            else:
                raise ValueError(mode)
    write(worker / 'Proof.lean', PROOF)
    write(worker / 'lakefile.toml', CONFIG)
    write(worker / 'lean-toolchain', TOOLCHAIN)
    write(worker / 'anneal-manifest.json', json.dumps({'worker': idx, 'module': 'Proof',
                                                       'dependency': 'Dep'}, sort_keys=True) + '\n')
    result = run_lean(lean, worker, worker / 'Proof.lean', deps)
    assert result['exit'] == 0, result
    # Verify a fresh process can use the built import and source.
    check = run_lean(lean, worker, worker / 'Proof.lean', deps, outputs=False)
    assert check['exit'] == 0, check
    return {'build': result, 'fresh_check': check}


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--lean', type=Path, required=True)
    p.add_argument('--work', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args()
    if a.work.exists():
        raise SystemExit('work path must be absent')
    a.work.mkdir(parents=True)
    a.out.mkdir(parents=True, exist_ok=True)
    df = subprocess.run(['/bin/df', '-P', str(a.work)], text=True,
                        capture_output=True, check=True).stdout
    device = df.splitlines()[1].split()[0]
    disk_info = subprocess.run(['/usr/sbin/diskutil', 'info', device], text=True,
                               capture_output=True, check=True).stdout
    filesystem = next(x.split(':', 1)[1].strip() for x in disk_info.splitlines()
                      if x.strip().startswith('File System Personality:'))
    results = {'lean': str(a.lean), 'lean_sha256': digest(a.lean),
               'filesystem': filesystem, 'filesystem_device': device, 'df_preflight': df,
               'cases': {}}
    all_rows = []
    for case, count, mode in [('cold-1', 1, 'copy'), ('cold-2', 2, 'copy'),
                              ('warm-1', 1, 'symlink'), ('warm-2', 2, 'symlink'),
                              ('hardlink-1', 1, 'hardlink'), ('clone-1', 1, 'clone')]:
        root = a.work / case
        root.mkdir()
        shared, dep = make_shared(a.lean, root)
        workers = [make_worker(a.lean, root, i, mode, shared) for i in range(1, count + 1)]
        rows = inventory(root)
        all_rows += [dict(case=case, **r) for r in rows]
        results['cases'][case] = {'workers': count, 'mode': mode, 'dependency_build': dep,
                                  'worker_runs': workers, 'summary': summarize(rows),
                                  'dependency_hashes': {x.name: digest(x) for x in shared.iterdir()},
                                  'worker_dependency_identity': [
                                      {'worker': i, 'dep_kind': 'symlink' if (root / f'worker-{i}' / 'deps').is_symlink() else 'directory',
                                       'dep_source_inode': (root / f'worker-{i}' / 'deps' / 'Dep.lean').stat().st_ino,
                                       'shared_source_inode': (shared / 'Dep.lean').stat().st_ino}
                                      for i in range(1, count + 1)]}
    with open(a.out / 'inventory.csv', 'w', newline='') as f:
        fields = list(all_rows[0])
        w = csv.DictWriter(f, fields)
        w.writeheader()
        w.writerows(all_rows)
    (a.out / 'results.json').write_text(json.dumps(results, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: v['summary'] for k, v in results['cases'].items()}, indent=2))


if __name__ == '__main__':
    main()
