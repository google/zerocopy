#!/usr/bin/env python3
"""Compile only, preserve every command/output, and summarize per-function bodies.

No emitted object or assembly is linked or executed. No third-party script runs.
"""
import argparse, hashlib, json, os, pathlib, re, subprocess, sys

p = argparse.ArgumentParser()
p.add_argument('--clang', default='/usr/bin/clang')
p.add_argument('--out', type=pathlib.Path, required=True)
a = p.parse_args()
a.out.mkdir(parents=True, exist_ok=False)
source = pathlib.Path(__file__).with_name('atomics.c').resolve()
commands = []
def run(name, args):
    cp = subprocess.run(args, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                        timeout=60, env=dict(os.environ, TMPDIR=str(a.out.resolve())))
    (a.out/(name+'.stdout')).write_text(cp.stdout)
    (a.out/(name+'.stderr')).write_text(cp.stderr)
    commands.append(dict(name=name,argv=args,returncode=cp.returncode))
    (a.out/'commands.json').write_text(json.dumps(commands, indent=2)+'\n')
    if cp.returncode or re.search(r'Assertion.*failed|PLEASE submit a bug report|LLVM ERROR|panic', cp.stderr):
        sys.exit('Stopped on compiler failure; inspect retained command and stderr.')
    return cp.stdout
version = run('clang-version', [a.clang, '--version'])
configs = [
    ('x86_64', 'x86_64-unknown-linux-gnu', []),
    ('aarch64', 'aarch64-unknown-linux-gnu', ['-march=armv8-a', '-mno-outline-atomics']),
    ('aarch64-lse', 'aarch64-unknown-linux-gnu', ['-march=armv8.1-a+lse', '-mno-outline-atomics']),
]
summaries = {}
for label, target, flags in configs:
    base = [a.clang, '-target', target, '-std=c11', '-O2', '-Wall', '-Wextra', '-Werror',
            '-ffreestanding', '-fno-stack-protector'] + flags
    for kind, extra, ext in [('asm', [], 's'), ('ir', ['-emit-llvm'], 'll')]:
        output = a.out/(label+'.'+ext)
        run(label+'-'+kind, base+['-S']+extra+[str(source), '-o', str(output.resolve())])
    asm = (a.out/(label+'.s')).read_text()
    funcs = {}
    for m in re.finditer(r'^([A-Za-z_]\w*):[^\n]*\n(.*?)(?=^\s*\.Lfunc_end\d+:)', asm, re.M|re.S):
        body=m.group(2)
        instructions=[]
        for line in body.splitlines():
            line=line.strip()
            if not line or line.startswith(('#','//','.')) or line.endswith(':'):
                continue
            instructions.append(line)
        funcs[m.group(1)] = instructions
    summaries[label] = funcs
(a.out/'assembly-bodies.json').write_text(json.dumps(summaries,indent=2)+'\n')
files={q.name:dict(bytes=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest())
       for q in sorted(a.out.iterdir()) if q.is_file()}
(a.out/'result.json').write_text(json.dumps(dict(status='compile-only-completed',
    compiler=version.strip(),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    targets=[dict(label=x,target=y,flags=z) for x,y,z in configs],
    commands=len(commands),function_counts={k:len(v) for k,v in summaries.items()},files=files),indent=2)+'\n')
print(json.dumps(dict(status='compile-only-completed',commands=len(commands),
                      function_counts={k:len(v) for k,v in summaries.items()})))
