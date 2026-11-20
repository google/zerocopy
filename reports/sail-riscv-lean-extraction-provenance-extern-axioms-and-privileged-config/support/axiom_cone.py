#!/usr/bin/env python3
"""Syntactic (over-approximate) axiom-cone probe for Sail-generated Lean RISC-V models.

Builds a name-level reference graph over top-level declarations in a directory of
generated .lean files (def/abbrev/instance/theorem/axiom/inductive/structure),
then reports which `axiom` declarations are reachable from given root names.

This mimics Lean's CollectAxioms (which follows every constant syntactically
referenced in a declaration's type and value) but at the *source-token* level:
an identifier token counts as a reference if it equals the short name of any
top-level declaration.  It therefore OVER-approximates (e.g. local variables that
shadow a global name, comments, strings) and can under-approximate only for
references produced by elaboration (instances, auto-bound implicits, deriving).
Labelled `derived` evidence; not a substitute for `#print axioms` on a built env.

Usage: axiom_cone.py <dir-with-lean-files> <root1> [<root2> ...]
"""
import os, re, sys, collections

DECL_RE = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:noncomputable\s+|partial\s+|unsafe\s+)*'
                     r'(def|abbrev|instance|theorem|lemma|axiom|opaque|inductive|structure|class)\s+([^\s:({\[]+)?')
TOK_RE = re.compile(r"[A-Za-z_\u03b1-\u03c9][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*")

def load(d):
    decls = {}   # short name -> list of (kind, file, body)
    for root, _, files in os.walk(d):
        for f in sorted(files):
            if not f.endswith('.lean'):
                continue
            path = os.path.join(root, f)
            cur = None
            buf = []
            def flush():
                if cur is not None:
                    kind, name = cur
                    decls.setdefault(name, []).append((kind, path, '\n'.join(buf)))
            for line in open(path, encoding='utf-8', errors='replace'):
                line = line.rstrip('\n')
                # strip line comments
                code = re.sub(r'"(?:[^"\\]|\\.)*"', '""', line)  # drop string literals
                code = re.sub(r'--.*$', '', code)
                m = DECL_RE.match(code)
                if m and not line.startswith((' ', '\t')):
                    flush()
                    kind, name = m.group(1), m.group(2) or f'<anon@{path}>'
                    name = name.split('.')[-1]
                    cur = (kind, name)
                    buf = [code]
                elif re.match(r'^(namespace|end|section|open|set_option|import|mutual|variable|macro_rules|/--|-/)', line):
                    flush(); cur = None; buf = []
                else:
                    if cur is not None:
                        buf.append(code)
            flush()
    return decls

MODEL_NS = {'LeanRV64D','Functions','Out','RiscvZkvm','LeanRV64DExecutable','Lean_RV64D'}

def cone(decls, roots):
    names = set(decls)
    seen = set()
    stack = [r for r in roots if r in names]
    missing = [r for r in roots if r not in names]
    while stack:
        n = stack.pop()
        if n in seen:
            continue
        seen.add(n)
        for kind, path, body in decls[n]:
            for tok in TOK_RE.findall(body):
                parts = tok.split('.')
                # dotted tokens count only when qualified by a model namespace
                # (e.g. LeanRV64D.Functions.foo); `IntRange.forIn'.loop` etc. are not model refs.
                if len(parts) > 1 and not (parts[0] in MODEL_NS):
                    continue
                short = parts[-1]
                if short in names and short not in seen:
                    stack.append(short)
    axioms = sorted(n for n in seen if any(k == 'axiom' for k, _, _ in decls[n]))
    return seen, axioms, missing

if __name__ == '__main__':
    d, roots = sys.argv[1], sys.argv[2:]
    decls = load(d)
    all_axioms = sorted(n for n, v in decls.items() if any(k == 'axiom' for k, _, _ in v))
    print(f'dir={d} decl_names={len(decls)} axioms_declared={len(all_axioms)}')
    for r in roots:
        seen, axioms, missing = cone(decls, [r])
        if missing:
            print(f'ROOT {r}: NOT FOUND'); continue
        fl = [a for a in axioms if a.startswith('riscv_f') or a.startswith('riscv_i') or a.startswith('riscv_ui')]
        nonfl = [a for a in axioms if a not in fl]
        print(f'ROOT {r}: reachable_decls={len(seen)} axioms={len(axioms)} float={len(fl)} nonfloat={nonfl}')
