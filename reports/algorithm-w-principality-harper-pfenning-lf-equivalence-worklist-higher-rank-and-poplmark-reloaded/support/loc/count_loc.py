#!/usr/bin/env python3
"""Non-blank, non-comment line counts for Coq (.v), Agda (.agda), Beluga (.bel),
F* (.fst). For Coq, also split into 'proof' (between `Proof.` and `Qed.`/`Defined.`/
`Admitted.`) and 'spec' (all other lines). Counts `Admitted`/`admit`/`postulate`/
`Axiom` occurrences. Comment syntax: Coq/F*-style (* *), F* also //, Agda/Beluga
-- line and {- -} block (Beluga: % line, %{ }% block)."""
import re, sys, pathlib, collections
def strip(text, ext):
    if ext in ('.v', '.fst'):
        prev = None
        while prev != text:  # nested (* *)
            prev = text; text = re.sub(r'\(\*(?:(?!\(\*).)*?\*\)', '', text, flags=re.S)
        if ext == '.fst': text = re.sub(r'//[^\n]*', '', text)
    elif ext == '.agda':
        text = re.sub(r'\{-.*?-\}', '', text, flags=re.S); text = re.sub(r'--[^\n]*', '', text)
    elif ext == '.bel':
        text = re.sub(r'%\{.*?\}%', '', text, flags=re.S); text = re.sub(r'%[^\n]*', '', text)
    return [l for l in text.splitlines() if l.strip()]
groups = collections.OrderedDict()
for arg in sys.argv[1:]:
    root = pathlib.Path(arg)
    files = [root] if root.is_file() else sorted(p for p in root.rglob('*') if p.suffix in ('.v', '.agda', '.bel', '.fst'))
    tot = collections.Counter()
    for f in files:
        lines = strip(f.read_text(errors='replace'), f.suffix)
        tot['loc'] += len(lines); tot['files'] += 1
        joined = '\n'.join(lines)
        tot['admit'] += len(re.findall(r'\b(Admitted|admit|postulate|Axiom|assume)\b', joined))
        if f.suffix == '.v':
            inproof = False
            for l in lines:
                s = l.strip()
                if re.match(r'^Proof\b', s): inproof = True; tot['proof'] += 1; continue
                if inproof:
                    tot['proof'] += 1
                    if re.search(r'\b(Qed|Defined|Admitted)\.\s*$', s): inproof = False
                else:
                    tot['spec'] += 1
    print(f'{arg:40s} files={tot["files"]:3d} loc={tot["loc"]:6d}' + (f' spec={tot["spec"]} proof={tot["proof"]}' if tot['spec'] else '') + f' admit/postulate/axiom-tokens={tot["admit"]}')
