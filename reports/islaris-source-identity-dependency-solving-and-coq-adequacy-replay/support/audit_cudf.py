"""Check the selected set against the retained CUDF, not the opam translator.
Only atoms with integer comparisons, CNF dependencies, conflict lists and an
install-only request are supported. Unsupported constructs fail closed.
"""
import json, pathlib, re, operator, hashlib, sys

def audit(cudf_path, native_json_path, selection_override=None):
    duplicate_keys=[]
    def pairs(xs):
        d={}
        for k,v in xs:
            if k in d:
                duplicate_keys.append({'key':k,'identical':d[k]==v})
                if d[k]!=v:raise ValueError('conflicting duplicate JSON key')
            d[k]=v
        return d
    raw=native_json_path.read_bytes()
    native=json.loads(raw,object_pairs_hook=pairs)
    if any(set(x)!= {'install'} for x in native['solution']):raise ValueError('non-install action')
    selection={(x['install']['name'],x['install']['version']) for x in native['solution']}
    if len(selection)!=len(native['solution']):raise ValueError('duplicate selection')
    if selection_override is not None: selection=set(selection_override)
    records=[];requests=[]
    for block in re.split(r'\n\s*\n',cudf_path.read_text()):
        d={};last=None
        for line in block.splitlines():
            if not line or line.startswith('#'):continue
            if line[0].isspace():
                if last is None:raise ValueError('unexpected continuation')
                d[last]+=' '+line.strip();continue
            if ':' not in line:raise ValueError('invalid CUDF line')
            k,v=line.split(':',1)
            if k in d:raise ValueError('duplicate CUDF field')
            d[k]=v.strip();last=k
        if 'package' in d:records.append(d)
        elif 'request' in d:requests.append(d)
    if len(requests)!=1:raise ValueError('request count')
    synthetic={'package':'%3dopam-invariant','version':'1','installed':'true','was-installed':'true','keep':'version','opam-name':'SWITCH_INVARIANT','opam-version':'NULL'}
    retained=[d for d in records if d.get('installed','false')!='false' or d.get('keep','none')!='none']
    if retained != [synthetic]:raise ValueError('unexpected installed/keep record; only exact observed synthetic invariant supported')
    all_keys=[(d['package'],int(d['version'])) for d in records]
    if len(set(all_keys))!=len(all_keys):raise ValueError('duplicate CUDF package identity')
    selected=[d for d in records if (d.get('opam-name'),d.get('opam-version')) in selection]
    if len(selected)!=len(selection):raise ValueError('selected identity count')
    if len({d['opam-name'] for d in selected})!=len(selected):raise ValueError('multiple selected versions')
    real_count=len(selected)
    selected=selected+[synthetic]
    if any(d.get('provides') for d in selected):raise ValueError('provides unsupported')
    selected_keys={(d['package'],int(d['version'])) for d in selected}
    ops={'=':operator.eq,'!=':operator.ne,'<':operator.lt,'>':operator.gt,'<=':operator.le,'>=':operator.ge}
    atom_rx=re.compile(r'([A-Za-z0-9+.%_-]+)(?:\s*(>=|<=|!=|=|<|>)\s*([0-9]+))?')
    atom_count=0
    def matches(atom,exclude=None):
        nonlocal atom_count
        atom_count+=1;m=atom_rx.fullmatch(atom.strip())
        if not m:raise ValueError('unsupported atom '+repr(atom))
        name,op,version=m.groups()
        return sorted((n,v) for n,v in selected_keys if (n,v)!=exclude and n==name and (op is None or ops[op](v,int(version))))
    evidence=[];dependencies=0;conflicts=0
    for d in selected:
        nv=(d['package'],int(d['version']));row={'package':d['opam-name'],'version':d['opam-version'],'cudf':list(nv),'dependency_witnesses':[],'conflicts_checked':[]}
        if d.get('depends'):
            for clause in d['depends'].split(','):
                dependencies+=1
                alternatives=[{'atom':a.strip(),'matches':matches(a)} for a in clause.split('|')]
                if not any(x['matches'] for x in alternatives):raise ValueError('unsatisfied dependency '+str(nv)+' '+clause)
                row['dependency_witnesses'].append(alternatives)
        if d.get('conflicts'):
            for atom in d['conflicts'].split(','):
                conflicts+=1
                if matches(atom,exclude=nv):raise ValueError('conflict '+str(nv)+' '+atom)
                row['conflicts_checked'].append(atom.strip())
        evidence.append(row)
    req=requests[0]
    if set(req)-{'request','install','remove','upgrade'}:raise ValueError('unsupported request field')
    if req.get('remove') or req.get('upgrade'):raise ValueError('non-install request unsupported')
    req_atoms=[x.strip() for x in req['install'].split(',')]
    if not all(matches(x) for x in req_atoms):raise ValueError('request unsatisfied')
    roots=set(native['request']['install']);selected_atoms={n+'.'+v for n,v in selection}
    if not roots<=selected_atoms:raise ValueError('exact opam root missing')
    return dict(status='PASS',role='host-side satisfaction audit of exported CUDF; not opam-to-CUDF validation, optimality or build proof',
        native_json_sha256=hashlib.sha256(raw).hexdigest(),cudf_sha256=hashlib.sha256(cudf_path.read_bytes()).hexdigest(),
        raw_json_duplicate_keys=duplicate_keys,universe_records=len(records),selected_count=real_count,exact_roots=len(roots),
        request_atoms=len(req_atoms),dependency_clauses=dependencies,conflict_atoms=conflicts,atom_evaluations=atom_count,
        initial_synthetic_invariant=synthetic,real_initial_installed_and_keep_empty=True,selected_provides_absent=True,unsupported_syntax=False,
        evidence=evidence,request=req)

if __name__=='__main__':
    if len(sys.argv)!=4:raise SystemExit('audit_cudf.py CUDF NATIVE_JSON OUTPUT')
    result=audit(pathlib.Path(sys.argv[1]),pathlib.Path(sys.argv[2]))
    pathlib.Path(sys.argv[3]).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['evidence','request']},indent=2))
