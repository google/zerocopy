import hashlib,json,re
from pathlib import Path

def ident(p):
    b=p.read_bytes()
    return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),
            'md5':hashlib.md5(b).hexdigest()}

def census(p):
    b=p.read_bytes();s=b.decode()
    paths=re.findall(r'^\(\* ([^\n]+) \*\)\n#1 "\1"\n',s,re.M)
    digests=[]
    pattern=r'\(\* update digest \*\)\nloaded_files := \n  let digest_bytes = \[\|([0-9; ]+)\|\] in\n  let digest = Bytes.init \(Array.length digest_bytes\) \(fun i -> Char.chr digest_bytes.\(i\)\) in\n  \("([^"]+)", Bytes.to_string digest\)::!loaded_files;;'
    for octets,name in re.findall(pattern,s):
        digests.append({'basename':name,'md5':bytes(int(x.strip()) for x in octets.split(';')).hex()})
    return {'artifact':ident(p),'inclusion_order':paths,
            'inputs':[ident(Path(x)) for x in paths],
            'digest_completion_order':digests,
            'raw_digest_update_marker_count':s.count('(* update digest *)')}

root=Path('/home/opam/anneal-cross-sources')
out=Path('/home/opam/anneal-cross-output')
result={'hol_core':census(root/'hol-light/hol_lib_inlined.ml'),
        'audit_files':[ident(p) for p in sorted((out/'audit').iterdir()) if p.is_file()],
        'chosen_generated_sources':[ident(root/'hol-light'/rel) for rel in ['pa_j.ml','update_database.ml']],
        'output_files':[ident(p) for p in sorted(out.rglob('*')) if p.is_file()]}
if (out/'selected_inlined.ml').is_file():result['selected']=census(out/'selected_inlined.ml')
print(json.dumps(result,indent=2))
