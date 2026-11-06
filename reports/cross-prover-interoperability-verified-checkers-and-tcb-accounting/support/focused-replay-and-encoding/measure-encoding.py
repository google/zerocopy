#!/usr/bin/env python3
"""Lexical source-size specimen; not an MM0 compiler or semantic proof audit."""
from pathlib import Path
import argparse,hashlib,json,re
HERE=Path(__file__).resolve().parent
args=argparse.ArgumentParser();args.add_argument('--source-dir',type=Path,default=HERE.parent/'sources');args.add_argument('--output',type=Path,default=HERE/'encoding-costs.json');options=args.parse_args()
SOURCES=options.source_dir
def row(name):
 p=SOURCES/('mm0-'+name);b=p.read_bytes();t=b.decode();clean='\n'.join(line.split('--',1)[0] for line in t.splitlines())
 decls=list(re.finditer(r'(?m)^(?:@[A-Za-z0-9_-]+\s+)*(?:(?:pub|local)\s+)*(theorem|def|axiom|term|sort)\s+([A-Za-z_][A-Za-z_0-9]*)',clean))
 counts={k:sum(m[1]==k for m in decls) for k in ['theorem','def','axiom','term','sort']}
 return {'path':'examples/'+name if name.endswith(('.mm0','.mm1')) else 'mm0-c/'+name,'bytes':len(b),'lines':len(t.splitlines()),'sha256':hashlib.sha256(b).hexdigest(),'lexical_declaration_heads':counts,'imports':re.findall(r'(?m)^import "([^"]+)";',clean),'source_sorry_uses':len(re.findall(r"'sorry\b",clean))},t
closure=[];seen=set()
def visit(name):
 if name in seen:return
 seen.add(name);r,t=row(name);closure.append(r)
 for dep in r['imports']:visit(dep)
visit('separation_logic.mm1')
r,text=row('separation_logic.mm1')
heads=list(re.finditer(r'(?m)^(?:@[A-Za-z0-9_-]+\s+)*(?:(?:pub|local)\s+)*(?:theorem|def|axiom|term|sort)\s+([A-Za-z_][A-Za-z_0-9]*)',text))
selected=[]
for name in ['heap_join_ass','s_sep','s_sepcom','s_sepass','s_sepim1','s_wand','s_wand_mp','s_Sep','cbvs_Seps','s_Sep_un']:
 i=next(i for i,m in enumerate(heads) if m[1]==name);start=heads[i].start();end=heads[i+1].start() if i+1<len(heads) else len(text);body=text[start:end]
 selected.append({'symbol':name,'start_line':text[:start].count('\n')+1,'end_line':text[:end].count('\n'),'bytes_in_declaration_region':len(body.encode()),'non_whitespace_tokens':len(body.split()),'sha256':hashlib.sha256(body.encode()).hexdigest()})
extra=[row(n)[0] for n in ['hol.mm0','hol.mm1','hello_mmc.mm0','hello_mmc.mm1','compiler.mm0','verifier.c']]
result={'revision':'0d414c0bfdaaeb7fea571895127abc1fa5a3d956','method':'Byte/line counts and lexical declaration heads from pinned source. Regions extend to the next lexical declaration head; notation/comments may be included. No elaboration, binary proof generation, timing, transitive axiom closure or theorem verification.','separation_library':r,'selected_regions':selected,'actual_mm1_import_closure':closure,'closure_source_bytes':sum(r['bytes'] for r in closure),'other_specimens':extra,'scope':'Source-derived encoding/library burden. Compiler/separation import path exposes unrestricted sorry; this is not a completed admission-free compiler proof or an Iris port benchmark.'}
options.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'library':r,'selected_regions':selected,'closure_files':len(closure),'closure_bytes':result['closure_source_bytes'],'other_bytes':{r['path']:r['bytes'] for r in extra}},indent=2))
