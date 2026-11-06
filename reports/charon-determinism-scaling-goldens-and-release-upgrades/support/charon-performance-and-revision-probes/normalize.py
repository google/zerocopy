#!/usr/bin/env python3
import hashlib,json,pathlib
R=pathlib.Path(__file__).resolve().parent
files=[R/'nightly-2026.06.02/baseline.llbc',R/'nightly-2026.06.03/baseline.llbc']
def canonicalize(p):
 x=json.loads(p.read_text())
 t=x['translated']
 t['options']['dest_file']='<OUTPUT>'
 for k in ('item_names','short_names','assoc_item_names'):
  if k in t:
   t[k]=sorted(t[k],key=lambda e:json.dumps(e.get('key'),sort_keys=True,separators=(',',':')))
 return x
out=[]
for i,p in enumerate(files):
 x=canonicalize(p); target=R/f'normalized-{i+1}.json'; b=(json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode();target.write_bytes(b);out.append((target,hashlib.sha256(b).hexdigest()))
print(json.dumps({'files':[{'path':str(p),'canonical_sha256':h} for p,h in out],'equal':out[0][1]==out[1][1]},indent=2))
if out[0][1]!=out[1][1]:
 import difflib
 a=json.loads(out[0][0].read_text());b=json.loads(out[1][0].read_text())
 print('\nTop-level keys differ:',set(a)^set(b))
 for k in a:
  if a.get(k)!=b.get(k): print('DIFFERENT:',k)
