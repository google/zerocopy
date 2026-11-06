#!/usr/bin/env python3
"""Reproduce R37 same-path warm Charon LLBC rewrites and localize byte changes."""
import argparse,difflib,hashlib,json,os,re,shutil,subprocess,time
from pathlib import Path

HERE=Path(__file__).resolve().parent;FIX=HERE/'fixture';OUT=HERE/'results.json';ART=HERE/'artifacts';DIFF=HERE/'diffs'
TOOLS=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
CHARON=TOOLS/'bin/charon';BIN=TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin';CARGO=BIN/'cargo'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def tree(root):return {str(p.relative_to(root)):sha(p) for p in sorted(root.rglob('*')) if p.is_file() and 'target' not in p.parts and p.name!='probe.llbc'}
def changes(a,b,path='$',limit=10000):
 out=[]
 def walk(x,y,p):
  if len(out)>=limit:return
  if type(x)!=type(y):out.append({'path':p,'before':x,'after':y});return
  if isinstance(x,dict):
   for k in sorted(set(x)|set(y)):
    if k not in x or k not in y:out.append({'path':p+'.'+k,'before':x.get(k),'after':y.get(k)})
    else:walk(x[k],y[k],p+'.'+k)
  elif isinstance(x,list):
   if len(x)!=len(y):out.append({'path':p+'.length','before':len(x),'after':len(y)})
   for i in range(min(len(x),len(y))):walk(x[i],y[i],p+f'[{i}]')
  elif x!=y:out.append({'path':p,'before':x,'after':y})
 walk(a,b,path);return out
def common_prefix(a,b):
 n=0
 for x,y in zip(a,b):
  if x!=y:break
  n+=1
 return n
def norm(s,work):return s.replace(str(work),'$WORK').replace(str(TOOLS),'$TOOLS')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);args=ap.parse_args();work=args.work.resolve()
 assert not work.exists() and shutil.disk_usage(work.parent).free>=15*(1<<30)
 work.mkdir();root=work/'u0'/'root';shutil.copytree(FIX,work/'u0',dirs_exist_ok=True)
 ART.mkdir(exist_ok=True);DIFF.mkdir(exist_ok=True)
 for d in (ART,DIFF):
  for p in d.iterdir():
   if p.is_file():p.unlink()
 env=dict(os.environ);env.update({'RUSTUP_HOME':str(TOOLS/'rustup'),'CARGO_HOME':str(TOOLS/'cargo'),
  'CHARON_TOOLCHAIN_IS_IN_PATH':'1','CARGO_BUILD_JOBS':'1','CARGO_INCREMENTAL':'0','RAYON_NUM_THREADS':'1',
  'PATH':os.pathsep.join([str(BIN),str(TOOLS/'bin'),env.get('PATH','')])})
 source_before=tree(work/'u0')
 dest=root/'probe.llbc'
 argv=[str(CHARON),'cargo','--preset','aeneas','--dest-file',str(dest),'--','--manifest-path',
       str(root/'Cargo.toml'),'--lib','--offline','--locked','-j','1']
 rows=[]
 for i in range(1,6):
  t=time.monotonic();p=subprocess.run(argv,cwd=root,env=env,capture_output=True,text=True,timeout=40)
  assert p.returncode==0 and dest.is_file(),(i,p.stderr)
  snap=ART/f'run-{i}.llbc';shutil.copyfile(dest,snap)
  raw=dest.read_bytes();doc=json.loads(raw)
  rows.append({'run':i,'exit':p.returncode,'elapsed_seconds':round(time.monotonic()-t,4),
    'stdout':norm(p.stdout,work),'stderr':norm(p.stderr,work),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),
    'mtime_ns':dest.stat().st_mtime_ns,'json_top_level_keys':sorted(doc),'has_errors':doc.get('has_errors'),
    'crate_name':doc.get('translated',{}).get('crate_name')})
  time.sleep(.06)
 source_after=tree(work/'u0');assert source_before==source_after
 base=(ART/'run-1.llbc').read_bytes();segment_start=base.index(b'"short_names":')
 segment_end=base.index(b',"type_decls":',segment_start)
 prefix=base[:segment_start];suffix=base[segment_end:]
 orders=[];canonical_hashes=[]
 for i in range(1,6):
  raw=(ART/f'run-{i}.llbc').read_bytes();doc=json.loads(raw)
  assert len(raw)==len(base) and raw[:segment_start]==prefix and raw[segment_end:]==suffix
  names=doc['translated']['short_names'];orders.append([entry['key']['Fun'] for entry in names])
  canonical_field=b'"short_names":'+json.dumps(sorted(names,key=lambda x:x['key']['Fun']),separators=(',',':')).encode()
  canonical_hashes.append(hashlib.sha256(prefix+canonical_field+suffix).hexdigest())
 assert len(set(canonical_hashes))==1
 (ART/'canonical-sorted-short-names.llbc').write_bytes(prefix+canonical_field+suffix)
 comparisons=[]
 for i in range(1,5):
  p=ART/f'run-{i}.llbc';q=ART/f'run-{i+1}.llbc';a=p.read_bytes();b=q.read_bytes()
  aj=json.loads(a);bj=json.loads(b);delta=changes(aj,bj)
  assert all(d['path'].startswith('$.translated.short_names[') for d in delta)
  diff=''.join(difflib.unified_diff([a[segment_start:segment_end].decode()+'\n'],
                                    [b[segment_start:segment_end].decode()+'\n'],
                                    fromfile=f'run-{i}:short_names',tofile=f'run-{i+1}:short_names'))
  (DIFF/f'run-{i}-to-{i+1}.diff').write_text(diff)
  comparisons.append({'from':i,'to':i+1,'same_bytes':a==b,'same_parsed_json':aj==bj,
      'first_different_byte_offset':None if a==b else common_prefix(a,b),
      'changed_byte_count_by_position':sum(x!=y for x,y in zip(a,b))+abs(len(a)-len(b)),
      'json_changed_leaf_count':len(delta),'json_changed_leaves':delta,
      'diff_sha256':sha(DIFF/f'run-{i}-to-{i+1}.diff')})
 result={'tool_sha256':{'charon':sha(CHARON),'cargo':sha(CARGO),'rustc':sha(BIN/'rustc')},
   'source_manifest_sha256':source_before,'argv':[norm(x,work) for x in argv],
   'isolated_region':{'start_byte':segment_start,'end_byte_exclusive':segment_end,'length_bytes':segment_end-segment_start,
       'common_prefix_sha256':hashlib.sha256(prefix).hexdigest(),'common_suffix_sha256':hashlib.sha256(suffix).hexdigest(),
       'short_name_fun_id_order':orders,'canonical_sha256':canonical_hashes[0]},
   'environment':{'CARGO_BUILD_JOBS':'1','CARGO_INCREMENTAL':'0','RAYON_NUM_THREADS':'1',
                  'RUSTUP_HOME':str(TOOLS/'rustup'),'CARGO_HOME':str(TOOLS/'cargo'),
                  'CHARON_TOOLCHAIN_IS_IN_PATH':'1'},
   'runs':rows,'comparisons':comparisons,
   'artifact_sha256':{p.name:sha(p) for p in sorted(ART.iterdir()) if p.is_file()},
   'diff_sha256':{p.name:sha(p) for p in sorted(DIFF.iterdir()) if p.is_file()}}
 OUT.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
 print(json.dumps({'runs':[(r['run'],r['bytes'],r['sha256'][:12],r['mtime_ns']) for r in rows],
                   'comparisons':[(c['from'],c['to'],c['same_bytes'],c['json_changed_leaf_count']) for c in comparisons]},indent=2))
if __name__=='__main__':main()
