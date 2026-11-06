"""Check packaged receipts; optionally requery the omitted exact DB snapshot with an existing matching main DB."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, io, json, sqlite3, tarfile
P=Path(__file__).resolve().parents[1]
def digest(b):return hashlib.sha256(b).hexdigest()
def j(n):return json.loads((P/n).read_text())
def safe_members(tf):
 seen=set()
 for m in tf:
  q=PurePosixPath(m.name)
  if q.is_absolute() or '..' in q.parts or m.name in seen or not(m.isfile() or m.isdir()):raise ValueError('unsafe tar member')
  seen.add(m.name);yield m

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--store-db-tar',type=Path);ap.add_argument('--sqlite-main',type=Path);args=ap.parse_args()
 allfiles=j('package-manifest.json')['files']
 assert sorted(x['path'] for x in allfiles)==sorted(str(f.relative_to(P)) for f in P.rglob('*') if f.is_file() and f.name!='package-manifest.json')
 for row in allfiles:
  b=(P/row['path']).read_bytes();assert len(b)==row['bytes'] and digest(b)==row['sha256']
 archives={}
 for name,expected in j('support/archive-members.json').items():
  with tarfile.open(P/'support'/name) as tf:
   data={m.name:tf.extractfile(m).read() for m in safe_members(tf) if m.isfile()}
  assert sorted(data)==sorted(x['path'] for x in expected)
  for x in expected:assert len(data[x['path']])==x['bytes'] and digest(data[x['path']])==x['sha256']
  archives[name]=data
 build=archives['build-receipts.tar.gz'];phase=json.loads(build['build-phase.json'])
 assert phase['status']==1 and len(phase['targets'])==18
 for name,b in build.items():
  if name.endswith('.json'):
   rec=json.loads(b)
   for stream in ['stdout','stderr']:
    if isinstance(rec.get(stream),dict):
     raw=build[name[:-5]+'.'+stream] if name!='build-phase.json' else build['build.'+stream]
     assert len(raw)==rec[stream]['bytes'] and digest(raw)==rec[stream]['sha256']
 assert build['build.stdout']==b'' and b'home directory' in build['build.stderr']
 config=json.loads(build['effective-build-config.stdout'])
 for k,want in j('support/config-facts.json').items():assert config[k]['value']==want
 attrs=j('support/target-18-attrs.json');census=j('support/target-output-census.json')
 assert len(attrs)==18 and len(census)==19 and sum(x['registered'] for x in census)==1
 assert {x['drv']+'^*' for x in attrs}==set(phase['targets'])
 for d in attrs:
  assert d['system']=='aarch64-linux' and not d['builder'].startswith('builtin:')
  assert not d['attrs']['__noChroot'] and d['attrs']['HOME'] is None
  for oid,out in d['outputs'].items():
   path=out['path'] if out['path'].startswith('/nix/store/') else '/nix/store/'+out['path']
   rows=[r for r in census if r['drv']==d['drv'] and r['output']==oid];assert len(rows)==1 and rows[0]['path']==path
 registered=next(x for x in census if x['registered']);assert registered['name']=='easycrypt-2026.09'
 assert registered['validpath']['deriver']==registered['drv'] and registered['validpath']['narSize']==57956152
 for x in j('support/nix-source-manifest.json'):
  b=(P/'support/nix-source'/x['path']).read_bytes()
  assert len(b)==x['bytes'] and digest(b)==x['sha256']
  assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['sha']
 assert digest((P/'support/nix-source/COPYING').read_bytes())=='20e50fe7aae3e56378ebf0417d9de904f55a0e61e4df315333e632a4d3555d95'
 stopped=archives['stopped-readback-records.tar.gz'];home=stopped['parent/jasmin-home.tar']
 assert digest(home)=='831ca5a8c240ae07c85147e43377c0789b673a09f1d73bf44640577c72f54856'
 with tarfile.open(fileobj=io.BytesIO(home)) as tf:
  rows=list(safe_members(tf));assert len(rows)==11 and all(m.isdir() and m.uid==m.gid==0 and m.mode==0o755 for m in rows)
 assert set(m.name for m in rows)==set(x['name'] for x in j('support/archive-censuses.json')['jasmin-home'])
 optional='not requested; compact query results are preserved historical evidence'
 if args.store_db_tar:
  raw=args.store_db_tar.read_bytes();assert len(raw)==10462208 and digest(raw)=='7e3667920dc4efa75bc012a4aa0884da85bb927465e10ef2880a2e0360555034'
  with tarfile.open(fileobj=io.BytesIO(raw)) as tf:
   data={m.name:tf.extractfile(m).read() for m in safe_members(tf) if m.isfile()}
  assert data['db/db.sqlite-wal']==b''
  assert args.sqlite_main is not None, '--sqlite-main requires the existing extracted matching main DB; no extraction is performed'
  original=args.sqlite_main.read_bytes();assert original==data['db/db.sqlite']
  conn=sqlite3.connect(args.sqlite_main.resolve().as_uri()+'?mode=ro&immutable=1',uri=True);conn.row_factory=sqlite3.Row;conn.execute('PRAGMA query_only=ON')
  assert conn.execute('PRAGMA integrity_check').fetchone()[0]=='ok'
  for x in census:
   actual=[dict(r) for r in conn.execute('SELECT * FROM ValidPaths WHERE path=?',(x['path'],))]
   assert actual==([x['validpath']] if x['registered'] else [])
   drv=[dict(r) for r in conn.execute('SELECT * FROM ValidPaths WHERE path=?',(x['drv'],))];assert drv==[x['drv_validpath']]
   mappings=[dict(r) for r in conn.execute('SELECT id,path FROM DerivationOutputs WHERE drv=? ORDER BY id',(drv[0]['id'],))];assert mappings==x['derivation_output_mappings']
   refs=[r[0] for r in conn.execute('SELECT v.path FROM Refs r JOIN ValidPaths v ON v.id=r.reference WHERE r.referrer=? ORDER BY v.path',(actual[0]['id'],))] if actual else []
   assert refs==x['references']
  conn.close();assert args.sqlite_main.read_bytes()==original
  optional='exact snapshot hash, byte-matched main DB, integrity and all19 output/drv/mapping/ref results rechecked read-only'
 print(json.dumps({'package_manifest':'PASS','archives':{n:len(v) for n,v in archives.items()},'receipts_and_sources':'PASS','target_derivations':18,'output_paths':19,'registered':1,'absent':18,'optional_db_requery':optional},indent=2))
if __name__=='__main__':main()
