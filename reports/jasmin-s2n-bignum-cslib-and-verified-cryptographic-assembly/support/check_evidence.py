"""Host-only consistency replay of preserved data; no native tools or writes.
Authored during packaging; not the original native acquisition driver.
"""
from pathlib import Path
import json,tarfile,hashlib,re,copy
P=Path(__file__).resolve().parent

def read(phase,name):
 with tarfile.open(P/'support'/(phase+'-receipts.tar.gz')) as t:return t.extractfile(phase+'/'+name).read()
def load(phase,name):return json.loads(read(phase,name))
def same_identity(a,b):return all(a[k]==b[k] for k in ['narHash','narSize','references'])
def record_ok(a,b,prior):
 if not same_identity(a,b):return False
 if prior is not None:return a==prior and str(a.get('ca','')).startswith('fixed:r:sha256:')
 return any(s.startswith('cache.nixos.org-1:') and s in b['signatures'] for s in a['signatures'])
if __name__=='__main__':
 e='native-eval-gate';c='cache-acquisition';q='coqword-data-gate'
 raw=read(e,'cache-fetch-191.json');assert hashlib.sha256(raw).hexdigest()=='94f52a3b0ad9038c84cac5397d2f1b6455c9234cd88098e9cf7943f76dbe2dff'
 paths=json.loads(raw)['paths'];assert len(paths)==len(set(paths))==191
 for stem in ['parse','instantiate','derivations','dry-run']:
  r=load(e,stem+'.json');assert r['status']==0
  for s in ['stdout','stderr']:assert hashlib.sha256(read(e,stem+'.'+s)).hexdigest()==r['streams'][s]['sha256']
 drvs=load(e,'derivations.stdout');assert drvs['version']==4 and len(drvs['derivations'])==1485
 assert {x['system'] for x in drvs['derivations'].values()}=={'aarch64-linux','builtin'}
 before=load(c,'store-before.stdout');after=load(c,'store-after.stdout');remote=load(c,'selected-cache-metadata.json');closure=remote['closures']['https://cache.nixos.org']
 assert set(after)-set(before)==set(paths) and set(before)<=set(after) and len(closure)==205
 assert len(set(closure)&set(before))==14
 for path in closure:assert record_ok(after[path],closure[path],before.get(path))
 new=paths[0];old=next(x for x in closure if x in before)
 controls={'signed_new':record_ok(after[new],closure[new],None),'unsigned_new_rejected':not record_ok({**after[new],'signatures':[]},closure[new],None),'existing_CA':record_ok(after[old],closure[old],before[old]),'changed_existing_rejected':not record_ok({**after[old],'narHash':'wrong'},closure[old],before[old])}
 assert all(controls.values())
 assert sum(after[x]['narSize'] for x in paths)==3168388760
 r=load(q,'full-content-signature-verify.json');assert r['status']==0 and '--offline' in r['argv'] and '--no-contents' not in r['argv'] and '--repair' not in r['argv']
 assert {x for x in r['argv'] if x.startswith('/nix/store/') and x in paths}==set(paths)
 src='/nix/store/bvl5ajwrawal0hq40hdh2q3vwvbi0lpq-source';expected='sha256-TdjMp/4Eo9uEcUWhV3OSy/eX1GzQO2nhym3MNTzNvwY='
 assert load(q,'coqword-prefetch.json')['status']==0 and load(q,'coqword-prefetch.stdout')=={'hash':expected,'storePath':src}
 assert read(q,'coqword-nar-rehash.stdout').decode().strip()==expected and load(q,'coqword-nar-rehash.json')['status']==0
 before2=load(q,'store-before.stdout');after2=load(q,'store-after.stdout');assert before2==after and set(after2)-set(before2)=={src} and set(before2)<=set(after2)
 assert after2[src]['narHash']==expected and after2[src]['narSize']==85112 and after2[src]['references']==[]
 probe='offline-probe'
 pr=load(probe,'probe-build.json');assert pr['status']==0 and '--offline' in pr['argv'] and '--no-link' in pr['argv']
 ai=pr['argv'].index('--option');assert pr['argv'][ai+1:ai+3]==['max-jobs','1'] and pr['argv'].count('--option')==1
 assert next(v for v in pr['argv'] if v.startswith('NIX_CONFIG='))=='NIX_CONFIG='+(P/'support/evaluation-policy.txt').read_text()
 ni=load(probe,'offline-inspect.stdout')[0];assert ni['NetworkSettings']['Networks']=={} and ni['HostConfig']['NetworkMode']=='bridge'
 assert ni['HostConfig']['CapDrop']==['ALL'] and 'no-new-privileges' in ni['HostConfig']['SecurityOpt']
 output=read(probe,'probe-output.stdout');assert output==b'anneal-owned-probe\n' and hashlib.sha256(output).hexdigest()=='ec2420b37aa9a5c9f66acba9f5488c9c403a96962e9a2736017a1c6599fc7b6a'
 assert load(probe,'probe-output.json')['status']==0
 for stem in ['probe-build','offline-inspect','disconnect-bridge']:
  rec=load(probe,stem+'.json');assert rec['status']==0
  for stream in ['stdout','stderr']:assert hashlib.sha256(read(probe,stem+'.'+stream)).hexdigest()==rec[stream]['sha256']
 print(json.dumps({'status':'PASS','evaluated_derivations':1485,'new_signed_cache_paths':191,'reference_closure':205,'unchanged_preexisting_CA_records':14,'only_new_source':src,'separate_owned_offline_probe':{'status':0,'network':'detached; HostConfig remains bridge','max_jobs_override':1,'output_bytes':19},'typed_signature_controls':controls,'scope':'host data/receipt consistency; trusts the preserved native executable observations'},indent=2))
