#!/usr/bin/env python3
"""One-shot guarded sequential same-key Lake interruption/recovery probe."""
import hashlib,json,os,re,resource,shutil,signal,subprocess,time
from pathlib import Path
P=Path(__file__).resolve().parent; W=P/'work'; F=P/'fixture'; RAW=P/'raw'
BIN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin')
LAKE=BIN/'lake'; LEAN=BIN/'lean'; TOOL='leanprover/lean4:v4.30.0-rc2'
L_SHA='9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb'
N_SHA='b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997'
R={'schema':1,'status':'prepared','runs':[],'cases':{},'admissions':[]}
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def inv(path):
 root=Path(path)
 return {str(f.relative_to(root)):{'sha256':sha(f),'size':f.stat().st_size} for f in sorted(root.rglob('*')) if f.is_file() and not f.is_symlink()}
def memory():
 txt=subprocess.check_output(['vm_stat'],text=True)
 page=int(re.search(r'page size of (\d+)',txt).group(1))
 vals={k:int(n) for k,n in re.findall(r'Pages (free|inactive|speculative):\s+(\d+)\.',txt)}
 total=int(subprocess.check_output(['sysctl','-n','hw.memsize']))
 return page*sum(vals.values())/total

def ps_group(pid):
 rows={}
 txt=subprocess.check_output(['ps','-axo','pid=,ppid=,pgid=,rss=,comm='],text=True)
 for line in txt.splitlines():
  v=line.split(None,4)
  if len(v)==5 and all(x.isdigit() for x in v[:4]):rows[int(v[0])]=(int(v[1]),int(v[2]),int(v[3]),v[4])
 return [{'pid':p,'ppid':v[0],'rss_kib':v[2],'comm':v[3]} for p,v in rows.items() if v[1]==pid]
def save(): (P/'results.json').write_text(json.dumps(R,indent=2,sort_keys=True)+'\n')
def admission(label):
 a={'label':label,'memory_fraction':memory(),'disk_free':shutil.disk_usage(P).free}
 R['admissions'].append(a);save()
 if a['memory_fraction']<=.30 or a['disk_free']<=10*1024**3:raise RuntimeError(f'{label}:fresh_admission_denied')
 return a

def run(label,cwd,cache,args,enabled=True,limit=None):
 admission(label)
 env=dict(os.environ);env.update({'ELAN_TOOLCHAIN':TOOL,'LEAN_NUM_THREADS':'1','LAKE_NO_NET':'1',
  'LAKE_CACHE_DIR':str(cache),'LAKE_ARTIFACT_CACHE':'true' if enabled else 'false',
  'HOME':str(W/'home'),'XDG_CACHE_HOME':str(W/'xdg'),'PATH':str(BIN)+os.pathsep+env.get('PATH','')})
 env.pop('LEAN_PATH',None);env.pop('PROBE_MARKER',None)
 cmd=[str(LAKE),'--keep-toolchain','--no-ansi',*args]
 before=inv(cache) if cache.exists() else {}
 def pre():
  resource.setrlimit(resource.RLIMIT_CORE,(0,0))
  if limit is not None:resource.setrlimit(resource.RLIMIT_FSIZE,(limit,limit))
 p=subprocess.Popen(cmd,cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True,preexec_fn=pre)
 t=time.monotonic();samples=[];reason=None
 while p.poll() is None:
  members=ps_group(p.pid);rss=sum(x['rss_kib'] for x in members)
  sample={'elapsed':round(time.monotonic()-t,4),'memory_fraction':memory(),'group_rss_kib':rss,
          'disk_free':shutil.disk_usage(P).free,'members':members}
  samples.append(sample)
  if sample['memory_fraction']<.20:reason='memory_below_20_percent'
  elif rss>2200*1024:reason='group_rss_over_2200_mib'
  elif sample['disk_free']<10*1024**3:reason='disk_below_10_gib'
  elif sample['elapsed']>30:reason='over_30_seconds'
  if reason:
   os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.08)
 out,err=p.communicate(timeout=5)
 RAW.mkdir(exist_ok=True);(RAW/f'{label}.stdout').write_bytes(out);(RAW/f'{label}.stderr').write_bytes(err)
 rec={'label':label,'argv':cmd,'cwd':str(cwd),'cache':str(cache),'limit':limit,'exit':p.returncode,
      'elapsed':round(time.monotonic()-t,4),'abort':reason,'stdout_sha256':hashlib.sha256(out).hexdigest(),
      'stderr_sha256':hashlib.sha256(err).hexdigest(),'cache_before':before,'cache_after':inv(cache) if cache.exists() else {},
      'resource_samples':samples,'env_overrides':{k:env.get(k) for k in ('LAKE_NO_NET','LAKE_ARTIFACT_CACHE','LAKE_CACHE_DIR','LEAN_PATH','HOME','XDG_CACHE_HOME')}}
 R['runs'].append(rec);save()
 if reason:raise RuntimeError(f'{label}:{reason}')
 return rec

def main():
 assert not W.exists() and not (P/'results.json').exists()
 assert sha(LAKE)==L_SHA and sha(LEAN)==N_SHA
 R['lake_sha256']=L_SHA;R['lean_sha256']=N_SHA;R['fixture']=inv(F)
 golden=inv(F/'golden-cache');R['golden']=golden
 exts={f.suffix[1:]:f for f in (F/'golden-cache/artifacts').iterdir()}
 assert set(exts)=={'olean','ilean','c'}
 W.mkdir();(W/'home').mkdir();(W/'xdg').mkdir();mount=W/'mount';mount.mkdir()
 for name in ('a','b'):
  shutil.copytree(F/'producer',W/name/'producer')
  shutil.copytree(F/'consumer',W/name/'consumer')
 R['status']='running';save()
 image=W/'cache.sparseimage';attached=False
 try:
  # Prebuild two private roots without artifact cache; both will later use the same cache key.
  local=W/'local-cache'
  for name in ('a','b'):
   assert run(f'prebuild-{name}',W/name/'consumer',local,['build','Dep'],enabled=False)['exit']==0
  create=subprocess.run(['/usr/bin/hdiutil','create','-size','128m','-fs','APFS','-volname','I102Scratch',
     '-type','SPARSE','-ov','-o',str(image)],capture_output=True,text=True,timeout=30)
  R['image_create']={'exit':create.returncode,'stdout':create.stdout,'stderr':create.stderr};save();assert create.returncode==0
  attach=subprocess.run(['/usr/bin/hdiutil','attach','-nobrowse','-mountpoint',str(mount),str(image)],
     capture_output=True,text=True,timeout=30)
  R['image_attach']={'exit':attach.returncode,'stdout':attach.stdout,'stderr':attach.stderr};save();assert attach.returncode==0
  attached=True;R['devices']={'work':os.stat(W).st_dev,'image':os.stat(mount).st_dev};assert R['devices']['work']!=R['devices']['image']
  # Artifact case: separate APFS volume forces Lake's binary-write fallback.
  artcache=mount/'artifact-cache';(artcache/'artifacts').mkdir(parents=True)
  target=exts['olean'];cap=target.stat().st_size//2
  for ext,f in exts.items():
   if ext!='olean':shutil.copy2(f,artcache/'artifacts'/f.name)
  first=run('artifact-interrupted-a',W/'a/consumer',artcache,['build','Dep'],limit=cap)
  partial=artcache/'artifacts'/target.name
  assert first['exit']!=0 and partial.exists() and 0<partial.stat().st_size<target.stat().st_size
  shutil.copy2(partial,P/'partial-olean.bin')
  R['cases']['artifact']={'limit':cap,'partial_size':partial.stat().st_size,'partial_sha256':sha(partial),
    'expected_size':target.stat().st_size,'expected_sha256':sha(target),'target':target.name,
    'map_after_failure':list((artcache/'outputs').rglob('*.json')) if (artcache/'outputs').exists() else []}
  R['cases']['artifact']['map_after_failure']=[str(f.relative_to(artcache)) for f in R['cases']['artifact']['map_after_failure']]
  save()
  retry=run('artifact-retry-b-present',W/'b/consumer',artcache,['build','Dep'])
  R['cases']['artifact'].update({'retry_exit':retry['exit'],'same_key_map':list((artcache/'outputs').rglob('*.json'))[0].name,
    'present_integrity':sha(partial)==sha(target),'after_retry':inv(artcache)})
  assert retry['exit']==0
  # Delete only damaged object and map; same second root republishes clean bytes.
  partial.unlink()
  for f in (artcache/'outputs').rglob('*.json'):f.unlink()
  repair=run('artifact-repair-b-deleted',W/'b/consumer',artcache,['build','Dep'])
  R['cases']['artifact'].update({'repair_exit':repair['exit'],'after_repair':inv(artcache)})
  assert repair['exit']==0 and sha(artcache/'artifacts'/target.name)==sha(target)
  # Map case: same-volume hard links succeed, 64-byte limit targets direct JSON map write.
  mapcache=W/'map-cache';first=run('map-interrupted-a',W/'a/consumer',mapcache,['build','Dep'],limit=64)
  maps=list((mapcache/'outputs').rglob('*.json'))
  assert first['exit']!=0 and len(maps)==1 and maps[0].stat().st_size==64
  shutil.copy2(maps[0],P/'partial-map.json')
  R['cases']['map']={'first_exit':first['exit'],'partial_size':64,'partial_sha256':sha(maps[0]),
    'partial_valid_json':False,'artifacts_after_failure':len(list((mapcache/'artifacts').iterdir()))};save()
  try:json.loads(maps[0].read_text());R['cases']['map']['partial_valid_json']=True
  except json.JSONDecodeError:pass
  retry=run('map-retry-b',W/'b/consumer',mapcache,['build','Dep'])
  R['cases']['map'].update({'retry_exit':retry['exit'],'after_retry':inv(mapcache),
      'valid_json_after_retry':bool(json.loads(maps[0].read_text()))})
  assert retry['exit']==0
  R['status']='completed';save()
 except Exception as exc:
  R['status']='stopped';R['error']=repr(exc);save()
 finally:
  if attached:
   det=subprocess.run(['/usr/bin/hdiutil','detach',str(mount)],capture_output=True,text=True,timeout=30)
   R['image_detach']={'exit':det.returncode,'stdout':det.stdout,'stderr':det.stderr};save()
  R['final_memory_fraction']=memory();R['final_disk_free']=shutil.disk_usage(P).free;save()
 print(json.dumps({'status':R['status'],'runs':len(R['runs']),'error':R.get('error')},sort_keys=True))
if __name__=='__main__':main()
