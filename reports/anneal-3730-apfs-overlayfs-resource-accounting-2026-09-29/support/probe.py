#!/usr/bin/env python3
"""Bounded APFS versus cached Ubuntu overlayfs file-accounting probe."""
import argparse,hashlib,json,os,pwd,re,shutil,subprocess,time,uuid
from pathlib import Path

HERE=Path(__file__).resolve().parent;FIX=HERE/'fixture';OUT=HERE/'results.json'
DOCKER=Path('/usr/local/bin/docker');IMAGE='ubuntu:24.04';BLOB_COUNT=8;BLOB_SIZE=256*1024
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def run(argv,cwd=None,timeout=20):
 env=dict(os.environ);env.setdefault('HOME',pwd.getpwuid(os.getuid()).pw_dir)
 t=time.monotonic();p=subprocess.run([str(x) for x in argv],cwd=cwd,env=env,capture_output=True,text=True,timeout=timeout)
 return {'argv':[str(x) for x in argv],'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'seconds':round(time.monotonic()-t,3)}
def ledger(root):
 files=[]
 for p in sorted(root.rglob('*')):
  if not p.is_file():continue
  s=p.stat();files.append({'path':str(p.relative_to(root)),'bytes':s.st_size,'blocks_512':s.st_blocks,
                           'device':s.st_dev,'inode':s.st_ino,'links':s.st_nlink,'sha256':sha(p)})
 v=os.statvfs(root)
 return {'files':files,'file_count':len(files),'logical_bytes':sum(f['bytes'] for f in files),
         'allocated_file_bytes':sum(f['blocks_512']*512 for f in files),
         'distinct_inode_count':len({(f['device'],f['inode']) for f in files}),
         'volume_available_bytes':v.f_bavail*v.f_frsize}
def linux_ledger(cid,root,records):
 argv=[DOCKER,'exec',cid,'find',root,'-type','f','-printf','%P\t%s\t%b\t%i\t%n\t%D\n']
 r=run(argv);records.append(r);assert r['exit']==0,r
 files=[]
 for line in r['stdout'].splitlines():
  rel,size,blocks,inode,links,dev=line.split('\t')
  files.append({'path':rel,'bytes':int(size),'blocks_512':int(blocks),'inode':int(inode),'links':int(links),'device':int(dev)})
 du=run([DOCKER,'exec',cid,'du','-s','-B1',root]);records.append(du);assert du['exit']==0
 df=run([DOCKER,'exec',cid,'df','-B1',root]);records.append(df);assert df['exit']==0
 size=run([DOCKER,'inspect','--size','--format','{{.SizeRw}}',cid]);records.append(size);assert size['exit']==0
 return {'files':files,'file_count':len(files),'logical_bytes':sum(f['bytes'] for f in files),
         'allocated_file_bytes':sum(f['blocks_512']*512 for f in files),
         'distinct_inode_count':len({(f['device'],f['inode']) for f in files}),
         'du_bytes':int(du['stdout'].split()[0]),'df_text':df['stdout'],'docker_size_rw_bytes':int(size['stdout'].strip())}
def write_fixture(base):
 (base/'cache').mkdir(parents=True)
 for name in ('Dep.olean','Plugin.olean'):shutil.copyfile(FIX/name,base/name)
 for i in range(BLOB_COUNT):
  (base/'cache'/f'unit-{i:02d}.bin').write_bytes(hashlib.shake_256(f'anneal-r40-{i}'.encode()).digest(BLOB_SIZE))
 (base/'project').mkdir();(base/'project'/'Proof.lean').write_text('import Dep\ntheorem ok : True := by trivial\n')
def clone_apfs(src,dst,records):
 for p in sorted(src.rglob('*')):
  rel=p.relative_to(src);q=dst/rel
  if p.is_dir():q.mkdir(parents=True,exist_ok=True)
  elif p.is_file():
   q.parent.mkdir(parents=True,exist_ok=True)
   r=run(['/bin/cp','-c',p,q]);records.append(r);assert r['exit']==0,r
def find_file(led,rel):return next(f for f in led['files'] if f['path']==rel)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);args=ap.parse_args();work=args.work.resolve()
 assert not work.exists() and shutil.disk_usage(work.parent).free>=15*(1<<30)
 work.mkdir();records=[]
 assert work.stat().st_dev==Path('/System/Volumes/Data').stat().st_dev
 fs=run(['/usr/sbin/diskutil','info','/System/Volumes/Data']);records.append(fs);assert fs['exit']==0 and 'APFS' in fs['stdout']
 apfs={};base=work/'apfs'/'base';base.mkdir(parents=True)
 apfs['empty']=ledger(work/'apfs')
 write_fixture(base);apfs['base']=ledger(work/'apfs')
 assert apfs['base']['file_count']==BLOB_COUNT+3
 full=work/'apfs'/'full';shutil.copytree(base,full);apfs['full_copy']=ledger(work/'apfs')
 clone=work/'apfs'/'clone';clone_apfs(base,clone,records);apfs['clone_copy']=ledger(work/'apfs')
 hard=work/'apfs'/'read_only_link';hard.mkdir();os.link(base/'Dep.olean',hard/'Dep.olean');apfs['hardlink']=ledger(work/'apfs')
 base_hash=sha(base/'cache/unit-00.bin')
 with (clone/'cache/unit-00.bin').open('r+b') as f:f.write(b'\0'*4096)
 assert sha(base/'cache/unit-00.bin')==base_hash and sha(clone/'cache/unit-00.bin')!=base_hash
 apfs['clone_mutated']=ledger(work/'apfs')
 apfs['baseline_blob_sha256']=base_hash
 # Only the cached image is used; the container has no network or host bind mount.
 image=run([DOCKER,'image','inspect',IMAGE,'--format','{{.Id}} {{.Os}} {{.Architecture}}']);records.append(image)
 info=run([DOCKER,'info','--format','{{.Driver}} {{.Architecture}} {{.MemTotal}}']);records.append(info)
 assert image['exit']==info['exit']==0
 cid='anneal-r40-'+uuid.uuid4().hex[:10]
 start=run([DOCKER,'run','-d','--rm','--pull=never','--network=none','--platform','linux/amd64',
            '--memory=512m','--cpus=1','--name',cid,IMAGE,'sleep','120']);records.append(start);assert start['exit']==0,start
 overlay={};mounted=False
 try:
  def dx(*args):
   r=run([DOCKER,'exec',cid,*args]);records.append(r);return r
  overlay['filesystem']=dx('stat','-f','-c','%T','/tmp')['stdout'].strip()
  assert overlay['filesystem']=='overlayfs',overlay['filesystem']
  assert dx('mkdir','-p','/tmp/account')['exit']==0
  overlay['empty']=linux_ledger(cid,'/tmp/account',records)
  copied=run([DOCKER,'cp',base,f'{cid}:/tmp/account/base']);records.append(copied);assert copied['exit']==0,copied
  overlay['base']=linux_ledger(cid,'/tmp/account',records)
  assert dx('cp','-a','/tmp/account/base','/tmp/account/full')['exit']==0
  overlay['full_copy']=linux_ledger(cid,'/tmp/account',records)
  reflink=dx('cp','-a','--reflink=always','/tmp/account/base','/tmp/account/clone')
  overlay['reflink_attempt']={'exit':reflink['exit'],'stderr':reflink['stderr']}
  if reflink['exit']==0:
   overlay['clone_copy']=linux_ledger(cid,'/tmp/account',records)
   mutate_path='/tmp/account/clone/cache/unit-00.bin';mutate_kind='reflink'
  else:
   # Partial cp trees are removed before the hardlink/ordinary-copy fallback.
   assert dx('rm','-rf','/tmp/account/clone')['exit']==0
   assert dx('cp','-a','/tmp/account/base','/tmp/account/clone')['exit']==0
   overlay['clone_copy']=linux_ledger(cid,'/tmp/account',records)
   mutate_path='/tmp/account/clone/cache/unit-00.bin';mutate_kind='ordinary-copy-fallback'
  assert dx('mkdir','-p','/tmp/account/read_only_link')['exit']==0
  assert dx('ln','/tmp/account/base/Dep.olean','/tmp/account/read_only_link/Dep.olean')['exit']==0
  overlay['hardlink']=linux_ledger(cid,'/tmp/account',records)
  before_hash=dx('sha256sum','/tmp/account/base/cache/unit-00.bin',mutate_path)
  assert before_hash['exit']==0
  mutated=dx('dd','if=/dev/zero',f'of={mutate_path}','bs=4096','count=1','conv=notrunc')
  assert mutated['exit']==0
  after_hash=dx('sha256sum','/tmp/account/base/cache/unit-00.bin',mutate_path)
  assert after_hash['exit']==0
  overlay['clone_mutated']=linux_ledger(cid,'/tmp/account',records)
  overlay['mutation']={'kind':mutate_kind,'before_sha256sum':before_hash['stdout'],'after_sha256sum':after_hash['stdout']}
  assert before_hash['stdout'].splitlines()[0].split()[0]==after_hash['stdout'].splitlines()[0].split()[0]
  assert after_hash['stdout'].splitlines()[0].split()[0]!=after_hash['stdout'].splitlines()[1].split()[0]
 finally:
  removed=run([DOCKER,'rm','-f',cid]);records.append(removed)
  assert removed['exit']==0,removed
 result={'fixture_sha256':{p.name:sha(p) for p in FIX.iterdir() if p.is_file()},
         'fixture_blob_count':BLOB_COUNT,'fixture_blob_bytes':BLOB_SIZE,
         'host':{'diskutil_apfs':re.search(r'Type \(Bundle\):\s*(\w+)',fs['stdout']).group(1) if re.search(r'Type \(Bundle\):\s*(\w+)',fs['stdout']) else 'APFS',
                 'apfs':apfs},'container':{'image':image['stdout'].strip(),'docker_info':info['stdout'].strip(),
                 'platform':'linux/amd64','limits':{'memory':'512m','cpus':'1','network':'none','pull':'never'},'overlayfs':overlay},
         'commands':records}
 raw=json.dumps(result,indent=2,ensure_ascii=False).replace(str(work),'$WORK').replace(cid,'$CONTAINER')
 OUT.write_text(raw+'\n')
 print(json.dumps({'apfs':{k:{'logical':v['logical_bytes'],'allocated':v['allocated_file_bytes'],
  'available':v['volume_available_bytes']} for k,v in apfs.items() if isinstance(v,dict) and 'logical_bytes' in v},
  'overlayfs':{k:{'logical':v['logical_bytes'],'allocated':v['allocated_file_bytes'],
   'size_rw':v['docker_size_rw_bytes']} for k,v in overlay.items() if isinstance(v,dict) and 'logical_bytes' in v},
  'reflink':overlay['reflink_attempt']},indent=2))
if __name__=='__main__':main()
