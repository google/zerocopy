from pathlib import Path
import struct as S,json,hashlib
root=Path('work/execution/abi-witness'); out=[]
def h(b):return hashlib.sha256(b).hexdigest()
# Independently parse MachO load commands/sections, then bind retained ranges and instruction words.
for row in json.loads((root/'stage5/artifact-comparison.json').read_bytes())['rows']:
 p=root/'stage5/codegen'/row['profile']; b=next(p.glob('*.o')).read_bytes();assert h(b)==row['object_sha256']; assert S.unpack_from('<I',b)[0]==0xfeedfacf
 ncmds=S.unpack_from('<I',b,16)[0]; off=32; sections=[]; syms=None
 for _ in range(ncmds):
  cmd,size=S.unpack_from('<II',b,off)
  if cmd==0x19:
   nsec=S.unpack_from('<I',b,off+64)[0]
   for j in range(nsec):
    z=off+72+j*80;name=b[z:z+16].split(b'\0')[0];addr,n,ptr=S.unpack_from('<QQI',b,z+32);reloff,nrel=S.unpack_from('<II',b,z+56);sections.append((name,addr,n,ptr,reloff,nrel))
  if cmd==2:syms=S.unpack_from('<IIII',b,off+8)
  off+=size
 sec=[x for x in sections if x[0]==b'__text'];assert len(sec)==1
 _,addr,n,ptr,rptr,nrel=sec[0];text=b[ptr:ptr+n];assert n==row['text_bytes'];cursor=0;count=0
 for f in row['functions']:
  assert f['start']==cursor;rb=bytes.fromhex(f['raw_hex']);assert text[f['start']:f['end_exclusive']]==rb
  assert b''.join(S.pack('<I',int(x,16)) for x in f['object_words'])==rb
  cursor=f['end_exclusive'];count+=len(f['object_words'])
 assert cursor==n and count==row['instruction_count']
 symoff,nsyms,stroff,strsize=syms;names=[]
 for i in range(nsyms):
  stridx,typ,sect,desc,value=S.unpack_from('<IBBHQ',b,symoff+i*16);end=b.index(0,stroff+stridx);names.append((b[stroff+stridx:end].decode(),value,sect))
 rels=[]
 for i in range(nrel):
  a,v=S.unpack_from('<iI',b,rptr+i*8);idx=v&0xffffff;ext=(v>>27)&1;kind=v>>28
  if ext and kind==2:rels.append({'offset':a,'symbol':names[idx][0],'word':hex(S.unpack_from('<I',text,a)[0])})
 for alias,target in row['alias_equalities'].items():
  ns={name:(v,s) for name,v,s in names};assert ns[alias]==ns[target]
 out.append({'profile':row['profile'],'text_bytes':n,'instructions':count,'branch26':rels})
# Independently parse COFF, including section/symbol/relocation tables.
p=root/'stage5/windows-codegen/subjects-opt2-01';b=(p/'abi_subjects.o').read_bytes();c=json.loads((root/'stage6/analysis/artifact-comparison.json').read_bytes());assert h(b)==c['object_sha256']
machine,nsecs,timestamp,symoff,nsyms,optsz,chars=S.unpack_from('<HHIIIHH',b);assert machine==0x8664 and nsecs==23; strings=symoff+nsyms*18
syms={};i=0
while i<nsyms:
 z=symoff+i*18;nb=b[z:z+8]
 if nb[:4]==b'\0'*4:start=strings+S.unpack_from('<I',nb,4)[0];name=b[start:b.index(0,start)].decode()
 else:name=nb.split(b'\0')[0].decode()
 value,sect,typ,storage,aux=S.unpack_from('<IhHBB',b,z+8);syms[i]=(name,value,sect,storage);i+=aux+1
texts=[]
for idx,expected in enumerate(c['sections']):
 z=20+optsz+40*idx;name=b[z:z+8].split(b'\0')[0].decode();n,ptr,rptr=S.unpack_from('<III',b,z+16);nr=S.unpack_from('<H',b,z+32)[0];rb=b[ptr:ptr+n] if ptr else b''
 assert name==expected['name'] and n==expected['size'] and rb.hex()==expected['raw_hex'];rels=[]
 for j in range(nr):
  a,si,kind=S.unpack_from('<IIH',b,rptr+j*10);rels.append({'offset':a,'symbol':syms[si][0],'type':kind})
 if name=='.text' and n:
  cursor=0
  for ins in expected['instructions']:
   assert ins['offset']==cursor;v=bytes.fromhex(ins['bytes']);assert rb[cursor:cursor+len(v)]==v;cursor+=len(v)
  assert cursor==n
  texts.append({'section_one_based':idx+1,'bytes':n,'instructions':len(expected['instructions']),'relocations':rels,'symbols':[s[0] for s in syms.values() if s[2]==idx+1 and s[3]==2]})
assert sum(t['bytes'] for t in texts)==232 and sum(t['instructions'] for t in texts)==72 and sum(len(t['symbols']) for t in texts)==20
out.append({'profile':'windows-subjects-opt2','sections':texts})
Path('work/execution/review-abi-witness/object-byte-audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':'PASS independent section/symbol/relocation and all retained instruction-byte/range bindings','host_bytes':sum(x['text_bytes'] for x in out[:-1]),'host_instructions':sum(x['instructions'] for x in out[:-1]),'windows_bytes':232,'windows_instructions':72,'windows_relocs':[x for t in texts for x in t['relocations']]}))
