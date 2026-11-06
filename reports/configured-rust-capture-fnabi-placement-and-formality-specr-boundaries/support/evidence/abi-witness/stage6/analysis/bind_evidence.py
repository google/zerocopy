from pathlib import Path
import struct,json,re,hashlib
root=Path(__file__).resolve().parents[2];out=Path(__file__).resolve().parent
obj=root/'stage5/windows-codegen/subjects-opt2-01/abi_subjects.o';data=obj.read_bytes()
machine,nsec,stamp,symoff,nsym,opth,flags=struct.unpack_from('<HHIIIHH',data)
assert machine==0x8664 and opth==0
strbase=symoff+18*nsym
symbols={};i=0
while i<nsym:
 off=symoff+18*i;name=data[off:off+8]
 if name[:4]==b'\0'*4:
  start=strbase+struct.unpack_from('<I',name,4)[0];name=data[start:data.index(b'\0',start)]
 else:name=name.rstrip(b'\0')
 val,sec,typ,storage,aux=struct.unpack_from('<IhHBB',data,off+8)
 symbols[i]={'name':name.decode(),'value':val,'section_one_based':sec,'type':typ,'storage':storage,'aux_count':aux};i+=1+aux
sections=[]
for k in range(nsec):
 off=20+40*k;name,vsize,vaddr,size,raw,reloc,line,nreloc,nline,chars=struct.unpack_from('<8sIIIIIIHHI',data,off)
 rel=[]
 for j in range(nreloc):
  addr,sym,typ=struct.unpack_from('<IIH',data,reloc+10*j);rel.append({'offset':addr,'type':typ,'symbol_index':sym,'symbol':symbols[sym]['name']})
 sections.append({'index_zero_based':k,'name':name.rstrip(b'\0').decode(),'size':size,'raw_file_offset':raw,'raw_hex':data[raw:raw+size].hex(),'characteristics':chars,'symbols':[v for v in symbols.values() if v['section_one_based']==k+1 and v['storage']==2],'relocations':rel})
text=[s for s in sections if s['name']=='.text' and s['size']]
dump=(out/'reader.stdout').read_text();blocks=dump.split('Disassembly of section .text:')[1:]
assert len(text)==len(blocks)==16
asm=(root/'stage5/windows-codegen/subjects-opt2-01/abi_subjects.s').read_text();ab={};cur=None
for line in asm.splitlines():
 if re.fullmatch(r'abi_\w+:',line):cur=line[:-1];ab[cur]=[]
 elif line.startswith('\t') and cur and not line.strip().startswith('.'):
  ab[cur].append(line.strip())
def norm(x):
 x=re.sub(r'0x([0-9a-f]+)',lambda m:str(int(m[1],16)),x)
 return re.sub(r'\s+','',x)
count=0
for s,b in zip(text,blocks):
 ins=[];position=0
 for line in b.splitlines():
  m=re.match(r'\s*([0-9a-f]+): ((?:[0-9a-f]{2} )+)\s*\t(.*)',line)
  if not m:continue
  at=int(m[1],16);raw=bytes.fromhex(m[2]);assert at==position and raw==bytes.fromhex(s['raw_hex'])[at:at+len(raw)]
  ins.append({'offset':at,'bytes':raw.hex(),'instruction':m[3]});position+=len(raw)
 assert position==s['size']
 primary=s['symbols'][0]['name'];assert len(ab[primary])==len(ins)
 for a,i in zip(ab[primary],ins):
  it=i['instruction']
  if it.startswith('callq'):
   rr=[r for r in s['relocations'] if r['offset']==i['offset']+1];assert len(rr)==1 and rr[0]['type']==4
   it='callq '+rr[0]['symbol']
  assert norm(a)==norm(it),(primary,a,it)
 s['range_half_open']=[0,s['size']];s['instructions']=ins;s['assembly_match']='all instructions, whitespace/hex normalization; calls use actual REL32 symbol';count+=len(ins)
headers=[l for l in (root/'stage5/windows-codegen/subjects-opt2-01/abi_subjects.ll').read_text().splitlines() if l.startswith(('define ','declare ','@abi_'))]
report={'object_sha256':hashlib.sha256(data).hexdigest(),'format':{'machine':machine,'sections':nsec,'symbol_table_entries_including_aux':nsym,'timestamp':stamp,'characteristics':flags},'sections':sections,'text_bytes':sum(s['size'] for s in text),'text_instruction_count':count,'text_body_count':len(text),'exported_function_symbols':sum(len(s['symbols']) for s in text),'unexplained_text_bytes':0,'padding_text_bytes':0,'ir_headers':headers,'trust':'Untrusted bounded Python COFF parsing and selected LLVM decoding/assembly comparison; no verified decoder/assembler/compiler theorem.'}
(out/'artifact-comparison.json').write_text(json.dumps(report,indent=2)+'\n');print({k:report[k] for k in ['text_bytes','text_instruction_count','text_body_count','exported_function_symbols','unexplained_text_bytes']})
