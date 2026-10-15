"""Read the four owned MH_OBJECT files; no compilation, linking or execution."""
from pathlib import Path
import hashlib,json,struct,subprocess
S=Path(__file__).resolve().parent
READER=Path('/Library/Developer/CommandLineTools/usr/bin/llvm-objdump')
READER_SHA='83b32f39e5475ee168927eb1509c82978e08e0100ec8c6fafeca588d9960773c'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,z):
 with p.open('x') as f:json.dump(z,f,indent=2);f.write('\n')
def name(s):return s.split(b'\0')[0].decode('ascii')
def macho(p):
 b=p.read_bytes();magic,cpu,subcpu,kind,ncmds,sizecmds,flags,reserved=struct.unpack_from('<8I',b)
 assert magic==0xfeedfacf and cpu==0x100000c and kind==1
 off=32;sections=[];symtab=None
 for i in range(ncmds):
  cmd,size=struct.unpack_from('<II',b,off);assert 8<=size and off+size<=len(b)
  if cmd==0x19:
   nsects=struct.unpack_from('<I',b,off+64)[0]
   for j in range(nsects):
    f=struct.unpack_from('<16s16sQQIIIIIIII',b,off+72+80*j)
    sn,sg,addr,sz,foff,al,roff,nrel,sflags,r1,r2,r3=f
    data=b[foff:foff+sz];assert len(data)==sz
    rel=[]
    for k in range(nrel):
     a,w=struct.unpack_from('<iI',b,roff+8*k)
     rel.append({'address':a,'symbol_index':w&0xffffff,'pcrel':(w>>24)&1,'length_log2':(w>>25)&3,'external':(w>>27)&1,'type':(w>>28)&15,'raw_hex':b[roff+8*k:roff+8*k+8].hex()})
    sections.append({'name':name(sn),'segment':name(sg),'address':addr,'bytes':sz,'file_offset':foff,'alignment_log2':al,'flags':sflags,'data_hex':data.hex(),'sha256':hashlib.sha256(data).hexdigest(),'relocations':rel})
  elif cmd==2:symtab=struct.unpack_from('<4I',b,off+8)
  off+=size
 assert off==32+sizecmds and symtab
 so,ns,st,ss=symtab;symbols=[]
 for i in range(ns):
  si,nt,nsect,desc,value=struct.unpack_from('<IBBHQ',b,so+16*i)
  nm=b[st+si:st+ss].split(b'\0',1)[0].decode('utf-8')
  symbols.append({'index':i,'name':nm,'n_type':nt,'section_index':nsect,'n_desc':desc,'value':value})
 for sec in sections:
  for r in sec['relocations']:
   if r['external']:r['symbol']=symbols[r['symbol_index']]['name']
 return {'sha256':h(p),'bytes':len(b),'header':{'magic':hex(magic),'cpu':cpu,'cpu_subtype':subcpu,'filetype':kind,'commands':ncmds,'command_bytes':sizecmds,'flags':flags},'sections':sections,'symbols':symbols,'scope':'Untrusted bounded MachO metadata reader; exact raw bytes retained. No machine operational semantics or compiler correctness theorem.'}
def main():
 R=S/'object-inspection';assert not R.exists();R.mkdir()
 rows=[]
 for profile in ['host-subjects-opt0','host-subjects-opt2','host-vectors-opt0','host-vectors-opt2']:
  ps=list((S/'codegen'/profile).glob('*.o'));assert len(ps)==1;p=ps[0]
  m=macho(p);assert h(READER)==READER_SHA
  argv=[str(READER),'--disassemble','--reloc','--syms','--section-headers','--full-contents',str(p)]
  r=subprocess.run(argv,capture_output=True,timeout=30,env={'PATH':'/usr/bin:/bin:/usr/sbin:/sbin','LC_ALL':'C','LANG':'C'})
  with (R/(profile+'.stdout')).open('xb') as f:f.write(r.stdout)
  with (R/(profile+'.stderr')).open('xb') as f:f.write(r.stderr)
  after=h(READER);assert after==READER_SHA
  save(R/(profile+'.macho.json'),m)
  result={'profile':profile,'argv':argv,'exit_code':r.returncode,'reader_sha256_before_after':after,'object_sha256_before_after':h(p),'stdout_sha256':h(R/(profile+'.stdout')),'stderr_sha256':h(R/(profile+'.stderr')),'stdout_bytes':len(r.stdout),'metadata_sha256':h(R/(profile+'.macho.json')),'native_execution':False}
  rows.append(result);save(R/(profile+'.result.json'),result)
  print(json.dumps(result))
  if r.returncode or r.stderr or len(r.stdout)>1048576:raise SystemExit('STOP unexpected reader result')
 save(R/'summary.json',{'status':'PASS','helper_sha256':h(Path(__file__)),'rows':rows,'scope':'Actual raw object inspection only; no link/fixture execution/official ISA adequacy.'})
if __name__=='__main__':main()
