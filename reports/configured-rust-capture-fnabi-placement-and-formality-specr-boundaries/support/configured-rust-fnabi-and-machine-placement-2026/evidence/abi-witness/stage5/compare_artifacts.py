"""Check every emitted assembly instruction against disassembly and raw object words.
This is an untrusted data comparison, not ARM operational semantics/adequacy.
"""
from pathlib import Path
import hashlib,json,re
S=Path(__file__).resolve().parent
PROFILES=['host-subjects-opt0','host-subjects-opt2','host-vectors-opt0','host-vectors-opt2']
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def norm(s):
 s=s.split(';',1)[0].strip()
 s=re.sub(r'#(-?0x[0-9a-fA-F]+)',lambda m:'#'+str(int(m[1],0)),s)
 return re.sub(r'\s+','',s)
def main():
 rows=[]
 for profile in PROFILES:
  R=S/'codegen'/profile;asm=list(R.glob('*.s'))[0];ir=list(R.glob('*.ll'))[0];obj=list(R.glob('*.o'))[0]
  m=json.loads((S/'object-inspection'/(profile+'.macho.json')).read_text())
  assert h(obj)==m['sha256']
  assert len(m['sections'])==1 and m['sections'][0]['name']=='__text'
  text=m['sections'][0];raw=bytes.fromhex(text['data_hex'])
  symbols={x['name']:x for x in m['symbols']}
  relocs={x['address']:x for x in text['relocations']}
  dis={}
  for line in (S/'object-inspection'/(profile+'.stdout')).read_text().splitlines():
   mt=re.fullmatch(r'\s*([0-9a-f]+): ([0-9a-f]{8})\s+(.+)',line)
   if mt:
    a=int(mt[1],16);word=int(mt[2],16);insn=mt[3]
    assert a not in dis and int.from_bytes(raw[a:a+4],'little')==word
    if a in relocs:
     r=relocs[a]
     assert r['type']==2 and r['pcrel']==1 and r['length_log2']==2 and r['external']==1 and word&0xfc000000==0x94000000
     insn='bl '+r['symbol']
    dis[a]={'word':word,'instruction':insn,'normalized':norm(insn)}
  assert set(dis)==set(range(0,len(raw),4))
  functions={};aliases={};current=None
  for line in asm.read_text().splitlines():
   if line.startswith('_') and line.endswith(':'):
    current=line[:-1];functions[current]=[]
   elif re.fullmatch(r'_[^ ]+ = _[^ ]+',line):
    a,b=line.split(' = ');aliases[a]=b;current=None
   elif line.startswith('\t') and line.strip() and not line.strip().startswith('.'):
    assert current is not None
    functions[current].append(line.strip())
  covered=set();bindings=[]
  for symbol,instructions in functions.items():
   assert symbol in symbols and symbols[symbol]['section_index']==1
   start=symbols[symbol]['value'];end=start+4*len(instructions)
   for i,insn in enumerate(instructions):
    a=start+4*i
    assert a in dis and norm(insn)==dis[a]['normalized'],(profile,symbol,a,insn,dis.get(a))
    assert a not in covered;covered.add(a)
   bindings.append({'symbol':symbol,'start':start,'end_exclusive':end,'instruction_count':len(instructions),'raw_hex':raw[start:end].hex(),'raw_sha256':hashlib.sha256(raw[start:end]).hexdigest(),'assembly':instructions,'object_words':[hex(dis[a]['word']) for a in range(start,end,4)],'relocations':[r for a,r in relocs.items() if start<=a<end]})
  assert covered==set(dis)
  for a,b in aliases.items():assert symbols[a]['value']==symbols[b]['value']
  headers=[{'line':i+1,'text':x} for i,x in enumerate(ir.read_text().splitlines()) if x.startswith('define ') or ' alias ' in x or (x.startswith('declare ') and '@abi_' in x)]
  rows.append({'profile':profile,'ir_sha256':h(ir),'assembly_sha256':h(asm),'object_sha256':h(obj),'instruction_count':len(dis),'text_bytes':len(raw),'matched_all_instruction_text_and_raw_words':True,'alias_equalities':aliases,'functions':bindings,'ir_headers':headers})
 output={'status':'PASS','helper_sha256':h(Path(__file__)),'scope':'All bytes of the four __text sections are compared to object-reader raw words; every emitted assembly instruction compared to reader mnemonic modulo whitespace/immediate numeral spelling and symbol-bound unresolved BL relocations. Aliases checked by nlist values. IR headers preserved for manual FnAbi/IR/placement inspection. Not a verified parser/disassembler/assembler or compiler/ISA theorem.','rows':rows}
 with (S/'artifact-comparison.json').open('x') as f:json.dump(output,f,indent=2);f.write('\n')
 print(json.dumps({'status':output['status'],'profiles':[{'profile':x['profile'],'text_bytes':x['text_bytes'],'instructions':x['instruction_count'],'functions':len(x['functions']),'aliases':x['alias_equalities']} for x in rows]},indent=2))
if __name__=='__main__':main()
