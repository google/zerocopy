#!/usr/bin/env python3
"""Narrow unverified COFF/UNWIND_INFO check and owned context reconstruction.
Only the recorded single-function x64 V1 subset is accepted. No native execution.
"""
import hashlib
import json
from pathlib import Path
import struct

def sha(b): return hashlib.sha256(b).hexdigest()

def coff(raw):
    if len(raw) < 20: raise ValueError('truncated COFF')
    machine, count, timestamp, symoff, symcount, optional, flags = struct.unpack_from('<HHIIIHH', raw)
    if machine != 0x8664 or optional != 0 or len(raw) < 20+40*count:
        raise ValueError('unexpected COFF header')
    stringoff = symoff + 18*symcount
    if stringoff+4 > len(raw): raise ValueError('truncated symbols')
    stringsize = struct.unpack_from('<I',raw,stringoff)[0]
    if stringsize < 4 or stringoff+stringsize > len(raw): raise ValueError('bad strings')
    def string(offset):
        if not 4 <= offset < stringsize: raise ValueError('bad string offset')
        end = raw.find(b'\0',stringoff+offset,stringoff+stringsize)
        if end < 0: raise ValueError('unterminated string')
        return raw[stringoff+offset:end].decode('ascii')
    sections = {}
    bynumber = {}
    for i in range(count):
        h = 20+40*i
        name = raw[h:h+8].rstrip(b'\0').decode('ascii')
        if name.startswith('/'): name = string(int(name[1:]))
        size, ptr, reloc, _, nreloc, _, characteristics = struct.unpack_from('<IIIIHHI', raw,h+16)
        if ptr+size > len(raw) or reloc+10*nreloc > len(raw): raise ValueError('section bounds')
        if name in sections: raise ValueError('duplicate section')
        sec = {'name':name,'number':i+1,'header':h,'data_offset':ptr,'size':size,
            'data':raw[ptr:ptr+size], 'reloc_offset':reloc,'reloc_count':nreloc}
        sections[name] = sec; bynumber[i+1] = sec
    symbols = {}
    index = 0
    while index < symcount:
        off = symoff+index*18
        if off+18 > len(raw): raise ValueError('symbol bounds')
        namebytes=raw[off:off+8]
        name=string(struct.unpack_from('<I',namebytes,4)[0]) if namebytes[:4]==bytes(4) else namebytes.rstrip(b'\0').decode('ascii')
        value, section, kind, storage, aux = struct.unpack_from('<IhHBB',raw,off+8)
        symbols[index]={'name':name,'value':value,'section':section,'type':kind,'storage':storage}
        index += 1+aux
    if index != symcount: raise ValueError('aux bounds')
    for sec in sections.values():
        sec['relocations']=[]
        for i in range(sec['reloc_count']):
            offset, symbol, kind = struct.unpack_from('<IIH',raw,sec['reloc_offset']+10*i)
            if symbol not in symbols: raise ValueError('bad relocation symbol')
            sec['relocations'].append({'offset':offset,'kind':kind,'symbol':symbols[symbol]})
    return sections, symbols

def decode_v1(data):
    if len(data)<4: raise ValueError('truncated unwind header')
    version, flags = data[0]&7, data[0]>>3
    prolog, count, frame, scaled = data[1],data[2],data[3]&15,data[3]>>4
    if version != 1 or flags != 0 or frame != 5 or len(data)<4+2*count:
        raise ValueError('unsupported unwind subset')
    codes=[]
    previous=256
    for i in range(count):
        offset, code = data[4+2*i:6+2*i]
        op, info = code&15,code>>4
        if offset > prolog or offset > previous: raise ValueError('bad code order/range')
        previous=offset
        if op==0 and info==5: action={'kind':'push_rbp'}
        elif op==2: action={'kind':'alloc','bytes':info*8+8}
        elif op==3 and info==0: action={'kind':'set_fp','offset':scaled*16}
        else: raise ValueError('unsupported unwind opcode')
        codes.append({'code_offset':offset,'op':op,'info':info,**action})
    return {'version':version,'flags':flags,'prolog_size':prolog,'count':count,'frame_register':'RBP','frame_offset':scaled*16,'codes':codes}

def reconstruct(info, pc_offset, context, memory):
    rsp,rbp=context['rsp'],context['rbp']
    if info is not None:
        for code in info['codes']:
            if code['code_offset']>pc_offset: continue
            if code['kind']=='set_fp': rsp=rbp-code['offset']
            elif code['kind']=='alloc': rsp+=code['bytes']
            elif code['kind']=='push_rbp': rbp=memory[rsp];rsp+=8
    return {'rip':memory[rsp], 'rsp':rsp+8, 'rbp':rbp}

def main():
    root=Path(__file__).resolve().parent
    original=(root/'specimen.obj').read_bytes()
    sections,symbols=coff(original)
    if set(['.text','.xdata','.pdata'])-set(sections): raise ValueError('missing required sections')
    text=sections['.text']['data']
    if not text.startswith(bytes.fromhex('554883ec50488d6c2450')) or not text.endswith(bytes.fromhex('4883c4505dc3')):
        raise ValueError('different recorded prologue/epilogue')
    functions=[s for s in symbols.values() if s['name']=='unwind_frame' and s['section']==sections['.text']['number']]
    if len(functions)!=1 or functions[0]['value']!=0: raise ValueError('wrong function symbol')
    pdata=sections['.pdata']; fields=struct.unpack('<III',pdata['data'])
    if fields!=(0,len(text),0): raise ValueError('different object runtime-function addends')
    expected=[(0,'.text'),(4,'.text'),(8,'.xdata')]
    relocs=pdata['relocations']
    if [(r['offset'],r['symbol']['name']) for r in relocs] != expected or any(r['kind']!=3 for r in relocs):
        raise ValueError('different ADDR32NB pdata relocation pattern')
    info=decode_v1(sections['.xdata']['data'])
    if info['prolog_size']!=10 or [(c['code_offset'],c['kind']) for c in info['codes']] != [(10,'set_fp'),(5,'alloc'),(1,'push_rbp')]:
        raise ValueError('unexpected recorded prologue offsets')
    entry=0x1008; old_rbp=0x55550000; return_pc=0x12345678
    memory={addr:0x70000000+addr for addr in range(entry-128,entry+64,8)}
    memory[entry-8]=old_rbp;memory[entry]=return_pc
    expected_caller={'rip':return_pc,'rsp':entry+8,'rbp':old_rbp}
    samples=[]
    for pc,rsp,rbp in [(0,entry,old_rbp),(1,entry-8,old_rbp),(5,entry-88,old_rbp),(10,entry-88,entry-8),(43,entry-88,entry-8)]:
        context={'rsp':rsp,'rbp':rbp}
        observed=reconstruct(info,pc,context,memory)
        if observed!=expected_caller: raise RuntimeError('positive context mismatch')
        samples.append({'pc_offset':pc,'context':context,'recovered':observed})
    # Ordinary epilogue: ADD RSP,80; POP RBP; RET. Metadata is never consulted.
    body={'rsp':entry-88,'rbp':entry-8}
    normal_rsp=body['rsp']+80
    normal={'rbp':memory[normal_rsp],'rip':memory[normal_rsp+8],'rsp':normal_rsp+16}
    if normal!=expected_caller:raise RuntimeError('normal epilogue mismatch')
    controls=[]
    for name,change in [('wrong_frame_offset',('frame',)),('wrong_alloc_size',('alloc',)),('stripped_pdata',('pdata',))]:
        altered=bytearray(original)
        if change[0]=='frame':altered[sections['.xdata']['data_offset']+3]^=0x10
        elif change[0]=='alloc':altered[sections['.xdata']['data_offset']+7]-=0x10
        else:altered[pdata['header']:pdata['header']+8]=b'.gone\0\0\0'
        mutant=bytes(altered); (root/(name+'.obj')).write_bytes(mutant)
        secs,_=coff(mutant)
        if secs['.text']['data']!=text:raise RuntimeError('control changed machine instructions')
        decoded=decode_v1(secs['.xdata']['data']) if '.pdata' in secs else None
        recovered=reconstruct(decoded,43,body,memory)
        if recovered==expected_caller:raise RuntimeError('control did not distinguish unwind context')
        controls.append({'name':name,'object_sha256':sha(mutant),'text_unchanged':True,'normal_epilogue_recovered':normal,'unwind_recovered':recovered,'correct_unwind_rejected':True})
    result={'status':'passed','scope':'one COFF function, V1 flags0/PUSH_RBP/ALLOC_SMALL/SET_FPREG, fixed body and prologue contexts; owned non-OS reconstruction',
      'object_sha256':sha(original),'text_sha256':sha(text),'text_bytes':len(text),'xdata_hex':sections['.xdata']['data'].hex(),
      'runtime_function_object_addends':fields,'runtime_function_relocations':relocs,'unwind_info':info,
      'expected_caller':expected_caller,'positive_contexts':samples,'negative_controls':controls,
      'section_summary':[{k:v for k,v in sec.items() if k not in ['data','relocations']} for sec in sections.values()]}
    (root/'unwind-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'passed','positive_contexts':len(samples),'negative_controls':len(controls),'xdata':result['xdata_hex']}))

if __name__=='__main__':main()
