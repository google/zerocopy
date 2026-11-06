import hashlib,json,struct
from pathlib import Path

def describe(p):
    b=p.read_bytes()
    if b[:7] != b'\x7fELF\x02\x01\x01':
        raise SystemExit('STOP: not ELF64 little-endian v1')
    machine=struct.unpack_from('<H',b,18)[0]
    if machine != 62:
        raise SystemExit('STOP: unexpected machine')
    off=struct.unpack_from('<Q',b,40)[0]
    size,count,strings=struct.unpack_from('<HHH',b,58)
    headers=[struct.unpack_from('<IIQQQQIIQQ',b,off+i*size) for i in range(count)]
    shstr=headers[strings];names=b[shstr[4]:shstr[4]+shstr[5]]
    def cstr(buf,n):return buf[n:buf.index(b'\0',n)].decode()
    sections=[(cstr(names,h[0]),h) for h in headers]
    text=[(i,h) for i,(name,h) in enumerate(sections) if name=='.text']
    if len(text)!=1:raise SystemExit('STOP: nonunique text section')
    index,h=text[0];code=b[h[4]:h[4]+h[5]]
    syms=[]
    for section,hdr in sections:
        if hdr[1]!=2:continue
        st=headers[hdr[6]];strtab=b[st[4]:st[4]+st[5]]
        for pos in range(hdr[4],hdr[4]+hdr[5],hdr[9]):
            name,info,other,section_index,value,length=struct.unpack_from('<IBBHQQ',b,pos)
            if name and cstr(strtab,name)=='bignum_add':
                syms.append({'name':'bignum_add','section_index':section_index,'value':value,'size':length,'info':info,'other':other,'equals_entire_text':section_index==index and value==0 and length==len(code)})
    return {'path':str(p),'object_bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'machine':machine,'text_section_index':index,'text_file_offset':h[4],'text_bytes':len(code),'text_sha256':hashlib.sha256(code).hexdigest(),'text_hex':code.hex(),'bignum_add_symbols':syms}

base=Path('/home/opam/anneal-cross-sources/s2n-bignum/x86/generic')
print(json.dumps([describe(base/name) for name in ['bignum_add.o','bignum_add.obj']],indent=2))
