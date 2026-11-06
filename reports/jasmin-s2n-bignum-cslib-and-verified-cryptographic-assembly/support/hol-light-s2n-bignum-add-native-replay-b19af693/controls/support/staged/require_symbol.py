"""PREPARATION ONLY; owned binding check, not part of the HOL importer."""
import json,struct,sys
from pathlib import Path
p=Path(sys.argv[1]);b=p.read_bytes()
if b[:7]!=b'\x7fELF\x02\x01\x01':raise SystemExit('unexpected ELF input')
off=struct.unpack_from('<Q',b,40)[0];size,count=struct.unpack_from('<HH',b,58)
headers=[struct.unpack_from('<IIQQQQIIQQ',b,off+i*size) for i in range(count)]
found=[]
for h in headers:
    if h[1]!=2:continue
    st=headers[h[6]];names=b[st[4]:st[4]+st[5]]
    for pos in range(h[4],h[4]+h[5],h[9]):
        n,info,other,section,value,length=struct.unpack_from('<IBBHQQ',b,pos)
        if n and names[n:names.index(b'\0',n)]==b'bignum_add':
            found.append({'section':section,'value':value,'size':length})
print(json.dumps({'required_symbol':'bignum_add','matches':found}))
if len(found)!=1:
    raise SystemExit('ANNEAL_REQUIRED_SYMBOL_MISSING_OR_NONUNIQUE')
