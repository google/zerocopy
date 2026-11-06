"""Owned finite store-buffering fragment; not a full Rust or hardware model."""
import json

def explore(buffered):
    initial=(0,0,0,0,None,None,None,None)
    seen=set();final=set();witness={}
    def visit(s,trace):
        if s in seen: return
        seen.add(s)
        p,q,x,y,b,c,r,t=s
        if p==q==2 and b is None and c is None:
            final.add((r,t));witness.setdefault(str((r,t)),trace);return
        if p==0:
            visit((1,q,x if buffered else 1,y,1 if buffered else None,c,r,t),trace+['T0:Wx=1'])
        if p==1: visit((2,q,x,y,b,c,y,t),trace+['T0:Ry'])
        if q==0:
            visit((p,1,x,y if buffered else 1,b,1 if buffered else None,r,t),trace+['T1:Wy=1'])
        if q==1: visit((p,2,x,y,b,c,r,x),trace+['T1:Rx'])
        if buffered and b is not None: visit((p,q,b,y,None,c,r,t),trace+['flush0'])
        if buffered and c is not None: visit((p,q,x,c,b,None,r,t),trace+['flush1'])
    visit(initial,[])
    return {'states':len(seen),'outcomes':[list(x) for x in sorted(final)],'witnesses':witness}

sc=explore(False);store_buffer=explore(True)
if [0,0] in sc['outcomes'] or [0,0] not in store_buffer['outcomes']:
    raise SystemExit('litmus distinction failed')
print(json.dumps({'program':'T0: Wx=1;Ry / T1: Wy=1;Rx',
                  'sc_fragment':sc,'store_buffer_fragment':store_buffer},indent=2))
