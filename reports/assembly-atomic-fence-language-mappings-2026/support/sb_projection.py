#!/usr/bin/env python3
"""Owned four-event relation calculation, NOT herd/model/ISA execution.

Fixed SB candidate: a=Wx1,b=Ry0,c=Wy1,d=Rx0. Initial writes are omitted;
their relevant from-read edges are b->c and d->a. Each thread's program
order is a->b or c->d. This projects only the named ordering-cycle checks;
it does not generate candidates, interpret CAT, or validate all model rules.
"""
import json, pathlib, sys
po={('a','b'),('c','d')}
fr={('b','c'),('d','a')}
def closure(edges):
    reached=set(edges)
    while True:
        grown=reached|{(a,d) for a,b in reached for c,d in reached if b==c}
        if grown==reached:return reached
        reached=grown
def case(name,ordered,expected_cycle):
    edges=fr|ordered
    reached=closure(edges)
    cycle=any(a==b for a,b in reached)
    return dict(name=name,order_edges=sorted(ordered),from_read_edges=sorted(fr),
                cyclic=cycle,expected_cycle_fixture=expected_cycle,
                fixture_agrees=cycle==expected_cycle,
                self_edges=sorted(a for a,b in reached if a==b))
rows=[case('x86 plain MOV: no preserved WR edges',set(),False),
      case('x86 MFENCE in both threads: ghb mfence edges',po,True),
      case('x86 one MFENCE missing: one order edge only',{('a','b')},False),
      case('x86 locked SC stores: implied AM WR edges',po,True),
      case('A64 STR/LDR: no bob WR edges',set(),False),
      case('A64 DMB ISH in both threads: bob full edges',po,True),
      case('A64 one DMB missing: one order edge only',{('a','b')},False),
      case('A64 DMB ISHLD after stores: no preceding-read edges',set(),False),
      case('A64 STLR/LDAR: bob L-po-A edges',po,True),
      case('empty compiler memory-clobber asm: no hardware event',set(),False)]
result=dict(status='pass' if all(r['fixture_agrees'] for r in rows) else 'fail',
    scope='fixed-candidate four-event ordering relation projection, not herd execution or complete model validation',cases=rows)
path=pathlib.Path(sys.argv[1]);path.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status=result['status'],cases=len(rows),cyclic=sum(r['cyclic'] for r in rows))))
if result['status']!='pass':sys.exit(1)
