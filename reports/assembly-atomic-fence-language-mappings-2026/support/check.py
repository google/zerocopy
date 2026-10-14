#!/usr/bin/env python3
"""Check the finite compiled witnesses, never execute target instructions."""
import argparse, json, pathlib, re, sys
p=argparse.ArgumentParser()
p.add_argument('directory',type=pathlib.Path)
a=p.parse_args()
bodies=json.loads((a.directory/'assembly-bodies.json').read_text())
rows=[]
ir_orders={
 'load_relaxed':'load atomic i64, ptr %0 monotonic, align 8',
 'load_acquire':'load atomic i64, ptr %0 acquire, align 8',
 'load_seq_cst':'load atomic i64, ptr %0 seq_cst, align 8',
 'store_relaxed':'store atomic i64 %1, ptr %0 monotonic, align 8',
 'store_release':'store atomic i64 %1, ptr %0 release, align 8',
 'store_seq_cst':'store atomic i64 %1, ptr %0 seq_cst, align 8',
 'add_relaxed':'atomicrmw add ptr %0, i64 %1 monotonic, align 8',
 'add_acq_rel':'atomicrmw add ptr %0, i64 %1 acq_rel, align 8',
 'add_seq_cst':'atomicrmw add ptr %0, i64 %1 seq_cst, align 8',
 'cas_acq_rel':'cmpxchg ptr %0, i64 %4, i64 %2 acq_rel acquire, align 8',
 'fence_acquire':'fence acquire', 'fence_release':'fence release',
 'fence_acq_rel':'fence acq_rel', 'fence_seq_cst':'fence seq_cst',
 'signal_seq_cst':'fence syncscope("singlethread") seq_cst',
 'compiler_barrier':'asm sideeffect "",',
}
for config,fs in bodies.items():
 ir=(a.directory/(config+'.ll')).read_text()
 irm={m.group(1):m.group(2) for m in re.finditer(r'^define[^\n]*@([A-Za-z_]\w*)\([^\n]*\{\n(.*?)^}',ir,re.M|re.S)}
 for name,instructions in fs.items():
  asm='\n'.join(instructions)
  critical=[x.strip() for x in irm.get(name,'').splitlines() if re.search(r'atomic|cmpxchg|fence|asm sideeffect',x)]
  checks={'ir_order_or_effect':ir_orders.get(name,'asm sideeffect "dmb ish"' if config.startswith('aarch64') else 'asm sideeffect "mfence"') in irm.get(name,''),
          'no_external_call':not bool(re.search(r'^\s*(call|bl)\b',asm,re.M))}
  if config=='x86_64':
   if name.startswith('load_'):rule=r'^movq\s+\(%rdi\), %rax$'
   elif name in ('store_relaxed','store_release'):rule=r'^movq\s+%rsi, \(%rdi\)$'
   elif name=='store_seq_cst':rule=r'^xchgq\s+%rsi, \(%rdi\)$'
   elif name.startswith('add_'):rule=r'^lock\s+xaddq\b'
   elif name=='cas_acq_rel':rule=r'^lock\s+cmpxchgq\b'
   elif name=='fence_seq_cst':rule=r'^lock\s+orl\s+\$0, -64\(%rsp\)$'
   elif name=='explicit_hw_fence':rule=r'^mfence$'
   else:rule=None
  else:
   if name=='load_relaxed':rule=r'^ldr\s+x0, \[x0\]$'
   elif name.startswith('load_'):rule=r'^ldar\s+x0, \[x0\]$'
   elif name=='store_relaxed':rule=r'^str\s+x1, \[x0\]$'
   elif name.startswith('store_'):rule=r'^stlr\s+x1, \[x0\]$'
   elif name.startswith('add_') and config=='aarch64-lse':rule=r'^'+('ldadd' if name=='add_relaxed' else 'ldaddal')+r'\s'
   elif name.startswith('add_'):
    rule=r'^'+('ldxr' if name=='add_relaxed' else 'ldaxr')+r'\s'
    checks['exclusive_store']=bool(re.search(r'^'+('stxr' if name=='add_relaxed' else 'stlxr')+r'\s',asm,re.M))
    checks['retry_branch']=bool(re.search(r'^cbnz\s',asm,re.M))
   elif name=='cas_acq_rel' and config=='aarch64-lse':rule=r'^casal\s'
   elif name=='cas_acq_rel':
    rule=r'^ldaxr\s'
    checks['exclusive_store']=bool(re.search(r'^stlxr\s',asm,re.M))
    checks['mismatch_clears_exclusive']=bool(re.search(r'^clrex$',asm,re.M))
   elif name=='fence_acquire':rule=r'^dmb\s+ishld$'
   elif name.startswith('fence_') or name=='explicit_hw_fence':rule=r'^dmb\s+ish$'
   else:rule=None
  if rule:checks['selected_machine_sequence']=bool(re.search(rule,asm,re.M))
  else:checks['return_only_no_hardware_barrier']=instructions in (['ret'],['retq'])
  if name in ('compiler_barrier','explicit_hw_fence'):
   checks['ir_memory_clobber']='~{memory}' in irm.get(name,'')
  rows.append(dict(configuration=config,function=name,checks=checks,critical_ir=critical))
counts={k:len(v) for k,v in bodies.items()}
failed=[r for r in rows if not all(r['checks'].values())]
result=dict(status='pass' if not failed and counts==dict(x86_64=17,aarch64=17,**{'aarch64-lse':17}) else 'fail',
            function_rows=len(rows),predicate_checks=sum(len(r['checks']) for r in rows),function_counts=counts,failed=failed,rows=rows)
(a.directory/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='rows'}))
if result['status']!='pass':sys.exit(1)
