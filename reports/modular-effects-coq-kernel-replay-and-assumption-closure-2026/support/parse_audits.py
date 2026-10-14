from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parent
rows=[]
for kind,f in [('core','AuditCore.v'),('heaplang','AuditHeapLang.v'),('islaris','AuditIslaris.v')]:
    expected=re.findall(r'^Print Assumptions (\S+)\.',(R/f).read_text(),re.M)
    out=(R/'logs'/('audit-'+kind+'.stdout')).read_text()
    heads=list(re.finditer(r'(?m)^(@?[A-Za-z_][A-Za-z0-9_.]*)\n     :',out))
    if len(heads)!=len(expected):raise ValueError((kind,len(heads),len(expected)))
    for j,(h,name) in enumerate(zip(heads,expected)):
        block=out[h.start():heads[j+1].start() if j+1<len(heads) else out.index('ANNEAL_PHASE_RESULT')]
        if block.count('Axioms:')==1:
            ax=re.findall(r'(?m)^(\S+)(?:[ \t]*\n[ \t]*)?[ \t]*:',block.split('Axioms:\n',1)[1])
            if not ax:raise ValueError(('unparsed axioms',name))
            state='axioms'
        elif block.count('Closed under the global context')==1:
            ax=[];state='closed-under-global-context'
        else:raise ValueError(('unexpected context',name))
        rows.append({'constant':name,'audit':f,'log':'logs/audit-'+kind+'.stdout','observed_header':h.group(1),'context_status':state,'reported_axioms':ax,'observation_block_sha256':hashlib.sha256(block.encode()).hexdigest(),'observation_block':block})
x={'selected_result_constants':25,'explicit_axiom_observations':3,'rows':rows,'basis':'Actual coqc Check and Print Assumptions stdout; full observation blocks retained. Labels canonicalized only in summary below.'}
(R/'actual-assumptions.json').write_text(json.dumps(x,indent=2)+'\n')
for r in rows:print(r['constant'],':',','.join(r['reported_axioms']) or r['context_status'])
