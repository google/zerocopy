"""Owned bounded formulas; no installs, builders, or accepted-status shortcuts."""
from pathlib import Path
import hashlib, json, os, subprocess, time

ROOT = Path(__file__).resolve().parent
CVC = Path(os.environ['BYTE_LAWS_CVC5']).resolve()
CARCARA = Path(os.environ['BYTE_LAWS_CARCARA']).resolve()
assert ROOT.resolve() == ROOT

def s(array, index): return f'(select {array} {index})'
def eq(a,b): return f'(= {a} {b})'
def lt2(x): return f'(not (>= {x} 2))'
def conj(*xs): return '(and ' + ' '.join(xs) + ')'

S0,S1,T0,T1 = s('source',0),s('source',1),s('current',0),s('current',1)
SR = [s('source_init',0),s('source_read',0),s('source_init',1),s('source_read',1)]
TR = [s('current_init',0),s('current_read',0),s('current_init',1),s('current_read',1)]
base='''(set-logic QF_AUFLIA)
(declare-const source (Array Int Int))
(declare-const current (Array Int Int))
(declare-const source_init (Array Int Bool))
(declare-const source_read (Array Int Bool))
(declare-const current_init (Array Int Bool))
(declare-const current_read (Array Int Bool))
(declare-const write_authority (Array Int Bool))
(declare-const changed Int)
(declare-const framed Int)
(declare-const replacement Int)
'''
domains = [f'(and (<= 0 {v}) (< {v} 256))' for v in [S0,S1,T0,T1,'replacement']]
domains += ['(or (= changed 0) (= changed 1))','(or (= framed 0) (= framed 1))']
stored='(store source changed replacement)'
stored_init='(store source_init changed true)'
write_goal=conj(eq(s(stored,'changed'),'replacement'),s(stored_init,'changed'),eq(s(stored,'framed'),s('source','framed')),eq(s(stored_init,'framed'),s('source_init','framed')))
bool_pre=[SR[0],SR[1],TR[0],TR[1],eq(S0,T0),lt2(S0)]
bool_goal=conj(TR[0],TR[1],lt2(T0))
array_pre=SR+TR+[eq(S0,T0),eq(S1,T1),lt2(S0),lt2(S1)]
array_goal=conj(*TR,lt2(T0),lt2(T1))
cases={
 'into_bytes': {'want':'unsat','premises':SR,'goal':conj(*SR)},
 'byte_write': {'want':'unsat','premises':[s('write_authority','changed'),'(not (= changed framed))'],'goal':write_goal},
 'bool_validate': {'want':'unsat','premises':bool_pre,'goal':bool_goal},
 'array_validate': {'want':'unsat','premises':array_pre,'goal':array_goal},
 'missing_initialization': {'want':'sat','premises':SR[1:],'goal':conj(*SR)},
 'alias_frame': {'want':'sat','premises':[s('write_authority','changed')],'goal':write_goal},
 'bool_two': {'want':'sat','premises':bool_pre[:-1]+[f'(< {S0} 3)'],'goal':bool_goal},
 'missing_stability': {'want':'sat','premises':[x for x in bool_pre if x!=eq(S0,T0)],'goal':bool_goal},
 'array_index_omission': {'want':'sat','premises':array_pre[:-1],'goal':array_goal},
 'wrong_narrow_domain': {'want':'unsat','premises':bool_pre[:-1]+[f'(< {S0} 2)',f'(< {S0} 3)'],'goal':bool_goal},
}

# Equivalent decomposition, with the exact original byte-write premises.
# All four component obligations are mandatory; one valid projection is not
# acceptance of the conjunction. No resource or domain premise is added.
write_components=[eq(s(stored,'changed'),'replacement'),s(stored_init,'changed'),eq(s(stored,'framed'),s('source','framed')),eq(s(stored_init,'framed'),s('source_init','framed'))]
for i,g in enumerate(write_components):
 cases[f'byte_write_component{i}']={'want':'unsat','premises':cases['byte_write']['premises'].copy(),'goal':g}

values=[S0,S1,T0,T1]+SR+TR+[s('write_authority',0),s('write_authority',1),'changed','framed','replacement']

def run(args, stem, timeout=20):
 start=time.monotonic_ns()
 try:
  p=subprocess.run([str(a) for a in args],capture_output=True,timeout=timeout)
  row={'exit':p.returncode,'elapsed_ns':time.monotonic_ns()-start,'stdout_bytes':len(p.stdout),'stderr_bytes':len(p.stderr)}
  out,err=p.stdout,p.stderr
 except subprocess.TimeoutExpired as e:
  row={'exit':None,'timeout':True,'elapsed_ns':time.monotonic_ns()-start};out,err=e.stdout or b'',e.stderr or b''
 Path(str(stem)+'.stdout').write_bytes(out);Path(str(stem)+'.stderr').write_bytes(err)
 Path(str(stem)+'.json').write_text(json.dumps(row,indent=2)+'\n')
 return row,out

def exact_valid(row,out): return row['exit']==0 and out==b'valid\n'

def main():
 out=ROOT/'smt';out.mkdir(exist_ok=True)
 rows=[]
 for name,c in cases.items():
  before=time.monotonic_ns()
  f=out/(name+'.smt2')
  text=base+'(set-option :produce-'+('proofs' if c['want']=='unsat' else 'models')+' true)\n'
  text+=''.join('(assert '+p+')\n' for p in domains+c['premises'])
  text+='(assert (not '+c['goal']+'))\n(check-sat)\n'
  text+='(get-proof)\n' if c['want']=='unsat' else '(get-value ('+' '.join(values)+'))\n'
  f.write_text(text)
  c['source_creation_ns']=time.monotonic_ns()-before
  row,raw=run([CVC,'--proof-format-mode=alethe','--proof-granularity=dsl-rewrite-strict',f],out/(name+'.generate'))
  row.update(case=name,phase='generate',want=c['want'])
  rows.append(row)
  if row['exit']!=0 or not raw.startswith((c['want']+'\n').encode()):
   c['observed']='operational-or-result-mismatch';continue
  if c['want']=='sat': c['observed']='countermodel';continue
  proof=out/(name+'.alethe');proof.write_bytes(raw[len(b'unsat\n'):])
  row,raw=run([CARCARA,'--no-color','check',proof,f],out/(name+'.check'))
  row.update(case=name,phase='check',accepted=exact_valid(row,raw));rows.append(row)
  c['observed']='strict-valid' if exact_valid(row,raw) else 'not-strict-valid'
 (ROOT/'smt-results.json').write_text(json.dumps({'cases':cases,'runs':rows,'policy':'exit0 AND exact valid newline; holey exit0 rejected; no allowed-rule/custom-checker bypass flags','scope':'All source, formula, parser/quotation, arithmetic/array interpretation and native binary/runtime premises remain explicit.'},indent=2)+'\n')
 print(json.dumps({name:c['observed'] for name,c in cases.items()},indent=2))

if __name__=='__main__': main()
