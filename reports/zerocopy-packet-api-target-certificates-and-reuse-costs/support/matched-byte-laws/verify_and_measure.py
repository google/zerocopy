from pathlib import Path
import hashlib, json, os, re, subprocess, time

ROOT=Path(__file__).resolve().parent
LEAN=Path(os.environ['BYTE_LAWS_LEAN']).resolve()
CVC=Path(os.environ['BYTE_LAWS_CVC5']).resolve()
CAR=Path(os.environ['BYTE_LAWS_CARCARA']).resolve()
assert ROOT.resolve()==ROOT

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def writej(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def run(args,stem):
 env=os.environ.copy();env['LEAN_PATH']=str(ROOT)
 start=time.monotonic_ns();r=subprocess.run([str(a) for a in args],cwd=ROOT,env=env,capture_output=True,timeout=30)
 row={'exit':r.returncode,'elapsed_ns':time.monotonic_ns()-start,'stdout_bytes':len(r.stdout),'stderr_bytes':len(r.stderr)}
 Path(str(stem)+'.stdout').write_bytes(r.stdout);Path(str(stem)+'.stderr').write_bytes(r.stderr)
 Path(str(stem)+'.json').write_text(json.dumps(row,indent=2)+'\n')
 return row,r.stdout,r.stderr

def parse(text):
 tokens=re.findall(r'\(|\)|[^\s()]+',text);i=0
 def term():
  nonlocal i
  t=tokens[i];i+=1
  if t!='(':return t
  xs=[]
  while tokens[i]!=')':xs.append(term())
  i+=1;return xs
 out=[]
 while i<len(tokens):out.append(term())
 return out

def atom(x):
 if x=='true':return True
 if x=='false':return False
 if isinstance(x,list) and x[0]=='-':return -int(x[1])
 return int(x)

def evaluate(x,env):
 if isinstance(x,str):
  if x in env:return env[x]
  return atom(x)
 op,*args=x
 xs=[evaluate(a,env) for a in args]
 if op=='select':return xs[0][xs[1]]
 if op=='store':return {**xs[0],xs[1]:xs[2]}
 if op=='and':return all(xs)
 if op=='or':return any(xs)
 if op=='not':return not xs[0]
 if op=='=':return xs[0]==xs[1]
 if op=='<':return xs[0]<xs[1]
 if op=='<=':return xs[0]<=xs[1]
 if op=='>=':return xs[0]>=xs[1]
 raise ValueError(('unknown exact formula operation',op))

def literal(env,which):
 def b(v):assert type(v) is bool;return 'true' if v else 'false'
 vals=env[which]
 for i in [0,1]:assert type(vals[i]) is int and 0<=vals[i]<256
 init=env[which+'_init'];read=env[which+'_read'];wr=env['write_authority']
 return '⟨'+', '.join([str(vals[0]),str(vals[1]),b(init[0]),b(init[1]),b(read[0]),b(read[1]),b(wr[0]),b(wr[1])])+'⟩'

def witnesses():
 names=['missing_initialization','alias_frame','bool_two','missing_stability','array_index_omission']
 lines=['import ByteLaws','open ByteLaws','namespace SolverWitnesses'];rows=[]
 for name in names:
  f=ROOT/'smt'/(name+'.generate.stdout');parsed=parse(f.read_text());assert parsed[0]=='sat'
  env={a:{} for a in ['source','current','source_init','source_read','current_init','current_read','write_authority']}
  for key,value in parsed[1]:
   value=atom(value)
   if isinstance(key,list):assert key[0]=='select';env[key[1]][int(key[2])]=value
   else:env[key]=value
  statements=parse((ROOT/'smt'/(name+'.smt2')).read_text())
  checks=[evaluate(t[1],env) for t in statements if t[0]=='assert']
  assert checks and all(v is True for v in checks),(name,checks)
  s,t=literal(env,'source'),literal(env,'current')
  lines += [f'def {name}_s : Memory := {s}',f'def {name}_t : Memory := {t}']
  if name=='missing_initialization':prop=f'intoWithoutInit {name}_s';unfold='intoWithoutInit'
  elif name=='alias_frame':
   a='true' if env['changed']==1 else 'false';frame='true' if env['framed']==1 else 'false'
   prop=f'WriteWithoutDisjoint {name}_s {a} {frame} {env["replacement"]}';unfold='WriteWithoutDisjoint'
  elif name=='bool_two':prop=f'BoolWrongLaw {name}_s {name}_t 3';unfold='BoolWrongLaw'
  elif name=='missing_stability':prop=f'BoolWithoutStability {name}_s {name}_t';unfold='BoolWithoutStability'
  else:prop=f'ArrayWrongLaw {name}_s {name}_t';unfold='ArrayWrongLaw'
  lines += [f'theorem {name}_countermodel : ¬ ({prop}) := by unfold {unfold}; decide',f'#print axioms {name}_countermodel']
  rows.append({'case':name,'source':env['source'],'current':env['current'],'valuation':env,'assertions_evaluated':len(checks),'all_original_smt_assertions_true':True,'solver_output_sha256':sha(f)})
 lines+=['end SolverWitnesses']
 (ROOT/'SolverWitnesses.lean').write_text('\n'.join(lines)+'\n');writej(ROOT/'countermodels.json',rows)

def main():
 logs=ROOT/'measurements';logs.mkdir(exist_ok=True)
 versions={}
 for name,binary,args in [('lean',LEAN,['--version']),('cvc5',CVC,['--version']),('carcara',CAR,['--version'])]:
  row,out,err=run([binary]+args,logs/(name+'.version'));assert row['exit']==0
  versions[name]={'binary_sha256':sha(binary),'version_stdout':out.decode(),'version_stderr':err.decode()}
 for name,path in [('lean_shared',LEAN.parent.parent/'lib/lean/libleanshared.dylib'),('lean_Init',LEAN.parent.parent/'lib/lean/Init.olean')]:
  versions[name]={'sha256':sha(path)}
 row,out,err=run([LEAN,'-o',ROOT/'ByteLaws.olean',ROOT/'ByteLaws.lean'],logs/'model-build')
 assert row['exit']==0 and b'sorryAx' not in out+err and not err,row
 witnesses();row,out,err=run([LEAN,ROOT/'SolverWitnesses.lean'],logs/'countermodel-replay')
 assert row['exit']==0 and b'sorryAx' not in out+err and not err,(row,out.decode(),err.decode())
 claims=[('into','(s : Memory)','IntoLaw s','into_direct s','.into s'),('write','(s : Memory) (a f : Addr) (v : Byte)','WriteLaw s a f v','write_direct s a f v','.write s a f v'),('boolean','(s t : Memory) (a : Addr)','BoolLaw s t a','bool_direct s t a','.boolean s t a'),('array','(s t : Memory)','ArrayLaw s t','array_direct s t','.array s t')]
 fixed=[('into','IntoLaw base','into_direct base','.into base'),('write','WriteLaw base false true 2','write_direct base false true 2','.write base false true 2'),('boolean','BoolLaw base base false','bool_direct base base false','.boolean base base false'),('array','ArrayLaw base base','array_direct base base','.array base base')]
 rows=[]
 for sample in range(3):
  for route in ['direct','reflected']:
   start=time.monotonic_ns();lines=['import ByteLaws','open ByteLaws']
   for name,args,goal,direct,query in claims:
    proof=direct if route=='direct' else f'check_sound ({query}) (all_reflected ({query}))'
    lines += [f'theorem universal_{name} {args} : {goal} := {proof}',f'#print axioms universal_{name}']
   for name,goal,direct,query in fixed:
    proof=direct if route=='direct' else f'check_sound ({query}) (by decide)'
    lines += [f'theorem concrete_{name} : {goal} := {proof}',f'#print axioms concrete_{name}']
   source=logs/f'{route}{sample}.lean';source.write_text('\n'.join(lines)+'\n');create=time.monotonic_ns()-start
   row,out,err=run([LEAN,source],logs/f'{route}{sample}.check')
   row.update(route=route,sample=sample,phase='Lean-check',source_creation_ns=create,source_bytes=source.stat().st_size)
   assert row['exit']==0 and b'sorryAx' not in out+err and not err,(row,out.decode(),err.decode());rows.append(row)
  for name in ['into_bytes','byte_write','bool_validate','array_validate']:
   original=ROOT/'smt'/(name+'.smt2');source=logs/f'{name}{sample}.smt2';proof=logs/f'{name}{sample}.alethe'
   start=time.monotonic_ns();source.write_bytes(original.read_bytes());create=time.monotonic_ns()-start
   row,out,err=run([CVC,'--proof-format-mode=alethe','--proof-granularity=dsl-rewrite-strict',source],logs/f'{name}{sample}.generate')
   row.update(route='cvc5-Alethe-Carcara',case=name,sample=sample,phase='proof-generation',source_creation_ns=create,source_bytes=source.stat().st_size,source_sha256=sha(source))
   assert row['exit']==0 and out.startswith(b'unsat\n'),row
   proof.write_bytes(out[len(b'unsat\n'):]);row['proof_bytes']=proof.stat().st_size;rows.append(row)
   row,out,err=run([CAR,'--no-color','check',proof,source],logs/f'{name}{sample}.check')
   row.update(route='cvc5-Alethe-Carcara',case=name,sample=sample,phase='strict-check',exact_status=out.decode().strip(),accepted=row['exit']==0 and out==b'valid\n');rows.append(row)
   if name=='into_bytes':assert row['accepted'],row
   else:
    assert not row['accepted'] and row['exit']!=0 and out==b'invalid\n' and b'error: the rule ' in err and b'was not found' in err,(row,out,err)
    row['classification']='named-export-rule-incompatible'
 # A proof of the narrowed problem is checked against the consumer full-domain
 # problem as a separate actual binding rejection, without accepting its holes.
 row,out,err=run([CAR,'--no-color','check',ROOT/'smt/wrong_narrow_domain.alethe',ROOT/'smt/bool_two.smt2'],logs/'wrong-domain-root')
 assert row['exit']!=0 and out==b'invalid\n',(row,out,err)
 writej(ROOT/'measurements.json',{'samples':rows,'tool_identities':versions,'wrong_domain_root':row,'scope':'Three process-inclusive samples, one tiny fixed workload and shared precompiled model. Reflected/direct proofs share definitions and direct generic lemmas; no algorithmic independence, cross-tool ranking, full Rust correspondence or native checker verification is claimed.'})
 print(json.dumps({'Lean_samples':6,'SMT_generate_check_pairs':12,'SAT_witnesses_checked':5,'wrong_domain_root_rejected':True,'strict_SMT_whole_laws_accepted':['into_bytes'],'strict_SMT_whole_laws_not_accepted':['byte_write','bool_validate','array_validate']},indent=2))

if __name__=='__main__':main()
