"""Replay only owned sources in a fresh caller-selected directory; no installs."""
from pathlib import Path
import argparse, json, os, runpy, shutil

def main():
 p=argparse.ArgumentParser()
 for x in ['lean','cvc5','carcara','out']:p.add_argument('--'+x,required=True,type=Path)
 a=p.parse_args();src=Path(__file__).resolve().parent;out=a.out.resolve()
 out.mkdir(exist_ok=False)
 for name in ['ByteLaws.lean','run_smt.py','verify_and_measure.py']:
  shutil.copyfile(src/name,out/name)
 # Required caller selections; no personal/default path or source rewriting.
 os.environ['BYTE_LAWS_LEAN']=str(a.lean.resolve())
 os.environ['BYTE_LAWS_CVC5']=str(a.cvc5.resolve())
 os.environ['BYTE_LAWS_CARCARA']=str(a.carcara.resolve())
 smt=runpy.run_path(str(out/'run_smt.py'),run_name='owned_replay_smt')
 smt['main']()
 verify=runpy.run_path(str(out/'verify_and_measure.py'),run_name='owned_replay_verify')
 verify['main']()
 print(json.dumps({'replayed':True,'scope':'Owned finite ByteLaws, generated exact formulas, strict result matrix, SAT-to-Lean reification and3small cost samples; external tool/quotation/native premises retained.'}))

if __name__=='__main__':main()
