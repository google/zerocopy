#!/usr/bin/env python3
"""Controlled APFS symlink-pointer replacement and reader interleaving probe."""
import hashlib,json,os,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent/'publication-fixture'
ROOT.mkdir(exist_ok=True)
for old in ROOT.iterdir():
 if old.is_dir() and not old.is_symlink():
  import shutil; shutil.rmtree(old)
 elif old.is_symlink() or old.is_file(): old.unlink()
def sha(b): return hashlib.sha256(b).hexdigest()
def make_gen(name,complete=True):
 d=ROOT/name; d.mkdir()
 files={'Types.lean':f'-- generation {name}\ndef model : Nat := {name[-1]}\n','Funs.lean':f'-- generation {name}\nimport Types\ntheorem model_ok : model = {name[-1]} := by rfl\n','lake-manifest.json':json.dumps({'generation':name},sort_keys=True)+'\n','Module.olean':('olean:'+name+'\n').encode()}
 for file,content in files.items():
  if file=='Module.olean' and isinstance(content,bytes): (d/file).write_bytes(content)
  elif complete or file!='Funs.lean': (d/file).write_text(content)
 return d
def swap(name):
 tmp=ROOT/'current.next'
 if tmp.exists() or tmp.is_symlink(): tmp.unlink()
 tmp.symlink_to(name)
 os.replace(tmp,ROOT/'current')
def read_pair(base):
 return [(base/'Types.lean').read_text().splitlines()[0],(base/'Funs.lean').read_text().splitlines()[0],json.loads((base/'lake-manifest.json').read_text())['generation'],(base/'Module.olean').read_text().strip()]

gA=make_gen('gen-A'); gB=make_gen('gen-B'); swap('gen-A')
# Deliberately interleave per-file symlink resolution with pointer replacement.
first=(ROOT/'current'/'Types.lean').read_text().splitlines()[0]
swap('gen-B')
second=(ROOT/'current'/'Funs.lean').read_text().splitlines()[0]
manifest=json.loads((ROOT/'current'/'lake-manifest.json').read_text())['generation']
# Correct consumer resolves once and holds an immutable generation path.
swap('gen-A'); pinned=(ROOT/'current').resolve(strict=True)
pinned_first=(pinned/'Types.lean').read_text().splitlines()[0]
swap('gen-B')
pinned_second=(pinned/'Funs.lean').read_text().splitlines()[0]
# An incomplete unpublished stage must not change the current visible generation.
make_gen('gen-C',complete=False)
visible_before=(ROOT/'current').resolve(strict=True).name
visible_state=read_pair((ROOT/'current').resolve(strict=True))
# A pointer replacement by itself has no completeness gate: force C into view,
# observe its missing member, then restore B before recording the final pointer.
swap('gen-C')
forced_current=(ROOT/'current').resolve(strict=True).name
try:
 (ROOT/'current'/'Funs.lean').read_text()
 forced_missing=False
except FileNotFoundError:
 forced_missing=True
assert forced_current=='gen-C' and forced_missing
swap('gen-B')
# Verify final current resolves to complete B; existing reader can still use A.
final_path=(ROOT/'current').resolve(strict=True)
result={'filesystem':'APFS (workspace volume; macOS host)','pointer_type':'symlink replaced using os.replace','pointer_after':os.readlink(ROOT/'current'),'generation_a_sha256':{p.name:sha(p.read_bytes()) for p in gA.iterdir()},'generation_b_sha256':{p.name:sha(p.read_bytes()) for p in gB.iterdir()},'un-pinned_reader_interleaving':{'first_file':first,'second_file_after_swap':second,'manifest_generation_after_swap':manifest,'mixed_generation_observed':first!='-- generation '+manifest},'pinned_reader':{'resolved_path':'gen-A (resolved immutable directory)','first_file':pinned_first,'second_file_after_swap':pinned_second,'consistent_old_generation':pinned_first==pinned_second=='-- generation gen-A'},'incomplete_stage':{'stage':'gen-C missing Funs.lean','visible_generation_before':visible_before,'visible_state_before_forced_swap':visible_state,'forced_current':forced_current,'forced_publish_missing_file':forced_missing,'restored_current':final_path.name,'published_incomplete_at_end':final_path.name=='gen-C'},'old_generation_retained_after_swap':(gA/'Funs.lean').exists()}
assert result['un-pinned_reader_interleaving']['mixed_generation_observed']
assert result['pinned_reader']['consistent_old_generation']
assert result['incomplete_stage']['forced_publish_missing_file']
assert not result['incomplete_stage']['published_incomplete_at_end']
assert result['old_generation_retained_after_swap']
(ROOT/'publication-probe.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
