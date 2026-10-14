#!/usr/bin/env python3
"""Prepare a portable offline replay tree; does not fetch or execute a compiler."""
from pathlib import Path
import argparse,hashlib,tarfile,shutil,json
parser=argparse.ArgumentParser();parser.add_argument('--work',required=True)
args=parser.parse_args();work=Path(args.work).resolve()
if work.exists() and any(work.iterdir()):raise SystemExit('work directory must be empty')
work.mkdir(parents=True,exist_ok=True)
support=Path(__file__).resolve().parent
expected={'minirust.tar.gz':'0b808e620296bde607ed6cf74642f39a023c2dbf9fe842d458fdfb69392913c0','specr.tar.gz':'7e39738319f77a43fd0ce8e185888306b3a777f7b3f9d3234ec1802b9da5e220'}
for name,digest in expected.items():
 archive=support/'archives'/name
 if hashlib.sha256(archive.read_bytes()).hexdigest()!=digest:raise SystemExit('source archive digest mismatch')
 with tarfile.open(archive) as t:
  if not all(not m.issym() and not m.islnk() and not m.name.startswith('/') and '..' not in Path(m.name).parts for m in t.getmembers()):raise SystemExit('unsafe source archive member')
  t.extractall(work/'source')
mini=work/'source/minirust-d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed'
specr=work/'source/specr-15200eb5e676e2ee91f43bd79e674f8fc32e5348'
harness=work/'harness';harness.mkdir()
for crate in ['miniutil','minitest']:shutil.copytree(mini/'tooling'/crate,harness/crate)
(harness/'Cargo.toml').write_text('[workspace]\nresolver = "2"\nmembers = ["miniutil", "minitest"]\nexclude = ["minirust-rs"]\n')
shutil.copyfile(support/'locks/harness.Cargo.lock',harness/'Cargo.lock')
generated=harness/'minirust-rs';(generated/'src').mkdir(parents=True)
for source in (support/'generated').glob('*.rs'):shutil.copyfile(source,generated/'src'/source.name)
(generated/'Cargo.toml').write_text('[package]\nname = "minirust-rs"\nversion = "0.1.0"\nedition = "2024"\n[dependencies]\nlibspecr = {path="../../source/specr-15200eb5e676e2ee91f43bd79e674f8fc32e5348/libspecr"}\nserde = {version="1.0", features=["derive"]}\n')
owned=work/'owned-probe';(owned/'src').mkdir(parents=True)
shutil.copyfile(support/'actual_core_probe.rs',owned/'src/main.rs')
shutil.copyfile(support/'locks/owned.Cargo.lock',owned/'Cargo.lock')
(owned/'Cargo.toml').write_text('[package]\nname="owned-core-probe"\nversion="0.1.0"\nedition="2021"\n[workspace]\n[dependencies]\nminirust-rs={path="../harness/minirust-rs"}\nminiutil={path="../harness/miniutil"}\n')
print(json.dumps({'work':str(work),'status':'prepared; no compiler or network execution','harness':str(harness/'Cargo.toml'),'owned_probe':str(owned/'Cargo.toml')},indent=2))

