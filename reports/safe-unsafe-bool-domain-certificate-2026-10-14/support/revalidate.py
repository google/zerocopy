import argparse,hashlib,json,pathlib,shutil,subprocess,time
p=argparse.ArgumentParser();p.add_argument('--lean-bin',required=True);p.add_argument('--rustc',required=True);p.add_argument('--out',required=True);a=p.parse_args()
src=pathlib.Path(__file__).resolve().parent;dest=pathlib.Path(a.out).resolve()
if dest.exists():raise SystemExit('Use a fresh scratch directory')
expected={'api.rs': '416eded2d8d38c4de7212091446c16ffca3bd49f7aa266d02ec718d07c1038fa', 'native.rs': '84ce24c7bac022708e885fdbf831ab35db11f35512e6acd9f9b83513a463f684', 'ApiCertificate.lean': '64d5e8b8df69fe8a6874a32d6d19e6cab6253af1c186ba5238a6e428d652f914'}
for name,digest in expected.items():
 if hashlib.sha256((src/name).read_bytes()).hexdigest()!=digest:raise SystemExit('Selected source changed: '+name)
shutil.copytree(src,dest);rows=[]
for name,argv in [('kernel',[a.lean_bin,'ApiCertificate.lean']),('compile',[a.rustc,'--edition=2021','native.rs','-o','native']),('native',[str(dest/'native')])]:
 t=time.monotonic();r=subprocess.run(argv,cwd=dest,capture_output=True,text=True)
 (dest/(name+'.stdout')).write_text(r.stdout);(dest/(name+'.stderr')).write_text(r.stderr)
 rows.append(dict(stage=name,exit_code=r.returncode,seconds=time.monotonic()-t))
 if r.returncode or 'sorryAx' in r.stdout:raise SystemExit('Rejected phase: '+name)
 if name=='native' and r.stdout!='all_native_u8_inputs=256; accepted=2; rejected=254\n':raise SystemExit('Native result differs')
(dest/'revalidation.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows))
