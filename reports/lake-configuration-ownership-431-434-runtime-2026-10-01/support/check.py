#!/usr/bin/env python3
"""Offline verifier of R423 Lake ownership snapshots; never runs Lake."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def tree(path):
    out={}
    for p in sorted(path.rglob("*")):
        if p.is_symlink():continue
        st=p.stat()
        # Files are copied into packages and worktrees, so inode/ctime are
        # local observation data, not portable replay invariants. Validate the
        # retained bytes and shape here; the original metadata remains in the
        # raw results.json snapshots.
        is_dir=p.is_dir()
        item={"type":"dir" if is_dir else "file","sha256":None if is_dir else sha(p)}
        if not is_dir:item["size"]=st.st_size
        out[str(p.relative_to(path))]=item
    return out
x=json.loads((ROOT/"results.json").read_text())
assert x["schema"]==1 and x["status"]=="completed" and len(x["calls"])==8
assert {str(p.relative_to(ROOT/"fixture")):sha(p) for p in (ROOT/"fixture").rglob("*") if p.is_file()}==x["fixture_sha256"]
commits={"v4.31.0":"68218e876d2a38b1985b8590fff244a83c321783",
         "v4.34.1":"5045d0056413266e57c625dcd7c365b10e377c52"}
for version in commits:
    ident=x["identities"][version]
    assert commits[version] in ident["lean_version"] and version.lstrip("v") in ident["lake_version"]
    assert ident["lake_sha256"]=={"v4.31.0":"58261a1a2fa1a362376c71e02ca854a093e71cc5e6ea64b287a931cb2565273d",
                                  "v4.34.1":"c8c24f1398162ab4004e2a869952d8469f54293651151feaad4526f2b8474c6e"}[version]
    assert ident["lean_sha256"]=="1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554"
    s=x["snapshots"][version]
    assert s["load-a"]["a"]==s["load-b"]["a"]
    assert s["load-a"]["shared"]==s["load-b"]["shared"]==s["reload-a"]["shared"]==s["load-toml"]["shared"]
    assert ".lake" not in s["before"]["shared"] and s["load-a"]["shared"][".lake"]["type"]=="dir"
    assert not [p for p,z in s["load-toml"]["shared"].items() if p.startswith(".lake/") and z["type"]=="file"]
    a=s["load-a"]["a"];b=s["load-b"]["b"];t=s["load-toml"]["t"]
    assert all(p in a for p in (".lake/config/0/lakefile.olean",".lake/config/0/lakefile.olean.trace",
                               ".lake/config/1/lakefile.olean",".lake/config/1/lakefile.olean.trace"))
    assert all(p in b for p in (".lake/config/0/lakefile.olean",".lake/config/1/lakefile.olean",
                               ".lake/config/2/lakefile.olean",".lake/config/2/lakefile.olean.trace"))
    assert ".lake/config/1/lakefile.olean" in t and ".lake/config/0" not in t
    assert not [p for p in a if p.endswith(".lock")]
    lock=s["reload-a"]["a"][".lake/config/1/lakefile.olean.lock"]
    assert lock["type"]=="file" and lock["size"]==0
    for p,z in a.items():
        if p.startswith(".lake/config/") and z["type"]=="file":
            assert z["sha256"]==s["reload-a"]["a"][p]["sha256"]
            if p.startswith(".lake/config/0/"):
                assert z==s["reload-a"]["a"][p]
            else:
                assert z["mtime_ns"]!=s["reload-a"]["a"][p]["mtime_ns"]
    assert a[".lake/config/1/lakefile.olean"]["inode"]!=s["reload-a"]["a"][".lake/config/1/lakefile.olean"]["inode"]
    traces={name:s[stage+"-traces"][name] for name,stage in (("a","load-a"),("b","load-b"),("t","load-toml"))}
    for name,path,idx in (("a",".lake/config/1/lakefile.olean.trace",1),
                          ("b",".lake/config/2/lakefile.olean.trace",2),
                          ("t",".lake/config/1/lakefile.olean.trace",1)):
        assert traces[name][path]["idx"]==idx and traces[name][path]["name"]=="shared"
        assert traces[name][path]["leanHash"]==commits[version]
    assert not any(p.startswith(".lake/config/0") for p in t)
    run=ROOT/"runs"/version.replace(".","_")
    for name in ("a","b","t","shared","filler"):
        expected_tree={p:{"type":z["type"],"sha256":z["sha256"],**({"size":z["size"]} if z["type"]=="file" else {})}
                       for p,z in s["load-toml"][name].items()}
        assert tree(run/name)==expected_tree,(version,name)
    expected={"v4.31.0":("716e38bf6d4d6b05927ab8359cf9a5ec46455a6fee53e81626e177926efc30f9","239465b996551391b07ff67b3f99a2a03e6170d38167034a244fdfdb47197ea1"),
              "v4.34.1":("4afb906bc3a42bf095f75fccc889f9644d995ad3d576d26a4925e57f7700d389","5c9bf313df6dcd985f71010f055a44cbae0a55fe8ae94ca42ff9156b2bc35c89")}[version]
    assert a[".lake/config/1/lakefile.olean.trace"]["sha256"]==expected[0]
    assert b[".lake/config/2/lakefile.olean.trace"]["sha256"]==expected[1]
    labels=[c["label"] for c in x["calls"] if c["version"]==version]
    assert labels==["load-a","load-b","reload-a","load-toml"]
samples=[z for c in x["calls"] for z in [c["admission"]]+c["live_samples"]]
assert all(c["returncode"]==0 and c["abort"] is None for c in x["calls"])
assert all(c["admission"]["reclaimable_fraction"]>.20 and c["admission"]["disk_free_bytes"]>10*1024**3 for c in x["calls"])
assert all(z["reclaimable_fraction"]>=.18 and z["disk_free_bytes"]>10*1024**3 and z["scratch_bytes"]<=100*1024**2 for z in samples)
assert all(z.get("group_rss_kib",0)<=1200*1024 for z in samples)
assert round(min(z["reclaimable_fraction"] for z in samples)*100,2)==21.87
assert min(z["disk_free_bytes"] for z in samples)==13065048064
print("PASS: fixture, exact versions, A/B/T config locations, no cross-workspace rewrite, and guards")
