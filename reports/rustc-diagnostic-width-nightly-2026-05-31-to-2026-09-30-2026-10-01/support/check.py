#!/usr/bin/env python3
"""Offline R562 check; reads raw JSON and fixture, never runs rustc."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
x=json.loads((ROOT/"results.json").read_text())
assert x["schema"]==1 and x["status"]=="completed" and x["fixture_status"]=="reconstructed_not_original_ui_bytes"
assert len(x["cells"])==15 and sha(ROOT/"fixture/Width.rs")==x["fixture_sha256"]
versions=("nightly-2026-05-31","stable-1.98.1","nightly-2026-09-30")
commits={"nightly-2026-05-31":"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1",
         "stable-1.98.1":"48a229ceaefd4985c50990b14116b6d856af0985",
         "nightly-2026-09-30":"5c543b0b8c73c7b72bc8284ced4fb22ead15734d"}
binary_hashes={"nightly-2026-05-31":"2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc",
               "stable-1.98.1":"2814fb55fb9cfb3eef5848a8104d77e3de7fd95394661144a12ee90cd4405340",
               "nightly-2026-09-30":"29f8ccc9aa7b0d8798eda854fa7f0e4ba3867c8c336b87d52dbb3b24b3f0878d"}
expected={
    "nightly-2026-05-31":{40:"`Vec<...>` is not an iterator",100:"`Vec<BTreeMap<String, Vec<Option<...>>>>` is not an iterator"},
    "stable-1.98.1":{40:"`Vec<...>` is not an iterator",100:"`Vec<BTreeMap<String, Vec<Option<...>>>>` is not an iterator"},
    "nightly-2026-09-30":{40:"`Vec<_>` is not an iterator",100:"`Vec<BTreeMap<String, Vec<Option<_>>>>` is not an iterator"}}
for v in versions:
    assert commits[v] in x["compiler_versions"][v]
    assert x["compiler_sha256"][v] == binary_hashes[v]
def cell(v,mode,width):
    matches=[a for a in x["cells"] if a["version"]==v and a["mode"]==mode and a["width"]==width]
    assert len(matches)==1
    return matches[0]
def raw(c,stream):
    path=ROOT/c[stream+"_path"]
    assert sha(path)==c[stream+"_sha256"]
    return path.read_bytes()
def msgs(c):
    data=raw(c,"stderr")
    rows=[json.loads(line) for line in data.splitlines()]
    assert all(row.get("$message_type")=="diagnostic" for row in rows)
    return rows
for c in x["cells"]:
    assert c["returncode"]==1 and c["elapsed_seconds"]<10
    assert c["admission"]["reclaimable_fraction"]>.20 and c["admission"]["disk_free_bytes"]>1024**3 and c["admission"]["scratch_bytes"]<100*1024**2
    assert raw(c,"stdout")==b""
    for p,h in c["output_files"].items():assert sha(ROOT/"out"/p)==h
    if c["mode"]=="human":
        out=raw(c,"stderr")
        assert b"error[E0277]" in out and b"error[E0308]" in out and b"\x1b[" not in out
    else:assert len(msgs(c))== (10 if c["mode"]=="json-short" else 12)
for v in versions:
    for width in (40,100):
        m=msgs(cell(v,"json",width))
        e30=[z for z in m if (z.get("code") or {}).get("code")=="E0308"]
        e27=[z for z in m if (z.get("code") or {}).get("code")=="E0277"]
        assert len(e30)==8 and len(e27)==1
        assert all(z["message"]=="mismatched types" and z["level"]=="error" for z in e30)
        assert all((s["line_start"],s["line_end"])==(11,11) for z in e30 for s in z["spans"] if s["is_primary"])
        z=e27[0];assert z["message"]==expected[v][width]
        primary=[s for s in z["spans"] if s["is_primary"]]
        assert len(primary)==1 and (primary[0]["line_start"],primary[0]["column_start"],primary[0]["line_end"],primary[0]["column_end"])==(12,22,12,31)
        assert primary[0]["label"]==z["message"]
        assert any(child["level"]=="help" and "Iterator" in child["message"] for child in z["children"])
        assert c["argv"][1].endswith("/fixture/Width.rs")
        assert primary[0]["file_name"]==c["argv"][1]
        assert z["rendered"]
    assert msgs(cell(v,"json",40))[-1]["level"]=="failure-note"
    assert msgs(cell(v,"json-short",100))[-1]["message"]=="aborting due to 9 previous errors"
    short=next(z for z in msgs(cell(v,"json-short",100)) if (z.get("code") or {}).get("code")=="E0277")
    assert short["message"]==expected[v][100] and len(short["rendered"].splitlines())==1
    ordinary=next(z for z in msgs(cell(v,"json",100)) if (z.get("code") or {}).get("code")=="E0277")
    assert len(ordinary["rendered"].splitlines())>1
    assert raw(cell(v,"human",40),"stderr")!=raw(cell(v,"human",100),"stderr")
assert x["initial_admission"]["reclaimable_fraction"]>.20 and x["initial_admission"]["disk_free_bytes"]>1024**3
print("PASS: exact fixture/raw bytes, 15 exits, JSON messages/spans, width/version differences, guards")
