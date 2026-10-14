#!/usr/bin/env python3
"""Checker-admitted enum shape, owned translation of the selected WF branches.
No MiniRust executable and no Rust UB is run.
"""
import json
from pathlib import Path
ty={"size":1,"align":1,"discriminant_bits":8,
    "variants":{str(d):{"payload":{"kind":"Tuple","fields":[],"size":1,"align":1},
                        "tagger":[{"offset":0,"bits":8,"value":d}]} for d in (0,1)},
    "discriminator":{"Known":0}}
# Corresponding Type::check_wf checks, all naturally true for this specimen.
checks={
 "discriminants_representable":all(0<=int(d)<256 for d in ty["variants"]),
 "payloads_well_formed":all(not v["payload"]["fields"] and v["payload"]["align"]==1 for v in ty["variants"].values()),
 "same_variant_size":all(v["payload"]["size"]==ty["size"] for v in ty["variants"].values()),
 "variant_align_bounded":all(v["payload"]["align"]<=ty["align"] for v in ty["variants"].values()),
 "taggers_valid_and_in_bounds":all(0<=t["value"]<256 and t["offset"]+1<=ty["size"] for v in ty["variants"].values() for t in v["tagger"]),
 "known_discriminator_names_variant":str(ty["discriminator"]["Known"]) in ty["variants"]
}
# Tuple payload encode starts with Uninit, has no fields, then enum tagger writes.
def encode(d):return [ty["variants"][str(d)]["tagger"][0]["value"]]
# Discriminator::Known ignores bytes; selected payload ignores all padding.
def decode(bs):return {"variant":ty["discriminator"]["Known"],"payload":[]}
input_value={"variant":1,"payload":[]}
encoded=encode(input_value["variant"]);decoded=decode(encoded)
out={"status":"counterexample-confirmed" if all(checks.values()) and decoded!=input_value else "unexpected",
     "subject":"owned branch transcription; not executable MiniRust",
     "type":ty,"well_formed_branch_checks":checks,
     "input":input_value,"encoded":encoded,"decoded":decoded,
     "violated_claim":"decode(encode(value)) == Some(value) from checker-admitted WF alone",
     "extra_hypothesis_needed":"each variant tagger/discriminator pair returns that variant without altering payload"}
Path("enum-wf-counterexample.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out,indent=2))
raise SystemExit(0 if out["status"]=="counterexample-confirmed" else 1)

