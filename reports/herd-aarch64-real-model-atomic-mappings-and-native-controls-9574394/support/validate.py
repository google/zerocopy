"""Read preserved evidence only; no compiler, model runner, native call or network."""
from pathlib import Path
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
checks = []


def require(condition, label):
    checks.append({"check": label, "pass": bool(condition)})
    if not condition:
        raise ValueError(label)


def read(name):
    return (ROOT / name).read_text()


def sha(b):
    return hashlib.sha256(b).hexdigest()


def js(name):
    return json.loads(read(name))


def instructions(text):
    return [" ".join(l.split()).replace(", ", ",") for l in text.splitlines()
            if l.strip() and not l.lstrip().startswith((".", ";")) and not l.rstrip().endswith(":" )]


def asm_function(text, name):
    match = re.search(r"^_" + re.escape(name) + r":\n(.*?)(?=^\s*\.cfi_endproc|^\s*\.globl|^\s*\.private_extern|\Z)", text, re.M | re.S)
    if match is None:
        raise ValueError("missing assembly function " + name)
    return instructions(match.group(1))


def main():
    receipts = js("projection-receipts.json")
    by_public = {x["public_path"]: x for x in receipts["files"]}
    for f in receipts["files"]:
        b = (ROOT / f["public_path"]).read_bytes()
        require(sha(b) == f["public_sha256"] and len(b) == f["public_bytes"], "projection binding " + f["public_path"])
        require((f["raw_sha256"] == f["public_sha256"]) == (not f["substitutions"]), "projection disclosure " + f["public_path"])
    inv = js("source-inventory-audit.json")
    require(inv["source_inventory_entries"] == inv["container_verification_OK_lines"] == 6580
            and not inv["current_source_mismatches"], "6580 local/container source bindings")
    require(all(x["matches_original_inventory"] for x in inv["selected_preserved_source"]), "selected sources match pinned inventory")
    for item in js("evidence/input-identities.json"):
        require(sha((ROOT / "evidence/inputs" / item["path"]).read_bytes()) == item["sha256"], "litmus input binding " + item["path"])

    expected = {"MP-r0-a0": "Sometimes", "MP-r0-a1": "Sometimes", "MP-r0-p1": "Sometimes",
                "MP-r1-a0": "Sometimes", "MP-r1-a1": "Never", "MP-r1-p1": "Never",
                "SB": "Sometimes", "SB-STLR-LDAPR": "Sometimes", "SB-STLR-LDAR": "Never", "SB-dmb": "Never"}
    model_cases = []
    states_by_case = {}
    for name, status in expected.items():
        text = read("evidence/runs/" + name + ".stdout")
        run = js("evidence/runs/" + name + ".json")
        require(run["exit"] == 0, "herd exit " + name)
        require(run["argv"][-3:] == ["-model", "herd/libdir/aarch64.cat", "<HERD_INPUTS>/" + name + ".litmus"], "explicit pinned model invocation " + name)
        require(not any(s in run["argv"] for s in ["-variant", "-conf"]), "no explicit variant/config overrides " + name)
        observation = re.search(r"^Observation (\S+) (\S+) (\d+) (\d+)$", text, re.M)
        require(observation is not None and observation[1] == name and observation[2] == status, "herd observation " + name)
        positive, negative = int(observation[3]), int(observation[4])
        require((positive, negative) == ((1, 3) if status == "Sometimes" else (0, 3)), "herd witness counts " + name)
        states = []
        for left, right in re.findall(r"^\d+:X\d+=(\d+); \d+:X\d+=(\d+);$", text, re.M):
            states.append((int(left), int(right)))
        require(len(states) == positive + negative, "herd state count " + name)
        target = (1, 0) if name.startswith("MP-") else (0, 0)
        require((target in states) == (status == "Sometimes"), "model target membership " + name)
        states_by_case[name] = states
        model_cases.append({"case": name, "target": list(target), "model_status": status,
                            "states": [list(s) for s in states], "positive": positive, "negative": negative})
        require(read("evidence/runs/" + name + ".stderr") == "[WARNING] Running as root is not recommended\n", "herd stderr classified " + name)

    # Compare instruction variants directly in actual inputs, independent of output labels.
    for name in expected:
        lit = read("evidence/inputs/" + name + ".litmus")
        if name.startswith("MP-"):
            rel = "STLR" if "r1" in name else "STR"
            acq = "LDAPR" if name.endswith("p1") else ("LDAR" if name.endswith("a1") else "LDR")
            require(re.search(rel + r" W2,\[X3\]", lit) is not None and re.search(acq + r" W4,\[X3\]", lit) is not None,
                    "MP actual release/acquire instructions " + name)
        elif name == "SB-dmb":
            require(lit.count("DMB ISH") == 2, "actual two-sided DMB control")
        elif name.startswith("SB-STLR-"):
            require(lit.count("STLR W0") == 2 and lit.count(name.removeprefix("SB-STLR-")) == 3,
                    "actual store/load ordering control " + name)

    expected_asm = {
        "publish_relaxed": ["mov w8,#1", "str w8,[x0]", "str w8,[x1]", "ret"],
        "publish_release": ["mov w8,#1", "str w8,[x0]", "stlr w8,[x1]", "ret"],
        "observe_relaxed": ["ldr w8,[x1]", "ldr w9,[x0]", "orr x0,x9,x8,lsl #32", "ret"],
        "observe_acquire": ["ldapr w8,[x1]", "ldr w9,[x0]", "orr x0,x9,x8,lsl #32", "ret"],
        "store_then_load_relaxed": ["mov w8,#1", "str w8,[x0]", "ldr w0,[x1]", "ret"],
        "store_then_load_fenced": ["mov w8,#1", "str w8,[x0]", "dmb ish", "ldr w0,[x1]", "ret"],
        "store_then_load_release_acquire": ["mov w8,#1", "stlr w8,[x0]", "ldapr w0,[x1]", "ret"],
        "store_then_load_seqcst": ["mov w8,#1", "stlr w8,[x0]", "ldar w0,[x1]", "ret"]}
    compiled = read("evidence/atomic_wrappers.s")
    wrapper_map = {}
    for name, wanted in expected_asm.items():
        actual = asm_function(compiled, name)
        require(actual == wanted, "actual compiler instructions " + name)
        wrapper_map[name] = actual
    require('"target-cpu"="apple-m1"' in read("evidence/annotation_controls.ll"), "observed LLVM target cpu apple-m1")
    cfg = read("evidence/runs/rustc-cfg.stdout")
    require('target_feature="rcpc"' in cfg and 'target_pointer_width="64"' in cfg, "compiler default RCpc/64-bit cfg")
    require("f53b654a8882fd5fc036c4ca7a4ff41ce32497a6" in read("evidence/runs/rustc-version.stdout"), "May1 rustc actual commit")
    require(js("evidence/runs/final-rustc-atomic-asm.json")["source_sha256"] == by_public["evidence/atomic_wrappers.rs"]["raw_sha256"], "final eight-wrapper source binding")

    control_s = read("evidence/annotation_controls.s")
    control_ir = read("evidence/annotation_controls.ll")
    for name in ["complete", "wrong_nomem", "wrong_readonly"]:
        body = asm_function(control_s, "annotation_" + name)
        require(body.count("str w8,[x0]") == 2, "control actual Rust+asm stores " + name)
        require(("ldr w0,[x0]" in body) == (name == "complete"), "control reload distinction " + name)
        require(("mov w0,#7" in body) == (name != "complete"), "control folded result distinction " + name)
        ir = re.search(r"define[^\n]+@annotation_" + name + r"\(.*?\n\}", control_ir, re.S)[0]
        require(("ret i32 7" in ir) == (name != "complete"), "LLVM folded return " + name)
        require(("= load i32" in ir) == (name == "complete"), "LLVM reload distinction " + name)
    require("no binary linked or executed" in js("evidence/runs/annotation-compile.json")["policy"], "bad annotation compile-only policy")

    leaf_names = {"publish_relaxed": "publish_relaxed", "publish_release": "publish_release", "observe_relaxed": "observe_relaxed", "observe_acquire": "observe_acquire",
                  "sb_relaxed": "store_then_load_relaxed", "sb_ra": "store_then_load_release_acquire", "sb_sc": "store_then_load_seqcst", "sb_fence": "store_then_load_fenced"}
    native_asm = read("evidence/concurrent_assembly.s")
    exact = read("evidence/concurrent-leaves-exact.s")
    for name, source_name in leaf_names.items():
        require(asm_function(native_asm, "anneal_" + name) == expected_asm[source_name], "native leaf matches compiler mapping " + name)
        require(asm_function(exact, "anneal_" + name) == expected_asm[source_name], "unchanged extracted native leaf " + name)
    require(sha(exact.encode()) == receipts["native_leaf_extract"]["sha256"], "native exact extraction hash")
    raw_native = js("evidence/runs/concurrent-native.json")
    require(raw_native["exit"] == 0 and read("evidence/runs/concurrent-native.stderr") == "", "native run successful no diagnostics")
    require(raw_native["binary_sha256"] == receipts["excluded"][0]["sha256"], "original binary hash checked without execution")
    require(raw_native["assembly_sha256"] == by_public["evidence/concurrent_assembly.s"]["raw_sha256"], "native original assembly binding before path projection")
    require(raw_native["source_sha256"] == by_public["evidence/concurrent_assembly.rs"]["raw_sha256"] == js("evidence/runs/concurrent-build.json")["source_sha256"], "native source build/run binding")
    aliases = {"MP-relaxed": "MP-r0-a0", "MP-release-acquire": "MP-r1-p1", "SB-relaxed": "SB",
               "SB-release-acquire": "SB-STLR-LDAPR", "SB-seqcst": "SB-STLR-LDAR", "SB-fence": "SB-dmb"}
    native_cases = []
    lines = read("evidence/runs/concurrent-native.stdout").splitlines()
    require(len(lines) == 6, "six native run cases")
    for line in lines:
        m = re.fullmatch(r"([^:]+): rounds=(\d+) counts00_01_10_11=\[(\d+), (\d+), (\d+), (\d+)\]", line)
        require(m is not None, "native output grammar")
        name, rounds = m[1], int(m[2])
        counts = [int(m[i]) for i in range(3, 7)]
        model = aliases[name]
        require(rounds == sum(counts) == 10000, "native complete outcome count " + name)
        require(all(count == 0 or divmod(i, 2) in states_by_case[model] for i, count in enumerate(counts)), "native observed outcomes model-allowed " + name)
        require(counts[2 if name.startswith("MP-") else 0] == 0, "weak target not observed " + name)
        native_cases.append({"case": name, "model_case": model, "rounds": rounds, "counts00_01_10_11": counts,
                             "all_observed_states_model_allowed": True, "weak_target_observed": False})
    # Validate original captured-output identities even when a public projection changed display text.
    for path in sorted((ROOT / "evidence/runs").glob("*.json")):
        record = json.loads(path.read_text())
        if "exit" in record:
            require(record["exit"] == 0, "captured successful command " + path.stem)
        for stream in ["stdout", "stderr"]:
            key = stream + "_sha256"
            if key in record:
                dest = "evidence/runs/" + path.stem + "." + stream
                require(record[key] == by_public[dest]["raw_sha256"], "original output receipt " + path.stem + " " + stream)
    require(read("evidence/runs/host-cpu-query.stdout").strip() == "Apple M4 Pro", "observed host CPU receipt")
    require(read("evidence/runs/host-os.stdout").strip() == "27.0.1" and read("evidence/runs/host-process-arch.stdout").strip() == "arm64", "observed host OS/process architecture")
    require(read("evidence/runs/herd-version.stdout").strip() == "7.58+1, Rev: exported", "herd version receipt")
    result = {"role": "static audit of preserved evidence; no subject re-execution", "checks": checks,
              "all_passed": True, "model_cases": model_cases, "compiler_functions": wrapper_map, "native_cases": native_cases,
              "limits": ["Does not replay herd or rustc or execute native wrappers", "Does not prove a Rust/compiler/hardware refinement",
                         "No weak target was observed on hardware", "Plain external assembly accesses retain the raw-FFI semantic trust boundary"]}
    if "--write" in sys.argv:
        (ROOT / "static-validation.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"all_passed": True, "checks": len(checks), "model_cases": len(model_cases), "native_rounds": sum(c["rounds"] for c in native_cases)}))


if __name__ == "__main__":
    main()
