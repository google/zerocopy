"""Static public-data audit only: no compiler, linker, loader or native execution."""
from pathlib import Path
import hashlib
import json
import re
import sys
sys.dont_write_bytecode = True
import metadata_core as core

ROOT = Path(__file__).resolve().parents[1]
CHECKS = []


def check(ok, message):
    CHECKS.append({"check": message, "pass": bool(ok)})
    if not ok:
        raise ValueError(message)


def read(name):
    return (ROOT / name).read_text()


def js(name):
    return json.loads(read(name))


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main():
    receipts = js("projection-receipts.json")
    projected = {p["public_path"]: p for p in receipts["files"]}
    for entry in receipts["files"]:
        p = ROOT / entry["public_path"]
        b = p.read_bytes()
        check(sha(b) == entry["public_sha256"] and len(b) == entry["public_bytes"], "public binding " + entry["public_path"])
        if entry["binary_projection"]:
            check(p.stat().st_mode & 0o111 == 0, "image-data nonexecutable " + entry["public_path"])
            check(entry["public_bytes"] == entry["raw_bytes"] and len(entry["edits"]) == 4, "four equal-length N_OSO projections " + entry["public_path"])
            for edit in entry["edits"]:
                expected = bytes.fromhex(edit["replacement_hex"])
                check(b[edit["offset"]:edit["offset"] + edit["length"]] == expected, "declared N_OSO replacement bytes")
            for s in entry["unchanged_sections"]:
                check(sha(b[s["offset"]:s["offset"] + s["bytes"]]) == s["sha256"], "raw/public section identity " + entry["public_path"] + " " + s["name"])
    meta = js("evidence/metadata-results.json")
    raw_native = js("evidence/captures/native-positive.json")
    positive_path = "data-controls/positive-image.macho-data.bin"
    check(raw_native["exit"] == 0 and raw_native["image_sha256_before"] == raw_native["image_sha256_after"] == meta["image_sha256"] == projected[positive_path]["raw_sha256"], "ACTUAL executed raw image identity before/after; distinct from public projection")
    check(projected[positive_path]["public_sha256"] != meta["image_sha256"], "public image is declared projected DATA, never labeled executed raw image")
    image = (ROOT / positive_path).read_bytes()
    obj = (ROOT / "artifacts/specimen.o").read_bytes()
    im, om = core.macho(image), core.macho(obj)
    ib, ob = core.code_binding(image, im), core.code_binding(obj, om)
    check(ib == meta["image_binding"] and ob == meta["object_binding"], "actual object/raw/public code binding")
    active = core.active_unwind(image, im, ib["start"] + 20)
    check(active == meta["active_unwind"] and active["encoding"] == 0x03000014, "actual public-data active DWARF route equals original")
    fde = core.fde(image, im, active["encoding"] & 0xffffff)
    check(fde == meta["final_FDE"], "actual public-data FDE equals raw FDE")
    contexts = [core.recover(fde["rows"], offset) for offset in [0, 4, 8, 20, 28]]
    check(contexts == meta["five_recovery_contexts"] and all(c["matches"] for c in contexts), "five bounded recovery contexts")
    ep = core.normal_epilogue()
    for control in meta["data_controls"]:
        data = (ROOT / control["path"]).read_bytes()
        check(projected[control["path"]]["raw_sha256"] == control["sha256"], "original data-control identity " + control["name"])
        check(core.code_binding(data, core.macho(data))["bytes"] == ib["bytes"], "control code unchanged " + control["name"])
        diffs = [i for i, (a, b) in enumerate(zip(image, data)) if a != b]
        span = 4 if control["name"] == "missing-active-fde" else 1
        check(len(data) == len(image) and diffs and all(control["changed_file_offset"] <= i < control["changed_file_offset"] + span for i in diffs), "only declared metadata difference from projected positive " + control["name"])
        check(control["modeled_ordinary_epilogue"] == ep and ep["matches"], "calculated unchanged ordinary epilogue " + control["name"])
        if control["name"] == "missing-active-fde":
            try:
                core.fde(data, core.macho(data), 0x14)
            except ValueError as e:
                check(str(e) == "missing or out-of-range FDE", "expected missing selected FDE rejection")
            else:
                raise ValueError("missing FDE accepted")
        else:
            result = core.recover(core.fde(data, core.macho(data), 0x14)["rows"], 20)
            check(result == control["body_recovery"] and not result["matches"], "wrong body recovery distinguished " + control["name"])

    stdout = read("evidence/captures/native-positive.stdout")
    stderr = read("evidence/captures/native-positive.stderr")
    marker_line = "EXPECTED_SUBJECT_PANIC marker=0x4534305f554e5744 value=0x1122334455667788\n"
    check(stderr == marker_line * 2, "exactly two expected typed subject panic diagnostics; no unknown diagnostics")
    images = {}
    for label, address, base, offset, symbol, path in re.findall(r"^IMAGE label=(\S+) address=(0x[0-9a-f]+) image_base=(0x[0-9a-f]+) offset=(0x[0-9a-f]+) symbol=(\S+) image=(.+)$", stdout, re.M):
        images[label] = {"address": int(address, 16), "image_base": int(base, 16), "offset": int(offset, 16), "symbol": symbol, "image": path}
    check(set(images) == {"assembly-bounce", "rust-bounce", "platform-unwinder"}, "three actual loaded-image observations")
    for label, sym in [("assembly-bounce", "_anneal_unwind_bounce"), ("rust-bounce", "_anneal_rust_bounce")]:
        i = images[label]
        check(i["address"] - i["image_base"] == i["offset"] == core.symbol(im, sym)["value"] - active["image_base"], "loaded/static image-relative symbol binding " + label)
    check(images["platform-unwinder"]["image"] == "/usr/lib/system/libunwind.dylib" and images["platform-unwinder"]["symbol"] == "_Unwind_Backtrace", "observed platform unwinder image/symbol (no source-version proof)")
    cases = []
    for path, panic, hook, status, values in re.findall(r"^CASE_PASS path=(Rust|Assembly) panic=(false|true) counts=\[1, 1, 1, 12, ([01])\] trace_status=([05]) ips=\[(.*?)\]$", stdout, re.M):
        ips = [int(x.strip(), 16) for x in values.split(",")]
        key = "assembly-bounce" if path == "Assembly" else "rust-bounce"
        check(images[key]["address"] + 20 in ips, "live callback return PC in actual platform walk " + path + "/" + panic)
        cases.append({"path": path, "panic": panic == "true", "calls": 1, "callback_drops": 1, "outer_drops": 1,
                      "drop_order": 12, "expected_hooks": int(hook), "backtrace_status": int(status), "backtrace_ips": ips})
    check([(c["path"], c["panic"], c["expected_hooks"]) for c in cases] == [("Rust", False, 0), ("Rust", True, 1), ("Assembly", False, 0), ("Assembly", True, 1)], "four actual cases and exact call/drop/hook counts")
    check(re.findall(r"^NORMAL_RESULT path=(Rust|Assembly) value=0x336699cd00336699$", stdout, re.M) == ["Rust", "Assembly"], "both normal results match widened arithmetic oracle")
    check(re.findall(r"^EXPECTED_PAYLOAD_CONFIRMED path=(Rust|Assembly) marker=0x4534305f554e5744 value=0x1122334455667788$", stdout, re.M) == ["Rust", "Assembly"], "two exact typed payloads confirmed outside bounces")
    check(len(stdout.splitlines()) == 12 and stdout.splitlines()[-1] == "ALL_FOUR_CASES_PASSED", "complete native output grammar")

    # Captured hashes bind raw streams; the projection receipt binds public streams.
    for p in sorted((ROOT / "evidence/captures").glob("*.json")):
        record = json.loads(p.read_text())
        if "exit" in record:
            expected_exit = 1 if p.stem == "positive-compile" else 0
            check(record["exit"] == expected_exit, "captured status classified " + p.stem)
        for stream in ["stdout", "stderr"]:
            if "streams" in record:
                expected = record["streams"][stream]["sha256"]
            elif stream + "_sha256" in record:
                expected = record[stream + "_sha256"]
            else:
                continue
            target = "evidence/captures/" + p.stem + "." + stream
            check(projected[target]["raw_sha256"] == expected, "raw stream receipt " + p.stem + "/" + stream)
    sources = js("evidence/compile-outputs.json")["source_hashes"]
    for name, expected in sources.items():
        check(sha((ROOT / "support" / name).read_bytes()) == expected, "unchanged actually compiled source " + name)
    summary = {"status": "actual ONE positive native run completed; public validation is static data inspection only",
               "native_run_count": 1, "native_exit": 0, "native_raw_image_sha256": meta["image_sha256"],
               "public_positive_image_DATA_sha256": projected[positive_path]["public_sha256"],
               "public_projected_images_executed": False, "mutated_images_executed": False,
               "image_identity_observations": images, "actual_cases": cases, "positive_recovery_contexts": contexts,
               "metadata_only_controls": 3, "E41": "No universal unwinder/metadata/personality/Rust-resource proof",
               "checks": CHECKS, "all_passed": True}
    if "--write" in sys.argv:
        (ROOT / "native-results-and-static-validation.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({"all_passed": True, "static_checks": len(CHECKS), "actual_native_runs": 1,
                      "actual_native_cases": len(cases), "data_only_mutants": 3, "native_executed_by_validator": False}))


if __name__ == "__main__":
    main()
