"""Independent retained-evidence review only: never starts a subprocess."""
import hashlib
import json
import re
import struct
from pathlib import Path

HERE = Path(__file__).resolve().parent
TASK = HERE.parents[2]
RAW = TASK / "work/execution/hol-replay"
SOURCES = TASK / "work/execution/cross-foundation-runtime/sources"
PACKAGE = RAW / "reports/hol-light-s2n-bignum-add-native-replay-b19af693"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def identity(path):
    b = path.read_bytes()
    return {"bytes": len(b), "sha256": digest(b)}


def require(value, explanation):
    if not value:
        raise RuntimeError(explanation)


def read_json(path):
    return json.loads(path.read_text())


def host_source(path):
    prefix = "/home/opam/anneal-cross-sources/"
    if path.startswith(prefix):
        return SOURCES / path[len(prefix):]
    prefix = "/home/opam/anneal-cross-output/audit/"
    require(path.startswith(prefix), "Unknown source origin: " + path)
    return RAW / "inputs" / path[len(prefix):]


def inlined_census(path):
    """Parse actual emitted events with a stack, separately from author's regex."""
    lines = path.read_text().splitlines()
    stack, entries, completed = [], [], []
    for i, line in enumerate(lines):
        if line.startswith("(* /") and line.endswith(" *)"):
            source = line[3:-3]
            if i + 1 < len(lines) and lines[i + 1] == '#1 "' + source + '"':
                stack.append(source)
                entries.append(source)
        if line == "(* update digest *)":
            require(bool(stack), "Digest without an active source")
            source = stack.pop()
            require(lines[i + 1] == "loaded_files := ", "Unexpected digest assignment")
            octets = lines[i + 2].split("[|", 1)[1].split("|]", 1)[0]
            md5 = bytes(int(x.strip()) for x in octets.split(";")).hex()
            name = json.loads(lines[i + 4].strip().split(",", 1)[0][1:])
            data = host_source(source).read_bytes()
            require(name == Path(source).name, "Digest source/basename mismatch")
            require(md5 == hashlib.md5(data).hexdigest(), "Digest differs from original source")
            completed.append({"path": source, "basename": name, "md5": md5})
    require(not stack, "Incomplete inlined source")
    return {"entries": entries, "completion": completed, "identity": identity(path)}


def elf(path):
    """Read bounded ELF64LE sections and symbol ranges without running a tool."""
    data = path.read_bytes()
    h = struct.unpack_from("<16sHHIQQQIHHHHHH", data)
    require(h[0][:7] == b"\x7fELF\x02\x01\x01", "ELF identity")
    require(h[8] == 64 and h[11] == 64, "ELF header sizes")
    sections = []
    for i in range(h[12]):
        pos = h[6] + i * h[11]
        require(pos + 64 <= len(data), "Section table bound")
        s = struct.unpack_from("<IIQQQQIIQQ", data, pos)
        require(s[1] == 8 or s[4] + s[5] <= len(data), "Section data bound")
        sections.append(s)
    names = sections[h[13]]
    strings = data[names[4]:names[4] + names[5]]

    def cstring(buf, start):
        return buf[start:buf.index(b"\0", start)].decode()

    text_sections = [(i, s) for i, s in enumerate(sections) if cstring(strings, s[0]) == ".text"]
    require(len(text_sections) == 1, "Unique .text section")
    text_index, text = text_sections[0]
    code = data[text[4]:text[4] + text[5]]
    symbols = []
    needed = []
    for s in sections:
        if s[1] == 2:
            table = sections[s[6]]
            strings2 = data[table[4]:table[4] + table[5]]
            require(s[9] == 24, "Symbol entry size")
            for pos in range(s[4], s[4] + s[5], s[9]):
                name, info, other, si, value, size = struct.unpack_from("<IBBHQQ", data, pos)
                if name and cstring(strings2, name) == "bignum_add":
                    symbols.append({"section_index": si, "offset": value, "size": size,
                                    "covers_text": si == text_index and value == 0 and size == len(code)})
        elif s[1] == 6:
            table = sections[s[6]]
            strings2 = data[table[4]:table[4] + table[5]]
            for pos in range(s[4], s[4] + s[5], s[9]):
                tag, val = struct.unpack_from("<qQ", data, pos)
                if tag == 1:
                    needed.append(cstring(strings2, val))
    interp = []
    for i in range(h[10]):
        p = struct.unpack_from("<IIQQQQQQ", data, h[5] + i * h[9])
        if p[0] == 3:
            interp.append(data[p[2]:p[2] + p[5]].rstrip(b"\0").decode())
    return {"identity": identity(path), "machine": h[2], "text_bytes": len(code),
            "text_sha256": digest(code), "bignum_add_symbols": symbols,
            "interpreter": interp, "needed": needed}, code


def positive_stream(data, core, selected):
    lines = data.decode().splitlines()
    theorems, ledgers, offsets, axioms, markers = {}, {}, [], [], {}
    active, body, axiom = None, [], None
    for line in lines:
        if line.startswith("ANNEAL_"):
            if axiom is not None:
                axioms.append("\n".join(axiom))
                axiom = None
            if line.startswith("ANNEAL_THEOREM_BEGIN "):
                require(active is None, "Nested theorem")
                active, body = line.split(" ", 1)[1], []
            elif line.startswith("ANNEAL_THEOREM_END "):
                require(line.split(" ", 1)[1] == active and active not in theorems, "Theorem delimiter/duplicate")
                theorems[active] = "\n".join(body)
                active = None
            elif line.startswith("ANNEAL_LOADED "):
                stage, value = line[len("ANNEAL_LOADED "):].split(" ", 1)
                name, md5 = value.rsplit(" ", 1)
                ledgers.setdefault(stage, []).append([json.loads(name), md5])
            elif line.startswith("ANNEAL_DECODE_NONE "):
                offsets.append(int(line.rsplit(" ", 1)[1]))
            elif line.startswith("ANNEAL_GLOBAL_AXIOM "):
                axiom = [line[len("ANNEAL_GLOBAL_AXIOM "):]]
            else:
                markers[line] = markers.get(line, 0) + 1
        elif active is not None:
            body.append(line)
        elif axiom is not None:
            axiom.append(line)
    require(active is None, "Unfinished theorem")
    if axiom is not None:
        axioms.append("\n".join(axiom))
    expected = read_json(RAW / "theorem-statements.json")
    require(theorems == expected, "Full theorem strings differ from retained statement data")
    require(len(theorems) == 71, "Theorem count")
    require(all(s.startswith("|-") for s in theorems.values()), "Closed printed sequents")
    some = [int(n.split("decode_")[1]) for n in theorems if n.startswith("BIGNUM_ADD_EXEC.decode_")]
    require(len(some) == 59 and len(offsets) == 122, "Decode counts")
    require(sorted(some + offsets) == list(range(181)), "Every decode slot exactly once")
    expected_core = [[x["basename"], x["md5"]] for x in reversed(core["completion"])]
    expected_after = [[x["basename"], x["md5"]] for x in reversed(selected["completion"][:-1])] + expected_core
    require(ledgers == {"core_before_proof": expected_core, "after_inner_audit": expected_after}, "Runtime ledgers")
    require(markers == {"ANNEAL_DECODE_ARRAY_LENGTH 181": 1, "ANNEAL_CHECK_AXIOMS_PASS": 1,
                        "ANNEAL_AUDIT_INNER_FINISHED": 1, "ANNEAL_CHECK_AXIOMS_OUTER_PASS": 1,
                        "ANNEAL_AUDIT_FINISHED": 1}, "Exact marker set/multiplicity")
    require(axioms == ["|- exists f. ONE_ONE f /\\ ~ONTO f", "|- forall P x. P x ==> P ((@) P)",
                       "|- forall t. (\\x. t x) = t"], "Complete global axiom statements")
    return {"theorem_count": len(theorems), "some_offsets": some, "none_offsets": offsets,
            "ledger_counts": {k: len(v) for k, v in ledgers.items()}, "axioms": axioms,
            "markers": markers, "all_actual_theorem_statements_match": True}


def main():
    require(HERE.resolve() == HERE and not HERE.is_symlink(), "Own physical destination")
    manifest_path = PACKAGE / "package-manifest.json"
    manifest_before = identity(manifest_path)
    report_before = identity(PACKAGE / "REPORT.md")
    manifest = read_json(manifest_path)
    file_paths = [row["path"] for row in manifest["files"]]
    require(len(file_paths) == len(set(file_paths)), "Duplicate package paths")
    actual = {str(p.relative_to(PACKAGE)) for p in PACKAGE.rglob("*") if p.is_file()}
    require(actual == set(file_paths) | {"package-manifest.json"}, "Package file set")
    for row in manifest["files"]:
        rel = Path(row["path"])
        require(not rel.is_absolute() and ".." not in rel.parts, "Unsafe inventory path")
        require(identity(PACKAGE / rel) == {"bytes": row["bytes"], "sha256": row["sha256"]}, "Manifest mismatch: " + row["path"])
    source_rows = []
    for line in (RAW / "inputs/source-sha256sum.txt").read_text().splitlines():
        sha, rel = line.split("  ", 1)
        require(digest((SOURCES / rel).read_bytes()) == sha, "Original source changed: " + rel)
        source_rows.append(rel)
    core = inlined_census(RAW / "artifacts/hol_lib_inlined.ml")
    selected = inlined_census(RAW / "artifacts/selected_inlined.ml")
    require(len(core["entries"]) == 47 and len(selected["entries"]) == 37, "Inclusion counts")
    original_selected = [p for p in selected["entries"] if "/anneal-cross-sources/" in p]
    require(len(original_selected) == 35 and not set(original_selected) & set(core["entries"]), "Distinct original closure")
    require(len(set(core["entries"] + original_selected)) == 82, "Actual original closure count")
    census = read_json(RAW / "logs/selected-census.stdout")
    for name, observed in [("hol_core", core), ("selected", selected)]:
        recorded = census[name]
        require(recorded["inclusion_order"] == observed["entries"], "Recorded source order")
        require([(r["basename"], r["md5"]) for r in recorded["digest_completion_order"]] ==
                [(r["basename"], r["md5"]) for r in observed["completion"]], "Recorded completion order")
        for row in recorded["inputs"]:
            require(identity(host_source(row["path"])) == {"bytes": row["bytes"], "sha256": row["sha256"]}, "Census source identity")
    raw_stdout = (RAW / "logs/positive.stdout").read_bytes()
    receipt = read_json(RAW / "logs/positive.json")
    require(receipt["returncode"] == 0, "Original positive status")
    for stream in ["stdout", "stderr"]:
        require(identity(RAW / ("logs/positive." + stream)) ==
                {"bytes": receipt[stream + "_bytes"], "sha256": receipt[stream + "_sha256"]}, "Positive stream receipt")
    parsed = positive_stream(raw_stdout, core, selected)
    a, code = elf(RAW / "artifacts/bignum_add.o")
    b, code_windows = elf(RAW / "artifacts/bignum_add.obj")
    native, _ = elf(RAW / "artifacts/selected.native")
    proof = (SOURCES / "s2n-bignum/x86/proofs/bignum_add.ml").read_text()
    literal = proof.split('define_assert_from_elf "bignum_add_mc" "x86/generic/bignum_add.o"', 1)[1].split("];;", 1)[0]
    literal = re.sub(r"\(\*.*?\*\)", "", literal, flags=re.S)
    literal = bytes(int(x, 16) for x in re.findall(r"0x[0-9a-f]+", literal))
    require(literal == code and len(code) == 185 and code[:4] == bytes.fromhex("f30f1efa"), "Embedded literal/code identity")
    require(len(code_windows) == 215, "Windows .text length")
    for item in [a, b]:
        require(item["machine"] == 62 and len(item["bignum_add_symbols"]) == 1 and item["bignum_add_symbols"][0]["covers_text"], "ELF subject range")
    statements = read_json(RAW / "theorem-statements.json")
    for name, value in [("bignum_add_mc", code), ("bignum_add_tmc", code[4:]),
                        ("bignum_add_windows_mc", code_windows), ("bignum_add_windows_tmc", code_windows[4:])]:
        printed = bytes(int(x) for x in re.findall(r"\bword (\d+)", statements[name]))
        require(printed == value, "Printed code theorem/object identity: " + name)
    for label in ["preproducer", "postproducer", "postpositive"]:
        data = read_json(RAW / ("logs/" + label + ".stdout"))
        require(data["original_files_checked"] == 23177 and data["original_mismatches"] == [], "Original identity inventory")
        require(len(data["tools"]) == 69 and len(data["compiler_libraries"]) == 2417 and len(data["generated_at_preflight"]) == 23, "Recorded identity counts")
    require((RAW / "logs/preproducer.stdout").read_bytes() == (RAW / "logs/postproducer.stdout").read_bytes() ==
            (RAW / "logs/postpositive.stdout").read_bytes(), "Before/after original/tool/library/module/object identity inventories")
    require((RAW / "logs/selected-census.stdout").read_bytes() == (RAW / "logs/final-census.stdout").read_bytes(), "Before/after complete output inventories")
    signature = read_json(RAW / "artifacts/signature-result.json")
    require(signature["returncode"] == 0 and len(signature["copied_inputs"]) == 690, "Signature generator outcome")
    for row in signature["copied_inputs"]:
        require(identity(SOURCES / "s2n-bignum" / row["path"]) == {"bytes": row["bytes"], "sha256": row["sha256"]}, "Signature input")
    for row in signature["outputs"]:
        arch = row["path"].split("/")[0]
        original = SOURCES / "s2n-bignum" / row["path"]
        generated = RAW / ("artifacts/generated-" + arch + "-subroutine_signatures.ml")
        require(generated.read_bytes() == original.read_bytes(), "Generated signatures differ")
        require(identity(generated) == {"bytes": row["bytes"], "sha256": row["sha256"]}, "Generated signatures identity")
    projection = read_json(PACKAGE / "support/public-path-projection.json")
    replacements = [(x.encode(), y.encode()) for x, y in projection["replacements"]]
    for row in projection["projected_files"]:
        rel = row["path"]
        require(rel.startswith("support/"), "Projection origin domain")
        original = RAW / rel[len("support/"):]
        require(original.is_file(), "Missing raw projection origin: " + rel)
        raw = original.read_bytes()
        public = raw
        for old, new in replacements:
            public = public.replace(old, new)
        require(digest(raw) == row["original_sha256"] and digest(public) == row["public_sha256"], "Projection hashes")
        require(public == (PACKAGE / rel).read_bytes(), "Projection byte relation")
    private_fields = []
    for row in manifest["files"]:
        p = PACKAGE / row["path"]
        if p.stat().st_size < 6 * 1024 * 1024:
            raw = p.read_bytes()
            for old, new in replacements:
                if old in raw:
                    private_fields.append({"path": row["path"], "prefix_label": new.decode(), "occurrences": raw.count(old)})
    require(identity(manifest_path) == manifest_before and identity(PACKAGE / "REPORT.md") == report_before, "Mutable candidate changed during static review")
    result = {"status": "SOURCE_AND_RETAINED_EVIDENCE_PASS_WITH_PUBLIC_METADATA_CORRECTION_REQUIRED; independent native replay NOT RUN",
              "review_phase": "preparation/source-and-evidence only", "report": report_before,
              "package_manifest": manifest_before, "package_files": len(file_paths),
              "package_bytes": sum(row["bytes"] for row in manifest["files"]),
              "original_source_manifest": identity(RAW / "inputs/source-sha256sum.txt"),
              "original_files_rehashed_on_host": len(source_rows),
              "HOL_s2n_original_files": sum(not p.startswith("opam-metadata/") for p in source_rows),
              "logical_original_source_closure": 82, "core": core, "selected": selected,
              "positive_receipt": receipt, "positive": parsed, "elfs": [a, b], "native_ELF": native,
              "retained_identity_observations": {"tools": 69, "compiler_library_files": 2417, "generated_module_and_objects": 23,
                 "output_files": len(census["output_files"]), "all_recorded_before_after_inventories_byte_equal": True},
              "signature_generator": {"returncode": 0, "inputs_rehashed": 690, "generated_outputs_equal_originals": 2},
              "public_projection": {"relation_verified_files": len(projection["projected_files"]),
                 "receipt_identity": identity(PACKAGE / "support/public-path-projection.json"),
                 "remaining_private_prefixes": private_fields, "disposition": "Parent separate public candidate correction; original frozen candidate untouched"},
              "axiom_scope": "Global policy allows only infinity/choice/eta. No per-theorem axiom dependency certificate.",
              "launch_count_this_review": 0, "runtime_queries_this_review": 0}
    (HERE / "static-review-results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ["status", "report", "package_manifest", "package_files", "package_bytes", "original_files_rehashed_on_host", "logical_original_source_closure", "public_projection", "launch_count_this_review"]}, indent=2))


if __name__ == "__main__":
    main()
