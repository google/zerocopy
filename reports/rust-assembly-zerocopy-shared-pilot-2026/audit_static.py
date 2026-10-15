#!/usr/bin/env python3
"""Owned static ELF/IR/CFI/version data checks; no executable is loaded/run."""
from pathlib import Path
import hashlib
import json
import re
import struct
import sys
sys.dont_write_bytecode = True
from bind_elf import ELF, WHOLE

ROOT = Path(__file__).resolve().parent / "compile-static"


def needs(text):
    out, current = {}, None
    if "Version needs section" not in text:
        return out
    for line in text.split("Version needs section", 1)[1].splitlines():
        match = re.search(r"File: (\S+)", line)
        if match:
            current = match.group(1); out[current] = []
        match = re.search(r"Name: (\S+)", line)
        if match and current:
            out[current].append(match.group(1))
    return out


def definitions(text):
    if "Version definition section" not in text:
        return []
    block = text.split("Version definition section", 1)[1].split("Version needs section", 1)[0]
    return re.findall(r"Name: (\S+)", block)


def main():
    checks, cases = [], []
    def check(ident, ok):
        checks.append({"id": ident, "pass": bool(ok)})
        if not ok:
            raise SystemExit("Static review disagreement: " + ident)
    bindings = json.loads((ROOT / "function-bindings.json").read_text())
    loader_files = {x["path"]: x for x in json.loads((ROOT / "inspection/runtime-library-files-read-only.stdout").read_text())}
    for image in bindings["images"]:
        arch, opt = image["arch"], image["opt"]
        stem = f"{arch}-O{opt}"
        elf = ELF(ROOT / "artifacts/build" / arch / f"O{opt}" / "pilot")
        main_symbol = elf.lookup("main", True)
        main_bytes, main_file_at = elf.function(main_symbol)
        text = (ROOT / "inspection" / (stem + "-image-disassembly.stdout")).read_text()
        symbols = {name: elf.lookup(name)["value"] for name in WHOLE}
        got_slots = {}
        if arch == "x86_64":
            for sec in elf.sections:
                if sec["type"] != 4 or sec["name"] != ".rela.dyn":
                    continue
                for at in range(sec["offset"], sec["offset"] + sec["size"], 24):
                    where, info, addend = struct.unpack_from("<QQq", elf.raw, at)
                    if info == 8:  # R_X86_64_RELATIVE, symbol0; loader adds base.
                        for name, address in symbols.items():
                            if addend == address:
                                got_slots[where] = name
        callsites = {name: [] for name in WHOLE}
        lines = text.splitlines()
        windows = []
        for i, line in enumerate(lines):
            match = re.match(r"\s*([0-9a-f]+):", line)
            if not match:
                continue
            pc = int(match.group(1), 16)
            off = pc - main_symbol["value"]
            if not (0 <= off < len(main_bytes)):
                continue
            name, route = None, None
            if arch == "aarch64" and "\tbl\t" in line:
                word = struct.unpack_from("<I", main_bytes, off)[0]
                check(stem + "-BL-encoding-" + hex(pc), word >> 26 == 0x25)
                delta = ((word & 0x3ffffff) ^ 0x2000000) - 0x2000000
                target = pc + 4 * delta
                for candidate, address in symbols.items():
                    if target == address:
                        name, route = candidate, {"kind": "direct-BL", "target": target}
            elif arch == "x86_64" and re.search(r"\bcall\s+QWORD PTR \[rip", line) and main_bytes[off:off + 2] == b"\xff\x15":
                slot = pc + 6 + struct.unpack_from("<i", main_bytes, off + 2)[0]
                if slot in got_slots:
                    name = got_slots[slot]
                    route = {"kind": "RIP-GOT-call-with-R_X86_64_RELATIVE", "slot": slot,
                             "base_relative_function": symbols[name], "runtime_loader_not_executed": True}
            if name:
                callsites[name].append({"pc": pc, **route})
                windows.append("\n" + name + "\n" + "\n".join(lines[max(0, i - 18):i + 6]) + "\n")
        if arch == "x86_64" and opt == 3:
            # One exact observed route, not a general register/CFG analysis.
            # The unsupported-route attempt is preserved under operational/.
            lea_pc, call_pc = 0xc9ce, 0xcb93
            lea_off, call_off = lea_pc - main_symbol["value"], call_pc - main_symbol["value"]
            check(stem + "-observed-R13-LEA-opcode", main_bytes[lea_off:lea_off + 3] == b"\x4c\x8d\x2d")
            lea_target = lea_pc + 7 + struct.unpack_from("<i", main_bytes, lea_off + 3)[0]
            check(stem + "-observed-R13-LEA-callee", lea_target == symbols["pilot_ptr"])
            check(stem + "-observed-R13-CALL", main_bytes[call_off:call_off + 3] == b"\x41\xff\xd5")
            check(stem + "-no-duplicate-ptr-route", not callsites["pilot_ptr"])
            callsites["pilot_ptr"].append({"pc": call_pc, "kind": "exact-observed-LEA-R13-then-CALL-R13",
                "definition_pc": lea_pc, "base_relative_target": lea_target,
                "preservation_premise": "Manual selected interval/CFG review plus R13 callee-save contract for intervening calls; no universal dataflow theorem."})
            for pc in [lea_pc, call_pc]:
                positions = [i for i, line in enumerate(lines) if re.match(r"\s*" + format(pc, "x") + r":", line)]
                check(stem + "-observed-route-text-" + hex(pc), len(positions) == 1)
                i = positions[0]
                windows.append("\npilot_ptr exact hoisted route\n" + "\n".join(lines[max(0, i - 5):i + 6]) + "\n")
        for name, calls in callsites.items():
            check(stem + "-C-callsite-" + name, len(calls) >= 1)
        (ROOT / ("callers-" + stem + ".txt")).write_text("".join(windows))
        ir = (ROOT / "artifacts/build" / arch / f"O{opt}" / "pilot.ll").read_text()
        declarations = [line for line in ir.splitlines() if line.startswith("declare ") and any("@" + n + "(" in line for n in WHOLE)]
        check(stem + "-ten-C-declarations", len(declarations) == 10 and not any("fastcc" in x for x in declarations))
        zc_ir = [line for line in ir.splitlines() if line.startswith("define ") and "_ZN14extended_pilot9zc_decode17h" in line]
        check(stem + "-zc-internal-ABI-signature", len(zc_ir) == 1 and ("(i64 %bytes.0.val)" in zc_ir[0] if opt == 3 else "ptr " in zc_ir[0]))
        frame_rows = []
        helper = next(f for f in image["functions"] if f["name"] == "pilot_call_helper")
        for kind in ["object", "image"]:
            s = helper[kind]; lo = s["symbol"]["value"]; hi = lo + s["bytes"]
            frames = (ROOT / "inspection" / f"{stem}-{kind}-frames.stdout").read_text()
            chunks = re.split(r"\n\n+", frames)
            selected = [c for c in chunks if (m := re.search(r"pc=([0-9a-f]+)\.\.([0-9a-f]+)", c)) and int(m.group(1), 16) == lo and int(m.group(2), 16) == hi]
            check(stem + "-" + kind + "-one-exact-helper-FDE", len(selected) == 1)
            fde = selected[0]
            if arch == "aarch64":
                check(stem + "-" + kind + "-CFI-A64", all(x in fde for x in ["DW_CFA_def_cfa_offset: 16", "r29 (x29) at cfa-16", "r30 (x30) at cfa-8", "DW_CFA_def_cfa_register: r29", "r31 (sp) ofs 0", "DW_CFA_restore: r30"]))
            else:
                check(stem + "-" + kind + "-CFI-SysV", "DW_CFA_def_cfa_offset: 16" in fde and "DW_CFA_def_cfa_offset: 8" in fde)
            cie_at = re.search(r"cie=([0-9a-f]+)", fde).group(1)
            cie = [c for c in chunks if re.match(r"0*" + cie_at.lstrip("0") + r" .* CIE", c)] if int(cie_at, 16) else [c for c in chunks if re.match(r"0+ .* CIE", c)]
            check(stem + "-" + kind + "-one-CIE", len(cie) == 1)
            check(stem + "-" + kind + "-CIE-return-rule", "Return address column: 30" in cie[0] if arch == "aarch64" else "r16 (rip) at cfa-8" in cie[0])
            frame_rows.append({"artifact": kind, "fde": fde, "cie": cie[0]})
        loader = "/lib/ld-linux-aarch64.so.1" if arch == "aarch64" else "/lib64/ld-linux-x86-64.so.2"
        metadata = (ROOT / "inspection" / (stem + "-image-metadata.stdout")).read_text()
        check(stem + "-PT_INTERP", "Requesting program interpreter: " + loader in metadata)
        actual_loader = loader if arch == "aarch64" else "/usr/x86_64-linux-gnu" + loader
        check(stem + "-loader-file-present", loader_files[actual_loader]["exists"])
        dynamic = (ROOT / "inspection" / (stem + "-image-dynamic.stdout")).read_text()
        required = needs(dynamic)
        library_versions = {}
        loader_base = "ld-linux-aarch64.so.1" if arch == "aarch64" else "ld-linux-x86-64.so.2"
        for name in [loader_base, "libc.so.6", "libgcc_s.so.1"]:
            libtext = (ROOT / "inspection" / (arch + "-library-" + name.replace(".", "-") + ".stdout")).read_text()
            library_versions[name] = definitions(libtext)
        needed = re.findall(r"\(NEEDED\).*\[([^]]+)\]", dynamic)
        for name in needed:
            check(stem + "-NEEDED-known-" + name, name in library_versions)
        for name, versions in required.items():
            check(stem + "-required-versions-" + name, name in library_versions and set(versions) <= set(library_versions[name]))
        cases.append({"arch": arch, "opt": opt, "callsites": callsites, "C_declarations": declarations,
                      "zc_decode_actual_IR_signature": zc_ir[0], "helper_frames": frame_rows,
                      "PT_INTERP": loader, "actual_loader_file": loader_files[actual_loader],
                      "NEEDED": needed, "needed_versions": required, "target_executed": False})
    result = {"status": "static-only", "checks_passed": len(checks), "checks": checks, "cases": cases,
              "limits": "Owned unverified readers/text checks; selected relocation/CFI/version interpretation, not loader/unwinder/ISA/Rust proof. No target or guest execution."}
    (ROOT / "static-checks.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"checks_passed": len(checks), "images": len(cases), "target_executed": False}))


if __name__ == "__main__":
    main()
