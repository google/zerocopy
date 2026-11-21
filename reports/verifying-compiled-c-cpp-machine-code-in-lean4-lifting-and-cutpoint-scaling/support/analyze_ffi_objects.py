#!/usr/bin/env python3
"""
Empirical anatomy analyzer for GCC/G++ 15.2.0 compiled C/C++ .o files vs hand-written .S.

Compiles ffi_anatomy_suite.c, ffi_anatomy_cpp.cpp, and handwritten_leaf.S across multiple
optimization and hardening profiles, disassembles every function, extracts CFG structure
(instructions, basic blocks, direct/indirect edges, back-edges), stack-frame/spill/canary/
stack-clash metrics, ELF relocations, compiler-synthesized runtime dependencies, .eh_frame
CFA entries, DWARF v5 location-list coverage, and .BTF metadata.

Uses tempfile.TemporaryDirectory() so zero temporary files leak into /tmp.
"""
import json
import os
import re
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent

C_PROFILES = {
    "c_O2": ["gcc", "-O2", "-g", "-c"],
    "c_O3_avx2": ["gcc", "-O3", "-mavx2", "-g", "-c"],
    "c_hardened_O2": [
        "gcc", "-O2", "-fPIC", "-fstack-protector-strong",
        "-fstack-clash-protection", "-fcf-protection=full", "-g", "-c",
    ],
    "c_hardened_O3_avx2": [
        "gcc", "-O3", "-mavx2", "-fPIC", "-fstack-protector-strong",
        "-fstack-clash-protection", "-fcf-protection=full", "-g", "-c",
    ],
    "c_O2_btf": ["gcc", "-O2", "-gbtf", "-c"],
}

CPP_PROFILES = {
    "cpp_O2_exc": ["g++", "-O2", "-g", "-c"],
    "cpp_O2_noexc": ["g++", "-O2", "-fno-exceptions", "-fno-rtti", "-g", "-c"],
    "cpp_hardened_O2_exc": [
        "g++", "-O2", "-fPIC", "-fstack-protector-strong",
        "-fstack-clash-protection", "-fcf-protection=full", "-g", "-c",
    ],
    "cpp_O2_btf": ["g++", "-O2", "-gbtf", "-c"],
}

ASM_PROFILES = {
    "asm_handwritten": ["gcc", "-c"],
}

COND_JUMPS = {
    "je", "jne", "jz", "jnz", "ja", "jae", "jb", "jbe", "jg", "jge", "jl", "jle",
    "jo", "jno", "js", "jns", "jp", "jnp", "jpe", "jpo", "jc", "jnc", "jcxz", "jecxz", "jrcxz",
}
UNCOND_JUMPS = {"jmp", "jmpq"}
CALL_OPS = {"call", "callq"}
RET_OPS = {"ret", "retq"}
CALLEE_SAVED = {"rbx", "rbp", "r12", "r13", "r14", "r15"}
SIMD_PREFIXES = ("v", "movdqa", "movdqu", "movaps", "movups", "padd", "psub", "pxor", "punpck", "pshuf")


def run_cmd(cmd):
    res = subprocess.run(cmd, capture_output=True, text=True, check=True)
    return res.stdout


def parse_objdump_functions(obj_path):
    """Parse `objdump -d -r -M intel` into per-function instruction, CFG, stack, and reloc metrics."""
    out = run_cmd(["objdump", "-d", "-r", "-M", "intel", str(obj_path)])
    funcs = {}
    cur_fn = None
    cur_sec = None

    sec_re = re.compile(r"^Disassembly of section (\S+):")
    fn_re = re.compile(r"^([0-9a-f]+) <([^>]+)>:")
    ins_re = re.compile(r"^\s*([0-9a-f]+):\s+((?:[0-9a-f]{2}\s)+)\s*(.*)$")
    reloc_re = re.compile(r"^\s*([0-9a-f]+):\s+(R_X86_64_\S+)\s+(.*)$")

    for line in out.splitlines():
        m = sec_re.match(line)
        if m:
            cur_sec = m.group(1)
            cur_fn = None
            continue
        m = fn_re.match(line)
        if m:
            addr = int(m.group(1), 16)
            name = m.group(2)
            cur_fn = name
            funcs[name] = {
                "section": cur_sec,
                "start_addr": addr,
                "insns": [],
                "relocs": [],
            }
            continue
        if cur_fn is None:
            continue
        m = reloc_re.match(line)
        if m:
            funcs[cur_fn]["relocs"].append({
                "offset": int(m.group(1), 16),
                "type": m.group(2),
                "target": m.group(3).strip(),
            })
            continue
        m = ins_re.match(line)
        if m:
            addr = int(m.group(1), 16)
            raw_bytes = m.group(2).strip().split()
            asm_txt = m.group(3).strip()
            # Strip trailing `# comment`
            code_part = asm_txt.split("#", 1)[0].strip()
            parts = code_part.split(None, 1)
            if not parts:
                continue
            mnem = parts[0]
            ops = parts[1].strip() if len(parts) > 1 else ""
            # Handle prefixes like `notrack jmp`, `repz ret`, `data16 nop`, `cs nop`
            prefix = ""
            if mnem in {"notrack", "rep", "repz", "repne", "lock", "bnd", "data16", "cs"} and ops:
                prefix = mnem
                p2 = ops.split(None, 1)
                mnem = p2[0]
                ops = p2[1].strip() if len(p2) > 1 else ""
            funcs[cur_fn]["insns"].append({
                "addr": addr,
                "len": len(raw_bytes),
                "prefix": prefix,
                "mnem": mnem,
                "ops": ops,
                "full": asm_txt,
            })

    analyzed = {}
    for name, f in funcs.items():
        insns = f["insns"]
        if not insns:
            continue
        addr_set = {i["addr"] for i in insns}
        addr_to_idx = {i["addr"]: idx for idx, i in enumerate(insns)}
        fn_start = insns[0]["addr"]
        fn_end = insns[-1]["addr"] + insns[-1]["len"]

        # Map relocations by containing instruction address
        reloc_by_insn = {}
        for r in f["relocs"]:
            for idx, ins in enumerate(insns):
                if ins["addr"] <= r["offset"] < ins["addr"] + ins["len"]:
                    reloc_by_insn.setdefault(ins["addr"], []).append(r)
                    break

        leaders = {insns[0]["addr"]}
        direct_edges = []
        back_edges = 0
        indirect_jmps = []
        indirect_calls = []
        direct_calls = []
        tail_jumps = []
        stack_sub_bytes = 0
        pushed_callee_saved = []
        rsp_mem_refs = 0
        rbp_mem_refs = 0
        tls_canary_ops = 0
        endbr64_count = 0
        simd_insns = 0
        stack_clash_probe_ops = 0
        ret_count = 0
        ud2_or_trap = 0

        target_hex_re = re.compile(r"^([0-9a-f]+)\s+<([^>]+)>$")
        sub_rsp_re = re.compile(r"^rsp,\s*0x([0-9a-f]+)$|^rsp,\s*(\d+)$")

        for idx, ins in enumerate(insns):
            addr = ins["addr"]
            mnem = ins["mnem"]
            ops = ins["ops"]
            next_addr = insns[idx + 1]["addr"] if idx + 1 < len(insns) else None
            ins_relocs = reloc_by_insn.get(addr, [])

            if mnem == "endbr64":
                endbr64_count += 1
            if mnem in {"ud2", "int3"}:
                ud2_or_trap += 1
            if mnem in RET_OPS:
                ret_count += 1
            if mnem == "push" and ops in CALLEE_SAVED:
                pushed_callee_saved.append(ops)
            if mnem == "sub":
                sm = sub_rsp_re.match(ops)
                if sm:
                    val = int(sm.group(1), 16) if sm.group(1) else int(sm.group(2))
                    stack_sub_bytes += val
            if "[rsp" in ops:
                rsp_mem_refs += 1
            if "[rbp" in ops:
                rbp_mem_refs += 1
            if "fs:0x28" in ops:
                tls_canary_ops += 1
            if mnem == "or" and "[rsp" in ops and ops.endswith(",0x0"):
                stack_clash_probe_ops += 1
            if any(mnem.startswith(p) for p in SIMD_PREFIXES) and ("xmm" in ops or "ymm" in ops or "zmm" in ops):
                simd_insns += 1

            if mnem in COND_JUMPS:
                tm = target_hex_re.match(ops)
                if tm:
                    taddr = int(tm.group(1), 16)
                    if taddr in addr_set:
                        leaders.add(taddr)
                        direct_edges.append((addr, taddr))
                        if taddr <= addr:
                            back_edges += 1
                if next_addr is not None:
                    leaders.add(next_addr)
                    direct_edges.append((addr, next_addr))
            elif mnem in UNCOND_JUMPS:
                tm = target_hex_re.match(ops)
                if ins_relocs:
                    # Sibling tail call via relocation (e.g. R_X86_64_PLT32)
                    tail_jumps.append({
                        "addr": hex(addr),
                        "kind": "direct_reloc_tail",
                        "ops": ops,
                        "relocs": [r["target"] for r in ins_relocs],
                    })
                elif tm:
                    taddr = int(tm.group(1), 16)
                    if taddr in addr_set:
                        leaders.add(taddr)
                        direct_edges.append((addr, taddr))
                        if taddr <= addr:
                            back_edges += 1
                    else:
                        tail_jumps.append({
                            "addr": hex(addr),
                            "kind": "local_sym_tail",
                            "ops": ops,
                            "relocs": [],
                        })
                else:
                    # Indirect jmp (jump table or indirect tail call)
                    indirect_jmps.append({
                        "addr": hex(addr),
                        "prefix": ins["prefix"],
                        "ops": ops,
                    })
                if next_addr is not None:
                    leaders.add(next_addr)
            elif mnem in CALL_OPS:
                if ins_relocs:
                    direct_calls.append({
                        "addr": hex(addr),
                        "target": ins_relocs[0]["target"],
                        "reloc_type": ins_relocs[0]["type"],
                    })
                elif target_hex_re.match(ops):
                    direct_calls.append({
                        "addr": hex(addr),
                        "target": ops,
                        "reloc_type": "local",
                    })
                else:
                    indirect_calls.append({
                        "addr": hex(addr),
                        "ops": ops,
                    })

        # Compute basic block count from sorted leaders
        sorted_leaders = sorted(leaders)
        analyzed[name] = {
            "section": f["section"],
            "bytes": fn_end - fn_start,
            "insn_count": len(insns),
            "basic_blocks": len(sorted_leaders),
            "direct_cfg_edges": len(direct_edges),
            "back_edges": back_edges,
            "indirect_jmps": indirect_jmps,
            "indirect_calls": indirect_calls,
            "direct_calls": direct_calls,
            "tail_jumps": tail_jumps,
            "ret_count": ret_count,
            "endbr64_count": endbr64_count,
            "callee_saved_pushes": pushed_callee_saved,
            "stack_sub_bytes": stack_sub_bytes,
            "rsp_mem_refs": rsp_mem_refs,
            "rbp_mem_refs": rbp_mem_refs,
            "tls_canary_ops": tls_canary_ops,
            "stack_clash_probe_ops": stack_clash_probe_ops,
            "simd_insns": simd_insns,
            "reloc_count": len(f["relocs"]),
            "reloc_types": sorted({r["type"] for r in f["relocs"]}),
            "relocs": f["relocs"],
        }
    return analyzed


def parse_elf_metadata(obj_path):
    """Extract ELF sections, undefined external symbols, GNU properties, and .eh_frame FDE count."""
    sec_out = run_cmd(["readelf", "-SW", str(obj_path)])
    sections = []
    sec_re = re.compile(r"^\s*\[\s*(\d+)\]\s+(\S+)\s+(\S+)\s+[0-9a-f]+\s+[0-9a-f]+\s+([0-9a-f]+)")
    for line in sec_out.splitlines():
        m = sec_re.match(line)
        if m and m.group(2) != "NULL":
            sections.append({"name": m.group(2), "type": m.group(3), "size": int(m.group(4), 16)})

    sym_out = run_cmd(["readelf", "-sW", str(obj_path)])
    undef_syms = []
    for line in sym_out.splitlines():
        parts = line.split()
        if len(parts) >= 8 and parts[6] == "UND" and parts[0].endswith(":"):
            undef_syms.append(parts[7])

    notes_out = run_cmd(["readelf", "-n", str(obj_path)])
    gnu_props = [l.strip() for l in notes_out.splitlines() if "x86 feature:" in l or "Properties:" in l]

    eh_out = run_cmd(["readelf", "--debug-dump=frames-interp", str(obj_path)])
    fde_count = sum(1 for l in eh_out.splitlines() if " FDE " in l)
    cie_count = sum(1 for l in eh_out.splitlines() if " CIE " in l)
    cfa_rows = sum(1 for l in eh_out.splitlines() if re.match(r"^[0-9a-f]{16}\s+(rsp|rbp)\+", l))
    cfa_rbp_rows = sum(1 for l in eh_out.splitlines() if re.match(r"^[0-9a-f]{16}\s+rbp\+", l))

    rel_out = run_cmd(["readelf", "-rW", str(obj_path)])
    rodata_relocs = []
    in_ro = False
    for l in rel_out.splitlines():
        if "Relocation section '.rela.rodata" in l:
            in_ro = True
            continue
        if in_ro:
            if l.startswith("Relocation section") or not l.strip():
                in_ro = False
                continue
            parts = l.split()
            if len(parts) >= 5 and parts[2].startswith("R_X86_64_"):
                rodata_relocs.append({
                    "offset": parts[0],
                    "type": parts[2],
                    "target": " ".join(parts[4:]),
                })

    return {
        "sections": sections,
        "undef_syms": sorted(set(undef_syms)),
        "gnu_properties": gnu_props,
        "rodata_reloc_count": len(rodata_relocs),
        "rodata_relocs": rodata_relocs,
        "eh_frame": {
            "cie_count": cie_count,
            "fde_count": fde_count,
            "cfa_rows": cfa_rows,
            "cfa_rbp_rows": cfa_rbp_rows,
        },
    }


def parse_btf_section(obj_path, td_path):
    """Parse raw .BTF section if present; return None if absent."""
    sec_out = run_cmd(["readelf", "-SW", str(obj_path)])
    if ".BTF" not in sec_out:
        return {"present": False, "bytes": 0, "kinds": {}, "funcs": []}
    btf_bin = td_path / f"{obj_path.stem}.btf"
    run_cmd(["objcopy", "--dump-section", f".BTF={btf_bin}", str(obj_path)])
    data = btf_bin.read_bytes()
    magic, ver, flags, hdr_len, type_off, type_len, str_off, str_len = struct.unpack_from("<HBBIIIII", data, 0)
    strings = data[hdr_len + str_off : hdr_len + str_off + str_len]
    def get_str(off):
        end = strings.index(b"\0", off)
        return strings[off:end].decode("utf-8", errors="replace")
    KINDS = {
        0:"UNKN",1:"INT",2:"PTR",3:"ARRAY",4:"STRUCT",5:"UNION",6:"ENUM",7:"FWD",
        8:"TYPEDEF",9:"VOLATILE",10:"CONST",11:"RESTRICT",12:"FUNC",13:"FUNC_PROTO",
        14:"VAR",15:"DATASEC",16:"FLOAT",17:"DECL_TAG",18:"TYPE_TAG",19:"ENUM64"
    }
    pos = hdr_len + type_off
    end_pos = pos + type_len
    counts = {}
    funcs = []
    while pos < end_pos:
        name_off, info, size_or_type = struct.unpack_from("<III", data, pos)
        pos += 12
        vlen = info & 0xFFFF
        kind = (info >> 24) & 0x1F
        kname = KINDS.get(kind, str(kind))
        counts[kname] = counts.get(kname, 0) + 1
        name = get_str(name_off) if name_off else ""
        if kind == 12:
            funcs.append(name)
        if kind == 1: pos += 4
        elif kind == 3: pos += 12
        elif kind in (4, 5): pos += 12 * vlen
        elif kind == 6: pos += 8 * vlen
        elif kind == 13: pos += 8 * vlen
        elif kind == 14: pos += 4
        elif kind == 15: pos += 12 * vlen
        elif kind == 17: pos += 4
        elif kind == 19: pos += 12 * vlen
    return {
        "present": True,
        "magic": hex(magic),
        "version": ver,
        "bytes": len(data),
        "type_len": type_len,
        "str_len": str_len,
        "kinds": counts,
        "funcs": sorted(funcs),
    }


def parse_dwarf_stats(obj_path):
    """Run llvm-dwarfdump --statistics and inspect variable location coverage / DW_OP_entry_value."""
    stats_out = run_cmd(["llvm-dwarfdump", "--statistics", str(obj_path)])
    stats = json.loads(stats_out)
    info_out = run_cmd(["llvm-dwarfdump", "--debug-info", str(obj_path)])
    entry_val_cnt = info_out.count("DW_OP_entry_value")
    implicit_val_cnt = info_out.count("DW_OP_implicit_value") + info_out.count("DW_OP_stack_value")
    fbreg_cnt = info_out.count("DW_OP_fbreg")
    var_cnt = info_out.count("DW_TAG_variable")
    param_cnt = info_out.count("DW_TAG_formal_parameter")
    loc_attr_cnt = info_out.count("DW_AT_location")
    const_val_cnt = info_out.count("DW_AT_const_value")
    return {
        "llvm_dwarfdump_statistics": stats,
        "die_counts": {
            "DW_TAG_formal_parameter": param_cnt,
            "DW_TAG_variable": var_cnt,
            "DW_AT_location": loc_attr_cnt,
            "DW_AT_const_value": const_val_cnt,
            "DW_OP_entry_value": entry_val_cnt,
            "DW_OP_stack_or_implicit_value": implicit_val_cnt,
            "DW_OP_fbreg": fbreg_cnt,
        },
    }


def main():
    gcc_ver = run_cmd(["gcc", "--version"]).splitlines()[0]
    gpp_ver = run_cmd(["g++", "--version"]).splitlines()[0]
    results = {
        "toolchain": {"gcc": gcc_ver, "g++": gpp_ver},
        "profiles": {},
    }

    with tempfile.TemporaryDirectory(prefix="ffi_anatomy_") as td:
        td_path = Path(td)

        # 1. C profiles
        for prof, cmd_prefix in C_PROFILES.items():
            obj = td_path / f"{prof}.o"
            run_cmd(cmd_prefix + [str(HERE / "ffi_anatomy_suite.c"), "-o", str(obj)])
            entry = {
                "cmd": " ".join(cmd_prefix + ["ffi_anatomy_suite.c"]),
                "obj_bytes": obj.stat().st_size,
                "elf": parse_elf_metadata(obj),
                "functions": parse_objdump_functions(obj),
            }
            if "-g" in cmd_prefix:
                entry["dwarf"] = parse_dwarf_stats(obj)
            if "-gbtf" in cmd_prefix:
                entry["btf"] = parse_btf_section(obj, td_path)
            results["profiles"][prof] = entry

        # 2. C++ profiles
        for prof, cmd_prefix in CPP_PROFILES.items():
            obj = td_path / f"{prof}.o"
            run_cmd(cmd_prefix + [str(HERE / "ffi_anatomy_cpp.cpp"), "-o", str(obj)])
            entry = {
                "cmd": " ".join(cmd_prefix + ["ffi_anatomy_cpp.cpp"]),
                "obj_bytes": obj.stat().st_size,
                "elf": parse_elf_metadata(obj),
                "functions": parse_objdump_functions(obj),
            }
            if "-g" in cmd_prefix:
                entry["dwarf"] = parse_dwarf_stats(obj)
            if "-gbtf" in cmd_prefix:
                entry["btf"] = parse_btf_section(obj, td_path)
            results["profiles"][prof] = entry

        # 3. Hand-written .S baseline
        for prof, cmd_prefix in ASM_PROFILES.items():
            obj = td_path / f"{prof}.o"
            run_cmd(cmd_prefix + [str(HERE / "handwritten_leaf.S"), "-o", str(obj)])
            results["profiles"][prof] = {
                "cmd": " ".join(cmd_prefix + ["handwritten_leaf.S"]),
                "obj_bytes": obj.stat().st_size,
                "elf": parse_elf_metadata(obj),
                "functions": parse_objdump_functions(obj),
            }

    out_json = HERE / "ffi_anatomy_results.json"
    out_json.write_text(json.dumps(results, indent=2) + "\n")

    # Print compact summary table
    print(f"Wrote {out_json}")
    for prof, pdata in results["profiles"].items():
        print(f"\n=== {prof} (obj={pdata['obj_bytes']}B, undef={pdata['elf']['undef_syms']}) ===")
        if pdata["elf"]["gnu_properties"]:
            print("  GNU props:", pdata["elf"]["gnu_properties"])
        if "dwarf" in pdata:
            st = pdata["dwarf"]["llvm_dwarfdump_statistics"]
            dc = pdata["dwarf"]["die_counts"]
            print(
                f"  DWARF: vars={dc['DW_TAG_variable']} params={dc['DW_TAG_formal_parameter']} "
                f"AT_loc={dc['DW_AT_location']} entry_val={dc['DW_OP_entry_value']} "
                f"stack/implicit={dc['DW_OP_stack_or_implicit_value']} fbreg={dc['DW_OP_fbreg']} "
                f"params100%={st.get('#params with 100% of parent scope covered by DW_AT_location')}/"
                f"{st.get('#params processed by location statistics')} "
                f"(no-entry-val={st.get('#params - entry values with 100% of parent scope covered by DW_AT_location')}) "
                f"vars100%={st.get('#local vars with 100% of parent scope covered by DW_AT_location')}/"
                f"{st.get('#local vars processed by location statistics')}"
            )
        if "btf" in pdata:
            print(f"  BTF: {pdata['btf']}")
        for fn, m in pdata["functions"].items():
            print(
                f"  {fn:28s} insns={m['insn_count']:3d} BBs={m['basic_blocks']:2d} "
                f"back={m['back_edges']} ijmp={len(m['indirect_jmps'])} icall={len(m['indirect_calls'])} "
                f"dcall={len(m['direct_calls'])} tail={len(m['tail_jumps'])} ret={m['ret_count']} "
                f"push={len(m['callee_saved_pushes'])} sub_rsp={m['stack_sub_bytes']:4d} "
                f"rsp_mem={m['rsp_mem_refs']:2d} canary={m['tls_canary_ops']} "
                f"clash={m['stack_clash_probe_ops']} simd={m['simd_insns']:2d} "
                f"endbr={m['endbr64_count']} relocs={m['reloc_count']}"
            )


if __name__ == "__main__":
    main()
