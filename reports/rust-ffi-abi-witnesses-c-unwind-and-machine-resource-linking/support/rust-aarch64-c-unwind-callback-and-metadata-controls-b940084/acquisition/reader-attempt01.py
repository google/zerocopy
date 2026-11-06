"""Narrow owned Mach-O/CFI data reader, unverified. No image execution.

Reads actual positive object/image and writes three non-executable data copies.
Structural bounds follow the owned earlier byte-importer, extended for this
one explicit CIE/FDE instruction subset and selected compressed unwind page.
"""
from pathlib import Path
import copy
import hashlib
import json
import struct

ROOT = Path(__file__).resolve().parent
CODE = bytes.fromhex("fd7bbfa9fd030091f00300aae00301aa00023fd600040091fd7bc1a8c0035fd6")
SYMBOL = "_anneal_unwind_bounce"


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(b):
    return hashlib.sha256(b).hexdigest()


def unpack(fmt, b, at):
    require(0 <= at and at + struct.calcsize(fmt) <= len(b), "data bounds")
    return struct.unpack_from(fmt, b, at)


def macho(b):
    magic, cpu, subtype, kind, count, cmdbytes, flags, reserved = unpack("<IiiIIIII", b, 0)
    require(magic == 0xfeedfacf and cpu == 0x100000c and subtype == 0 and kind in [1, 2], "selected thin arm64, not arm64e")
    limit = 32 + cmdbytes
    require(limit <= len(b), "load command limit")
    sections, segments, symtab, at = [], [], None, 32
    for _ in range(count):
        cmd, length = unpack("<II", b, at)
        require(length >= 8 and at + length <= limit, "load command size")
        if cmd == 0x19:
            require(length >= 72, "segment size")
            name, vm, vmsize, fileoff, filesize, maxprot, initprot, nsects, segflags = unpack("<16sQQQQiiII", b, at + 8)
            segments.append({"name": name.rstrip(b"\0").decode(), "vm": vm, "vmsize": vmsize, "fileoff": fileoff, "filesize": filesize})
            require(72 + nsects * 80 <= length, "section table size")
            for i in range(nsects):
                name, seg, addr, size, off, align, reloff, nreloc, sf = unpack("<16s16sQQIIIII", b, at + 72 + i * 80)
                sections.append({"name": name.rstrip(b"\0").decode(), "segment": seg.rstrip(b"\0").decode(),
                                 "address": addr, "size": size, "offset": off, "align": align,
                                 "reloff": reloff, "nreloc": nreloc, "flags": sf})
        elif cmd == 2:
            require(length >= 24 and symtab is None, "symbol table command")
            symtab = unpack("<IIII", b, at + 8)
        at += length
    require(at == limit and symtab is not None, "load command exhaustion")
    symoff, nsyms, stroff, strsize = symtab
    require(symoff + nsyms * 16 <= len(b) and stroff + strsize <= len(b), "symbol table bounds")
    symbols = []
    for i in range(nsyms):
        ni, typ, sec, desc, value = unpack("<IBBHQ", b, symoff + i * 16)
        require(ni < strsize, "symbol name index")
        end = b.find(b"\0", stroff + ni, stroff + strsize)
        require(end >= 0, "symbol name terminator")
        symbols.append({"name": b[stroff + ni:end].decode(), "type": typ, "section": sec, "value": value})
    return {"kind": kind, "sections": sections, "segments": segments, "symbols": symbols}


def section(m, name):
    hits = [s for s in m["sections"] if s["name"] == name]
    require(len(hits) == 1, "selected section " + name)
    return hits[0]


def symbol(m, name):
    hits = [s for s in m["symbols"] if s["name"] == name]
    require(len(hits) == 1 and hits[0]["type"] & 0x0e == 0x0e, "selected defined symbol " + name)
    return hits[0]


def relocations(b, m, s):
    require(s["reloff"] + s["nreloc"] * 8 <= len(b), "relocation table bounds")
    rows = []
    for i in range(s["nreloc"]):
        address, fields = unpack("<II", b, s["reloff"] + i * 8)
        require(address < 0x80000000, "no scattered relocation")
        index = fields & 0xffffff
        external = (fields >> 27) & 1
        require(not external or index < len(m["symbols"]), "relocation symbol index")
        rows.append({"address": address, "type": fields >> 28, "length_log2": (fields >> 25) & 3,
                     "pcrel": (fields >> 24) & 1, "external": external,
                     "symbol": m["symbols"][index] if external else None, "index": index})
    return rows


def code_binding(b, m):
    start, end = symbol(m, SYMBOL), symbol(m, SYMBOL + "_end")
    require(start["section"] == end["section"] and end["value"] - start["value"] == 32, "32-byte explicit symbol range")
    s = m["sections"][start["section"] - 1]
    delta = start["value"] - s["address"]
    require(s["name"] == "__text" and s["segment"] == "__TEXT" and s["flags"] & 0x80000000, "instruction section identity")
    require(delta >= 0 and delta + 32 <= s["size"], "code section range")
    off = s["offset"] + delta
    require(b[off:off + 32] == CODE, "exact bounce instruction bytes")
    require(not any(delta <= r["address"] < delta + 32 for r in relocations(b, m, s)), "no relocation in bounce bytes")
    return {"start": start["value"], "end": end["value"], "file_offset": off, "bytes": CODE.hex(), "bytes_sha256": sha(CODE), "section": s}


def leb(b, at, signed=False):
    value, shift, start = 0, 0, at
    while True:
        require(at < len(b) and shift < 64, "LEB bounds")
        byte = b[at]
        at += 1
        value |= (byte & 0x7f) << shift
        shift += 7
        if not byte & 0x80:
            if signed and byte & 0x40:
                value -= 1 << shift
            return value, at, start


def program(b, begin, end, data_alignment=-8):
    at, pc, state, rows, ops = begin, 0, {"cfa": None, "registers": {}}, [], []
    while at < end:
        op_at = at
        opcode = b[at]
        at += 1
        op = {"at": op_at, "pc_offset": pc, "opcode": opcode}
        if opcode == 0:
            op["kind"] = "nop"
        elif opcode & 0xc0 == 0x40:
            pc += opcode & 0x3f
            op.update(kind="advance", to=pc)
        elif opcode & 0xc0 == 0x80:
            arg, at, arg_at = leb(b, at)
            reg = opcode & 0x3f
            state["registers"][str(reg)] = ["offset", arg * data_alignment]
            op.update(kind="offset", reg=reg, arg=arg, arg_at=arg_at)
        elif opcode == 0x0c:
            reg, at, _ = leb(b, at)
            offset, at, arg_at = leb(b, at)
            state["cfa"] = [reg, offset]
            op.update(kind="def_cfa", reg=reg, offset=offset, arg_at=arg_at)
        elif opcode == 0x0d:
            reg, at, _ = leb(b, at)
            require(state["cfa"] is not None, "CFA register needs prior rule")
            state["cfa"][0] = reg
            op.update(kind="def_cfa_register", reg=reg)
        elif opcode == 0x0e:
            offset, at, arg_at = leb(b, at)
            require(state["cfa"] is not None, "CFA offset needs prior rule")
            state["cfa"][1] = offset
            op.update(kind="def_cfa_offset", offset=offset, arg_at=arg_at)
        elif opcode == 0x08:
            reg, at, _ = leb(b, at)
            state["registers"][str(reg)] = ["same"]
            op.update(kind="same", reg=reg)
        else:
            raise ValueError("unsupported selected CFI opcode " + hex(opcode))
        require(at <= end, "CFI operand exhaustion")
        ops.append(op)
        if rows and rows[-1]["pc_offset"] == pc:
            rows[-1]["state"] = copy.deepcopy(state)
        else:
            rows.append({"pc_offset": pc, "state": copy.deepcopy(state)})
    return rows, ops


def fde(b, m, fde_offset):
    s = section(m, "__eh_frame")
    require(fde_offset + 8 <= s["size"], "FDE section bounds")
    at = s["offset"] + fde_offset
    length, cie_distance = unpack("<II", b, at)
    require(length > 0 and fde_offset + 4 + length <= s["size"], "missing or out-of-range FDE")
    cie_at = at + 4 - cie_distance
    cie_length, cie_id = unpack("<II", b, cie_at)
    require(cie_id == 0 and b[cie_at + 8] == 1, "selected CIE version1")
    end_aug = b.find(b"\0", cie_at + 9, cie_at + 4 + cie_length)
    require(end_aug >= 0 and b[cie_at + 9:end_aug] == b"zR", "selected CIE zR")
    code_align, p, _ = leb(b, end_aug + 1)
    data_align, p, _ = leb(b, p, True)
    return_reg, p, _ = leb(b, p)
    auglen, p, _ = leb(b, p)
    require((code_align, data_align, return_reg, auglen) == (1, -8, 30, 1) and b[p] == 0x10, "selected pointer/alignment CIE")
    initial, initial_ops = program(b, p + 1, cie_at + 4 + cie_length)
    require(initial[-1]["state"]["cfa"] == [31, 0], "CIE entry CFA")
    initial_field = at + 8
    encoded_pc, length_range = unpack("<qQ", b, initial_field)
    auglen, p, _ = leb(b, initial_field + 16)
    require(auglen == 0, "selected FDE no LSDA")
    rows, ops = program(b, p, at + 4 + length)
    raw_pc = s["address"] + initial_field - s["offset"] + encoded_pc
    return {"section": s, "fde_section_offset": fde_offset, "file_offset": at, "record_bytes": length + 4,
            "CIE_file_offset": cie_at, "CIE_RA_column": return_reg, "CIE_pointer_encoding": "pcrel native64 (0x10)",
            "initial_field_section_offset": initial_field - s["offset"], "encoded_pc": encoded_pc,
            "unrelocated_or_final_pc": raw_pc, "range": length_range, "rows": rows, "ops": ops}


def active_unwind(b, m, address):
    s = section(m, "__unwind_info")
    data = b[s["offset"]:s["offset"] + s["size"]]
    version, common_off, common_count, pers_off, pers_count, index_off, index_count = unpack("<7I", data, 0)
    require(version == 1 and index_count >= 2, "unwind_info version/index")
    common = list(unpack("<" + "I" * common_count, data, common_off))
    entries = []
    for i in range(index_count - 1):
        base, page, lsda = unpack("<III", data, index_off + 12 * i)
        kind, ep, nc, encp, nenc = unpack("<IHHHH", data, page)
        require(kind == 3, "selected compressed second-level page")
        encs = list(unpack("<" + "I" * nenc, data, page + encp))
        for j in range(nc):
            word, = unpack("<I", data, page + ep + j * 4)
            ei = word >> 24
            require(ei < common_count + len(encs), "unwind encoding index")
            enc = common[ei] if ei < common_count else encs[ei - common_count]
            entries.append({"function_offset": base + (word & 0xffffff), "encoding": enc})
    sentinel, _, _ = unpack("<III", data, index_off + 12 * (index_count - 1))
    image_base = [seg["vm"] for seg in m["segments"] if seg["fileoff"] == 0 and seg["filesize"] > 0]
    require(len(image_base) == 1, "preferred image header VM base")
    entries.sort(key=lambda x: x["function_offset"])
    for i, entry in enumerate(entries):
        end = entries[i + 1]["function_offset"] if i + 1 < len(entries) else sentinel
        if image_base[0] + entry["function_offset"] <= address < image_base[0] + end:
            return {**entry, "range_end_offset": end, "image_base": image_base[0], "section": s,
                    "personality_index": (entry["encoding"] >> 28) & 3, "has_lsda": bool(entry["encoding"] & 0x40000000)}
    raise ValueError("no active unwind entry")


def recover(rows, pc):
    S, F, R = 0x1000, 0x3000, 0x8004
    memory = {S - 24: 0xdeadbeef, S - 16: F, S - 8: R}
    if pc < 4:
        regs = {31: S, 29: F, 30: R}
    elif pc < 8:
        regs = {31: S - 16, 29: F, 30: R}
    elif pc < 28:
        regs = {31: S - 16, 29: S - 16, 30: 0x9014}
    else:
        regs = {31: S, 29: F, 30: R}
    eligible = [r for r in rows if r["pc_offset"] <= pc]
    require(eligible, "recovery row exists")
    state = eligible[-1]["state"]
    cfa_reg, off = state["cfa"]
    cfa = regs[cfa_reg] + off
    out = {"sp": cfa}
    for reg, name in [(29, "fp"), (30, "lr")]:
        rule = state["registers"][str(reg)]
        out[name] = regs[reg] if rule[0] == "same" else memory.get(cfa + rule[1])
    return {"pc_offset": pc, "recovered": out, "expected": {"sp": S, "fp": F, "lr": R},
            "matches": out == {"sp": S, "fp": F, "lr": R}}


def main():
    outputs = json.loads((ROOT / "compile-outputs.json").read_text())["outputs"]
    for e in outputs:
        require(sha((ROOT / e["path"]).read_bytes()) == e["sha256"], "compiled output identity")
    obj = (ROOT / "build/specimen.o").read_bytes()
    image = (ROOT / "build/specimen").read_bytes()
    om, im = macho(obj), macho(image)
    ob, ib = code_binding(obj, om), code_binding(image, im)
    require(ib["bytes"] == ob["bytes"], "object/final bounce identity")
    active = active_unwind(image, im, ib["start"] + 20)
    require(active["function_offset"] == ib["start"] - active["image_base"] and
            active["range_end_offset"] == ib["end"] - active["image_base"], "active range equals explicit bounce range")
    require(active["encoding"] & 0x0f000000 == 0x03000000 and not active["has_lsda"] and active["personality_index"] == 0, "actual transparent DWARF route")
    fde_off = active["encoding"] & 0xffffff
    selected = fde(image, im, fde_off)
    require(selected["unrelocated_or_final_pc"] == ib["start"] and selected["range"] == 32, "final resolved FDE PC/range")
    expected_rows = [
        {"pc_offset": 0, "state": {"cfa": [31, 0], "registers": {"29": ["same"], "30": ["same"]}}},
        {"pc_offset": 4, "state": {"cfa": [31, 16], "registers": {"29": ["offset", -16], "30": ["offset", -8]}}},
        {"pc_offset": 8, "state": {"cfa": [29, 16], "registers": {"29": ["offset", -16], "30": ["offset", -8]}}},
        {"pc_offset": 28, "state": {"cfa": [31, 0], "registers": {"29": ["same"], "30": ["same"]}}}]
    require(selected["rows"] == expected_rows, "actual CFI rows match independent calculation")
    contexts = [recover(selected["rows"], pc) for pc in [0, 4, 8, 20, 28]]
    require(all(c["matches"] for c in contexts), "five recovery contexts")
    original_object_fde = fde(obj, om, 0x14)
    erel = relocations(obj, om, section(om, "__eh_frame"))
    pair = [r for r in erel if r["address"] == original_object_fde["initial_field_section_offset"]]
    require(len(pair) == 2 and [r["type"] for r in pair] == [1, 0], "object FDE subtractor/unsigned pair")
    require(pair[1]["symbol"]["name"] == SYMBOL and pair[0]["symbol"]["name"].startswith("ltmp"), "object FDE relocation target and base")
    require(all(r["external"] == 1 and r["length_log2"] == 3 and r["pcrel"] == 0 for r in pair), "selected native64 external relocation pair")
    P = original_object_fde["section"]["address"] + original_object_fde["initial_field_section_offset"]
    resolved_object_pc = P + original_object_fde["encoded_pc"] + pair[1]["symbol"]["value"] - pair[0]["symbol"]["value"]
    require(resolved_object_pc == ob["start"], "owned object relocation resolves to actual code start")
    compact = section(om, "__compact_unwind")
    compact_raw = obj[compact["offset"]:compact["offset"] + 32]
    require(unpack("<QI", compact_raw, 0) == (0, 32) and unpack("<I", compact_raw, 12)[0] == 0x03000000, "object DWARF marker and range")
    # Generate/interpret only non-executable owned image-data copies.
    controls = []
    outdir = ROOT / "data-controls"
    outdir.mkdir(exist_ok=True)
    modifications = [
        ("wrong-cfa-offset", next(op["arg_at"] for op in selected["ops"] if op["kind"] == "def_cfa_offset"), 8),
        ("wrong-lr-offset", next(op["arg_at"] for op in selected["ops"] if op["kind"] == "offset" and op["reg"] == 30), 2)]
    for name, offset, value in modifications:
        changed = bytearray(image)
        before = changed[offset]
        changed[offset] = value
        cb = code_binding(changed, macho(changed))
        require(cb["bytes"] == ib["bytes"], "mutant instruction identity")
        mutant_fde = fde(changed, macho(changed), fde_off)
        result = recover(mutant_fde["rows"], 20)
        require(not result["matches"], "expected metadata negative distinguished")
        path = outdir / (name + ".macho-data.bin")
        path.write_bytes(changed)
        require(path.stat().st_mode & 0o111 == 0, "data mutant not executable")
        controls.append({"name": name, "path": path.relative_to(ROOT).as_posix(), "sha256": sha(changed),
                         "changed_file_offset": offset, "original_byte": before, "new_byte": value,
                         "instruction_bytes_identical": True, "body_recovery": result,
                         "modeled_ordinary_epilogue_restores_caller": True, "native_execution": False})
    missing = bytearray(image)
    missing[selected["file_offset"]:selected["file_offset"] + 4] = b"\0\0\0\0"
    require(code_binding(missing, macho(missing))["bytes"] == ib["bytes"], "missing FDE code identity")
    try:
        fde(missing, macho(missing), fde_off)
    except ValueError as e:
        require(str(e) == "missing or out-of-range FDE", "expected missing-FDE diagnostic")
    else:
        raise ValueError("missing FDE unexpectedly accepted")
    path = outdir / "missing-active-fde.macho-data.bin"
    path.write_bytes(missing)
    require(path.stat().st_mode & 0o111 == 0, "missing FDE data not executable")
    controls.append({"name": "missing-active-fde", "path": path.relative_to(ROOT).as_posix(), "sha256": sha(missing),
                     "changed_file_offset": selected["file_offset"], "instruction_bytes_identical": True,
                     "active_route_is_dwarf": True, "expected_owned_lookup_failure": "missing or out-of-range FDE",
                     "modeled_ordinary_epilogue_restores_caller": True, "native_execution": False})
    result = {"reader_status": "owned unverified bounded data decoder/interpreter, not a verified loader/unwinder",
              "object_sha256": sha(obj), "image_sha256": sha(image), "object_binding": ob, "image_binding": ib,
              "active_unwind": active, "final_FDE": selected, "five_recovery_contexts": contexts,
              "object_FDE_relocation": {"pair": pair, "raw_tool_PC": original_object_fde["unrelocated_or_final_pc"],
                                        "resolved_object_PC": resolved_object_pc,
                                        "explanation": "Object dwarf display has not applied the symbol subtractor/unsigned relocation pair; use resolved final image for active PC binding"},
              "data_controls": controls, "no_native_execution": True, "no_mutant_compilation_link_loading_execution": True}
    (ROOT / "metadata-results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"all_selected_checks_pass": True, "positive_recovery_contexts": len(contexts),
                      "metadata_only_controls": len(controls), "active_encoding": hex(active["encoding"]),
                      "bounce_start": hex(ib["start"]), "native_executed": False}))


if __name__ == "__main__":
    main()
