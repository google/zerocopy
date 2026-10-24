"""Unverified, data-only Mach-O binding reader. No execution is authorized here.

CLI: bind_artifacts.py OBJECT LINKED positive|control METADATA REFERENCE|none
Source/CLI schemas and limitations are in reader-source-notes.md.
"""
import hashlib
import json
from pathlib import Path
import struct
import sys

PROTOCOL = "0c67a8622d53245a76801c59f60243a33abeafd84a0d25526f1e5a45a72d1775"
LEAF, CALLER = "_anneal_exchange", "_anneal_call"
FILE_CAP, CALLER_CAP, RECORD_CAP = 64 << 20, 16384, 65536
META_KEYS = {"protocol_sha256", "cell", "variant", "source_sha256",
             "object_sha256", "linked_sha256", "object_caller_bytes",
             "linked_caller_bytes", "object_call_offset", "linked_call_offset"}
REF_KEYS = {"approved", "protocol_sha256", "cell", "source_sha256",
            "object_sha256", "linked_sha256", "leaf_hex"}


class Rejected(Exception):
    def __init__(self, stage, detail=""):
        super().__init__(stage)
        self.stage, self.detail = stage, str(detail)[:240]


def need(ok, stage, detail=""):
    if not ok:
        raise Rejected(stage, detail)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def span(blob, offset, length, stage):
    need(type(offset) is int and type(length) is int and
         0 <= offset <= len(blob) and 0 <= length <= len(blob) - offset,
         stage, (offset, length, len(blob)))
    return blob[offset:offset + length]


def read_file(name, limit):
    path = Path(name)
    need(path.is_absolute() and path.is_file(), "input-path", name)
    with path.open("rb") as stream:
        data = stream.read(limit + 1)
    need(len(data) <= limit, "input-size", name)
    return data


def unique(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, "json-duplicate-key", key)
        result[key] = value
    return result


def read_record(name):
    raw = read_file(name, RECORD_CAP)
    def bad_constant(value):
        raise Rejected("json-constant", value)
    try:
        record = json.loads(raw.decode("utf-8"), object_pairs_hook=unique,
                            parse_constant=bad_constant)
    except (UnicodeError, json.JSONDecodeError) as error:
        raise Rejected("json-format", type(error).__name__)
    need(type(record) is dict, "record-object")
    return record, sha(raw)


def hash_string(value):
    return type(value) is str and len(value) == 64 and all(
        c in "0123456789abcdef" for c in value)


def metadata(record, variant):
    need(set(record) == META_KEYS, "metadata-schema")
    need(record["protocol_sha256"] == PROTOCOL, "protocol-identity")
    need(variant in ("positive", "control") and record["variant"] == variant,
         "variant-identity")
    need(record["cell"] in (variant + "-o0", variant + "-o3"), "cell-identity")
    for key in ("source_sha256", "object_sha256", "linked_sha256"):
        need(hash_string(record[key]), "metadata-hash", key)
    for kind in ("object", "linked"):
        length, offset = record[kind + "_caller_bytes"], record[kind + "_call_offset"]
        need(type(length) is int and 16 <= length <= CALLER_CAP and length % 4 == 0,
             "caller-candidate-length", kind)
        need(type(offset) is int and offset >= 0 and offset % 4 == 0 and
             offset + 8 <= length, "call-offset", kind)


def c_name(raw):
    end = raw.find(b"\0")
    return (raw if end < 0 else raw[:end]).decode("ascii")


def parse(blob, expected_type):
    need(len(blob) >= 32, "header-short")
    magic, cpu, subtype, kind, ncmd, command_bytes, flags, reserved = struct.unpack_from(
        "<IiiIIIII", blob)
    need(magic == 0xfeedfacf and cpu == 0x100000c and subtype == 0,
         "mach-o-target", (magic, cpu, subtype))
    need(kind == expected_type and reserved == 0, "mach-o-header")
    need(0 < ncmd <= 8192 and command_bytes <= 16 << 20, "load-command-count")
    span(blob, 32, command_bytes, "load-command-bounds")
    image = {"blob": blob, "sha256": sha(blob), "kind": kind, "flags": flags,
             "command_bytes": command_bytes, "segments": [], "sections": [],
             "commands": [], "linkedit": [], "entry": None, "relocations": []}
    symtab, dysym, position = None, None, 32
    for unused in range(ncmd):
        need(position + 8 <= 32 + command_bytes, "load-command-short")
        command, length = struct.unpack_from("<II", blob, position)
        need(length >= 8 and length % 8 == 0 and
             position + length <= 32 + command_bytes, "load-command-size")
        image["commands"].append({"command": command, "offset": position, "size": length})
        if command == 0x19:
            need(length >= 72, "segment-short")
            values = struct.unpack_from("<II16sQQQQiiII", blob, position)
            segment = dict(zip(("name", "address", "size", "file_offset", "file_size",
                                "maxprot", "initprot", "nsects", "flags"),
                               (c_name(values[2]),) + values[3:]))
            need(length == 72 + 80 * segment["nsects"], "segment-size")
            need(segment["address"] + segment["size"] <= 1 << 64, "segment-vm-wrap")
            need(0 <= segment["initprot"] <= 7 and 0 <= segment["maxprot"] <= 7 and
                 segment["initprot"] & segment["maxprot"] == segment["initprot"], "segment-protection")
            span(blob, segment["file_offset"], segment["file_size"], "segment-file-bounds")
            segment["index"] = len(image["segments"]) + 1
            image["segments"].append(segment)
            for number in range(segment["nsects"]):
                values = struct.unpack_from("<16s16sQQIIIIIIII", blob, position + 72 + 80 * number)
                section = dict(zip(("name", "destination_segment", "address", "size", "offset",
                                    "alignment_log2", "reloff", "nreloc", "flags",
                                    "reserved1", "reserved2", "reserved3"),
                                   (c_name(values[0]), c_name(values[1])) + values[2:]))
                section.update(index=len(image["sections"]) + 1, container=segment["name"],
                               container_segment_index=segment["index"])
                need(section["index"] <= 255 and section["alignment_log2"] <= 31,
                     "section-shape")
                need(segment["address"] <= section["address"] and
                     section["address"] + section["size"] <= segment["address"] + segment["size"],
                     "section-vm-bounds")
                if section["flags"] & 255 not in (1, 12, 18):
                    span(blob, section["offset"], section["size"], "section-file-bounds")
                    need(segment["file_offset"] <= section["offset"] and
                         section["offset"] + section["size"] <= segment["file_offset"] + segment["file_size"],
                         "section-container-file-bounds")
                span(blob, section["reloff"], 8 * section["nreloc"], "relocation-table-bounds")
                image["sections"].append(section)
        elif command == 2:
            need(length == 24 and symtab is None, "symbol-table-command")
            symtab = struct.unpack_from("<IIII", blob, position + 8)
        elif command == 0xb:
            need(length == 80 and dysym is None, "dynamic-symbol-command")
            dysym = struct.unpack_from("<20I", blob, position)
        elif command in (0x22, 0x80000022):
            need(length == 48, "dyld-info-command")
            fields = struct.unpack_from("<10I", blob, position + 8)
            for label, index in zip(("rebase", "bind", "weak_bind", "lazy_bind", "export"), range(0, 10, 2)):
                data = span(blob, fields[index], fields[index + 1], "dyld-info-bounds")
                image["linkedit"].append(dict(kind=label, offset=fields[index], size=len(data), sha256=sha(data)))
        elif command in (0x1d, 0x26, 0x29, 0x2e, 0x80000033, 0x80000034):
            need(length == 16, "linkedit-command")
            offset, size = struct.unpack_from("<II", blob, position + 8)
            data = span(blob, offset, size, "linkedit-bounds")
            image["linkedit"].append(dict(kind=command, offset=offset, size=size, sha256=sha(data)))
        elif command == 0x80000028:
            need(length == 24 and image["entry"] is None, "entry-command")
            entry, stack = struct.unpack_from("<QQ", blob, position + 8)
            span(blob, entry, 4, "entry-file-bounds")
            image["entry"] = dict(raw_entryoff=entry, stacksize=stack, bootstrap_verified=False)
        elif command == 1:
            raise Rejected("unsupported-32-bit-segment")
        position += length
    need(position == 32 + command_bytes and symtab is not None, "load-command-closure")
    if kind == 1:
        need(len(image["segments"]) == 1 and image["segments"][0]["name"] == "",
             "unsupported-object-container")
    else:
        need(image["entry"] is not None, "unsupported-executable-entry")
    offset, count, strings, string_size = symtab
    need(count <= 131072, "symbol-count-cap")
    span(blob, offset, count * 16, "symbol-table-bounds")
    table = span(blob, strings, string_size, "string-table-bounds")
    need(len(table) > 0 and table[0] == 0, "string-table-zero")
    def string_at(index):
        need(0 <= index < len(table), "string-index")
        end = table.find(b"\0", index)
        need(end >= 0, "string-termination")
        return table[index:end].decode("utf-8")
    image["symbols"] = []
    image["symbol_table"] = dict(offset=offset, count=count, strings=strings, string_size=string_size)
    for index in range(count):
        name, typ, section, desc, value = struct.unpack_from("<IBBHQ", blob, offset + index * 16)
        symbol = dict(index=index, name=string_at(name), type=typ, section=section, desc=desc, value=value)
        if not typ & 0xe0 and typ & 0x0e == 0x0e:
            need(1 <= section <= len(image["sections"]), "symbol-section")
            sec = image["sections"][section - 1]
            need(sec["address"] <= value <= sec["address"] + sec["size"], "symbol-value")
        if not typ & 0xe0 and typ & 0x0e == 0x0a:
            string_at(value)
        image["symbols"].append(symbol)
    if dysym is not None:
        for start, amount in ((dysym[2], dysym[3]), (dysym[4], dysym[5]), (dysym[6], dysym[7])):
            need(start + amount <= count, "dynamic-symbol-bounds")
        need(dysym[9] == dysym[11] == dysym[13] == 0, "unsupported-dynamic-symbol-tables")
        span(blob, dysym[14], dysym[15] * 4, "indirect-table-bounds")
        span(blob, dysym[16], dysym[17] * 8, "external-relocation-bounds")
        span(blob, dysym[18], dysym[19] * 8, "local-relocation-bounds")
        need(dysym[17] == dysym[19] == 0, "unsupported-global-relocations")
    need(sum(s["nreloc"] for s in image["sections"]) <= 131072, "relocation-count-cap")
    for section in image["sections"]:
        for index in range(section["nreloc"]):
            address, bits = struct.unpack_from("<iI", blob, section["reloff"] + index * 8)
            relocation = dict(section=section["index"], table_index=index, offset=address, symbol=bits & 0xffffff,
                              pcrel=(bits >> 24) & 1, length=(bits >> 25) & 3,
                              external=(bits >> 27) & 1, type=(bits >> 28) & 15)
            validate_relocation(image, relocation)
            image["relocations"].append(relocation)
    return image


def validate_relocation(image, record):
    need(1 <= record["section"] <= len(image["sections"]), "relocation-section")
    section = image["sections"][record["section"] - 1]
    need(0 <= record["offset"] and record["offset"] + (1 << record["length"]) <= section["size"],
         "relocation-address")
    if record["external"]:
        need(record["symbol"] < len(image["symbols"]), "relocation-symbol")
    elif record["type"] != 10:
        need(record["symbol"] <= len(image["sections"]), "local-relocation-symbol")


def resolve(symbols, name):
    matches = [s for s in symbols if not s["type"] & 0xe0 and s["name"] == name]
    need(len(matches) == 1, "requested-name-count", name)
    symbol = matches[0]
    need(symbol["type"] & 0x0e == 0x0e and not symbol["desc"] & 0x100,
         "requested-symbol-kind", name)
    return symbol


def selected_range(image, symbol, length, leaf=False):
    section = image["sections"][symbol["section"] - 1]
    delta = symbol["value"] - section["address"]
    need(symbol["value"] % 4 == 0 and 0 <= delta <= section["size"] - length,
         "selected-range-bounds", symbol["name"])
    need(section["destination_segment"] == "__TEXT" and section["name"] == "__text" and
         section["flags"] & 255 == 0 and section["flags"] & 0x80000400,
         "selected-text-section")
    need(not any(s["index"] != section["index"] and s["address"] < symbol["value"] + length and
                 symbol["value"] < s["address"] + s["size"] for s in image["sections"]),
         "contradictory-section-map")
    offset = section["offset"] + delta
    if image["kind"] == 2:
        segment = image["segments"][section["container_segment_index"] - 1]
        need(segment["name"] == "__TEXT" and segment["initprot"] & 7 == 5,
             "selected-text-protection")
        need(segment["flags"] == 0, "selected-segment-flags")
        need(segment["file_size"] <= segment["size"], "selected-segment-file-vm-size")
        need(segment["address"] <= symbol["value"] and
             symbol["value"] + length <= segment["address"] + segment["file_size"],
             "selected-file-backed-vm-range")
        need(not any(s["index"] != segment["index"] and s["size"] > 0 and
                     s["address"] < symbol["value"] + length and
                     symbol["value"] < s["address"] + s["size"] for s in image["segments"]),
             "contradictory-segment-map")
        need(offset == segment["file_offset"] + symbol["value"] - segment["address"],
             "selected-vm-file-mapping")
    peers = [dict(s) for s in image["symbols"] if not s["type"] & 0xe0 and
             s["type"] & 0x0e == 0x0e and s["section"] == symbol["section"] and
             symbol["value"] <= s["value"] < symbol["value"] + length and s["index"] != symbol["index"]]
    need(len(peers) <= 128, "selected-symbol-report-cap")
    need(not leaf or not any(s["value"] > symbol["value"] for s in peers), "interior-leaf-entry")
    data = span(image["blob"], offset, length, "selected-file-range")
    return dict(name=symbol["name"], symbol_index=symbol["index"], section=symbol["section"],
                entry=symbol["value"], file_offset=offset, length=length, data=data,
                other_symbols=peers, candidate_not_function_size=not leaf)


def binding_identity(candidate, contract):
    need((candidate["name"], candidate["section"], candidate["entry"], candidate["length"]) == contract,
         "requested-binding")


def decode_leaf(data, variant):
    need(len(data) == 16, "leaf-size16")
    load, store, move, ret = struct.unpack("<4I", data)
    need(load & 0xffc00000 == 0xf9400000 and load & 31 == 2 and
         (load >> 5) & 31 == 0 and (load >> 10) & 4095 == 0, "leaf-load-form")
    need(store & 0xffc00000 == 0xf9000000 and store & 31 == 1 and
         (store >> 5) & 31 == 0, "leaf-store-form")
    need(((store >> 10) & 4095) * 8 == (0 if variant == "positive" else 8), "leaf-store-offset")
    need(move & 0xffe0ffe0 == 0xaa0003e0 and (move >> 16) & 31 == 2 and move & 31 == 0,
         "leaf-mov-orr-form")
    need(ret & 0xfffffc1f == 0xd65f0000 and (ret >> 5) & 31 == 30, "leaf-ret-form")
    return [load, store, move, ret]


def pair_identity(object_leaf, linked_leaf, variant):
    need(object_leaf["data"] == linked_leaf["data"], "leaf-byte-identity")
    return decode_leaf(object_leaf["data"], variant)


def overlapping(record, image, chosen):
    section = image["sections"][chosen["section"] - 1]
    delta = chosen["entry"] - section["address"]
    return record["section"] == chosen["section"] and record["offset"] < delta + chosen["length"] and delta < record["offset"] + (1 << record["length"])


def no_leaf_relocations(records, image, leaf):
    need(not any(overlapping(r, image, leaf) for r in records), "leaf-relocation")


def object_call_relocation(image, caller, word, pc, leaf):
    call_range = dict(caller, entry=pc, length=4)
    relocs = [r for r in image["relocations"] if overlapping(r, image, call_range)]
    need(len(relocs) == 1, "object-call-relocation-count")
    relocation = relocs[0]
    need(relocation["type"] == 2 and relocation["length"] == 2 and relocation["external"] == 1 and
         relocation["pcrel"] == 1 and relocation["symbol"] == leaf["symbol_index"] and
         relocation["offset"] == pc - image["sections"][caller["section"] - 1]["address"] and
         word & 0x3ffffff == 0, "object-call-relocation-form")
    need(not any(r["section"] == relocation["section"] and
                 r["table_index"] + 1 == relocation["table_index"] and r["type"] == 10
                 for r in image["relocations"]), "paired-call-addend")
    return relocation


def branch_target(word, pc):
    need(word & 0xfc000000 == 0x94000000, "call-not-bl")
    immediate = word & 0x3ffffff
    if immediate & (1 << 25):
        immediate -= 1 << 26
    target = pc + immediate * 4
    need(0 <= target < 1 << 64 and pc + 4 < 1 << 64, "branch-address-wrap")
    return target


def linked_call(word, pc, expected_entry):
    target = branch_target(word, pc)
    need(target == expected_entry, "linked-call-target")
    return dict(pc=pc, word_hex=f"{word:08x}", target=target, return_pc=pc + 4)


def approved_reference(path, meta):
    if path == "none":
        need(meta["cell"] == "positive-o0", "positive-reference-required")
        return None, None
    need(meta["cell"] != "positive-o0", "first-positive-reference-must-be-none")
    reference, digest = read_record(path)
    need(set(reference) == REF_KEYS and reference["approved"] is True and
         reference["protocol_sha256"] == PROTOCOL and reference["cell"] == "positive-o0" and
         reference["source_sha256"] == meta["source_sha256"], "positive-reference-identity")
    need(all(hash_string(reference[k]) for k in ("source_sha256", "object_sha256", "linked_sha256")), "positive-reference-hash")
    need(type(reference["leaf_hex"]) is str and len(reference["leaf_hex"]) == 32 and
         all(c in "0123456789abcdef" for c in reference["leaf_hex"]), "positive-reference-bytes")
    data = bytes.fromhex(reference["leaf_hex"])
    decode_leaf(data, "positive")
    return data, digest


def negative_controls(obj, exe, oleaf, eleaf, ocaller, relocation, call, variant, positive,
                      object_word, object_pc):
    rows = []
    def rejects(name, mode, stage, operation):
        try:
            operation()
        except Rejected as error:
            need(error.stage == stage, "control-wrong-stage", (name, stage, error.stage))
            rows.append(dict(name=name, mode=mode, rejected_at=stage))
            return
        raise Rejected("control-accepted", name)
    rejects("empty", "raw", "header-short", lambda: parse(b"", 1))
    rejects("short-header", "raw", "header-short", lambda: parse(obj["blob"][:31], 1))
    rejects("short-command-region", "raw", "load-command-bounds",
            lambda: parse(obj["blob"][:32 + obj["command_bytes"] - 1], 1))
    rejects("short-body", "record", "leaf-size16", lambda: decode_leaf(oleaf["data"][:15], variant))
    changed = dict(eleaf, data=bytes([eleaf["data"][0] ^ 1]) + eleaf["data"][1:])
    rejects("changed-linked-body", "record", "leaf-byte-identity", lambda: pair_identity(oleaf, changed, variant))
    # Contract is a separate immutable snapshot, never taken from the mutated candidate.
    contract = (LEAF, oleaf["section"], oleaf["entry"], 16)
    competitor = dict(ocaller, length=16, data=ocaller["data"][:16])
    rejects("valid-competing-binding", "record", "requested-binding", lambda: binding_identity(competitor, contract))
    symbols = obj["symbols"] + [dict(resolve(obj["symbols"], LEAF))]
    rejects("duplicate-requested-name", "record", "requested-name-count", lambda: resolve(symbols, LEAF))
    bad = dict(resolve(obj["symbols"], LEAF))
    section = obj["sections"][bad["section"] - 1]
    bad["value"] = section["address"] + section["size"]
    rejects("out-of-section-body", "record", "selected-range-bounds", lambda: selected_range(obj, bad, 16, True))
    raw = bytearray(obj["blob"])
    struct.pack_into("<I", raw, obj["symbol_table"]["offset"] + oleaf["symbol_index"] * 16,
                     obj["symbol_table"]["string_size"])
    rejects("invalid-string-index", "raw", "string-index", lambda: parse(raw, 1))
    bad_relocation = dict(relocation, section=oleaf["section"], offset=oleaf["entry"] - section["address"])
    validate_relocation(obj, bad_relocation)
    rejects("leaf-relocation-overlap", "record", "leaf-relocation",
            lambda: no_leaf_relocations([bad_relocation], obj, oleaf))
    alternative = resolve(exe["symbols"], CALLER)["value"]
    displacement = alternative - call["pc"]
    need(displacement % 4 == 0 and -(1 << 27) <= displacement < 1 << 27 and alternative != eleaf["entry"], "control-alternative-target")
    word = 0x94000000 | ((displacement // 4) & 0x3ffffff)
    need(branch_target(word, call["pc"]) == alternative, "control-bl-construction")
    rejects("redirected-bl", "record", "linked-call-target", lambda: linked_call(word, call["pc"], eleaf["entry"]))
    call_section = obj["sections"][ocaller["section"] - 1]
    addend_offset = ocaller["entry"] - call_section["address"]
    if addend_offset == relocation["offset"]:
        addend_offset += 4
    addend = dict(section=relocation["section"], table_index=relocation["table_index"],
                  offset=addend_offset, symbol=1, pcrel=0, length=2, external=0, type=10)
    validate_relocation(obj, addend)
    call_range = dict(ocaller, entry=object_pc, length=4)
    need(not overlapping(addend, obj, call_range) and not overlapping(addend, obj, oleaf),
         "control-paired-addend-offset")
    copied_relocations = []
    for record in obj["relocations"]:
        copied = dict(record)
        if record["section"] == relocation["section"] and record["table_index"] >= relocation["table_index"]:
            if record["table_index"] == relocation["table_index"]:
                copied_relocations.append(addend)
            copied["table_index"] += 1
        copied_relocations.append(copied)
    copied_image = dict(obj, relocations=copied_relocations)
    rejects("nonoverlapping-preceding-call-addend", "record", "paired-call-addend",
            lambda: object_call_relocation(copied_image, ocaller, object_word, object_pc, oleaf))
    if variant == "positive":
        mapping_sections = [dict(s) for s in exe["sections"]]
        mapping_section = mapping_sections[eleaf["section"] - 1]
        segment = exe["segments"][mapping_section["container_segment_index"] - 1]
        alternative_offset = segment["file_offset"]
        if alternative_offset == mapping_section["offset"]:
            alternative_offset += 4
        need(alternative_offset != mapping_section["offset"] and
             segment["file_offset"] <= alternative_offset and
             alternative_offset + mapping_section["size"] <= segment["file_offset"] + segment["file_size"] and
             alternative_offset + mapping_section["size"] <= len(exe["blob"]),
             "control-alternative-section-offset")
        mapping_section["offset"] = alternative_offset
        mapping_image = dict(exe, sections=mapping_sections)
        rejects("contradictory-linked-section-offset", "record", "selected-vm-file-mapping",
                lambda: selected_range(mapping_image, resolve(mapping_image["symbols"], LEAF), 16, True))
    if variant == "control":
        need(positive is not None, "control-positive-reference")
        stale_object, stale_linked = dict(oleaf, data=positive), dict(eleaf, data=positive)
        rejects("stale-positive-in-both-control-ranges", "record", "leaf-store-offset",
                lambda: pair_identity(stale_object, stale_linked, variant))
    need(len(rows) <= 13, "control-count")
    return rows


def public_range(record):
    return dict((key, value) for key, value in record.items() if key != "data") | dict(bytes_hex=record["data"].hex(), sha256=sha(record["data"]))


def bind(image, caller_length, call_offset):
    leaf_symbol, caller_symbol = resolve(image["symbols"], LEAF), resolve(image["symbols"], CALLER)
    leaf = selected_range(image, leaf_symbol, 16, True)
    caller = selected_range(image, caller_symbol, caller_length)
    need(sum(overlapping(r, image, caller) for r in image["relocations"]) <= 128,
         "caller-relocation-report-cap")
    need(not (caller["section"] == leaf["section"] and caller["entry"] < leaf["entry"] + 16 and
              leaf["entry"] < caller["entry"] + caller["length"]), "caller-leaf-range-overlap")
    no_leaf_relocations(image["relocations"], image, leaf)
    word = struct.unpack_from("<I", caller["data"], call_offset)[0]
    pc = caller["entry"] + call_offset
    branch_target(word, pc)
    return leaf, caller, word, pc


def main():
    need(len(sys.argv) == 6, "cli", "OBJECT LINKED positive|control METADATA REFERENCE|none")
    object_path, linked_path, variant, metadata_path, reference_path = sys.argv[1:]
    meta, metadata_digest = read_record(metadata_path)
    metadata(meta, variant)
    positive, reference_digest = approved_reference(reference_path, meta)
    object_blob, linked_blob = read_file(object_path, FILE_CAP), read_file(linked_path, FILE_CAP)
    need(sha(object_blob) == meta["object_sha256"] and sha(linked_blob) == meta["linked_sha256"], "artifact-hash-identity")
    obj, exe = parse(object_blob, 1), parse(linked_blob, 2)
    oleaf, ocaller, oword, opc = bind(obj, meta["object_caller_bytes"], meta["object_call_offset"])
    eleaf, ecaller, eword, epc = bind(exe, meta["linked_caller_bytes"], meta["linked_call_offset"])
    words = pair_identity(oleaf, eleaf, variant)
    relocation = object_call_relocation(obj, ocaller, oword, opc, oleaf)
    need(not any(overlapping(r, exe, ecaller) for r in exe["relocations"]), "linked-caller-relocation")
    call = linked_call(eword, epc, eleaf["entry"])
    if positive is not None:
        need(oleaf["data"][:4] + oleaf["data"][8:] == positive[:4] + positive[8:], "positive-reference-frame")
        need((oleaf["data"] == positive) == (variant == "positive"), "positive-reference-variant")
    controls = negative_controls(obj, exe, oleaf, eleaf, ocaller, relocation, call, variant, positive,
                                 oword, opc)
    candidate = None
    if meta["cell"] == "positive-o0":
        candidate = dict(protocol_sha256=PROTOCOL, cell=meta["cell"], source_sha256=meta["source_sha256"],
                         object_sha256=obj["sha256"], linked_sha256=exe["sha256"], leaf_hex=oleaf["data"].hex())
    images = []
    for image, leaf, caller in ((obj, oleaf, ocaller), (exe, eleaf, ecaller)):
        images.append(dict(sha256=image["sha256"], size=len(image["blob"]), kind=image["kind"],
                           flags=image["flags"], commands=image["commands"], segments=image["segments"],
                           sections=image["sections"], symbol_table=image["symbol_table"], entry=image["entry"],
                           linkedit=image["linkedit"], leaf=public_range(leaf), caller=public_range(caller),
                           caller_relocations=[r for r in image["relocations"] if overlapping(r, image, caller)]))
    report = dict(status="reader_checks_passed_pending_human_review", protocol_sha256=PROTOCOL,
                  reader_sha256=sha(read_file(str(Path(__file__).resolve()), RECORD_CAP)),
                  cell=meta["cell"], variant=variant, source_sha256=meta["source_sha256"],
                  metadata_sha256=metadata_digest, reference_record_sha256=reference_digest,
                  input_paths=[object_path, linked_path], artifacts=images, observed_leaf_words=words,
                  object_call=dict(pc=opc, word_hex=f"{oword:08x}", relocation=relocation), linked_call=call,
                  controls=controls, positive_reference_candidate=candidate,
                  pending=["source/MIR/LLVM association", "complete disassembly and fixup inspection",
                           "caller range completeness and post-call dataflow", "parent release before native run"],
                  limitations="Unverified format/opcode predicates; no loader, runtime bootstrap, hardware or Rust/ISA proof.")
    print(json.dumps(report, sort_keys=True, allow_nan=False))


if __name__ == "__main__":
    try:
        main()
    except Rejected as error:
        print(json.dumps(dict(status="rejected", stage=error.stage, detail=error.detail)), file=sys.stderr)
        sys.exit(2)
    except Exception as error:
        print(json.dumps(dict(status="internal_error", kind=type(error).__name__, detail=str(error)[:240])), file=sys.stderr)
        sys.exit(3)
