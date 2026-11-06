"""Manufactured specimen and deliberately tiny, unverified byte importer.

This checks a local certificate protocol, not general x86 correctness or an
assembler/object file. Run with Python 3.10+; no dependencies or native code.
"""
import copy
import hashlib
import json


def decode_leaf(blob):
    if len(blob) != 8 or blob[:3] != bytes.fromhex("48c7c0") or blob[7] != 0xc3:
        raise ValueError("outside importer grammar")
    return [["mov_rax_signed_imm32", int.from_bytes(blob[3:7], "little", signed=True)], ["ret"]]


def validate(cert):
    blob = bytes.fromhex(cert["bytes"])
    if hashlib.sha256(blob).hexdigest() != cert["sha256"]:
        raise ValueError("byte binding")
    if decode_leaf(blob) != cert["ast"]:
        raise ValueError("decoded AST")
    if cert["sizes"] != [7, 1]:
        raise ValueError("instruction sizes")
    start = cert["start"]
    if not -(2**63) <= start <= 2**63 - 1 - len(blob):
        raise ValueError("signed layout overflow")
    labels = cert["labels"]
    if len({name for name, _ in labels}) != len(labels):
        raise ValueError("duplicate label")
    if any(offset not in [0, 7] for _, offset in labels):
        raise ValueError("label is not instruction boundary")
    return True


def run():
    blob = bytes.fromhex("48c7c02a000000c3")
    base = {"bytes": blob.hex(), "sha256": hashlib.sha256(blob).hexdigest(),
            "ast": [["mov_rax_signed_imm32", 42], ["ret"]], "sizes": [7, 1],
            "start": 4096, "labels": [["entry", 0]]}
    mutants = {"positive": base}
    for name in ["stale_byte_hash", "changed_immediate", "wrong_size", "duplicate_label", "interior_label", "embedded_data", "overflow"]:
        mutants[name] = copy.deepcopy(base)
    mutants["stale_byte_hash"]["bytes"] = "48c7c02b000000c3"
    mutants["changed_immediate"]["bytes"] = "48c7c02b000000c3"
    mutants["changed_immediate"]["sha256"] = hashlib.sha256(bytes.fromhex(mutants["changed_immediate"]["bytes"])).hexdigest()
    mutants["wrong_size"]["sizes"] = [6, 2]
    mutants["duplicate_label"]["labels"] += [["entry", 7]]
    mutants["interior_label"]["labels"] = [["entry", 1]]
    mutants["embedded_data"]["bytes"] += "00"
    mutants["embedded_data"]["sha256"] = hashlib.sha256(bytes.fromhex(mutants["embedded_data"]["bytes"])).hexdigest()
    mutants["overflow"]["start"] = 2**63 - 1
    results = {}
    for name, cert in mutants.items():
        try:
            validate(cert)
            results[name] = {"accepted": True}
        except ValueError as err:
            results[name] = {"accepted": False, "reason": str(err)}
    assert results["positive"]["accepted"]
    assert all(not row["accepted"] for name, row in results.items() if name != "positive")
    return {"specimen": base, "results": results, "scope": "owned protocol experiment; no upstream decoder or actual object file"}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
