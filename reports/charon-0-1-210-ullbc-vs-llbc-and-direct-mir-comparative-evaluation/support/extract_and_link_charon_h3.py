#!/usr/bin/env python3
"""N2 & R1/R3/R4 (#68 §4.4 & #89 §§8, 10, 11):
- Content-complete `MirPhase::Built` parser over `bodies_stateful_generic_lib_*.json` + real `--cfg wrong_cfg_probe` capture (`R1`, fixing `U1`).
- Native-first single-artifact Charon 0.1.210 H3 client closure translator + optional multi-artifact linker (`R3`, fixing `U2`).
- HashConsedValue/Deduplicated generic call-site instance checker + mechanically bound H3/Charon controls (`R4`, fixing `U6`).
"""

import copy
import hashlib
import json
import os
import pathlib
import re
import resource
import subprocess
import time

BASE_DIR = pathlib.Path(__file__).resolve().parent
WS_DIR = BASE_DIR / "workspace"
ART_DIR = BASE_DIR / "artifacts"
TC_DIR = "/usr/local/google/home/joshlf/.anneal/toolchain/4791adccd9a0d457c1700a5eeec084d335a94a8ba17341cec727d22f6cc27f61"
CHARON = os.path.join(TC_DIR, "aeneas/bin/charon")
RUSTC = os.path.join(TC_DIR, "rust/bin/rustc")
LIB_DIR = os.path.join(TC_DIR, "rust/lib")
HOST_LIB_DIR = os.path.join(TC_DIR, "rust/lib/rustlib/x86_64-unknown-linux-gnu/lib")
DRIVER_SRC = "/usr/local/google/home/joshlf/workspace/anneal/experiments/opsem/real-mir-ullbc-capture/direct_mir_driver_v4.rs"
DRIVER_BIN = "/tmp/direct_mir_driver_v4_bin"


def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def sha256_file(p: pathlib.Path) -> str:
    return sha256_bytes(p.read_bytes())


def compute_fp16(crate_name: str, body_bytes: bytes) -> tuple[int, int]:
    acc = 0x5A3C
    for b in crate_name.encode("utf-8"):
        acc = ((acc * 31) + b) & 0xFFFF
    for b in body_bytes:
        acc = ((acc * 131) + b) & 0xFFFF
    return ((acc >> 8) & 0xFF, acc & 0xFF)


def build_amir_v3_package(
    crate_name: str, default_phase: int, flags: int, bodies_raw: list[bytes]
) -> bytes:
    concat_bodies = b"".join(bodies_raw)
    fp_hi, fp_lo = compute_fp16(crate_name, concat_bodies)
    header = bytes(
        [
            0x41,
            0x4D,
            0x49,
            0x52,
            3,
            default_phase,
            flags,
            fp_hi,
            fp_lo,
            len(bodies_raw),
        ]
    )
    return header + concat_bodies


def build_charon_hc_table(ullbc_doc: dict) -> dict[int, object]:
    hc: dict[int, object] = {}

    def walk(x: object) -> None:
        if isinstance(x, dict):
            if "HashConsedValue" in x:
                hid, val = x["HashConsedValue"]
                hc[int(hid)] = val
                walk(val)
            else:
                for v in x.values():
                    walk(v)
        elif isinstance(x, list):
            for v in x:
                walk(v)

    walk(ullbc_doc)
    return hc


def resolve_charon_hc(x: object, hc: dict[int, object]) -> object:
    if isinstance(x, dict):
        if "Deduplicated" in x:
            hid = int(x["Deduplicated"])
            if hid not in hc:
                raise ValueError(f"Unresolved Deduplicated ID in Charon ULLBC: {hid}")
            return resolve_charon_hc(hc[hid], hc)
        if "HashConsedValue" in x:
            return resolve_charon_hc(x["HashConsedValue"][1], hc)
        return {k: resolve_charon_hc(v, hc) for k, v in x.items()}
    if isinstance(x, list):
        return [resolve_charon_hc(v, hc) for v in x]
    return x


def encode_charon_place(p: dict) -> tuple[int, int]:
    chain = []
    cur = p
    while "Projection" in cur["kind"]:
        inner, proj = cur["kind"]["Projection"]
        chain.append(proj)
        cur = inner
    chain.reverse()
    loc = int(cur["kind"]["Local"])
    if not chain:
        return (loc, 0)
    if len(chain) == 1:
        e0 = chain[0]
        if e0 == "Deref":
            return (loc, 4)
        if isinstance(e0, dict) and "Field" in e0:
            kind_info, fidx = e0["Field"]
            fidx = int(fidx)
            if isinstance(kind_info, dict) and "Adt" in kind_info:
                _, variant_id = kind_info["Adt"]
                if variant_id is not None:
                    v = int(variant_id)
                    if v == 0 and fidx == 0:
                        return (loc, 8)
                    if v == 1 and fidx == 0:
                        return (loc, 9)
            if fidx in (0, 1, 2):
                return (loc, 1 + fidx)
    if len(chain) == 2 and chain[0] == "Deref":
        e1 = chain[1]
        if isinstance(e1, dict) and "Field" in e1:
            _, fidx = e1["Field"]
            fidx = int(fidx)
            if fidx in (0, 1, 2):
                return (loc, 5 + fidx)
    raise ValueError(f"Unsupported Charon place projection: {p}")


def encode_charon_operand(
    op: dict,
    instance_layout: tuple[int, int] = (4, 4),
    ullbc_doc: dict | None = None,
    hc_table: dict[int, object] | None = None,
) -> bytes:
    if "Copy" in op:
        loc, proj = encode_charon_place(op["Copy"])
        return bytes([loc, proj])
    if "Move" in op:
        loc, proj = encode_charon_place(op["Move"])
        return bytes([loc + 64, proj])
    if "Const" in op:
        ck = op["Const"]["kind"]
        if "Literal" in ck:
            lit = ck["Literal"]
            if "Bool" in lit:
                return bytes([128, 1 if lit["Bool"] else 0])
            if "Scalar" in lit:
                sc = lit["Scalar"]
                if "Unsigned" in sc:
                    uty, val_str = sc["Unsigned"]
                    val = int(val_str)
                    if uty == "U32":
                        return bytes([129, val])
                    if uty == "Usize":
                        return bytes([130, val])
            if "Str" in lit:
                return bytes([131, 2])
        if "Adt" in ck:
            return bytes([131, 0])
        if "TraitConst" in ck:
            # SizedTypeProperties::SIZE (idx 0) or SizedTypeProperties::ALIGN (idx 1)
            trait_ref_raw, const_idx = ck["TraitConst"]
            if ullbc_doc is not None and hc_table is not None:
                tref = resolve_charon_hc(trait_ref_raw, hc_table)
                tdecl_id = int(tref["trait_decl_ref"]["skip_binder"]["id"])
                tdecl = ullbc_doc["translated"]["trait_decls"][tdecl_id]
                tnames = [
                    x.get("Ident", [None])[0]
                    for x in tdecl["item_meta"]["name"]
                    if "Ident" in x
                ]
                if "SizedTypeProperties" not in tnames:
                    raise ValueError(
                        f"Unsupported TraitConst trait declaration: {tnames}"
                    )
            const_idx = int(const_idx)
            size_val, align_val = instance_layout
            if const_idx == 0:
                return bytes([130, size_val])
            if const_idx == 1:
                return bytes([130, align_val])
            raise ValueError(f"Unsupported TraitConst index: {const_idx}")
    raise ValueError(f"Unsupported Charon operand: {op}")


BINOP_TAG_MAP = {
    "Eq": 1,
    "Ne": 2,
    "Lt": 3,
    "Le": 4,
    "Gt": 5,
    "Ge": 6,
    "Add": 7,
    "Sub": 8,
    "Mul": 9,
    "Div": 10,
    "Rem": 11,
    "BitAnd": 12,
}


def resolve_adt_agg_tag(ullbc_doc: dict | None, adt_idx: int) -> int:
    if ullbc_doc is not None and "translated" in ullbc_doc and "type_decls" in ullbc_doc["translated"]:
        tdecls = ullbc_doc["translated"]["type_decls"]
        if 0 <= adt_idx < len(tdecls) and tdecls[adt_idx] is not None:
            names = [
                x.get("Ident", [None])[0]
                for x in tdecls[adt_idx]["item_meta"]["name"]
                if "Ident" in x
            ]
            if "Guard" in names:
                return 1
            if "PairGuards" in names:
                return 2
            if "EffectLog" in names:
                return 3
    if adt_idx == 0:
        return 3
    if adt_idx == 1:
        return 1
    if adt_idx == 2:
        return 2
    return 4


def resolve_charon_local_type_tag(
    ty_obj: object,
    ullbc_doc: dict,
    hc_table: dict[int, object],
    type_var_tag: int | None = None,
) -> int:
    """Q6 (#93 §11 / F6): Strictly extracts and validates the `.amir` v3 type tag of a local
    directly from the Charon ULLBC `locals` AST (`fd['body']['Unstructured']['locals']['locals']`),
    resolving `HashConsedValue`/`Deduplicated` entries and failing closed on unsupported types."""
    ty = resolve_charon_hc(ty_obj, hc_table)
    if ty == {"Literal": {"UInt": "U32"}}:
        return 3
    if ty in ({"Literal": {"UInt": "Usize"}}, {"Literal": {"UInt": "U64"}}):
        return 4
    if ty == {"Literal": "Bool"}:
        return 2
    if isinstance(ty, dict) and "Adt" in ty:
        adt_id = ty["Adt"]["id"]
        if adt_id == "Tuple" and len(ty["Adt"]["generics"]["types"]) == 0:
            return 1
        if isinstance(adt_id, dict) and "Adt" in adt_id:
            tdecl = ullbc_doc["translated"]["type_decls"][int(adt_id["Adt"])]
            names = [
                x.get("Ident", [None])[0]
                for x in tdecl["item_meta"]["name"]
                if "Ident" in x
            ]
            if "EffectLog" in names:
                return 7
            if "Guard" in names:
                return 8
            if "Arguments" in names:
                return 19
    if isinstance(ty, dict) and "RawPtr" in ty:
        inner, mutability = ty["RawPtr"]
        if inner == {"Literal": {"UInt": "U32"}} and mutability == "Shared":
            return 5
    if isinstance(ty, dict) and "Ref" in ty:
        _reg, inner, mutability = ty["Ref"]
        if mutability == "Mut" and isinstance(inner, dict) and "Adt" in inner:
            adt_id = inner["Adt"]["id"]
            if isinstance(adt_id, dict) and "Adt" in adt_id:
                tdecl = ullbc_doc["translated"]["type_decls"][int(adt_id["Adt"])]
                names = [
                    x.get("Ident", [None])[0]
                    for x in tdecl["item_meta"]["name"]
                    if "Ident" in x
                ]
                if "EffectLog" in names:
                    return 6
                if "Guard" in names:
                    return 22
    if ty == {"TypeVar": {"Bound": [0, 0]}} and type_var_tag is not None:
        return type_var_tag
    raise ValueError(f"Unsupported Charon local type in ULLBC AST: {ty!r}")


def extract_ullbc_local_type_tags(
    fd: dict,
    ullbc_doc: dict,
    hc_table: dict[int, object],
    type_var_tag: int | None = None,
) -> list[int]:
    locals_list = fd["body"]["Unstructured"]["locals"]["locals"]
    return [
        resolve_charon_local_type_tag(loc["ty"], ullbc_doc, hc_table, type_var_tag=type_var_tag)
        for loc in locals_list
    ]


def encode_charon_stmt(
    s: dict,
    ullbc_doc: dict | None = None,
    instance_layout: tuple[int, int] = (4, 4),
    hc_table: dict[int, object] | None = None,
) -> bytes:
    k = s["kind"]
    if isinstance(k, dict):
        if "StorageLive" in k:
            return bytes([0x20, int(k["StorageLive"])])
        if "StorageDead" in k:
            return bytes([0x21, int(k["StorageDead"])])
        if "PlaceMention" in k:
            loc, proj = encode_charon_place(k["PlaceMention"])
            return bytes([0x30, loc, proj])
        if "Assign" in k:
            dst_place, rval = k["Assign"]
            dloc, dproj = encode_charon_place(dst_place)
            if isinstance(rval, dict):
                if "Use" in rval:
                    uop, retag = rval["Use"]
                    op_code = 0x11 if retag == "Yes" else 0x10
                    return bytes([op_code, dloc, dproj]) + encode_charon_operand(
                        uop, instance_layout, ullbc_doc=ullbc_doc, hc_table=hc_table
                    )
                if "Ref" in rval:
                    sloc, sproj = encode_charon_place(rval["Ref"]["place"])
                    bkind = rval["Ref"]["kind"]
                    btag = 1 if bkind in ("Mut", "TwoPhaseMut") else 0
                    return bytes([0x13, dloc, dproj, btag, sloc, sproj])
                if "RawPtr" in rval:
                    sloc, sproj = encode_charon_place(rval["RawPtr"]["place"])
                    bkind = rval["RawPtr"]["kind"]
                    btag = 3 if bkind == "Mut" else 2
                    return bytes([0x13, dloc, dproj, btag, sloc, sproj])
                if "BinaryOp" in rval:
                    bop_info, lhs_op, rhs_op = rval["BinaryOp"]
                    bop_name = bop_info if isinstance(bop_info, str) else list(bop_info.keys())[0]
                    if bop_name not in BINOP_TAG_MAP:
                        raise ValueError(f"Unsupported Charon BinaryOp: {bop_info}")
                    btag = BINOP_TAG_MAP[bop_name]
                    return (
                        bytes([0x15, dloc, dproj, btag])
                        + encode_charon_operand(lhs_op, instance_layout, ullbc_doc=ullbc_doc, hc_table=hc_table)
                        + encode_charon_operand(rhs_op, instance_layout, ullbc_doc=ullbc_doc, hc_table=hc_table)
                    )
                if "Aggregate" in rval:
                    agg_kind, ops = rval["Aggregate"]
                    if len(ops) == 0:
                        return bytes([0x10, dloc, dproj, 131, 0])
                    if len(ops) == 2 and isinstance(agg_kind, dict) and "Adt" in agg_kind:
                        adt_info, _, _ = agg_kind["Adt"]
                        aid = adt_info["id"]
                        agg_tag = 4
                        if isinstance(aid, dict) and "Adt" in aid:
                            adt_idx = int(aid["Adt"])
                            agg_tag = resolve_adt_agg_tag(ullbc_doc, adt_idx)
                        out = bytearray([0x19, dloc, dproj, agg_tag])
                        for op in ops:
                            out.extend(
                                encode_charon_operand(op, instance_layout, ullbc_doc=ullbc_doc, hc_table=hc_table)
                            )
                        return bytes(out)
    elif k == "Nop":
        return bytes([0x22])
    raise ValueError(f"Unsupported Charon statement: {s}")


def make_body_bytes(
    body_id: int,
    sym_id: int,
    origin_kind: int,
    mir_phase: int,
    local_count: int,
    arg_count: int,
    blocks_bytes: list[bytes],
    local_types: list[int],
) -> bytes:
    assert len(local_types) == local_count, f"{len(local_types)} != {local_count}"
    out = bytearray(
        [
            body_id,
            sym_id,
            origin_kind,
            mir_phase,
            local_count,
            arg_count,
            len(blocks_bytes),
        ]
    )
    out.extend(local_types)
    for bb in blocks_bytes:
        out.extend(bb)
    return bytes(out)


def resolve_trait_drop_in_place_from_impls(ullbc_doc: dict) -> int:
    """Resolves `impl Destruct for Guard` method 0 from `translated.trait_impls`."""
    for ti in ullbc_doc["translated"]["trait_impls"]:
        if ti is None:
            continue
        names = [x.get("Ident", [None])[0] for x in ti["item_meta"]["name"] if "Ident" in x]
        if "stateful_generic_lib" in names and "Guard" in names:
            methods = ti.get("methods", [])
            if methods:
                return int(methods[0]["skip_binder"]["id"])
    raise ValueError("Could not resolve Guard Destruct::drop_in_place from trait_impls")


def resolve_generic_call_callee_sym(
    base_callee_sym: int,
    call_inner: dict,
    hc_table: dict[int, object] | None,
) -> int:
    if hc_table is None:
        return base_callee_sym
    reg = call_inner["func"].get("Regular")
    if not reg or "generics" not in reg:
        return base_callee_sym
    gens = reg["generics"]
    resolved_types = [resolve_charon_hc(t, hc_table) for t in gens.get("types", [])]
    resolved_trefs = [resolve_charon_hc(tr, hc_table) for tr in gens.get("trait_refs", [])]
    if base_callee_sym == 63:
        if len(resolved_types) != 1:
            raise ValueError(f"Expected 1 generic type arg for step_generic_slot, got {resolved_types}")
        t0 = resolved_types[0]
        # Verify every trait_ref in generics.trait_refs carries the exact same type argument
        for tr in resolved_trefs:
            if isinstance(tr, dict) and "trait_decl_ref" in tr:
                tr_types = tr["trait_decl_ref"]["skip_binder"]["generics"]["types"]
                if tr_types and tr_types[0] != t0:
                    raise ValueError(
                        f"Inconsistent trait_ref type {tr_types[0]} vs call type {t0} on step_generic_slot"
                    )
        if t0 == {"Literal": {"UInt": "U32"}}:
            return 63
        if t0 == {"Literal": {"UInt": "U64"}}:
            # Distinct monomorphized symbol for step_generic_slot::<u64> (R4 / U6)
            return 93
        raise ValueError(f"Unsupported type specialization for step_generic_slot: {t0}")
    return base_callee_sym


def translate_unstructured_body(
    fd: dict,
    body_id: int,
    sym_id: int,
    origin_kind: int,
    mir_phase: int,
    fun_map: dict[int, int],
    trait_drop_sym: int,
    local_types: list[int],
    panic_abort_unwind_target: int = 3,
    ullbc_doc: dict | None = None,
    hc_table: dict[int, object] | None = None,
    instance_layout: tuple[int, int] = (4, 4),
) -> bytes:
    unstruct = fd["body"]["Unstructured"]
    locals_list = unstruct["locals"]["locals"]
    arg_count = int(unstruct["locals"]["arg_count"])
    blks = unstruct["body"]

    blocks_bytes = []
    for b in blks:
        stmts = b["statements"]
        term = b["terminator"]["kind"]
        is_cleanup = (
            1
            if term == "UnwindResume"
            or (isinstance(term, dict) and "Abort" in term and term["Abort"] == "UnwindTerminate")
            else 0
        )
        bb_out = bytearray([is_cleanup, len(stmts)])
        for s in stmts:
            bb_out.extend(
                encode_charon_stmt(
                    s, ullbc_doc=ullbc_doc, instance_layout=instance_layout, hc_table=hc_table
                )
            )
        if term == "Return":
            bb_out.append(0x40)
        elif term == "UnwindResume":
            bb_out.append(0x41)
        elif isinstance(term, dict) and "Abort" in term:
            ab = term["Abort"]
            if ab == "UnwindTerminate":
                bb_out.extend([0x42, 2])
            elif ab == "UndefinedBehavior":
                bb_out.append(0x43)
            else:
                bb_out.extend([0x4A, 27, 0, 0, 255, panic_abort_unwind_target, 131, 2])
        elif isinstance(term, dict) and "Goto" in term:
            bb_out.extend([0x44, int(term["Goto"]["target"])])
        elif isinstance(term, dict) and "Switch" in term:
            sw = term["Switch"]
            discr_bytes = encode_charon_operand(
                sw["discr"], instance_layout, ullbc_doc=ullbc_doc, hc_table=hc_table
            )
            if "If" in sw["targets"]:
                t_true, t_false = sw["targets"]["If"]
                bb_out.append(0x45)
                bb_out.extend(discr_bytes)
                bb_out.extend([0, int(t_false), int(t_true)])
            else:
                raise ValueError(f"Unsupported Charon Switch targets: {sw}")
        elif isinstance(term, dict) and "Drop" in term:
            dr = term["Drop"]
            ploc, pproj = encode_charon_place(dr["place"])
            fn_kind = dr["fn_ptr"]["kind"]
            if "Fun" in fn_kind and "Regular" in fn_kind["Fun"]:
                fn_reg = int(fn_kind["Fun"]["Regular"])
                glue_sym = fun_map[fn_reg]
            elif "Trait" in fn_kind:
                trait_ref_raw, method_idx, _unspec_fidx = fn_kind["Trait"]
                if ullbc_doc is not None and hc_table is not None:
                    tref = resolve_charon_hc(trait_ref_raw, hc_table)
                    tdecl_id = int(tref["trait_decl_ref"]["skip_binder"]["id"])
                    tdecl = ullbc_doc["translated"]["trait_decls"][tdecl_id]
                    tnames = [
                        x.get("Ident", [None])[0]
                        for x in tdecl["item_meta"]["name"]
                        if "Ident" in x
                    ]
                    if "Destruct" not in tnames or int(method_idx) != 0:
                        raise ValueError(
                            f"Unsupported Trait Drop target: {tnames} method {method_idx}"
                        )
                glue_sym = trait_drop_sym
            else:
                raise ValueError(f"Unsupported Drop fn_ptr: {dr}")
            bb_out.extend([0x47, ploc, pproj, glue_sym, int(dr["target"]), int(dr["on_unwind"])])
        elif isinstance(term, dict) and "Call" in term:
            c = term["Call"]
            call_inner = c["call"]
            fn_reg = int(call_inner["func"]["Regular"]["kind"]["Fun"]["Regular"])
            base_callee_sym = fun_map[fn_reg]
            callee_sym = resolve_generic_call_callee_sym(base_callee_sym, call_inner, hc_table)
            dloc, dproj = encode_charon_place(call_inner["dest"])
            args = call_inner["args"]
            bb_out.extend(
                [0x49 + len(args), callee_sym, dloc, dproj, int(c["target"]), int(c["on_unwind"])]
            )
            for a in args:
                bb_out.extend(
                    encode_charon_operand(a, instance_layout, ullbc_doc=ullbc_doc, hc_table=hc_table)
                )
        else:
            raise ValueError(f"Unsupported Charon terminator: {term}")
        blocks_bytes.append(bytes(bb_out))

    return make_body_bytes(
        body_id=body_id,
        sym_id=sym_id,
        origin_kind=origin_kind,
        mir_phase=mir_phase,
        local_count=len(locals_list),
        arg_count=arg_count,
        blocks_bytes=blocks_bytes,
        local_types=local_types,
    )


def translate_h3_library_ullbc(
    lib_doc: dict,
    resolve_trait_drop: bool = True,
    include_layout_wrappers: bool = False,
    instance_layout: tuple[int, int] = (4, 4),
) -> list[bytes]:
    guard_drop_in_place_fidx = resolve_trait_drop_in_place_from_impls(lib_doc)
    assert guard_drop_in_place_fidx == 16
    trait_drop_sym = 7 if resolve_trait_drop else 91
    hc_table = build_charon_hc_table(lib_doc)

    fun_map = {
        0: 3,    # may_unwind_op
        1: 63,   # step_generic_slot
        2: 64,   # step_u32_slot
        3: 65,   # transactional_step
        4: 1,    # EffectLog::record
        5: 2,    # <Guard as Drop>::drop
        9: 26,   # Arguments::from_str
        10: 20,  # u32::wrapping_add
        11: 38,  # core::mem::align_of
        12: 40,  # usize::wrapping_add
        13: 24,  # core::mem::drop
        14: 91,  # unspecialized Destruct::drop_in_place
        15: 21,  # u32::wrapping_mul
        16: 7,   # stateful_generic_lib::Guard::drop_in_place
        19: 37,  # core::mem::size_of
    }

    order = [
        (4, 1, 1, 3),    # EffectLog::record -> sym 1
        (5, 2, 1, 3),    # <Guard as Drop>::drop -> sym 2
        (0, 3, 1, 3),    # may_unwind_op -> sym 3
        (1, 63, 1, 3),   # step_generic_slot -> sym 63
        (2, 64, 1, 3),   # step_u32_slot -> sym 64
        (3, 65, 1, 3),   # transactional_step -> sym 65
        (16, 7, 2, 3),   # Guard::drop_in_place -> sym 7
        (13, 24, 3, 3),  # core::mem::drop<Guard> -> sym 24
    ]
    if include_layout_wrappers:
        order.extend([
            (19, 37, 3, 4),  # core::mem::size_of<T> -> sym 37
            (11, 38, 3, 4),  # core::mem::align_of<T> -> sym 38
        ])

    bodies_raw = []
    for body_id, (fidx, sym_id, orig, phase) in enumerate(order, start=1):
        fd = lib_doc["translated"]["fun_decls"][fidx]
        panic_uw = 7 if fidx == 1 else 3
        local_types = extract_ullbc_local_type_tags(
            fd, lib_doc, hc_table, type_var_tag=(8 if sym_id == 24 else None)
        )
        bodies_raw.append(
            translate_unstructured_body(
                fd=fd,
                body_id=body_id,
                sym_id=sym_id,
                origin_kind=orig,
                mir_phase=phase,
                fun_map=fun_map,
                trait_drop_sym=trait_drop_sym,
                local_types=local_types,
                panic_abort_unwind_target=panic_uw,
                ullbc_doc=lib_doc,
                hc_table=hc_table,
                instance_layout=instance_layout,
            )
        )
    return bodies_raw


def translate_h3_client_contract_ullbc(cc_doc: dict) -> list[bytes]:
    hc_table = build_charon_hc_table(cc_doc)
    fun_map = {
        0: 66,   # client_contract_entry
        1: 63,   # step_generic_slot
        2: 40,   # usize::wrapping_add
    }
    fd = cc_doc["translated"]["fun_decls"][0]
    local_types = extract_ullbc_local_type_tags(fd, cc_doc, hc_table)
    return [
        translate_unstructured_body(
            fd=fd,
            body_id=1,
            sym_id=66,
            origin_kind=1,
            mir_phase=3,
            fun_map=fun_map,
            trait_drop_sym=7,
            local_types=local_types,
            ullbc_doc=cc_doc,
            hc_table=hc_table,
        )
    ]


def translate_h3_client_inspector_ullbc(ci_doc: dict) -> list[bytes]:
    hc_table = build_charon_hc_table(ci_doc)
    fun_map = {
        0: 67,   # client_audit_entry
        1: 63,   # step_generic_slot
        2: 65,   # transactional_step
    }
    fd = ci_doc["translated"]["fun_decls"][0]
    local_types = extract_ullbc_local_type_tags(fd, ci_doc, hc_table)
    return [
        translate_unstructured_body(
            fd=fd,
            body_id=1,
            sym_id=67,
            origin_kind=1,
            mir_phase=3,
            fun_map=fun_map,
            trait_drop_sym=7,
            local_types=local_types,
            ullbc_doc=ci_doc,
            hc_table=hc_table,
        )
    ]


EXPECTED_H3_NATIVE_INSPECTOR_LOCAL_TYPES = {
    0: [3, 6, 6, 5, 2, 4, 6, 5, 3, 6, 6, 2, 2, 4],
    4: [1, 6, 3, 3, 3, 3, 3, 3, 3],
    15: [1, 22, 1, 6, 3, 6],
    8: [3, 2, 3, 2, 19, 3],
    1: [4, 6, 5, 4, 4, 1, 6, 4, 4, 2, 4, 19],
    2: [3, 6, 6, 2, 8, 6, 8, 6, 2, 1, 6, 1, 8, 3, 2, 1, 8, 6, 2, 2],
    12: [1, 22, 22, 1],
    7: [1, 8],
    14: [4],
    3: [4],
}


def validate_h3_native_inspector_adapter_domain(ci_doc: dict) -> None:
    """Q6 (#93 §11 / F6): Validates that every local type in the `H3` native inspector closure
    extracted from the ULLBC AST matches the supported `H3` adapter domain signature/local types."""
    hc_table = build_charon_hc_table(ci_doc)
    for fidx, expected_tags in EXPECTED_H3_NATIVE_INSPECTOR_LOCAL_TYPES.items():
        fd = ci_doc["translated"]["fun_decls"][fidx]
        actual_tags = extract_ullbc_local_type_tags(
            fd, ci_doc, hc_table, type_var_tag=(8 if fidx == 7 else None)
        )
        if actual_tags != expected_tags:
            raise ValueError(
                f"ULLBC local type mismatch at fun_decls[{fidx}]: actual={actual_tags} != expected={expected_tags}"
            )


def translate_h3_native_client_inspector_closure_ullbc_legacy_pr92(
    ci_doc: dict,
    resolve_trait_drop: bool = True,
    include_layout_wrappers: bool = True,
    instance_layout: tuple[int, int] = (4, 4),
) -> list[bytes]:
    """Historical PR #92 (`39c56d016351207792a0d29a7a51a6c7dabec18e`) version preserved for Q0 Appendix B comparison."""
    guard_drop_in_place_fidx = resolve_trait_drop_in_place_from_impls(ci_doc)
    assert guard_drop_in_place_fidx == 12
    trait_drop_sym = 7 if resolve_trait_drop else 91
    hc_table = build_charon_hc_table(ci_doc)
    fun_map = {
        0: 67, 1: 63, 2: 65, 3: 38, 4: 1, 5: 40, 6: 91, 7: 24,
        8: 3, 10: 20, 11: 21, 12: 7, 13: 26, 14: 37, 15: 2,
    }
    order = [
        (0, 67, 1, 3, 1), (4, 1, 1, 3, 2), (15, 2, 1, 3, 3), (8, 3, 1, 3, 4),
        (1, 63, 1, 3, 5), (2, 65, 1, 3, 6), (12, 7, 2, 3, 7), (7, 24, 3, 3, 8),
    ]
    if include_layout_wrappers:
        order.extend([(14, 37, 3, 4, 98), (3, 38, 3, 4, 99)])
    bodies_raw = []
    for fidx, sym_id, orig, phase, bid in order:
        fd = ci_doc["translated"]["fun_decls"][fidx]
        panic_uw = 7 if fidx == 1 else 3
        bodies_raw.append(
            translate_unstructured_body(
                fd=fd,
                body_id=bid,
                sym_id=sym_id,
                origin_kind=orig,
                mir_phase=phase,
                fun_map=fun_map,
                trait_drop_sym=trait_drop_sym,
                local_types=EXPECTED_H3_NATIVE_INSPECTOR_LOCAL_TYPES[fidx],
                panic_abort_unwind_target=panic_uw,
                ullbc_doc=ci_doc,
                hc_table=hc_table,
                instance_layout=instance_layout,
            )
        )
    return bodies_raw


def translate_h3_native_client_inspector_closure_ullbc(
    ci_doc: dict,
    resolve_trait_drop: bool = True,
    include_layout_wrappers: bool = True,
    instance_layout: tuple[int, int] = (4, 4),
    strict_domain_check: bool = False,
) -> list[bytes]:
    """R3 (#89 §10), Q6 (#93 §11 / F6), & C2/D4 (#95 §5 D4): Native-first single-artifact
    translation of the H3 inspector closure from `client_direct_mir_inspector_strongest.ullbc`.
    Preserves `strict_domain_check: bool = False` default only for diagnostic control generation
    and `portable_pr94_control.py` replay; the production path in `main()` (`L1401–1407`) passes
    `strict_domain_check=True` directly."""
    if strict_domain_check:
        validate_h3_native_inspector_adapter_domain(ci_doc)
    guard_drop_in_place_fidx = resolve_trait_drop_in_place_from_impls(ci_doc)
    assert guard_drop_in_place_fidx == 12
    trait_drop_sym = 7 if resolve_trait_drop else 91
    hc_table = build_charon_hc_table(ci_doc)

    fun_map = {
        0: 67,   # client_audit_entry
        1: 63,   # step_generic_slot
        2: 65,   # transactional_step
        3: 38,   # core::mem::align_of
        4: 1,    # EffectLog::record
        5: 40,   # usize::wrapping_add
        6: 91,   # unspecialized Destruct::drop_in_place
        7: 24,   # core::mem::drop
        8: 3,    # may_unwind_op
        10: 20,  # u32::wrapping_add
        11: 21,  # u32::wrapping_mul
        12: 7,   # Guard::drop_in_place
        13: 26,  # Arguments::from_str
        14: 37,  # core::mem::size_of
        15: 2,   # <Guard as Drop>::drop
    }
    order = [
        (0, 67, 1, 3, 1),   # client_audit_entry -> sym 67
        (4, 1, 1, 3, 2),    # EffectLog::record -> sym 1
        (15, 2, 1, 3, 3),   # <Guard as Drop>::drop -> sym 2
        (8, 3, 1, 3, 4),    # may_unwind_op -> sym 3
        (1, 63, 1, 3, 5),   # step_generic_slot -> sym 63
        (2, 65, 1, 3, 6),   # transactional_step -> sym 65
        (12, 7, 2, 3, 7),   # Guard::drop_in_place -> sym 7
        (7, 24, 3, 3, 8),   # core::mem::drop<Guard> -> sym 24
    ]
    if include_layout_wrappers:
        order.extend([
            (14, 37, 3, 4, 98),  # core::mem::size_of<u32> -> sym 37
            (3, 38, 3, 4, 99),   # core::mem::align_of<u32> -> sym 38
        ])
    bodies_raw = []
    for fidx, sym_id, orig, phase, bid in order:
        fd = ci_doc["translated"]["fun_decls"][fidx]
        panic_uw = 7 if fidx == 1 else 3
        local_types = extract_ullbc_local_type_tags(
            fd, ci_doc, hc_table, type_var_tag=(8 if sym_id == 24 else None)
        )
        bodies_raw.append(
            translate_unstructured_body(
                fd=fd,
                body_id=bid,
                sym_id=sym_id,
                origin_kind=orig,
                mir_phase=phase,
                fun_map=fun_map,
                trait_drop_sym=trait_drop_sym,
                local_types=local_types,
                panic_abort_unwind_target=panic_uw,
                ullbc_doc=ci_doc,
                hc_table=hc_table,
                instance_layout=instance_layout,
            )
        )
    return bodies_raw


def translate_h3_native_client_contract_closure_ullbc(
    cc_doc: dict,
    include_layout_wrappers: bool = True,
    instance_layout: tuple[int, int] = (4, 4),
) -> list[bytes]:
    """R3 (#89 §10) & Q6 (#93 §11 / F6): Native-first single-artifact translation of the complete
    H3 contract-user closure directly from `client_contract_user_strongest.ullbc`, extracting
    every local's type tag directly from `fd['body']['Unstructured']['locals']['locals']`."""
    hc_table = build_charon_hc_table(cc_doc)
    fun_map = {
        0: 66,   # client_contract_entry
        1: 63,   # step_generic_slot
        2: 40,   # usize::wrapping_add
        3: 38,   # core::mem::align_of
        4: 1,    # EffectLog::record
        7: 20,   # u32::wrapping_add
        8: 21,   # u32::wrapping_mul
        9: 37,   # core::mem::size_of
        10: 26,  # Arguments::from_str
    }
    order = [
        (0, 66, 1, 3, 1),   # client_contract_entry -> sym 66
        (4, 1, 1, 3, 2),    # EffectLog::record -> sym 1
        (1, 63, 1, 3, 3),   # step_generic_slot -> sym 63
    ]
    if include_layout_wrappers:
        order.extend([
            (9, 37, 3, 4, 98),  # core::mem::size_of<u32> -> sym 37
            (3, 38, 3, 4, 99),  # core::mem::align_of<u32> -> sym 38
        ])
    bodies_raw = []
    for fidx, sym_id, orig, phase, bid in order:
        fd = cc_doc["translated"]["fun_decls"][fidx]
        panic_uw = 7 if fidx == 1 else 3
        local_types = extract_ullbc_local_type_tags(fd, cc_doc, hc_table)
        bodies_raw.append(
            translate_unstructured_body(
                fd=fd,
                body_id=bid,
                sym_id=sym_id,
                origin_kind=orig,
                mir_phase=phase,
                fun_map=fun_map,
                trait_drop_sym=7,
                local_types=local_types,
                panic_abort_unwind_target=panic_uw,
                ullbc_doc=cc_doc,
                hc_table=hc_table,
                instance_layout=instance_layout,
            )
        )
    return bodies_raw


# ==============================================================================
# R1 (#89 §8): Strict Content-Complete Parser for `MirPhase::Built` Driver JSON
# ==============================================================================

DRIVER_TYPE_TAG_MAP = {
    "()": 1,
    "bool": 2,
    "u32": 3,
    "usize": 4,
    "*const u32": 5,
    "&'{erased} mut EffectLog": 6,
    "Guard<'{erased}>": 8,
    "!": 19,
    "core::fmt::Arguments<'{erased}>": 19,
    "&'{erased} mut Guard<'{erased}>": 22,
}

DRIVER_ORIGIN_MAP = {
    "LocalOwner": 1,
    "CompilerShim": 2,
    "ExternalRlib": 3,
}

DRIVER_PHASE_MAP = {
    "Built": 1,
    "Promoted": 2,
    "Runtime(PostCleanup)": 3,
    "Runtime(Optimized)": 4,
}

DRIVER_CALLEE_MAP = {
    "EffectLog::record": 1,
    "<Guard<'_> as core::ops::Drop>::drop": 2,
    "may_unwind_op": 3,
    "core::num::<impl u32>::wrapping_add": 20,
    "core::num::<impl u32>::wrapping_mul": 21,
    "core::mem::drop::<Guard<'_>>": 24,
    "core::fmt::Arguments::<'_>::from_str": 26,
    "core::panicking::panic_fmt": 27,
    "core::mem::size_of::<T>": 37,
    "core::mem::align_of::<T>": 38,
    "core::num::<impl usize>::wrapping_add": 40,
    "step_generic_slot::<u32>": 63,
    "step_generic_slot::<u64>": 93,
}


def parse_driver_place(expr: str) -> tuple[int, int]:
    s = expr.strip()
    m = re.fullmatch(r"_(\d+)", s)
    if m:
        return (int(m.group(1)), 0)
    m = re.fullmatch(r"\(\*_(\d+)\)", s)
    if m:
        return (int(m.group(1)), 4)
    m = re.fullmatch(r"\(_(\d+)\.(\d+):\s*[^)]+\)", s)
    if m:
        loc, fidx = int(m.group(1)), int(m.group(2))
        if fidx not in (0, 1, 2):
            raise ValueError(f"Unsupported field index in place {s}")
        return (loc, 1 + fidx)
    m = re.fullmatch(r"\(\(\*_(\d+)\)\.(\d+):\s*[^)]+\)", s)
    if m:
        loc, fidx = int(m.group(1)), int(m.group(2))
        if fidx not in (0, 1, 2):
            raise ValueError(f"Unsupported deref-field index in place {s}")
        return (loc, 5 + fidx)
    # e.g. `(*(_4.1: &mut EffectLog))` or `(*((*_1).1: &mut EffectLog))`
    m = re.fullmatch(r"\(\*\(_(\d+)\.(\d+):\s*[^)]+\)\)", s)
    if m:
        loc, fidx = int(m.group(1)), int(m.group(2))
        if fidx not in (0, 1, 2):
            raise ValueError(f"Unsupported deref-of-field index in place {s}")
        return (loc, 1 + fidx)
    m = re.fullmatch(r"\(\*\(\(\*_(\d+)\)\.(\d+):\s*[^)]+\)\)", s)
    if m:
        loc, fidx = int(m.group(1)), int(m.group(2))
        if fidx not in (0, 1, 2):
            raise ValueError(f"Unsupported deref-of-deref-field index in place {s}")
        return (loc, 5 + fidx)
    raise ValueError(f"Unsupported driver place expression: {expr!r}")


def parse_driver_operand(expr: str) -> bytes:
    s = expr.strip()
    if s.startswith("copy "):
        loc, proj = parse_driver_place(s[len("copy "):])
        return bytes([loc, proj])
    if s.startswith("move "):
        loc, proj = parse_driver_place(s[len("move "):])
        return bytes([loc + 64, proj])
    if s == "const ()" or s.startswith("const step_generic_slot::<"):
        return bytes([131, 0])
    if s == "const false":
        return bytes([128, 0])
    if s == "const true":
        return bytes([128, 1])
    if s.startswith('const "') and s.endswith('"'):
        return bytes([131, 2])
    m = re.fullmatch(r"const (\d+)_u32", s)
    if m:
        return bytes([129, int(m.group(1))])
    m = re.fullmatch(r"const (\d+)_usize", s)
    if m:
        return bytes([130, int(m.group(1))])
    raise ValueError(f"Unsupported driver operand expression: {expr!r}")


def parse_driver_stmt(kind: str, repr_str: str) -> bytes:
    s = repr_str.strip()
    if kind == "StorageLive":
        m = re.fullmatch(r"StorageLive\(_(\d+)\)", s)
        if not m:
            raise ValueError(f"Malformed StorageLive statement: {s!r}")
        return bytes([0x20, int(m.group(1))])
    if kind == "StorageDead":
        m = re.fullmatch(r"StorageDead\(_(\d+)\)", s)
        if not m:
            raise ValueError(f"Malformed StorageDead statement: {s!r}")
        return bytes([0x21, int(m.group(1))])
    if kind == "FakeRead":
        # Scoped administrative lowering (R1 §8.1): `FakeRead(ForLet(None), _N)` in MirPhase::Built
        # is a borrowck-only let-binding check with zero runtime effect, lowered to WireStmt.nop (0x22).
        m = re.fullmatch(r"FakeRead\(ForLet\(None\),\s*_(\d+)\)", s)
        if not m:
            raise ValueError(f"Unsupported FakeRead statement: {s!r}")
        return bytes([0x22])
    if kind == "PlaceMention":
        m = re.fullmatch(r"PlaceMention\((.+)\)", s)
        if not m:
            raise ValueError(f"Malformed PlaceMention statement: {s!r}")
        loc, proj = parse_driver_place(m.group(1))
        return bytes([0x30, loc, proj])
    if kind in ("Assign(Use,WithRetag::Yes)", "Assign(Use,WithRetag::No)", "Assign(Other)"):
        if " = " not in s:
            raise ValueError(f"Malformed Assign statement: {s!r}")
        lhs, rhs = s.split(" = ", 1)
        dloc, dproj = parse_driver_place(lhs)
        rhs = rhs.strip()
        if rhs.startswith("&mut "):
            sloc, sproj = parse_driver_place(rhs[len("&mut "):])
            return bytes([0x13, dloc, dproj, 1, sloc, sproj])
        m_guard = re.fullmatch(
            r"Guard::<'_>\s*\{\s*id:\s*([^,]+),\s*log:\s*([^}]+)\s*\}", rhs
        )
        if m_guard:
            op0 = parse_driver_operand(m_guard.group(1))
            op1 = parse_driver_operand(m_guard.group(2))
            return bytes([0x19, dloc, dproj, 1]) + op0 + op1
        if rhs.startswith("no_retag "):
            return bytes([0x10, dloc, dproj]) + parse_driver_operand(rhs[len("no_retag "):])
        op_code = 0x10 if kind == "Assign(Use,WithRetag::No)" else 0x11
        return bytes([op_code, dloc, dproj]) + parse_driver_operand(rhs)
    raise ValueError(f"Unsupported driver statement kind={kind!r} repr={repr_str!r}")


def parse_driver_unwind(uw_str: str) -> int:
    u = uw_str.strip()
    if u in ("unwind: continue", "unwind continue"):
        return 252
    if u in ("unwind: terminate(cleanup)", "unwind terminate(cleanup)"):
        return 255
    m = re.fullmatch(r"unwind:\s*bb(\d+)", u)
    if m:
        return int(m.group(1))
    raise ValueError(f"Unsupported driver unwind specification: {uw_str!r}")


def split_top_level_args(args_str: str) -> list[str]:
    s = args_str.strip()
    if not s:
        return []
    out = []
    cur = []
    depth = 0
    in_str = False
    for ch in s:
        if ch == '"':
            in_str = not in_str
            cur.append(ch)
        elif not in_str:
            if ch in "([{":
                depth += 1
                cur.append(ch)
            elif ch in ")]}":
                depth -= 1
                cur.append(ch)
            elif ch == "," and depth == 0:
                out.append("".join(cur).strip())
                cur = []
            else:
                cur.append(ch)
        else:
            cur.append(ch)
    if cur:
        out.append("".join(cur).strip())
    return out


def parse_driver_terminator(term_obj: dict) -> bytes:
    kind = term_obj["kind"]
    s = term_obj["repr"].strip()
    if kind == "Return" and s == "return":
        return bytes([0x40])
    if kind == "UnwindResume" and s == "resume":
        return bytes([0x41])
    if kind == "Goto":
        m = re.fullmatch(r"goto -> bb(\d+)", s)
        if not m:
            raise ValueError(f"Malformed Goto terminator: {s!r}")
        return bytes([0x44, int(m.group(1))])
    if kind == "SwitchInt":
        m = re.fullmatch(
            r"switchInt\((.+)\) -> \[0:\s*bb(\d+),\s*otherwise:\s*bb(\d+)\]", s
        )
        if not m:
            raise ValueError(f"Malformed SwitchInt terminator: {s!r}")
        op_bytes = parse_driver_operand(m.group(1))
        f_bb = int(m.group(2))
        t_bb = int(m.group(3))
        return bytes([0x45]) + op_bytes + bytes([0, f_bb, t_bb])
    if kind == "Drop":
        m = re.fullmatch(r"drop\((.+)\) -> \[return:\s*bb(\d+),\s*(.+)\]", s)
        if not m:
            raise ValueError(f"Malformed Drop terminator: {s!r}")
        ploc, pproj = parse_driver_place(m.group(1))
        t_bb = int(m.group(2))
        uw = parse_driver_unwind(m.group(3))
        return bytes([0x47, ploc, pproj, 7, t_bb, uw])
    if kind == "Call":
        # Either `dst = callee(args) -> [return: bbT, unwind...]` or diverging `dst = callee(args) -> bbU` / `-> unwind continue`
        m_norm = re.fullmatch(
            r"(.+?)\s*=\s*([^(]+)\((.*)\)\s*->\s*\[return:\s*bb(\d+),\s*(.+)\]", s
        )
        if m_norm:
            dst_str, callee_name, args_str, t_bb_str, uw_str = m_norm.groups()
            t_bb = int(t_bb_str)
            uw = parse_driver_unwind(uw_str)
        else:
            m_div_bb = re.fullmatch(
                r"(.+?)\s*=\s*([^(]+)\((.*)\)\s*->\s*bb(\d+)", s
            )
            m_div_uw = re.fullmatch(
                r"(.+?)\s*=\s*([^(]+)\((.*)\)\s*->\s*(unwind.+)", s
            )
            if m_div_bb:
                dst_str, callee_name, args_str, uw_bb_str = m_div_bb.groups()
                t_bb = 255
                uw = int(uw_bb_str)
            elif m_div_uw:
                dst_str, callee_name, args_str, uw_str = m_div_uw.groups()
                t_bb = 255
                uw = parse_driver_unwind(uw_str)
            else:
                raise ValueError(f"Malformed Call terminator: {s!r}")
        dloc, dproj = parse_driver_place(dst_str)
        callee_clean = callee_name.strip()
        if callee_clean not in DRIVER_CALLEE_MAP:
            raise ValueError(f"Unsupported Call callee in driver JSON: {callee_clean!r}")
        callee_sym = DRIVER_CALLEE_MAP[callee_clean]
        arg_exprs = split_top_level_args(args_str)
        if len(arg_exprs) > 4:
            raise ValueError(f"Too many Call arguments ({len(arg_exprs)}): {s!r}")
        out = bytearray([0x49 + len(arg_exprs), callee_sym, dloc, dproj, t_bb, uw])
        for a in arg_exprs:
            out.extend(parse_driver_operand(a))
        return bytes(out)
    raise ValueError(f"Unsupported driver terminator: {term_obj!r}")


def parse_driver_body_entry(
    entry: dict,
    body_id: int,
    sym_id: int,
    arg_count: int,
) -> bytes:
    origin_str = entry["origin_kind"]
    phase_str = entry["phase"]
    if origin_str not in DRIVER_ORIGIN_MAP:
        raise ValueError(f"Unsupported origin_kind: {origin_str!r}")
    if phase_str not in DRIVER_PHASE_MAP:
        raise ValueError(f"Unsupported phase: {phase_str!r}")
    origin_kind = DRIVER_ORIGIN_MAP[origin_str]
    mir_phase = DRIVER_PHASE_MAP[phase_str]

    local_types = []
    for idx, loc_entry in enumerate(entry["locals"]):
        expected_name = f"_{idx}"
        if loc_entry["local"] != expected_name:
            raise ValueError(f"Out-of-order local {loc_entry['local']!r} != {expected_name!r}")
        ty_str = loc_entry["ty"]
        if ty_str not in DRIVER_TYPE_TAG_MAP:
            raise ValueError(f"Unsupported local type in driver JSON: {ty_str!r}")
        local_types.append(DRIVER_TYPE_TAG_MAP[ty_str])

    blocks_bytes = []
    for b_idx, bb in enumerate(entry["basic_blocks"]):
        expected_bb = f"bb{b_idx}"
        if bb["block"] != expected_bb:
            raise ValueError(f"Out-of-order basic block {bb['block']!r} != {expected_bb!r}")
        is_cleanup = 1 if bb["is_cleanup"] else 0
        stmts = bb["statements"]
        bb_out = bytearray([is_cleanup, len(stmts)])
        for st in stmts:
            bb_out.extend(parse_driver_stmt(st["kind"], st["repr"]))
        bb_out.extend(parse_driver_terminator(bb["terminator"]))
        blocks_bytes.append(bytes(bb_out))

    return make_body_bytes(
        body_id=body_id,
        sym_id=sym_id,
        origin_kind=origin_kind,
        mir_phase=mir_phase,
        local_count=len(local_types),
        arg_count=arg_count,
        blocks_bytes=blocks_bytes,
        local_types=local_types,
    )


def build_built_phase_lib_bodies(bodies_json: list | None = None) -> list[bytes]:
    """R1 (#89 §8): Strictly parses every local, statement, operand, projection, and terminator
    of the 6 `MirPhase::Built` local bodies (`doc[0, 2, 4, 6, 10, 12]`) plus `DropGlue<Guard>` (`doc[27]`)
    and `core::mem::drop::<Guard>` (`doc[28]`) directly from `bodies_stateful_generic_lib_*.json`."""
    if bodies_json is None:
        bodies_json = json.loads(
            (ART_DIR / "bodies_stateful_generic_lib_always_encode.json").read_text()
        )
    spec_order = [
        (0, "EffectLog::record", "Built", 1, 1, 2),
        (2, "<Guard<'a> as core::ops::Drop>::drop", "Built", 2, 2, 1),
        (4, "may_unwind_op", "Built", 3, 3, 2),
        (6, "step_generic_slot", "Built", 4, 63, 3),
        (10, "step_u32_slot", "Built", 5, 64, 3),
        (12, "transactional_step", "Built", 6, 65, 3),
        (27, "DropGlue<Guard>", "Runtime(Optimized)", 7, 7, 1),
        (28, "core::mem::drop::<Guard>", "Runtime(Optimized)", 8, 24, 1),
    ]
    bodies_raw = []
    for doc_idx, expected_owner, expected_phase, body_id, sym_id, arg_count in spec_order:
        entry = bodies_json[doc_idx]
        if entry["owner"] != expected_owner or entry["phase"] != expected_phase:
            raise ValueError(
                f"Unexpected entry at doc[{doc_idx}]: owner={entry['owner']!r}, phase={entry['phase']!r}"
            )
        bodies_raw.append(parse_driver_body_entry(entry, body_id, sym_id, arg_count))
    return bodies_raw


def run_wrong_cfg_driver_capture() -> dict:
    """R1 (§8.2 Control 4): Runs a real second `direct_mir_driver_v4` invocation on `stateful_generic_lib`
    with `--cfg wrong_cfg_probe` and WITHOUT `-Z mir-preserve-ub`, producing genuine compiler outputs
    `out_stateful_generic_lib_wrong_cfg.json`, `bodies_stateful_generic_lib_wrong_cfg.json`, and
    `stateful_generic_lib_postcleanup_wrong_cfg.amir`."""
    env = os.environ.copy()
    env["LD_LIBRARY_PATH"] = f"{LIB_DIR}:{HOST_LIB_DIR}:" + env.get("LD_LIBRARY_PATH", "")
    subprocess.run(
        [RUSTC, "--edition=2021", "-O", DRIVER_SRC, "-o", DRIVER_BIN],
        env=env,
        check=True,
    )
    out_json = ART_DIR / "out_stateful_generic_lib_wrong_cfg.json"
    out_bodies = ART_DIR / "bodies_stateful_generic_lib_wrong_cfg.json"
    out_post_amir = ART_DIR / "stateful_generic_lib_postcleanup_wrong_cfg.amir"
    out_rlib = pathlib.Path("/tmp/libstateful_generic_lib_wrong_cfg.rlib")
    cmd = [
        DRIVER_BIN,
        "--crate-name",
        "stateful_generic_lib",
        "--edition=2021",
        str(WS_DIR / "stateful_generic_lib/src/lib.rs"),
        "--crate-type",
        "lib",
        "--cfg",
        "wrong_cfg_probe",
        "-C",
        "panic=unwind",
        "-Z",
        "always-encode-mir=yes",
        "--sysroot",
        f"{TC_DIR}/rust",
        "--driver-include-const-owners",
        "--driver-run-mono-collector",
        "--driver-out-json",
        str(out_json),
        "--driver-dump-bodies",
        str(out_bodies),
        "--driver-emit-amir-v3",
        str(out_post_amir),
        "-o",
        str(out_rlib),
    ]
    t0 = time.monotonic()
    proc = subprocess.run(cmd, cwd=str(WS_DIR), env=env, capture_output=True, text=True, timeout=60)
    t1 = time.monotonic()
    if proc.returncode != 0:
        raise RuntimeError(f"direct_mir_driver_v4 wrong_cfg_probe failed: {proc.stderr}")
    meta = json.loads(out_json.read_text())
    return {
        "cmd": cmd,
        "elapsed_ms": int(round((t1 - t0) * 1000)),
        "out_json": str(out_json.relative_to(BASE_DIR)),
        "out_json_sha256": sha256_file(out_json),
        "out_bodies": str(out_bodies.relative_to(BASE_DIR)),
        "out_bodies_sha256": sha256_file(out_bodies),
        "postcleanup_amir": str(out_post_amir.relative_to(BASE_DIR)),
        "postcleanup_amir_sha256": sha256_file(out_post_amir),
        "local_crate_svh": meta.get("local_crate_svh"),
        "preserve_ub_enabled": meta.get("preserve_ub_enabled"),
        "post_run_compiler_verified": meta.get("post_run_compiler_verified"),
        "amir_v3_status": meta.get("amir_v3_status"),
        "amir_v3_fp16": meta.get("amir_v3_fp16"),
    }


def run_charon_strongest(pkg: str, dest_path: pathlib.Path) -> dict:
    env = os.environ.copy()
    env["LD_LIBRARY_PATH"] = f"{LIB_DIR}:{HOST_LIB_DIR}:" + env.get("LD_LIBRARY_PATH", "")
    env["PATH"] = f"{TC_DIR}/rust/bin:{TC_DIR}/aeneas/bin:" + env.get("PATH", "")
    env["RUSTC"] = RUSTC
    env["CHARON_TOOLCHAIN_IS_IN_PATH"] = "1"

    cmd = [
        CHARON,
        "cargo",
        "--ullbc",
        "--precise-drops",
        "--mir",
        "elaborated",
        "--extract-opaque-bodies",
        "--rustc-arg=-Zmir-preserve-ub",
        "--rustc-arg=-Zalways-encode-mir=yes",
        "--dest-file",
        str(dest_path),
        "--",
        "--package",
        pkg,
        "--target-dir",
        "/tmp/anneal_ws_target_charon_strongest_v3",
    ]
    t0 = time.monotonic()
    proc = subprocess.run(
        ["/usr/bin/time", "-v"] + cmd,
        cwd=str(WS_DIR),
        env=env,
        capture_output=True,
        text=True,
        timeout=120,
    )
    t1 = time.monotonic()
    assert proc.returncode == 0, f"Charon failed on {pkg}: {proc.stderr}"
    m = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", proc.stderr)
    rss_bytes = int(m.group(1)) * 1024 if m else 0
    doc = json.loads(dest_path.read_text())
    opts = doc["translated"]["options"]
    assert opts["ullbc"] is True
    assert opts["precise_drops"] is True
    assert opts["extract_opaque_bodies"] is True
    assert opts["mir"] == "Elaborated"
    assert opts["rustc_args"] == ["-Zmir-preserve-ub", "-Zalways-encode-mir=yes"]
    return {
        "package": pkg,
        "dest_file": str(dest_path.relative_to(BASE_DIR)),
        "sha256": sha256_file(dest_path),
        "size_bytes": dest_path.stat().st_size,
        "elapsed_ms": int(round((t1 - t0) * 1000)),
        "max_rss_bytes": rss_bytes,
        "recorded_options": {
            "ullbc": opts["ullbc"],
            "precise_drops": opts["precise_drops"],
            "extract_opaque_bodies": opts["extract_opaque_bodies"],
            "mir": opts["mir"],
            "rustc_args": opts["rustc_args"],
        },
    }


def main() -> None:
    ART_DIR.mkdir(parents=True, exist_ok=True)
    capture_runs = []
    for pkg in ["stateful_generic_lib", "client_contract_user", "client_direct_mir_inspector"]:
        dest = ART_DIR / f"{pkg}_strongest.ullbc"
        rec = run_charon_strongest(pkg, dest)
        capture_runs.append(rec)
        print(
            f"Captured {pkg}_strongest.ullbc: {rec['size_bytes']} B, {rec['elapsed_ms']} ms, sha256={rec['sha256']}"
        )

    lib_doc = json.loads((ART_DIR / "stateful_generic_lib_strongest.ullbc").read_text())
    cc_doc = json.loads((ART_DIR / "client_contract_user_strongest.ullbc").read_text())
    ci_doc = json.loads((ART_DIR / "client_direct_mir_inspector_strongest.ullbc").read_text())

    # 1. Retained multi-artifact and single-entry translations (preserving byte-for-byte compatibility)
    lib_bodies = translate_h3_library_ullbc(lib_doc, resolve_trait_drop=True)
    cc_bodies = translate_h3_client_contract_ullbc(cc_doc)
    ci_bodies = translate_h3_client_inspector_ullbc(ci_doc)

    pkg_lib = build_amir_v3_package("stateful_generic_lib", 3, 11, lib_bodies)
    pkg_cc = build_amir_v3_package("client_contract_user", 3, 11, cc_bodies)
    pkg_ci = build_amir_v3_package("client_direct_mir_inspector", 3, 11, ci_bodies)
    pkg_linked = build_amir_v3_package("client_direct_mir_inspector", 3, 11, ci_bodies + lib_bodies)

    # 2. R3 (#89 §10) & C2/D4 (#95 §5 D4): Native-first single-artifact client closures directly from
    #    client_direct_mir_inspector_strongest.ullbc and client_contract_user_strongest.ullbc, with
    #    mandatory complete-vector domain enforcement (`strict_domain_check=True`) on the production path.
    native_ci_closure_bodies = translate_h3_native_client_inspector_closure_ullbc(
        ci_doc,
        resolve_trait_drop=True,
        include_layout_wrappers=True,
        instance_layout=(4, 4),
        strict_domain_check=True,
    )
    pkg_native_ci_closure = build_amir_v3_package(
        "client_direct_mir_inspector", 3, 11, native_ci_closure_bodies
    )

    native_cc_closure_bodies = translate_h3_native_client_contract_closure_ullbc(
        cc_doc, include_layout_wrappers=True, instance_layout=(4, 4)
    )
    pkg_native_cc_closure = build_amir_v3_package(
        "client_contract_user", 3, 11, native_cc_closure_bodies
    )

    # Verify that the 8 dependency bodies extracted natively from client_direct_mir_inspector_strongest.ullbc
    # match the 8 bodies extracted from stateful_generic_lib_strongest.ullbc byte-for-byte (after normalizing body_id)!
    native_ci_dep_only = translate_h3_native_client_inspector_closure_ullbc(
        ci_doc, resolve_trait_drop=True, include_layout_wrappers=False
    )[1:]
    lib_by_sym = {b[1]: b[1:] for b in lib_bodies}
    for b in native_ci_dep_only:
        assert b[1:] == lib_by_sym[b[1]], f"Mismatch on dependency sym {b[1]}"

    # 3. R4 (#89 §11): Mechanically bound Charon H3 controls
    # Control 1: Single-entry unlinked inspector (as produced by default charon without --extract-opaque-bodies)
    pkg_ctrl1_unlinked = pkg_ci

    # Control 2a: Wrong generic call-site specialization (`Deduplicated(29)` U32 -> U64 in `client_audit_entry` `bb0`),
    #             emitting `callee_sym = 93` (`step_generic_slot::<u64>`) instead of `63`.
    ci_doc_call_u64 = copy.deepcopy(ci_doc)
    gens = ci_doc_call_u64["translated"]["fun_decls"][0]["body"]["Unstructured"]["body"][0][
        "terminator"
    ]["kind"]["Call"]["call"]["func"]["Regular"]["generics"]

    def mutate_dedup29_to_u64(x: object, c: list[int]) -> object:
        if isinstance(x, dict):
            if x == {"Deduplicated": 29}:
                c[0] += 1
                return {"HashConsedValue": [900000 + c[0], {"Literal": {"UInt": "U64"}}]}
            return {k: mutate_dedup29_to_u64(v, c) for k, v in x.items()}
        if isinstance(x, list):
            return [mutate_dedup29_to_u64(v, c) for v in x]
        return x

    c_mut = [0]
    gens.update(mutate_dedup29_to_u64(gens, c_mut))
    ctrl2a_call_u64_bodies = translate_h3_client_inspector_ullbc(ci_doc_call_u64)
    assert ctrl2a_call_u64_bodies != ci_bodies
    pkg_ctrl2a_call_u64 = build_amir_v3_package(
        "client_direct_mir_inspector", 3, 11, ctrl2a_call_u64_bodies
    )

    # Control 2b: Native client closure instantiated with wrong type layout `T = u64` (`instance_layout = (8, 8)`),
    #             so `align_of::<T>()` (`symId = 38`) returns `8` instead of `4`!
    ctrl2_wrong_instance_bodies = translate_h3_native_client_inspector_closure_ullbc(
        ci_doc, resolve_trait_drop=True, include_layout_wrappers=True, instance_layout=(8, 8)
    )
    pkg_ctrl2_wrong_rev = build_amir_v3_package(
        "client_direct_mir_inspector", 3, 11, ctrl2_wrong_instance_bodies
    )

    # Control 3a: Omitted trait drop specialization (`Destruct::drop_in_place` left unspecialized at `symId = 91`)
    ctrl3_unspec_drop_bodies = translate_h3_native_client_inspector_closure_ullbc(
        ci_doc, resolve_trait_drop=False, include_layout_wrappers=True, instance_layout=(4, 4)
    )
    pkg_ctrl3_unspec_drop = build_amir_v3_package(
        "client_direct_mir_inspector", 3, 11, ctrl3_unspec_drop_bodies
    )

    # Control 3b: Omitted drop-flag clear (`_18 = false -> true` in `bb3` of `transactional_step` in `ci_doc`)
    ci_doc_omit_drop_clear = copy.deepcopy(ci_doc)
    bb3_stmts = ci_doc_omit_drop_clear["translated"]["fun_decls"][2]["body"]["Unstructured"][
        "body"
    ][3]["statements"]
    found_drop_flag_clear = False
    for st in bb3_stmts:
        if "Assign" in st["kind"]:
            pl, rv = st["kind"]["Assign"]
            if pl["kind"] == {"Local": 18} and "Use" in rv:
                rv["Use"][0]["Const"]["kind"]["Literal"]["Bool"] = True
                found_drop_flag_clear = True
    assert found_drop_flag_clear
    ctrl3b_omit_drop_clear_bodies = translate_h3_native_client_inspector_closure_ullbc(
        ci_doc_omit_drop_clear, resolve_trait_drop=True, include_layout_wrappers=True
    )
    pkg_ctrl3b_omit_drop_clear = build_amir_v3_package(
        "client_direct_mir_inspector", 3, 11, ctrl3b_omit_drop_clear_bodies
    )

    # Control 4: Changed private event tag `4 -> 9` in ULLBC AST of `step_generic_slot` (`fun_decl[1]` `bb2`)
    ci_doc_ev9 = copy.deepcopy(ci_doc)
    bb2_call = ci_doc_ev9["translated"]["fun_decls"][1]["body"]["Unstructured"]["body"][2][
        "terminator"
    ]["kind"]["Call"]["call"]
    bb2_call["args"][1]["Const"]["kind"]["Literal"]["Scalar"]["Unsigned"] = ["U32", "9"]
    ctrl4_ev9_bodies = translate_h3_native_client_inspector_closure_ullbc(
        ci_doc_ev9, resolve_trait_drop=True, include_layout_wrappers=True
    )
    pkg_ctrl4_ev9 = build_amir_v3_package(
        "client_direct_mir_inspector", 3, 11, ctrl4_ev9_bodies
    )

    # Control 5: Valid administrative change (`StorageLive(17); StorageDead(17)` in `transactional_step` `bb4` of ULLBC AST)
    ci_doc_admin = copy.deepcopy(ci_doc)
    bb4_stmts = ci_doc_admin["translated"]["fun_decls"][2]["body"]["Unstructured"]["body"][4][
        "statements"
    ]
    dummy_span = bb4_stmts[0]["span"]
    bb4_stmts.insert(0, {"span": dummy_span, "kind": {"StorageDead": 17}, "comments_before": []})
    bb4_stmts.insert(0, {"span": dummy_span, "kind": {"StorageLive": 17}, "comments_before": []})
    ctrl5_admin_bodies = translate_h3_native_client_inspector_closure_ullbc(
        ci_doc_admin, resolve_trait_drop=True, include_layout_wrappers=True
    )
    pkg_ctrl5_admin = build_amir_v3_package(
        "client_direct_mir_inspector", 3, 11, ctrl5_admin_bodies
    )

    # Control 6 (Q6 / #93 §11 / F6): Mutate `fun_decls[0]` (`client_audit_entry`) return local `_0`
    # in `ci_doc` from `Deduplicated(29)` (`U32`) to `HashConsedValue(990001, U64)`.
    # Under the legacy PR #92 hardcoded `local_types_table`, output bytes were unchanged;
    # under repaired `extract_ullbc_local_type_tags`, `_0`'s encoded type tag changes from `3` (`u32`)
    # to `4` (`usize`), changing the package bytes and failing `validate_h3_native_inspector_adapter_domain`!
    ci_doc_local_u64 = copy.deepcopy(ci_doc)
    ci_doc_local_u64["translated"]["fun_decls"][0]["body"]["Unstructured"]["locals"]["locals"][0][
        "ty"
    ] = {"HashConsedValue": [990001, {"Literal": {"UInt": "U64"}}]}
    pkg_ctrl6_legacy = build_amir_v3_package(
        "client_direct_mir_inspector",
        3,
        11,
        translate_h3_native_client_inspector_closure_ullbc_legacy_pr92(ci_doc_local_u64),
    )
    assert pkg_ctrl6_legacy == pkg_native_ci_closure
    ctrl6_local_u64_bodies = translate_h3_native_client_inspector_closure_ullbc(
        ci_doc_local_u64, resolve_trait_drop=True, include_layout_wrappers=True
    )
    pkg_ctrl6_local_u64 = build_amir_v3_package(
        "client_direct_mir_inspector", 3, 11, ctrl6_local_u64_bodies
    )
    assert pkg_ctrl6_local_u64 != pkg_native_ci_closure
    domain_check_rejected = False
    try:
        validate_h3_native_inspector_adapter_domain(ci_doc_local_u64)
    except ValueError:
        domain_check_rejected = True
    assert domain_check_rejected

    # 4. R1 (#89 §8): Content-complete `MirPhase::Built` packages and controls from driver JSON
    built_doc = json.loads((ART_DIR / "bodies_stateful_generic_lib_always_encode.json").read_text())
    built_bodies = build_built_phase_lib_bodies(built_doc)
    pkg_built = build_amir_v3_package("stateful_generic_lib", 1, 11, built_bodies)

    # Real second compiler invocation with `--cfg wrong_cfg_probe` (without `-Z mir-preserve-ub`)
    wrong_cfg_run = run_wrong_cfg_driver_capture()
    wrong_cfg_built_doc = json.loads(
        (ART_DIR / "bodies_stateful_generic_lib_wrong_cfg.json").read_text()
    )
    wrong_cfg_built_bodies = build_built_phase_lib_bodies(wrong_cfg_built_doc)
    pkg_built_wrong_cfg = build_amir_v3_package("stateful_generic_lib", 1, 9, wrong_cfg_built_bodies)

    # R1 Control 1: Mutate `const 4_u32 -> const 9_u32` in `doc[6]` (`step_generic_slot` `Built` `bb1`)
    built_doc_ev9 = copy.deepcopy(built_doc)
    built_doc_ev9[6]["basic_blocks"][1]["terminator"]["repr"] = built_doc_ev9[6]["basic_blocks"][1][
        "terminator"
    ]["repr"].replace("const 4_u32", "const 9_u32")
    pkg_r1_ctrl1_built_ev9 = build_amir_v3_package(
        "stateful_generic_lib", 1, 11, build_built_phase_lib_bodies(built_doc_ev9)
    )
    assert pkg_r1_ctrl1_built_ev9 != pkg_built

    # R1 Control 2: Mutate `_17 = move _6 -> _17 = move _4` in `doc[12]` (`transactional_step` `Built` `bb6`),
    # swapping the normal-return drop order under `runStepsBuiltConditionalDrop` from `[2, 1]` to `[1, 2]`!
    built_doc_swap_drop = copy.deepcopy(built_doc)
    built_doc_swap_drop[12]["basic_blocks"][6]["statements"][4]["repr"] = built_doc_swap_drop[12][
        "basic_blocks"
    ][6]["statements"][4]["repr"].replace("move _6", "move _4")
    pkg_r1_ctrl2_built_swap_drop = build_amir_v3_package(
        "stateful_generic_lib", 1, 11, build_built_phase_lib_bodies(built_doc_swap_drop)
    )
    assert pkg_r1_ctrl2_built_swap_drop != pkg_built

    # R1 Control 3: Replace `PlaceMention((*_2))` with `StorageLive(_4)` in `doc[6]` (`step_generic_slot` `Built` `bb0`)
    built_doc_no_pm = copy.deepcopy(built_doc)
    built_doc_no_pm[6]["basic_blocks"][0]["statements"][3] = {
        "kind": "StorageLive",
        "repr": "StorageLive(_4)",
    }
    pkg_r1_ctrl3_built_no_pm = build_amir_v3_package(
        "stateful_generic_lib", 1, 11, build_built_phase_lib_bodies(built_doc_no_pm)
    )
    assert pkg_r1_ctrl3_built_no_pm != pkg_built

    # R1 Control 5: Valid administrative `FakeRead(ForLet(None), _4)` in `doc[12]` (`transactional_step` `Built` `bb4`)
    built_doc_admin = copy.deepcopy(built_doc)
    built_doc_admin[12]["basic_blocks"][4]["statements"].insert(
        0, {"kind": "FakeRead", "repr": "FakeRead(ForLet(None), _4)"}
    )
    pkg_r1_ctrl5_built_admin = build_amir_v3_package(
        "stateful_generic_lib", 1, 11, build_built_phase_lib_bodies(built_doc_admin)
    )
    assert pkg_r1_ctrl5_built_admin != pkg_built

    out_packages = {
        "charon_h3_stateful_generic_lib.amir": pkg_lib,
        "charon_h3_client_contract_user.amir": pkg_cc,
        "charon_h3_client_direct_mir_inspector.amir": pkg_ci,
        "charon_h3_linked_inspector_and_lib.amir": pkg_linked,
        "charon_h3_native_client_inspector_closure.amir": pkg_native_ci_closure,
        "charon_h3_native_client_contract_closure.amir": pkg_native_cc_closure,
        "charon_h3_ctrl1_unlinked_inspector.amir": pkg_ctrl1_unlinked,
        "charon_h3_ctrl2a_call_u64_inspector.amir": pkg_ctrl2a_call_u64,
        "charon_h3_ctrl2_wrong_lib_instance.amir": pkg_ctrl2_wrong_rev,
        "charon_h3_ctrl3_unspecialized_destruct_trait.amir": pkg_ctrl3_unspec_drop,
        "charon_h3_ctrl3b_omitted_drop_flag_clear.amir": pkg_ctrl3b_omit_drop_clear,
        "charon_h3_ctrl4_private_event_9.amir": pkg_ctrl4_ev9,
        "charon_h3_ctrl5_valid_admin_change.amir": pkg_ctrl5_admin,
        "charon_h3_ctrl6_local_u64_type_mismatch.amir": pkg_ctrl6_local_u64,
        "stateful_generic_lib_built_phase.amir": pkg_built,
        "stateful_generic_lib_built_wrong_cfg.amir": pkg_built_wrong_cfg,
        "r1_ctrl1_built_event_9.amir": pkg_r1_ctrl1_built_ev9,
        "r1_ctrl2_built_swapped_drop.amir": pkg_r1_ctrl2_built_swap_drop,
        "r1_ctrl3_built_deleted_place_mention.amir": pkg_r1_ctrl3_built_no_pm,
        "r1_ctrl5_built_admin_nop.amir": pkg_r1_ctrl5_built_admin,
    }

    pkg_records = {}
    for fname, data in out_packages.items():
        fpath = ART_DIR / fname
        fpath.write_bytes(data)
        pkg_records[fname] = {
            "size_bytes": len(data),
            "sha256": sha256_bytes(data),
            "fp16": [data[7], data[8]],
            "body_count": data[9],
            "bytes_list": list(data),
        }
        print(
            f"Wrote {fname}: {len(data)} B, fp16={[data[7], data[8]]}, sha256={sha256_bytes(data)}"
        )

    ledger = {
        "study": "N2_R1_R3_R4_Q6_charon_h3_native_closure_and_built_phase_parser",
        "charon_version": "0.1.210",
        "strongest_flags": [
            "--ullbc",
            "--precise-drops",
            "--mir",
            "elaborated",
            "--extract-opaque-bodies",
            "--rustc-arg=-Zmir-preserve-ub",
            "--rustc-arg=-Zalways-encode-mir=yes",
        ],
        "capture_runs": capture_runs,
        "r1_wrong_cfg_compiler_run": wrong_cfg_run,
        "r1_fake_read_administrative_lowering": {
            "source_construct": "FakeRead(ForLet(None), _N)",
            "wire_opcode": "0x22 (WireStmt.nop)",
            "justification": "In rustc MirPhase::Built, FakeRead(ForLet(None), _N) is a borrow-checker-only marker with no runtime effect and is stripped before Runtime(PostCleanup).",
        },
        "r3_native_charon_closure_verification": {
            "branch_supported": "Branch 1 (#89 §10): Strongest-flags single-artifact client ULLBC (client_direct_mir_inspector_strongest.ullbc and client_contract_user_strongest.ullbc) natively contains the concrete Unstructured bodies of cross-crate callees step_generic_slot (fun_decl[1], 12 blocks), transactional_step (fun_decl[2], 16 blocks), EffectLog::record (fun_decl[4], 7 blocks), <Guard as Drop>::drop (fun_decl[15], 3 blocks), may_unwind_op (fun_decl[8], 7 blocks), Guard::drop_in_place (fun_decl[12], 3 blocks), core::mem::drop (fun_decl[7], 3 blocks), core::mem::size_of (fun_decl[14], 1 block), and core::mem::align_of (fun_decl[3], 1 block).",
            "native_dep_bodies_equal_lib_ullbc_bodies": True,
            "remaining_external_remedies": [
                "R2_trait_drop_specialization: Resolve core::mem::drop<T>'s polymorphic Trait(Clause(0), Destruct::drop_in_place) target via translated.trait_impls[0].methods[0].skip_binder.id == 12 (Guard::drop_in_place, symId = 7).",
                "R3_trait_const_layout_specialization: Instantiate core::mem::size_of<T> (fun_decl[14]) and core::mem::align_of<T> (fun_decl[3]) 1-block Unstructured wrapper bodies at TraitConst(SizedTypeProperties, 0/1) using the compilation-bound layout table (size = 4, align = 4 for u32; size = 8, align = 8 for u64), because SizedTypeProperties::SIZE/ALIGN call core::intrinsics::size_of/align_of (Intrinsic).",
            ],
        },
        "q6_local_type_binding_verification": {
            "legacy_pr92_export_unchanged": pkg_ctrl6_legacy == pkg_native_ci_closure,
            "repaired_q6_export_unchanged": pkg_ctrl6_local_u64 == pkg_native_ci_closure,
            "domain_validator_rejects_local_u64_mutation": domain_check_rejected,
            "baseline_sha256": sha256_bytes(pkg_native_ci_closure),
            "repaired_mutant_sha256": sha256_bytes(pkg_ctrl6_local_u64),
        },
        "translated_packages": {
            k: {kk: vv for kk, vv in v.items() if kk != "bytes_list"}
            for k, v in pkg_records.items()
        },
    }
    ledger_path = BASE_DIR / "charon-h3-n2-ledger.json"
    ledger_path.write_text(json.dumps(ledger, indent=2) + "\n")
    print("Wrote", ledger_path, "sha256:", sha256_file(ledger_path))


if __name__ == "__main__":
    main()
