#!/usr/bin/env python3
"""
Standalone reproducible verification suite for:
  1. Atomic InductiveBlock Merkle constant-cone canonicalization and kernel
     sensitivity to RecRule.rhs, Defn.hints, and Rec.k mutations.
  2. Lossless canonical NDJSON re-serialization (letE.nondep, binderInfo,
     binder names, nested and mutual inductives, recs vs rules order).
  3. Bottom-up topological lambda-lifting across monomorphic and
     universe-polymorphic helper theorems, DAG memoization ratio, and offline
     zero-axiom application stitching without rewriting helpers.
  4. Multi-shard Tarjan union-SCC acyclicity checking and bottom-up zero-axiom
     shard stitching with canonical shared-declaration equality verification.
  5. Lean 4 `module` system (.olean / .olean.server / .olean.private) behavior
     under `leanexport`.

Requires a Lean 4 toolchain (default: Lean v4.35.0 under ~/.elan/toolchains)
providing `lean`, `leanexport`, `nanoda_bin`, `con-ron`, `con-leche`, and
`lean4lean`. Override via `LEAN_TOOLCHAIN_DIR`.
"""
from __future__ import annotations

import copy
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from typing import Any, Dict, List, Optional, Set, Tuple

DEFAULT_TOOLCHAIN = os.path.expanduser(
    "~/.elan/toolchains/leanprover--lean4---v4.35.0"
)
TOOLCHAIN_DIR = os.environ.get("LEAN_TOOLCHAIN_DIR", DEFAULT_TOOLCHAIN)
BIN_DIR = os.path.join(TOOLCHAIN_DIR, "bin")
LIB_DIR = os.path.join(TOOLCHAIN_DIR, "lib", "lean")
STANDARD_AXIOMS = ["propext", "Quot.sound", "Classical.choice"]


def make_env(extra_paths: List[str]) -> Dict[str, str]:
    env = os.environ.copy()
    env["LEAN_PATH"] = ":".join(extra_paths + [LIB_DIR])
    env["LEAN_SYSROOT"] = TOOLCHAIN_DIR
    return env


def run_cmd(
    cmd: List[str], env: Optional[Dict[str, str]] = None, timeout: int = 90
) -> Dict[str, Any]:
    proc = subprocess.run(
        cmd, env=env, capture_output=True, text=True, timeout=timeout
    )
    return {
        "rc": proc.returncode,
        "stdout": proc.stdout.strip(),
        "stderr": proc.stderr.strip(),
    }


def compile_lean(
    src: str, root: str, olean: str, extra_paths: List[str]
) -> Dict[str, Any]:
    cmd = [
        os.path.join(BIN_DIR, "lean"),
        "-R", root, "-o", olean, "-j1",
        "-DElab.async=false", "-Ddebug.skipKernelTC=false",
        src,
    ]
    res = run_cmd(cmd, env=make_env(extra_paths))
    if res["rc"] != 0:
        raise RuntimeError(
            f"lean failed on {src}: rc={res['rc']} stderr={res['stderr']} stdout={res['stdout']}"
        )
    return res


def export_ndjson_raw(
    mods: List[str], decls: List[str], extra_paths: List[str]
) -> Dict[str, Any]:
    cmd = [os.path.join(BIN_DIR, "leanexport"), *mods, "--", *decls]
    return run_cmd(cmd, env=make_env(extra_paths))


def export_ndjson(
    mods: List[str], decls: List[str], out_path: str, extra_paths: List[str]
) -> int:
    res = export_ndjson_raw(mods, decls, extra_paths)
    if res["rc"] != 0:
        raise RuntimeError(f"leanexport failed on {mods}: {res['stderr']}")
    with open(out_path, "w") as f:
        f.write(res["stdout"] + "\n")
    return res["stdout"].count("\n") + 1


def check_all_4_kernels(
    ndjson_path: str, tmp_dir: str, tag: str
) -> Dict[str, Any]:
    cfg = os.path.join(tmp_dir, f"nanoda_{tag}.json")
    with open(cfg, "w") as f:
        json.dump(
            {
                "export_file_path": ndjson_path,
                "permitted_axioms": STANDARD_AXIOMS,
                "unpermitted_axiom_hard_error": True,
                "nat_extension": True,
                "string_extension": True,
                "pp_decl_names": [],
                "print_success_message": True,
            },
            f,
        )
    env = make_env([])
    r_nan = run_cmd([os.path.join(BIN_DIR, "nanoda_bin"), cfg])
    r_cr = run_cmd(
        [os.path.join(BIN_DIR, "con-ron"), "--verified", "--jobs=1", ndjson_path]
    )
    r_cl = run_cmd(
        [
            os.path.join(BIN_DIR, "con-leche"),
            "--verified",
            "--jobs=1",
            ndjson_path,
        ]
    )
    r_l4l = run_cmd(
        [os.path.join(BIN_DIR, "lean4lean"), "--import", ndjson_path], env=env
    )
    return {
        "nanoda": {"rc": r_nan["rc"], "err": r_nan["stderr"][:180]},
        "con_ron": {
            "rc": r_cr["rc"],
            "err": (r_cr["stderr"] or r_cr["stdout"])[:180],
        },
        "con_leche": {
            "rc": r_cl["rc"],
            "err": (r_cl["stderr"] or r_cl["stdout"])[:180],
        },
        "lean4lean": {
            "rc": r_l4l["rc"],
            "err": (r_l4l["stderr"] or r_l4l["stdout"])[:180],
        },
    }


# ---------------------------------------------------------------------------
# Self-Contained NDJSON 3.1.0 Stream Representation
# ---------------------------------------------------------------------------


class NdjsonStream:
    """Minimal hash-consed arena for Lean 4 export NDJSON 3.1.0 streams."""

    def __init__(self) -> None:
        self.meta_line: str = ""
        self.names: Dict[int, Dict[str, Any]] = {}
        self.name_segs: Dict[int, Tuple[Tuple[str, Any], ...]] = {0: ()}
        self.name_str: Dict[int, str] = {0: ""}
        self.seg_to_nid: Dict[Tuple[Tuple[str, Any], ...], int] = {(): 0}
        self.str_to_nid: Dict[str, int] = {"": 0}
        self.max_nid: int = 0

        self.levels: Dict[int, Dict[str, Any]] = {}
        self.level_key_to_id: Dict[str, int] = {}
        self.max_lid: int = 0

        self.exprs: Dict[int, Dict[str, Any]] = {}
        self.expr_key_to_id: Dict[str, int] = {}
        self.max_eid: int = 0

        self.decls: List[Tuple[str, Dict[str, Any]]] = []
        self.decl_by_name: Dict[str, Tuple[str, Dict[str, Any]]] = {}

    def parse_lines(self, lines: List[str]) -> None:
        for raw in lines:
            raw = raw.strip()
            if not raw:
                continue
            obj = json.loads(raw)
            if "meta" in obj:
                self.meta_line = raw
            elif "in" in obj:
                nid = obj["in"]
                rec = {k: v for k, v in obj.items() if k != "in"}
                self.names[nid] = rec
                if "str" in rec:
                    pre = rec["str"]["pre"]
                    s = rec["str"]["str"]
                    segs = self.name_segs[pre] + (("S", s),)
                    full = f"{self.name_str[pre]}.{s}" if self.name_str[pre] else s
                else:
                    pre = rec["num"]["pre"]
                    num = rec["num"]["i"]
                    segs = self.name_segs[pre] + (("N", num),)
                    full = (
                        f"{self.name_str[pre]}.{num}"
                        if self.name_str[pre]
                        else str(num)
                    )
                self.name_segs[nid] = segs
                self.name_str[nid] = full
                self.seg_to_nid[segs] = nid
                self.str_to_nid[full] = nid
                self.max_nid = max(self.max_nid, nid)
            elif "il" in obj:
                lid = obj["il"]
                rec = {k: v for k, v in obj.items() if k != "il"}
                self.levels[lid] = rec
                key = json.dumps(rec, sort_keys=True, separators=(",", ":"))
                self.level_key_to_id[key] = lid
                self.max_lid = max(self.max_lid, lid)
            elif "ie" in obj:
                eid = obj["ie"]
                rec = {k: v for k, v in obj.items() if k != "ie"}
                self.exprs[eid] = rec
                key = json.dumps(rec, sort_keys=True, separators=(",", ":"))
                self.expr_key_to_id[key] = eid
                self.max_eid = max(self.max_eid, eid)
            else:
                kind = next(iter(obj.keys()))
                payload = obj[kind]
                self.decls.append((kind, payload))
                if kind == "inductive":
                    for t in payload.get("types", []):
                        self.decl_by_name[self.name_str[t["name"]]] = (
                            kind,
                            payload,
                        )
                    for c in payload.get("ctors", []):
                        self.decl_by_name[self.name_str[c["name"]]] = (
                            kind,
                            payload,
                        )
                    for r in payload.get("recs", []):
                        self.decl_by_name[self.name_str[r["name"]]] = (
                            kind,
                            payload,
                        )
                else:
                    self.decl_by_name[self.name_str[payload["name"]]] = (
                        kind,
                        payload,
                    )

    def alloc_name_str(self, pre: int, s: str) -> int:
        segs = self.name_segs[pre] + (("S", s),)
        if segs in self.seg_to_nid:
            return self.seg_to_nid[segs]
        self.max_nid += 1
        nid = self.max_nid
        self.names[nid] = {"str": {"pre": pre, "str": s}}
        self.name_segs[nid] = segs
        full = f"{self.name_str[pre]}.{s}" if self.name_str[pre] else s
        self.name_str[nid] = full
        self.seg_to_nid[segs] = nid
        self.str_to_nid[full] = nid
        return nid

    def alloc_name_num(self, pre: int, num: int) -> int:
        segs = self.name_segs[pre] + (("N", num),)
        if segs in self.seg_to_nid:
            return self.seg_to_nid[segs]
        self.max_nid += 1
        nid = self.max_nid
        self.names[nid] = {"num": {"pre": pre, "i": num}}
        self.name_segs[nid] = segs
        full = f"{self.name_str[pre]}.{num}" if self.name_str[pre] else str(num)
        self.name_str[nid] = full
        self.seg_to_nid[segs] = nid
        self.str_to_nid[full] = nid
        return nid

    def alloc_dotted_name(self, dotted: str) -> int:
        cur = 0
        for part in dotted.split("."):
            cur = self.alloc_name_str(cur, part)
        return cur

    def alloc_level(self, rec: Dict[str, Any]) -> int:
        key = json.dumps(rec, sort_keys=True, separators=(",", ":"))
        if key in self.level_key_to_id:
            return self.level_key_to_id[key]
        self.max_lid += 1
        lid = self.max_lid
        self.levels[lid] = rec
        self.level_key_to_id[key] = lid
        return lid

    def alloc_expr(self, rec: Dict[str, Any]) -> int:
        key = json.dumps(rec, sort_keys=True, separators=(",", ":"))
        if key in self.expr_key_to_id:
            return self.expr_key_to_id[key]
        self.max_eid += 1
        eid = self.max_eid
        self.exprs[eid] = rec
        self.expr_key_to_id[key] = eid
        return eid

    def emit_gc_ndjson(
        self, decls: List[Tuple[str, Dict[str, Any]]], root_names: List[str]
    ) -> Tuple[List[str], Dict[str, int]]:
        """Garbage-collect declarations, exprs, levels, and names from roots."""
        decl_map: Dict[str, Tuple[str, Dict[str, Any], int]] = {}
        for idx, (kind, p) in enumerate(decls):
            if kind == "inductive":
                for t in p["types"]:
                    decl_map[self.name_str[t["name"]]] = (kind, p, idx)
                for c in p["ctors"]:
                    decl_map[self.name_str[c["name"]]] = (kind, p, idx)
                for r in p["recs"]:
                    decl_map[self.name_str[r["name"]]] = (kind, p, idx)
            else:
                decl_map[self.name_str[p["name"]]] = (kind, p, idx)

        used_decl_idx: Set[int] = set()
        used_exprs: Set[int] = set()
        used_levels: Set[int] = set()
        used_names: Set[int] = set()

        def mark_name(nid: int) -> None:
            while nid != 0 and nid not in used_names:
                used_names.add(nid)
                rec = self.names[nid]
                nid = rec["str"]["pre"] if "str" in rec else rec["num"]["pre"]

        def mark_level(lid: int) -> None:
            stack = [lid]
            while stack:
                x = stack.pop()
                if x == 0 or x in used_levels:
                    continue
                used_levels.add(x)
                r = self.levels[x]
                if "succ" in r:
                    stack.append(r["succ"])
                elif "max" in r:
                    stack.extend(r["max"])
                elif "imax" in r:
                    stack.extend(r["imax"])
                elif "param" in r:
                    mark_name(r["param"])

        decl_queue: List[str] = list(root_names)

        def mark_expr(root_eid: int) -> None:
            stack = [root_eid]
            while stack:
                eid = stack.pop()
                if eid in used_exprs:
                    continue
                used_exprs.add(eid)
                r = self.exprs[eid]
                if "sort" in r:
                    mark_level(r["sort"])
                elif "const" in r:
                    c = r["const"]
                    mark_name(c["name"])
                    for u in c["us"]:
                        mark_level(u)
                    cnm = self.name_str[c["name"]]
                    if cnm in decl_map:
                        decl_queue.append(cnm)
                elif "app" in r:
                    stack.append(r["app"]["fn"])
                    stack.append(r["app"]["arg"])
                elif "lam" in r:
                    mark_name(r["lam"]["name"])
                    stack.append(r["lam"]["type"])
                    stack.append(r["lam"]["body"])
                elif "forallE" in r:
                    mark_name(r["forallE"]["name"])
                    stack.append(r["forallE"]["type"])
                    stack.append(r["forallE"]["body"])
                elif "letE" in r:
                    mark_name(r["letE"]["name"])
                    stack.append(r["letE"]["type"])
                    stack.append(r["letE"]["value"])
                    stack.append(r["letE"]["body"])
                elif "proj" in r:
                    mark_name(r["proj"]["typeName"])
                    tnm = self.name_str[r["proj"]["typeName"]]
                    if tnm in decl_map:
                        decl_queue.append(tnm)
                    stack.append(r["proj"]["struct"])
                elif "natVal" in r:
                    for req in ("Nat", "Nat.zero", "Nat.succ"):
                        if req in decl_map:
                            decl_queue.append(req)
                elif "strVal" in r:
                    for req in (
                        "String",
                        "String.ofList",
                        "List",
                        "List.nil",
                        "List.cons",
                        "Char",
                        "Char.ofNat",
                        "Nat",
                        "Nat.zero",
                        "Nat.succ",
                    ):
                        if req in decl_map:
                            decl_queue.append(req)
                elif "mdata" in r:
                    stack.append(r["mdata"]["expr"])

        while decl_queue:
            nm = decl_queue.pop()
            if nm not in decl_map:
                continue
            kind, p, idx = decl_map[nm]
            if idx in used_decl_idx:
                continue
            used_decl_idx.add(idx)
            if kind == "inductive":
                for t in p["types"]:
                    mark_name(t["name"])
                    for a in t["all"]:
                        mark_name(a)
                    for c in t["ctors"]:
                        mark_name(c)
                    for u in t["levelParams"]:
                        mark_name(u)
                    mark_expr(t["type"])
                for c in p["ctors"]:
                    mark_name(c["name"])
                    mark_name(c["induct"])
                    for u in c["levelParams"]:
                        mark_name(u)
                    mark_expr(c["type"])
                for r in p["recs"]:
                    mark_name(r["name"])
                    for a in r["all"]:
                        mark_name(a)
                    for u in r["levelParams"]:
                        mark_name(u)
                    mark_expr(r["type"])
                    for rl in r["rules"]:
                        mark_name(rl["ctor"])
                        mark_expr(rl["rhs"])
            else:
                mark_name(p["name"])
                for u in p.get("levelParams", []):
                    mark_name(u)
                for a in p.get("all", []):
                    mark_name(a)
                mark_expr(p["type"])
                if "value" in p:
                    mark_expr(p["value"])

        # Compact/renumber surviving IDs contiguously (nanoda_bin requires continuous in/il/ie back-refs!)
        nid_map: Dict[int, int] = {0: 0}
        for new_nid, old_nid in enumerate(sorted(used_names), start=1):
            nid_map[old_nid] = new_nid
        lid_map: Dict[int, int] = {0: 0}
        for new_lid, old_lid in enumerate(sorted(used_levels), start=1):
            lid_map[old_lid] = new_lid
        eid_map: Dict[int, int] = {}
        for new_eid, old_eid in enumerate(sorted(used_exprs), start=0):
            eid_map[old_eid] = new_eid

        out: List[str] = [self.meta_line]
        for old_nid in sorted(used_names):
            r = self.names[old_nid]
            if "str" in r:
                rec = {"in": nid_map[old_nid], "str": {"pre": nid_map[r["str"]["pre"]], "str": r["str"]["str"]}}
            else:
                rec = {"in": nid_map[old_nid], "num": {"pre": nid_map[r["num"]["pre"]], "i": r["num"]["i"]}}
            out.append(json.dumps(rec, separators=(",", ":")))
        for old_lid in sorted(used_levels):
            r = self.levels[old_lid]
            if "succ" in r:
                rec = {"il": lid_map[old_lid], "succ": lid_map[r["succ"]]}
            elif "max" in r:
                rec = {"il": lid_map[old_lid], "max": [lid_map[r["max"][0]], lid_map[r["max"][1]]]}
            elif "imax" in r:
                rec = {"il": lid_map[old_lid], "imax": [lid_map[r["imax"][0]], lid_map[r["imax"][1]]]}
            elif "param" in r:
                rec = {"il": lid_map[old_lid], "param": nid_map[r["param"]]}
            else:
                raise ValueError(r)
            out.append(json.dumps(rec, separators=(",", ":")))
        for old_eid in sorted(used_exprs):
            r = self.exprs[old_eid]
            ne = eid_map[old_eid]
            if "bvar" in r or "natVal" in r or "strVal" in r:
                rec = dict(r); rec["ie"] = ne
            elif "sort" in r:
                rec = {"ie": ne, "sort": lid_map[r["sort"]]}
            elif "const" in r:
                c = r["const"]
                rec = {"ie": ne, "const": {"name": nid_map[c["name"]], "us": [lid_map[u] for u in c["us"]]}}
            elif "app" in r:
                a = r["app"]
                rec = {"ie": ne, "app": {"fn": eid_map[a["fn"]], "arg": eid_map[a["arg"]]}}
            elif "lam" in r:
                l = r["lam"]
                rec = {"ie": ne, "lam": {"name": nid_map[l["name"]], "type": eid_map[l["type"]], "body": eid_map[l["body"]], "binderInfo": l["binderInfo"]}}
            elif "forallE" in r:
                f = r["forallE"]
                rec = {"ie": ne, "forallE": {"name": nid_map[f["name"]], "type": eid_map[f["type"]], "body": eid_map[f["body"]], "binderInfo": f["binderInfo"]}}
            elif "letE" in r:
                le = r["letE"]
                rec = {"ie": ne, "letE": {"name": nid_map[le["name"]], "type": eid_map[le["type"]], "value": eid_map[le["value"]], "body": eid_map[le["body"]], "nondep": False}}
            elif "proj" in r:
                pr = r["proj"]
                rec = {"ie": ne, "proj": {"typeName": nid_map[pr["typeName"]], "idx": pr["idx"], "struct": eid_map[pr["struct"]]}}
            elif "mdata" in r:
                md = r["mdata"]
                rec = {"ie": ne, "mdata": {"data": md["data"], "expr": eid_map[md["expr"]]}}
            else:
                raise ValueError(r)
            out.append(json.dumps(rec, separators=(",", ":")))
        for idx in sorted(used_decl_idx):
            kind, p = decls[idx]
            if kind == "inductive":
                nt = [{**t, "name": nid_map[t["name"]], "all": [nid_map[a] for a in t["all"]], "ctors": [nid_map[c] for c in t["ctors"]], "levelParams": [nid_map[u] for u in t["levelParams"]], "type": eid_map[t["type"]]} for t in p["types"]]
                nc = [{**c, "name": nid_map[c["name"]], "induct": nid_map[c["induct"]], "levelParams": [nid_map[u] for u in c["levelParams"]], "type": eid_map[c["type"]]} for c in p["ctors"]]
                nr = [{**r, "name": nid_map[r["name"]], "all": [nid_map[a] for a in r["all"]], "levelParams": [nid_map[u] for u in r["levelParams"]], "type": eid_map[r["type"]], "rules": [{"ctor": nid_map[rl["ctor"]], "nfields": rl["nfields"], "rhs": eid_map[rl["rhs"]]} for rl in r["rules"]]} for r in p["recs"]]
                out.append(json.dumps({"inductive": {"types": nt, "ctors": nc, "recs": nr}}, separators=(",", ":")))
            else:
                np = dict(p)
                np["name"] = nid_map[p["name"]]
                np["levelParams"] = [nid_map[u] for u in p.get("levelParams", [])]
                np["type"] = eid_map[p["type"]]
                if "value" in np:
                    np["value"] = eid_map[p["value"]]
                if "all" in np:
                    np["all"] = [nid_map[a] for a in p["all"]]
                out.append(json.dumps({kind: np}, separators=(",", ":")))

        return out, {
            "emitted_decls": len(used_decl_idx),
            "emitted_exprs": len(used_exprs),
        }


# ---------------------------------------------------------------------------
# Canonical Cycle-Safe Merkle Constant-Cone Hasher (Structured Name Segments)
# ---------------------------------------------------------------------------


def _u64(n: int) -> bytes:
    return int(n).to_bytes(8, "big", signed=False)


def _bytes(b: bytes) -> bytes:
    return _u64(len(b)) + b


def _str(s: str) -> bytes:
    return _bytes(s.encode("utf-8"))


def _ser_name_segs(segs: Tuple[Tuple[str, Any], ...]) -> bytes:
    parts = [b"N:ANON", _u64(len(segs))]
    for kind, val in segs:
        if kind == "S":
            parts.append(b"N:STR" + _str(val))
        else:
            parts.append(b"N:NUM" + _u64(val))
    return b"".join(parts)


def canonical_merkle_cone_hash(
    stream: NdjsonStream, root_name: str, include_thm_value: bool = False
) -> Dict[str, Any]:
    """
    Compute deterministic, domain-separated, cycle-safe Merkle SHA-256 over
    `root_name` and its transitive dependency cone:
      - Atomic mutual-inductive block condensation ({types, ctors, recs}),
        preserving positional `types`, `ctors`, and `Rec.rules` (`cidx`) order
        while sorting `recs` canonically by structured name.
      - Structured `Name` segment serialization (`N:ANON` / `N:STR` / `N:NUM`).
      - `Level.simplify` + positional `ParamIdx(i)` alpha-renaming.
      - Strips cosmetic binder names, `binderInfo`, `letE.nondep`, and `mdata`.
      - Tracks full implicit literal deps (`Nat.{zero,succ}`, `String.ofList`,
        `List.{nil,cons}`, `Char.ofNat`).
    """
    decl_by_name: Dict[str, Tuple[str, Dict[str, Any]]] = {}
    ind_block_members: Dict[str, List[str]] = {}
    ind_block_payload: Dict[str, Dict[str, Any]] = {}
    for kind, p in stream.decls:
        if kind == "inductive":
            members = (
                [stream.name_str[t["name"]] for t in p.get("types", [])]
                + [stream.name_str[c["name"]] for c in p.get("ctors", [])]
                + [stream.name_str[r["name"]] for r in p.get("recs", [])]
            )
            bkey = members[0]
            for nm in members:
                decl_by_name[nm] = ("inductive_member", {"block_key": bkey})
                ind_block_members[nm] = members
            ind_block_payload[bkey] = p
        else:
            decl_by_name[stream.name_str[p["name"]]] = (kind, p)

    memo_decl: Dict[str, str] = {}

    def simp_level(lid: int, lparam_pos: Dict[int, int]) -> Tuple[Any, ...]:
        def comb(l: Tuple[Any, ...], r: Tuple[Any, ...]) -> Tuple[Any, ...]:
            if l == ("Z",):
                return r
            if r == ("Z",):
                return l
            if l[0] == "S" and r[0] == "S":
                return ("S", comb(l[1], r[1]))
            if l == r:
                return l
            return ("M", l, r)

        def norm(x: int) -> Tuple[Any, ...]:
            if x == 0:
                return ("Z",)
            rec = stream.levels[x]
            if "succ" in rec:
                return ("S", norm(rec["succ"]))
            if "param" in rec:
                pnid = rec["param"]
                if pnid not in lparam_pos:
                    raise ValueError(
                        f"Unbound level param {stream.name_str[pnid]}"
                    )
                return ("P", lparam_pos[pnid])
            if "max" in rec:
                return comb(norm(rec["max"][0]), norm(rec["max"][1]))
            if "imax" in rec:
                l, r = norm(rec["imax"][0]), norm(rec["imax"][1])
                if l == ("Z",) or l == ("S", ("Z",)):
                    return r
                if r == ("Z",):
                    return ("Z",)
                if r[0] == "S":
                    return comb(l, r)
                return ("IM", l, r)
            raise ValueError(rec)

        return norm(lid)

    def ser_level(t: Tuple[Any, ...]) -> bytes:
        tag = t[0]
        if tag == "Z":
            return b"L0"
        if tag == "S":
            return b"LS" + ser_level(t[1])
        if tag == "P":
            return b"LP" + _u64(t[1])
        if tag == "M":
            return b"LM" + ser_level(t[1]) + ser_level(t[2])
        if tag == "IM":
            return b"LI" + ser_level(t[1]) + ser_level(t[2])
        raise ValueError(t)

    def hash_expr_and_collect_deps(
        root_eid: int, lparams: List[int], internal_block: Set[str]
    ) -> Tuple[bytes, Set[str]]:
        lparam_pos = {nid: i for i, nid in enumerate(lparams)}
        used_ext: Set[str] = set()
        ememo: Dict[int, bytes] = {}
        stack: List[Tuple[int, bool]] = [(root_eid, False)]
        while stack:
            eid, done = stack.pop()
            if eid in ememo:
                continue
            rec = stream.exprs[eid]
            if not done:
                stack.append((eid, True))
                if "app" in rec:
                    stack.append((rec["app"]["fn"], False))
                    stack.append((rec["app"]["arg"], False))
                elif "lam" in rec:
                    stack.append((rec["lam"]["type"], False))
                    stack.append((rec["lam"]["body"], False))
                elif "forallE" in rec:
                    stack.append((rec["forallE"]["type"], False))
                    stack.append((rec["forallE"]["body"], False))
                elif "letE" in rec:
                    stack.append((rec["letE"]["type"], False))
                    stack.append((rec["letE"]["value"], False))
                    stack.append((rec["letE"]["body"], False))
                elif "proj" in rec:
                    stack.append((rec["proj"]["struct"], False))
                elif "mdata" in rec:
                    stack.append((rec["mdata"]["expr"], False))
            else:
                if "mdata" in rec:
                    ememo[eid] = ememo[rec["mdata"]["expr"]]
                    continue
                h = hashlib.sha256()
                if "bvar" in rec:
                    h.update(b"E:BV" + _u64(rec["bvar"]))
                elif "sort" in rec:
                    h.update(
                        b"E:SO"
                        + _bytes(ser_level(simp_level(rec["sort"], lparam_pos)))
                    )
                elif "const" in rec:
                    c = rec["const"]
                    cnid = c["name"]
                    cnm = stream.name_str[cnid]
                    if cnm not in internal_block:
                        used_ext.add(cnm)
                    h.update(
                        b"E:CO"
                        + _ser_name_segs(stream.name_segs[cnid])
                        + _u64(len(c["us"]))
                    )
                    for u in c["us"]:
                        h.update(_bytes(ser_level(simp_level(u, lparam_pos))))
                elif "app" in rec:
                    h.update(
                        b"E:AP"
                        + ememo[rec["app"]["fn"]]
                        + ememo[rec["app"]["arg"]]
                    )
                elif "lam" in rec:
                    h.update(
                        b"E:LA"
                        + ememo[rec["lam"]["type"]]
                        + ememo[rec["lam"]["body"]]
                    )
                elif "forallE" in rec:
                    h.update(
                        b"E:FA"
                        + ememo[rec["forallE"]["type"]]
                        + ememo[rec["forallE"]["body"]]
                    )
                elif "letE" in rec:
                    h.update(
                        b"E:LE"
                        + ememo[rec["letE"]["type"]]
                        + ememo[rec["letE"]["value"]]
                        + ememo[rec["letE"]["body"]]
                    )
                elif "proj" in rec:
                    tnid = rec["proj"]["typeName"]
                    tnm = stream.name_str[tnid]
                    if tnm not in internal_block:
                        used_ext.add(tnm)
                    h.update(
                        b"E:PR"
                        + _ser_name_segs(stream.name_segs[tnid])
                        + _u64(rec["proj"]["idx"])
                        + ememo[rec["proj"]["struct"]]
                    )
                elif "natVal" in rec:
                    for dep in ("Nat", "Nat.zero", "Nat.succ"):
                        if dep in decl_by_name and dep not in internal_block:
                            used_ext.add(dep)
                    h.update(b"E:NA" + _str(rec["natVal"]))
                elif "strVal" in rec:
                    for dep in (
                        "String",
                        "String.ofList",
                        "List",
                        "List.nil",
                        "List.cons",
                        "Char",
                        "Char.ofNat",
                        "Nat",
                        "Nat.zero",
                        "Nat.succ",
                    ):
                        if dep in decl_by_name and dep not in internal_block:
                            used_ext.add(dep)
                    h.update(b"E:ST" + _str(rec["strVal"]))
                else:
                    raise ValueError(rec)
                ememo[eid] = h.digest()
        return ememo[root_eid], used_ext

    visiting: Set[str] = set()

    def hash_const(nm: str) -> str:
        if nm in memo_decl:
            return memo_decl[nm]
        kind, payload = decl_by_name[nm]
        if kind == "inductive_member":
            bkey = payload["block_key"]
            if bkey in visiting:
                raise RuntimeError(f"Cycle hitting block {bkey}")
            visiting.add(bkey)
            members = set(ind_block_members[nm])
            blk = ind_block_payload[bkey]
            ext_deps: Set[str] = set()
            bh = hashlib.sha256(b"D:IND_BLK")
            types = blk.get("types", [])
            ctors = blk.get("ctors", [])
            recs = blk.get("recs", [])
            bh.update(_u64(len(types)))
            for t in types:
                th, d = hash_expr_and_collect_deps(
                    t["type"], t["levelParams"], members
                )
                ext_deps |= d
                bh.update(
                    _ser_name_segs(stream.name_segs[t["name"]])
                    + _u64(len(t["levelParams"]))
                    + _u64(t["numParams"])
                    + _u64(t["numIndices"])
                    + _u64(t["numNested"])
                    + bytes([int(t["isRec"]), int(t["isUnsafe"]), int(t["isReflexive"])])
                    + _u64(len(t["all"]))
                )
                for a in t["all"]:
                    bh.update(_ser_name_segs(stream.name_segs[a]))
                bh.update(_u64(len(t["ctors"])))
                for c in t["ctors"]:
                    bh.update(_ser_name_segs(stream.name_segs[c]))
                bh.update(th)
            bh.update(_u64(len(ctors)))
            for c in ctors:
                ch, d = hash_expr_and_collect_deps(
                    c["type"], c["levelParams"], members
                )
                ext_deps |= d
                bh.update(
                    _ser_name_segs(stream.name_segs[c["name"]])
                    + _ser_name_segs(stream.name_segs[c["induct"]])
                    + _u64(len(c["levelParams"]))
                    + _u64(c["cidx"])
                    + _u64(c["numParams"])
                    + _u64(c["numFields"])
                    + bytes([int(c["isUnsafe"])])
                    + ch
                )
            bh.update(_u64(len(recs)))
            # Sort recs canonically by structured name; preserve rules in cidx order!
            for r in sorted(recs, key=lambda x: stream.name_segs[x["name"]]):
                rh, d = hash_expr_and_collect_deps(
                    r["type"], r["levelParams"], members
                )
                ext_deps |= d
                bh.update(
                    _ser_name_segs(stream.name_segs[r["name"]])
                    + _u64(len(r["levelParams"]))
                    + _u64(r["numParams"])
                    + _u64(r["numIndices"])
                    + _u64(r["numMotives"])
                    + _u64(r["numMinors"])
                    + bytes([int(r["k"]), int(r["isUnsafe"])])
                    + _u64(len(r["all"]))
                )
                for a in r["all"]:
                    bh.update(_ser_name_segs(stream.name_segs[a]))
                bh.update(rh)
                rules = r.get("rules", [])
                bh.update(_u64(len(rules)))
                for rl in rules:
                    rlh, rd = hash_expr_and_collect_deps(
                        rl["rhs"], r["levelParams"], members
                    )
                    ext_deps |= rd
                    bh.update(
                        _ser_name_segs(stream.name_segs[rl["ctor"]])
                        + _u64(rl["nfields"])
                        + rlh
                    )
            visiting.remove(bkey)
            dep_hashes = [
                (dep, hash_const(dep))
                for dep in sorted(ext_deps, key=lambda s: stream.name_segs[stream.str_to_nid[s]])
                if dep in decl_by_name
            ]
            bh.update(_u64(len(dep_hashes)))
            for dnm, dh in dep_hashes:
                bh.update(_ser_name_segs(stream.name_segs[stream.str_to_nid[dnm]]) + _str(dh))
            block_digest = bh.hexdigest()
            for mnm in members:
                memo_decl[mnm] = hashlib.sha256(
                    b"D:IND_MEM"
                    + _ser_name_segs(stream.name_segs[stream.str_to_nid[mnm]])
                    + _str(block_digest)
                ).hexdigest()
            return memo_decl[nm]

        if nm in visiting:
            raise RuntimeError(f"Cycle on non-inductive {nm}")
        visiting.add(nm)
        dh = hashlib.sha256()
        ext_deps: Set[str] = set()
        nbytes = _ser_name_segs(stream.name_segs[payload["name"]])
        if kind == "axiom":
            th, d = hash_expr_and_collect_deps(payload["type"], payload["levelParams"], set())
            ext_deps |= d
            dh.update(b"D:AX" + nbytes + _u64(len(payload["levelParams"])) + bytes([int(payload["isUnsafe"])]) + th)
        elif kind == "quot":
            th, d = hash_expr_and_collect_deps(payload["type"], payload["levelParams"], set())
            ext_deps |= d
            dh.update(b"D:QU" + nbytes + _u64(len(payload["levelParams"])) + _str(payload["kind"]) + th)
        elif kind == "def":
            th, d1 = hash_expr_and_collect_deps(payload["type"], payload["levelParams"], set())
            vh, d2 = hash_expr_and_collect_deps(payload["value"], payload["levelParams"], set())
            ext_deps |= d1 | d2
            hints_s = json.dumps(payload["hints"], sort_keys=True, separators=(",", ":"))
            dh.update(b"D:DF" + nbytes + _u64(len(payload["levelParams"])) + _str(hints_s) + _str(payload["safety"]) + th + vh)
        elif kind == "opaque":
            th, d1 = hash_expr_and_collect_deps(payload["type"], payload["levelParams"], set())
            vh, d2 = hash_expr_and_collect_deps(payload["value"], payload["levelParams"], set())
            ext_deps |= d1 | d2
            dh.update(b"D:OP" + nbytes + _u64(len(payload["levelParams"])) + bytes([int(payload.get("isUnsafe", False))]) + th + vh)
        elif kind == "thm":
            th, d1 = hash_expr_and_collect_deps(payload["type"], payload["levelParams"], set())
            ext_deps |= d1
            if include_thm_value:
                vh, d2 = hash_expr_and_collect_deps(payload["value"], payload["levelParams"], set())
                ext_deps |= d2
                dh.update(b"D:THM_FULL" + nbytes + _u64(len(payload["levelParams"])) + th + vh)
            else:
                dh.update(b"D:THM_CONE" + nbytes + _u64(len(payload["levelParams"])) + th)
        else:
            raise ValueError(kind)
        visiting.remove(nm)
        dep_hashes = [
            (dep, hash_const(dep))
            for dep in sorted(ext_deps, key=lambda s: stream.name_segs[stream.str_to_nid[s]])
            if dep in decl_by_name
        ]
        dh.update(_u64(len(dep_hashes)))
        for dnm, dhd in dep_hashes:
            dh.update(_ser_name_segs(stream.name_segs[stream.str_to_nid[dnm]]) + _str(dhd))
        res = dh.hexdigest()
        memo_decl[nm] = res
        return res

    return {"root_merkle_sha256": hash_const(root_name), "cone_hashes": dict(memo_decl)}


# ---------------------------------------------------------------------------
# Universe Simplification, Substitution, Option-B Topo Lifting & Stitching
# ---------------------------------------------------------------------------


def simp_level_ast(stream: NdjsonStream, lid: int) -> Tuple[Any, ...]:
    def comb(l: Tuple[Any, ...], r: Tuple[Any, ...]) -> Tuple[Any, ...]:
        if l == ("Z",):
            return r
        if r == ("Z",):
            return l
        if l[0] == "S" and r[0] == "S":
            return ("S", comb(l[1], r[1]))
        if l == r:
            return l
        return ("M", l, r)

    def norm(x: int) -> Tuple[Any, ...]:
        if x == 0:
            return ("Z",)
        rec = stream.levels[x]
        if "succ" in rec:
            return ("S", norm(rec["succ"]))
        if "param" in rec:
            return ("P", stream.name_str[rec["param"]])
        if "max" in rec:
            return comb(norm(rec["max"][0]), norm(rec["max"][1]))
        if "imax" in rec:
            l, r = norm(rec["imax"][0]), norm(rec["imax"][1])
            if l == ("Z",) or l == ("S", ("Z",)):
                return r
            if r == ("Z",):
                return ("Z",)
            if r[0] == "S":
                return comb(l, r)
            return ("IM", l, r)
        raise ValueError(rec)

    return norm(lid)


def alloc_level_ast(stream: NdjsonStream, ast: Tuple[Any, ...]) -> int:
    tag = ast[0]
    if tag == "Z":
        return 0
    if tag == "S":
        return stream.alloc_level({"succ": alloc_level_ast(stream, ast[1])})
    if tag == "P":
        return stream.alloc_level({"param": stream.str_to_nid[ast[1]]})
    if tag == "M":
        return stream.alloc_level(
            {"max": [alloc_level_ast(stream, ast[1]), alloc_level_ast(stream, ast[2])]}
        )
    if tag == "IM":
        return stream.alloc_level(
            {"imax": [alloc_level_ast(stream, ast[1]), alloc_level_ast(stream, ast[2])]}
        )
    raise ValueError(ast)


def subst_level_ast(
    ast: Tuple[Any, ...], mapping: Dict[str, Tuple[Any, ...]]
) -> Tuple[Any, ...]:
    def comb(l: Tuple[Any, ...], r: Tuple[Any, ...]) -> Tuple[Any, ...]:
        if l == ("Z",):
            return r
        if r == ("Z",):
            return l
        if l[0] == "S" and r[0] == "S":
            return ("S", comb(l[1], r[1]))
        if l == r:
            return l
        return ("M", l, r)

    tag = ast[0]
    if tag == "Z":
        return ("Z",)
    if tag == "S":
        return ("S", subst_level_ast(ast[1], mapping))
    if tag == "P":
        return mapping.get(ast[1], ast)
    if tag == "M":
        return comb(subst_level_ast(ast[1], mapping), subst_level_ast(ast[2], mapping))
    if tag == "IM":
        l, r = subst_level_ast(ast[1], mapping), subst_level_ast(ast[2], mapping)
        if l == ("Z",) or l == ("S", ("Z",)):
            return r
        if r == ("Z",):
            return ("Z",)
        if r[0] == "S":
            return comb(l, r)
        return ("IM", l, r)
    raise ValueError(ast)


def subst_expr_levels(
    stream: NdjsonStream,
    root_eid: int,
    lparam_names: List[str],
    arg_asts: List[Tuple[Any, ...]],
) -> int:
    mapping = dict(zip(lparam_names, arg_asts))
    if not mapping:
        return root_eid
    ememo: Dict[int, int] = {}

    def subst_lid(lid: int) -> int:
        return alloc_level_ast(
            stream, subst_level_ast(simp_level_ast(stream, lid), mapping)
        )

    def rec_e(eid: int) -> int:
        if eid in ememo:
            return ememo[eid]
        r = stream.exprs[eid]
        if "bvar" in r or "natVal" in r or "strVal" in r:
            res = eid
        elif "sort" in r:
            res = stream.alloc_expr({"sort": subst_lid(r["sort"])})
        elif "const" in r:
            c = r["const"]
            res = stream.alloc_expr(
                {"const": {"name": c["name"], "us": [subst_lid(u) for u in c["us"]]}}
            )
        elif "app" in r:
            a = r["app"]
            res = stream.alloc_expr(
                {"app": {"fn": rec_e(a["fn"]), "arg": rec_e(a["arg"])}}
            )
        elif "lam" in r:
            l = r["lam"]
            res = stream.alloc_expr(
                {
                    "lam": {
                        "name": l["name"],
                        "type": rec_e(l["type"]),
                        "body": rec_e(l["body"]),
                        "binderInfo": l["binderInfo"],
                    }
                }
            )
        elif "forallE" in r:
            f = r["forallE"]
            res = stream.alloc_expr(
                {
                    "forallE": {
                        "name": f["name"],
                        "type": rec_e(f["type"]),
                        "body": rec_e(f["body"]),
                        "binderInfo": f["binderInfo"],
                    }
                }
            )
        elif "letE" in r:
            le = r["letE"]
            res = stream.alloc_expr(
                {
                    "letE": {
                        "name": le["name"],
                        "type": rec_e(le["type"]),
                        "value": rec_e(le["value"]),
                        "body": rec_e(le["body"]),
                        "nondep": False,
                    }
                }
            )
        elif "proj" in r:
            pr = r["proj"]
            res = stream.alloc_expr(
                {
                    "proj": {
                        "typeName": pr["typeName"],
                        "idx": pr["idx"],
                        "struct": rec_e(pr["struct"]),
                    }
                }
            )
        elif "mdata" in r:
            md = r["mdata"]
            res = stream.alloc_expr(
                {"mdata": {"data": md["data"], "expr": rec_e(md["expr"])}}
            )
        else:
            raise ValueError(r)
        ememo[eid] = res
        return res

    return rec_e(root_eid)


def collect_expr_const_refs(
    stream: NdjsonStream, root_eid: int
) -> List[Tuple[str, List[Tuple[Any, ...]]]]:
    seen_e: Set[int] = set()
    refs: List[Tuple[str, List[Tuple[Any, ...]]]] = []
    stack = [root_eid]
    while stack:
        eid = stack.pop()
        if eid in seen_e:
            continue
        seen_e.add(eid)
        r = stream.exprs[eid]
        if "const" in r:
            c = r["const"]
            refs.append(
                (stream.name_str[c["name"]], [simp_level_ast(stream, u) for u in c["us"]])
            )
        elif "app" in r:
            stack.append(r["app"]["fn"])
            stack.append(r["app"]["arg"])
        elif "lam" in r:
            stack.append(r["lam"]["type"])
            stack.append(r["lam"]["body"])
        elif "forallE" in r:
            stack.append(r["forallE"]["type"])
            stack.append(r["forallE"]["body"])
        elif "letE" in r:
            stack.append(r["letE"]["type"])
            stack.append(r["letE"]["value"])
            stack.append(r["letE"]["body"])
        elif "proj" in r:
            stack.append(r["proj"]["struct"])
        elif "mdata" in r:
            stack.append(r["mdata"]["expr"])
    return refs


def topo_lambda_lift(
    stream: NdjsonStream,
    expected_root: Optional[str],
    target_thm: str,
    allowlist_names: Set[str],
) -> Tuple[List[str], Dict[str, Any]]:
    """Bottom-up topological lambda-lifting across liftable helper theorems."""
    unliftable: Set[str] = set()
    queue: List[str] = [expected_root] if expected_root else []
    for kind, p in stream.decls:
        if kind == "inductive":
            for t in p["types"]:
                queue.append(stream.name_str[t["name"]])
            for c in p["ctors"]:
                queue.append(stream.name_str[c["name"]])
            for r in p["recs"]:
                queue.append(stream.name_str[r["name"]])
        elif kind != "thm":
            queue.append(stream.name_str[p["name"]])

    while queue:
        nm = queue.pop()
        if nm in unliftable or nm not in stream.decl_by_name:
            continue
        unliftable.add(nm)
        kind, p = stream.decl_by_name[nm]
        eids = []
        if kind == "inductive":
            for t in p["types"]:
                eids.append(t["type"])
            for c in p["ctors"]:
                eids.append(c["type"])
            for r in p["recs"]:
                eids.append(r["type"])
                for rl in r["rules"]:
                    eids.append(rl["rhs"])
        else:
            eids.append(p["type"])
            if "value" in p:
                eids.append(p["value"])
        for eid in eids:
            for dep, _ in collect_expr_const_refs(stream, eid):
                if dep not in unliftable:
                    queue.append(dep)

    effective_allow = allowlist_names - unliftable
    unliftable_kept = sorted(allowlist_names & unliftable)

    lifted_hyps: Dict[str, List[Tuple[str, Tuple[Tuple[Any, ...], ...]]]] = {}
    new_decls: List[Tuple[str, Dict[str, Any]]] = []
    h_name_nid = stream.alloc_name_str(0, "_m3_h")

    for kind, p in stream.decls:
        if kind != "thm":
            new_decls.append((kind, p))
            continue
        nm = stream.name_str[p["name"]]
        if nm in effective_allow or nm in unliftable:
            new_decls.append((kind, p))
            continue

        needed: Set[Tuple[str, Tuple[Tuple[Any, ...], ...]]] = set()
        for ref_nm, call_us in collect_expr_const_refs(stream, p["value"]):
            if ref_nm in effective_allow:
                needed.add((ref_nm, tuple(call_us)))
            elif ref_nm in lifted_hyps:
                _, hp = stream.decl_by_name[ref_nm]
                h_map = dict(
                    zip([stream.name_str[u] for u in hp["levelParams"]], call_us)
                )
                for a_nm, hyp_us in lifted_hyps[ref_nm]:
                    needed.add(
                        (a_nm, tuple(subst_level_ast(u, h_map) for u in hyp_us))
                    )

        if not needed:
            new_decls.append((kind, p))
            continue

        hyps_sorted = sorted(needed, key=lambda x: (x[0], repr(x[1])))
        lifted_hyps[nm] = hyps_sorted
        k = len(hyps_sorted)
        slot_of = {h: idx for idx, h in enumerate(hyps_sorted)}
        memo: Dict[Tuple[int, int], int] = {}

        def rw(eid: int, depth: int) -> int:
            key = (eid, depth)
            if key in memo:
                return memo[key]
            r = stream.exprs[eid]
            if "bvar" in r:
                assert r["bvar"] < depth, f"Free BVar {r['bvar']} at depth {depth}"
                res = eid
            elif "const" in r:
                c = r["const"]
                cnm = stream.name_str[c["name"]]
                call_us = tuple(simp_level_ast(stream, u) for u in c["us"])
                if cnm in effective_allow:
                    slot = slot_of[(cnm, call_us)]
                    res = stream.alloc_expr({"bvar": depth + (k - 1 - slot)})
                elif cnm in lifted_hyps:
                    _, hp = stream.decl_by_name[cnm]
                    h_map = dict(
                        zip([stream.name_str[u] for u in hp["levelParams"]], call_us)
                    )
                    cur = eid
                    for a_nm, hyp_us in lifted_hyps[cnm]:
                        inst_us = tuple(subst_level_ast(u, h_map) for u in hyp_us)
                        slot = slot_of[(a_nm, inst_us)]
                        bv = stream.alloc_expr({"bvar": depth + (k - 1 - slot)})
                        cur = stream.alloc_expr({"app": {"fn": cur, "arg": bv}})
                    res = cur
                else:
                    res = eid
            elif "app" in r:
                a = r["app"]
                res = stream.alloc_expr(
                    {"app": {"fn": rw(a["fn"], depth), "arg": rw(a["arg"], depth)}}
                )
            elif "lam" in r:
                l = r["lam"]
                res = stream.alloc_expr(
                    {
                        "lam": {
                            "name": l["name"],
                            "type": rw(l["type"], depth),
                            "body": rw(l["body"], depth + 1),
                            "binderInfo": l["binderInfo"],
                        }
                    }
                )
            elif "forallE" in r:
                f = r["forallE"]
                res = stream.alloc_expr(
                    {
                        "forallE": {
                            "name": f["name"],
                            "type": rw(f["type"], depth),
                            "body": rw(f["body"], depth + 1),
                            "binderInfo": f["binderInfo"],
                        }
                    }
                )
            elif "letE" in r:
                le = r["letE"]
                res = stream.alloc_expr(
                    {
                        "letE": {
                            "name": le["name"],
                            "type": rw(le["type"], depth),
                            "value": rw(le["value"], depth),
                            "body": rw(le["body"], depth + 1),
                            "nondep": False,
                        }
                    }
                )
            elif "proj" in r:
                pr = r["proj"]
                res = stream.alloc_expr(
                    {
                        "proj": {
                            "typeName": pr["typeName"],
                            "idx": pr["idx"],
                            "struct": rw(pr["struct"], depth),
                        }
                    }
                )
            elif "mdata" in r:
                md = r["mdata"]
                res = stream.alloc_expr(
                    {"mdata": {"data": md["data"], "expr": rw(md["expr"], depth)}}
                )
            else:
                res = eid
            memo[key] = res
            return res

        new_val = rw(p["value"], 0)
        new_ty = p["type"]
        for a_nm, hyp_us in reversed(hyps_sorted):
            _, ap = stream.decl_by_name[a_nm]
            a_lparams = [stream.name_str[u] for u in ap["levelParams"]]
            dom_ty = subst_expr_levels(stream, ap["type"], a_lparams, list(hyp_us))
            new_ty = stream.alloc_expr(
                {
                    "forallE": {
                        "name": h_name_nid,
                        "type": dom_ty,
                        "body": new_ty,
                        "binderInfo": "default",
                    }
                }
            )
            new_val = stream.alloc_expr(
                {
                    "lam": {
                        "name": h_name_nid,
                        "type": dom_ty,
                        "body": new_val,
                        "binderInfo": "default",
                    }
                }
            )

        np = dict(p)
        np["type"] = new_ty
        np["value"] = new_val
        new_decls.append(("thm", np))
        stream.decl_by_name[nm] = ("thm", np)

    roots = [r for r in (expected_root, target_thm) if r]
    out_lines, stats = stream.emit_gc_ndjson(new_decls, roots)
    return out_lines, {
        "lifted_by_thm": {
            k: [(a, repr(u)) for a, u in v] for k, v in lifted_hyps.items()
        },
        "target_hyps_raw": lifted_hyps.get(target_thm, []),
        "unliftable_kept": unliftable_kept,
        "gc_stats": stats,
    }


def merge_stream_checked(dst: NdjsonStream, lines: List[str]) -> None:
    """Merge an NDJSON stream into `dst`, verifying canonical equality on shared decls."""
    src_s = NdjsonStream()
    src_s.parse_lines(lines)
    sn = {0: 0}
    for nid in sorted(src_s.names):
        r = src_s.names[nid]
        if "str" in r:
            sn[nid] = dst.alloc_name_str(sn[r["str"]["pre"]], r["str"]["str"])
        else:
            sn[nid] = dst.alloc_name_num(sn[r["num"]["pre"]], r["num"]["i"])
    sl = {0: 0}

    def ml(x: int) -> int:
        if x in sl:
            return sl[x]
        r = src_s.levels[x]
        if "succ" in r:
            res = dst.alloc_level({"succ": ml(r["succ"])})
        elif "max" in r:
            res = dst.alloc_level({"max": [ml(r["max"][0]), ml(r["max"][1])]})
        elif "imax" in r:
            res = dst.alloc_level({"imax": [ml(r["imax"][0]), ml(r["imax"][1])]})
        elif "param" in r:
            res = dst.alloc_level({"param": sn[r["param"]]})
        else:
            raise ValueError(r)
        sl[x] = res
        return res

    for x in sorted(src_s.levels):
        ml(x)
    se: Dict[int, int] = {}
    for eid in sorted(src_s.exprs):
        r = src_s.exprs[eid]
        if "bvar" in r or "natVal" in r or "strVal" in r:
            se[eid] = dst.alloc_expr(dict(r))
        elif "sort" in r:
            se[eid] = dst.alloc_expr({"sort": sl[r["sort"]]})
        elif "const" in r:
            c = r["const"]
            se[eid] = dst.alloc_expr(
                {"const": {"name": sn[c["name"]], "us": [sl[u] for u in c["us"]]}}
            )
        elif "app" in r:
            a = r["app"]
            se[eid] = dst.alloc_expr({"app": {"fn": se[a["fn"]], "arg": se[a["arg"]]}})
        elif "lam" in r:
            l = r["lam"]
            se[eid] = dst.alloc_expr(
                {
                    "lam": {
                        "name": sn[l["name"]],
                        "type": se[l["type"]],
                        "body": se[l["body"]],
                        "binderInfo": l["binderInfo"],
                    }
                }
            )
        elif "forallE" in r:
            f = r["forallE"]
            se[eid] = dst.alloc_expr(
                {
                    "forallE": {
                        "name": sn[f["name"]],
                        "type": se[f["type"]],
                        "body": se[f["body"]],
                        "binderInfo": f["binderInfo"],
                    }
                }
            )
        elif "letE" in r:
            le = r["letE"]
            se[eid] = dst.alloc_expr(
                {
                    "letE": {
                        "name": sn[le["name"]],
                        "type": se[le["type"]],
                        "value": se[le["value"]],
                        "body": se[le["body"]],
                        "nondep": False,
                    }
                }
            )
        elif "proj" in r:
            pr = r["proj"]
            se[eid] = dst.alloc_expr(
                {
                    "proj": {
                        "typeName": sn[pr["typeName"]],
                        "idx": pr["idx"],
                        "struct": se[pr["struct"]],
                    }
                }
            )
        elif "mdata" in r:
            md = r["mdata"]
            se[eid] = dst.alloc_expr(
                {"mdata": {"data": md["data"], "expr": se[md["expr"]]}}
            )

    ex = set(dst.decl_by_name.keys())
    for kind, p in src_s.decls:
        if kind == "inductive":
            fnm = src_s.name_str[p["types"][0]["name"]]
            if fnm in ex:
                h1 = canonical_merkle_cone_hash(dst, fnm)["root_merkle_sha256"]
                h2 = canonical_merkle_cone_hash(src_s, fnm)["root_merkle_sha256"]
                assert h1 == h2, f"InductiveBlock Merkle drift on {fnm}: {h1} != {h2}"
                continue
            nt = [
                {
                    **t,
                    "name": sn[t["name"]],
                    "all": [sn[a] for a in t["all"]],
                    "ctors": [sn[c] for c in t["ctors"]],
                    "levelParams": [sn[u] for u in t["levelParams"]],
                    "type": se[t["type"]],
                }
                for t in p["types"]
            ]
            nc = [
                {
                    **c,
                    "name": sn[c["name"]],
                    "induct": sn[c["induct"]],
                    "levelParams": [sn[u] for u in c["levelParams"]],
                    "type": se[c["type"]],
                }
                for c in p["ctors"]
            ]
            nr = [
                {
                    **r,
                    "name": sn[r["name"]],
                    "all": [sn[a] for a in r["all"]],
                    "levelParams": [sn[u] for u in r["levelParams"]],
                    "type": se[r["type"]],
                    "rules": [
                        {"ctor": sn[rl["ctor"]], "nfields": rl["nfields"], "rhs": se[rl["rhs"]]}
                        for rl in r["rules"]
                    ],
                }
                for r in p["recs"]
            ]
            blk = {"types": nt, "ctors": nc, "recs": nr}
            dst.decls.append(("inductive", blk))
            for t in nt:
                nm = dst.name_str[t["name"]]
                ex.add(nm)
                dst.decl_by_name[nm] = ("inductive", blk)
            for c in nc:
                nm = dst.name_str[c["name"]]
                ex.add(nm)
                dst.decl_by_name[nm] = ("inductive", blk)
            for r in nr:
                nm = dst.name_str[r["name"]]
                ex.add(nm)
                dst.decl_by_name[nm] = ("inductive", blk)
        else:
            nm = src_s.name_str[p["name"]]
            if nm in ex:
                ek, _ = dst.decl_by_name[nm]
                assert ek == kind, f"Shared decl kind drift on {nm}: {ek} vs {kind}"
                h1 = canonical_merkle_cone_hash(dst, nm)["root_merkle_sha256"]
                h2 = canonical_merkle_cone_hash(src_s, nm)["root_merkle_sha256"]
                assert h1 == h2, f"Shared decl Merkle drift on {nm}: {h1} != {h2}"
                continue
            ex.add(nm)
            np = dict(p)
            np["name"] = sn[p["name"]]
            np["levelParams"] = [sn[u] for u in p["levelParams"]]
            np["type"] = se[p["type"]]
            if "value" in np:
                np["value"] = se[p["value"]]
            if "all" in np:
                np["all"] = [sn[a] for a in p["all"]]
            dst.decls.append((kind, np))
            dst.decl_by_name[nm] = (kind, np)


def tarjan_union_check(shards: Dict[str, Dict[str, Any]]) -> Tuple[bool, str]:
    nodes = sorted(shards.keys())
    edges = {
        s: set(info["mir_calls"]) | set(info["indirect_prov"]) | set(info["m3_callee_hyps"])
        for s, info in shards.items()
    }
    idx: Dict[str, int] = {}
    low: Dict[str, int] = {}
    st: List[str] = []
    on: Set[str] = set()
    sccs: List[List[str]] = []
    cnt = [0]

    def sc(v: str) -> None:
        idx[v] = low[v] = cnt[0]
        cnt[0] += 1
        st.append(v)
        on.add(v)
        for w in sorted(edges.get(v, set())):
            if w not in idx:
                sc(w)
                low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], idx[w])
        if low[v] == idx[v]:
            comp = []
            while True:
                w = st.pop()
                on.remove(w)
                comp.append(w)
                if w == v:
                    break
            sccs.append(sorted(comp))

    for v in nodes:
        if v not in idx:
            sc(v)
    for comp in sccs:
        if len(comp) > 1:
            return False, f"REJECT_UNION_CYCLE:{','.join(comp)}"
        u = comp[0]
        if u in edges[u]:
            return False, f"REJECT_SELF_LOOP:{u}"
    return True, f"ACCEPT_DAG:{len(sccs)}_shards"


# ---------------------------------------------------------------------------
# Probes 1..5
# ---------------------------------------------------------------------------


def probe_1_inductive_rec_hints_merkle(tmp: str) -> Dict[str, Any]:
    d = os.path.join(tmp, "p1")
    os.makedirs(d, exist_ok=True)
    src = os.path.join(d, "Probe1.lean")
    open(src, "w").write("""prelude
import Init.Core
namespace Probe1
inductive MyNat where
  | z : MyNat
  | s : MyNat → MyNat
def toNat : MyNat → Nat
  | .z => 0
  | .s n => toNat n + 1
theorem check_one : toNat (.s .z) = 1 := rfl
end Probe1
""")
    compile_lean(src, d, os.path.join(d, "Probe1.olean"), [d])
    nd = os.path.join(d, "base.ndjson")
    export_ndjson(["Probe1"], ["Probe1.check_one"], nd, [d])
    base_lines = [l for l in open(nd).read().splitlines() if l.strip()]
    st_base = NdjsonStream()
    st_base.parse_lines(base_lines)
    base_h = canonical_merkle_cone_hash(st_base, "Probe1.check_one")["root_merkle_sha256"]

    # Mutate MyNat.rec rules[1].rhs := rules[0].rhs
    m1_lines = []
    for line in base_lines:
        obj = json.loads(line)
        if "inductive" in obj:
            for r in obj["inductive"]["recs"]:
                if st_base.name_str[r["name"]] == "Probe1.MyNat.rec":
                    r["rules"][1]["rhs"] = r["rules"][0]["rhs"]
        m1_lines.append(json.dumps(obj, separators=(",", ":")))
    m1_nd = os.path.join(d, "mut_rec_rhs.ndjson")
    open(m1_nd, "w").write("\n".join(m1_lines) + "\n")
    st_m1 = NdjsonStream()
    st_m1.parse_lines(m1_lines)
    m1_h = canonical_merkle_cone_hash(st_m1, "Probe1.check_one")["root_merkle_sha256"]

    # Mutate toNat hints -> opaque
    m2_lines = []
    for line in base_lines:
        obj = json.loads(line)
        if "def" in obj and st_base.name_str[obj["def"]["name"]] == "Probe1.toNat":
            obj["def"]["hints"] = "opaque"
        m2_lines.append(json.dumps(obj, separators=(",", ":")))
    m2_nd = os.path.join(d, "mut_hints.ndjson")
    open(m2_nd, "w").write("\n".join(m2_lines) + "\n")
    st_m2 = NdjsonStream()
    st_m2.parse_lines(m2_lines)
    m2_h = canonical_merkle_cone_hash(st_m2, "Probe1.check_one")["root_merkle_sha256"]

    # Flip MyNat.rec k -> true
    m3_lines = []
    for line in base_lines:
        obj = json.loads(line)
        if "inductive" in obj:
            for r in obj["inductive"]["recs"]:
                if st_base.name_str[r["name"]] == "Probe1.MyNat.rec":
                    r["k"] = True
        m3_lines.append(json.dumps(obj, separators=(",", ":")))
    m3_nd = os.path.join(d, "mut_k.ndjson")
    open(m3_nd, "w").write("\n".join(m3_lines) + "\n")
    st_m3 = NdjsonStream()
    st_m3.parse_lines(m3_lines)
    m3_h = canonical_merkle_cone_hash(st_m3, "Probe1.check_one")["root_merkle_sha256"]

    return {
        "base_merkle_prefix": base_h[:16],
        "mut_rec_rhs_kernels": check_all_4_kernels(m1_nd, d, "m1"),
        "mut_rec_rhs_merkle_changed": m1_h != base_h,
        "mut_defn_hints_kernels": check_all_4_kernels(m2_nd, d, "m2"),
        "mut_defn_hints_merkle_changed": m2_h != base_h,
        "mut_rec_k_kernels": check_all_4_kernels(m3_nd, d, "m3"),
        "mut_rec_k_merkle_changed": m3_h != base_h,
    }


def probe_2_canonical_reserialization(tmp: str) -> Dict[str, Any]:
    d = os.path.join(tmp, "p2")
    os.makedirs(d, exist_ok=True)
    src = os.path.join(d, "Probe2.lean")
    open(src, "w").write("""prelude
import Init.Core
namespace Probe2
inductive Rose : Type
  | node : List Rose → Rose
mutual
  inductive Even : Type
    | zero : Even
    | succ : Odd → Even
  inductive Odd : Type
    | succ : Even → Odd
end
def roseDepth : Rose → Nat
  | .node xs => listDepth xs + 1
where
  listDepth : List Rose → Nat
    | List.nil => 0
    | List.cons r rs => roseDepth r + listDepth rs
def evenToNat : Even → Nat
  | .zero => 0
  | .succ o => oddToNat o + 1
where
  oddToNat : Odd → Nat
    | .succ e => evenToNat e + 1
def idAll {α : Type} ⦃β : Type⦄ [Inhabited α] (x : α) (_ : β) : α := x
theorem verify :
    let x : Nat := 2
    (Fin.mk 0 (Nat.zero_lt_succ x) : Fin (x + 1)).val = 0 ∧
    roseDepth (.node (List.cons (.node List.nil) List.nil)) = 2 ∧
    evenToNat (.succ (.succ .zero)) = 2 ∧
    idAll (α := Nat) (β := Unit) x () + 5 = 7 :=
  let x : Nat := 2
  have h_nondep : Nat := 5
  let f : Fin (x + 1) := Fin.mk 0 (Nat.zero_lt_succ x)
  have h1 : f.val = 0 := rfl
  have h2 : roseDepth (.node (List.cons (.node List.nil) List.nil)) = 2 := rfl
  have h3 : evenToNat (.succ (.succ .zero)) = 2 := rfl
  have h_use_nd : h_nondep = h_nondep := rfl
  have h4 : idAll (α := Nat) (β := Unit) x () + 5 = 7 :=
    Eq.ndrec (motive := fun _ => idAll (α := Nat) (β := Unit) x () + 5 = 7) rfl h_use_nd
  And.intro h1 (And.intro h2 (And.intro h3 h4))
end Probe2
""")
    compile_lean(src, d, os.path.join(d, "Probe2.olean"), [d])
    raw_nd = os.path.join(d, "raw.ndjson")
    export_ndjson(["Probe2"], ["Probe2.verify"], raw_nd, [d])
    raw_lines = [l for l in open(raw_nd).read().splitlines() if l.strip()]

    st = NdjsonStream()
    st.parse_lines(raw_lines)
    x_nid = st.alloc_name_str(0, "_x")

    # Canonical lossless re-serialization (preserving rules order)
    canon_lines = [st.meta_line]
    for nid in sorted(st.names):
        rec = dict(st.names[nid])
        rec["in"] = nid
        canon_lines.append(json.dumps(rec, separators=(",", ":")))
    for lid in sorted(st.levels):
        rec = dict(st.levels[lid])
        rec["il"] = lid
        canon_lines.append(json.dumps(rec, separators=(",", ":")))
    for eid in sorted(st.exprs):
        rec = copy.deepcopy(st.exprs[eid])
        if "lam" in rec:
            rec["lam"]["name"] = x_nid
            rec["lam"]["binderInfo"] = "default"
        elif "forallE" in rec:
            rec["forallE"]["name"] = x_nid
            rec["forallE"]["binderInfo"] = "default"
        elif "letE" in rec:
            rec["letE"]["name"] = x_nid
            rec["letE"]["nondep"] = False
        rec["ie"] = eid
        canon_lines.append(json.dumps(rec, separators=(",", ":")))
    for kind, p in st.decls:
        canon_lines.append(json.dumps({kind: p}, separators=(",", ":")))
    nd_canon = os.path.join(d, "canon.ndjson")
    open(nd_canon, "w").write("\n".join(canon_lines) + "\n")

    # Reverse recs only vs reverse rules only vs omit nondep key
    rev_recs = []
    rev_rules = []
    omit_nd = []
    for line in raw_lines:
        o1 = json.loads(line)
        o2 = json.loads(line)
        o3 = json.loads(line)
        if "inductive" in o1:
            o1["inductive"]["recs"] = list(reversed(o1["inductive"]["recs"]))
            for r in o2["inductive"]["recs"]:
                r["rules"] = list(reversed(r["rules"]))
        if "ie" in o3 and "letE" in o3:
            o3["letE"].pop("nondep", None)
        rev_recs.append(json.dumps(o1, separators=(",", ":")))
        rev_rules.append(json.dumps(o2, separators=(",", ":")))
        omit_nd.append(json.dumps(o3, separators=(",", ":")))
    p_rr = os.path.join(d, "rev_recs.ndjson")
    p_rl = os.path.join(d, "rev_rules.ndjson")
    p_on = os.path.join(d, "omit_nd.ndjson")
    open(p_rr, "w").write("\n".join(rev_recs) + "\n")
    open(p_rl, "w").write("\n".join(rev_rules) + "\n")
    open(p_on, "w").write("\n".join(omit_nd) + "\n")

    return {
        "kernels_canon_preserve_rules": check_all_4_kernels(nd_canon, d, "canon"),
        "kernels_reversed_recs_only": check_all_4_kernels(p_rr, d, "rev_recs"),
        "kernels_reversed_rules_only": check_all_4_kernels(p_rl, d, "rev_rules"),
        "kernels_omit_nondep_key": check_all_4_kernels(p_on, d, "omit_nd"),
    }


def probe_3_option_b_and_dag_ratio(tmp: str) -> Dict[str, Any]:
    d = os.path.join(tmp, "p3")
    os.makedirs(d, exist_ok=True)
    lib_src = os.path.join(d, "PolyLib.lean")
    open(lib_src, "w").write("""prelude
import Init.Core
namespace PolyLib
theorem poly_zero.{u, v} (α : Type u) (β : Type v) : (0 : Nat) = 0 := rfl
theorem mono_add_zero (n : Nat) : n + 0 = n := rfl
theorem def_locked : (0 : Nat) = 0 := rfl
def locked_val : Nat := (fun (_ : (0 : Nat) = 0) => 42) def_locked
end PolyLib
""")
    pf_src = os.path.join(d, "OptBProof.lean")
    open(pf_src, "w").write("""prelude
import Init.Core
import PolyLib
namespace OptBProof
def Expected.claim : Prop := (0 : Nat) + 0 = 0 ∧ PolyLib.locked_val = 42
theorem sub_helper.{v} (β : Type v) : (0 : Nat) = 0 :=
  PolyLib.poly_zero.{max v 1, 0} (PUnit.{max v 1 + 1}) (PUnit.{1})
theorem poly_helper.{v} (β : Type v) : (0 : Nat) = 0 :=
  Eq.trans (sub_helper.{v} β) (PolyLib.poly_zero.{max v 1, 0} (PUnit.{max v 1 + 1}) (PUnit.{1}))
theorem verify._proof_1 (n : Nat) : n + 0 = n :=
  Eq.ndrec (motive := fun x => n + x = n) (PolyLib.mono_add_zero n) (PolyLib.poly_zero.{0, 0} Nat Nat)
theorem verify : Expected.claim :=
  let h_mono : (0 : Nat) + 0 = 0 := verify._proof_1 0
  let h_p0 : (0 : Nat) = 0 := poly_helper.{0} (PUnit.{1})
  let h_p2 : (0 : Nat) = 0 := poly_helper.{2} (PUnit.{3})
  let h_direct : (0 : Nat) = 0 := PolyLib.poly_zero.{1, 0} (PUnit.{2}) (PUnit.{1})
  let h_all : (0 : Nat) = 0 := Eq.trans h_p0 (Eq.trans h_p2 h_direct)
  And.intro (Eq.ndrec (motive := fun x => (0 : Nat) + x = 0) h_mono h_all) rfl
end OptBProof
""")
    compile_lean(lib_src, d, os.path.join(d, "PolyLib.olean"), [d])
    compile_lean(pf_src, d, os.path.join(d, "OptBProof.olean"), [d])
    raw_nd = os.path.join(d, "raw.ndjson")
    lib_nd = os.path.join(d, "lib.ndjson")
    export_ndjson(["OptBProof"], ["OptBProof.verify"], raw_nd, [d])
    export_ndjson(["PolyLib"], ["PolyLib.poly_zero", "PolyLib.mono_add_zero"], lib_nd, [d])

    st = NdjsonStream()
    st.parse_lines(open(raw_nd).readlines())
    allow = {"PolyLib.poly_zero", "PolyLib.mono_add_zero", "PolyLib.def_locked"}
    m3_lines, info = topo_lambda_lift(
        st, "OptBProof.Expected.claim", "OptBProof.verify", allow
    )
    m3_nd = os.path.join(d, "m3.ndjson")
    open(m3_nd, "w").write("\n".join(m3_lines) + "\n")

    merged = NdjsonStream()
    merged.parse_lines(open(lib_nd).readlines())
    merge_stream_checked(merged, m3_lines)
    _, vp = merged.decl_by_name["OptBProof.verify"]
    cur_ty = vp["type"]
    app_val = merged.alloc_expr({"const": {"name": vp["name"], "us": []}})
    for a_nm, hyp_us in info["target_hyps_raw"]:
        cur_ty = merged.exprs[cur_ty]["forallE"]["body"]
        us_lids = [alloc_level_ast(merged, u) for u in hyp_us]
        hconst = merged.alloc_expr(
            {"const": {"name": merged.str_to_nid[a_nm], "us": us_lids}}
        )
        app_val = merged.alloc_expr({"app": {"fn": app_val, "arg": hconst}})
    lnm = "OptBProof.verify_linked"
    lnid = merged.alloc_dotted_name(lnm)
    merged.decls.append(
        ("thm", {"all": [lnid], "levelParams": [], "name": lnid, "type": cur_ty, "value": app_val})
    )
    merged.decl_by_name[lnm] = ("thm", merged.decls[-1][1])
    linked_lines, _ = merged.emit_gc_ndjson(
        merged.decls, ["OptBProof.Expected.claim", lnm]
    )
    linked_nd = os.path.join(d, "linked.ndjson")
    open(linked_nd, "w").write("\n".join(linked_lines) + "\n")

    # 40-deep nested let/lam DAG memoization ratio check
    lets = "\n".join(
        f"  let x{i} : Nat := (fun (_ : 0 + 0 = 0) => x{i-1} + 0) (PolyLib.mono_add_zero 0)"
        if i > 0
        else "  let x0 : Nat := (fun (_ : 0 + 0 = 0) => 0) (PolyLib.mono_add_zero 0)"
        for i in range(40)
    )
    dag_src = os.path.join(d, "DagProof.lean")
    open(dag_src, "w").write(f"""prelude
import Init.Core
import PolyLib
namespace DagProof
theorem verify : 0 = 0 := by
{lets}
  have _ := x39
  exact rfl
end DagProof
""")
    compile_lean(dag_src, d, os.path.join(d, "DagProof.olean"), [d])
    dag_nd = os.path.join(d, "dag.ndjson")
    export_ndjson(["DagProof"], ["DagProof.verify"], dag_nd, [d])
    st_dag = NdjsonStream()
    st_dag.parse_lines(open(dag_nd).readlines())
    in_exprs = len(st_dag.exprs)
    dag_m3_lines, dag_info = topo_lambda_lift(
        st_dag, None, "DagProof.verify", {"PolyLib.mono_add_zero"}
    )
    dag_m3_nd = os.path.join(d, "dag_m3.ndjson")
    open(dag_m3_nd, "w").write("\n".join(dag_m3_lines) + "\n")

    return {
        "lifted_by_thm": info["lifted_by_thm"],
        "unliftable_kept": info["unliftable_kept"],
        "m3_kernels": check_all_4_kernels(m3_nd, d, "m3"),
        "linked_kernels": check_all_4_kernels(linked_nd, d, "linked"),
        "dag_exprs_in": in_exprs,
        "dag_exprs_out": dag_info["gc_stats"]["emitted_exprs"],
        "dag_expansion_ratio": round(
            dag_info["gc_stats"]["emitted_exprs"] / max(1, in_exprs), 3
        ),
        "dag_m3_kernels": check_all_4_kernels(dag_m3_nd, d, "dag_m3"),
    }


def probe_4_multi_shard_tarjan_and_link(tmp: str) -> Dict[str, Any]:
    d = os.path.join(tmp, "p4")
    os.makedirs(d, exist_ok=True)
    files = {
        "BaseThm": """prelude
import Init.Core
namespace BaseThm
theorem add_zero_eq (n : Nat) : n + 0 = n := rfl
end BaseThm
""",
        "Shard1": """prelude
import Init.Core
import BaseThm
namespace Shard1
def f1 (x : Nat) : Nat := x + 0
def Expected.claim : Prop := ∀ x : Nat, f1 x = x
theorem Proof.verify : Expected.claim := fun x => BaseThm.add_zero_eq x
end Shard1
""",
        "Shard2": """prelude
import Init.Core
import BaseThm
import Shard1
namespace Shard2
def f2 (x : Nat) : Nat := Shard1.f1 x + 0
def Expected.claim : Prop := ∀ x : Nat, f2 x = x
theorem Proof.verify : Expected.claim := fun x =>
  Eq.trans (BaseThm.add_zero_eq (Shard1.f1 x)) (Shard1.Proof.verify x)
end Shard2
""",
        "Shard3": """prelude
import Init.Core
import Shard1
import Shard2
namespace Shard3
def f3 (x : Nat) : Nat := Shard1.f1 (Shard2.f2 x)
def Expected.claim : Prop := ∀ x : Nat, f3 x = x
theorem Proof.verify : Expected.claim := fun x =>
  Eq.trans (Shard1.Proof.verify (Shard2.f2 x)) (Shard2.Proof.verify x)
end Shard3
""",
    }
    for nm, body in files.items():
        src = os.path.join(d, f"{nm}.lean")
        open(src, "w").write(body)
        compile_lean(src, d, os.path.join(d, f"{nm}.olean"), [d])

    base_nd = os.path.join(d, "base.ndjson")
    export_ndjson(["BaseThm"], ["BaseThm.add_zero_eq"], base_nd, [d])

    stub_targets = {"BaseThm.add_zero_eq", "Shard1.Proof.verify", "Shard2.Proof.verify"}
    shard_m3: Dict[str, List[str]] = {}
    shard_hyps: Dict[str, List[Tuple[str, Tuple[Tuple[Any, ...], ...]]]] = {}
    for nm in ("Shard1", "Shard2", "Shard3"):
        raw = os.path.join(d, f"{nm}_raw.ndjson")
        export_ndjson([nm], [f"{nm}.Proof.verify"], raw, [d])
        st = NdjsonStream()
        st.parse_lines(open(raw).readlines())
        lines, info = topo_lambda_lift(
            st, f"{nm}.Expected.claim", f"{nm}.Proof.verify", stub_targets
        )
        shard_m3[nm] = lines
        shard_hyps[nm] = info["target_hyps_raw"]

    merged = NdjsonStream()
    merged.parse_lines(open(base_nd).readlines())
    linked_map = {"BaseThm.add_zero_eq": "BaseThm.add_zero_eq"}
    for nm in ("Shard1", "Shard2", "Shard3"):
        merge_stream_checked(merged, shard_m3[nm])
        raw_thm = f"{nm}.Proof.verify"
        _, tp = merged.decl_by_name[raw_thm]
        cur_ty = tp["type"]
        app_val = merged.alloc_expr({"const": {"name": tp["name"], "us": []}})
        for a_nm, hyp_us in shard_hyps[nm]:
            cur_ty = merged.exprs[cur_ty]["forallE"]["body"]
            us_lids = [alloc_level_ast(merged, u) for u in hyp_us]
            hconst = merged.alloc_expr(
                {"const": {"name": merged.str_to_nid[linked_map[a_nm]], "us": us_lids}}
            )
            app_val = merged.alloc_expr({"app": {"fn": app_val, "arg": hconst}})
        lnm = f"{nm}.Proof.verify_linked"
        lnid = merged.alloc_dotted_name(lnm)
        merged.decls.append(
            ("thm", {"all": [lnid], "levelParams": [], "name": lnid, "type": cur_ty, "value": app_val})
        )
        merged.decl_by_name[lnm] = ("thm", merged.decls[-1][1])
        linked_map[raw_thm] = lnm

    final_lines, _ = merged.emit_gc_ndjson(
        merged.decls, ["Shard3.Proof.verify_linked", "Shard3.Expected.claim"]
    )
    final_nd = os.path.join(d, "linked_dag.ndjson")
    open(final_nd, "w").write("\n".join(final_lines) + "\n")

    return {
        "tarjan_valid": tarjan_union_check({
            "Shard1": {"mir_calls": [], "indirect_prov": [], "m3_callee_hyps": []},
            "Shard2": {"mir_calls": ["Shard1"], "indirect_prov": [], "m3_callee_hyps": ["Shard1"]},
            "Shard3": {"mir_calls": ["Shard1", "Shard2"], "indirect_prov": [], "m3_callee_hyps": ["Shard1", "Shard2"]},
        }),
        "tarjan_mutual_proof_cycle": tarjan_union_check({
            "F": {"mir_calls": [], "indirect_prov": [], "m3_callee_hyps": ["G"]},
            "G": {"mir_calls": [], "indirect_prov": [], "m3_callee_hyps": ["F"]},
        }),
        "tarjan_indirect_self_loop": tarjan_union_check({
            "apply_cb": {"mir_calls": [], "indirect_prov": [], "m3_callee_hyps": []},
            "bad": {"mir_calls": ["apply_cb"], "indirect_prov": ["bad"], "m3_callee_hyps": ["bad"]},
        }),
        "linked_lines": len(final_lines),
        "linked_kernels": check_all_4_kernels(final_nd, d, "linked_dag"),
    }


def probe_5_module_olean_private(tmp: str) -> Dict[str, Any]:
    d = os.path.join(tmp, "p5")
    os.makedirs(d, exist_ok=True)
    mod_src = os.path.join(d, "ModHidden.lean")
    open(mod_src, "w").write("""module
prelude
public import Init.Core
namespace ModHidden
public section
def unexposed_fn (x : Nat) : Nat := x + 1
@[expose] def exposed_fn (x : Nat) : Nat := x + 1
theorem secret_sorry : (0 : Nat) = 1 := sorry
theorem clean_thm : (0 : Nat) = 0 := rfl
end
end ModHidden
""")
    compile_lean(mod_src, d, os.path.join(d, "ModHidden.olean"), [d])
    decls = [
        "ModHidden.unexposed_fn",
        "ModHidden.exposed_fn",
        "ModHidden.secret_sorry",
        "ModHidden.clean_thm",
    ]
    exp_full = export_ndjson_raw(["ModHidden"], decls, [d])
    st_full = NdjsonStream()
    st_full.parse_lines(exp_full["stdout"].splitlines())
    kinds = {
        nm: st_full.decl_by_name[nm][0]
        for nm in decls
        if nm in st_full.decl_by_name
    }
    axioms = sorted(
        st_full.name_str[p["name"]]
        for k, p in st_full.decls
        if k == "axiom"
    )

    # Test missing-constant stderr panic with rc=0
    exp_missing = export_ndjson_raw(["ModHidden"], ["ModHidden.does_not_exist"], [d])

    # Remove ONLY .olean.private and re-export
    os.remove(os.path.join(d, "ModHidden.olean.private"))
    exp_no_priv = export_ndjson_raw(["ModHidden"], decls, [d])

    # Also remove .olean.server
    os.remove(os.path.join(d, "ModHidden.olean.server"))
    exp_olean_only = export_ndjson_raw(["ModHidden"], decls, [d])

    return {
        "full_export_rc": exp_full["rc"],
        "full_export_kinds": kinds,
        "full_export_axioms": axioms,
        "missing_const_rc": exp_missing["rc"],
        "missing_const_stderr_has_panic": "PANIC" in exp_missing["stderr"],
        "without_private_rc": exp_no_priv["rc"],
        "without_private_stderr": exp_no_priv["stderr"][:180],
        "olean_only_rc": exp_olean_only["rc"],
        "olean_only_stderr": exp_olean_only["stderr"][:180],
    }


def main() -> int:
    with tempfile.TemporaryDirectory() as tmp:
        results = {
            "probe_1_inductive_rec_hints_merkle": probe_1_inductive_rec_hints_merkle(tmp),
            "probe_2_canonical_reserialization": probe_2_canonical_reserialization(tmp),
            "probe_3_option_b_and_dag_ratio": probe_3_option_b_and_dag_ratio(tmp),
            "probe_4_multi_shard_tarjan_and_link": probe_4_multi_shard_tarjan_and_link(tmp),
            "probe_5_module_olean_private": probe_5_module_olean_private(tmp),
        }
    print(json.dumps(results, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
