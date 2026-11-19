#!/usr/bin/env python3
"""Standalone verification probe for linking, loading, and separate-compilation models.

Verifies deterministic formal models of:
  1. ELF flat-namespace dynamic linking (gABI v4.2 + glibc elf/dl-lookup.c):
     breadth-first search, LD_PRELOAD interposition, STV_PROTECTED / DF_SYMBOLIC,
     glibc default dl_dynamic_weak=0 vs static-linker strong-over-weak,
     RTLD_LOCAL vs RTLD_GLOBAL identity splitting, STB_GNU_UNIQUE pinning,
     and DT_INIT_ARRAY topological initialization ordering.
  2. Apple Mach-O two-level namespace lookup (dyld/Loader.cpp) and Windows PE/COFF
     explicit DLL-scoped Import Address Table binding (pe-format.md), including
     Mach-O BIND_SPECIAL_DYLIB_WEAK_LOOKUP cross-image weak-def coalescing.
  3. Project Oberon whole-module .smb structural checksums (ORB.Mod / Modules.Mod)
     contrasted with Crelier (1994) per-item structural fingerprinting across
     body-only edits, ABI-breaking layout edits, hidden GC pointer changes, and
     monotonic additive exports.
  4. ELF SHT_GROUP / GRP_COMDAT first-seen deduplication silent ODR mismatch
     (lld/ELF/InputFiles.cpp) contrasted with PE/COFF COMDAT selection modes.

When executed on a Linux ELF host with `cc` and `ld` on PATH, also executes live
empirical checks inside a temporary directory confirming:
  - Order-dependent silent COMDAT ODR flipping with zero linker diagnostics.
  - LD_PRELOAD intra-DSO interposition on STV_DEFAULT vs local binding on STV_PROTECTED.
  - dlopen(RTLD_LOCAL) vs dlopen(RTLD_GLOBAL) visibility isolation.

Requires Python 3.10+ standard library only. Exits 0 iff all assertions pass.
"""

from __future__ import annotations

import hashlib
import json
import os
import platform
import shutil
import struct
import subprocess
import sys
import tempfile
from collections import deque
from dataclasses import dataclass, field
from pathlib import Path
from typing import Literal


# ---------------------------------------------------------------------------
# 1. ELF Flat-Namespace Dynamic Linking Model (gABI v4.2 + glibc dl-lookup.c)
# ---------------------------------------------------------------------------

BindKind = Literal["STB_GLOBAL", "STB_WEAK", "STB_GNU_UNIQUE", "STB_LOCAL"]
VisKind = Literal["STV_DEFAULT", "STV_PROTECTED", "STV_HIDDEN"]


@dataclass(frozen=True)
class ElfSymbol:
    name: str
    binding: BindKind
    visibility: VisKind
    value: str


@dataclass
class ElfObject:
    name: str
    is_executable: bool = False
    needed: tuple[str, ...] = ()
    df_symbolic: bool = False
    symbols: dict[str, ElfSymbol] = field(default_factory=dict)
    nodelete: bool = False
    rtld_global: bool = True


class ElfDynamicLinker:
    """Models ELF gABI breadth-first lookup and glibc dl-lookup.c semantics."""

    def __init__(self, objects: dict[str, ElfObject], dl_dynamic_weak: bool = False):
        self.objects = objects
        self.dl_dynamic_weak = dl_dynamic_weak
        self.global_scope: list[str] = []
        self.loaded: set[str] = set()
        self.local_scopes: dict[str, list[str]] = {}
        self.unique_sym_table: dict[str, tuple[str, ElfSymbol]] = {}

    def load_startup(self, exe_name: str, ld_preload: list[str] | None = None) -> list[str]:
        """Construct startup global scope: exe -> LD_PRELOAD -> BFS DT_NEEDED."""
        ld_preload = ld_preload or []
        order: list[str] = []
        seen: set[str] = set()

        def enqueue(obj_name: str, q: deque[str]) -> None:
            if obj_name not in seen:
                seen.add(obj_name)
                order.append(obj_name)
                self.loaded.add(obj_name)
                q.append(obj_name)

        q: deque[str] = deque()
        enqueue(exe_name, q)
        for p in ld_preload:
            enqueue(p, q)
        while q:
            cur = q.popleft()
            for dep in self.objects[cur].needed:
                enqueue(dep, q)

        self.global_scope = order
        return list(order)

    def dlopen(self, root_name: str, rtld_global: bool) -> list[str]:
        """Load root_name and its DT_NEEDED BFS closure with RTLD_GLOBAL or RTLD_LOCAL."""
        closure: list[str] = []
        seen: set[str] = set()
        q: deque[str] = deque([root_name])
        seen.add(root_name)
        while q:
            cur = q.popleft()
            closure.append(cur)
            self.loaded.add(cur)
            for dep in self.objects[cur].needed:
                if dep not in seen:
                    seen.add(dep)
                    q.append(dep)
        self.local_scopes[root_name] = closure
        if rtld_global:
            for name in closure:
                if name not in self.global_scope:
                    self.global_scope.append(name)
        return closure

    def resolve(self, requester: str, sym_name: str) -> tuple[str, ElfSymbol]:
        """Resolve sym_name referenced by requester following gABI + glibc rules."""
        req_obj = self.objects[requester]
        local_def = req_obj.symbols.get(sym_name)
        if local_def is not None and local_def.binding != "STB_LOCAL":
            if local_def.visibility == "STV_PROTECTED" or req_obj.df_symbolic:
                return (requester, local_def)

        search_list: list[str] = list(self.global_scope)
        if requester in self.local_scopes:
            for obj_name in self.local_scopes[requester]:
                if obj_name not in search_list:
                    search_list.append(obj_name)

        weak_fallback: tuple[str, ElfSymbol] | None = None
        for obj_name in search_list:
            obj = self.objects[obj_name]
            sym = obj.symbols.get(sym_name)
            if sym is None or sym.binding == "STB_LOCAL" or sym.visibility == "STV_HIDDEN":
                continue
            if sym.binding == "STB_GNU_UNIQUE":
                if sym_name not in self.unique_sym_table:
                    self.unique_sym_table[sym_name] = (obj_name, sym)
                    if not obj.is_executable:
                        obj.nodelete = True
                return self.unique_sym_table[sym_name]
            if sym.binding == "STB_WEAK":
                if self.dl_dynamic_weak:
                    if weak_fallback is None:
                        weak_fallback = (obj_name, sym)
                    continue
                return (obj_name, sym)
            if sym.binding == "STB_GLOBAL":
                return (obj_name, sym)

        if weak_fallback is not None:
            return weak_fallback
        raise LookupError(f"Undefined ELF symbol {sym_name!r} requested by {requester!r}")

    def compute_init_order(self, root: str) -> tuple[list[str], list[tuple[str, str]]]:
        """Compute dependency-before-dependent DT_INIT_ARRAY order; flag cycles."""
        visited: set[str] = set()
        in_stack: set[str] = set()
        order: list[str] = []
        cycles: list[tuple[str, str]] = []

        def dfs(node: str) -> None:
            visited.add(node)
            in_stack.add(node)
            for dep in self.objects[node].needed:
                if dep in in_stack:
                    cycles.append((node, dep))
                elif dep not in visited:
                    dfs(dep)
            in_stack.remove(node)
            order.append(node)

        dfs(root)
        return order, cycles


def verify_elf_model() -> dict[str, object]:
    objs = {
        "main": ElfObject("main", is_executable=True, needed=("libtarget.so", "libstrong.so")),
        "libpreload.so": ElfObject(
            "libpreload.so",
            symbols={
                "api_default": ElfSymbol("api_default", "STB_GLOBAL", "STV_DEFAULT", "preload::api_default"),
                "api_protected": ElfSymbol("api_protected", "STB_GLOBAL", "STV_DEFAULT", "preload::api_protected"),
                "weak_or_strong": ElfSymbol("weak_or_strong", "STB_WEAK", "STV_DEFAULT", "preload::weak_def"),
            },
        ),
        "libtarget.so": ElfObject(
            "libtarget.so",
            needed=("libbase.so",),
            symbols={
                "api_default": ElfSymbol("api_default", "STB_GLOBAL", "STV_DEFAULT", "target::api_default"),
                "api_protected": ElfSymbol("api_protected", "STB_GLOBAL", "STV_PROTECTED", "target::api_protected"),
                "internal_hidden": ElfSymbol("internal_hidden", "STB_GLOBAL", "STV_HIDDEN", "target::hidden"),
            },
        ),
        "libstrong.so": ElfObject(
            "libstrong.so",
            symbols={
                "weak_or_strong": ElfSymbol("weak_or_strong", "STB_GLOBAL", "STV_DEFAULT", "strong::global_def"),
            },
        ),
        "libbase.so": ElfObject("libbase.so", symbols={}),
        "plugin_a.so": ElfObject(
            "plugin_a.so",
            symbols={
                "_ZTI3Foo": ElfSymbol("_ZTI3Foo", "STB_WEAK", "STV_DEFAULT", "plugin_a::typeinfo_Foo"),
                "_ZZ3barvE5cache": ElfSymbol("_ZZ3barvE5cache", "STB_GNU_UNIQUE", "STV_DEFAULT", "plugin_a::static_local"),
            },
        ),
        "plugin_b.so": ElfObject(
            "plugin_b.so",
            symbols={
                "_ZTI3Foo": ElfSymbol("_ZTI3Foo", "STB_WEAK", "STV_DEFAULT", "plugin_b::typeinfo_Foo"),
                "_ZZ3barvE5cache": ElfSymbol("_ZZ3barvE5cache", "STB_GNU_UNIQUE", "STV_DEFAULT", "plugin_b::static_local"),
            },
        ),
    }

    ld_default = ElfDynamicLinker(objs, dl_dynamic_weak=False)
    scope = ld_default.load_startup("main", ld_preload=["libpreload.so"])
    assert scope == ["main", "libpreload.so", "libtarget.so", "libstrong.so", "libbase.so"], scope

    provider, sym = ld_default.resolve("libtarget.so", "api_default")
    assert (provider, sym.value) == ("libpreload.so", "preload::api_default")

    provider, sym = ld_default.resolve("libtarget.so", "api_protected")
    assert (provider, sym.value) == ("libtarget.so", "target::api_protected")

    provider, sym = ld_default.resolve("main", "api_protected")
    assert (provider, sym.value) == ("libpreload.so", "preload::api_protected")

    provider, sym = ld_default.resolve("main", "weak_or_strong")
    assert (provider, sym.value) == ("libpreload.so", "preload::weak_def")

    ld_dynweak = ElfDynamicLinker(objs, dl_dynamic_weak=True)
    ld_dynweak.load_startup("main", ld_preload=["libpreload.so"])
    provider, sym = ld_dynweak.resolve("main", "weak_or_strong")
    assert (provider, sym.value) == ("libstrong.so", "strong::global_def")

    ld_default.dlopen("plugin_a.so", rtld_global=False)
    ld_default.dlopen("plugin_b.so", rtld_global=False)
    pa_rtti = ld_default.resolve("plugin_a.so", "_ZTI3Foo")
    pb_rtti = ld_default.resolve("plugin_b.so", "_ZTI3Foo")
    assert pa_rtti[0] == "plugin_a.so" and pb_rtti[0] == "plugin_b.so"
    assert pa_rtti[1].value != pb_rtti[1].value

    pa_uniq = ld_default.resolve("plugin_a.so", "_ZZ3barvE5cache")
    pb_uniq = ld_default.resolve("plugin_b.so", "_ZZ3barvE5cache")
    assert pa_uniq == pb_uniq == ("plugin_a.so", objs["plugin_a.so"].symbols["_ZZ3barvE5cache"])
    assert objs["plugin_a.so"].nodelete is True

    init_order, cycles = ld_default.compute_init_order("main")
    assert cycles == []
    assert init_order.index("libbase.so") < init_order.index("libtarget.so") < init_order.index("main")

    cyclic_objs = {
        "app": ElfObject("app", is_executable=True, needed=("libA.so",)),
        "libA.so": ElfObject("libA.so", needed=("libB.so",)),
        "libB.so": ElfObject("libB.so", needed=("libA.so",)),
    }
    _, cyc = ElfDynamicLinker(cyclic_objs).compute_init_order("app")
    assert cyc == [("libB.so", "libA.so")]

    return {
        "startup_bfs_scope": scope,
        "preload_hijacked_default": True,
        "protected_bound_locally_inside_dso": True,
        "glibc_default_weak_stops_lookup": True,
        "rtld_local_rtti_split": True,
        "stb_gnu_unique_pinned_nodelete": True,
        "cyclic_init_detected": True,
    }


# ---------------------------------------------------------------------------
# 2. Mach-O Two-Level Namespace (dyld) & PE/COFF Explicit Import Tables
# ---------------------------------------------------------------------------

BIND_SPECIAL_DYLIB_SELF = 0
BIND_SPECIAL_DYLIB_MAIN_EXECUTABLE = -1
BIND_SPECIAL_DYLIB_FLAT_LOOKUP = -2
BIND_SPECIAL_DYLIB_WEAK_LOOKUP = -3


@dataclass(frozen=True)
class MachOSymbol:
    name: str
    value: str
    is_weak_def: bool = False


@dataclass
class MachOImage:
    name: str
    dependents: tuple[str, ...] = ()
    exports: dict[str, MachOSymbol] = field(default_factory=dict)
    has_weak_defs: bool = False
    hidden_from_flat: bool = False


class DyldTwoLevelLinker:
    """Models Apple dyld Loader::resolveSymbol (dyld/Loader.cpp:2853-3095)."""

    def __init__(self, images: dict[str, MachOImage], load_order: list[str], main_exe: str):
        self.images = images
        self.load_order = load_order
        self.main_exe = main_exe

    def resolve_symbol(self, requester: str, lib_ordinal: int, sym_name: str) -> tuple[str, MachOSymbol]:
        req = self.images[requester]
        if lib_ordinal > 0:
            target_name = req.dependents[lib_ordinal - 1]
            sym = self.images[target_name].exports.get(sym_name)
            if sym is None:
                raise LookupError(f"Two-level missing symbol {sym_name!r} in {target_name!r}")
            return (target_name, sym)
        if lib_ordinal == BIND_SPECIAL_DYLIB_SELF:
            return (requester, req.exports[sym_name])
        if lib_ordinal == BIND_SPECIAL_DYLIB_MAIN_EXECUTABLE:
            return (self.main_exe, self.images[self.main_exe].exports[sym_name])
        if lib_ordinal == BIND_SPECIAL_DYLIB_FLAT_LOOKUP:
            for name in self.load_order:
                img = self.images[name]
                if img.hidden_from_flat and name != requester:
                    continue
                if sym_name in img.exports:
                    return (name, img.exports[sym_name])
            raise LookupError(f"Flat lookup missing {sym_name!r}")
        if lib_ordinal == BIND_SPECIAL_DYLIB_WEAK_LOOKUP:
            chosen: tuple[str, MachOSymbol] | None = None
            for name in self.load_order:
                img = self.images[name]
                if not img.has_weak_defs or img.hidden_from_flat:
                    continue
                sym = img.exports.get(sym_name)
                if sym is None:
                    continue
                if chosen is None:
                    chosen = (name, sym)
                elif (not sym.is_weak_def) and chosen[1].is_weak_def:
                    chosen = (name, sym)
            if chosen is None:
                raise LookupError(f"Weak-def lookup missing {sym_name!r}")
            return chosen
        raise ValueError(f"Unknown Mach-O libOrdinal {lib_ordinal}")


@dataclass
class PeDll:
    name: str
    exports_by_name: dict[str, str]
    exports_by_ordinal: dict[int, str]


class PeLoader:
    """Models PE/COFF explicit (dll_name, name_or_ordinal) IAT binding."""

    def __init__(self, dlls: dict[str, PeDll]):
        self.dlls = {k.lower(): v for k, v in dlls.items()}

    def bind_iat(self, imports: list[tuple[str, str | int]]) -> list[str]:
        iat: list[str] = []
        for dll_name, entry in imports:
            dll = self.dlls[dll_name.lower()]
            if isinstance(entry, int):
                iat.append(dll.exports_by_ordinal[entry])
            else:
                iat.append(dll.exports_by_name[entry])
        return iat


def verify_macho_and_pe_models() -> dict[str, object]:
    images = {
        "App": MachOImage("App", dependents=("libInterpose.dylib", "libTarget.dylib")),
        "libInterpose.dylib": MachOImage(
            "libInterpose.dylib",
            exports={
                "_helper": MachOSymbol("_helper", "interpose::_helper", is_weak_def=False),
                "__ZTI3Foo": MachOSymbol("__ZTI3Foo", "interpose::weak_typeinfo", is_weak_def=True),
            },
            has_weak_defs=True,
        ),
        "libTarget.dylib": MachOImage(
            "libTarget.dylib",
            dependents=("libRealDep.dylib",),
            exports={
                "_helper": MachOSymbol("_helper", "target::_helper", is_weak_def=False),
                "__ZTI3Foo": MachOSymbol("__ZTI3Foo", "target::strong_typeinfo", is_weak_def=False),
            },
            has_weak_defs=True,
        ),
        "libRealDep.dylib": MachOImage(
            "libRealDep.dylib",
            exports={"_helper": MachOSymbol("_helper", "realdep::_helper", is_weak_def=False)},
        ),
    }
    dyld = DyldTwoLevelLinker(
        images,
        load_order=["App", "libInterpose.dylib", "libTarget.dylib", "libRealDep.dylib"],
        main_exe="App",
    )

    prov, sym = dyld.resolve_symbol("libTarget.dylib", lib_ordinal=1, sym_name="_helper")
    assert (prov, sym.value) == ("libRealDep.dylib", "realdep::_helper")

    prov, sym = dyld.resolve_symbol("libTarget.dylib", lib_ordinal=BIND_SPECIAL_DYLIB_FLAT_LOOKUP, sym_name="_helper")
    assert (prov, sym.value) == ("libInterpose.dylib", "interpose::_helper")

    prov, sym = dyld.resolve_symbol("libTarget.dylib", lib_ordinal=BIND_SPECIAL_DYLIB_WEAK_LOOKUP, sym_name="__ZTI3Foo")
    assert (prov, sym.value) == ("libTarget.dylib", "target::strong_typeinfo")

    pe = PeLoader(
        {
            "crypto_v1.dll": PeDll("crypto_v1.dll", {"hash": "v1::sha1"}, {1: "v1::sha1"}),
            "crypto_v2.dll": PeDll("crypto_v2.dll", {"hash": "v2::sha256"}, {1: "v2::sha256"}),
        }
    )
    assert pe.bind_iat([("crypto_v1.dll", "hash")]) == ["v1::sha1"]
    assert pe.bind_iat([("crypto_v2.dll", "hash"), ("crypto_v2.dll", 1)]) == ["v2::sha256", "v2::sha256"]

    return {
        "macho_two_level_blocks_interposition": True,
        "macho_weak_def_nonweak_overrides_weak": True,
        "pe_iat_side_by_side_diamond_isolated": True,
    }


# ---------------------------------------------------------------------------
# 3. Oberon .smb Whole-Module Key (ORB.Mod / Modules.Mod) vs Crelier (1994)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class FieldDesc:
    name: str
    type_name: str
    offset: int
    exported: bool = True
    is_pointer: bool = False


@dataclass(frozen=True)
class RecordTypeDesc:
    name: str
    size: int
    fields: tuple[FieldDesc, ...]


@dataclass(frozen=True)
class ProcDesc:
    name: str
    params: tuple[tuple[str, str], ...]
    ret_type: str


@dataclass(frozen=True)
class OberonModuleInterface:
    module_name: str
    records: tuple[RecordTypeDesc, ...]
    procs: tuple[ProcDesc, ...]
    private_body_hash: str


def serialize_oberon_smb(iface: OberonModuleInterface) -> bytes:
    """Serialize exported interface + hidden GC pointer offsets (models ORB.OutType + Export)."""
    chunks: list[bytes] = [f"MOD:{iface.module_name}\x00".encode("utf-8")]
    for rec in iface.records:
        chunks.append(f"REC:{rec.name}:{rec.size}\x00".encode("utf-8"))
        for f in rec.fields:
            if f.exported:
                chunks.append(f"FLD:{f.name}:{f.type_name}:{f.offset}\x00".encode("utf-8"))
            elif f.is_pointer:
                chunks.append(f"HIDPTR:{f.offset}\x00".encode("utf-8"))
    for p in iface.procs:
        sig = ",".join(f"{m}:{t}" for m, t in p.params)
        chunks.append(f"PROC:{p.name}({sig})->{p.ret_type}\x00".encode("utf-8"))
    raw = b"".join(chunks)
    pad = (-len(raw)) % 4
    return raw + (b"\x00" * pad)


def oberon_whole_module_key(iface: OberonModuleInterface) -> int:
    """Compute 32-bit word-sum key as in Project Oberon ORB.Export (ORB.Mod:350-351)."""
    data = serialize_oberon_smb(iface)
    total = 0
    for (word,) in struct.iter_unpack("<I", data):
        total = (total + word) & 0xFFFFFFFF
    return total


def crelier_item_fingerprints(iface: OberonModuleInterface) -> dict[str, str]:
    """Compute per-item structural fingerprints (models Crelier 1994 Diss. ETH 10650)."""
    fps: dict[str, str] = {}
    for rec in iface.records:
        payload = json.dumps(
            {
                "kind": "REC",
                "name": rec.name,
                "size": rec.size,
                "fields": [
                    (f.name, f.type_name, f.offset) if f.exported else ("<hidden_ptr>", f.offset)
                    for f in rec.fields
                    if f.exported or f.is_pointer
                ],
            },
            sort_keys=True,
        ).encode("utf-8")
        fps[f"type:{rec.name}"] = hashlib.sha256(payload).hexdigest()[:16]
    for p in iface.procs:
        payload = json.dumps({"kind": "PROC", "name": p.name, "params": p.params, "ret": p.ret_type}).encode("utf-8")
        fps[f"proc:{p.name}"] = hashlib.sha256(payload).hexdigest()[:16]
    return fps


def oberon_load_check(client_expected_key: int, provider_actual_key: int) -> int:
    """Models Modules.Load check (Modules.Mod:73-75): 0=ok, 3=key conflict."""
    return 0 if provider_actual_key == client_expected_key else 3


def crelier_load_check(client_used_fps: dict[str, str], provider_fps: dict[str, str]) -> bool:
    return all(provider_fps.get(item) == fp for item, fp in client_used_fps.items())


def verify_oberon_and_crelier_models() -> dict[str, object]:
    v1 = OberonModuleInterface(
        module_name="Storage",
        records=(
            RecordTypeDesc(
                name="Header",
                size=16,
                fields=(
                    FieldDesc("tag", "INTEGER", 0, exported=True),
                    FieldDesc("len", "INTEGER", 4, exported=True),
                    FieldDesc("priv_flags", "INTEGER", 8, exported=False, is_pointer=False),
                ),
            ),
        ),
        procs=(ProcDesc("Read", (("VAR", "Header"), ("VAL", "INTEGER")), "BOOLEAN"),),
        private_body_hash="impl_v1",
    )
    key_v1 = oberon_whole_module_key(v1)
    fps_v1 = crelier_item_fingerprints(v1)
    client_used = {"type:Header": fps_v1["type:Header"], "proc:Read": fps_v1["proc:Read"]}

    v1_body_edit = OberonModuleInterface(v1.module_name, v1.records, v1.procs, private_body_hash="impl_v2_faster")
    assert oberon_load_check(key_v1, oberon_whole_module_key(v1_body_edit)) == 0
    assert crelier_load_check(client_used, crelier_item_fingerprints(v1_body_edit)) is True

    v2_abi_break = OberonModuleInterface(
        module_name="Storage",
        records=(
            RecordTypeDesc(
                name="Header",
                size=24,
                fields=(
                    FieldDesc("tag", "LONGINT", 0, exported=True),
                    FieldDesc("len", "LONGINT", 8, exported=True),
                    FieldDesc("priv_flags", "INTEGER", 16, exported=False, is_pointer=False),
                ),
            ),
        ),
        procs=v1.procs,
        private_body_hash="impl_v2",
    )
    assert oberon_load_check(key_v1, oberon_whole_module_key(v2_abi_break)) == 3
    assert crelier_load_check(client_used, crelier_item_fingerprints(v2_abi_break)) is False

    v2_hidden_ptr = OberonModuleInterface(
        module_name="Storage",
        records=(
            RecordTypeDesc(
                name="Header",
                size=16,
                fields=(
                    FieldDesc("tag", "INTEGER", 0, exported=True),
                    FieldDesc("len", "INTEGER", 4, exported=True),
                    FieldDesc("priv_ptr", "POINTER", 8, exported=False, is_pointer=True),
                ),
            ),
        ),
        procs=v1.procs,
        private_body_hash="impl_v2_ptr",
    )
    assert oberon_load_check(key_v1, oberon_whole_module_key(v2_hidden_ptr)) == 3
    assert crelier_load_check(client_used, crelier_item_fingerprints(v2_hidden_ptr)) is False

    v2_additive = OberonModuleInterface(
        module_name="Storage",
        records=v1.records,
        procs=v1.procs + (ProcDesc("Stats", (), "INTEGER"),),
        private_body_hash="impl_v2_add",
    )
    assert oberon_load_check(key_v1, oberon_whole_module_key(v2_additive)) == 3
    assert crelier_load_check(client_used, crelier_item_fingerprints(v2_additive)) is True

    return {
        "body_only_edit_compatible_both": True,
        "abi_layout_break_rejected_both": True,
        "hidden_gc_pointer_change_rejected_both": True,
        "additive_export_invalidates_oberon_preserves_crelier": True,
    }


# ---------------------------------------------------------------------------
# 4. COMDAT Deduplication ODR Mismatch Model (lld/ELF/InputFiles.cpp vs COFF)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ComdatGroup:
    tu_name: str
    signature: str
    payload_bytes: bytes
    semantic_return_value: int


def link_elf_comdat(objects: list[ComdatGroup]) -> ComdatGroup:
    """Models lld/ELF/InputFiles.cpp:659-662 (try_emplace(signature, this).second)."""
    comdat_groups: dict[str, ComdatGroup] = {}
    for grp in objects:
        if grp.signature not in comdat_groups:
            comdat_groups[grp.signature] = grp
    assert len(comdat_groups) == 1
    return next(iter(comdat_groups.values()))


def link_coff_comdat(
    objects: list[ComdatGroup],
    selection: Literal["ANY", "SAME_SIZE", "EXACT_MATCH"],
) -> ComdatGroup:
    """Models PE/COFF IMAGE_COMDAT_SELECT_{ANY,SAME_SIZE,EXACT_MATCH} (pe-format.md:1117-1119)."""
    kept: ComdatGroup | None = None
    for grp in objects:
        if kept is None:
            kept = grp
            continue
        if selection == "ANY":
            continue
        if selection == "SAME_SIZE" and len(grp.payload_bytes) != len(kept.payload_bytes):
            raise ValueError(f"COFF LNK2005 size mismatch for {grp.signature}")
        if selection == "EXACT_MATCH" and grp.payload_bytes != kept.payload_bytes:
            raise ValueError(f"COFF LNK2005 byte mismatch for {grp.signature}")
    assert kept is not None
    return kept


def verify_comdat_model() -> dict[str, object]:
    tu_a = ComdatGroup("tu_a.o", "_ZN3Cfg4sizeEv", b"\xb8\x04\x00\x00\x00\xc3", 4)
    tu_b = ComdatGroup("tu_b.o", "_ZN3Cfg4sizeEv", b"\xb8\x10\x00\x00\x00\x90\xc3", 16)

    res_ab = link_elf_comdat([tu_a, tu_b])
    res_ba = link_elf_comdat([tu_b, tu_a])
    assert res_ab.semantic_return_value == 4
    assert res_ba.semantic_return_value == 16

    assert link_coff_comdat([tu_a, tu_b], "ANY").semantic_return_value == 4
    caught_size = False
    try:
        link_coff_comdat([tu_a, tu_b], "SAME_SIZE")
    except ValueError:
        caught_size = True
    assert caught_size

    caught_exact = False
    try:
        link_coff_comdat([tu_a, tu_b], "EXACT_MATCH")
    except ValueError:
        caught_exact = True
    assert caught_exact

    return {
        "elf_comdat_order_ab_value": res_ab.semantic_return_value,
        "elf_comdat_order_ba_value": res_ba.semantic_return_value,
        "coff_same_size_caught_odr": caught_size,
        "coff_exact_match_caught_odr": caught_exact,
    }


# ---------------------------------------------------------------------------
# 5. Optional Live Linux ELF Toolchain Verification (cc + ld + ld.so)
# ---------------------------------------------------------------------------

def run_live_elf_probes() -> dict[str, object]:
    if sys.platform != "linux" or not shutil.which("cc") or not shutil.which("ld"):
        return {"status": "skipped", "reason": "non-Linux host or cc/ld unavailable"}

    arch = platform.machine()
    if arch not in ("x86_64", "aarch64"):
        return {"status": "skipped", "reason": f"unsupported arch {arch} for asm probe"}

    with tempfile.TemporaryDirectory(prefix="linking_probe_") as tmp:
        td = Path(tmp)

        def emit_comdat_asm(val: int) -> str:
            if arch == "x86_64":
                body = f"movl ${val}, %eax\n    ret"
            else:
                body = f"mov w0, #{val}\n    ret"
            return (
                '.section .text.odr_fn,"axG",@progbits,odr_group_sig,comdat\n'
                ".globl odr_fn\n"
                ".type odr_fn, @function\n"
                "odr_fn:\n"
                f"    {body}\n"
                ".size odr_fn, .-odr_fn\n"
                '.section .note.GNU-stack,"",@progbits\n'
            )

        (td / "tu_a.s").write_text(emit_comdat_asm(42), encoding="utf-8")
        (td / "tu_b.s").write_text(emit_comdat_asm(99), encoding="utf-8")
        (td / "main_odr.c").write_text(
            '#include <stdio.h>\nint odr_fn(void);\nint main(void) { printf("%d\\n", odr_fn()); return 0; }\n',
            encoding="utf-8",
        )
        subprocess.run(["cc", "-c", str(td / "tu_a.s"), "-o", str(td / "tu_a.o")], check=True)
        subprocess.run(["cc", "-c", str(td / "tu_b.s"), "-o", str(td / "tu_b.o")], check=True)
        subprocess.run(["cc", "-c", str(td / "main_odr.c"), "-o", str(td / "main_odr.o")], check=True)

        p_ab = subprocess.run(
            ["cc", str(td / "main_odr.o"), str(td / "tu_a.o"), str(td / "tu_b.o"), "-o", str(td / "bin_ab")],
            capture_output=True,
            text=True,
            check=True,
        )
        p_ba = subprocess.run(
            ["cc", str(td / "main_odr.o"), str(td / "tu_b.o"), str(td / "tu_a.o"), "-o", str(td / "bin_ba")],
            capture_output=True,
            text=True,
            check=True,
        )
        out_ab = subprocess.check_output([str(td / "bin_ab")], text=True).strip()
        out_ba = subprocess.check_output([str(td / "bin_ba")], text=True).strip()
        assert out_ab == "42", out_ab
        assert out_ba == "99", out_ba
        assert p_ab.stderr.strip() == "" and p_ba.stderr.strip() == ""

        (td / "target.c").write_text(
            '__attribute__((visibility("default"), noinline)) int default_fn(void) { return 10; }\n'
            '__attribute__((visibility("protected"), noinline)) int protected_fn(void) { return 20; }\n'
            'int call_both(void) { return default_fn() * 100 + protected_fn(); }\n',
            encoding="utf-8",
        )
        (td / "preload.c").write_text(
            'int default_fn(void) { return 77; }\n'
            'int protected_fn(void) { return 88; }\n',
            encoding="utf-8",
        )
        (td / "main_dyn.c").write_text(
            '#include <stdio.h>\nint call_both(void);\nint main(void) { printf("%d\\n", call_both()); return 0; }\n',
            encoding="utf-8",
        )
        subprocess.run(
            [
                "cc", "-shared", "-fPIC", "-O2", "-fsemantic-interposition",
                str(td / "target.c"), "-o", str(td / "libtarget.so"),
            ],
            check=True,
        )
        subprocess.run(
            ["cc", "-shared", "-fPIC", "-O2", str(td / "preload.c"), "-o", str(td / "libpreload.so")],
            check=True,
        )
        subprocess.run(
            [
                "cc", str(td / "main_dyn.c"),
                f"-L{td}", "-ltarget", f"-Wl,-rpath,{td}", "-o", str(td / "main_dyn"),
            ],
            check=True,
        )
        base_out = subprocess.check_output([str(td / "main_dyn")], text=True).strip()
        env = dict(os.environ, LD_PRELOAD=str(td / "libpreload.so"))
        preload_out = subprocess.check_output([str(td / "main_dyn")], env=env, text=True).strip()
        assert base_out == "1020", base_out
        assert preload_out == "7720", preload_out

        (td / "plug.c").write_text("int plugin_exported_sym(void) { return 314; }\n", encoding="utf-8")
        (td / "dl_test.c").write_text(
            "#define _GNU_SOURCE\n"
            "#include <dlfcn.h>\n"
            "#include <stdio.h>\n"
            "int main(int argc, char **argv) {\n"
            "  void *h1 = dlopen(argv[1], RTLD_NOW | RTLD_LOCAL);\n"
            "  void *s1 = dlsym(RTLD_DEFAULT, \"plugin_exported_sym\");\n"
            "  void *h2 = dlopen(argv[1], RTLD_NOW | RTLD_GLOBAL);\n"
            "  void *s2 = dlsym(RTLD_DEFAULT, \"plugin_exported_sym\");\n"
            "  printf(\"%d %d\\n\", s1 != NULL, s2 != NULL);\n"
            "  dlclose(h2); dlclose(h1);\n"
            "  return 0;\n"
            "}\n",
            encoding="utf-8",
        )
        subprocess.run(["cc", "-shared", "-fPIC", str(td / "plug.c"), "-o", str(td / "libplug.so")], check=True)
        subprocess.run(["cc", str(td / "dl_test.c"), "-ldl", "-o", str(td / "dl_test")], check=True)
        dl_out = subprocess.check_output([str(td / "dl_test"), str(td / "libplug.so")], text=True).strip()
        assert dl_out == "0 1", dl_out

        return {
            "status": "executed",
            "arch": arch,
            "live_comdat_ab_vs_ba": [int(out_ab), int(out_ba)],
            "live_preload_base_vs_interposed": [int(base_out), int(preload_out)],
            "live_dlopen_local_vs_global_visible": dl_out,
        }


def main() -> int:
    results = {
        "elf_model": verify_elf_model(),
        "macho_pe_models": verify_macho_and_pe_models(),
        "oberon_crelier_models": verify_oberon_and_crelier_models(),
        "comdat_model": verify_comdat_model(),
        "live_elf_probes": run_live_elf_probes(),
    }
    print(json.dumps(results, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
