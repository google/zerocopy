#!/usr/bin/env python3
"""Standalone verification probe for polymorphism compilation, Value Witness Tables,
affine-ceiling slice-DST layout algebras, polymorphic padding constraints, and
reference-admissible repr(Rust) nondeterminism.

Requires Python 3.10+ and only the Python standard library.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import itertools
import math
import struct
import sys
from typing import Callable, Iterable, Optional

# =============================================================================
# Part 1: Swift-Style Value Witness Tables & Unspecialized Generic Execution
# =============================================================================
# Mirrors swiftlang/swift include/swift/ABI/{ValueWitness.def,ValueWitnessTable.h,
# MetadataValues.h,Enum.h} and stdlib/public/runtime/{Metadata.cpp,Enum.cpp,EnumImpl.h}.

VW_ALIGNMENT_MASK = 0x000000FF
VW_IS_NON_POD = 0x00010000
VW_IS_NON_INLINE = 0x00020000
VW_HAS_SPARE_BITS = 0x00080000
VW_IS_NON_BITWISE_TAKABLE = 0x00100000
VW_HAS_ENUM_WITNESSES = 0x00200000
VW_INCOMPLETE = 0x00400000
VW_IS_NON_COPYABLE = 0x00800000
VW_IS_NON_BITWISE_BORROWABLE = 0x01000000
VW_IS_ADDRESSABLE_FOR_DEPS = 0x02000000

NUM_WORDS_VALUE_BUFFER = 3  # swiftlang/swift MetadataValues.h:46
PTR_SIZE_64 = 8
VALUE_BUFFER_SIZE_64 = NUM_WORDS_VALUE_BUFFER * PTR_SIZE_64  # 24 bytes
VALUE_BUFFER_ALIGN_64 = PTR_SIZE_64  # 8 bytes


def is_power_of_two(n: int) -> bool:
    return n > 0 and (n & (n - 1)) == 0


def round_up(value: int, align: int) -> int:
    assert is_power_of_two(align), f"alignment must be power of two, got {align}"
    mask = align - 1
    return (value + mask) & ~mask


def round_down(value: int, align: int) -> int:
    assert is_power_of_two(align), f"alignment must be power of two, got {align}"
    return value & ~(align - 1)


def swift_can_be_inline(is_bitwise_takable: bool, size: int, alignment: int) -> bool:
    """Matches ValueWitnessTable.h:canBeInline on 64-bit targets."""
    return (
        is_bitwise_takable
        and size <= VALUE_BUFFER_SIZE_64
        and alignment <= VALUE_BUFFER_ALIGN_64
    )


def swift_get_enum_tag_counts(
    payload_size: int, empty_cases: int, payload_cases: int
) -> tuple[int, int]:
    """Exact port of swiftlang/swift include/swift/ABI/Enum.h:getEnumTagCounts."""
    num_tags = payload_cases
    if empty_cases > 0:
        if payload_size >= 4:
            num_tags += 1
        else:
            bits = payload_size * 8
            cases_per_tag_value = 1 << bits
            num_tags += (empty_cases + (cases_per_tag_value - 1)) >> bits
    if num_tags <= 1:
        num_tag_bytes = 0
    elif num_tags < 256:
        num_tag_bytes = 1
    elif num_tags < 65536:
        num_tag_bytes = 2
    else:
        num_tag_bytes = 4
    return num_tags, num_tag_bytes


class SimRuntime:
    """Linear byte-addressed memory plus ARC and address-sensitive weak-ref tables."""

    def __init__(self, capacity: int = 8192) -> None:
        self.mem = bytearray(capacity)
        self.alloc_ptr = 0
        self.arc_refcounts: dict[int, int] = {}
        self.next_obj_id = 1
        # Address-indexed side table modeling Swift weak references (non-bitwise-takable).
        self.weak_side_table: dict[int, int] = {}

    def alloc_stack(self, size: int, align: int) -> int:
        addr = round_up(self.alloc_ptr, align)
        self.alloc_ptr = addr + max(size, 1)
        assert self.alloc_ptr <= len(self.mem), "simulated stack overflow"
        return addr

    def new_heap_object(self) -> int:
        oid = self.next_obj_id
        self.next_obj_id += 1
        self.arc_refcounts[oid] = 1
        return oid

    def retain(self, oid: int) -> None:
        assert oid != 0 and self.arc_refcounts.get(oid, 0) > 0, f"retain dead object {oid}"
        self.arc_refcounts[oid] += 1

    def release(self, oid: int) -> None:
        assert oid != 0 and self.arc_refcounts.get(oid, 0) > 0, f"double-release {oid}"
        self.arc_refcounts[oid] -= 1

    def register_weak(self, addr: int, target_oid: int) -> None:
        assert addr not in self.weak_side_table, f"overwrite live weak slot @{addr}"
        self.weak_side_table[addr] = target_oid

    def unregister_weak(self, addr: int) -> int:
        assert addr in self.weak_side_table, f"destroy unregistered weak slot @{addr}"
        return self.weak_side_table.pop(addr)


@dataclass
class ValueWitnessTable:
    """Models Swift TargetValueWitnessTable data + function witnesses."""

    name: str
    size: int
    stride: int
    flags: int
    extra_inhabitant_count: int
    destroy: Callable[[SimRuntime, int], None]
    init_with_copy: Callable[[SimRuntime, int, int], None]
    assign_with_copy: Callable[[SimRuntime, int, int], None]
    init_with_take: Callable[[SimRuntime, int, int], None]
    assign_with_take: Callable[[SimRuntime, int, int], None]
    get_extra_inhabitant_tag: Callable[[SimRuntime, int, int], int]
    store_extra_inhabitant_tag: Callable[[SimRuntime, int, int, int], None]
    field_offsets: tuple[int, ...] = ()

    @property
    def align_mask(self) -> int:
        return self.flags & VW_ALIGNMENT_MASK

    @property
    def alignment(self) -> int:
        return self.align_mask + 1

    @property
    def is_pod(self) -> bool:
        return not (self.flags & VW_IS_NON_POD)

    @property
    def is_inline(self) -> bool:
        return not (self.flags & VW_IS_NON_INLINE)

    @property
    def is_bitwise_takable(self) -> bool:
        return not (self.flags & VW_IS_NON_BITWISE_TAKABLE)

    def get_enum_tag_single_payload(
        self, rt: SimRuntime, enum_addr: int, empty_cases: int
    ) -> int:
        """Port of swiftlang/swift EnumImpl.h:getEnumTagSinglePayloadImpl (little-endian)."""
        if empty_cases > self.extra_inhabitant_count:
            extra_tag_addr = enum_addr + self.size
            _, num_bytes = swift_get_enum_tag_counts(
                self.size, empty_cases - self.extra_inhabitant_count, 1
            )
            extra_tag_bits = int.from_bytes(
                rt.mem[extra_tag_addr : extra_tag_addr + num_bytes], "little"
            )
            if extra_tag_bits > 0:
                if self.size >= 4:
                    from_extra = 0
                    from_val = int.from_bytes(rt.mem[enum_addr : enum_addr + 4], "little")
                else:
                    from_extra = (extra_tag_bits - 1) << (self.size * 8)
                    from_val = int.from_bytes(
                        rt.mem[enum_addr : enum_addr + self.size], "little"
                    )
                no_payload_idx = (from_extra | from_val) + self.extra_inhabitant_count
                return no_payload_idx + 1
        if self.extra_inhabitant_count > 0:
            return self.get_extra_inhabitant_tag(rt, enum_addr, self.extra_inhabitant_count)
        return 0

    def store_enum_tag_single_payload(
        self, rt: SimRuntime, enum_addr: int, which_case: int, empty_cases: int
    ) -> None:
        """Port of swiftlang/swift EnumImpl.h:storeEnumTagSinglePayloadImpl (little-endian)."""
        extra_tag_addr = enum_addr + self.size
        num_extra_tag_bytes = (
            swift_get_enum_tag_counts(
                self.size, empty_cases - self.extra_inhabitant_count, 1
            )[1]
            if empty_cases > self.extra_inhabitant_count
            else 0
        )
        if which_case <= self.extra_inhabitant_count:
            if num_extra_tag_bytes:
                rt.mem[extra_tag_addr : extra_tag_addr + num_extra_tag_bytes] = (
                    b"\x00" * num_extra_tag_bytes
                )
            if which_case == 0:
                return
            self.store_extra_inhabitant_tag(
                rt, enum_addr, which_case, self.extra_inhabitant_count
            )
            return

        no_payload_idx = which_case - 1
        case_idx = no_payload_idx - self.extra_inhabitant_count
        if self.size >= 4:
            extra_tag_idx = 1
            payload_idx = case_idx
            rt.mem[enum_addr : enum_addr + 4] = payload_idx.to_bytes(4, "little")
            if self.size > 4:
                rt.mem[enum_addr + 4 : enum_addr + self.size] = b"\x00" * (self.size - 4)
        else:
            payload_bits = self.size * 8
            extra_tag_idx = 1 + (case_idx >> payload_bits)
            payload_idx = case_idx & ((1 << payload_bits) - 1)
            if self.size:
                rt.mem[enum_addr : enum_addr + self.size] = payload_idx.to_bytes(
                    self.size, "little"
                )
        if num_extra_tag_bytes:
            rt.mem[extra_tag_addr : extra_tag_addr + num_extra_tag_bytes] = (
                extra_tag_idx.to_bytes(num_extra_tag_bytes, "little")
            )


def make_pod_vwt(
    name: str,
    size: int,
    align: int,
    extra_inhabitants: int = 0,
    xi_base: int = 0,
) -> ValueWitnessTable:
    """Create a trivial (POD) Value Witness Table."""
    assert is_power_of_two(align) and align <= 256
    stride = max(1, round_up(size, align))
    flags = align - 1
    if not swift_can_be_inline(True, size, align):
        flags |= VW_IS_NON_INLINE

    def noop_destroy(rt: SimRuntime, addr: int) -> None:
        pass

    def memcpy_copy(rt: SimRuntime, dst: int, src: int) -> None:
        if size > 0:
            rt.mem[dst : dst + size] = rt.mem[src : src + size]

    def get_xi(rt: SimRuntime, addr: int, max_xi: int) -> int:
        if extra_inhabitants == 0 or size == 0:
            return 0
        raw = int.from_bytes(rt.mem[addr : addr + size], "little")
        if raw >= xi_base and (raw - xi_base) < min(extra_inhabitants, max_xi):
            return (raw - xi_base) + 1
        return 0

    def store_xi(rt: SimRuntime, addr: int, which: int, max_xi: int) -> None:
        assert 1 <= which <= min(extra_inhabitants, max_xi)
        val = xi_base + (which - 1)
        rt.mem[addr : addr + size] = val.to_bytes(size, "little")

    return ValueWitnessTable(
        name=name,
        size=size,
        stride=stride,
        flags=flags,
        extra_inhabitant_count=extra_inhabitants,
        destroy=noop_destroy,
        init_with_copy=memcpy_copy,
        assign_with_copy=memcpy_copy,
        init_with_take=memcpy_copy,
        assign_with_take=memcpy_copy,
        get_extra_inhabitant_tag=get_xi,
        store_extra_inhabitant_tag=store_xi,
    )


def make_arc_class_ref_vwt() -> ValueWitnessTable:
    """Non-POD, bitwise-takable 64-bit Swift class reference with 0 as extra inhabitant."""
    size, align = 8, 8
    flags = (align - 1) | VW_IS_NON_POD  # bitwise-takable, inlineable (8 <= 24)

    def destroy(rt: SimRuntime, addr: int) -> None:
        oid = struct.unpack_from("<Q", rt.mem, addr)[0]
        rt.release(oid)

    def init_copy(rt: SimRuntime, dst: int, src: int) -> None:
        oid = struct.unpack_from("<Q", rt.mem, src)[0]
        rt.retain(oid)
        struct.pack_into("<Q", rt.mem, dst, oid)

    def assign_copy(rt: SimRuntime, dst: int, src: int) -> None:
        new_oid = struct.unpack_from("<Q", rt.mem, src)[0]
        old_oid = struct.unpack_from("<Q", rt.mem, dst)[0]
        rt.retain(new_oid)
        struct.pack_into("<Q", rt.mem, dst, new_oid)
        rt.release(old_oid)

    def init_take(rt: SimRuntime, dst: int, src: int) -> None:
        # Bitwise take: no retain/release traffic.
        rt.mem[dst : dst + 8] = rt.mem[src : src + 8]

    def assign_take(rt: SimRuntime, dst: int, src: int) -> None:
        old_oid = struct.unpack_from("<Q", rt.mem, dst)[0]
        rt.mem[dst : dst + 8] = rt.mem[src : src + 8]
        rt.release(old_oid)

    def get_xi(rt: SimRuntime, addr: int, max_xi: int) -> int:
        # Low unmapped page extra inhabitants (0..4095); 0 is first extra inhabitant.
        val = struct.unpack_from("<Q", rt.mem, addr)[0]
        if val == 0:
            return 1
        return 0

    def store_xi(rt: SimRuntime, addr: int, which: int, max_xi: int) -> None:
        assert which == 1
        struct.pack_into("<Q", rt.mem, addr, 0)

    return ValueWitnessTable(
        name="ClassRef",
        size=size,
        stride=8,
        flags=flags,
        extra_inhabitant_count=1,
        destroy=destroy,
        init_with_copy=init_copy,
        assign_with_copy=assign_copy,
        init_with_take=init_take,
        assign_with_take=assign_take,
        get_extra_inhabitant_tag=get_xi,
        store_extra_inhabitant_tag=store_xi,
    )


def make_weak_ref_vwt() -> ValueWitnessTable:
    """Non-POD, NON-bitwise-takable weak reference tracked in an address-indexed side table."""
    size, align = 8, 8
    # Non-bitwise-takable => IsNonInline must also be set (ValueWitnessTable.h:81).
    flags = (align - 1) | VW_IS_NON_POD | VW_IS_NON_BITWISE_TAKABLE | VW_IS_NON_INLINE

    def destroy(rt: SimRuntime, addr: int) -> None:
        rt.unregister_weak(addr)

    def init_copy(rt: SimRuntime, dst: int, src: int) -> None:
        oid = struct.unpack_from("<Q", rt.mem, src)[0]
        assert rt.weak_side_table[src] == oid
        struct.pack_into("<Q", rt.mem, dst, oid)
        rt.register_weak(dst, oid)

    def assign_copy(rt: SimRuntime, dst: int, src: int) -> None:
        oid = struct.unpack_from("<Q", rt.mem, src)[0]
        assert rt.weak_side_table[src] == oid
        rt.unregister_weak(dst)
        struct.pack_into("<Q", rt.mem, dst, oid)
        rt.register_weak(dst, oid)

    def init_take(rt: SimRuntime, dst: int, src: int) -> None:
        oid = rt.unregister_weak(src)
        struct.pack_into("<Q", rt.mem, dst, oid)
        rt.register_weak(dst, oid)

    def assign_take(rt: SimRuntime, dst: int, src: int) -> None:
        oid = rt.unregister_weak(src)
        rt.unregister_weak(dst)
        struct.pack_into("<Q", rt.mem, dst, oid)
        rt.register_weak(dst, oid)

    return ValueWitnessTable(
        name="WeakRef",
        size=size,
        stride=8,
        flags=flags,
        extra_inhabitant_count=0,
        destroy=destroy,
        init_with_copy=init_copy,
        assign_with_copy=assign_copy,
        init_with_take=init_take,
        assign_with_take=assign_take,
        get_extra_inhabitant_tag=lambda rt, addr, m: 0,
        store_extra_inhabitant_tag=lambda rt, addr, w, m: None,
    )


def compose_struct_vwt(name: str, fields: list[ValueWitnessTable]) -> ValueWitnessTable:
    """Exact port of Swift Metadata.cpp:performBasicLayout (size != stride tail reuse)."""
    size = 0
    align_mask = 0
    is_pod = True
    is_bitwise_takable = True
    offsets: list[int] = []

    for f in fields:
        size = round_up(size, f.alignment)
        offsets.append(size)
        size += f.size
        align_mask = max(align_mask, f.align_mask)
        if not f.is_pod:
            is_pod = False
        if not f.is_bitwise_takable:
            is_bitwise_takable = False

    alignment = align_mask + 1
    stride = max(1, round_up(size, alignment))
    is_inline = swift_can_be_inline(is_bitwise_takable, size, alignment)
    flags = align_mask
    if not is_pod:
        flags |= VW_IS_NON_POD
    if not is_bitwise_takable:
        flags |= VW_IS_NON_BITWISE_TAKABLE
    if not is_inline:
        flags |= VW_IS_NON_INLINE

    # Extra-inhabitant field: Swift picks a field with the maximum extra inhabitants.
    xi_idx: Optional[int] = None
    best_xi = 0
    for idx, f in enumerate(fields):
        if f.extra_inhabitant_count > best_xi:
            best_xi = f.extra_inhabitant_count
            xi_idx = idx

    field_pairs = list(zip(offsets, fields))

    def destroy(rt: SimRuntime, addr: int) -> None:
        for off, f in field_pairs:
            f.destroy(rt, addr + off)

    def init_copy(rt: SimRuntime, dst: int, src: int) -> None:
        for off, f in field_pairs:
            f.init_with_copy(rt, dst + off, src + off)

    def assign_copy(rt: SimRuntime, dst: int, src: int) -> None:
        for off, f in field_pairs:
            f.assign_with_copy(rt, dst + off, src + off)

    def init_take(rt: SimRuntime, dst: int, src: int) -> None:
        for off, f in field_pairs:
            f.init_with_take(rt, dst + off, src + off)

    def assign_take(rt: SimRuntime, dst: int, src: int) -> None:
        for off, f in field_pairs:
            f.assign_with_take(rt, dst + off, src + off)

    def get_xi(rt: SimRuntime, addr: int, max_xi: int) -> int:
        if xi_idx is None:
            return 0
        off, f = field_pairs[xi_idx]
        return f.get_extra_inhabitant_tag(rt, addr + off, max_xi)

    def store_xi(rt: SimRuntime, addr: int, which: int, max_xi: int) -> None:
        assert xi_idx is not None
        off, f = field_pairs[xi_idx]
        f.store_extra_inhabitant_tag(rt, addr + off, which, max_xi)

    return ValueWitnessTable(
        name=name,
        size=size,
        stride=stride,
        flags=flags,
        extra_inhabitant_count=best_xi,
        destroy=destroy,
        init_with_copy=init_copy,
        assign_with_copy=assign_copy,
        init_with_take=init_take,
        assign_with_take=assign_take,
        get_extra_inhabitant_tag=get_xi,
        store_extra_inhabitant_tag=store_xi,
        field_offsets=tuple(offsets),
    )


def compose_single_payload_enum_vwt(
    name: str, payload: ValueWitnessTable, empty_cases: int
) -> ValueWitnessTable:
    """Exact port of Swift Enum.cpp:swift_initEnumMetadataSinglePayload."""
    payload_xi = payload.extra_inhabitant_count
    if payload_xi >= empty_cases:
        size = payload.size
        unused_xi = payload_xi - empty_cases
    else:
        _, num_tag_bytes = swift_get_enum_tag_counts(
            payload.size, empty_cases - payload_xi, 1
        )
        size = payload.size + num_tag_bytes
        unused_xi = 0

    alignment = payload.alignment
    stride = max(1, round_up(size, alignment))
    is_bt = payload.is_bitwise_takable
    is_inline = swift_can_be_inline(is_bt, size, alignment)
    flags = (payload.flags & ~VW_IS_NON_INLINE) | VW_HAS_ENUM_WITNESSES
    if not is_inline:
        flags |= VW_IS_NON_INLINE

    def destroy(rt: SimRuntime, addr: int) -> None:
        if payload.get_enum_tag_single_payload(rt, addr, empty_cases) == 0:
            payload.destroy(rt, addr)

    def init_copy(rt: SimRuntime, dst: int, src: int) -> None:
        tag = payload.get_enum_tag_single_payload(rt, src, empty_cases)
        if tag == 0:
            payload.init_with_copy(rt, dst, src)
            payload.store_enum_tag_single_payload(rt, dst, 0, empty_cases)
        else:
            payload.store_enum_tag_single_payload(rt, dst, tag, empty_cases)

    def init_take(rt: SimRuntime, dst: int, src: int) -> None:
        tag = payload.get_enum_tag_single_payload(rt, src, empty_cases)
        if tag == 0:
            payload.init_with_take(rt, dst, src)
            payload.store_enum_tag_single_payload(rt, dst, 0, empty_cases)
        else:
            payload.store_enum_tag_single_payload(rt, dst, tag, empty_cases)

    def assign_copy(rt: SimRuntime, dst: int, src: int) -> None:
        destroy(rt, dst)
        init_copy(rt, dst, src)

    def assign_take(rt: SimRuntime, dst: int, src: int) -> None:
        destroy(rt, dst)
        init_take(rt, dst, src)

    def get_xi(rt: SimRuntime, addr: int, max_xi: int) -> int:
        if unused_xi == 0:
            return 0
        raw_tag = payload.get_extra_inhabitant_tag(rt, addr, payload_xi)
        if raw_tag > empty_cases:
            return raw_tag - empty_cases
        return 0

    def store_xi(rt: SimRuntime, addr: int, which: int, max_xi: int) -> None:
        assert 1 <= which <= unused_xi
        payload.store_extra_inhabitant_tag(rt, addr, empty_cases + which, payload_xi)

    return ValueWitnessTable(
        name=name,
        size=size,
        stride=stride,
        flags=flags,
        extra_inhabitant_count=unused_xi,
        destroy=destroy,
        init_with_copy=init_copy,
        assign_with_copy=assign_copy,
        init_with_take=init_take,
        assign_with_take=assign_take,
        get_extra_inhabitant_tag=get_xi,
        store_extra_inhabitant_tag=store_xi,
    )


def generic_swap(rt: SimRuntime, a_addr: int, b_addr: int, vwt: ValueWitnessTable) -> None:
    """Unspecialized generic swap<T>(&mut a, &mut b) executing solely via VWT."""
    saved_sp = rt.alloc_ptr
    tmp = rt.alloc_stack(vwt.size, vwt.alignment)
    vwt.init_with_take(rt, tmp, a_addr)
    vwt.init_with_take(rt, a_addr, b_addr)
    vwt.init_with_take(rt, b_addr, tmp)
    rt.alloc_ptr = saved_sp


def generic_array_reverse(
    rt: SimRuntime, base_addr: int, count: int, vwt: ValueWitnessTable
) -> None:
    """Unspecialized generic reverse<T>(buf: &mut [T]) stepping by vwt.stride."""
    lo, hi = 0, count - 1
    while lo < hi:
        generic_swap(rt, base_addr + lo * vwt.stride, base_addr + hi * vwt.stride, vwt)
        lo += 1
        hi -= 1


def verify_swift_vwt_composition() -> dict[str, object]:
    """Verify Swift TypeLayout, tail-padding reuse, single-payload enums, and generic exec."""
    u8 = make_pod_vwt("UInt8", 1, 1)
    bool_vwt = make_pod_vwt("Bool", 1, 1, extra_inhabitants=254, xi_base=2)
    i64 = make_pod_vwt("Int", 8, 8)
    empty = make_pod_vwt("Empty", 0, 1)
    cls = make_arc_class_ref_vwt()
    weak = make_weak_ref_vwt()

    # 1. Exact TypeLayout.rst examples: S { x: Int, y: UInt8 }, S2 { x: UInt8, s: S, y: UInt8 }
    s_vwt = compose_struct_vwt("S", [i64, u8])
    assert (s_vwt.size, s_vwt.alignment, s_vwt.stride, s_vwt.field_offsets) == (9, 8, 16, (0, 8))
    s2_vwt = compose_struct_vwt("S2", [u8, s_vwt, u8])
    assert (s2_vwt.size, s2_vwt.alignment, s2_vwt.stride, s2_vwt.field_offsets) == (
        18,
        8,
        24,
        (0, 8, 17),
    )
    # Compare with C/Rust repr(C), where S is padded to 16 so S2.y sits at offset 24, size 32!
    c_s_size = round_up(9, 8)  # 16
    c_s2_y_offset = round_up(1, 8) + c_s_size  # 24
    c_s2_size = round_up(c_s2_y_offset + 1, 8)  # 32
    assert c_s2_size - s2_vwt.stride == 8  # Swift saves 8 bytes of stride via tail-padding reuse

    contains_empty = compose_struct_vwt("ContainsEmpty", [i64, empty, i64])
    assert (contains_empty.size, contains_empty.stride, contains_empty.field_offsets) == (
        16,
        16,
        (0, 8, 8),
    )
    assert empty.size == 0 and empty.stride == 1

    # 2. Single-payload enum extra-inhabitant nesting: Bool -> Optional<Bool> -> Optional<Optional<Bool>>
    opt_bool = compose_single_payload_enum_vwt("Optional<Bool>", bool_vwt, 1)
    assert (opt_bool.size, opt_bool.stride, opt_bool.extra_inhabitant_count) == (1, 1, 253)
    opt_opt_bool = compose_single_payload_enum_vwt("Optional<Optional<Bool>>", opt_bool, 1)
    assert (opt_opt_bool.size, opt_opt_bool.stride, opt_opt_bool.extra_inhabitant_count) == (
        1,
        1,
        252,
    )

    opt_cls = compose_single_payload_enum_vwt("Optional<ClassRef>", cls, 1)
    assert (opt_cls.size, opt_cls.stride, opt_cls.extra_inhabitant_count) == (8, 8, 0)
    opt_i64 = compose_single_payload_enum_vwt("Optional<Int>", i64, 1)
    assert (opt_i64.size, opt_i64.stride, opt_i64.extra_inhabitant_count) == (9, 16, 0)

    # 3. Overflowing empty cases: 1-byte payload with 300 empty cases -> 1 extra tag byte, size=2
    big_enum = compose_single_payload_enum_vwt("BigEnum<UInt8>", u8, 300)
    assert (big_enum.size, big_enum.stride, big_enum.extra_inhabitant_count) == (2, 2, 0)
    rt = SimRuntime()
    slot = rt.alloc_stack(big_enum.size, big_enum.alignment)
    for case_tag in range(0, 301):
        if case_tag == 0:
            rt.mem[slot] = 0xAB
            u8.store_enum_tag_single_payload(rt, slot, 0, 300)
            assert u8.get_enum_tag_single_payload(rt, slot, 300) == 0
            assert rt.mem[slot] == 0xAB
        else:
            u8.store_enum_tag_single_payload(rt, slot, case_tag, 300)
            assert u8.get_enum_tag_single_payload(rt, slot, 300) == case_tag

    # 4. Unspecialized generic_array_reverse over ARC-bearing struct and non-bitwise-takable WeakRef
    pair_arc_weak = compose_struct_vwt("Pair<ClassRef, WeakRef>", [cls, weak])
    assert not pair_arc_weak.is_pod
    assert not pair_arc_weak.is_bitwise_takable
    assert not pair_arc_weak.is_inline  # non-bitwise-takable forces IsNonInline even at 16 <= 24B
    assert (pair_arc_weak.size, pair_arc_weak.stride, pair_arc_weak.field_offsets) == (
        16,
        16,
        (0, 8),
    )

    arr_base = rt.alloc_stack(pair_arc_weak.stride * 4, pair_arc_weak.alignment)
    objs = [rt.new_heap_object() for _ in range(4)]
    for i, oid in enumerate(objs):
        elem_addr = arr_base + i * pair_arc_weak.stride
        struct.pack_into("<Q", rt.mem, elem_addr + 0, oid)
        struct.pack_into("<Q", rt.mem, elem_addr + 8, oid)
        rt.register_weak(elem_addr + 8, oid)

    generic_array_reverse(rt, arr_base, 4, pair_arc_weak)
    for i, expected_oid in enumerate(reversed(objs)):
        elem_addr = arr_base + i * pair_arc_weak.stride
        got_strong = struct.unpack_from("<Q", rt.mem, elem_addr + 0)[0]
        got_weak = struct.unpack_from("<Q", rt.mem, elem_addr + 8)[0]
        assert got_strong == expected_oid and got_weak == expected_oid
        assert rt.weak_side_table[elem_addr + 8] == expected_oid
        assert rt.arc_refcounts[expected_oid] == 1  # take moved without retain/release churn

    # Destroy all elements via VWT and verify zero ARC leaks and zero dangling weak registrations.
    for i in range(4):
        pair_arc_weak.destroy(rt, arr_base + i * pair_arc_weak.stride)
    assert all(rc == 0 for rc in rt.arc_refcounts.values())
    assert len(rt.weak_side_table) == 0

    # 5. Verify 3-word ValueBuffer (24B, align 8) inline-vs-out-of-line existential container rule
    big_pod = compose_struct_vwt("BigPod32", [i64, i64, i64, i64])
    assert big_pod.size == 32 and not big_pod.is_inline  # exceeds 24B ValueBuffer
    aligned_16 = make_pod_vwt("Simd16", 16, 16)
    assert not aligned_16.is_inline  # align 16 > alignof(ValueBuffer) == 8 forces out-of-line
    assert s2_vwt.size == 18 and s2_vwt.alignment == 8 and s2_vwt.is_inline  # fits inline

    return {
        "S_layout": (s_vwt.size, s_vwt.alignment, s_vwt.stride, s_vwt.field_offsets),
        "S2_layout": (s2_vwt.size, s2_vwt.alignment, s2_vwt.stride, s2_vwt.field_offsets),
        "S2_c_size": c_s2_size,
        "Optional_Optional_Bool": (
            opt_opt_bool.size,
            opt_opt_bool.stride,
            opt_opt_bool.extra_inhabitant_count,
        ),
        "BigEnum_300_cases_roundtrip": "301/301 exact",
        "Pair_ClassRef_WeakRef_inline": pair_arc_weak.is_inline,
        "ValueBuffer_inline_flags": {
            "S2_18B_a8": s2_vwt.is_inline,
            "BigPod32_32B_a8": big_pod.is_inline,
            "Simd16_16B_a16": aligned_16.is_inline,
            "WeakRef_8B_a8_nonBT": weak.is_inline,
        },
    }


# =============================================================================
# Part 2: Exact Affine-Ceiling Slice-DST Layout Algebra (zerocopy::layout)
# =============================================================================
# Mirrors google/zerocopy@ec133ce4d7993775413d852f91c9e3eb2a2a0897 zerocopy/src/layout.rs.


@dataclass(frozen=True)
class RoundingAlignAndPhase:
    encoded: int

    @classmethod
    def new(cls, align: int, phase: int) -> "RoundingAlignAndPhase":
        assert is_power_of_two(align) and 0 <= phase < align
        return cls(align | phase)

    def components(self) -> tuple[int, int]:
        assert self.encoded > 0
        align = 1 << (self.encoded.bit_length() - 1)
        phase = self.encoded ^ align
        return align, phase


@dataclass(frozen=True)
class TrailingSliceLayout:
    offset: int
    elem_size: int
    size_base: int
    rounding: RoundingAlignAndPhase

    @property
    def size_align(self) -> int:
        return self.rounding.components()[0]

    @property
    def size_phase(self) -> int:
        return self.rounding.components()[1]

    def size_for_elems(self, elems: int) -> int:
        a, r = self.rounding.components()
        return self.size_base + round_up(r + elems * self.elem_size, a)

    def padding_for_elems(self, elems: int) -> int:
        return self.size_for_elems(elems) - (self.offset + elems * self.elem_size)

    def max_trailing_bytes(self, available_bytes: int) -> Optional[int]:
        a, r = self.rounding.components()
        rounded_phase = 0 if r == 0 else a
        minimum_size = self.size_base + rounded_phase
        if available_bytes < minimum_size:
            return None
        extra_bytes = available_bytes - minimum_size
        aligned_bytes = round_down(extra_bytes, a)
        initial_padding = rounded_phase - r
        return aligned_bytes | initial_padding

    def is_injective(self) -> bool:
        """Theorem: S(n) = C + round_up(r + n*E, A) is injective on N iff E >= A."""
        return self.elem_size >= self.size_align

    def find_minimal_plateau(self) -> Optional[tuple[int, int, int]]:
        """When not injective, returns minimal (n1, n2, shared_size) with n1 < n2."""
        if self.elem_size == 0:
            return (0, 1, self.size_for_elems(0))
        if self.elem_size >= self.size_align:
            return None
        prev_size = self.size_for_elems(0)
        for n in range(self.size_align):
            nxt_size = self.size_for_elems(n + 1)
            if nxt_size == prev_size:
                return (n, n + 1, prev_size)
            prev_size = nxt_size
        raise AssertionError("Pigeonhole principle guarantees plateau for 0 < E < A")


@dataclass(frozen=True)
class DstLayout:
    align: int
    sized_size: Optional[int]  # None iff slice DST
    trailing: Optional[TrailingSliceLayout]
    statically_shallow_unpadded: bool = True

    @classmethod
    def new_zst(cls) -> "DstLayout":
        return cls(align=1, sized_size=0, trailing=None, statically_shallow_unpadded=True)

    @classmethod
    def new_sized(cls, size: int, align: int, unpadded: bool = True) -> "DstLayout":
        assert is_power_of_two(align) and size % align == 0
        return cls(align=align, sized_size=size, trailing=None, statically_shallow_unpadded=unpadded)

    @classmethod
    def new_slice(cls, elem_size: int, elem_align: int) -> "DstLayout":
        assert is_power_of_two(elem_align) and elem_size % elem_align == 0
        return cls(
            align=elem_align,
            sized_size=None,
            trailing=TrailingSliceLayout(
                offset=0,
                elem_size=elem_size,
                size_base=0,
                rounding=RoundingAlignAndPhase.new(elem_align, 0),
            ),
            statically_shallow_unpadded=True,
        )

    def align_to(self, min_align: int) -> "DstLayout":
        assert is_power_of_two(min_align)
        return DstLayout(
            align=max(self.align, min_align),
            sized_size=self.sized_size,
            trailing=self.trailing,
            statically_shallow_unpadded=self.statically_shallow_unpadded,
        )

    def extend(self, field_layout: "DstLayout", repr_packed: Optional[int] = None) -> "DstLayout":
        assert self.sized_size is not None, "cannot extend a DST"
        field_align = (
            min(field_layout.align, repr_packed) if repr_packed is not None else field_layout.align
        )
        new_align = max(self.align, field_align)
        offset = round_up(self.sized_size, field_align)
        interfield_pad = offset - self.sized_size
        unpadded = (
            self.statically_shallow_unpadded
            and field_layout.statically_shallow_unpadded
            and interfield_pad == 0
        )
        if field_layout.sized_size is not None:
            return DstLayout(
                align=new_align,
                sized_size=offset + field_layout.sized_size,
                trailing=None,
                statically_shallow_unpadded=unpadded,
            )
        assert field_layout.trailing is not None
        t = field_layout.trailing
        return DstLayout(
            align=new_align,
            sized_size=None,
            trailing=TrailingSliceLayout(
                offset=offset + t.offset,
                elem_size=t.elem_size,
                size_base=offset + t.size_base,
                rounding=t.rounding,
            ),
            statically_shallow_unpadded=unpadded,
        )

    def pad_to_align(self) -> "DstLayout":
        if self.sized_size is not None:
            padded = round_up(self.sized_size, self.align)
            return DstLayout(
                align=self.align,
                sized_size=padded,
                trailing=None,
                statically_shallow_unpadded=self.statically_shallow_unpadded
                and (padded == self.sized_size),
            )
        assert self.trailing is not None
        t = self.trailing
        size_align, size_phase = t.rounding.components()
        if size_align < self.align:
            rounded_base = round_up(t.size_base, size_align)
            fixed_contrib = rounded_base + size_phase
            new_phase = fixed_contrib & (self.align - 1)
            new_base = round_down(fixed_contrib, self.align)
            new_t = TrailingSliceLayout(
                offset=t.offset,
                elem_size=t.elem_size,
                size_base=new_base,
                rounding=RoundingAlignAndPhase.new(self.align, new_phase),
            )
        else:
            new_base = round_up(t.size_base, self.align)
            new_t = TrailingSliceLayout(
                offset=t.offset,
                elem_size=t.elem_size,
                size_base=new_base,
                rounding=t.rounding,
            )
        return DstLayout(
            align=self.align,
            sized_size=None,
            trailing=new_t,
            statically_shallow_unpadded=self.statically_shallow_unpadded,
        )

    def validate_cast(
        self, addr: int, bytes_len: int, prefix: bool
    ) -> Optional[tuple[int, int]]:
        """Port of zerocopy/src/layout.rs:validate_cast_and_convert_metadata."""
        endpoint = addr if prefix else addr + bytes_len
        if endpoint % self.align != 0:
            return None
        if self.sized_size is not None:
            if self.sized_size > bytes_len:
                return None
            obj_size = self.sized_size
            elems = 0
        else:
            assert self.trailing is not None and self.trailing.elem_size > 0
            t = self.trailing
            max_slice = t.max_trailing_bytes(bytes_len)
            if max_slice is None:
                return None
            elems = max_slice // t.elem_size
            unused = max_slice % t.elem_size
            unused_aligned = round_down(unused, t.size_align)
            max_rounded = round_down(bytes_len - t.size_base, t.size_align)
            obj_size = t.size_base + (max_rounded - unused_aligned)
        split_at = obj_size if prefix else bytes_len - obj_size
        return elems, split_at


def verify_dst_layout_algebra() -> dict[str, object]:
    """Exhaustively check algebraic closure, injectivity iff E>=A, and zerocopy bug reproducers."""
    # 1. Exhaustive verification of exact algebraic closure of round_up(c + round_up(r + nE, a), A)
    closure_cases = 0
    for a in (1, 2, 4, 8, 16):
        for A in (1, 2, 4, 8, 16):
            for r in range(a):
                for c in range(0, 2 * max(a, A)):
                    for E in (0, 1, 2, 3, 4, 5, 7, 8, 12, 16):
                        inner = DstLayout(
                            align=A,
                            sized_size=None,
                            trailing=TrailingSliceLayout(
                                offset=c + r,
                                elem_size=E,
                                size_base=c,
                                rounding=RoundingAlignAndPhase.new(a, r),
                            ),
                        )
                        norm = inner.pad_to_align().trailing
                        assert norm is not None
                        for n in range(0, 24):
                            direct = round_up(c + round_up(r + n * E, a), A)
                            normalized = norm.size_for_elems(n)
                            assert direct == normalized, (
                                f"closure mismatch a={a} A={A} r={r} c={c} E={E} n={n}: "
                                f"{direct} != {normalized}"
                            )
                        closure_cases += 1

    # 2. Exhaustive verification of Injectivity Theorem: injective on N iff E >= A
    injectivity_cases = 0
    for A in (1, 2, 4, 8, 16):
        for r in range(A):
            for E in range(0, 2 * A + 1):
                t = TrailingSliceLayout(
                    offset=r,
                    elem_size=E,
                    size_base=0,
                    rounding=RoundingAlignAndPhase.new(A, r),
                )
                sizes = [t.size_for_elems(n) for n in range(0, 2 * A + 4)]
                observed_injective = len(set(sizes)) == len(sizes)
                theorem_injective = E >= A
                assert observed_injective == theorem_injective, (
                    f"injectivity theorem failed A={A}, r={r}, E={E}"
                )
                plateau = t.find_minimal_plateau()
                if theorem_injective:
                    assert plateau is None
                else:
                    assert plateau is not None
                    n1, n2, sz = plateau
                    assert n1 < n2 and t.size_for_elems(n1) == sz == t.size_for_elems(n2)
                injectivity_cases += 1

    # 3. Reproducer A (commit 12f746d23): #[repr(C)] struct Align4Tail { hdr: u32, tail: [u8] }
    u32_l = DstLayout.new_sized(4, 4)
    u8_slice = DstLayout.new_slice(1, 1)
    align4_tail = DstLayout.new_zst().extend(u32_l).extend(u8_slice).pad_to_align()
    assert align4_tail.trailing is not None
    t_a = align4_tail.trailing
    assert (t_a.offset, t_a.elem_size, t_a.size_base, t_a.size_align, t_a.size_phase) == (
        4,
        1,
        4,
        4,
        0,
    )
    plateau_a = [t_a.size_for_elems(n) for n in range(6)]  # [4, 8, 8, 8, 8, 12]
    assert plateau_a == [4, 8, 8, 8, 8, 12]
    # Reconstructing from 8-byte buffer returns max elems = 4 even if caller validated elems = 1!
    reconstructed = align4_tail.validate_cast(0, 8, prefix=True)
    assert reconstructed == (4, 8)
    # Also #[repr(C, align(4))] struct Header3 { hdr: u16, tag: u8, tail: [u8] }: n=0 and n=1 both 4B
    header3 = (
        DstLayout.new_zst()
        .extend(DstLayout.new_sized(2, 2))
        .extend(DstLayout.new_sized(1, 1))
        .extend(u8_slice)
        .align_to(4)
        .pad_to_align()
    )
    assert header3.trailing is not None
    assert [header3.trailing.size_for_elems(n) for n in range(6)] == [4, 4, 8, 8, 8, 8]

    # 4. Reproducer B (commit 242ff08b5): legal Rust packed(2) wrapping naturally align-4 repr(C) DST:
    #    #[repr(C)] struct Inner { a: u32, b: u8, s: [u8] }   (align=4, offset=5, size_base=4, phase=1)
    #    #[repr(C, packed(2))] struct Outer { hdr: u8, inner: Inner }
    u8_l = DstLayout.new_sized(1, 1)
    inner = DstLayout.new_zst().extend(u32_l).extend(u8_l).extend(u8_slice).pad_to_align()
    assert inner.trailing is not None
    assert (inner.align, inner.trailing.offset, inner.trailing.size_base,
            inner.trailing.size_align, inner.trailing.size_phase) == (4, 5, 4, 4, 1)
    outer = DstLayout.new_zst().extend(u8_l, repr_packed=2).extend(inner, repr_packed=2).pad_to_align()
    assert outer.trailing is not None
    to = outer.trailing
    # Notice outer.align == 2 < outer.trailing.size_align == 4 and offset (7) % 4 == 3 != size_phase (1)!
    assert (outer.align, to.offset, to.size_base, to.size_align, to.size_phase) == (2, 7, 6, 4, 1)
    exact_sizes = [to.size_for_elems(n) for n in range(7)]
    naive_flattened = [round_up(to.offset + n * to.elem_size, outer.align) for n in range(7)]
    assert exact_sizes == [10, 10, 10, 10, 14, 14, 14]
    assert naive_flattened == [8, 8, 10, 10, 12, 12, 14]  # understates true size at n=0,1,4,5!

    # 5. Cross-check O(1) validate_cast against brute force across prefix & suffix casts
    cast_checks = 0
    for layout in (align4_tail, header3, outer):
        assert layout.trailing is not None
        t = layout.trailing
        for addr in (0, 1, 2, 3, 4, 6, 8):
            for buf_len in range(0, 28):
                for prefix in (True, False):
                    got = layout.validate_cast(addr, buf_len, prefix=prefix)
                    endpoint = addr if prefix else addr + buf_len
                    if endpoint % layout.align != 0:
                        expected = None
                    else:
                        fitting = [
                            (n, t.size_for_elems(n))
                            for n in range(0, 32)
                            if t.size_for_elems(n) <= buf_len
                        ]
                        if not fitting:
                            expected = None
                        else:
                            best_n, best_sz = fitting[-1]
                            expected = (best_n, best_sz if prefix else buf_len - best_sz)
                    assert got == expected, (
                        f"validate_cast mismatch addr={addr} len={buf_len} prefix={prefix}: "
                        f"{got} != {expected}"
                    )
                    cast_checks += 1

    return {
        "closure_identities_checked": closure_cases,
        "injectivity_triples_checked": injectivity_cases,
        "cast_oracle_checks": cast_checks,
        "align4_tail_sizes_0_to_5": plateau_a,
        "outer_packed2_inner_align4_exact": exact_sizes,
        "outer_packed2_inner_align4_naive_bug": naive_flattened,
    }


# =============================================================================
# Part 3: Symbolic Polymorphic Interior & Trailing Padding Solver
# =============================================================================


@dataclass(frozen=True)
class SymType:
    """Symbolic field type in a generic repr(C)/packed(k)/align(m) composite."""

    kind: str  # "concrete" | "param" | "array" | "slice"
    name: str
    size: int = 0  # for concrete
    align: int = 1  # for concrete
    elem: Optional["SymType"] = None  # for array / slice
    count: int = 1  # for array


@dataclass(frozen=True)
class LayoutSpec:
    name: str
    fields: tuple[SymType, ...]
    repr_packed: Optional[int] = None
    repr_align: Optional[int] = None


@dataclass(frozen=True)
class ConcreteParamVal:
    size: int
    align: int


def eval_field_concrete(
    ft: SymType, env: dict[str, ConcreteParamVal]
) -> tuple[bool, int, int]:
    """Returns (is_slice, size_or_elem_size, align)."""
    if ft.kind == "concrete":
        return (False, ft.size, ft.align)
    if ft.kind == "param":
        v = env[ft.name]
        return (False, v.size, v.align)
    if ft.kind == "array":
        assert ft.elem is not None
        is_s, esz, eal = eval_field_concrete(ft.elem, env)
        assert not is_s
        return (False, esz * ft.count, eal)
    if ft.kind == "slice":
        assert ft.elem is not None
        is_s, esz, eal = eval_field_concrete(ft.elem, env)
        assert not is_s
        return (True, esz, eal)
    raise ValueError(ft.kind)


def check_concrete_padding(
    spec: LayoutSpec, env: dict[str, ConcreteParamVal]
) -> tuple[int, int]:
    """Returns (max_interfield_padding, max_trailing_padding) across slice lengths."""
    assert not (spec.repr_packed is not None and spec.repr_align is not None)
    offset = 0
    struct_align = spec.repr_align if spec.repr_align is not None else 1
    interfield_pad = 0
    has_slice = False
    slice_elem_size = 0
    slice_offset = 0

    for idx, ft in enumerate(spec.fields):
        is_slice, sz, al = eval_field_concrete(ft, env)
        eff_align = min(al, spec.repr_packed) if spec.repr_packed is not None else al
        aligned_off = round_up(offset, eff_align)
        interfield_pad += aligned_off - offset
        offset = aligned_off
        struct_align = max(struct_align, eff_align)
        if is_slice:
            assert idx == len(spec.fields) - 1, "slice must be trailing field"
            has_slice = True
            slice_elem_size = sz
            slice_offset = offset
        else:
            offset += sz

    if not has_slice:
        trailing_pad = round_up(offset, struct_align) - offset
        return interfield_pad, trailing_pad

    # Trailing padding for slice DST is periodic modulo struct_align.
    max_trailing = 0
    for n in range(struct_align + 1):
        end = slice_offset + n * slice_elem_size
        pad = round_up(end, struct_align) - end
        if pad > max_trailing:
            max_trailing = pad
    return interfield_pad, max_trailing


def collect_params(spec: LayoutSpec) -> list[str]:
    found: list[str] = []

    def visit(ft: SymType) -> None:
        if ft.kind == "param" and ft.name not in found:
            found.append(ft.name)
        elif ft.elem is not None:
            visit(ft.elem)

    for f in spec.fields:
        visit(f)
    return found


def decide_universal_padding_free(
    spec: LayoutSpec,
    constraint: Callable[[dict[str, ConcreteParamVal]], bool] = lambda _env: True,
) -> tuple[bool, Optional[dict[str, ConcreteParamVal]], tuple[int, int]]:
    """Bounded small-model solver for universal NoInteriorPadding & NoTrailingPadding.

    Because repr(C)/packed(k)/align(m) padding depends solely on alignments (powers
    of two) and sizes modulo the maximum alignment, testing alignments up to
    2 * max_explicit_align (with distinct fresh powers per parameter) and sizes
    {0, a, 2a, 3a} (with 0 only if zero-sized allowed, and multiples of a up to
    max_align + a) is complete for finding padding counterexamples.
    """
    params = collect_params(spec)
    max_concrete = 1
    if spec.repr_packed:
        max_concrete = max(max_concrete, spec.repr_packed)
    if spec.repr_align:
        max_concrete = max(max_concrete, spec.repr_align)

    def scan_align(ft: SymType) -> int:
        if ft.kind == "concrete":
            return ft.align
        if ft.elem is not None:
            return scan_align(ft.elem)
        return 1

    for f in spec.fields:
        max_concrete = max(max_concrete, scan_align(f))

    # Candidate power-of-two alignments covering 1 .. max_concrete * 2^len(params)
    max_pow = max(4, (max_concrete.bit_length() - 1) + max(1, len(params)))
    aligns = [1 << k for k in range(0, min(max_pow + 1, 6))]
    max_a = aligns[-1]

    # Candidate (size, align) pairs per parameter: size is a multiple of align
    # covering all residues modulo max_a (including ZST size=0 and odd/even multiples).
    domain: list[ConcreteParamVal] = []
    for a in aligns:
        seen_mods: set[int] = set()
        for mult in (0, 1, 2, 3, 4, 5):
            sz = mult * a
            key = (sz == 0, sz % max_a)
            if key not in seen_mods:
                seen_mods.add(key)
                domain.append(ConcreteParamVal(size=sz, align=a))

    for combo in itertools.product(domain, repeat=len(params)):
        env = dict(zip(params, combo))
        if not constraint(env):
            continue
        inter, trail = check_concrete_padding(spec, env)
        if inter > 0 or trail > 0:
            return (False, env, (inter, trail))
    return (True, None, (0, 0))


def verify_polymorphic_padding_solver() -> dict[str, object]:
    T = SymType("param", "T")
    U = SymType("param", "U")
    u8 = SymType("concrete", "u8", size=1, align=1)
    u16 = SymType("concrete", "u16", size=2, align=2)

    # Case 1: Unconstrained repr(C) Pair<T, U>(T, U) -> FAILS (e.g. T=(1,1), U=(2,2))
    s_pair = LayoutSpec("Pair<T, U>", (T, U))
    ok1, cex1, pads1 = decide_universal_padding_free(s_pair)
    assert not ok1 and cex1 is not None and (pads1[0] > 0 or pads1[1] > 0)

    # Case 2: Homogeneous repr(C) Homog<T>(T, [T; 3], [T]) -> UNIVERSALLY PADDING-FREE
    s_homog = LayoutSpec(
        "Homog<T>",
        (T, SymType("array", "[T; 3]", elem=T, count=3), SymType("slice", "[T]", elem=T)),
    )
    ok2, cex2, _ = decide_universal_padding_free(s_homog)
    assert ok2 and cex2 is None

    # Case 2b: Homogeneous with repr(C, packed(4)) -> STILL UNIVERSALLY PADDING-FREE
    s_homog_p4 = LayoutSpec("HomogPacked4<T>", s_homog.fields, repr_packed=4)
    ok2b, _, _ = decide_universal_padding_free(s_homog_p4)
    assert ok2b

    # Case 3: Pair<T, U> with Align(T) >= Align(U) ONLY -> FAILS on trailing padding!
    ok3, cex3, pads3 = decide_universal_padding_free(
        s_pair, constraint=lambda e: e["T"].align >= e["U"].align
    )
    assert not ok3 and pads3[0] == 0 and pads3[1] > 0  # zero interior, nonzero trailing!

    # Case 3b: Same check restricted to non-ZST fields (size > 0): still fails on trailing pad!
    ok3_nz, cex3_nz, pads3_nz = decide_universal_padding_free(
        s_pair,
        constraint=lambda e: e["T"].align >= e["U"].align
        and e["T"].size > 0
        and e["U"].size > 0,
    )
    assert not ok3_nz and pads3_nz[0] == 0 and pads3_nz[1] > 0

    # Case 4: Pair<T, U> with Align(T) >= Align(U) AND Size(U) % Align(T) == 0 -> PASSES!
    ok4, cex4, _ = decide_universal_padding_free(
        s_pair,
        constraint=lambda e: e["T"].align >= e["U"].align
        and (e["U"].size % e["T"].align == 0),
    )
    assert ok4 and cex4 is None

    # Case 5: repr(C, packed(2)) Pack2<T>(u16, T) unconstrained -> FAILS on trailing padding (T=u8)
    s_p2 = LayoutSpec("Pack2<T>", (u16, T), repr_packed=2)
    ok5, cex5, pads5 = decide_universal_padding_free(s_p2)
    assert not ok5 and pads5 == (0, 1)

    # Case 6: repr(C, packed(2)) Pack2<T>(u16, T) with Size(T) % 2 == 0 -> PASSES!
    ok6, _, _ = decide_universal_padding_free(s_p2, constraint=lambda e: e["T"].size % 2 == 0)
    assert ok6

    # Case 7: repr(C, packed(1)) Pack1<T, U>(u8, T, U) -> UNIVERSALLY PADDING-FREE
    s_p1 = LayoutSpec("Pack1<T, U>", (u8, T, U), repr_packed=1)
    ok7, _, _ = decide_universal_padding_free(s_p1)
    assert ok7

    return {
        "Pair_unconstrained": (ok1, cex1, pads1),
        "Homog_slice_dst": ok2,
        "Homog_packed4": ok2b,
        "Pair_alignT_ge_alignU": (ok3, cex3, pads3),
        "Pair_alignT_ge_alignU_nonzero": (ok3_nz, cex3_nz, pads3_nz),
        "Pair_alignT_ge_alignU_and_sizeU_div_alignT": ok4,
        "Pack2_u16_T_unconstrained": (ok5, cex5, pads5),
        "Pack2_u16_T_even_size": ok6,
        "Pack1_u8_T_U": ok7,
    }


# =============================================================================
# Part 4: Reference-Admissible Nondeterministic repr(Rust) Layout Refinement
# =============================================================================


def enumerate_reference_admissible_layouts(
    fields: list[tuple[str, int, int]], extra_pad_budget: int = 2
) -> list[dict[str, object]]:
    """Enumerate reference-admissible repr(Rust) layouts satisfying Rust Reference
    r[layout.repr.rust.layout] & r[layout.repr.rust.struct]:
      1. offset(f) % align(f) == 0
      2. struct_align >= max(align(f))
      3. non-overlapping intervals [offset(f), offset(f) + size(f))
      4. size % struct_align == 0
    """
    min_align = max((a for _, _, a in fields), default=1)
    admissible: list[dict[str, object]] = []
    for perm in itertools.permutations(fields):
        # Compact layout for this field permutation (0 extra arbitrary padding)
        off = 0
        offsets: dict[str, int] = {}
        for name, sz, al in perm:
            off = round_up(off, al)
            offsets[name] = off
            off += sz
        min_size = round_up(off, min_align)
        admissible.append(
            {
                "order": tuple(name for name, _, _ in perm),
                "offsets": offsets,
                "align": min_align,
                "size": min_size,
                "padding": min_size - sum(sz for _, sz, _ in fields),
            }
        )
        # Also include a reference-admissible compiler choice adding extra tail alignment/padding
        if extra_pad_budget > 0:
            larger_size = min_size + min_align
            admissible.append(
                {
                    "order": tuple(name for name, _, _ in perm),
                    "offsets": offsets,
                    "align": min_align,
                    "size": larger_size,
                    "padding": larger_size - sum(sz for _, sz, _ in fields),
                }
            )
    return admissible


def verify_reference_admissible_refinement() -> dict[str, object]:
    fields = [("a", 1, 1), ("b", 2, 2), ("c", 1, 1)]
    admissible = enumerate_reference_admissible_layouts(fields)
    compact_sizes = sorted({int(x["size"]) for x in admissible if x["padding"] <= 2})
    # Compiler V1 (size-optimal greedy sort): order (b, a, c) -> size 4, padding 0
    # Compiler V2 (declaration order): order (a, b, c) -> size 6, padding 2
    assert 4 in compact_sizes and 6 in compact_sizes
    # Check universal (demonic) property: non-overlap & alignment hold for ALL admissible layouts
    for lay in admissible:
        offs = lay["offsets"]
        assert isinstance(offs, dict)
        intervals = []
        for name, sz, al in fields:
            assert offs[name] % al == 0
            intervals.append((offs[name], offs[name] + sz))
        intervals.sort()
        for (_, end_prev), (start_next, _) in zip(intervals, intervals[1:]):
            assert end_prev <= start_next
        assert int(lay["size"]) % int(lay["align"]) == 0
    # Fragile property (size == 4 / zero padding) holds for some refinements, FAILS demonically!
    all_zero_pad = all(lay["padding"] == 0 for lay in admissible)
    some_zero_pad = any(lay["padding"] == 0 for lay in admissible)
    assert some_zero_pad and not all_zero_pad
    return {
        "struct_R_fields": fields,
        "admissible_layouts_enumerated": len(admissible),
        "compact_sizes": compact_sizes,
        "demonic_zero_padding_holds": all_zero_pad,
        "existential_zero_padding_holds": some_zero_pad,
    }


def main() -> int:
    r1 = verify_swift_vwt_composition()
    r2 = verify_dst_layout_algebra()
    r3 = verify_polymorphic_padding_solver()
    r4 = verify_reference_admissible_refinement()
    print("[PASS] Part 1 (Swift Value Witness Table composition & generic execution):", r1)
    print("[PASS] Part 2 (Affine-ceiling slice-DST algebra & plateau counterexamples):", r2)
    print("[PASS] Part 3 (Symbolic polymorphic interior/trailing padding solver):", r3)
    print("[PASS] Part 4 (Reference-admissible repr(Rust) nondeterministic refinement):", r4)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
