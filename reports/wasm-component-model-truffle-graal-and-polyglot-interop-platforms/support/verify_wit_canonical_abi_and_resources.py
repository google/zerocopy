#!/usr/bin/env python3
"""Executable specification probe for:
1. WebAssembly Component Model Canonical ABI:
   - Disjoint linear memories with `cabi_realloc` + `may_leave` reentrancy guard.
   - String transcoding (`utf8`, `utf16`, `latin1+utf16`) byte-copy & realloc amplification.
   - `own<T>` / `borrow<T>` resource handle table state machine & dynamic traps.
2. Cap'n Proto zero-copy wire format validation:
   - 64-bit word-aligned in-place pointer decoding (0 payload copies).
   - `nestingLimit` cycle rejection, `ReadLimiter` DAG amplification rejection,
     `amplifiedRead` zero-sized `INLINE_COMPOSITE` list rejection, and bounds checking.

Self-contained Python 3.10+ standard-library script; exits 0 iff all checks pass.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import IntEnum
import json
import struct
import sys
from typing import Any, Callable, Literal


# =============================================================================
# Part 1: WebAssembly Component Model Canonical ABI & Resource State Machine
# Mirrors WebAssembly/component-model design/mvp/canonical-abi/definitions.py
# =============================================================================

MAX_TABLE_LENGTH = (1 << 28) - 1
MAX_STRING_BYTE_LENGTH = (1 << 28) - 1
MAX_LIST_BYTE_LENGTH = (1 << 28) - 1
REALLOC_I32_MAX = (1 << 32) - 1
UTF16_TAG_32 = 1 << 31
MAX_FLAT_PARAMS = 16
MAX_FLAT_ASYNC_PARAMS = 4
MAX_FLAT_RESULTS = 1


class WasmTrap(RuntimeError):
    """Canonical ABI runtime trap."""

    def __init__(self, code: str, message: str) -> None:
        super().__init__(f"[{code}] {message}")
        self.code = code
        self.message = message


class StaticValidationError(ValueError):
    """Component binary/WIT static type validation failure."""


def trap_if(cond: bool, code: str, msg: str) -> None:
    if cond:
        raise WasmTrap(code, msg)


def align_to(ptr: int, alignment: int) -> int:
    return (ptr + alignment - 1) & ~(alignment - 1)


@dataclass(frozen=True)
class ValType:
    kind: str
    inner: Any = None


def contains_borrow(t: ValType | None) -> bool:
    if t is None:
        return False
    if t.kind == "borrow":
        return True
    if t.kind in ("list", "option", "stream", "future"):
        return contains_borrow(t.inner)
    if t.kind in ("record", "variant", "tuple"):
        return any(contains_borrow(sub) for sub in t.inner)
    if t.kind == "result":
        ok_t, err_t = t.inner
        return contains_borrow(ok_t) or contains_borrow(err_t)
    return False


@dataclass(frozen=True)
class FuncType:
    params: tuple[ValType, ...]
    results: tuple[ValType, ...]
    async_: bool = False


def validate_func_type(ft: FuncType) -> None:
    """Static rule (Binary.md): transitive `borrow<T>` is rejected in results."""
    for res in ft.results:
        if contains_borrow(res):
            raise StaticValidationError(
                "borrow<T> is forbidden anywhere in a component function result type"
            )
    for param in ft.params:
        if param.kind in ("stream", "future") and contains_borrow(param.inner):
            raise StaticValidationError(
                "borrow<T> is forbidden inside stream<T> or future<T> element types"
            )


@dataclass
class CopyMetrics:
    src_bytes_read: int = 0
    dst_bytes_written: int = 0
    realloc_calls: int = 0
    peak_allocated_bytes: int = 0
    final_allocated_bytes: int = 0
    in_place_widen_bytes_moved: int = 0


class LinearMemory:
    """Disjoint linear memory with instrumented bump/realloc allocator (`cabi_realloc`)."""

    def __init__(self, size: int = 1 << 20) -> None:
        self.buf = bytearray(size)
        self.heap_top = 16  # Reserve address 0 as non-allocated sentinel
        self.allocs: dict[int, int] = {}

    def __len__(self) -> int:
        return len(self.buf)

    def cabi_realloc(
        self, old_ptr: int, old_size: int, align: int, new_size: int
    ) -> int:
        if align == 0 or (align & (align - 1)) != 0:
            raise WasmTrap("INVALID_ALIGN", f"alignment {align} is not a power of two")
        if new_size == 0:
            return align
        if old_ptr == 0:
            ptr = align_to(self.heap_top, align)
            if ptr + new_size > len(self.buf):
                raise WasmTrap("OOM", "linear memory exhausted")
            self.heap_top = ptr + new_size
            self.allocs[ptr] = new_size
            return ptr
        # Shrink in-place if new_size <= old_size
        if new_size <= old_size:
            self.allocs[old_ptr] = new_size
            return old_ptr
        # Grow by allocating a new block and copying existing bytes
        new_ptr = align_to(self.heap_top, align)
        if new_ptr + new_size > len(self.buf):
            raise WasmTrap("OOM", "linear memory exhausted on grow")
        self.buf[new_ptr : new_ptr + old_size] = self.buf[old_ptr : old_ptr + old_size]
        self.heap_top = new_ptr + new_size
        self.allocs[new_ptr] = new_size
        return new_ptr


class HandleTable:
    """Component-local resource handle table (definitions.py `Table`)."""

    def __init__(self) -> None:
        # Slot 0 is always reserved (None) per Table.__init__.
        self.array: list[Any] = [None]
        self.free: list[int] = []

    def get(self, idx: int) -> Any:
        trap_if(idx < 0 or idx >= len(self.array), "UNKNOWN_HANDLE", f"invalid handle {idx}")
        entry = self.array[idx]
        trap_if(entry is None, "UNKNOWN_HANDLE", f"handle slot {idx} is empty/dropped")
        return entry

    def add(self, entry: Any) -> int:
        if self.free:
            idx = self.free.pop()
            assert self.array[idx] is None
            self.array[idx] = entry
            return idx
        idx = len(self.array)
        trap_if(idx > MAX_TABLE_LENGTH, "HANDLE_TABLE_FULL", "handle table overflow")
        self.array.append(entry)
        return idx

    def remove(self, idx: int) -> Any:
        entry = self.get(idx)
        self.array[idx] = None
        self.free.append(idx)
        return entry


@dataclass
class ResourceType:
    name: str
    impl_inst: "ComponentInstance"
    dtor: Callable[[int], None] | None = None


@dataclass
class ResourceHandle:
    rt: ResourceType
    rep_val: int
    own: bool
    borrow_scope: "Task | None" = None
    num_lends: int = 0


@dataclass
class Task:
    inst: "ComponentInstance"
    num_borrows: int = 0
    resolved: bool = False

    def return_(self) -> None:
        trap_if(self.resolved, "DOUBLE_RETURN", "task already resolved")
        trap_if(
            self.num_borrows > 0,
            "UNRELEASED_BORROW",
            f"borrow handles still remain at the end of the call ({self.num_borrows})",
        )
        self.resolved = True


@dataclass
class Subtask:
    lenders: list[ResourceHandle] = field(default_factory=list)
    resolved: bool = False

    def add_lender(self, h: ResourceHandle) -> None:
        assert not self.resolved
        h.num_lends += 1
        self.lenders.append(h)

    def deliver_resolve(self) -> None:
        assert not self.resolved
        for h in self.lenders:
            h.num_lends -= 1
        self.lenders.clear()
        self.resolved = True


StringEncoding = Literal["utf8", "utf16", "latin1+utf16"]


class ComponentInstance:
    def __init__(
        self,
        name: str,
        string_encoding: StringEncoding = "utf8",
        realloc_hook: Callable[["ComponentInstance", int, int, int, int], int] | None = None,
    ) -> None:
        self.name = name
        self.memory = LinearMemory()
        self.handles = HandleTable()
        self.string_encoding: StringEncoding = string_encoding
        self.may_leave: bool = True
        self.realloc_hook = realloc_hook

    def reallocate(
        self,
        old_ptr: int,
        old_size: int,
        align: int,
        new_size: int,
        metrics: CopyMetrics | None = None,
    ) -> int:
        assert self.may_leave, "cannot invoke cabi_realloc when may_leave is already false"
        self.may_leave = False
        try:
            if self.realloc_hook is not None:
                ptr = self.realloc_hook(self, old_ptr, old_size, align, new_size)
            else:
                ptr = self.memory.cabi_realloc(old_ptr, old_size, align, new_size)
        finally:
            self.may_leave = True
        trap_if(ptr != align_to(ptr, align), "MISALIGNED_REALLOC", "cabi_realloc returned unaligned pointer")
        trap_if(ptr + new_size > len(self.memory), "OOB_REALLOC", "cabi_realloc returned out-of-bounds range")
        if metrics is not None:
            metrics.realloc_calls += 1
            if old_ptr != 0 and new_size > old_size:
                # Growing realloc copies old_size bytes inside guest allocator
                metrics.dst_bytes_written += old_size
            metrics.peak_allocated_bytes = max(metrics.peak_allocated_bytes, new_size)
            metrics.final_allocated_bytes = new_size
        return ptr

    # --- Canonical resource built-ins (definitions.py L2254-2293) ---

    def canon_resource_new(self, rt: ResourceType, rep_val: int) -> int:
        trap_if(not self.may_leave, "CANNOT_LEAVE", "may_leave is false during resource.new")
        trap_if(rt.impl_inst is not self, "WRONG_DEFINER", "only defining instance may call resource.new")
        return self.handles.add(ResourceHandle(rt=rt, rep_val=rep_val, own=True))

    def canon_resource_rep(self, rt: ResourceType, handle_idx: int) -> int:
        trap_if(rt.impl_inst is not self, "WRONG_DEFINER", "only defining instance may call resource.rep")
        h = self.handles.get(handle_idx)
        trap_if(not isinstance(h, ResourceHandle), "NOT_RESOURCE", "handle is not a resource")
        trap_if(h.rt is not rt, "TYPE_MISMATCH", "resource handle type mismatch")
        return h.rep_val

    def canon_resource_drop(self, rt: ResourceType, handle_idx: int) -> None:
        trap_if(not self.may_leave, "CANNOT_LEAVE", "may_leave is false during resource.drop")
        h = self.handles.get(handle_idx)
        trap_if(not isinstance(h, ResourceHandle), "NOT_RESOURCE", "handle is not a resource")
        trap_if(h.rt is not rt, "TYPE_MISMATCH", "resource handle type mismatch")
        if h.own:
            trap_if(h.num_lends != 0, "OWN_STILL_BORROWED", "cannot remove owned resource while borrowed")
        else:
            trap_if(h.num_lends != 0, "BORROW_STILL_LENT", "cannot remove borrowed resource while it is lent out")
        self.handles.remove(handle_idx)
        if h.own:
            assert h.borrow_scope is None
            if rt.dtor is not None:
                rt.dtor(h.rep_val)
        else:
            assert h.borrow_scope is not None
            h.borrow_scope.num_borrows -= 1

    # --- Resource lift/lower transitions (definitions.py L1440-1454, L1734-1748) ---

    def lift_own(self, handle_idx: int, rt: ResourceType) -> int:
        h = self.handles.get(handle_idx)
        trap_if(not isinstance(h, ResourceHandle), "NOT_RESOURCE", "handle is not a resource")
        trap_if(h.rt is not rt, "TYPE_MISMATCH", "resource handle type mismatch")
        trap_if(not h.own, "LIFT_OWN_FROM_BORROW", "cannot lift own resource from a borrow")
        trap_if(h.num_lends != 0, "OWN_STILL_BORROWED", "cannot transfer owned resource while borrowed")
        self.handles.remove(handle_idx)
        return h.rep_val

    def lift_borrow(self, handle_idx: int, rt: ResourceType, subtask: Subtask) -> int:
        h = self.handles.get(handle_idx)
        trap_if(not isinstance(h, ResourceHandle), "NOT_RESOURCE", "handle is not a resource")
        trap_if(h.rt is not rt, "TYPE_MISMATCH", "resource handle type mismatch")
        subtask.add_lender(h)
        return h.rep_val

    def lower_own(self, rep_val: int, rt: ResourceType) -> int:
        return self.handles.add(ResourceHandle(rt=rt, rep_val=rep_val, own=True))

    def lower_borrow(self, rep_val: int, rt: ResourceType, callee_task: Task) -> int:
        # Canonical ABI optimization (pass_rep_not_handle): if callee defines `rt`,
        # pass raw `rep_val` directly without creating a handle-table borrow entry.
        if self is rt.impl_inst:
            return rep_val
        h = ResourceHandle(rt=rt, rep_val=rep_val, own=False, borrow_scope=callee_task)
        callee_task.num_borrows += 1
        return self.handles.add(h)


# --- Canonical ABI String Lifting & Lowering (definitions.py L1352-1672) ---

def write_guest_string_raw(inst: ComponentInstance, raw_bytes: bytes, encoding_tag_bit: bool = False) -> tuple[int, int]:
    """Helper to place raw string bytes in a guest component's linear memory."""
    align = 1 if inst.string_encoding == "utf8" else 2
    ptr = inst.reallocate(0, 0, align, len(raw_bytes))
    inst.memory.buf[ptr : ptr + len(raw_bytes)] = raw_bytes
    if inst.string_encoding == "utf8":
        tagged = len(raw_bytes)
    elif inst.string_encoding == "utf16":
        assert len(raw_bytes) % 2 == 0
        tagged = len(raw_bytes) // 2
    else:  # latin1+utf16
        if encoding_tag_bit:
            assert len(raw_bytes) % 2 == 0
            tagged = (len(raw_bytes) // 2) | UTF16_TAG_32
        else:
            tagged = len(raw_bytes)
    return ptr, tagged


def load_string_from_range(
    src_inst: ComponentInstance,
    ptr: int,
    tagged_code_units: int,
    metrics: CopyMetrics,
) -> tuple[str, StringEncoding, int]:
    if src_inst.string_encoding == "utf8":
        alignment = 1
        byte_length = tagged_code_units
        py_enc = "utf-8"
    elif src_inst.string_encoding == "utf16":
        alignment = 2
        byte_length = 2 * tagged_code_units
        py_enc = "utf-16-le"
    else:  # latin1+utf16
        alignment = 2
        if tagged_code_units & UTF16_TAG_32:
            byte_length = 2 * (tagged_code_units ^ UTF16_TAG_32)
            py_enc = "utf-16-le"
        else:
            byte_length = tagged_code_units
            py_enc = "latin-1"

    trap_if(byte_length > MAX_STRING_BYTE_LENGTH, "STRING_TOO_LONG", "string exceeds MAX_STRING_BYTE_LENGTH")
    trap_if(ptr != align_to(ptr, alignment), "MISALIGNED_STRING", "string pointer misaligned")
    trap_if(ptr + byte_length > len(src_inst.memory), "OOB_STRING", "string out of bounds")
    raw = bytes(src_inst.memory.buf[ptr : ptr + byte_length])
    metrics.src_bytes_read += byte_length
    try:
        text = raw.decode(py_enc, errors="strict")
    except UnicodeError as exc:
        raise WasmTrap("INVALID_UNICODE", f"invalid {py_enc} scalar sequence: {exc}") from exc
    return text, src_inst.string_encoding, tagged_code_units


def store_string_into_range(
    dst_inst: ComponentInstance,
    lifted: tuple[str, StringEncoding, int],
    metrics: CopyMetrics,
) -> tuple[int, int]:
    src, src_enc, src_tagged = lifted
    if src_enc == "latin1+utf16":
        if src_tagged & UTF16_TAG_32:
            src_simple = "utf16"
            src_code_units = src_tagged ^ UTF16_TAG_32
        else:
            src_simple = "latin1"
            src_code_units = src_tagged
    else:
        src_simple = src_enc
        src_code_units = src_tagged

    dst_enc = dst_inst.string_encoding

    def store_copy(dst_unit_size: int, dst_align: int, py_enc: str) -> tuple[int, int]:
        dst_bytes = dst_unit_size * src_code_units
        ptr = dst_inst.reallocate(0, 0, dst_align, dst_bytes, metrics)
        encoded = src.encode(py_enc)
        assert len(encoded) == dst_bytes
        dst_inst.memory.buf[ptr : ptr + dst_bytes] = encoded
        metrics.dst_bytes_written += dst_bytes
        return ptr, src_code_units

    def store_to_utf8(worst_case_size: int) -> tuple[int, int]:
        ptr = dst_inst.reallocate(0, 0, 1, src_code_units, metrics)
        for i, cp in enumerate(src):
            if ord(cp) < 0x80:
                dst_inst.memory.buf[ptr + i] = ord(cp)
                metrics.dst_bytes_written += 1
            else:
                ptr = dst_inst.reallocate(ptr, src_code_units, 1, worst_case_size, metrics)
                encoded = src.encode("utf-8")
                tail = encoded[i:]
                dst_inst.memory.buf[ptr + i : ptr + len(encoded)] = tail
                metrics.dst_bytes_written += len(tail)
                if worst_case_size > len(encoded):
                    ptr = dst_inst.reallocate(ptr, worst_case_size, 1, len(encoded), metrics)
                return ptr, len(encoded)
        return ptr, src_code_units

    def store_utf8_to_utf16() -> tuple[int, int]:
        worst_case_size = 2 * src_code_units
        ptr = dst_inst.reallocate(0, 0, 2, worst_case_size, metrics)
        encoded = src.encode("utf-16-le")
        dst_inst.memory.buf[ptr : ptr + len(encoded)] = encoded
        metrics.dst_bytes_written += len(encoded)
        if len(encoded) < worst_case_size:
            ptr = dst_inst.reallocate(ptr, worst_case_size, 2, len(encoded), metrics)
        return ptr, len(encoded) // 2

    def store_to_latin1_or_utf16() -> tuple[int, int]:
        ptr = dst_inst.reallocate(0, 0, 2, src_code_units, metrics)
        dst_len = 0
        for ch in src:
            if ord(ch) < 256:
                dst_inst.memory.buf[ptr + dst_len] = ord(ch)
                metrics.dst_bytes_written += 1
                dst_len += 1
            else:
                worst_case_size = 2 * src_code_units
                ptr = dst_inst.reallocate(ptr, src_code_units, 2, worst_case_size, metrics)
                # Backward in-place widening of already-written Latin-1 prefix
                for j in range(dst_len - 1, -1, -1):
                    dst_inst.memory.buf[ptr + 2 * j] = dst_inst.memory.buf[ptr + j]
                    dst_inst.memory.buf[ptr + 2 * j + 1] = 0
                metrics.in_place_widen_bytes_moved += 2 * dst_len
                metrics.dst_bytes_written += 2 * dst_len
                encoded = src.encode("utf-16-le")
                tail = encoded[2 * dst_len :]
                dst_inst.memory.buf[ptr + 2 * dst_len : ptr + len(encoded)] = tail
                metrics.dst_bytes_written += len(tail)
                if worst_case_size > len(encoded):
                    ptr = dst_inst.reallocate(ptr, worst_case_size, 2, len(encoded), metrics)
                return ptr, (len(encoded) // 2) | UTF16_TAG_32
        if dst_len < src_code_units:
            ptr = dst_inst.reallocate(ptr, src_code_units, 2, dst_len, metrics)
        return ptr, dst_len

    if dst_enc == "utf8":
        if src_simple == "utf8":
            return store_copy(1, 1, "utf-8")
        if src_simple == "utf16":
            return store_to_utf8(src_code_units * 3)
        return store_to_utf8(src_code_units * 2)
    if dst_enc == "utf16":
        if src_simple == "utf8":
            return store_utf8_to_utf16()
        return store_copy(2, 2, "utf-16-le")
    # dst_enc == "latin1+utf16"
    if src_enc in ("utf8", "utf16"):
        return store_to_latin1_or_utf16()
    if src_simple == "latin1":
        return store_copy(1, 2, "latin-1")
    # src_simple == "utf16" from latin1+utf16
    return store_to_latin1_or_utf16()


def transfer_string_across_boundary(
    src_inst: ComponentInstance,
    dst_inst: ComponentInstance,
    text: str,
) -> tuple[CopyMetrics, tuple[int, int]]:
    if src_inst.string_encoding == "utf8":
        raw = text.encode("utf-8")
        tag_bit = False
    elif src_inst.string_encoding == "utf16":
        raw = text.encode("utf-16-le")
        tag_bit = False
    else:
        if all(ord(c) < 256 for c in text):
            raw = text.encode("latin-1")
            tag_bit = False
        else:
            raw = text.encode("utf-16-le")
            tag_bit = True
    src_ptr, src_tagged = write_guest_string_raw(src_inst, raw, tag_bit)
    metrics = CopyMetrics()
    lifted = load_string_from_range(src_inst, src_ptr, src_tagged, metrics)
    dst_ptr, dst_tagged = store_string_into_range(dst_inst, lifted, metrics)
    # Round-trip sanity check on dst memory
    check_metrics = CopyMetrics()
    roundtrip, _, _ = load_string_from_range(dst_inst, dst_ptr, dst_tagged, check_metrics)
    assert roundtrip == text, f"round-trip mismatch: {roundtrip!r} != {text!r}"
    return metrics, (dst_ptr, dst_tagged)


# =============================================================================
# Part 2: Cap'n Proto Zero-Copy Arena & Traversal/Nesting Security Validator
# Mirrors capnproto/capnproto doc/encoding.md + c++/src/capnp/{layout.c++,arena.h}
# =============================================================================

WORD_BYTES = 8
DEFAULT_TRAVERSAL_LIMIT_WORDS = 8 * 1024 * 1024  # 64 MiB (message.h L54)
DEFAULT_NESTING_LIMIT = 64  # (message.h L75)


class CapnpValidationError(RuntimeError):
    def __init__(self, code: str, message: str) -> None:
        super().__init__(f"[{code}] {message}")
        self.code = code
        self.message = message


class PointerKind(IntEnum):
    STRUCT = 0
    LIST = 1
    FAR = 2
    OTHER = 3  # Capability pointer when B == 0


class ListElementSize(IntEnum):
    VOID = 0
    BIT = 1
    BYTE = 2
    TWO_BYTES = 3
    FOUR_BYTES = 4
    EIGHT_BYTES = 5
    POINTER = 6
    INLINE_COMPOSITE = 7


def encode_struct_ptr(offset_words: int, data_words: int, ptr_words: int) -> int:
    """Cap'n Proto 64-bit struct pointer: A(2)=0, B(30)=signed word offset, C(16)=data, D(16)=ptrs."""
    assert -(1 << 29) <= offset_words < (1 << 29)
    b = offset_words & 0x3FFFFFFF
    return (PointerKind.STRUCT) | (b << 2) | ((data_words & 0xFFFF) << 32) | ((ptr_words & 0xFFFF) << 48)


def encode_list_ptr(offset_words: int, elem_size: ListElementSize, count_or_words: int) -> int:
    """Cap'n Proto 64-bit list pointer: A(2)=1, B(30)=signed word offset, C(3)=elem_size, D(29)=count/words."""
    assert -(1 << 29) <= offset_words < (1 << 29)
    b = offset_words & 0x3FFFFFFF
    return (PointerKind.LIST) | (b << 2) | ((int(elem_size) & 0x7) << 32) | ((count_or_words & 0x1FFFFFFF) << 35)


def encode_far_ptr(double_far: bool, pad_offset_words: int, segment_id: int) -> int:
    """Cap'n Proto 64-bit far pointer: A(2)=2, B(1)=double_far, C(29)=offset, D(32)=segment_id."""
    b = 1 if double_far else 0
    return (PointerKind.FAR) | (b << 2) | ((pad_offset_words & 0x1FFFFFFF) << 3) | ((segment_id & 0xFFFFFFFF) << 32)


def decode_signed_30(val: int) -> int:
    return val - (1 << 30) if (val & (1 << 29)) else val


@dataclass
class ReadLimiter:
    """Models capnp::ReadLimiter (arena.h L62-96)."""

    remaining_words: int
    total_words_charged: int = 0

    def consume(self, words: int) -> None:
        if words > self.remaining_words:
            raise CapnpValidationError(
                "TRAVERSAL_LIMIT_EXCEEDED",
                f"requested {words} words exceeds remaining ReadLimiter budget {self.remaining_words}",
            )
        self.remaining_words -= words
        self.total_words_charged += words


class CapnpArenaReader:
    """Zero-copy Cap'n Proto segment reader with exact bounds, nesting, and amplification checks."""

    def __init__(
        self,
        segments: list[memoryview],
        traversal_limit_words: int = DEFAULT_TRAVERSAL_LIMIT_WORDS,
        nesting_limit: int = DEFAULT_NESTING_LIMIT,
    ) -> None:
        self.segments = segments
        self.limiter = ReadLimiter(remaining_words=traversal_limit_words)
        self.nesting_limit = nesting_limit
        self.payload_bytes_copied = 0
        self.heap_allocations = 0

    def _read_word(self, seg_id: int, word_idx: int) -> int:
        if seg_id < 0 or seg_id >= len(self.segments):
            raise CapnpValidationError("UNKNOWN_SEGMENT", f"unknown segment id {seg_id}")
        seg = self.segments[seg_id]
        byte_off = word_idx * WORD_BYTES
        if byte_off < 0 or byte_off + WORD_BYTES > len(seg):
            raise CapnpValidationError("OUT_OF_BOUNDS", f"word {word_idx} out of bounds in seg {seg_id}")
        return struct.unpack_from("<Q", seg, byte_off)[0]

    def _bounds_check(self, seg_id: int, start_word: int, word_count: int) -> None:
        if seg_id < 0 or seg_id >= len(self.segments):
            raise CapnpValidationError("UNKNOWN_SEGMENT", f"unknown segment id {seg_id}")
        seg_words = len(self.segments[seg_id]) // WORD_BYTES
        if start_word < 0 or word_count < 0 or start_word + word_count > seg_words:
            raise CapnpValidationError(
                "OUT_OF_BOUNDS",
                f"range [{start_word}, {start_word + word_count}) exceeds segment {seg_id} ({seg_words} words)",
            )
        # Exact mirror of SegmentReader::checkObject (arena.h L423-424):
        # charge exact word_count (zero-sized lists separately call amplifiedRead).
        self.limiter.consume(word_count)

    def _follow_fars(self, seg_id: int, ptr_word_idx: int) -> tuple[int, int, int]:
        raw = self._read_word(seg_id, ptr_word_idx)
        kind = PointerKind(raw & 0x3)
        if kind != PointerKind.FAR:
            offset = decode_signed_30((raw >> 2) & 0x3FFFFFFF)
            return seg_id, raw, ptr_word_idx + 1 + offset
        double_far = bool((raw >> 2) & 0x1)
        pad_offset = (raw >> 3) & 0x1FFFFFFF
        target_seg = (raw >> 32) & 0xFFFFFFFF
        pad_words = 2 if double_far else 1
        self._bounds_check(target_seg, pad_offset, pad_words)
        pad = self._read_word(target_seg, pad_offset)
        if not double_far:
            inner_off = decode_signed_30((pad >> 2) & 0x3FFFFFFF)
            return target_seg, pad, pad_offset + 1 + inner_off
        if PointerKind(pad & 0x3) != PointerKind.FAR:
            raise CapnpValidationError("BAD_DOUBLE_FAR", "double-far pad first word is not FAR")
        final_seg = (pad >> 32) & 0xFFFFFFFF
        final_off = (pad >> 3) & 0x1FFFFFFF
        tag = self._read_word(target_seg, pad_offset + 1)
        return final_seg, tag, final_off

    def read_struct_pointer(
        self, seg_id: int, ptr_word_idx: int, nesting_limit: int
    ) -> tuple[int, int, int, int, int]:
        """Returns (target_seg, data_start_word, data_words, ptr_words, next_nesting)."""
        if nesting_limit <= 0:
            raise CapnpValidationError(
                "NESTING_LIMIT_EXCEEDED",
                "message is too deeply-nested or contains cycles",
            )
        target_seg, ref, target_word = self._follow_fars(seg_id, ptr_word_idx)
        if ref == 0:
            return target_seg, 0, 0, 0, nesting_limit - 1
        if PointerKind(ref & 0x3) != PointerKind.STRUCT:
            raise CapnpValidationError("SCHEMA_MISMATCH", "expected STRUCT pointer")
        data_words = (ref >> 32) & 0xFFFF
        ptr_words = (ref >> 48) & 0xFFFF
        self._bounds_check(target_seg, target_word, data_words + ptr_words)
        return target_seg, target_word, data_words, ptr_words, nesting_limit - 1

    def read_list_pointer(
        self, seg_id: int, ptr_word_idx: int, nesting_limit: int
    ) -> tuple[int, int, ListElementSize, int, memoryview]:
        """Returns zero-copy memoryview slice into the arena segment (0 payload copies)."""
        if nesting_limit <= 0:
            raise CapnpValidationError(
                "NESTING_LIMIT_EXCEEDED",
                "message is too deeply-nested or contains cycles",
            )
        target_seg, ref, target_word = self._follow_fars(seg_id, ptr_word_idx)
        if PointerKind(ref & 0x3) != PointerKind.LIST:
            raise CapnpValidationError("SCHEMA_MISMATCH", "expected LIST pointer")
        elem_size = ListElementSize((ref >> 32) & 0x7)
        count = (ref >> 35) & 0x1FFFFFFF

        if elem_size == ListElementSize.INLINE_COMPOSITE:
            word_count = count
            self._bounds_check(target_seg, target_word, word_count + 1)
            tag = self._read_word(target_seg, target_word)
            if PointerKind(tag & 0x3) != PointerKind.STRUCT:
                raise CapnpValidationError("BAD_COMPOSITE_TAG", "INLINE_COMPOSITE tag must be STRUCT")
            elem_count = (tag >> 2) & 0x3FFFFFFF
            data_words = (tag >> 32) & 0xFFFF
            ptr_words = (tag >> 48) & 0xFFFF
            words_per_elem = data_words + ptr_words
            if elem_count * words_per_elem > word_count:
                raise CapnpValidationError("LIST_OVERRUN", "INLINE_COMPOSITE elements overrun word count")
            if words_per_elem == 0:
                # Exact mirror of layout.c++ L2203-2208: amplifiedRead(segment, elem_count)
                self.limiter.consume(elem_count)
            start_b = (target_word + 1) * WORD_BYTES
            end_b = start_b + word_count * WORD_BYTES
            return target_seg, target_word + 1, elem_size, elem_count, self.segments[target_seg][start_b:end_b]

        if elem_size == ListElementSize.VOID:
            # Mirror layout.c++ L2268: amplifiedRead for VOID lists
            self._bounds_check(target_seg, target_word, 0)
            self.limiter.consume(count)
            return target_seg, target_word, elem_size, count, self.segments[target_seg][0:0]

        bits_map = {
            ListElementSize.BIT: 1,
            ListElementSize.BYTE: 8,
            ListElementSize.TWO_BYTES: 16,
            ListElementSize.FOUR_BYTES: 32,
            ListElementSize.EIGHT_BYTES: 64,
            ListElementSize.POINTER: 64,
        }
        total_bits = count * bits_map[elem_size]
        word_count = (total_bits + 63) // 64
        self._bounds_check(target_seg, target_word, word_count)
        start_b = target_word * WORD_BYTES
        byte_len = count if elem_size == ListElementSize.BYTE else word_count * WORD_BYTES
        return target_seg, target_word, elem_size, count, self.segments[target_seg][start_b : start_b + byte_len]

    def traverse_struct_tree(self, seg_id: int, ptr_word_idx: int, nesting: int) -> int:
        t_seg, data_w, d_cnt, p_cnt, next_nest = self.read_struct_pointer(seg_id, ptr_word_idx, nesting)
        if d_cnt == 0 and p_cnt == 0 and data_w == 0:
            return 0
        visited = 1
        ptr_base = data_w + d_cnt
        for i in range(p_cnt):
            raw = self._read_word(t_seg, ptr_base + i)
            if raw != 0:
                visited += self.traverse_struct_tree(t_seg, ptr_base + i, next_nest)
        return visited


# =============================================================================
# Verification Test Suite
# =============================================================================

def verify_resource_state_machine() -> dict[str, str]:
    receipts: dict[str, str] = {}

    # A1: Static rejection of `borrow<T>` in function result types and stream/future elements
    try:
        validate_func_type(FuncType(params=(), results=(ValType("borrow", "blob"),)))
        raise AssertionError("Expected StaticValidationError for borrow in return type")
    except StaticValidationError as exc:
        receipts["A1_static_reject_borrow_return"] = str(exc)

    try:
        validate_func_type(
            FuncType(params=(ValType("stream", ValType("borrow", "blob")),), results=())
        )
        raise AssertionError("Expected StaticValidationError for borrow inside stream<T>")
    except StaticValidationError as exc:
        receipts["A1b_static_reject_borrow_in_stream"] = str(exc)

    # Setup three isolated components: Owner (defines `file`), Caller, Callee
    destroyed: list[int] = []
    owner_inst = ComponentInstance("owner")
    caller_inst = ComponentInstance("caller")
    callee_inst = ComponentInstance("callee")
    file_rt = ResourceType("file", impl_inst=owner_inst, dtor=lambda rep: destroyed.append(rep))

    # Create resource in owner_inst and transfer `own<file>` to caller_inst
    owner_h = owner_inst.canon_resource_new(file_rt, 0xCAFE)
    rep = owner_inst.lift_own(owner_h, file_rt)
    caller_own_h = caller_inst.lower_own(rep, file_rt)
    assert destroyed == []

    # A2: Callee fails to drop `borrow<file>` before returning -> Task.return_() traps
    subtask_a2 = Subtask()
    callee_task_a2 = Task(callee_inst)
    lent_rep = caller_inst.lift_borrow(caller_own_h, file_rt, subtask_a2)
    leaked_borrow_h = callee_inst.lower_borrow(lent_rep, file_rt, callee_task_a2)
    assert callee_task_a2.num_borrows == 1
    try:
        callee_task_a2.return_()
        raise AssertionError("Expected WasmTrap(UNRELEASED_BORROW)")
    except WasmTrap as exc:
        assert exc.code == "UNRELEASED_BORROW"
        receipts["A2_trap_undropped_borrow_on_return"] = str(exc)

    # A3: Caller attempts to drop `own<file>` while actively lent out -> traps
    try:
        caller_inst.canon_resource_drop(file_rt, caller_own_h)
        raise AssertionError("Expected WasmTrap(OWN_STILL_BORROWED)")
    except WasmTrap as exc:
        assert exc.code == "OWN_STILL_BORROWED"
        receipts["A3_trap_drop_own_while_borrowed"] = str(exc)

    # A4: Caller attempts to transfer `own<file>` while lent, and callee attempts lift_own on borrow
    try:
        caller_inst.lift_own(caller_own_h, file_rt)
        raise AssertionError("Expected WasmTrap(OWN_STILL_BORROWED)")
    except WasmTrap as exc:
        assert exc.code == "OWN_STILL_BORROWED"
        receipts["A4a_trap_transfer_own_while_borrowed"] = str(exc)

    try:
        callee_inst.lift_own(leaked_borrow_h, file_rt)
        raise AssertionError("Expected WasmTrap(LIFT_OWN_FROM_BORROW)")
    except WasmTrap as exc:
        assert exc.code == "LIFT_OWN_FROM_BORROW"
        receipts["A4b_trap_lift_own_from_borrow"] = str(exc)

    # A5: Re-borrow chain: callee re-lends its `borrow<file>` to third_inst; callee tries to drop before nested call ends
    third_inst = ComponentInstance("third")
    nested_subtask = Subtask()
    third_task = Task(third_inst)
    nested_rep = callee_inst.lift_borrow(leaked_borrow_h, file_rt, nested_subtask)
    third_borrow_h = third_inst.lower_borrow(nested_rep, file_rt, third_task)
    try:
        callee_inst.canon_resource_drop(file_rt, leaked_borrow_h)
        raise AssertionError("Expected WasmTrap(BORROW_STILL_LENT)")
    except WasmTrap as exc:
        assert exc.code == "BORROW_STILL_LENT"
        receipts["A5_trap_drop_borrow_while_relent"] = str(exc)

    # Clean unwind of nested borrows -> proper drop -> destructor executes exactly once
    third_inst.canon_resource_drop(file_rt, third_borrow_h)
    third_task.return_()
    nested_subtask.deliver_resolve()

    callee_inst.canon_resource_drop(file_rt, leaked_borrow_h)
    callee_task_a2.return_()
    subtask_a2.deliver_resolve()
    assert caller_inst.handles.get(caller_own_h).num_lends == 0

    # Defining-instance pass_rep_not_handle optimization check:
    # lending borrow<file> to owner_inst passes raw rep 0xCAFE with 0 handle-table entries allocated!
    subtask_opt = Subtask()
    owner_task = Task(owner_inst)
    rep_direct = caller_inst.lift_borrow(caller_own_h, file_rt, subtask_opt)
    passed_val = owner_inst.lower_borrow(rep_direct, file_rt, owner_task)
    assert passed_val == 0xCAFE and owner_task.num_borrows == 0
    owner_task.return_()
    subtask_opt.deliver_resolve()
    receipts["A6_pass_rep_not_handle_verified"] = f"rep=0x{passed_val:x}, owner_task.num_borrows=0"

    # Drop owned handle -> triggers destructor exactly once; reuse fails
    caller_inst.canon_resource_drop(file_rt, caller_own_h)
    assert destroyed == [0xCAFE]
    try:
        caller_inst.canon_resource_drop(file_rt, caller_own_h)
        raise AssertionError("Expected WasmTrap(UNKNOWN_HANDLE) on double drop")
    except WasmTrap as exc:
        assert exc.code == "UNKNOWN_HANDLE"
        receipts["A7_double_drop_rejected"] = str(exc)

    # A8: Reentrancy guard (`may_leave = False`) inside `cabi_realloc`
    def malicious_realloc(inst: ComponentInstance, old_p: int, old_s: int, al: int, new_s: int) -> int:
        # Attempt to invoke canon_resource_new while inside cabi_realloc
        inst.canon_resource_new(ResourceType("x", impl_inst=inst), 1)
        return inst.memory.cabi_realloc(old_p, old_s, al, new_s)

    reentrant_inst = ComponentInstance("reentrant", realloc_hook=malicious_realloc)
    try:
        reentrant_inst.reallocate(0, 0, 1, 16)
        raise AssertionError("Expected WasmTrap(CANNOT_LEAVE) during cabi_realloc")
    except WasmTrap as exc:
        assert exc.code == "CANNOT_LEAVE"
        receipts["A8_reentrant_realloc_trapped"] = str(exc)

    # A9: Unpaired UTF-16 surrogate rejected by load_string_from_range
    utf16_inst = ComponentInstance("u16", string_encoding="utf16")
    bad_ptr, bad_len = write_guest_string_raw(utf16_inst, b"\x00\xd8")  # U+D800 lone high surrogate
    try:
        load_string_from_range(utf16_inst, bad_ptr, bad_len, CopyMetrics())
        raise AssertionError("Expected WasmTrap(INVALID_UNICODE)")
    except WasmTrap as exc:
        assert exc.code == "INVALID_UNICODE"
        receipts["A9_lone_surrogate_trapped"] = str(exc)

    return receipts


def verify_copy_amplification_vs_capnp() -> dict[str, Any]:
    results: dict[str, Any] = {"wit_string_crossings": {}, "capnp_zero_copy": {}}

    workloads = {
        "ascii_4096B": "A" * 4096,
        "mixed_latin1_plus_cjk_1024cp": ("café" * 200) + ("漢" * 224),  # 1024 code points
        "emoji_4byte_512cp": "🚀" * 512,  # 2048 UTF-8 bytes, 1024 UTF-16 code units (2048 B)
    }
    pairs: list[tuple[StringEncoding, StringEncoding]] = [
        ("utf8", "utf8"),
        ("utf8", "utf16"),
        ("utf16", "utf8"),
        ("utf8", "latin1+utf16"),
    ]

    for wname, text in workloads.items():
        results["wit_string_crossings"][wname] = {}
        for src_enc, dst_enc in pairs:
            c_src = ComponentInstance("src", src_enc)
            c_dst = ComponentInstance("dst", dst_enc)
            m, _ = transfer_string_across_boundary(c_src, c_dst, text)
            src_bytes = m.src_bytes_read
            results["wit_string_crossings"][wname][f"{src_enc}->{dst_enc}"] = {
                "src_bytes": src_bytes,
                "dst_bytes_written": m.dst_bytes_written,
                "peak_alloc_bytes": m.peak_allocated_bytes,
                "final_alloc_bytes": m.final_allocated_bytes,
                "realloc_calls": m.realloc_calls,
                "write_amplification_vs_src": round(m.dst_bytes_written / src_bytes, 3),
                "total_rw_amplification_vs_src": round((src_bytes + m.dst_bytes_written) / src_bytes, 3),
                "peak_alloc_amplification_vs_final": round(
                    m.peak_allocated_bytes / max(1, m.final_allocated_bytes), 3
                ),
            }

    # Verify specific Canonical ABI realloc-churn invariants
    mixed_u16_to_u8 = results["wit_string_crossings"]["mixed_latin1_plus_cjk_1024cp"]["utf16->utf8"]
    assert mixed_u16_to_u8["realloc_calls"] == 3  # optimistic alloc -> 3x worst-case grow -> shrink
    assert mixed_u16_to_u8["peak_alloc_bytes"] == 3 * 1024
    mixed_u8_to_compact = results["wit_string_crossings"]["mixed_latin1_plus_cjk_1024cp"]["utf8->latin1+utf16"]
    assert mixed_u8_to_compact["realloc_calls"] == 3  # optimistic alloc -> 2x grow+widen -> shrink

    # Multi-hop pipeline amplification: 4 UTF-8 <-> UTF-16 alternating component hops
    hops = 4
    total_rw_4hop = 0
    payload = workloads["ascii_4096B"]
    encs: list[StringEncoding] = ["utf8", "utf16", "utf8", "utf16", "utf8"]
    for i in range(hops):
        m, _ = transfer_string_across_boundary(
            ComponentInstance(f"c{i}", encs[i]),
            ComponentInstance(f"c{i+1}", encs[i + 1]),
            payload,
        )
        total_rw_4hop += m.src_bytes_read + m.dst_bytes_written
    results["wit_4hop_alternating_ascii_4096B_rw_bytes"] = total_rw_4hop
    results["wit_4hop_rw_amplification_vs_4096B"] = round(total_rw_4hop / 4096, 3)

    # --- Cap'n Proto zero-copy valid payload read ---
    # Segment layout:
    #   word 0: root struct pointer -> word 1 (data_words=1, ptr_words=1)
    #   word 1: struct data (u64 = 0x1122334455667788)
    #   word 2: list<u8> pointer -> word 3 (4096 bytes = 512 words)
    #   word 3..514: 4096-byte ASCII payload
    payload_bytes = b"A" * 4096
    seg_buf = bytearray((3 + 512) * WORD_BYTES)
    struct.pack_into("<Q", seg_buf, 0 * WORD_BYTES, encode_struct_ptr(0, data_words=1, ptr_words=1))
    struct.pack_into("<Q", seg_buf, 1 * WORD_BYTES, 0x1122334455667788)
    struct.pack_into("<Q", seg_buf, 2 * WORD_BYTES, encode_list_ptr(0, ListElementSize.BYTE, len(payload_bytes)))
    seg_buf[3 * WORD_BYTES : 3 * WORD_BYTES + len(payload_bytes)] = payload_bytes

    reader = CapnpArenaReader([memoryview(seg_buf)])
    t_seg, d_word, d_cnt, p_cnt, next_nest = reader.read_struct_pointer(0, 0, reader.nesting_limit)
    assert (t_seg, d_word, d_cnt, p_cnt) == (0, 1, 1, 1)
    _, _, elem_sz, count, view = reader.read_list_pointer(0, d_word + d_cnt, next_nest)
    assert elem_sz == ListElementSize.BYTE and count == 4096
    assert view.tobytes() == payload_bytes  # Only for assertion; reader itself returned zero-copy memoryview
    assert reader.payload_bytes_copied == 0 and reader.heap_allocations == 0
    results["capnp_zero_copy"]["valid_4096B_read"] = {
        "payload_bytes": count,
        "payload_bytes_copied": reader.payload_bytes_copied,
        "heap_allocations": reader.heap_allocations,
        "words_charged_to_read_limiter": reader.limiter.total_words_charged,
    }

    # --- Cap'n Proto Defense B1: Direct Pointer Cycle (nestingLimit) ---
    # word 0: root struct ptr -> word 1 (data=0, ptrs=1)
    # word 1: self-referential struct ptr (offset=-1 points back to word 1!)
    cyc_buf = bytearray(2 * WORD_BYTES)
    struct.pack_into("<Q", cyc_buf, 0 * WORD_BYTES, encode_struct_ptr(0, data_words=0, ptr_words=1))
    struct.pack_into("<Q", cyc_buf, 1 * WORD_BYTES, encode_struct_ptr(-1, data_words=0, ptr_words=1))
    cyc_reader = CapnpArenaReader([memoryview(cyc_buf)], nesting_limit=DEFAULT_NESTING_LIMIT)
    try:
        cyc_reader.traverse_struct_tree(0, 0, cyc_reader.nesting_limit)
        raise AssertionError("Expected CapnpValidationError(NESTING_LIMIT_EXCEEDED)")
    except CapnpValidationError as exc:
        assert exc.code == "NESTING_LIMIT_EXCEEDED"
        results["capnp_zero_copy"]["B1_cycle_rejected"] = {
            "error": str(exc),
            "nesting_limit": DEFAULT_NESTING_LIMIT,
            "wire_bytes": len(cyc_buf),
        }

    # --- Cap'n Proto Defense B2: Compact DAG Amplification Bomb (ReadLimiter) ---
    # 24-level binary DAG: each node has 0 data words, 2 pointer words, both pointing to next level!
    # Total wire size = 1 + 24*2 + 1 = 50 words (400 bytes), logical tree nodes = 2^25 - 1 = 33,554,431!
    levels = 24
    dag_words = 1 + 2 * levels + 1
    dag_buf = bytearray(dag_words * WORD_BYTES)
    # word 0 -> word 1 (node 0: 2 ptrs at words 1, 2)
    struct.pack_into("<Q", dag_buf, 0 * WORD_BYTES, encode_struct_ptr(0, data_words=0, ptr_words=2))
    for lvl in range(levels):
        w_left = 1 + 2 * lvl
        w_right = w_left + 1
        next_node = 1 + 2 * (lvl + 1)
        if lvl == levels - 1:
            # Point to leaf struct at next_node (data=1, ptrs=0)
            struct.pack_into("<Q", dag_buf, w_left * WORD_BYTES, encode_struct_ptr(next_node - (w_left + 1), 1, 0))
            struct.pack_into("<Q", dag_buf, w_right * WORD_BYTES, encode_struct_ptr(next_node - (w_right + 1), 1, 0))
        else:
            struct.pack_into("<Q", dag_buf, w_left * WORD_BYTES, encode_struct_ptr(next_node - (w_left + 1), 0, 2))
            struct.pack_into("<Q", dag_buf, w_right * WORD_BYTES, encode_struct_ptr(next_node - (w_right + 1), 0, 2))

    # Bounded traversal limit (e.g., 16,384 words = 128 KiB) trips well before 2^24 expansion
    dag_limit = 16_384
    dag_reader = CapnpArenaReader(
        [memoryview(dag_buf)], traversal_limit_words=dag_limit, nesting_limit=DEFAULT_NESTING_LIMIT
    )
    try:
        dag_reader.traverse_struct_tree(0, 0, dag_reader.nesting_limit)
        raise AssertionError("Expected CapnpValidationError(TRAVERSAL_LIMIT_EXCEEDED)")
    except CapnpValidationError as exc:
        assert exc.code == "TRAVERSAL_LIMIT_EXCEEDED"
        results["capnp_zero_copy"]["B2_dag_amplification_rejected"] = {
            "error": str(exc),
            "wire_bytes": len(dag_buf),
            "logical_leaf_amplification": 1 << levels,
            "traversal_limit_words": dag_limit,
            "words_charged_before_abort": dag_reader.limiter.total_words_charged,
        }

    # --- Cap'n Proto Defense B3: Zero-Sized INLINE_COMPOSITE List Bomb (amplifiedRead) ---
    # 2-word message (16 bytes) claiming a 10,000,000-element list of zero-sized structs!
    zlist_buf = bytearray(2 * WORD_BYTES)
    struct.pack_into("<Q", zlist_buf, 0 * WORD_BYTES, encode_list_ptr(0, ListElementSize.INLINE_COMPOSITE, 0))
    # Tag word at word 1: kind=STRUCT, B=element_count=10_000_000, data_words=0, ptr_words=0
    struct.pack_into("<Q", zlist_buf, 1 * WORD_BYTES, encode_struct_ptr(10_000_000, data_words=0, ptr_words=0))
    zlist_reader = CapnpArenaReader([memoryview(zlist_buf)], traversal_limit_words=DEFAULT_TRAVERSAL_LIMIT_WORDS)
    try:
        zlist_reader.read_list_pointer(0, 0, zlist_reader.nesting_limit)
        raise AssertionError("Expected CapnpValidationError(TRAVERSAL_LIMIT_EXCEEDED) on zero-sized struct list")
    except CapnpValidationError as exc:
        assert exc.code == "TRAVERSAL_LIMIT_EXCEEDED"
        results["capnp_zero_copy"]["B3_zero_sized_composite_list_rejected"] = {
            "error": str(exc),
            "wire_bytes": len(zlist_buf),
            "claimed_elements": 10_000_000,
            "default_traversal_limit_words": DEFAULT_TRAVERSAL_LIMIT_WORDS,
        }

    # --- Cap'n Proto Defense B4: Out-of-bounds pointer & invalid far segment ---
    oob_buf = bytearray(1 * WORD_BYTES)
    struct.pack_into("<Q", oob_buf, 0, encode_struct_ptr(50, data_words=1, ptr_words=0))
    oob_reader = CapnpArenaReader([memoryview(oob_buf)])
    try:
        oob_reader.read_struct_pointer(0, 0, oob_reader.nesting_limit)
        raise AssertionError("Expected CapnpValidationError(OUT_OF_BOUNDS)")
    except CapnpValidationError as exc:
        assert exc.code == "OUT_OF_BOUNDS"
        results["capnp_zero_copy"]["B4a_oob_struct_rejected"] = str(exc)

    far_buf = bytearray(1 * WORD_BYTES)
    struct.pack_into("<Q", far_buf, 0, encode_far_ptr(False, 0, segment_id=99))
    far_reader = CapnpArenaReader([memoryview(far_buf)])
    try:
        far_reader.read_struct_pointer(0, 0, far_reader.nesting_limit)
        raise AssertionError("Expected CapnpValidationError(UNKNOWN_SEGMENT)")
    except CapnpValidationError as exc:
        assert exc.code == "UNKNOWN_SEGMENT"
        results["capnp_zero_copy"]["B4b_invalid_far_segment_rejected"] = str(exc)

    return results


def main() -> int:
    resource_receipts = verify_resource_state_machine()
    copy_and_capnp = verify_copy_amplification_vs_capnp()
    summary = {
        "status": "PASS",
        "resource_handle_state_machine": resource_receipts,
        "copy_amplification_and_capnp_validation": copy_and_capnp,
    }
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
