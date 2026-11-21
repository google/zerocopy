#!/usr/bin/env python3
"""Toy model of the "retained handle" scenario under several enforcement disciplines.

This is a TOY MODEL. It does not execute MSWasm, a CHERI machine, a Cerise
capability machine, RichWasm, or any upstream artifact. It encodes, in a few
lines each, the rule that the cited semantics or implementations use to decide
what happens when an untrusted context keeps a handle to storage that the
component releases, and then uses the handle after the storage is reused.

Scenario (identical for every discipline):
  1. component allocates block A (4 cells) and writes secret 7 into A[0];
  2. component passes a handle h to the context; the context keeps a copy;
  3. component releases A;
  4. component allocates block B (4 cells); the allocator reuses A's cells;
     component writes 42 into B[0];
  5. context loads through its retained copy of h.

Fates: EXCLUDED (the copy cannot exist or cannot be used, rejected statically),
FAULTS (use traps dynamically), REVOKED (handle invalidated before reuse, so the
use traps), PERMITTED (the use succeeds and reads the reused cell).

Usage: python3 retained_handle_toy.py [--trials N] [--keybits K] [--seed S]
Deterministic for a fixed seed. Pure standard library.
"""
import argparse
import random


class Trap(Exception):
    pass


class Reject(Exception):
    """Static rejection (type/linearity checker)."""


def plain_linear_memory(_rng):
    """Plain Wasm-style linear memory: handles are integers, no checks."""
    mem = [0] * 8
    a = 0
    mem[a] = 7
    h = a  # context copies the integer
    # release: nothing happens to h; allocator reuses offset 0
    b = 0
    mem[b] = 42
    return "PERMITTED", mem[h]


def mswasm_unique_ids(_rng):
    """Formal MSWasm rule: handle carries segment id; load requires id in A.allocated;
    ids are never reused (H-Load premise nid in allocated)."""
    allocated = {}
    next_id = 1
    seg_a = (0, next_id); next_id += 1
    allocated[seg_a[1]] = [7, 0, 0, 0]
    h = (seg_a[0], 0, 4, True, seg_a[1])  # <base, offset, bound, valid, id>
    del allocated[seg_a[1]]  # segfree
    seg_b = (0, next_id); next_id += 1  # same base reused, fresh id
    allocated[seg_b[1]] = [42, 0, 0, 0]
    base, off, bound, valid, nid = h
    if not valid or nid not in allocated or not (0 <= off < bound):
        raise Trap("H-Load premise fails: segment id not allocated")
    return "PERMITTED", allocated[nid][off]


def random_key_segments(rng, keybits):
    """Random-key segment table (key drawn at allocation, removed at free, membership
    checked at use). With a K-bit key space a later allocation can redraw the freed
    key, which revalidates the stale handle."""
    table = {}
    ka = rng.randrange(1, 2 ** keybits)
    table[ka] = [7, 0, 0, 0]
    h = (ka, 0)
    del table[ka]
    kb = rng.randrange(1, 2 ** keybits)
    while kb in table:
        kb = rng.randrange(1, 2 ** keybits)
    table[kb] = [42, 0, 0, 0]
    key, off = h
    if key not in table:
        raise Trap("key not present")
    return "PERMITTED", table[key][off]


def linear_capability(_rng):
    """Linear capability discipline (hardware-enforced non-duplication or a linear
    type system): passing h moves it; a second live copy cannot be made."""
    live = {"h": "component"}

    def move(cap, to):
        live[cap] = to

    def duplicate(cap):
        raise Reject("linear capability cannot be duplicated (move-only)")

    move("h", "context")
    duplicate("h")  # the context's attempt to keep a copy while returning it
    return "PERMITTED", None


def typed_ptr_cap_split(_rng):
    """L3/RichWasm-style split: pointer is copyable, capability is linear and is
    consumed by free; a later load needs a capability for the location."""
    caps = {"rho_a": True}
    ptr = "rho_a"            # copyable pointer kept by the context
    caps.pop("rho_a")        # free consumes Cap rho_a
    if ptr not in caps:
        raise Reject("load needs Cap rho_a; none in scope after free")
    return "PERMITTED", None


def uninitialized_cap_stack(_rng):
    """Uninitialized (U) stack capability: reads allowed only below the cursor a;
    stale frame contents above a are unreadable until overwritten via StoreU."""
    stack = [0] * 8
    stack[3] = 7             # callee's old frame data at address 3
    cursor = 2               # callee returned; caller hands a U-cap with a = 2
    addr = 3                 # context tries to read the stale cell
    if not (0 <= addr < cursor):
        raise Trap("LoadU requires b <= a' < a")
    return "PERMITTED", stack[addr]


def sweeping_revocation(_rng):
    """Quarantine + sweep (CHERIvoke-style): free paints the region in a shadow map and
    quarantines it; before reuse a sweep clears tags of every capability whose base is
    painted; a use after the sweep traps on the cleared tag."""
    mem = [0] * 8
    tags = {}
    mem[0] = 7
    h_slot = 7               # context stores its copy in memory slot 7
    tags[h_slot] = (0, 4)    # tagged capability <base 0, len 4>
    shadow = set(range(0, 4))  # free(A): paint + quarantine
    # sweep before reuse: clear tag of any capability whose base is painted
    for slot, (base, _ln) in list(tags.items()):
        if base in shadow:
            del tags[slot]
    shadow.clear()           # quarantine released, region reusable
    mem[0] = 42              # B reuses offset 0
    if h_slot not in tags:
        raise Trap("capability tag cleared by sweep")
    return "PERMITTED", mem[tags[h_slot][0]]


def run(fn, *args):
    try:
        fate, val = fn(*args)
        return fate, val
    except Trap as t:
        return "FAULTS/REVOKED", str(t)
    except Reject as r:
        return "EXCLUDED", str(r)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--trials", type=int, default=100000)
    ap.add_argument("--keybits", type=int, default=8)
    ap.add_argument("--seed", type=int, default=1)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    rows = [
        ("plain linear memory (integer handle)", plain_linear_memory, (rng,)),
        ("unique segment ids (formal MSWasm rule)", mswasm_unique_ids, (rng,)),
        ("linear capability (move-only)", linear_capability, (rng,)),
        ("pointer/capability split (L3/RichWasm-style)", typed_ptr_cap_split, (rng,)),
        ("uninitialized stack capability", uninitialized_cap_stack, (rng,)),
        ("quarantine + sweeping revocation", sweeping_revocation, (rng,)),
    ]
    for name, fn, a in rows:
        fate, detail = run(fn, *a)
        print(f"{name:48s} {fate:15s} {detail}")
    permitted = 0
    for _ in range(args.trials):
        fate, _d = run(random_key_segments, rng, args.keybits)
        if fate == "PERMITTED":
            permitted += 1
    space = 2 ** args.keybits - 1
    print(f"random {args.keybits}-bit segment keys: {permitted}/{args.trials} trials PERMITTED "
          f"(expected about 1/{space} = {1/space:.6f}; observed {permitted/args.trials:.6f})")


if __name__ == "__main__":
    main()
