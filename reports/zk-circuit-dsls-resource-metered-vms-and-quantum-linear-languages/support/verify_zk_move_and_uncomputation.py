#!/usr/bin/env python3
r"""Standalone multi-paradigm verification probe for conservation-law languages.

Verifies three core semantic properties using only the Python 3.10+ standard library:
  1. Zero-Knowledge R1CS / F_p under-constrained circuit detection (Picus/Ecne-style
     uniqueness propagation + relational witness-forgery search over finite fields):
       - IsZero missing `in * out === 0` vs sound `circomlib::IsZero` (weak vs strong determinism)
       - Num2Bits missing booleanity `b*(b-1)===0` vs sound `Num2Bits` vs field-aliasing
         `Num2Bits(k)` with 2^k > p (and `AliasCheck` repair)
       - Dark Forest v0.3 `LessThan` missing input range-check modular wraparound exploit
  2. Move-style bytecode abstract interpreter enforcing:
       - Struct field ability requirements (`copy`, `drop`, `store`, `key`)
       - Control-flow-sensitive 3-point local-availability lattice (`Unavailable`,
         `MaybeAvailable`, `Available`) preventing duplication, silent drop, and branch leaks
       - Borrow-graph reference safety (`MOVELOC_EXISTS_BORROW_ERROR`,
         `WRITEREF_EXISTS_BORROW_ERROR`, `READREF_EXISTS_MUTABLE_BORROW_ERROR`)
       - Zero-ability hot-potato receipts and gas-metered atomic rollback conservation
  3. Silq-style quantum linear type/annotation checker (`!`, `const`, `qfree`, `mfree`, `lifted`)
     and exact statevector + reduced-density-matrix simulator demonstrating:
       - Static rejection of `useConsumed`, `discard`, `nonQfree`, `nonConst`, `condMeas`
       - Destruction of Hadamard interference (`P(0) = 0.5`, purity `0.5`) and 2-qubit Grover
         amplification (`P(11) = 0.625`, purity `0.625`) when ancilla uncomputation is omitted
       - Exact restoration of pure disentangled interference (`P(0) = 1.0`, `P(11) = 1.0`,
         purity `1.0`) under `qfree`/`const` automatic Bennett uncomputation (`U^\dagger`)
       - SQIR-style syntactic gate inversion soundness `U(invert(C)) == U(C)^\dagger`.
"""

from __future__ import annotations

import cmath
import enum
import itertools
import json
import math
from dataclasses import dataclass, field
from typing import Any


# =============================================================================
# PART 1: R1CS / F_p Under-Constrained Circuit & Uniqueness Verifier
# =============================================================================

@dataclass(frozen=True)
class LinearComb:
    """Linear combination over F_p mapping wire name (or '1' for constant) -> coeff."""
    terms: dict[str, int]

    def eval(self, env: dict[str, int], p: int) -> int:
        acc = 0
        for name, coeff in self.terms.items():
            val = 1 if name == "1" else env[name]
            acc = (acc + coeff * val) % p
        return acc


@dataclass(frozen=True)
class R1CSConstraint:
    """Rank-1 constraint A(w) * B(w) = C(w) (mod p)."""
    a: LinearComb
    b: LinearComb
    c: LinearComb
    label: str = ""

    def satisfied(self, env: dict[str, int], p: int) -> bool:
        return (self.a.eval(env, p) * self.b.eval(env, p)) % p == self.c.eval(env, p) % p


@dataclass
class R1CSCircuit:
    name: str
    prime: int
    inputs: tuple[str, ...]
    outputs: tuple[str, ...]
    intermediates: tuple[str, ...]
    constraints: list[R1CSConstraint]

    @property
    def all_wires(self) -> tuple[str, ...]:
        return self.inputs + self.intermediates + self.outputs

    def is_satisfied(self, env: dict[str, int]) -> bool:
        return all(c.satisfied(env, self.prime) for c in self.constraints)


def picus_propagate_uniqueness(circuit: R1CSCircuit) -> tuple[set[str], set[str]]:
    """Lightweight Picus/Ecne-style uniqueness propagation (Linear, Binary01, Basis2).

    Enforces Picus `basis2-lemma.rkt` aliasing precondition: basis length <= floor(log2(p)).
    Returns (known_unique_wires, binary01_wires).
    """
    p = circuit.prime
    known: set[str] = set(circuit.inputs)
    binary01: set[str] = set()
    max_safe_bits = int(math.floor(math.log2(p)))

    def is_binary_constraint(c: R1CSConstraint) -> str | None:
        # Match x * (x - 1) = 0 or (x - 1) * x = 0 (mod p)
        if any(v % p != 0 for v in c.c.terms.values()):
            return None
        for first, second in ((c.a.terms, c.b.terms), (c.b.terms, c.a.terms)):
            f_nz = {k: v % p for k, v in first.items() if v % p != 0}
            s_nz = {k: v % p for k, v in second.items() if v % p != 0}
            if len(f_nz) == 1 and "1" not in f_nz:
                (w, c1), = f_nz.items()
                if c1 == 1 and len(s_nz) == 2 and s_nz.get(w) == 1 and s_nz.get("1") == (p - 1):
                    return w
        return None

    changed = True
    while changed:
        changed = False
        # 1. Binary01 lemma: x * (x - 1) = 0 => x in {0, 1}
        for c in circuit.constraints:
            bw = is_binary_constraint(c)
            if bw is not None and bw not in binary01:
                binary01.add(bw)
                changed = True

        # 2. Linear lemma: if constraint is 1 * L(w) = R(w) (or A/B all known) with exactly
        #    one unknown wire appearing linearly with non-zero coefficient mod p, mark unique.
        for c in circuit.constraints:
            a_vars = {k for k, v in c.a.terms.items() if k != "1" and v % p != 0}
            b_vars = {k for k, v in c.b.terms.items() if k != "1" and v % p != 0}
            c_vars = {k for k, v in c.c.terms.items() if k != "1" and v % p != 0}

            # Case 2a: A and B are completely known (or constant), C has exactly 1 unknown wire
            if a_vars <= known and b_vars <= known:
                unk = c_vars - known
                if len(unk) == 1:
                    known.update(unk)
                    changed = True
            # Case 2b: A is a non-zero constant, C is completely known, B has 1 unknown wire
            if not a_vars and (c.a.terms.get("1", 0) % p != 0) and c_vars <= known:
                unk = b_vars - known
                if len(unk) == 1:
                    known.update(unk)
                    changed = True
            # Case 2c: B is a non-zero constant, C is completely known, A has 1 unknown wire
            if not b_vars and (c.b.terms.get("1", 0) % p != 0) and c_vars <= known:
                unk = a_vars - known
                if len(unk) == 1:
                    known.update(unk)
                    changed = True
            # Case 2d: Purely linear equality 1 * L = R where union has exactly 1 unknown
            if (not a_vars and c.a.terms.get("1", 0) % p == 1) or (
                not b_vars and c.b.terms.get("1", 0) % p == 1
            ):
                lin_a = c.b.terms if (not a_vars and c.a.terms.get("1", 0) % p == 1) else c.a.terms
                combined: dict[str, int] = {}
                for k, v in lin_a.items():
                    combined[k] = (combined.get(k, 0) + v) % p
                for k, v in c.c.terms.items():
                    combined[k] = (combined.get(k, 0) - v) % p
                nz_vars = {k for k, v in combined.items() if k != "1" and v % p != 0}
                unk = nz_vars - known
                if len(unk) == 1:
                    known.update(unk)
                    changed = True

                # 3. Basis-2 lemma: z = sum_{i=0}^{k-1} 2^i * b_i with b_i in {0,1} and z known
                #    ONLY sound when k <= floor(log2(p)) so sum 2^i = 2^k - 1 < p (no aliasing!).
                if len(unk) > 1 and all(w in binary01 for w in unk):
                    known_in_eq = nz_vars & known
                    if len(known_in_eq) == 1:
                        target = next(iter(known_in_eq))
                        # Normalize so target coefficient is p - 1 (i.e. sum c_i b_i = target)
                        t_coeff = combined[target]
                        inv_neg_t = pow((-t_coeff) % p, p - 2, p)
                        bit_coeffs = {(combined[w] * inv_neg_t) % p for w in unk}
                        k = len(unk)
                        expected_basis = {1 << i for i in range(k)}
                        if k <= max_safe_bits and bit_coeffs == expected_basis:
                            known.update(unk)
                            changed = True

    return known, binary01


def check_relational_uniqueness(
    circuit: R1CSCircuit,
    target_wires: tuple[str, ...] | None = None,
    input_domain: list[dict[str, int]] | None = None,
) -> dict[str, Any]:
    """Exact relational solver for small prime fields F_p.

    Checks:
      - output/target uniqueness: C(x, w1) /\\ C(x, w2) => w1[y] == w2[y]
      - strong uniqueness: C(x, w1) /\\ C(x, w2) => w1 == w2
      - completeness: every x in input_domain has >= 1 valid witness.
    """
    p = circuit.prime
    targets = target_wires if target_wires is not None else circuit.outputs
    non_inputs = circuit.intermediates + circuit.outputs

    if input_domain is None:
        input_domain = [
            dict(zip(circuit.inputs, vals))
            for vals in itertools.product(range(p), repeat=len(circuit.inputs))
        ]

    # Identify binary-constrained non-input wires to prune search cleanly without losing soundness
    _, binary_wires = picus_propagate_uniqueness(circuit)

    target_forgery: dict[str, Any] | None = None
    intermediate_nondet: dict[str, Any] | None = None
    unsat_inputs: list[dict[str, int]] = []

    for inp in input_domain:
        domains = [
            (0, 1) if w in binary_wires else range(p)
            for w in non_inputs
        ]
        solutions: list[dict[str, int]] = []
        for vals in itertools.product(*domains):
            env = dict(inp)
            env.update(zip(non_inputs, vals))
            if circuit.is_satisfied(env):
                solutions.append(env)
                if len(solutions) >= 2:
                    t0 = tuple(solutions[0][t] for t in targets)
                    t1 = tuple(env[t] for t in targets)
                    if t0 != t1 and target_forgery is None:
                        target_forgery = {
                            "input": inp,
                            "witness_1": solutions[0],
                            "witness_2": env,
                        }
                        break
                    elif t0 == t1 and intermediate_nondet is None:
                        intermediate_nondet = {
                            "input": inp,
                            "witness_1": solutions[0],
                            "witness_2": env,
                        }
        if not solutions:
            unsat_inputs.append(inp)

    return {
        "circuit": circuit.name,
        "prime": p,
        "target_unique": target_forgery is None,
        "strongly_unique": target_forgery is None and intermediate_nondet is None,
        "target_forgery": target_forgery,
        "intermediate_nondeterminism": intermediate_nondet,
        "unsat_input_count": len(unsat_inputs),
        "sample_unsat_input": unsat_inputs[0] if unsat_inputs else None,
    }


def run_zk_probe() -> dict[str, Any]:
    p17 = 17
    # A1a: Buggy IsZero (omits `in * out === 0`)
    buggy_is_zero = R1CSCircuit(
        name="IsZero_buggy_missing_in_mul_out",
        prime=p17,
        inputs=("in",),
        outputs=("out",),
        intermediates=("inv",),
        constraints=[
            # (-in) * inv = out - 1  <=>  out = -in * inv + 1
            R1CSConstraint(
                LinearComb({"in": p17 - 1}),
                LinearComb({"inv": 1}),
                LinearComb({"out": 1, "1": p17 - 1}),
                "out = -in * inv + 1",
            )
        ],
    )
    # A1b: Sound circomlib::IsZero (adds `in * out === 0`)
    sound_is_zero = R1CSCircuit(
        name="IsZero_circomlib_sound",
        prime=p17,
        inputs=("in",),
        outputs=("out",),
        intermediates=("inv",),
        constraints=buggy_is_zero.constraints
        + [
            R1CSConstraint(
                LinearComb({"in": 1}),
                LinearComb({"out": 1}),
                LinearComb({}),
                "in * out = 0",
            )
        ],
    )

    res_a1_buggy = check_relational_uniqueness(buggy_is_zero)
    res_a1_sound = check_relational_uniqueness(sound_is_zero)
    assert not res_a1_buggy["target_unique"], "Buggy IsZero must expose a witness forgery"
    assert res_a1_sound["target_unique"], "Sound IsZero must uniquely determine `out`"
    assert not res_a1_sound["strongly_unique"], (
        "Sound IsZero has weak determinism: `inv` is non-unique when `in == 0`"
    )
    assert res_a1_sound["intermediate_nondeterminism"]["input"] == {"in": 0}

    # A2a: Buggy Num2Bits(4) over F_17 missing boolean constraint on b0
    def make_num2bits(n: int, prime: int, drop_bool_idx: int | None = None, name: str = "") -> R1CSCircuit:
        bits = tuple(f"b{i}" for i in range(n))
        cnsts: list[R1CSConstraint] = []
        for i, b in enumerate(bits):
            if drop_bool_idx is not None and i == drop_bool_idx:
                continue
            cnsts.append(
                R1CSConstraint(
                    LinearComb({b: 1}),
                    LinearComb({b: 1, "1": prime - 1}),
                    LinearComb({}),
                    f"{b}*({b}-1)=0",
                )
            )
        lc = {b: (1 << i) % prime for i, b in enumerate(bits)}
        cnsts.append(
            R1CSConstraint(
                LinearComb({"1": 1}),
                LinearComb(lc),
                LinearComb({"in": 1}),
                "sum(2^i * b_i) = in",
            )
        )
        return R1CSCircuit(
            name=name,
            prime=prime,
            inputs=("in",),
            outputs=bits,
            intermediates=(),
            constraints=cnsts,
        )

    buggy_n2b = make_num2bits(4, p17, drop_bool_idx=0, name="Num2Bits4_missing_b0_bool")
    sound_n2b = make_num2bits(4, p17, drop_bool_idx=None, name="Num2Bits4_sound_F17")
    aliased_n2b = make_num2bits(5, p17, drop_bool_idx=None, name="Num2Bits5_field_aliasing_F17")

    prop_buggy, _ = picus_propagate_uniqueness(buggy_n2b)
    prop_sound, _ = picus_propagate_uniqueness(sound_n2b)
    prop_alias, _ = picus_propagate_uniqueness(aliased_n2b)

    assert not set(buggy_n2b.outputs).issubset(prop_buggy)
    assert set(sound_n2b.outputs).issubset(prop_sound), "Basis2Lemma must prove Num2Bits(4) over F_17"
    assert not set(aliased_n2b.outputs).issubset(prop_alias), (
        "Basis2Lemma must reject 5-bit basis over F_17 (2^5 > 17 aliasing)"
    )

    res_a2_buggy = check_relational_uniqueness(buggy_n2b, input_domain=[{"in": 5}])
    res_a2_sound = check_relational_uniqueness(sound_n2b)
    res_a2_alias = check_relational_uniqueness(aliased_n2b, input_domain=[{"in": 1}])

    assert not res_a2_buggy["target_unique"], "Missing boolean constraint must permit witness forgery"
    assert res_a2_sound["target_unique"], "Num2Bits(4) over F_17 is sound (unique bits)"
    assert res_a2_sound["unsat_input_count"] == 1 and res_a2_sound["sample_unsat_input"] == {"in": 16}, (
        "Num2Bits(4) over F_17 is incomplete/over-constrained for in=16 (outside [0, 15])"
    )
    assert not res_a2_alias["target_unique"], (
        "Num2Bits(5) over F_17 must exhibit field aliasing: 1 == 18 (mod 17)"
    )

    # A2d: AliasCheck repair on Num2Bits(5) over F_17: enforce sum(2^i * b_i) <= 16 over Z
    # Notice: for b0..b4 in {0,1}, sum <= 16 iff b4 == 0 OR (b4 == 1 and b3=b2=b1=b0=0).
    # Equivalently: b4 * (b0 + b1 + b2 + b3) = 0 (since b_i in {0,1} and sum <= 4 < 17).
    strict_n2b = R1CSCircuit(
        name="Num2Bits5_strict_alias_checked_F17",
        prime=p17,
        inputs=aliased_n2b.inputs,
        outputs=aliased_n2b.outputs,
        intermediates=(),
        constraints=aliased_n2b.constraints
        + [
            R1CSConstraint(
                LinearComb({"b4": 1}),
                LinearComb({"b0": 1, "b1": 1, "b2": 1, "b3": 1}),
                LinearComb({}),
                "AliasCheck: b4 * (b0 + b1 + b2 + b3) = 0",
            )
        ],
    )
    res_a2_strict = check_relational_uniqueness(strict_n2b)
    assert res_a2_strict["target_unique"] and res_a2_strict["unsat_input_count"] == 0, (
        "Num2Bits_strict over F_17 is both unique and complete for all 17 field elements"
    )

    # A3: Dark Forest v0.3 `LessThan(n)` modular wraparound exploit over F_257 with n=4 (2^4 = 16)
    p257 = 257
    n = 4
    in0, in1 = 250, 2  # Mathematically 250 < 2 is FALSE!
    shifted_mod_p = (in0 + (1 << n) - in1) % p257  # (250 + 16 - 2) % 257 = 7!
    assert shifted_mod_p < (1 << (n + 1)), "Wrapped difference fits in n+1=5 bits"
    top_bit = (shifted_mod_p >> n) & 1  # bit 4 of 7 is 0!
    forged_lt_out = 1 - top_bit  # 1 - 0 = 1 (claims 250 < 2 is TRUE!)
    assert forged_lt_out == 1, "Unchecked LessThan(4) wraps mod 257 and proves 250 < 2 == 1"
    # With Num2Bits(4) range checks on in0 and in1, in0=250 >= 16 has NO witness:
    range_check_blocks = not (0 <= in0 < (1 << n) and 0 <= in1 < (1 << n))
    assert range_check_blocks

    return {
        "is_zero_buggy_forgery": {
            "input": res_a1_buggy["target_forgery"]["input"],
            "witness_1": res_a1_buggy["target_forgery"]["witness_1"],
            "witness_2": res_a1_buggy["target_forgery"]["witness_2"],
        },
        "is_zero_sound_weak_determinism": {
            "target_unique": res_a1_sound["target_unique"],
            "strongly_unique": res_a1_sound["strongly_unique"],
            "nondet_intermediate_at": res_a1_sound["intermediate_nondeterminism"]["input"],
        },
        "num2bits_missing_bool_forgery": res_a2_buggy["target_forgery"],
        "num2bits4_sound_and_domain_boundary": {
            "picus_basis2_proved": set(sound_n2b.outputs).issubset(prop_sound),
            "unsat_outside_range": res_a2_sound["sample_unsat_input"],
        },
        "num2bits5_field_aliasing": {
            "picus_basis2_guarded": not set(aliased_n2b.outputs).issubset(prop_alias),
            "aliasing_witness_1": res_a2_alias["target_forgery"]["witness_1"],
            "aliasing_witness_2": res_a2_alias["target_forgery"]["witness_2"],
            "strict_alias_checked_unique_and_complete": (
                res_a2_strict["target_unique"] and res_a2_strict["unsat_input_count"] == 0
            ),
        },
        "dark_forest_lessthan_wraparound": {
            "prime": p257,
            "n": n,
            "in0": in0,
            "in1": in1,
            "shifted_mod_p": shifted_mod_p,
            "forged_out": forged_lt_out,
            "blocked_by_input_num2bits": range_check_blocks,
        },
    }


# =============================================================================
# PART 2: Move-Style Linear Bytecode Verifier & Gas-Metered Interpreter
# =============================================================================

class Ability(enum.IntFlag):
    NONE = 0x0
    COPY = 0x1
    DROP = 0x2
    STORE = 0x4
    KEY = 0x8

    def required_field_abilities(self) -> "Ability":
        req = Ability.NONE
        if Ability.COPY in self:
            req |= Ability.COPY
        if Ability.DROP in self:
            req |= Ability.DROP
        if Ability.STORE in self or Ability.KEY in self:
            req |= Ability.STORE
        return req


@dataclass(frozen=True)
class MoveType:
    name: str
    abilities: Ability
    ref_kind: str | None = None  # None, "imm", "mut"
    inner: "MoveType | None" = None

    def eff_abilities(self) -> Ability:
        # References in Move have `copy` (for imm) and `drop` (both imm and mut)
        if self.ref_kind == "imm":
            return Ability.COPY | Ability.DROP
        if self.ref_kind == "mut":
            return Ability.DROP
        return self.abilities


U64 = MoveType("u64", Ability.COPY | Ability.DROP | Ability.STORE)
BOOL = MoveType("bool", Ability.COPY | Ability.DROP | Ability.STORE)
COIN = MoveType("Coin", Ability.STORE)  # Linear resource: no COPY, no DROP!
FLASH_RECEIPT = MoveType("FlashReceipt", Ability.NONE)  # Hot potato: no COPY/DROP/STORE/KEY!


@dataclass(frozen=True)
class StructDef:
    name: str
    abilities: Ability
    fields: tuple[tuple[str, MoveType], ...]


def verify_struct_field_abilities(sdef: StructDef) -> str | None:
    """Mirrors Move `ability_field_requirements.rs`."""
    req = sdef.abilities.required_field_abilities()
    for fname, fty in sdef.fields:
        if (req & fty.eff_abilities()) != req:
            return f"FIELD_MISSING_TYPE_ABILITY({sdef.name}.{fname})"
    return None


class LocalState(enum.Enum):
    UNAVAILABLE = 0
    MAYBE_AVAILABLE = 1
    AVAILABLE = 2


def join_local_state(a: LocalState, b: LocalState) -> LocalState:
    if a == b:
        return a
    return LocalState.MAYBE_AVAILABLE


@dataclass(frozen=True)
class Instr:
    op: str
    arg: Any = None


@dataclass
class BasicBlock:
    label: str
    instrs: list[Instr]
    succs: tuple[str, ...] = ()


@dataclass
class MoveFunction:
    name: str
    params: list[tuple[str, MoveType]]
    locals_extra: list[tuple[str, MoveType]]
    returns: list[MoveType]
    blocks: dict[str, BasicBlock]
    entry: str = "entry"

    def all_locals(self) -> list[tuple[str, MoveType]]:
        return self.params + self.locals_extra


@dataclass
class RefNode:
    ref_id: int
    mutable: bool
    root_local: int
    parent: int | None = None  # None => borrowed directly from local


class VerifierError(Exception):
    def __init__(self, code: str, detail: str = ""):
        super().__init__(f"{code}: {detail}" if detail else code)
        self.code = code


def verify_move_function(
    fn: MoveFunction,
    struct_defs: dict[str, StructDef],
    callees: dict[str, tuple[list[MoveType], list[MoveType]]],
) -> None:
    """Abstract-interpretation verifier modeling Move's type, locals, and reference safety."""
    all_locals = fn.all_locals()
    loc_types = [t for _, t in all_locals]
    loc_idx_by_name = {name: i for i, (name, _) in enumerate(all_locals)}

    def loc_id(arg: int | str) -> int:
        return loc_idx_by_name[arg] if isinstance(arg, str) else int(arg)

    # Abstract state per block entry: (stack_types, local_states, active_borrows, local_ref_map)
    init_locals = tuple(
        LocalState.AVAILABLE if i < len(fn.params) else LocalState.UNAVAILABLE
        for i in range(len(all_locals))
    )
    init_local_refs = tuple(None for _ in range(len(all_locals)))
    init_state = ((), init_locals, frozenset(), init_local_refs)

    block_in: dict[str, tuple[tuple[MoveType, ...], tuple[LocalState, ...], frozenset, tuple[int | None, ...]]] = {
        fn.entry: init_state
    }
    worklist: list[str] = [fn.entry]
    next_ref_id = 1

    while worklist:
        bname = worklist.pop(0)
        stack_t, lstates_t, borrows_fs, lrefs_t = block_in[bname]
        stack: list[tuple[MoveType, int | None]] = [(t, None) for t in stack_t]
        lstates = list(lstates_t)
        lrefs: list[int | None] = list(lrefs_t)
        # Active borrow graph: ref_id -> (mutable, local_idx, parent_ref)
        borrows: dict[int, tuple[bool, int, int | None]] = {
            r[0]: (r[1], r[2], r[3]) for r in borrows_fs
        }
        held_in_locals = {rid for rid in lrefs if rid is not None}
        stack_ref_ids = sorted(rid for rid in borrows if rid not in held_in_locals)
        ri_cursor = 0
        for idx_s, (t, _) in enumerate(stack):
            if t.ref_kind is not None and ri_cursor < len(stack_ref_ids):
                stack[idx_s] = (t, stack_ref_ids[ri_cursor])
                ri_cursor += 1

        def has_local_borrow(lidx: int, only_mut: bool = False) -> bool:
            return any(
                (loc == lidx and (not only_mut or is_mut))
                for (is_mut, loc, _par) in borrows.values()
            )

        def has_child_borrow(rid: int, only_mut: bool = False) -> bool:
            return any(
                (par == rid and (not only_mut or is_mut))
                for (is_mut, _loc, par) in borrows.values()
            )

        def release_ref(rid: int | None) -> None:
            if rid is not None:
                borrows.pop(rid, None)

        blk = fn.blocks[bname]
        terminated = False

        for ins in blk.instrs:
            op, arg = ins.op, ins.arg
            if op == "LdU64":
                stack.append((U64, None))
            elif op == "LdBool":
                stack.append((BOOL, None))
            elif op == "MoveLoc":
                idx = loc_id(arg)
                if lstates[idx] != LocalState.AVAILABLE:
                    raise VerifierError("MOVELOC_UNAVAILABLE_ERROR", f"local {arg}")
                if loc_types[idx].ref_kind is None and has_local_borrow(idx):
                    raise VerifierError("MOVELOC_EXISTS_BORROW_ERROR", f"local {arg}")
                lstates[idx] = LocalState.UNAVAILABLE
                moved_rid = lrefs[idx]
                lrefs[idx] = None
                stack.append((loc_types[idx], moved_rid))
            elif op == "CopyLoc":
                idx = loc_id(arg)
                if Ability.COPY not in loc_types[idx].eff_abilities():
                    raise VerifierError("COPYLOC_WITHOUT_COPY_ABILITY", f"local {arg}")
                if lstates[idx] != LocalState.AVAILABLE:
                    raise VerifierError("COPYLOC_UNAVAILABLE_ERROR", f"local {arg}")
                if has_local_borrow(idx, only_mut=True):
                    raise VerifierError("COPYLOC_EXISTS_BORROW_ERROR", f"local {arg}")
                stack.append((loc_types[idx], lrefs[idx]))
            elif op == "StLoc":
                idx = loc_id(arg)
                if not stack:
                    raise VerifierError("STACK_UNDERFLOW", "StLoc")
                val_ty, val_rid = stack.pop()
                if val_ty != loc_types[idx]:
                    raise VerifierError("STLOC_TYPE_MISMATCH_ERROR", f"{val_ty} != {loc_types[idx]}")
                if lstates[idx] in (LocalState.AVAILABLE, LocalState.MAYBE_AVAILABLE):
                    if Ability.DROP not in loc_types[idx].eff_abilities():
                        raise VerifierError("STLOC_UNSAFE_TO_DESTROY_ERROR", f"local {arg}")
                if loc_types[idx].ref_kind is None and has_local_borrow(idx):
                    raise VerifierError("STLOC_UNSAFE_TO_DESTROY_ERROR", f"borrowed local {arg}")
                # Mirrors reference_safety::AbstractState::st_loc: release OLD local ref, keep NEW ref live
                release_ref(lrefs[idx])
                lrefs[idx] = val_rid
                lstates[idx] = LocalState.AVAILABLE
            elif op == "Pop":
                if not stack:
                    raise VerifierError("STACK_UNDERFLOW", "Pop")
                val_ty, val_rid = stack.pop()
                if Ability.DROP not in val_ty.eff_abilities():
                    raise VerifierError("POP_WITHOUT_DROP_ABILITY", val_ty.name)
                release_ref(val_rid)
            elif op in ("ImmBorrowLoc", "MutBorrowLoc"):
                idx = loc_id(arg)
                is_mut = op == "MutBorrowLoc"
                if lstates[idx] != LocalState.AVAILABLE:
                    raise VerifierError("BORROWLOC_UNAVAILABLE_ERROR", f"local {arg}")
                if not is_mut and has_local_borrow(idx, only_mut=True):
                    raise VerifierError("BORROWLOC_EXISTS_BORROW_ERROR", f"local {arg}")
                if is_mut and has_local_borrow(idx):
                    raise VerifierError("BORROWLOC_EXISTS_BORROW_ERROR", f"local {arg}")
                rid = next_ref_id
                next_ref_id += 1
                borrows[rid] = (is_mut, idx, None)
                rty = MoveType(
                    f"&{'mut ' if is_mut else ''}{loc_types[idx].name}",
                    Ability.NONE,
                    ref_kind="mut" if is_mut else "imm",
                    inner=loc_types[idx],
                )
                stack.append((rty, rid))
            elif op == "SubBorrowMut":
                # Models MutBorrowField / reborrow extending an existing &mut reference
                if not stack:
                    raise VerifierError("STACK_UNDERFLOW", "SubBorrowMut")
                rty, par_rid = stack[-1]  # keep parent ref live on stack or duplicate scenario
                if rty.ref_kind != "mut" or par_rid is None:
                    raise VerifierError("BORROWFIELD_TYPE_MISMATCH_ERROR", rty.name)
                rid = next_ref_id
                next_ref_id += 1
                _, lidx, _ = borrows[par_rid]
                borrows[rid] = (True, lidx, par_rid)
                stack.append((rty, rid))
            elif op == "ReadRef":
                if not stack:
                    raise VerifierError("STACK_UNDERFLOW", "ReadRef")
                rty, rid = stack.pop()
                if rty.ref_kind is None or rty.inner is None:
                    raise VerifierError("READREF_TYPE_MISMATCH_ERROR", rty.name)
                if Ability.COPY not in rty.inner.eff_abilities():
                    raise VerifierError("READREF_WITHOUT_COPY_ABILITY", rty.inner.name)
                if rid is not None and rty.ref_kind == "mut" and has_child_borrow(rid, only_mut=True):
                    raise VerifierError("READREF_EXISTS_MUTABLE_BORROW_ERROR", rty.name)
                release_ref(rid)
                stack.append((rty.inner, None))
            elif op == "WriteRef":
                if len(stack) < 2:
                    raise VerifierError("STACK_UNDERFLOW", "WriteRef")
                rty, rid = stack.pop()
                vty, _ = stack.pop()
                if rty.ref_kind != "mut" or rty.inner is None:
                    raise VerifierError("WRITEREF_NO_MUTABLE_REFERENCE_ERROR", rty.name)
                if Ability.DROP not in rty.inner.eff_abilities():
                    raise VerifierError("WRITEREF_WITHOUT_DROP_ABILITY", rty.inner.name)
                if vty != rty.inner:
                    raise VerifierError("WRITEREF_TYPE_MISMATCH_ERROR", f"{vty} != {rty.inner}")
                if rid is not None and has_child_borrow(rid):
                    raise VerifierError("WRITEREF_EXISTS_BORROW_ERROR", rty.name)
                release_ref(rid)
            elif op == "Pack":
                sdef = struct_defs[arg]
                for fname, fty in reversed(sdef.fields):
                    vty, _ = stack.pop()
                    if vty != fty:
                        raise VerifierError("PACK_TYPE_MISMATCH_ERROR", f"{sdef.name}.{fname}")
                stack.append((MoveType(sdef.name, sdef.abilities), None))
            elif op == "Unpack":
                sdef = struct_defs[arg]
                vty, _ = stack.pop()
                if vty.name != sdef.name:
                    raise VerifierError("UNPACK_TYPE_MISMATCH_ERROR", f"{vty.name} != {sdef.name}")
                for _, fty in sdef.fields:
                    stack.append((fty, None))
            elif op == "Add":
                b_ty, _ = stack.pop()
                a_ty, _ = stack.pop()
                if a_ty != U64 or b_ty != U64:
                    raise VerifierError("INTEGER_OP_TYPE_MISMATCH_ERROR", "Add")
                stack.append((U64, None))
            elif op == "Call":
                in_tys, out_tys = callees[arg]
                for expected in reversed(in_tys):
                    vty, rid = stack.pop()
                    if vty != expected:
                        raise VerifierError("CALL_TYPE_MISMATCH_ERROR", arg)
                    if rid is not None and vty.ref_kind == "mut" and has_child_borrow(rid):
                        raise VerifierError("CALL_BORROWED_MUTABLE_REFERENCE_ERROR", arg)
                    release_ref(rid)
                for ot in out_tys:
                    stack.append((ot, None))
            elif op == "BrFalse":
                cty, _ = stack.pop()
                if cty != BOOL:
                    raise VerifierError("BR_TYPE_MISMATCH_ERROR", cty.name)
            elif op == "Abort":
                terminated = True
                break
            elif op == "Ret":
                if [t for t, _ in stack] != fn.returns:
                    raise VerifierError(
                        "RET_TYPE_MISMATCH_ERROR",
                        f"got {[t.name for t, _ in stack]}, expected {[t.name for t in fn.returns]}",
                    )
                for idx_l, (st, ltype) in enumerate(zip(lstates, loc_types)):
                    if st in (LocalState.AVAILABLE, LocalState.MAYBE_AVAILABLE):
                        if Ability.DROP not in ltype.eff_abilities():
                            raise VerifierError(
                                "UNSAFE_RET_UNUSED_VALUES_WITHOUT_DROP",
                                f"local {all_locals[idx_l][0]} ({st.name})",
                            )
                terminated = True
                break
            else:
                raise VerifierError("UNKNOWN_OPCODE", op)

        if not terminated:
            out_stack = tuple(t for t, _ in stack)
            out_locals = tuple(lstates)
            out_borrows = frozenset((rid, m, loc, par) for rid, (m, loc, par) in borrows.items())
            out_lrefs = tuple(lrefs)
            for succ in blk.succs:
                if succ not in block_in:
                    block_in[succ] = (out_stack, out_locals, out_borrows, out_lrefs)
                    worklist.append(succ)
                else:
                    prev_s, prev_l, prev_b, prev_lr = block_in[succ]
                    if prev_s != out_stack:
                        raise VerifierError("JOIN_FAILURE", f"stack mismatch at {succ}")
                    joined_l = tuple(join_local_state(a, b) for a, b in zip(prev_l, out_locals))
                    joined_b = prev_b | out_borrows
                    joined_lr = tuple(a if a == b else None for a, b in zip(prev_lr, out_lrefs))
                    new_st = (prev_s, joined_l, joined_b, joined_lr)
                    if new_st != block_in[succ]:
                        block_in[succ] = new_st
                        worklist.append(succ)


def execute_metered_transfer(
    ledger: dict[str, int], sender: str, receiver: str, amount: int, gas_limit: int
) -> tuple[bool, dict[str, int], str]:
    """Deterministic gas-metered linear transfer with atomic rollback on out-of-gas/abort."""
    snapshot = dict(ledger)
    gas = gas_limit

    def charge(units: int) -> None:
        nonlocal gas
        if gas < units:
            raise RuntimeError("OUT_OF_GAS")
        gas -= units

    try:
        charge(5)  # withdraw linear Coin
        if snapshot[sender] < amount:
            raise RuntimeError("ABORT_INSUFFICIENT_BALANCE")
        snapshot[sender] -= amount
        coin_in_flight = amount
        charge(5)  # deposit linear Coin
        snapshot[receiver] += coin_in_flight
        coin_in_flight = 0
        return True, snapshot, f"COMMITTED(gas_left={gas})"
    except RuntimeError as exc:
        # Atomic transaction rollback: partial mutation discarded, total supply invariant holds!
        return False, dict(ledger), f"ROLLED_BACK({exc})"


def run_move_probe() -> dict[str, Any]:
    coin_def = StructDef("Coin", Ability.STORE, (("value", U64),))
    receipt_def = StructDef("FlashReceipt", Ability.NONE, (("owed", U64),))
    fake_copy_def = StructDef("FakeCopy", Ability.COPY, (("c", COIN),))
    structs = {"Coin": coin_def, "FlashReceipt": receipt_def}
    callees = {
        "borrow_flash": ([U64], [COIN, FLASH_RECEIPT]),
        "repay_flash": ([COIN, FLASH_RECEIPT], []),
    }

    assert verify_struct_field_abilities(coin_def) is None
    assert verify_struct_field_abilities(receipt_def) is None
    fake_err = verify_struct_field_abilities(fake_copy_def)
    assert fake_err == "FIELD_MISSING_TYPE_ABILITY(FakeCopy.c)"

    # B1: Sound linear coin merge: (c1: Coin, c2: Coin) -> Coin
    sound_merge = MoveFunction(
        name="merge_coins",
        params=[("c1", COIN), ("c2", COIN)],
        locals_extra=[],
        returns=[COIN],
        blocks={
            "entry": BasicBlock(
                "entry",
                [
                    Instr("MoveLoc", "c1"),
                    Instr("Unpack", "Coin"),
                    Instr("MoveLoc", "c2"),
                    Instr("Unpack", "Coin"),
                    Instr("Add"),
                    Instr("Pack", "Coin"),
                    Instr("Ret"),
                ],
            )
        },
    )
    verify_move_function(sound_merge, structs, callees)

    def expect_err(fn: MoveFunction, expected_code: str) -> str:
        try:
            verify_move_function(fn, structs, callees)
        except VerifierError as exc:
            assert exc.code == expected_code, f"{fn.name}: expected {expected_code}, got {exc.code}"
            return exc.code
        raise AssertionError(f"{fn.name}: unexpectedly passed verification!")

    # B2: Double-spend via CopyLoc on Coin
    bad_copy = MoveFunction(
        "bad_double_spend_copy",
        [("c", COIN)],
        [],
        [COIN, COIN],
        {"entry": BasicBlock("entry", [Instr("CopyLoc", "c"), Instr("MoveLoc", "c"), Instr("Ret")])},
    )
    e_copy = expect_err(bad_copy, "COPYLOC_WITHOUT_COPY_ABILITY")

    # B3: Reference-copy bypass via ImmBorrowLoc + ReadRef on Coin
    bad_readref = MoveFunction(
        "bad_readref_coin",
        [("c", COIN)],
        [],
        [COIN, COIN],
        {
            "entry": BasicBlock(
                "entry",
                [Instr("ImmBorrowLoc", "c"), Instr("ReadRef"), Instr("MoveLoc", "c"), Instr("Ret")],
            )
        },
    )
    e_readref = expect_err(bad_readref, "READREF_WITHOUT_COPY_ABILITY")

    # B4: Silent drop via Pop and WriteRef
    bad_pop = MoveFunction(
        "bad_pop_coin",
        [("c", COIN)],
        [],
        [],
        {"entry": BasicBlock("entry", [Instr("MoveLoc", "c"), Instr("Pop"), Instr("Ret")])},
    )
    e_pop = expect_err(bad_pop, "POP_WITHOUT_DROP_ABILITY")

    bad_writeref = MoveFunction(
        "bad_writeref_coin",
        [("c1", COIN), ("c2", COIN)],
        [],
        [],
        {
            "entry": BasicBlock(
                "entry",
                [Instr("MoveLoc", "c2"), Instr("MutBorrowLoc", "c1"), Instr("WriteRef"), Instr("Ret")],
            )
        },
    )
    e_writeref = expect_err(bad_writeref, "WRITEREF_WITHOUT_DROP_ABILITY")

    # B5: Control-flow-sensitive branch leak (`MaybeAvailable` at join -> rejected on `Ret`)
    bad_branch_leak = MoveFunction(
        "bad_branch_leak_coin",
        [("cond", BOOL), ("c", COIN)],
        [],
        [],
        {
            "entry": BasicBlock("entry", [Instr("CopyLoc", "cond"), Instr("BrFalse")], ("then_blk", "else_blk")),
            "then_blk": BasicBlock(
                "then_blk",
                [Instr("MoveLoc", "c"), Instr("Unpack", "Coin"), Instr("Pop")],
                ("join_blk",),
            ),
            "else_blk": BasicBlock("else_blk", [], ("join_blk",)),
            "join_blk": BasicBlock("join_blk", [Instr("Ret")]),
        },
    )
    e_branch = expect_err(bad_branch_leak, "UNSAFE_RET_UNUSED_VALUES_WITHOUT_DROP")

    # B5b: Control-flow-sensitive branch overwrite (`MaybeAvailable` -> STLOC_UNSAFE_TO_DESTROY_ERROR)
    bad_branch_overwrite = MoveFunction(
        "bad_branch_overwrite_coin",
        [("cond", BOOL), ("c", COIN), ("c2", COIN)],
        [],
        [COIN],
        {
            "entry": BasicBlock("entry", [Instr("CopyLoc", "cond"), Instr("BrFalse")], ("then_blk", "else_blk")),
            "then_blk": BasicBlock(
                "then_blk",
                [Instr("MoveLoc", "c"), Instr("Unpack", "Coin"), Instr("Pop")],
                ("join_blk",),
            ),
            "else_blk": BasicBlock("else_blk", [], ("join_blk",)),
            "join_blk": BasicBlock(
                "join_blk",
                [Instr("MoveLoc", "c2"), Instr("StLoc", "c"), Instr("MoveLoc", "c"), Instr("Ret")],
            ),
        },
    )
    e_branch_stloc = expect_err(bad_branch_overwrite, "STLOC_UNSAFE_TO_DESTROY_ERROR")

    # B6: Borrow safety (move while borrowed; write/read through parent &mut while child &mut live)
    bad_move_borrowed = MoveFunction(
        "bad_move_while_borrowed",
        [("x", U64)],
        [],
        [U64],
        {
            "entry": BasicBlock(
                "entry",
                [Instr("ImmBorrowLoc", "x"), Instr("MoveLoc", "x"), Instr("Ret")],
            )
        },
    )
    e_move_borr = expect_err(bad_move_borrowed, "MOVELOC_EXISTS_BORROW_ERROR")

    mut_u64 = MoveType("&mut u64", Ability.NONE, "mut", U64)
    bad_write_parent = MoveFunction(
        "bad_write_parent_while_child_mut_live",
        [("x", U64)],
        [("r_child", mut_u64), ("r_parent", mut_u64)],
        [],
        {
            "entry": BasicBlock(
                "entry",
                [
                    Instr("MutBorrowLoc", "x"),   # r1
                    Instr("SubBorrowMut"),        # stack: [r1, r2 (child of r1)]
                    Instr("StLoc", "r_child"),    # keeps r2 alive in local r_child
                    Instr("StLoc", "r_parent"),   # keeps r1 alive in local r_parent
                    Instr("LdU64", 42),
                    Instr("MoveLoc", "r_parent"),
                    Instr("WriteRef"),            # illegal: r_child borrows from r_parent!
                    Instr("Ret"),
                ],
            )
        },
    )
    e_write_sub = expect_err(bad_write_parent, "WRITEREF_EXISTS_BORROW_ERROR")

    bad_read_parent = MoveFunction(
        "bad_read_parent_while_child_mut_live",
        [("x", U64)],
        [("r_child", mut_u64), ("r_parent", mut_u64)],
        [U64],
        {
            "entry": BasicBlock(
                "entry",
                [
                    Instr("MutBorrowLoc", "x"),
                    Instr("SubBorrowMut"),
                    Instr("StLoc", "r_child"),
                    Instr("StLoc", "r_parent"),
                    Instr("MoveLoc", "r_parent"),
                    Instr("ReadRef"),             # illegal: r_child mut-borrows from r_parent!
                    Instr("Ret"),
                ],
            )
        },
    )
    e_read_sub = expect_err(bad_read_parent, "READREF_EXISTS_MUTABLE_BORROW_ERROR")

    # B7: Hot-potato FlashReceipt: must repay before Ret!
    sound_flash = MoveFunction(
        "sound_flash_loan",
        [],
        [("loan", COIN), ("rcpt", FLASH_RECEIPT)],
        [],
        {
            "entry": BasicBlock(
                "entry",
                [
                    Instr("LdU64", 100),
                    Instr("Call", "borrow_flash"),
                    Instr("StLoc", "rcpt"),
                    Instr("StLoc", "loan"),
                    Instr("MoveLoc", "loan"),
                    Instr("MoveLoc", "rcpt"),
                    Instr("Call", "repay_flash"),
                    Instr("Ret"),
                ],
            )
        },
    )
    verify_move_function(sound_flash, structs, callees)

    bad_flash_abandon = MoveFunction(
        "bad_flash_abandon_receipt",
        [],
        [("loan", COIN), ("rcpt", FLASH_RECEIPT)],
        [COIN],
        {
            "entry": BasicBlock(
                "entry",
                [
                    Instr("LdU64", 100),
                    Instr("Call", "borrow_flash"),
                    Instr("StLoc", "rcpt"),
                    Instr("StLoc", "loan"),
                    Instr("MoveLoc", "loan"),
                    Instr("Ret"),  # Forgot to repay FlashReceipt!
                ],
            )
        },
    )
    e_flash = expect_err(bad_flash_abandon, "UNSAFE_RET_UNUSED_VALUES_WITHOUT_DROP")

    # B8: Deterministic gas-metered atomic rollback preserves total value supply
    init_ledger = {"alice": 100, "bob": 25}
    ok_commit, led_commit, st_commit = execute_metered_transfer(init_ledger, "alice", "bob", 40, gas_limit=10)
    ok_oog, led_oog, st_oog = execute_metered_transfer(init_ledger, "alice", "bob", 40, gas_limit=7)
    assert ok_commit and sum(led_commit.values()) == 125 and led_commit == {"alice": 60, "bob": 65}
    assert (not ok_oog) and sum(led_oog.values()) == 125 and led_oog == init_ledger

    return {
        "field_ability_smuggling_rejected": fake_err,
        "sound_linear_merge_verified": True,
        "sound_hot_potato_flash_loan_verified": True,
        "rejected_violations": {
            "abandoned_hot_potato_receipt": e_flash,
            "branch_join_maybe_available_leak": e_branch,
            "branch_join_maybe_available_overwrite": e_branch_stloc,
            "double_spend_copy": e_copy,
            "move_while_borrowed": e_move_borr,
            "pop_silent_drop": e_pop,
            "read_parent_while_child_mut_borrowed": e_read_sub,
            "readref_bypass": e_readref,
            "write_parent_while_child_mut_borrowed": e_write_sub,
            "writeref_overwrite": e_writeref,
        },
        "gas_metering_conservation": {
            "committed": {"status": st_commit, "total_supply": sum(led_commit.values())},
            "out_of_gas_rollback": {"status": st_oog, "total_supply": sum(led_oog.values())},
        },
    }


# =============================================================================
# PART 3: Silq-Style Static Type/Uncomputation Checker & Statevector Simulator
# =============================================================================

@dataclass(frozen=True)
class SilqFnSig:
    name: str
    param_is_const: tuple[bool, ...]
    qfree: bool
    mfree: bool

    @property
    def lifted(self) -> bool:
        return self.qfree and all(self.param_is_const)


SILQ_STDLIB: dict[str, SilqFnSig] = {
    "H": SilqFnSig("H", (False,), qfree=False, mfree=True),
    "X": SilqFnSig("X", (False,), qfree=True, mfree=True),
    "phase": SilqFnSig("phase", (True,), qfree=False, mfree=True),
    "measure": SilqFnSig("measure", (False,), qfree=False, mfree=False),
    "oracle_and": SilqFnSig("oracle_and", (True, True), qfree=True, mfree=True),
    "dup": SilqFnSig("dup", (True,), qfree=True, mfree=True),
}


@dataclass
class SilqVar:
    name: str
    is_classical: bool
    is_const: bool
    consumed: bool = False
    uncomputable_from: tuple[str, ...] | None = None  # non-None => lifted temporary


def typecheck_silq_block(
    params: list[SilqVar],
    stmts: list[tuple[str, Any]],
    ret_var: str | None,
) -> tuple[bool, str]:
    """Enforces Silq-Core physicality rules (Bichsel et al., PLDI 2020 §4.4, §6)."""
    env: dict[str, SilqVar] = {
        v.name: SilqVar(v.name, v.is_classical, v.is_const) for v in params
    }

    for kind, payload in stmts:
        if kind == "call":
            # (dst, fn_name, args)
            dst, fn_name, args = payload
            sig = SILQ_STDLIB[fn_name]
            assert len(args) == len(sig.param_is_const)
            deps: list[str] = []
            for a, p_const in zip(args, sig.param_is_const):
                v = env[a]
                if v.consumed:
                    return False, f"USE_CONSUMED_VARIABLE({a})"
                if not p_const:
                    if v.is_const:
                        # Silq §4.4: passing const to consuming param implicitly duplicates via CNOT
                        deps.append(a)
                    else:
                        v.consumed = True
                else:
                    deps.append(a)
            uncomp_deps = tuple(deps) if sig.lifted else None
            env[dst] = SilqVar(
                dst,
                is_classical=(fn_name == "measure"),
                is_const=False,
                consumed=False,
                uncomputable_from=uncomp_deps,
            )
        elif kind == "qif":
            # (cond_var, body_fn_name, body_args) — quantum-controlled branch requires mfree!
            cond_var, body_fn, body_args = payload
            cv = env[cond_var]
            if cv.consumed:
                return False, f"USE_CONSUMED_VARIABLE({cond_var})"
            sig = SILQ_STDLIB[body_fn]
            if not cv.is_classical and not sig.mfree:
                return False, f"CONDITIONAL_MEASUREMENT_NOT_MFREE({body_fn})"
        elif kind == "auto_forget":
            # Attempt automatic uncomputation of temporary variable `target`
            target = payload
            tv = env[target]
            if tv.consumed or tv.is_classical:
                continue
            if tv.uncomputable_from is None:
                return False, f"CANNOT_UNCOMPUTE_NON_LIFTED({target})"
            for dep in tv.uncomputable_from:
                if env[dep].consumed:
                    return False, f"CANNOT_UNCOMPUTE_CONSUMED_DEPENDENCY({target}<-{dep})"
            tv.consumed = True

    # End-of-scope check: any unconsumed non-const, non-classical, non-returned variable
    for name, v in env.items():
        if name == ret_var or v.is_classical or v.is_const or v.consumed:
            continue
        if v.uncomputable_from is not None and all(not env[d].consumed for d in v.uncomputable_from):
            v.consumed = True  # Safe automatic Bennett uncomputation!
        else:
            if v.uncomputable_from is None:
                return False, f"UNSAFE_DISCARD_OR_NON_QFREE({name})"
            return False, f"CANNOT_UNCOMPUTE_CONSUMED_DEPENDENCY({name})"
    return True, "OK"


# Exact Statevector Quantum Simulator (big-endian bit ordering: qubit 0 is MSB)
INV_SQRT2 = 1.0 / math.sqrt(2.0)


def init_zero_state(n_qubits: int) -> list[complex]:
    st = [0j] * (1 << n_qubits)
    st[0] = 1.0 + 0j
    return st


def apply_1q(state: list[complex], n: int, q: int, mat: tuple[tuple[complex, complex], tuple[complex, complex]]) -> list[complex]:
    out = [0j] * len(state)
    bit = 1 << (n - 1 - q)
    for idx in range(len(state)):
        if (idx & bit) == 0:
            i0, i1 = idx, idx | bit
            a0, a1 = state[i0], state[i1]
            out[i0] = mat[0][0] * a0 + mat[0][1] * a1
            out[i1] = mat[1][0] * a0 + mat[1][1] * a1
    return out


def apply_cnot(state: list[complex], n: int, ctrl: int, tgt: int) -> list[complex]:
    assert ctrl != tgt
    out = list(state)
    cb = 1 << (n - 1 - ctrl)
    tb = 1 << (n - 1 - tgt)
    for idx in range(len(state)):
        if (idx & cb) and not (idx & tb):
            j = idx | tb
            out[idx], out[j] = state[j], state[idx]
    return out


def apply_ccx(state: list[complex], n: int, c0: int, c1: int, tgt: int) -> list[complex]:
    assert len({c0, c1, tgt}) == 3
    out = list(state)
    b0 = 1 << (n - 1 - c0)
    b1 = 1 << (n - 1 - c1)
    bt = 1 << (n - 1 - tgt)
    for idx in range(len(state)):
        if (idx & b0) and (idx & b1) and not (idx & bt):
            j = idx | bt
            out[idx], out[j] = state[j], state[idx]
    return out


H_MAT = ((INV_SQRT2, INV_SQRT2), (INV_SQRT2, -INV_SQRT2))
X_MAT = ((0j, 1 + 0j), (1 + 0j, 0j))
Z_MAT = ((1 + 0j, 0j), (0j, -1 + 0j))


def u_r_mat(theta: float, phi: float, lam: float) -> tuple[tuple[complex, complex], tuple[complex, complex]]:
    """SQIR `rotation θ ϕ λ` single-qubit unitary matrix."""
    ct = math.cos(theta / 2.0)
    st = math.sin(theta / 2.0)
    return (
        (complex(ct, 0.0), -cmath.exp(1j * lam) * st),
        (cmath.exp(1j * phi) * st, cmath.exp(1j * (phi + lam)) * ct),
    )


def reduced_density_matrix(state: list[complex], n: int, keep_qubits: tuple[int, ...]) -> list[list[complex]]:
    """Computes partial trace rho_A = Tr_B(|psi><psi|) over qubits not in `keep_qubits`."""
    k = len(keep_qubits)
    dim_a = 1 << k
    rho = [[0j] * dim_a for _ in range(dim_a)]
    trace_qubits = [q for q in range(n) if q not in keep_qubits]

    def extract_bits(idx: int, qubits: list[int] | tuple[int, ...]) -> int:
        val = 0
        for q in qubits:
            val = (val << 1) | ((idx >> (n - 1 - q)) & 1)
        return val

    # Group amplitudes by traced-out basis state
    by_env: dict[int, list[tuple[int, complex]]] = {}
    for idx, amp in enumerate(state):
        if abs(amp) < 1e-15:
            continue
        env_idx = extract_bits(idx, trace_qubits)
        sys_idx = extract_bits(idx, keep_qubits)
        by_env.setdefault(env_idx, []).append((sys_idx, amp))

    for entries in by_env.values():
        for i, ai in entries:
            for j, aj in entries:
                rho[i][j] += ai * aj.conjugate()
    return rho


def purity(rho: list[list[complex]]) -> float:
    """Returns Tr(rho^2): 1.0 iff pure (disentangled), < 1.0 iff entangled/mixed."""
    d = len(rho)
    acc = 0j
    for i in range(d):
        for j in range(d):
            acc += rho[i][j] * rho[j][i]
    return acc.real


def grover_diffusion_2q(state: list[complex], n: int, q0: int, q1: int) -> list[complex]:
    """2-qubit Grover diffuser D = H^2 * X^2 * CZ * X^2 * H^2."""
    s = apply_1q(state, n, q0, H_MAT)
    s = apply_1q(s, n, q1, H_MAT)
    s = apply_1q(s, n, q0, X_MAT)
    s = apply_1q(s, n, q1, X_MAT)
    # CZ(q0, q1) = H(q1); CNOT(q0, q1); H(q1)
    s = apply_1q(s, n, q1, H_MAT)
    s = apply_cnot(s, n, q0, q1)
    s = apply_1q(s, n, q1, H_MAT)
    s = apply_1q(s, n, q0, X_MAT)
    s = apply_1q(s, n, q1, X_MAT)
    s = apply_1q(s, n, q0, H_MAT)
    s = apply_1q(s, n, q1, H_MAT)
    return s


def run_quantum_probe() -> dict[str, Any]:
    # C0: Silq static type/annotation rejection checks
    ok_use_cons, r_use_cons = typecheck_silq_block(
        [SilqVar("x", False, False)],
        [("call", ("y", "H", ["x"])), ("call", ("z", "X", ["x"]))],
        "z",
    )
    assert not ok_use_cons and r_use_cons == "USE_CONSUMED_VARIABLE(x)"

    ok_discard, r_discard = typecheck_silq_block(
        [SilqVar("x", False, False)],
        [],
        None,
    )
    assert not ok_discard and r_discard == "UNSAFE_DISCARD_OR_NON_QFREE(x)"

    ok_non_qfree, r_non_qfree = typecheck_silq_block(
        [SilqVar("x", False, True)],
        [("call", ("t", "H", ["x"])), ("auto_forget", "t")],
        None,
    )
    assert not ok_non_qfree and r_non_qfree == "CANNOT_UNCOMPUTE_NON_LIFTED(t)"

    ok_non_const, r_non_const = typecheck_silq_block(
        [SilqVar("c", False, False)],
        [("call", ("t", "dup", ["c"])), ("call", ("c2", "X", ["c"])), ("auto_forget", "t")],
        "c2",
    )
    assert not ok_non_const and r_non_const == "CANNOT_UNCOMPUTE_CONSUMED_DEPENDENCY(t<-c)"

    ok_cond_meas, r_cond_meas = typecheck_silq_block(
        [SilqVar("q", False, True), SilqVar("y", False, False)],
        [("qif", ("q", "measure", ["y"]))],
        None,
    )
    assert not ok_cond_meas and r_cond_meas == "CONDITIONAL_MEASUREMENT_NOT_MFREE(measure)"

    ok_lifted, r_lifted = typecheck_silq_block(
        [SilqVar("x0", False, True), SilqVar("x1", False, True)],
        [
            ("call", ("anc", "oracle_and", ["x0", "x1"])),
            ("qif", ("anc", "phase", ["anc"])),
            ("auto_forget", "anc"),
        ],
        None,
    )
    assert ok_lifted and r_lifted == "OK"

    # C1: Hadamard interference with vs without ancilla uncomputation
    # Qubits: 0 = x, 1 = ancilla a
    st_prep = apply_1q(init_zero_state(2), 2, 0, H_MAT)
    st_ent = apply_cnot(st_prep, 2, 0, 1)  # a = dup(x) -> (|00> + |11>)/sqrt(2)

    # Without uncomputation: apply H(x) directly while a remains entangled
    st_buggy_h = apply_1q(st_ent, 2, 0, H_MAT)
    rho_buggy_h = reduced_density_matrix(st_buggy_h, 2, (0,))
    p0_buggy_h = rho_buggy_h[0][0].real
    pur_buggy_h = purity(rho_buggy_h)
    assert math.isclose(p0_buggy_h, 0.5, abs_tol=1e-12)
    assert math.isclose(pur_buggy_h, 0.5, abs_tol=1e-12)

    # With Silq automatic Bennett uncomputation: CNOT^\dagger = CNOT restores |+> \otimes |0>
    st_uncomp = apply_cnot(st_ent, 2, 0, 1)
    st_sound_h = apply_1q(st_uncomp, 2, 0, H_MAT)
    rho_sound_h = reduced_density_matrix(st_sound_h, 2, (0,))
    p0_sound_h = rho_sound_h[0][0].real
    pur_sound_h = purity(rho_sound_h)
    assert math.isclose(p0_sound_h, 1.0, abs_tol=1e-12)
    assert math.isclose(pur_sound_h, 1.0, abs_tol=1e-12)

    # C2: 2-qubit Grover search for marked state |11> with ancilla t = x0 AND x1
    # Qubits: 0 = x0, 1 = x1, 2 = ancilla t
    st_g = init_zero_state(3)
    st_g = apply_1q(st_g, 3, 0, H_MAT)
    st_g = apply_1q(st_g, 3, 1, H_MAT)
    st_g = apply_ccx(st_g, 3, 0, 1, 2)  # compute ancilla t = x0 & x1
    st_g = apply_1q(st_g, 3, 2, Z_MAT)  # phase oracle: (-1)^t

    # Buggy: omit CCX uncomputation of t before diffusion
    st_g_buggy = grover_diffusion_2q(st_g, 3, 0, 1)
    rho_g_buggy = reduced_density_matrix(st_g_buggy, 3, (0, 1))
    p11_buggy = rho_g_buggy[3][3].real
    pur_g_buggy = purity(rho_g_buggy)
    assert math.isclose(p11_buggy, 0.625, abs_tol=1e-12)
    assert math.isclose(pur_g_buggy, 0.625, abs_tol=1e-12)

    # Sound: Bennett uncomputation CCX^\dagger = CCX disentangles t -> |0> before diffusion
    st_g_uncomp = apply_ccx(st_g, 3, 0, 1, 2)
    st_g_sound = grover_diffusion_2q(st_g_uncomp, 3, 0, 1)
    rho_g_sound = reduced_density_matrix(st_g_sound, 3, (0, 1))
    p11_sound = rho_g_sound[3][3].real
    pur_g_sound = purity(rho_g_sound)
    assert math.isclose(p11_sound, 1.0, abs_tol=1e-12)
    assert math.isclose(pur_g_sound, 1.0, abs_tol=1e-12)

    # C3: SQIR `invert` soundness check: U(invert(C)) * U(C) == I on 3-qubit circuit
    # Mirrors SQIR/UnitaryOps.v L17-51: invert(U_R θ ϕ λ) = U_R (-θ) (-λ) (-ϕ), invert(CNOT) = CNOT
    circ = [
        ("R", 0, (math.pi / 2, 0.0, math.pi)),       # H 0
        ("CNOT", 0, 1),
        ("R", 1, (0.37, 0.81, 1.23)),                # arbitrary U_R
        ("CNOT", 1, 2),
        ("R", 2, (0.0, 0.0, math.pi / 4)),           # T 2
    ]
    inv_circ = [
        ("R", g[1], (-g[2][0], -g[2][2], -g[2][1])) if g[0] == "R" else g
        for g in reversed(circ)
    ]

    def run_sqir(st: list[complex], ops: list[tuple]) -> list[complex]:
        cur = st
        for g in ops:
            if g[0] == "R":
                cur = apply_1q(cur, 3, g[1], u_r_mat(*g[2]))
            elif g[0] == "CNOT":
                cur = apply_cnot(cur, 3, g[1], g[2])
        return cur

    max_err = 0.0
    for basis in range(8):
        e_vec = [1.0 + 0j if i == basis else 0j for i in range(8)]
        roundtrip = run_sqir(run_sqir(e_vec, circ), inv_circ)
        err = max(abs(roundtrip[i] - e_vec[i]) for i in range(8))
        max_err = max(max_err, err)
    assert max_err < 1e-12

    return {
        "silq_static_rejections": {
            "use_consumed": r_use_cons,
            "silent_discard": r_discard,
            "non_qfree_uncomp": r_non_qfree,
            "non_const_dependency": r_non_const,
            "conditional_measurement": r_cond_meas,
            "lifted_oracle_accepted": r_lifted,
        },
        "hadamard_interference": {
            "without_uncomp": {"P0": round(p0_buggy_h, 6), "purity": round(pur_buggy_h, 6)},
            "with_qfree_uncomp": {"P0": round(p0_sound_h, 6), "purity": round(pur_sound_h, 6)},
        },
        "grover_2q_oracle": {
            "without_uncomp": {"P11": round(p11_buggy, 6), "purity": round(pur_g_buggy, 6)},
            "with_qfree_uncomp": {"P11": round(p11_sound, 6), "purity": round(pur_g_sound, 6)},
        },
        "sqir_invert_max_identity_error": max_err,
    }


def main() -> int:
    report = {
        "zk_r1cs_uniqueness": run_zk_probe(),
        "move_linear_bytecode_verifier": run_move_probe(),
        "silq_and_sqir_quantum_uncomputation": run_quantum_probe(),
    }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
