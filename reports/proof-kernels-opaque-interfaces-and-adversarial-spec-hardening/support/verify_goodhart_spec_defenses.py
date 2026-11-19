#!/usr/bin/env python3
"""Mechanized finite-state model of adversarial Goodhart exploits and algebraic spec defenses.

Demonstrates six canonical specification-gaming exploit classes against formal
compiler, verifier, and semantic-correspondence contracts over finite state
machines, and verifies mechanically that:
  1. A naive behavioral refinement check accepts all six exploits (including
     guard-weakened TCB semantics mutants under positive-only proofs).
  2. A hardened contract (productivity preservation, domain witness pinning,
     observation-codec injectivity, end-to-end byte-level pinned ISA decoding,
     hash-locked unmodified reference oracles, and negative mutation canaries)
     rejects 100% of exploits and kills 100% of operational-semantics mutants.
  3. The same hardened contract admits honest exact optimizing compilers,
     honest conservative (incomplete) static analyzers, and honest unmodified
     correspondence bridges.

Standalone Python 3.10+ standard-library script; exits 0 iff all checks pass.
"""

from __future__ import annotations

import hashlib
import inspect
import json
import sys
from dataclasses import dataclass
from typing import Callable, Mapping, Sequence


# ---------------------------------------------------------------------------
# 1. Core Refinement Domain: Partial Behaviors (Behavior, <=)
# ---------------------------------------------------------------------------

Query = int  # Finite input space: 0..7
Value = int  # Finite observable outputs (modulo 256)
DOMAIN_ALL: tuple[Query, ...] = tuple(range(8))


@dataclass(frozen=True)
class PartialBehavior:
    """Element of Partial(Set(Obs)) with ub = Top and empty set = Bottom.

    Preorder (refinement `lhs <= rhs`):
      - `rhs.is_ub` (Top): every `lhs` refines `UB` (compiler has full freedom).
      - otherwise `lhs` must not be `UB` and `lhs.outcomes <= rhs.outcomes`.
    """

    is_ub: bool
    outcomes: frozenset[int] = frozenset()

    @staticmethod
    def ub() -> PartialBehavior:
        return PartialBehavior(is_ub=True)

    @staticmethod
    def exact(v: int) -> PartialBehavior:
        return PartialBehavior(is_ub=False, outcomes=frozenset({v}))

    @staticmethod
    def nondet(vs: Sequence[int]) -> PartialBehavior:
        return PartialBehavior(is_ub=False, outcomes=frozenset(vs))

    @staticmethod
    def miracle() -> PartialBehavior:
        return PartialBehavior(is_ub=False, outcomes=frozenset())

    def refines(self, spec: PartialBehavior) -> bool:
        if spec.is_ub:
            return True
        if self.is_ub:
            return False
        return self.outcomes.issubset(spec.outcomes)

    def map_codec(self, codec: Callable[[int], int]) -> PartialBehavior:
        if self.is_ub:
            return PartialBehavior.ub()
        return PartialBehavior(
            is_ub=False,
            outcomes=frozenset(codec(v) for v in self.outcomes),
        )


BehaviorMap = Mapping[Query, PartialBehavior]


# ---------------------------------------------------------------------------
# 2. Source IR (Finite-State Register/Accumulator Language) & Mutable UB Guards
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class SrcInstr:
    op: str  # "LOAD_ARG", "LOAD_IMM", "ADD_IMM", "SUB_IMM", "DIV_ARG", "CHOICE_01", "RET"
    imm: int = 0


@dataclass(frozen=True)
class SrcGuardConfig:
    """Toggleable UB guards in the source operational semantics (for mutation testing)."""

    check_div_by_zero: bool = True
    check_unsigned_underflow: bool = True
    check_u8_overflow: bool = True
    check_pc_in_bounds: bool = True
    check_valid_opcode: bool = True


def eval_src_program(
    prog: Sequence[SrcInstr],
    arg: Query,
    guards: SrcGuardConfig = SrcGuardConfig(),
) -> PartialBehavior:
    """Small-step finite-state semantics for `prog` on input `arg`."""
    states: set[tuple[int, int]] = {(0, arg)}  # (pc, acc)
    finished: set[int] = set()
    steps = 0
    max_steps = 32

    while states and steps < max_steps:
        steps += 1
        next_states: set[tuple[int, int]] = set()
        for pc, acc in states:
            if pc < 0 or pc >= len(prog):
                if guards.check_pc_in_bounds:
                    return PartialBehavior.ub()
                finished.add(acc & 0xFF)
                continue
            ins = prog[pc]
            if ins.op == "LOAD_ARG":
                next_states.add((pc + 1, arg))
            elif ins.op == "LOAD_IMM":
                next_states.add((pc + 1, ins.imm))
            elif ins.op == "ADD_IMM":
                res = acc + ins.imm
                if res > 255:
                    if guards.check_u8_overflow:
                        return PartialBehavior.ub()
                    res &= 0xFF
                next_states.add((pc + 1, res))
            elif ins.op == "SUB_IMM":
                if acc < ins.imm:
                    if guards.check_unsigned_underflow:
                        return PartialBehavior.ub()
                    res = 0  # Saturating subtraction mutant (classic Lean Nat.sub bug)
                else:
                    res = acc - ins.imm
                next_states.add((pc + 1, res))
            elif ins.op == "DIV_ARG":
                if arg == 0:
                    if guards.check_div_by_zero:
                        return PartialBehavior.ub()
                    res = 0  # Totalized division-by-zero mutant (classic ITP total division)
                else:
                    res = acc // arg
                next_states.add((pc + 1, res))
            elif ins.op == "CHOICE_01":
                # Benign source nondeterminism: may add 0 or 1 (refinable downward by compiler)
                next_states.add((pc + 1, acc))
                next_states.add((pc + 1, (acc + 1) & 0xFF))
            elif ins.op == "RET":
                finished.add(acc)
            else:
                if guards.check_valid_opcode:
                    return PartialBehavior.ub()
                finished.add(acc & 0xFF)
        states = next_states

    if states:
        return PartialBehavior.ub()
    return PartialBehavior(is_ub=False, outcomes=frozenset(finished))


def src_semantics(
    prog: Sequence[SrcInstr],
    guards: SrcGuardConfig = SrcGuardConfig(),
) -> dict[Query, PartialBehavior]:
    return {q: eval_src_program(prog, q, guards) for q in DOMAIN_ALL}


# ---------------------------------------------------------------------------
# 3. Target Mini-ISA: Pinned Byte Decoder & Machine Semantics
# ---------------------------------------------------------------------------
# Opcodes (2-byte fixed width: [opcode, imm]):
#   0x01, _   -> acc = arg
#   0x02, imm -> acc = imm
#   0x03, imm -> acc = (acc + imm) & 0xFF
#   0x04, imm -> acc = (acc - imm) & 0xFF
#   0x05, _   -> if arg == 0: UB else acc = acc // arg
#   0xFF, _   -> halt and return acc


def pinned_isa_exec(code: bytes, arg: Query) -> PartialBehavior:
    """Immutable pinned target ISA decoder + machine executor over raw bytes."""
    if len(code) == 0 or (len(code) % 2) != 0:
        return PartialBehavior.ub()
    pc = 0
    acc = arg
    for _ in range(32):
        if pc < 0 or pc + 1 >= len(code):
            return PartialBehavior.ub()
        op = code[pc]
        imm = code[pc + 1]
        if op == 0x01:
            acc = arg
            pc += 2
        elif op == 0x02:
            acc = imm
            pc += 2
        elif op == 0x03:
            acc = (acc + imm) & 0xFF
            pc += 2
        elif op == 0x04:
            acc = (acc - imm) & 0xFF
            pc += 2
        elif op == 0x05:
            if arg == 0:
                return PartialBehavior.ub()
            acc = acc // arg
            pc += 2
        elif op == 0xFF:
            return PartialBehavior.exact(acc)
        else:
            return PartialBehavior.ub()
    return PartialBehavior.ub()


def pinned_isa_semantics(code: bytes) -> dict[Query, PartialBehavior]:
    return {q: pinned_isa_exec(code, q) for q in DOMAIN_ALL}


# ---------------------------------------------------------------------------
# 4. Compiler / Artifact Contract Model (Naive vs. Hardened)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class CompilerSubmission:
    """An untrusted compiler/synthesizer output claiming correctness for `src_prog`."""

    label: str
    src_prog: tuple[SrcInstr, ...]
    claimed_domain: frozenset[Query]
    obs_codec: Callable[[int], int]
    claimed_tgt_sem: dict[Query, PartialBehavior]  # Claimed AST / custom-parser semantics
    emitted_bytes: bytes  # Actual machine-code bytes written to disk


def check_naive_compiler_contract(sub: CompilerSubmission) -> tuple[bool, str]:
    """Naive refinement: accepts any claimed domain, codec, and AST/custom semantics."""
    s_sem = src_semantics(sub.src_prog)
    for q in sub.claimed_domain:
        lhs = sub.claimed_tgt_sem[q]
        rhs = s_sem[q].map_codec(sub.obs_codec)
        if not lhs.refines(rhs):
            return False, f"refinement failed at q={q}: {lhs} !<= {rhs}"
    return True, "accepted (naive refinement)"


def check_hardened_compiler_contract(
    sub: CompilerSubmission,
    required_witness_domain: frozenset[Query],
    observable_universe: Sequence[int],
) -> tuple[bool, str]:
    """Hardened contract blocking Exploits 1-4 while admitting sound compilers."""
    # Defense (2): Domain non-degeneracy / pinned witness domain (blocks domain collapse)
    if not required_witness_domain.issubset(sub.claimed_domain):
        missing = sorted(required_witness_domain - sub.claimed_domain)
        return False, f"REJECTED[domain-collapse]: missing required witness inputs {missing}"

    # Defense (3): Observation codec injectivity on observable outputs (blocks obs erasure)
    seen: dict[int, int] = {}
    for v in observable_universe:
        mapped = sub.obs_codec(v)
        if mapped in seen and seen[mapped] != v:
            return (
                False,
                f"REJECTED[obs-erasure]: non-injective codec maps {seen[mapped]} and {v} both to {mapped}",
            )
        seen[mapped] = v

    # Defense (4): End-to-end byte-level pinned ISA decoding (blocks lying emitter & spoofed parser)
    real_byte_sem = pinned_isa_semantics(sub.emitted_bytes)
    s_sem = src_semantics(sub.src_prog)

    for q in sub.claimed_domain:
        src_b = s_sem[q]
        claimed_b = sub.claimed_tgt_sem[q]
        real_b = real_byte_sem[q]

        # Defense (1): Productivity / non-emptiness preservation (blocks miracle targets)
        if not src_b.is_ub and len(src_b.outcomes) > 0:
            if claimed_b.is_ub or len(claimed_b.outcomes) == 0:
                return (
                    False,
                    f"REJECTED[miracle-target]: claimed target uninhabited/UB on productive source input q={q}",
                )
            if real_b.is_ub or len(real_b.outcomes) == 0:
                return (
                    False,
                    f"REJECTED[miracle-target]: emitted bytes uninhabited/UB on productive source input q={q}",
                )

        # Check byte-level refinement under injective codec AND consistency with claimed semantics
        rhs = src_b.map_codec(sub.obs_codec)
        real_mapped = real_b.map_codec(sub.obs_codec)
        if not real_mapped.refines(rhs):
            return (
                False,
                f"REJECTED[lying-emitter]: pinned ISA bytes at q={q} produce {real_b}, violating {rhs}",
            )
        if claimed_b != real_mapped:
            return (
                False,
                f"REJECTED[lying-emitter]: claimed AST/parser semantics {claimed_b} != pinned ISA bytes {real_mapped} at q={q}",
            )

    return True, "ACCEPTED (hardened compiler contract)"


# ---------------------------------------------------------------------------
# 5. Exploit 5: Circular Reference-Correspondence Adapter Hook
# ---------------------------------------------------------------------------

def upstream_ref_eval_move(local_init: bool, val: int) -> tuple[bool, int | None]:
    """Pinned upstream reference oracle (analogous to upstream lean-miri Move==Copy).

    In this reference oracle, `Move` behaves like `Copy` and leaves the source
    local initialized (returns `(still_initialized=True, value)`).
    """
    if not local_init:
        return (False, None)
    return (True, val)


def candidate_eval_move(local_init: bool, val: int) -> tuple[bool, int | None]:
    """Candidate semantics where `Move` deinitializes the source local."""
    if not local_init:
        return (False, None)
    return (False, val)


PINNED_REF_ORACLE_SHA256 = hashlib.sha256(
    inspect.getsource(upstream_ref_eval_move).encode("utf-8")
).hexdigest()


def check_correspondence_naive(
    ref_hook: Callable[[bool, int], tuple[bool, int | None]],
    cand_fn: Callable[[bool, int], tuple[bool, int | None]],
) -> tuple[bool, str]:
    """Naive correspondence: checks lockstep equality without locking the reference hook."""
    for init in (False, True):
        for val in (0, 7, 42):
            if ref_hook(init, val) != cand_fn(init, val):
                return False, f"mismatch at init={init}, val={val}"
    return True, "accepted (naive lockstep correspondence)"


def check_correspondence_hardened(
    ref_hook: Callable[[bool, int], tuple[bool, int | None]],
    cand_fn: Callable[[bool, int], tuple[bool, int | None]],
    expected_ref_sha256: str,
) -> tuple[bool, str]:
    """Hardened correspondence: pins upstream oracle source digest + non-interference witness."""
    actual_sha = hashlib.sha256(inspect.getsource(ref_hook).encode("utf-8")).hexdigest()
    if actual_sha != expected_ref_sha256:
        return (
            False,
            f"REJECTED[circular-adapter]: reference oracle digest {actual_sha[:12]} != pinned {expected_ref_sha256[:12]}",
        )
    # Also verify non-vacuous behavioral correspondence on unmodified oracle
    for init in (False, True):
        for val in (0, 7, 42):
            if ref_hook(init, val) != cand_fn(init, val):
                return (
                    False,
                    f"REJECTED[semantic-divergence]: candidate diverges from unmodified reference oracle at init={init}, val={val}",
                )
    return True, "ACCEPTED (hardened unmodified-oracle correspondence)"


# ---------------------------------------------------------------------------
# 6. Exploit 6: Positive-Only TCB Rot (Guard-Weakened Semantics Mutants)
# ---------------------------------------------------------------------------

POSITIVE_SUITE: list[tuple[str, tuple[SrcInstr, ...], bytes, frozenset[Query]]] = [
    (
        "inc_by_3",
        (SrcInstr("LOAD_ARG"), SrcInstr("ADD_IMM", 3), SrcInstr("RET")),
        bytes([0x01, 0x00, 0x03, 0x03, 0xFF, 0x00]),
        frozenset(DOMAIN_ALL),
    ),
    (
        "sub_safe_domain",
        (SrcInstr("LOAD_ARG"), SrcInstr("ADD_IMM", 5), SrcInstr("SUB_IMM", 2), SrcInstr("RET")),
        bytes([0x01, 0x00, 0x03, 0x05, 0x04, 0x02, 0xFF, 0x00]),
        frozenset(DOMAIN_ALL),
    ),
    (
        "div_nonzero_domain",
        (SrcInstr("LOAD_IMM", 24), SrcInstr("DIV_ARG"), SrcInstr("RET")),
        bytes([0x02, 0x18, 0x05, 0x00, 0xFF, 0x00]),
        frozenset(range(1, 8)),  # avoids arg == 0
    ),
]

# Negative refutation canaries: each (name, prog, bad_input) MUST evaluate to UB!
NEGATIVE_CANARIES: list[tuple[str, tuple[SrcInstr, ...], Query]] = [
    ("canary_div_by_zero", (SrcInstr("LOAD_IMM", 10), SrcInstr("DIV_ARG"), SrcInstr("RET")), 0),
    ("canary_unsigned_underflow", (SrcInstr("LOAD_IMM", 0), SrcInstr("SUB_IMM", 1), SrcInstr("RET")), 0),
    ("canary_u8_overflow", (SrcInstr("LOAD_IMM", 250), SrcInstr("ADD_IMM", 10), SrcInstr("RET")), 0),
    ("canary_pc_oob", (SrcInstr("LOAD_IMM", 1),), 0),  # falls off end without RET
    ("canary_invalid_opcode", (SrcInstr("BOGUS_OP"), SrcInstr("RET")), 0),
]

SEMANTIC_MUTANTS: list[tuple[str, SrcGuardConfig]] = [
    ("mutant_drop_div_zero_guard", SrcGuardConfig(check_div_by_zero=False)),
    ("mutant_drop_underflow_guard", SrcGuardConfig(check_unsigned_underflow=False)),
    ("mutant_drop_overflow_guard", SrcGuardConfig(check_u8_overflow=False)),
    ("mutant_drop_pc_oob_guard", SrcGuardConfig(check_pc_in_bounds=False)),
    ("mutant_drop_invalid_op_guard", SrcGuardConfig(check_valid_opcode=False)),
]


def run_positive_suite(guards: SrcGuardConfig) -> bool:
    """Returns True if every positive proof passes under `guards`."""
    for _, prog, code, dom in POSITIVE_SUITE:
        s_sem = src_semantics(prog, guards)
        t_sem = pinned_isa_semantics(code)
        for q in dom:
            if not t_sem[q].refines(s_sem[q]):
                return False
    return True


def run_negative_canaries(guards: SrcGuardConfig) -> list[str]:
    """Returns list of canary names that KILLED the mutant (i.e. failed to be UB)."""
    killed_by: list[str] = []
    for name, prog, q_bad in NEGATIVE_CANARIES:
        beh = eval_src_program(prog, q_bad, guards)
        if not beh.is_ub:
            killed_by.append(name)
    return killed_by


# ---------------------------------------------------------------------------
# 7. Conservative Static Analyzer / Verifier (Admissibility Check)
# ---------------------------------------------------------------------------

def conservative_verifier_checks_safe(
    prog: Sequence[SrcInstr],
    dom: frozenset[Query],
) -> tuple[bool, dict[Query, PartialBehavior]]:
    """Sound but incomplete interval abstract interpreter (upward refinement in (Behavior, <=)).

    Rejects any program containing DIV_ARG or SUB_IMM (even if safe on `dom`),
    and for accepted LOAD/ADD/CHOICE/RET programs computes an abstract interval
    `[lo, hi]` without executing concrete semantics. Whenever `hi <= 255` and
    every path terminates at RET, it emits a sound non-UB over-approximation
    `L_src.sem(prog) <= L_abs.sem(prog)` proving UB-freedom on `dom`.
    """
    if not prog or prog[-1].op != "RET":
        return False, {}
    for ins in prog[:-1]:
        if ins.op in ("DIV_ARG", "SUB_IMM") or ins.op not in (
            "LOAD_ARG",
            "LOAD_IMM",
            "ADD_IMM",
            "CHOICE_01",
        ):
            return False, {}  # Conservative refusal ("UNKNOWN")

    abs_sem: dict[Query, PartialBehavior] = {}
    for q in DOMAIN_ALL:
        if q not in dom:
            abs_sem[q] = PartialBehavior.ub()
            continue
        # Interval abstract domain over accumulator [lo, hi]
        lo, hi = q, q
        for ins in prog[:-1]:
            if ins.op == "LOAD_ARG":
                lo, hi = q, q
            elif ins.op == "LOAD_IMM":
                lo, hi = ins.imm, ins.imm
            elif ins.op == "ADD_IMM":
                lo += ins.imm
                hi += ins.imm
                if hi > 255:
                    return False, {}  # Conservative overflow alarm
            elif ins.op == "CHOICE_01":
                hi += 1
                if hi > 255:
                    return False, {}
        # Deliberately widen upper bound by +1 (still sound & non-UB) to demonstrate
        # true upward over-approximation L_src.sem <= L_abs.sem without exact equality.
        abs_sem[q] = PartialBehavior(
            is_ub=False,
            outcomes=frozenset(range(lo, min(255, hi + 1) + 1)),
        )
    return True, abs_sem


def verify_conservative_analyzer_sound(
    prog: tuple[SrcInstr, ...],
    dom: frozenset[Query],
) -> tuple[bool, str]:
    """Verify an abstract verifier under the hardened upward-refinement contract."""
    accepted, abs_sem = conservative_verifier_checks_safe(prog, dom)
    if not accepted:
        return True, "ADMITTED (honest conservative refusal on out-of-fragment program)"
    s_sem = src_semantics(prog)
    for q in dom:
        # Upward refinement: L_src.sem(prog)[q] <= abs_sem[q] AND abs_sem[q] is non-UB & non-empty
        if abs_sem[q].is_ub or len(abs_sem[q].outcomes) == 0:
            return False, f"REJECTED: vacuous/UB abstract summary at q={q}"
        if not s_sem[q].refines(abs_sem[q]):
            return False, f"REJECTED: unsound abstract summary at q={q}"
    return True, "ACCEPTED (sound conservative verifier proved non-UB upward refinement)"


# ---------------------------------------------------------------------------
# 8. Main Mechanical Proof Harness
# ---------------------------------------------------------------------------

def main() -> int:
    # Target source program: compute arg + 3 with benign nondeterminism CHOICE_01
    # On q in 0..7, outcomes are {q+3, q+4} (all productive, all in 3..11).
    sample_prog = (
        SrcInstr("LOAD_ARG"),
        SrcInstr("ADD_IMM", 3),
        SrcInstr("CHOICE_01"),
        SrcInstr("RET"),
    )
    witness_dom = frozenset(DOMAIN_ALL)
    obs_universe = tuple(range(256))
    id_codec: Callable[[int], int] = lambda v: v
    unit_codec: Callable[[int], int] = lambda _v: 0  # Collapses all outputs to Unit

    # Honest exact compiler bytes: resolves CHOICE_01 to +0 -> returns arg + 3
    honest_bytes = bytes([0x01, 0x00, 0x03, 0x03, 0xFF, 0x00])
    # Lying bytes: returns constant 0 ("xor eax, eax; ret")
    lying_bytes = bytes([0x02, 0x00, 0xFF, 0x00])
    # Wrong-output bytes: returns constant 99 (hidden by Unit codec!)
    wrong_99_bytes = bytes([0x02, 0x63, 0xFF, 0x00])

    exploits: list[tuple[str, bool, bool, str]] = []

    # --- Exploit 1: Miracle target compiler (uninhabited target behavior False) ---
    exp1 = CompilerSubmission(
        label="exploit_1_miracle_target",
        src_prog=sample_prog,
        claimed_domain=witness_dom,
        obs_codec=id_codec,
        claimed_tgt_sem={q: PartialBehavior.miracle() for q in DOMAIN_ALL},
        emitted_bytes=b"",  # Empty / invalid bytes
    )
    n1, _ = check_naive_compiler_contract(exp1)
    h1, r1 = check_hardened_compiler_contract(exp1, witness_dom, obs_universe)
    exploits.append((exp1.label, n1, h1, r1))

    # --- Exploit 2: Contradictory precondition / domain collapse (dom = False) ---
    exp2 = CompilerSubmission(
        label="exploit_2_domain_collapse",
        src_prog=sample_prog,
        claimed_domain=frozenset(),  # Empty domain!
        obs_codec=id_codec,
        claimed_tgt_sem=pinned_isa_semantics(lying_bytes),
        emitted_bytes=lying_bytes,
    )
    n2, _ = check_naive_compiler_contract(exp2)
    h2, r2 = check_hardened_compiler_contract(exp2, witness_dom, obs_universe)
    exploits.append((exp2.label, n2, h2, r2))

    # --- Exploit 3: Observation codec erasure (Obs := Unit hides 42 |-> 99) ---
    exp3 = CompilerSubmission(
        label="exploit_3_observation_erasure",
        src_prog=sample_prog,
        claimed_domain=witness_dom,
        obs_codec=unit_codec,
        claimed_tgt_sem={q: PartialBehavior.exact(0) for q in DOMAIN_ALL},
        emitted_bytes=wrong_99_bytes,
    )
    n3, _ = check_naive_compiler_contract(exp3)
    h3, r3 = check_hardened_compiler_contract(exp3, witness_dom, obs_universe)
    exploits.append((exp3.label, n3, h3, r3))

    # --- Exploit 4a: Lying byte emitter (proves AST theorem, writes unrelated bytes) ---
    exp4a = CompilerSubmission(
        label="exploit_4a_lying_byte_emitter",
        src_prog=sample_prog,
        claimed_domain=witness_dom,
        obs_codec=id_codec,
        claimed_tgt_sem=pinned_isa_semantics(honest_bytes),
        emitted_bytes=lying_bytes,
    )
    n4a, _ = check_naive_compiler_contract(exp4a)
    h4a, r4a = check_hardened_compiler_contract(exp4a, witness_dom, obs_universe)
    exploits.append((exp4a.label, n4a, h4a, r4a))

    # --- Exploit 4b: Circular parser oracle (spoofed byte decoder reinterprets wrong bytes) ---
    # Valid productive bytes returning constant 7, which the spoofed decoder claims compute `q + 3`.
    spoofed_target_bytes = bytes([0x02, 0x07, 0xFF, 0x00])

    def spoofed_parser_exec(raw: bytes, q: Query) -> PartialBehavior:
        if raw == spoofed_target_bytes:
            return PartialBehavior.exact(q + 3)
        return pinned_isa_exec(raw, q)

    exp4b = CompilerSubmission(
        label="exploit_4b_circular_parser_oracle",
        src_prog=sample_prog,
        claimed_domain=witness_dom,
        obs_codec=id_codec,
        claimed_tgt_sem={q: spoofed_parser_exec(spoofed_target_bytes, q) for q in DOMAIN_ALL},
        emitted_bytes=spoofed_target_bytes,
    )
    n4b, _ = check_naive_compiler_contract(exp4b)
    h4b, r4b = check_hardened_compiler_contract(exp4b, witness_dom, obs_universe)
    exploits.append((exp4b.label, n4b, h4b, r4b))

    # --- Exploit 5: Circular adapter hook overwriting reference oracle ---
    def spoofed_ref_hook(local_init: bool, val: int) -> tuple[bool, int | None]:
        # Spoofed adapter makes reference oracle imitate candidate semantics!
        return candidate_eval_move(local_init, val)

    n5, _ = check_correspondence_naive(spoofed_ref_hook, candidate_eval_move)
    h5, r5 = check_correspondence_hardened(
        spoofed_ref_hook, candidate_eval_move, PINNED_REF_ORACLE_SHA256
    )
    exploits.append(("exploit_5_circular_adapter_hook", n5, h5, r5))

    # --- Exploit 6: Positive-only TCB rot (guard-weakened semantics mutants) ---
    baseline_pos = run_positive_suite(SrcGuardConfig())
    baseline_canaries_failed = run_negative_canaries(SrcGuardConfig())
    assert baseline_pos, "Baseline unmutated semantics must pass positive suite"
    assert baseline_canaries_failed == [], f"Baseline semantics failed canaries: {baseline_canaries_failed}"

    mutants_surviving_pos = 0
    mutants_killed_by_canaries = 0
    mutant_details: list[dict[str, object]] = []
    for m_name, m_cfg in SEMANTIC_MUTANTS:
        pos_ok = run_positive_suite(m_cfg)
        killers = run_negative_canaries(m_cfg)
        if pos_ok:
            mutants_surviving_pos += 1
        if killers:
            mutants_killed_by_canaries += 1
        mutant_details.append(
            {
                "mutant": m_name,
                "passes_positive_suite": pos_ok,
                "killed_by_negative_canaries": killers,
            }
        )

    n6 = mutants_surviving_pos == len(SEMANTIC_MUTANTS)  # Naive positive-only accepts all mutants
    h6 = mutants_killed_by_canaries != len(SEMANTIC_MUTANTS)  # False iff hardened suite rejects all
    r6 = f"REJECTED[mutation-canaries]: {mutants_killed_by_canaries}/{len(SEMANTIC_MUTANTS)} mutants killed (vs 0/{len(SEMANTIC_MUTANTS)} by positive proofs)"
    exploits.append(("exploit_6_guard_weakened_mutants", n6, h6, r6))

    # --- Honest tools: must ALL be accepted by hardened contracts ---
    honest_compiler = CompilerSubmission(
        label="honest_optimizing_compiler",
        src_prog=sample_prog,
        claimed_domain=witness_dom,
        obs_codec=id_codec,
        claimed_tgt_sem=pinned_isa_semantics(honest_bytes),
        emitted_bytes=honest_bytes,
    )
    hc_ok, hc_msg = check_hardened_compiler_contract(honest_compiler, witness_dom, obs_universe)

    ha_safe_ok, ha_safe_msg = verify_conservative_analyzer_sound(
        POSITIVE_SUITE[0][1], witness_dom
    )
    ha_refuse_ok, ha_refuse_msg = verify_conservative_analyzer_sound(
        POSITIVE_SUITE[2][1], frozenset(range(1, 8))
    )

    # Honest unmodified correspondence on matching Copy-like fragment
    def matching_copy_candidate(local_init: bool, val: int) -> tuple[bool, int | None]:
        if not local_init:
            return (False, None)
        return (True, val)

    hcorr_ok, hcorr_msg = check_correspondence_hardened(
        upstream_ref_eval_move, matching_copy_candidate, PINNED_REF_ORACLE_SHA256
    )

    # Assertions verifying the complete theorem of the probe
    for label, naive_acc, hardened_acc, reason in exploits:
        assert naive_acc is True, f"Expected naive contract to accept {label}, got {naive_acc}"
        assert hardened_acc is False, f"Expected hardened contract to reject {label}, got {hardened_acc} ({reason})"

    assert mutants_surviving_pos == len(SEMANTIC_MUTANTS)
    assert mutants_killed_by_canaries == len(SEMANTIC_MUTANTS)
    assert hc_ok, f"Honest compiler wrongly rejected: {hc_msg}"
    assert ha_safe_ok, f"Honest analyzer (in-fragment) wrongly rejected: {ha_safe_msg}"
    assert ha_refuse_ok, f"Honest analyzer (conservative refusal) wrongly rejected: {ha_refuse_msg}"
    assert hcorr_ok, f"Honest correspondence wrongly rejected: {hcorr_msg}"

    summary = {
        "probe": "verify_goodhart_spec_defenses",
        "exploits_tested": len(exploits),
        "naive_exploits_accepted": sum(1 for _, n, _, _ in exploits if n),
        "hardened_exploits_rejected": sum(1 for _, _, h, _ in exploits if not h),
        "semantic_mutants_total": len(SEMANTIC_MUTANTS),
        "semantic_mutants_passing_positive_suite": mutants_surviving_pos,
        "semantic_mutants_killed_by_negative_canaries": mutants_killed_by_canaries,
        "honest_tools_admitted": 4,
        "exploit_results": [
            {
                "exploit": label,
                "naive_accepted": naive_acc,
                "hardened_accepted": hardened_acc,
                "hardened_diagnostic": reason,
            }
            for label, naive_acc, hardened_acc, reason in exploits
        ],
        "mutant_matrix": mutant_details,
        "honest_tool_results": [
            {"tool": honest_compiler.label, "accepted": hc_ok, "detail": hc_msg},
            {"tool": "honest_conservative_analyzer_in_fragment", "accepted": ha_safe_ok, "detail": ha_safe_msg},
            {"tool": "honest_conservative_analyzer_out_of_fragment_refusal", "accepted": ha_refuse_ok, "detail": ha_refuse_msg},
            {"tool": "honest_unmodified_oracle_correspondence", "accepted": hcorr_ok, "detail": hcorr_msg},
        ],
        "all_assertions_passed": True,
    }
    print(json.dumps(summary, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
