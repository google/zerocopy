#!/usr/bin/env python3
"""Finite-model counterexample and theorem checker for heterogeneous
verification composition laws.

The script needs only the Python 3.10+ standard library, takes no input, is
deterministic, and exits 0 only if every check below holds.  A check is either
an exhaustive verification of a law over a small finite universe ("theorem")
or the confirmation that a specific counterexample really has the claimed
shape ("witness").  Finite exhaustive checks do not prove the general laws;
they make the algebra executable and guard the report's statements against
transcription errors.

Sections
  A  Compilation codecs and dual (source contract, compilation refinement)
     export.
  B  Hyperproperties under refinement: subset-closed (for-all/for-all)
     versus possibilistic (for-all/exists) policies, the observation-alphabet
     gap, and relational (2-trace) preservation.
  C  Step-indexed safety, adequacy at a closed-program boundary, prophetic
     first-order client specifications, re-entrancy, frames, and
     partial versus total correctness.
  D  A step-indexed Kripke model of propositions: excluded middle, the later
     modality, and Loeb induction.

Usage:  python3 verify_heterogeneous_composition_laws.py
"""

from __future__ import annotations

import itertools
from typing import Callable, Iterable

RESULTS: list[tuple[bool, str, str]] = []


def check(name: str, ok: bool, detail: str) -> None:
    RESULTS.append((bool(ok), name, detail))
    print(f"[{'PASS' if ok else 'FAIL'}] {name}: {detail}")


def nonempty_subsets(xs: Iterable) -> list[frozenset]:
    xs = list(xs)
    out = []
    for r in range(1, len(xs) + 1):
        for c in itertools.combinations(xs, r):
            out.append(frozenset(c))
    return out


def all_subsets(xs: Iterable) -> list[frozenset]:
    return [frozenset()] + nonempty_subsets(xs)


def all_maps(dom: list, cod: list) -> list[dict]:
    return [dict(zip(dom, img)) for img in itertools.product(cod, repeat=len(dom))]


# ---------------------------------------------------------------------------
# Section A: codecs and dual contract export
# ---------------------------------------------------------------------------
#
# Behaviours are sets of outcomes ordered by inclusion (smaller = more
# refined).  A codec pi maps source outcomes to target outcomes and is lifted
# to sets by direct image, so it is monotone by construction.
#
#   CompRef        Tc   <= pi(A)        the binary refines the source semantics
#   TargetThm      Tc   <= pi(P)        "only the compiled theorem is exported"
#   SourceContract A    <= P            the source semantics refines the contract
#   ClientVerified C[P] <= Good         the client is verified against P
#   SourceWhole    C[A] <= Good         the linked source program is correct
#
# Linking contexts are union-homomorphisms C[X] = U { c(x) | x in X }.


def image(pi: dict, xs: frozenset) -> frozenset:
    return frozenset(pi[x] for x in xs)


def link(c: dict, xs: frozenset) -> frozenset:
    out: set = set()
    for x in xs:
        out |= c[x]
    return frozenset(out)


def section_a() -> None:
    src = ["s0", "s1", "s2"]
    tgt = ["t0", "t1", "t2"]

    # A1: for image-lifted codecs, order reflection is exactly injectivity.
    subsets = all_subsets(src)
    agree = True
    n_inj = 0
    for pi in all_maps(src, tgt):
        injective = len(set(pi.values())) == len(src)
        n_inj += injective
        reflecting = all(
            a <= b for a in subsets for b in subsets if image(pi, a) <= image(pi, b)
        )
        agree &= injective == reflecting
    check(
        "A1 order-reflection iff injective codec",
        agree and n_inj == 6,
        "27 codecs on 3 atoms: pi(A)<=pi(B) => A<=B holds for exactly the 6 injective ones",
    )

    # A2: witness, forgetful codec with exact (deterministic) compilation.
    # Source distinguishes an uninitialised result from an initialised 0; the
    # target materialises both as the byte 0x00.  Source-level use of the
    # uninitialised value is undefined behaviour, i.e. the top behaviour.
    enc = {"init0": "b00", "init1": "b01", "uninit": "b00"}
    whole_tgt_all = frozenset({"t_ok", "t_other", "t_bad"})

    def pi_callee(xs: frozenset) -> frozenset:
        return frozenset(enc[x] for x in xs)

    def pi_whole(xs: frozenset) -> frozenset:
        if "UB" in xs:
            return whole_tgt_all
        return frozenset({"ret_ok": "t_ok", "ret_other": "t_other"}[x] for x in xs)

    client = {
        "init0": frozenset({"ret_ok"}),
        "init1": frozenset({"ret_other"}),
        "uninit": frozenset({"UB"}),
    }
    sem_src_callee = frozenset({"uninit"})
    contract = frozenset({"init0"})
    sem_tgt_callee = pi_callee(sem_src_callee)  # exact compilation
    good_src = frozenset({"ret_ok"})
    target_thm = sem_tgt_callee <= pi_callee(contract)
    source_contract = sem_src_callee <= contract
    client_verified = link(client, contract) <= good_src
    sem_src_whole = link(client, sem_src_callee)
    # A whole-program (inlining) compiler may emit anything below pi(top).
    sem_tgt_whole = frozenset({"t_bad"})
    whole_compile_ok = sem_tgt_whole <= pi_whole(sem_src_whole)
    end_to_end = sem_tgt_whole <= pi_whole(good_src)
    check(
        "A2 forgetful codec witness (uninit vs init 0)",
        target_thm and client_verified and whole_compile_ok
        and not source_contract and not end_to_end,
        "TargetThm, ClientVerified and whole-program CompRef all hold; SourceContract "
        "fails; linked binary may emit t_bad",
    )

    # A3: witness, injective codec with refining (nondeterminism-resolving)
    # compilation.  Recompiling the same source is equally correct and breaks
    # a client that was linked against the first binary's theorem.
    ident = {1: 1, 2: 2}
    sem_src_f = frozenset({1, 2})
    contract_f = frozenset({1})
    bin_one = frozenset({1})
    bin_two = frozenset({2})
    client_f = {1: frozenset({"ok"}), 2: frozenset({"assert_fail"})}
    ok3 = (
        bin_one <= image(ident, sem_src_f)
        and bin_two <= image(ident, sem_src_f)
        and bin_one <= image(ident, contract_f)
        and not sem_src_f <= contract_f
        and link(client_f, contract_f) == frozenset({"ok"})
        and link(client_f, bin_one) == frozenset({"ok"})
        and link(client_f, bin_two) == frozenset({"assert_fail"})
        and "assert_fail" in link(client_f, sem_src_f)
    )
    check(
        "A3 refining compilation witness (identity codec)",
        ok3,
        "binary {1} satisfies the exported theorem; equally correct binary {2} of the "
        "same source makes the verified client fail",
    )

    # A4: exhaustive classification over 3 source atoms, 3 target atoms.
    good = frozenset({"good"})
    whole = ["good", "bad"]
    clients = [dict(zip(src, img)) for img in itertools.product(nonempty_subsets(whole), repeat=3)]
    ne_src = nonempty_subsets(src)
    ne_tgt = nonempty_subsets(tgt)
    paired_total = paired_sound = 0
    target_only_total = target_only_bad = 0
    exact_inj_bad = exact_noninj_bad = strict_inj_bad = 0
    for pi in all_maps(src, tgt):
        injective = len(set(pi.values())) == len(src)
        for a in ne_src:
            pa = image(pi, a)
            for p in ne_src:
                pp = image(pi, p)
                contract_ok = a <= p
                for tc in ne_tgt:
                    if not tc <= pa:
                        continue  # CompRef is always assumed
                    thm = tc <= pp
                    exact = tc == pa
                    for c in clients:
                        if not link(c, p) <= good:
                            continue  # ClientVerified is always assumed
                        whole_ok = link(c, a) <= good
                        if contract_ok:
                            paired_total += 1
                            paired_sound += whole_ok and thm
                        if thm:
                            target_only_total += 1
                            if not whole_ok:
                                target_only_bad += 1
                                if exact and injective:
                                    exact_inj_bad += 1
                                elif exact:
                                    exact_noninj_bad += 1
                                elif injective:
                                    strict_inj_bad += 1
    check(
        "A4a paired export is sound",
        paired_total > 0 and paired_sound == paired_total,
        f"{paired_total} instances with SourceContract+CompRef+ClientVerified: all give "
        "SourceWhole and re-derive TargetThm",
    )
    check(
        "A4b target-only export is insufficient",
        target_only_bad > 0,
        f"{target_only_bad} of {target_only_total} instances with CompRef+TargetThm+"
        "ClientVerified violate SourceWhole",
    )
    check(
        "A4c exact compilation + injective codec recovers the contract",
        exact_inj_bad == 0 and exact_noninj_bad > 0 and strict_inj_bad > 0,
        f"violations: exact&injective={exact_inj_bad}, exact&forgetful={exact_noninj_bad}, "
        f"refining&injective={strict_inj_bad}",
    )

    # A5: context-parametric (open) compilation certificate.  If the compiled
    # client ct satisfies the lax square ct(pi(x)) <= c(x) for every source
    # outcome x, then TargetThm alone yields the linked-binary claim.
    src2, tgt2 = ["s0", "s1"], ["t0", "t1"]
    cl_src = [dict(zip(src2, img)) for img in itertools.product(nonempty_subsets(whole), repeat=2)]
    cl_tgt = [dict(zip(tgt2, img)) for img in itertools.product(nonempty_subsets(whole), repeat=2)]
    lax_total = lax_ok = nolax_bad = 0
    for pi in all_maps(src2, tgt2):
        for p in nonempty_subsets(src2):
            for tc in nonempty_subsets(tgt2):
                if not tc <= image(pi, p):
                    continue
                for c in cl_src:
                    if not link(c, p) <= good:
                        continue
                    for ct in cl_tgt:
                        lax = all(ct[pi[x]] <= c[x] for x in src2)
                        binary_ok = link(ct, tc) <= good
                        if lax:
                            lax_total += 1
                            lax_ok += binary_ok
                        elif not binary_ok:
                            nolax_bad += 1
    check(
        "A5 open (context-parametric) certificate makes TargetThm sufficient",
        lax_total > 0 and lax_ok == lax_total and nolax_bad > 0,
        f"{lax_total} instances with the lax square: linked binary correct in all; "
        f"{nolax_bad} violations without it",
    )
    # The A2 failure is exactly a lax-square violation at the shared byte.
    ct_a2 = {"b00": frozenset({"t_bad"}), "b01": frozenset({"t_other"})}
    lax_a2 = all(ct_a2[enc[x]] <= pi_whole(client[x]) for x in enc)
    ct_sep = {"b00": frozenset({"t_ok"}), "b01": frozenset({"t_other"})}
    lax_sep = all(ct_sep[enc[x]] <= pi_whole(client[x]) for x in enc)
    check(
        "A5b A2 revisited: separate compilation restores the lax square",
        (not lax_a2) and lax_sep and link(ct_sep, sem_tgt_callee) == frozenset({"t_ok"}),
        "inlining client violates the square at byte b00; ABI-level client satisfies it "
        "and the linked binary returns t_ok",
    )


# ---------------------------------------------------------------------------
# Section B: hyperproperties under refinement
# ---------------------------------------------------------------------------
#
# A trace is (pub, sec, leak).  A system is a set of traces.
#   ct_forall(T)  for-all/for-all: equal pub implies equal leak  (2-safety)
#   pni(T)        for-all/exists : the set of possible leaks for a public
#                 input does not depend on the secret (possibilistic)


def ct_forall(traces: frozenset) -> bool:
    return all(
        t1[2] == t2[2] for t1 in traces for t2 in traces if t1[0] == t2[0]
    )


def leaks_for(traces: frozenset, pub: int, sec: int) -> frozenset:
    return frozenset(t[2] for t in traces if t[0] == pub and t[1] == sec)


def input_total(traces: frozenset) -> bool:
    return all(leaks_for(traces, p, s) for p in (0, 1) for s in (0, 1))


def pni(traces: frozenset) -> bool:
    return all(
        leaks_for(traces, p, 0) == leaks_for(traces, p, 1) for p in (0, 1)
    )


def section_b() -> None:
    # B1: the introductory example of Clarkson and Schneider: a system that
    # nondeterministically outputs 0, 1 or the secret bit h, and its
    # refinement that always outputs h.  Traces here are (h, out).
    spec = frozenset((h, o) for h in (0, 1) for o in (0, 1))
    refined = frozenset((h, h) for h in (0, 1))

    def outputs_independent(sys_: frozenset) -> bool:
        return {o for (h, o) in sys_ if h == 0} == {o for (h, o) in sys_ if h == 1}

    check(
        "B1 refinement invalidates a possibilistic policy",
        refined <= spec and outputs_independent(spec) and not outputs_independent(refined),
        "{0,1,h} system satisfies 'possible outputs independent of h'; subset 'always h' does not",
    )

    universe = [(p, s, l) for p in (0, 1) for s in (0, 1) for l in (0, 1)]
    systems = all_subsets(universe)

    # B2: every subset of a for-all/for-all constant-time system is constant
    # time (subset closure), so same-alphabet refinement cannot break it.
    pairs = broken = 0
    for big in systems:
        if not ct_forall(big):
            continue
        for small in all_subsets(sorted(big)):
            pairs += 1
            broken += not ct_forall(small)
    check(
        "B2 for-all/for-all 2-safety is subset closed",
        pairs > 0 and broken == 0,
        f"{pairs} (system, refinement) pairs over 8 traces: 0 violations",
    )

    # B3: possibilistic noninterference is not subset closed, even when the
    # refinement keeps every input enabled.
    pni_pairs = pni_broken = 0
    for big in systems:
        if not (input_total(big) and pni(big)):
            continue
        for small in all_subsets(sorted(big)):
            if not input_total(small):
                continue
            pni_pairs += 1
            pni_broken += not pni(small)
    jitter = frozenset(universe)
    secret_resolved = frozenset((p, s, s) for p in (0, 1) for s in (0, 1))
    check(
        "B3 possibilistic noninterference is destroyed by refinement",
        pni_broken > 0
        and pni(jitter) and secret_resolved <= jitter and not pni(secret_resolved)
        and not ct_forall(jitter),
        f"{pni_broken} of {pni_pairs} input-total refinements break it; witness: leak "
        "jitter {0,1} resolved to leak = sec",
    )

    # B4: the observation-alphabet gap.  Deterministic programs map an input
    # to (out, leak).  Compiler correctness constrains only the (pub, sec,
    # out) projection.
    inputs = [(p, s) for p in (0, 1) for s in (0, 1)]

    def io_proj(prog: dict) -> frozenset:
        return frozenset((p, s, prog[(p, s)][0]) for (p, s) in inputs)

    def leak_sys(prog: dict) -> frozenset:
        return frozenset((p, s, prog[(p, s)][1]) for (p, s) in inputs)

    src_prog = {(p, s): (p & s, 0) for (p, s) in inputs}   # branchless select
    tgt_prog = {(p, s): (p & s, s) for (p, s) in inputs}   # branch on secret
    check(
        "B4a I/O refinement does not constrain leakage",
        io_proj(tgt_prog) <= io_proj(src_prog)
        and ct_forall(leak_sys(src_prog)) and not ct_forall(leak_sys(tgt_prog))
        and not leak_sys(tgt_prog) <= leak_sys(src_prog),
        "equal I/O behaviours; source constant time, target leaks sec; target leak "
        "traces are not a subset of the source's",
    )
    leak_fns = all_maps(inputs, [0, 1])
    gap = sum(
        1
        for ls in leak_fns for lt in leak_fns
        if ct_forall(frozenset((p, s, ls[(p, s)]) for (p, s) in inputs))
        and not ct_forall(frozenset((p, s, lt[(p, s)]) for (p, s) in inputs))
    )
    check(
        "B4b alphabet gap is generic",
        gap == 4 * 12,
        f"{gap} (source, target) leak assignments with identical I/O where only the "
        "source is constant time (4 constant-time x 12 leaky)",
    )

    # B5: relational (2-trace) preservation.  A pass is leak-relational if,
    # for every pair of inputs with equal public part, equal source leakage
    # implies equal target leakage.  Uniform leakage transformers satisfy it.
    seqs = [(), (0,), (1,), (0, 0), (0, 1), (1, 0), (1, 1)]
    src_leaks = all_maps(inputs, [(0, 0), (0, 1), (1, 0), (1, 1)])

    def ct_prog(leak: dict) -> bool:
        return all(
            leak[i1] == leak[i2] for i1 in inputs for i2 in inputs if i1[0] == i2[0]
        )

    def relational(ls: dict, lt: dict) -> bool:
        return all(
            lt[i1] == lt[i2]
            for i1 in inputs for i2 in inputs
            if i1[0] == i2[0] and ls[i1] == ls[i2]
        )

    transformers = [dict(zip((0, 1), img)) for img in itertools.product(seqs, repeat=2)]
    tr_total = tr_rel = tr_pres = 0
    for ls in src_leaks:
        for f in transformers:
            lt = {i: tuple(itertools.chain.from_iterable(f[e] for e in ls[i])) for i in inputs}
            tr_total += 1
            tr_rel += relational(ls, lt)
            tr_pres += (not ct_prog(ls)) or ct_prog(lt)
    check(
        "B5a uniform leakage transformers are relational and preserve constant time",
        tr_total == 256 * 49 and tr_rel == tr_total and tr_pres == tr_total,
        f"{tr_total} (source, per-event transformer) pairs: all relational, all preserve "
        "for-all/for-all constant time",
    )
    tgt_leaks = all_maps(inputs, [0, 1, 2])
    rel_pairs = rel_bad = 0
    for ls in src_leaks:
        if not ct_prog(ls):
            continue
        for lt in tgt_leaks:
            if relational(ls, lt):
                rel_pairs += 1
                rel_bad += not ct_prog(lt)
    check(
        "B5b the relational condition suffices for preservation",
        rel_pairs > 0 and rel_bad == 0,
        f"{rel_pairs} relational (constant-time source, target) pairs: 0 leaky targets",
    )
    ls_ct = {i: (0, 0) for i in inputs}
    lt_dep = {(p, s): s for (p, s) in inputs}
    check(
        "B5c a secret-dependent pass is not relational",
        ct_prog(ls_ct) and not relational(ls_ct, lt_dep) and not ct_prog(lt_dep),
        "target leak = sec fails the 2-trace condition against a constant-time source",
    )


# ---------------------------------------------------------------------------
# Section C: step-indexed safety, adequacy, prophecies, re-entrancy, frames
# ---------------------------------------------------------------------------
#
# A transition system assigns each state one of:
#   ("final", v)        terminated with value v (v in {0, 1})
#   ("stuck",)          no step and not final: undefined behaviour
#   ("step", succs)     may step to any state in the nonempty set succs
# wp(n, s, post): safe for n steps, and any final state met within those
# steps satisfies post.  wp(0, ...) is trivially true (zero steps of fuel).


def wp(n: int, ts: tuple, s: int, post: Callable[[int], bool]) -> bool:
    if n == 0:
        return True
    kind = ts[s]
    if kind[0] == "final":
        return post(kind[1])
    if kind[0] == "stuck":
        return False
    return all(wp(n - 1, ts, t, post) for t in kind[1])


def reach(ts: tuple, s0: int) -> set:
    seen, todo = {s0}, [s0]
    while todo:
        s = todo.pop()
        if ts[s][0] == "step":
            for t in ts[s][1]:
                if t not in seen:
                    seen.add(t)
                    todo.append(t)
    return seen


def section_c() -> None:
    states = [0, 1, 2]
    kinds = [("final", 0), ("final", 1), ("stuck",)] + [
        ("step", tuple(sorted(c))) for c in nonempty_subsets(states)
    ]
    post_one = lambda v: v == 1  # noqa: E731
    post_false = lambda v: False  # noqa: E731
    bound = len(states) + 1

    # C1: adequacy.  Quantifying the step index over all n is equivalent to
    # the index-free statement about reachable states of the closed system.
    total = agree = finite_index_gap = diverge_vacuous = 0
    for ts in itertools.product(kinds, repeat=len(states)):
        total += 1
        all_n = all(wp(n, ts, 0, post_one) for n in range(bound + 1))
        r = reach(ts, 0)
        meta = all(
            ts[s][0] != "stuck" and (ts[s][0] != "final" or post_one(ts[s][1])) for s in r
        )
        agree += all_n == meta
        if not meta and any(wp(k, ts, 0, post_one) for k in range(1, bound)):
            finite_index_gap += 1
        if all(wp(n, ts, 0, post_false) for n in range(bound + 1)):
            diverge_vacuous += 1
    check(
        "C1a adequacy: (for all n, wp n) iff reachable states are safe and final states satisfy post",
        total == 10 ** 3 and agree == total,
        f"{total} closed 3-state systems: equivalence holds in all",
    )
    chain = (("step", (1,)), ("step", (2,)), ("stuck",))
    check(
        "C1b a fixed finite index is not a safety proof",
        finite_index_gap > 0
        and wp(1, chain, 0, post_one) and wp(2, chain, 0, post_one)
        and not wp(3, chain, 0, post_one),
        f"{finite_index_gap} unsafe systems satisfy wp at some index k>=1; witness 0->1->stuck "
        "passes at k=1,2 and fails at k=3",
    )
    loop = (("step", (0,)), ("final", 0), ("final", 0))
    check(
        "C1c partial correctness is vacuous on divergence",
        diverge_vacuous > 0 and all(wp(n, loop, 0, post_false) for n in range(8))
        and not any(loop[s][0] == "final" for s in reach(loop, 0)),
        f"{diverge_vacuous} systems satisfy wp with postcondition False at every index; "
        "witness: a self-loop that never returns",
    )

    # C2: prophetic first-order client verification against a library that
    # is implemented with raw pointer steps (the max_mut example).
    dom = range(-3, 4)
    proph = range(-3, 11)

    def spec_max_mut(a, a_fin, b, b_fin, c, c_fin) -> bool:
        if a >= b:
            return (c, c_fin) == (a, a_fin) and b_fin == b
        return (c, c_fin) == (b, b_fin) and a_fin == a

    def lib_good(heap: dict) -> str:
        return "A" if heap["A"] >= heap["B"] else "B"

    def lib_returns_smaller(heap: dict) -> str:
        return "B" if heap["A"] >= heap["B"] else "A"

    def lib_writes_loser(heap: dict) -> str:
        win = "A" if heap["A"] >= heap["B"] else "B"
        lose = "B" if win == "A" else "A"
        heap[lose] = heap[win] + 7  # aliasing-violating write through the dropped borrow
        return win

    def run_client(lib: Callable[[dict], str], a: int, b: int) -> bool:
        heap = {"A": a, "B": b}
        ptr = lib(heap)
        heap[ptr] += 7
        return abs(heap["A"] - heap["B"]) >= 7

    def lib_satisfies_spec(lib: Callable[[dict], str]) -> bool:
        # Semantic obligation: for every call and every later write w through
        # the returned pointer, the spec holds when each prophecy is resolved
        # to the value actually observed when the borrow ends.
        for a in dom:
            for b in dom:
                for w in proph:
                    heap = {"A": a, "B": b}
                    ptr = lib(heap)
                    c = heap[ptr]
                    heap[ptr] = w
                    if not spec_max_mut(a, heap["A"], b, heap["B"], c, w):
                        return False
        return True

    def client_vc_forall() -> bool:
        # for all a, b and all prophesied finals a', b': spec and the
        # resolution c' = c + 7 imply |a' - b'| >= 7.
        for a in dom:
            for b in dom:
                for a_fin in proph:
                    for b_fin in proph:
                        c, c_fin = (a, a_fin) if a >= b else (b, b_fin)
                        if spec_max_mut(a, a_fin, b, b_fin, c, c_fin) and c_fin == c + 7:
                            if abs(a_fin - b_fin) < 7:
                                return False
        return True

    vc = client_vc_forall()
    good_sem = lib_satisfies_spec(lib_good)
    good_run = all(run_client(lib_good, a, b) for a in dom for b in dom)
    check(
        "C2a prophetic client VC + semantic library spec => closed-program assertion",
        vc and good_sem and good_run,
        "client VC valid for all prophecies; raw-pointer max_mut satisfies its prophetic "
        "spec; all 49 closed runs satisfy the assertion",
    )
    bad1_sem = lib_satisfies_spec(lib_returns_smaller)
    bad1_run = all(run_client(lib_returns_smaller, a, b) for a in dom for b in dom)
    bad2_sem = lib_satisfies_spec(lib_writes_loser)
    bad2_run = all(run_client(lib_writes_loser, a, b) for a in dom for b in dom)
    check(
        "C2b the client VC alone does not protect against an incorrect unsafe library",
        vc and not bad1_sem and not bad1_run and not bad2_sem and not bad2_run,
        "wrong-pointer and aliasing-violating libraries leave the client VC valid, fail "
        "the semantic spec check, and break closed runs",
    )

    # C3: prophecies are universally quantified on the client side.  The
    # borrow is handed to an unknown callee that may store any value.
    def vc_unknown_callee(quant: Callable[[Iterable[bool]], bool], claim: Callable[[int], bool]) -> bool:
        return all(quant(claim(a_fin) for a_fin in proph) for _a in dom)

    claim_five = lambda a_fin: a_fin == 5  # noqa: E731
    machine_claim = all(w == 5 for w in proph)
    check(
        "C3 prophecy quantifier discipline",
        (not vc_unknown_callee(all, claim_five)) and vc_unknown_callee(any, claim_five)
        and not machine_claim,
        "for-all prophecy VC rejects 'final value is 5' after an unknown callee; an "
        "exists-prophecy VC would accept it although runs storing other values exist",
    )

    # C4: a representation invariant that is broken between two raw writes.
    # Invariant at call boundaries: data[0 .. len) is initialised.
    def push_run(callback_mid_update: bool) -> tuple[bool, bool]:
        heap = {"len": 0, "data": [None, None]}
        observed_ok = True

        def client_callback() -> None:
            nonlocal observed_ok
            # Client reasoning assumes the invariant at every entry point.
            observed_ok &= all(heap["data"][i] is not None for i in range(heap["len"]))

        heap["len"] += 1                     # raw step 1: invariant broken
        if callback_mid_update:
            client_callback()                # re-entrancy while broken
        heap["data"][heap["len"] - 1] = 7    # raw step 2: invariant restored
        client_callback()                    # ordinary observation after return
        boundary_inv = all(heap["data"][i] is not None for i in range(heap["len"]))
        return observed_ok, boundary_inv

    plain = push_run(False)
    reentrant = push_run(True)
    check(
        "C4 call-boundary invariants do not survive mid-update callbacks",
        plain == (True, True) and reentrant == (False, True),
        "invariant holds at the return boundary in both variants; a callback between the "
        "two raw writes observes it broken",
    )

    # C5: frames.  A caller verified under 'the extern call leaves my stable
    # cells unchanged' is sound exactly for callees whose write set is
    # disjoint from those cells.
    cells = ["g0", "g1", "g2"]
    comp_total = comp_ok_disjoint = comp_bad_overlap = disjoint_total = overlap_total = 0
    for writes in all_subsets(cells):
        for stable in all_subsets(cells):
            comp_total += 1
            heap = {c: 1 for c in cells}
            for c in writes:
                heap[c] = 0                   # callee owns and overwrites these cells
            caller_assert = all(heap[c] == 1 for c in stable)
            if writes & stable:
                overlap_total += 1
                comp_bad_overlap += not caller_assert
            else:
                disjoint_total += 1
                comp_ok_disjoint += caller_assert
    check(
        "C5 frame compatibility is the composition side condition",
        comp_total == 64 and comp_ok_disjoint == disjoint_total == 27
        and comp_bad_overlap == overlap_total == 37,
        "27 footprint-disjoint (callee writes, caller-stable) pairs compose; all 37 "
        "overlapping pairs break the caller's assertion",
    )

    # C6: partial-correctness callee under a total-correctness caller.  The
    # caller is proved totally correct against the callee's contract treated
    # as one terminating step; the real callee satisfies that contract only
    # partially because it never returns.
    def total(ts: tuple, s: int, post: Callable[[int], bool], seen: frozenset = frozenset()) -> bool:
        kind = ts[s]
        if kind[0] == "final":
            return post(kind[1])
        if kind[0] == "stuck" or s in seen:
            return False  # a revisited state is an infinite run
        return all(total(ts, t, post, seen | {s}) for t in kind[1])

    abstract_link = (("step", (1,)), ("step", (2,)), ("final", 1))   # call; contract step; return 1
    concrete_link = (("step", (1,)), ("step", (1,)), ("final", 1))   # call; callee spins forever
    callee_pc = all(wp(n, loop, 0, post_false) for n in range(8))
    check(
        "C6 partial + total correctness do not compose to total correctness",
        callee_pc
        and total(abstract_link, 0, post_one)
        and all(wp(n, concrete_link, 0, post_one) for n in range(8))
        and not total(concrete_link, 0, post_one),
        "callee satisfies {True} f {False} partially; caller is total against the "
        "contract; the linked system is only partially correct (it diverges)",
    )

    # C7: the max_mut client and library as one closed small-step system.
    # An assertion failure is a stuck state.  Quantifying wp over all step
    # indices agrees with direct execution; any index below the run length
    # is satisfied even by the incorrect library.
    def chain_for(lib: Callable[[dict], str], a: int, b: int) -> tuple:
        ok = run_client(lib, a, b)
        steps = ["call", "lib_read_a", "lib_read_b", "lib_return", "client_write", "end_borrow"]
        ts = [("step", (i + 1,)) for i in range(len(steps))]
        ts.append(("final", 1) if ok else ("stuck",))
        return tuple(ts)

    depth = 7
    agree_good = all(
        all(wp(n, chain_for(lib_good, a, b), 0, post_one) for n in range(depth + 2))
        for a in dom for b in dom
    )
    bad_chains = [chain_for(lib_returns_smaller, a, b) for a in dom for b in dom]
    bad_detected = sum(not wp(depth, ts, 0, post_one) for ts in bad_chains)
    bad_hidden = sum(wp(depth - 1, ts, 0, post_one) for ts in bad_chains)
    bad_direct = sum(not run_client(lib_returns_smaller, a, b) for a in dom for b in dom)
    check(
        "C7 closed-system adequacy for the linked client and raw-pointer library",
        agree_good and bad_detected == bad_direct > 0 and bad_hidden == len(bad_chains),
        f"correct library: wp holds at every index for all 49 inputs; incorrect library: "
        f"{bad_detected} inputs fail at index {depth} and none fails below it",
    )


# ---------------------------------------------------------------------------
# Section D: a step-indexed Kripke model of propositions
# ---------------------------------------------------------------------------
#
# A proposition is a downward-closed set of step indices in {0, ..., N}: if it
# holds with n steps of fuel left it holds with fewer.  Validity means truth
# at every index.


def section_d() -> None:
    top = 6
    idx = range(top + 1)
    props = [frozenset(range(k)) for k in range(top + 2)]  # {}, {0}, ..., {0..N}
    everything = frozenset(idx)

    def impl(p: frozenset, q: frozenset) -> frozenset:
        return frozenset(n for n in idx if all((m not in p) or (m in q) for m in range(n + 1)))

    def neg(p: frozenset) -> frozenset:
        return impl(p, frozenset())

    def later(p: frozenset) -> frozenset:
        return frozenset(n for n in idx if n == 0 or (n - 1) in p)

    closed = all(impl(p, q) in props and later(p) in props and (p | q) in props
                 for p in props for q in props)
    check(
        "D0 the model is closed under implication, disjunction and later",
        closed and len(props) == top + 2,
        f"{len(props)} downward-closed propositions over indices 0..{top}",
    )
    em_valid = [p for p in props if (p | neg(p)) == everything]
    check(
        "D1 excluded middle is not valid step-indexed",
        em_valid == [frozenset(), everything],
        "P or not P is valid only for the two index-independent propositions",
    )
    drop_later = [p for p in props if impl(later(p), p) == everything]
    check(
        "D2 later cannot be eliminated at a fixed index",
        drop_later == [everything],
        "(later P => P) is valid only for P = True",
    )
    loeb = all(impl(impl(later(p), p), p) == everything for p in props)
    check(
        "D3 Loeb induction is valid",
        loeb,
        "((later P => P) => P) holds at every index for every proposition",
    )

    def later_n(n: int, p: frozenset) -> frozenset:
        for _ in range(n):
            p = later(p)
        return p

    sat = all(later_n(n, frozenset()) == frozenset(range(n)) for n in range(top + 1))
    check(
        "D4 later^n False holds at exactly the indices below n",
        sat,
        "n laters are discharged only by an observer that supplies more than n steps: "
        "the closed-program adequacy quantification",
    )


def main() -> int:
    section_a()
    section_b()
    section_c()
    section_d()
    failed = [name for ok, name, _ in RESULTS if not ok]
    print()
    if failed:
        print(f"{len(failed)} of {len(RESULTS)} checks FAILED: {', '.join(failed)}")
        return 1
    print(f"ALL {len(RESULTS)} CHECKS PASSED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
