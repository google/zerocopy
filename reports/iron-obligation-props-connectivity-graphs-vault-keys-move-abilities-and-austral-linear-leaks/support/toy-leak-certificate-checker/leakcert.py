#!/usr/bin/env python3
"""Toy leak-freedom certificate checker for last-use-annotated programs.

This is a TOY MODEL written for illustration. It is not an implementation of
any surveyed system (Iron, connectivity graphs, Vault, Move, Austral, Linear
Haskell). It shows what a certificate for compiler-inserted last-use
annotations must contain and what a small trusted checker must verify.

Toy language (statements over linear bindings):
  ("let", x)                 introduce linear binding x (must be fresh)
  ("move", x)                last use of x: consumes x (the compiler-inserted
                             last-use annotation)
  ("drop", x)                explicit destructor call: consumes x
  ("branch", jid, [S1..Sn])  n-ary branch (if / case); jid names a join point
  ("loop", lid, S)           loop body S, executed zero or more times
  ("par", pid, S1, S2)       parallel composition of two branches
  ("abort",)                 terminate the whole program

Certificate (all fields are data, checked locally):
  joins[jid]  = frozenset of bindings live after the join   (join condition)
  loops[lid]  = frozenset of bindings live at the loop head (loop invariant)
  pars[pid]   = (owned_by_left, owned_by_right)             (ownership split)
  policy      = {"abort_may_leak": bool}

Properties checked (all are obligations a trusted checker must discharge):
  O1 every move/drop names a binding live on the current path (no double use)
  O2 at every n-ary join, EVERY arm's live set equals the certified join set
     (compared against one reference, not adjacent pairs)
  O3 every loop body maps the certified invariant to itself and introduces no
     binding that survives an iteration
  O4 every par split hands disjoint subsets of the live set to the two
     branches; each branch consumes exactly what it owns and can touch nothing
     else; bindings not handed over stay live in the frame
  O5 at program end the live set is empty (leak freedom on normal exit)
  O6 abort is accepted only when the policy permits leaking on abort, or when
     the live set is already empty
"""
import sys


class Reject(Exception):
    pass


def check(prog, cert, join_mode="all"):
    """join_mode="all": every arm must equal the certified join set (sound).
    join_mode="pairs": reproduce the adjacent-pair comparison pattern
    ((arm0,arm1),(arm2,arm3),...) and continue with arm0's state, ignoring the
    certificate; used only to show which mutants that pattern misses."""
    joins = cert.get("joins", {})
    loops = cert.get("loops", {})
    pars = cert.get("pars", {})
    abort_may_leak = cert.get("policy", {}).get("abort_may_leak", False)
    seen = set()  # all binding names ever introduced (freshness)

    def run(stmts, live):
        """Return live set after stmts, or None if the path aborted."""
        live = set(live)
        for s in stmts:
            op = s[0]
            if op == "let":
                x = s[1]
                if x in seen:
                    raise Reject(f"O1: binding {x} not fresh")
                seen.add(x)
                live.add(x)
            elif op in ("move", "drop"):
                x = s[1]
                if x not in live:
                    raise Reject(f"O1: {op} of {x} which is not live")
                live.remove(x)
            elif op == "branch":
                jid, arms = s[1], s[2]
                if jid not in joins:
                    raise Reject(f"O2: missing join certificate {jid}")
                want = set(joins[jid])
                outs = [run(arm, live) for arm in arms]
                if join_mode == "pairs":
                    for a in range(0, len(outs) - 1, 2):
                        if None not in (outs[a], outs[a + 1]) and outs[a] != outs[a + 1]:
                            raise Reject(f"O2(pairs): join {jid} arms {a},{a + 1} differ")
                    if outs[0] is None:
                        return None
                    live = outs[0]
                    continue
                for i, out in enumerate(outs):
                    if out is not None and out != want:
                        raise Reject(f"O2: join {jid} arm {i} live={sorted(out)} "
                                     f"!= certified {sorted(want)}")
                if all(o is None for o in outs):
                    return None
                live = want
            elif op == "loop":
                lid, body = s[1], s[2]
                if lid not in loops:
                    raise Reject(f"O3: missing loop invariant {lid}")
                inv = set(loops[lid])
                if live != inv:
                    raise Reject(f"O3: loop {lid} entry live={sorted(live)} "
                                 f"!= invariant {sorted(inv)}")
                out = run(body, inv)
                if out is not None and out != inv:
                    raise Reject(f"O3: loop {lid} body does not preserve invariant")
            elif op == "par":
                pid, left, right = s[1], s[2], s[3]
                if pid not in pars:
                    raise Reject(f"O4: missing ownership split {pid}")
                own_l, own_r = set(pars[pid][0]), set(pars[pid][1])
                if own_l & own_r or not (own_l | own_r) <= live:
                    raise Reject(f"O4: split {pid} is not a disjoint split of {sorted(live)}")
                out_l = run(left, own_l)
                out_r = run(right, own_r)
                if out_l is None or out_r is None:
                    return None
                if out_l or out_r:
                    raise Reject(f"O4: par {pid} branch leaves owned bindings "
                                 f"{sorted(out_l | out_r)} unconsumed")
                # Frame: bindings not handed to either branch stay live.
                live = live - (own_l | own_r)
            elif op == "abort":
                if live and not abort_may_leak:
                    raise Reject(f"O6: abort with live bindings {sorted(live)}")
                return None
            else:
                raise Reject(f"unknown statement {op}")
        return live

    out = run(prog, set())
    if out:
        raise Reject(f"O5: leaked at exit: {sorted(out)}")
    return True


def accepts(prog, cert, join_mode="all"):
    try:
        return check(prog, cert, join_mode)
    except Reject:
        return False


if __name__ == "__main__":
    # The three-arm pattern that the Austral checker at the pinned revision
    # accepts: r consumed in two arms, not in the third.
    prog = [("let", "r"),
            ("branch", "j0", [[("move", "r")], [("move", "r")], []])]
    for jset in (frozenset(), frozenset({"r"})):
        try:
            check(prog, {"joins": {"j0": jset}})
            print("accepted with join set", sorted(jset))
        except Reject as e:
            print("rejected with join set", sorted(jset), "->", e)
    sys.exit(0)
