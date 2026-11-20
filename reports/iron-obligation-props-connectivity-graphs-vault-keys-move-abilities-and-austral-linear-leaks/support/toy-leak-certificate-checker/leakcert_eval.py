#!/usr/bin/env python3
"""Generator, mutation test and timing harness for leakcert.py (TOY MODEL).

Usage: python3 leakcert_eval.py [seed] [n_programs]
Deterministic for a given seed. Prints acceptance of generated valid programs,
mutant kill rates per mutation operator, and checking throughput.
"""
import copy
import random
import sys
import time

from leakcert import check, accepts, Reject


class Gen:
    def __init__(self, rng):
        self.rng = rng
        self.n = 0
        self.cert = {"joins": {}, "loops": {}, "pars": {}, "policy": {"abort_may_leak": False}}

    def fresh(self, p):
        self.n += 1
        return f"{p}{self.n}"

    def block(self, live, outer, depth, budget):
        """Generate statements that consume exactly `live` (a set), never touching
        `outer` (bindings owned by enclosing code). Certificates record the full
        live set outer | live, which is what the checker observes."""
        rng = self.rng
        live = set(live)
        out = []
        steps = rng.randint(1, budget)
        for _ in range(steps):
            k = rng.random()
            if k < 0.30 or depth >= 4:
                x = self.fresh("v")
                out.append(("let", x))
                live.add(x)
            elif k < 0.50 and live:
                x = rng.choice(sorted(live))
                out.append((rng.choice(["move", "drop"]), x))
                live.remove(x)
            elif k < 0.75:
                # n-ary branch: every arm consumes the same subset of local bindings
                consume = {x for x in live if rng.random() < 0.5}
                after = live - consume
                arms_n = rng.randint(2, 4)
                jid = self.fresh("j")
                arms = [self.block(consume, outer | after, depth + 1, max(1, budget // 2))
                        for _ in range(arms_n)]
                self.cert["joins"][jid] = frozenset(outer | after)
                out.append(("branch", jid, arms))
                live = after
            elif k < 0.87:
                lid = self.fresh("l")
                self.cert["loops"][lid] = frozenset(outer | live)
                body = self.block(set(), outer | live, depth + 1, max(1, budget // 2))
                out.append(("loop", lid, body))
            else:
                pid = self.fresh("p")
                handed = {x for x in live if rng.random() < 0.7}
                left = {x for x in handed if rng.random() < 0.5}
                right = handed - left
                self.cert["pars"][pid] = (frozenset(left), frozenset(right))
                out.append(("par", pid,
                            self.block(left, set(), depth + 1, max(1, budget // 2)),
                            self.block(right, set(), depth + 1, max(1, budget // 2))))
                live = live - handed
        for x in sorted(live):
            out.append(("drop", x))
        return out


def walk(stmts, path=()):
    """Yield (path, stmt) for every statement, path = list of (container, index)."""
    for i, s in enumerate(stmts):
        yield (stmts, i), s
        if s[0] == "branch":
            for arm in s[2]:
                yield from walk(arm)
        elif s[0] == "loop":
            yield from walk(s[2])
        elif s[0] == "par":
            yield from walk(s[2])
            yield from walk(s[3])


def count(stmts):
    return sum(1 for _ in walk(stmts))


def mutants(prog, cert, rng):
    """Yield (operator, mutant_prog, mutant_cert)."""
    sites = [(c, i, s) for (c, i), s in walk(prog) if s[0] in ("move", "drop")]
    if sites:
        # M1: delete one consumption
        p = copy.deepcopy(prog)
        psites = [(c, i, s) for (c, i), s in walk(p) if s[0] in ("move", "drop")]
        c, i, s = rng.choice(psites)
        del c[i]
        yield "M1-delete-consume", p, cert
        # M2: duplicate one consumption
        p = copy.deepcopy(prog)
        psites = [(c, i, s) for (c, i), s in walk(p) if s[0] in ("move", "drop")]
        c, i, s = rng.choice(psites)
        c.insert(i, s)
        yield "M2-duplicate-consume", p, cert
    # M3: in an n-ary branch with >=3 arms, delete a consumption from the LAST arm only
    p = copy.deepcopy(prog)
    for (c, i), s in walk(p):
        if s[0] == "branch" and len(s[2]) >= 3:
            last = s[2][-1]
            idx = [k for k, t in enumerate(last) if t[0] in ("move", "drop")]
            if idx:
                del last[idx[0]]
                yield "M3-last-arm-skip", p, cert
                break
    # M4: corrupt an ownership split (move one binding from left to right)
    for pid, (l, r) in cert["pars"].items():
        if l:
            x = sorted(l)[0]
            c2 = copy.deepcopy(cert)
            c2["pars"][pid] = (frozenset(l - {x}), frozenset(r | {x}))
            yield "M4-bad-split", prog, c2
            break


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 500
    rng = random.Random(seed)
    ok = 0
    total_stmts = 0
    kills = {}
    t_check = 0.0
    for _ in range(n):
        g = Gen(rng)
        prog = g.block(set(), set(), 0, 8)
        cert = g.cert
        total_stmts += count(prog)
        t0 = time.perf_counter()
        try:
            check(prog, cert)
            ok += 1
        except Reject as e:
            print("UNEXPECTED REJECT:", e)
        t_check += time.perf_counter() - t0
        for op, mp, mc in mutants(prog, cert, rng):
            # A mutant equal in behaviour to the original is possible only if the
            # mutation is a no-op; operators above always change consumption counts.
            k, t = kills.get(op, (0, 0))
            kills[op] = (k + (0 if accepts(mp, mc) else 1), t + 1)
            k, t = kills.get(op + " [pairs-join variant]", (0, 0))
            kills[op + " [pairs-join variant]"] = (k + (0 if accepts(mp, mc, "pairs") else 1), t + 1)
    print(f"seed={seed} programs={n} valid_accepted={ok}/{n} statements={total_stmts}")
    for op in sorted(kills):
        k, t = kills[op]
        print(f"  {op}: killed {k}/{t}")
    print(f"  check time total={t_check:.4f}s  throughput={total_stmts / t_check:,.0f} statements/s")


if __name__ == "__main__":
    main()
