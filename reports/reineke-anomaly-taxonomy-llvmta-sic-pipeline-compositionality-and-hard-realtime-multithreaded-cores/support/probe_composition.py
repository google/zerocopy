#!/usr/bin/env python3
"""Toy probe B: which parallel-composition rule is sound for threads that share
one functional unit, under different arbitration policies and thread cores?

TOY MODEL ONLY. It is not a model of FlexPRET, Patmos, SIC, or any real core.
It isolates the question "given each thread's isolated time T_i and its number
of shared-unit accesses a_i, which closed-form bound on the co-run completion
time C_i (and on the makespan) is sound?"

Machine
-------
n = 2 threads. One shared, non-preemptive, unit-capacity functional unit SU;
each SU operation occupies SU for D_S = 2 cycles. Each thread also has a
private ALU; a private operation occupies it for 1 cycle.

Thread cores
------------
  blocking : a thread executes its operations strictly one at a time, in
             program order (op k+1 starts only after op k finished). This is
             the "stall the whole pipeline" discipline.
  ooo      : each operation has dependencies on earlier operations of the same
             thread; the private ALU and the thread's SU port each start the
             oldest ready operation of their kind as soon as possible (greedy
             list scheduling inside the thread, at most one SU op in flight).

Arbitration of SU between threads (when SU is idle at cycle t)
---------------------------------------------------------------
  rr    : work-conserving round robin among requesting threads.
  fp    : fixed priority, thread 0 always wins.
  tdm   : non-work-conserving TDM: thread i may start an SU op only at cycles
          t with t mod (n*D_S) == i*D_S.
  ilv   : FlexPRET/PTARM-like whole-pipeline interleaving: thread i executes
          (any operation) only in cycles t with t mod N_SLOTS == i; an
          operation of length L needs L of the thread's own cycles; no SU
          contention can occur. Only used with the blocking core.

Bounds checked (a_i = number of SU ops of thread i, T_i = isolated time)
------------------------------------------------------------------------
  iso   : C_i <= T_i                             ("max" law for parallel composition)
  rr    : C_i <= T_i + a_i*(n-1)*D_S             (direct-effect per-access bound for RR)
  tdm   : C_i <= T_i + a_i*(n*D_S - 1)           (per-access slot-wait bound for TDM)
  ilv   : C_i <= N_SLOTS*T_i                     (interleaving scaling law)
  sum   : makespan <= sum_i T_i                  ("sum" law for parallel composition)
Also: "indep" = C_i does not change when the co-runner's program is replaced
by another random program (temporal isolation), checked on paired trials.

Python 3 standard library only; deterministic for a given PRNG initializer (first CLI argument).
"""
import random
import sys

D_S = 2
N = 2
N_SLOTS = 2


def gen_thread(rng, core):
    k = rng.randint(1, 8)
    ops = []
    for i in range(k):
        kind = 'S' if rng.random() < 0.5 else 'P'
        deps = [j for j in range(i) if rng.random() < 0.4] if core == 'ooo' else []
        ops.append((kind, deps))
    return ops


def simulate(threads, core, policy, limit=10000):
    """Return list of completion times (cycle after last op finishes)."""
    n = len(threads)
    finish = [[None] * len(t) for t in threads]
    started = [[False] * len(t) for t in threads]
    alu_busy = [0] * n          # cycle until which private ALU is busy
    su_busy_until = 0
    su_owner = None
    port_busy = [0] * n         # thread's SU op in flight until
    rr_last = n - 1
    nextop = [0] * n            # blocking core: index of next op
    blk_busy = [0] * n          # blocking core: busy until
    work_left = [0] * n         # ilv: remaining thread-cycles of current op
    done = [len(t) == 0 for t in threads]
    comp = [0] * n
    t = 0
    while not all(done):
        if t > limit:
            raise RuntimeError('no progress')
        if policy == 'ilv':
            i = t % N_SLOTS
            if i < n and not done[i]:
                if work_left[i] == 0:
                    kind, _ = threads[i][nextop[i]]
                    work_left[i] = D_S if kind == 'S' else 1
                work_left[i] -= 1
                if work_left[i] == 0:
                    nextop[i] += 1
                    if nextop[i] == len(threads[i]):
                        done[i] = True
                        comp[i] = t + 1
            t += 1
            continue
        # collect SU requests at cycle t
        req = []
        for i in range(n):
            if done[i]:
                continue
            if core == 'blocking':
                if blk_busy[i] <= t and nextop[i] < len(threads[i]):
                    kind, _ = threads[i][nextop[i]]
                    if kind == 'P':
                        blk_busy[i] = t + 1
                        finish[i][nextop[i]] = t + 1
                        nextop[i] += 1
                    else:
                        req.append((i, nextop[i]))
            else:
                ops = threads[i]
                # private ALU: oldest ready P op
                if alu_busy[i] <= t:
                    for j, (kind, deps) in enumerate(ops):
                        if kind == 'P' and not started[i][j] and all(
                                finish[i][d] is not None and finish[i][d] <= t for d in deps):
                            started[i][j] = True
                            finish[i][j] = t + 1
                            alu_busy[i] = t + 1
                            break
                if port_busy[i] <= t:
                    for j, (kind, deps) in enumerate(ops):
                        if kind == 'S' and not started[i][j] and all(
                                finish[i][d] is not None and finish[i][d] <= t for d in deps):
                            req.append((i, j))
                            break
        # arbitrate SU
        if su_busy_until <= t and req:
            grant = None
            if policy == 'rr':
                for step in range(1, n + 1):
                    cand = (rr_last + step) % n
                    m = [r for r in req if r[0] == cand]
                    if m:
                        grant = m[0]
                        rr_last = cand
                        break
            elif policy == 'fp':
                grant = min(req)
            elif policy == 'tdm':
                for r in req:
                    if t % (n * D_S) == r[0] * D_S:
                        grant = r
            elif policy == 'iso':
                grant = req[0]
            if grant is not None:
                i, j = grant
                su_busy_until = t + D_S
                finish[i][j] = t + D_S
                started[i][j] = True
                if core == 'blocking':
                    blk_busy[i] = t + D_S
                    nextop[i] += 1
                else:
                    port_busy[i] = t + D_S
        # completion check
        for i in range(n):
            if not done[i] and all(f is not None and f <= t + 1 for f in finish[i]):
                done[i] = True
                comp[i] = t + 1
        t += 1
    return comp


def isolated(thread, core, policy):
    if policy == 'ilv':
        # alone means the thread still only owns its slots; isolated time is
        # measured on a non-interleaved machine for the scaling law
        return simulate([thread], core, 'iso')[0]
    return simulate([thread], core, 'iso')[0]


def main():
    prng = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
    rng = random.Random(prng)
    configs = [('blocking', 'rr'), ('blocking', 'fp'), ('blocking', 'tdm'), ('blocking', 'ilv'),
               ('ooo', 'rr'), ('ooo', 'fp'), ('ooo', 'tdm')]
    print(f'prng={prng} trials={trials} n={N} D_S={D_S} N_SLOTS={N_SLOTS}')
    for core, policy in configs:
        viol = {'iso': 0, 'rr': 0, 'tdm': 0, 'ilv': 0, 'sum': 0, 'indep': 0}
        worst = {k: 0 for k in viol}
        for _ in range(trials):
            th = [gen_thread(rng, core) for _ in range(N)]
            alt = gen_thread(rng, core)
            T = [isolated(x, core, policy) for x in th]
            a = [sum(1 for k, _ in x if k == 'S') for x in th]
            C = simulate(th, core, policy)
            C_alt = simulate([th[0], alt], core, policy)
            for i in range(N):
                checks = {
                    'iso': C[i] - T[i],
                    'rr': C[i] - (T[i] + a[i] * (N - 1) * D_S),
                    'tdm': C[i] - (T[i] + a[i] * (N * D_S - 1)),
                    'ilv': C[i] - N_SLOTS * T[i],
                }
                for k, ex in checks.items():
                    if ex > 0:
                        viol[k] += 1
                        worst[k] = max(worst[k], ex)
            ex = max(C) - sum(T)
            if ex > 0:
                viol['sum'] += 1
                worst['sum'] = max(worst['sum'], ex)
            if C_alt[0] != C[0]:
                viol['indep'] += 1
                worst['indep'] = max(worst['indep'], abs(C_alt[0] - C[0]))
        cells = ' '.join(f'{k}={viol[k]}(max+{worst[k]})' for k in viol)
        print(f'{core:8s} {policy:4s} violations: {cells}')


if __name__ == '__main__':
    main()
