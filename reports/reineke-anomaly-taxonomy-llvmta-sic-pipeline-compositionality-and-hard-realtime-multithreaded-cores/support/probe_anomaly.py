#!/usr/bin/env python3
"""Toy probe A: scheduling timing anomalies in a two-resource task model.

TOY MODEL ONLY. It is not a model of any real processor. It reproduces, in the
task/resource view of Reineke et al. (WCET 2006, Sec. 4), the two effects that
the literature names (a) counter-intuitive timing anomalies (a locally shorter
"pivot" task yields a longer schedule) and (b) amplification (a local increase
of d cycles yields a global increase of more than d cycles).

Model
-----
A program is a list of tasks in program order. Task i has
  res[i]  in {0, 1}         (which of two unit-capacity resources it occupies),
  lat[i]  >= 1              (cycles it occupies that resource),
  deps[i] subset of {0..i-1} (tasks that must have finished before i starts).
Task 0 is the pivot; its latency is either HIT or MISS (HIT < MISS).

Two schedulers:
  ooo    greedy list scheduler: every cycle, each idle resource starts the
         oldest (lowest index) not-yet-started task whose deps have finished.
         Non-preemptive. This mimics greedy out-of-order dispatch.
  inord  strict in-order issue: task i may not start before task i-1 started;
         otherwise as above.  start[i] = max(start[i-1], max finish[deps],
         time resource res[i] becomes free).
Makespan = max finish time.

Output: counts of counter-intuitive anomalies (T(HIT) > T(MISS)) and of
amplification (T(MISS) - T(HIT) > MISS - HIT) for each scheduler, plus the
smallest counter-intuitive witness found for the ooo scheduler.
Python 3 standard library only; deterministic for a fixed PRNG initializer (first CLI argument).
"""
import random
import sys


def schedule_ooo(res, lat, deps):
    n = len(res)
    start = [None] * n
    finish = [None] * n
    busy_until = [0, 0]
    t = 0
    done = 0
    while done < n:
        for r in (0, 1):
            if busy_until[r] > t:
                continue
            for i in range(n):
                if start[i] is None and res[i] == r and all(
                        finish[d] is not None and finish[d] <= t for d in deps[i]):
                    start[i] = t
                    finish[i] = t + lat[i]
                    busy_until[r] = finish[i]
                    done += 1
                    break
        t += 1
        if t > 10000:
            raise RuntimeError("no progress")
    return max(finish)


def schedule_inorder(res, lat, deps):
    n = len(res)
    start = [0] * n
    finish = [0] * n
    free = [0, 0]
    prev_start = 0
    for i in range(n):
        s = max([prev_start, free[res[i]]] + [finish[d] for d in deps[i]])
        start[i] = s
        finish[i] = s + lat[i]
        free[res[i]] = finish[i]
        prev_start = s
    return max(finish)


def main():
    prng = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
    HIT, MISS = 1, 3
    rng = random.Random(prng)
    stats = {"ooo": [0, 0], "inord": [0, 0]}
    best = None
    for _ in range(trials):
        n = rng.randint(3, 6)
        res = [rng.randint(0, 1) for _ in range(n)]
        lat = [rng.randint(1, 4) for _ in range(n)]
        deps = [[d for d in range(i) if rng.random() < 0.35] for i in range(n)]
        for name, f in (("ooo", schedule_ooo), ("inord", schedule_inorder)):
            lh = list(lat); lh[0] = HIT
            lm = list(lat); lm[0] = MISS
            th, tm = f(res, lh, deps), f(res, lm, deps)
            if th > tm:
                stats[name][0] += 1
                if name == "ooo":
                    key = (n, sum(lat))
                    if best is None or key < best[0]:
                        best = (key, res, lh, lm, deps, th, tm)
            if tm - th > MISS - HIT:
                stats[name][1] += 1
    print(f"prng={prng} trials={trials} HIT={HIT} MISS={MISS}")
    for name in ("ooo", "inord"):
        print(f"{name}: counter_intuitive={stats[name][0]} amplification={stats[name][1]}")
    if best:
        _, res, lh, lm, deps, th, tm = best
        print("smallest ooo counter-intuitive witness:")
        print(f"  res={res} deps={deps}")
        print(f"  lat(hit)={lh} -> makespan {th}")
        print(f"  lat(miss)={lm} -> makespan {tm}")
        print(f"  inorder on same program: hit {schedule_inorder(res, lh, deps)}, miss {schedule_inorder(res, lm, deps)}")


if __name__ == "__main__":
    main()
