#!/usr/bin/env python3
"""TOY MODEL probe: allocation disciplines vs. renaming and reordering obligations.

This is not a model of any real compiler or proof development. It isolates
three allocator disciplines found in the surveyed developments and asks two
discriminating questions by exhaustive enumeration over small parameters.

Disciplines (component P and context C take turns; each turn allocates cells):
  per_party   : each party has its own unbounded counter (handles are
                (party, n)); the shape used by a per-component block counter.
  global      : one shared unbounded counter; handles are integers in
                allocation order.
  budget      : one shared counter with total budget B; an allocation that
                would exceed B fails, and the failure is visible to the
                allocating party.

Q1 (renaming): fix P's allocation script; vary the context's allocation
   counts. Record what P observes on its own turns (its handles and its
   success/failure bits). Count distinct observations (a) exactly and
   (b) modulo a bijective renaming of handles (canonicalised by first
   occurrence). One class modulo renaming means a renaming-based simulation
   can absorb the context's allocation differences.

Q2 (reordering): two allocations of sizes a (by P) and b (by C) against one
   shared budget B. Count (a, b, B) triples where the two execution orders give
   P different outcomes, i.e. where the allocations conflict through the budget.

Standard library only. Runs in well under a second.
"""
import itertools

P_SCRIPT = [1, 2, 1]          # cells P allocates on each of its turns
K = 3                          # context allocates 0..K cells per turn
BUDGETS = [3, 4, 5, 6, 8]


def run(discipline, ctx, budget=None):
    """Alternate C, P, C, P, ...; return P's observation tuple."""
    counters = {'P': 0, 'C': 0}
    used = 0
    obs = []
    for c_cells, p_cells in zip(ctx, P_SCRIPT):
        for party, cells in (('C', c_cells), ('P', p_cells)):
            handles, ok = [], True
            for _ in range(cells):
                if discipline == 'per_party':
                    handles.append((party, counters[party])); counters[party] += 1
                elif discipline == 'global':
                    handles.append(used); used += 1
                else:  # budget
                    if used + 1 > budget:
                        ok = False
                        break
                    handles.append(used); used += 1
            if party == 'P':
                obs.append((tuple(handles), ok))
    return tuple(obs)


def canon(obs):
    """Rename handles bijectively in order of first occurrence."""
    m = {}
    out = []
    for handles, ok in obs:
        out.append((tuple(m.setdefault(h, len(m)) for h in handles), ok))
    return tuple(out)


def q1():
    ctxs = list(itertools.product(range(K + 1), repeat=len(P_SCRIPT)))
    print(f'Q1: P script {P_SCRIPT}; {len(ctxs)} contexts (0..{K} cells per turn)')
    for disc, budgets in (('per_party', [None]), ('global', [None]), ('budget', BUDGETS)):
        for b in budgets:
            obs = [run(disc, c, b) for c in ctxs]
            exact = len(set(obs))
            modren = len(set(canon(o) for o in obs))
            label = disc if b is None else f'{disc}(B={b})'
            print(f'  {label:14s} exact observations={exact:3d}  modulo renaming={modren:3d}')


def q2():
    total = differ = 0
    for B in range(1, 9):
        for a in range(1, B + 1):
            for b in range(1, B + 1):
                total += 1
                p_first = a <= B                 # P allocates first
                p_second = b <= B and a + b <= B  # P allocates after C took b (C succeeds since b <= B)
                if p_first != p_second:
                    differ += 1
    print(f'Q2: (a, b, B) triples with 1 <= a, b <= B <= 8: {total}; '
          f'order changes P outcome in {differ} ({100.0 * differ / total:.1f}%)')
    print('    (differs exactly when a <= B, b <= B and a + b > B)')


if __name__ == '__main__':
    q1()
    q2()
