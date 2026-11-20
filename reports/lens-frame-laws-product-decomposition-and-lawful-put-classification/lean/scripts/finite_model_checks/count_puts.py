#!/usr/bin/env python3
"""Finite-model check of the counting form of F6 (not a proof).

For every getter get : range(n) -> range(k) with small n, k, enumerate all puts
that make (get, put) very well-behaved and compare their number with the
prediction of F6: (m!)^(k-1) if every fibre has exactly m elements (and 1 when
n = 0), and 0 otherwise.

Two enumerations are used:
  * full: all puts with PutGet (put[s][a] in the fibre over a), checking GetPut
    and PutPut, for n <= 4;
  * fast: puts with PutGet and GetPut built in (put[s][get[s]] = s), checking
    PutPut, for n <= 6.
"""
import itertools
import math


def fibres(get, n, k):
    return [[s for s in range(n) if get[s] == a] for a in range(k)]


def predicted(get, n, k):
    if n == 0:
        return 1
    sizes = {len(f) for f in fibres(get, n, k)}
    if len(sizes) != 1:
        return 0
    m = sizes.pop()
    return math.factorial(m) ** (k - 1)


def is_putput(put, n, k):
    return all(put[put[s][a]][a2] == put[s][a2] for s in range(n) for a in range(k) for a2 in range(k))


def count_full(get, n, k):
    fib = fibres(get, n, k)
    if n > 0 and any(not f for f in fib):
        return 0
    per_s = list(itertools.product(*fib))
    c = 0
    for put in itertools.product(per_s, repeat=n):
        if all(put[s][get[s]] == s for s in range(n)) and is_putput(put, n, k):
            c += 1
    return c


def count_fast(get, n, k):
    fib = fibres(get, n, k)
    if n > 0 and any(not f for f in fib):
        return 0
    choices = []
    for s in range(n):
        opts = [fib[a] if a != get[s] else [s] for a in range(k)]
        choices.append(list(itertools.product(*opts)))
    c = 0
    for put in itertools.product(*choices):
        if is_putput(put, n, k):
            c += 1
    return c


def main():
    checked = mismatches = 0
    for (n, k, counter) in [(n, k, count_full) for n in range(0, 5) for k in range(0, 4)] + \
                           [(n, k, count_fast) for n in (5, 6) for k in (1, 2, 3)]:
        for get in itertools.product(range(k), repeat=n):
            got, want = counter(get, n, k), predicted(get, n, k)
            checked += 1
            if got != want:
                mismatches += 1
                print("MISMATCH", n, k, get, got, want)
    print(f"checked {checked} getters; mismatches: {mismatches}")
    # the two puts for fst on Bool x Bool (state (a, b) encoded as 2a + b)
    get = tuple(s // 2 for s in range(4))
    print("fst on Bool x Bool:", count_full(get, 4, 2), "very well-behaved puts (predicted 2)")


if __name__ == "__main__":
    main()
