#!/usr/bin/env python3
"""TOY Monte Carlo study (not a property of any upstream library) of the
Christoffersen (1998) independence and conditional-coverage likelihood-ratio
tests and the Kupiec (1995) unconditional-coverage test for 99% VaR exception
sequences of length N=250, with asymptotic chi-square critical values.

Data-generating processes for the exception indicator I_t:
  * iid Bernoulli(p)                       -- correct model
  * iid Bernoulli(q), q > p                -- miscalibrated level
  * first-order Markov chain with stationary exception rate exactly p but
    clustering: P(I_t=1 | I_{t-1}=1) = pi11, P(I_t=1 | I_{t-1}=0) = pi01
    chosen so that pi01 / (1 - pi11 + pi01) = p.
Usage: python3 christoffersen_toy.py [reps] [seed]
Standard library only; deterministic given the seed.
"""
import math
import random
import sys

CHI2_1_95 = 3.841458820694124
CHI2_2_95 = 5.991464547107979


def xlogy(x, y):
    return 0.0 if x == 0 else x * math.log(y)


def lr_uc(seq, p):
    n = len(seq)
    x = sum(seq)
    ph = x / n
    return -2.0 * ((xlogy(n - x, 1 - p) + xlogy(x, p)) - (xlogy(n - x, 1 - ph) + xlogy(x, ph)))


def lr_ind(seq):
    n00 = n01 = n10 = n11 = 0
    for a, b in zip(seq, seq[1:]):
        if a == 0 and b == 0:
            n00 += 1
        elif a == 0:
            n01 += 1
        elif b == 0:
            n10 += 1
        else:
            n11 += 1
    pi01 = n01 / (n00 + n01) if n00 + n01 else 0.0
    pi11 = n11 / (n10 + n11) if n10 + n11 else 0.0
    pi = (n01 + n11) / (n00 + n01 + n10 + n11)
    l0 = xlogy(n00 + n10, 1 - pi) + xlogy(n01 + n11, pi)
    l1 = xlogy(n00, 1 - pi01) + xlogy(n01, pi01) + xlogy(n10, 1 - pi11) + xlogy(n11, pi11)
    return -2.0 * (l0 - l1)


def gen_iid(rng, n, q):
    return [1 if rng.random() < q else 0 for _ in range(n)]


def gen_markov(rng, n, p, pi11):
    # stationary rate p = pi01 / (1 - pi11 + pi01)  =>  pi01 = p (1 - pi11) / (1 - p)
    pi01 = p * (1 - pi11) / (1 - p)
    s = 1 if rng.random() < p else 0
    out = [s]
    for _ in range(n - 1):
        s = 1 if rng.random() < (pi11 if s else pi01) else 0
        out.append(s)
    return out


def study(reps, seed, n=250, p=0.01):
    rng = random.Random(seed)
    scenarios = [('iid p=0.01 (correct)', lambda: gen_iid(rng, n, p)),
                 ('iid q=0.02', lambda: gen_iid(rng, n, 0.02)),
                 ('iid q=0.03', lambda: gen_iid(rng, n, 0.03)),
                 ('Markov rate 0.01, pi11=0.1', lambda: gen_markov(rng, n, p, 0.1)),
                 ('Markov rate 0.01, pi11=0.2', lambda: gen_markov(rng, n, p, 0.2)),
                 ('Markov rate 0.01, pi11=0.4', lambda: gen_markov(rng, n, p, 0.4))]
    print(f'reps={reps} seed={seed} N={n} p={p}; rejection rates at nominal 5% (asymptotic chi2)')
    print(f'{"scenario":32s} {"LR_uc":>7s} {"LR_ind":>7s} {"LR_cc":>7s} {"mean exc":>9s}')
    for name, gen in scenarios:
        r_uc = r_ind = r_cc = 0
        tot = 0
        for _ in range(reps):
            s = gen()
            tot += sum(s)
            u = lr_uc(s, p)
            i = lr_ind(s)
            r_uc += u > CHI2_1_95
            r_ind += i > CHI2_1_95
            r_cc += (u + i) > CHI2_2_95
        mcse = math.sqrt(0.25 / reps)
        print(f'{name:32s} {r_uc/reps:7.4f} {r_ind/reps:7.4f} {r_cc/reps:7.4f} {tot/reps:9.3f}')
    print(f'(Monte Carlo standard error of each rate <= {mcse:.4f})')


if __name__ == '__main__':
    reps = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20261120
    study(reps, seed)
