# Exhaustive check of the statement shapes of several results over tiny pattern universes.
#
# Patterns 0..N-1 (N <= 4) stand in for the n-byte patterns of the Lean model and pattern 0
# for the zero pattern; a layout "in fewer bytes" uses a smaller universe 0..M-1 (M <= N).
# Every encoder and every decoder of the listed enum shapes is enumerated. Each failure is
# labeled with the Lean theorem whose statement shape it would contradict. This is a sanity
# check over a different (smaller) universe, not a proof of the Lean statements, whose
# pattern universe has 256^n elements.
import itertools

INVALID = object()
fails = []
checked = {}


def tick(name):
    checked[name] = checked.get(name, 0) + 1


for N in range(1, 5):
    for vmask in range(1 << N):
        V = [p for p in range(N) if vmask >> p & 1]
        ninv = N - len(V)
        for M in range(1, N + 1):
            for k in range(0, 3):
                vals = [('tag', i) for i in range(k)] + [('v', p) for p in V]
                if len(vals) > 5 or (len(vals) + 1) ** M * M ** len(vals) > 400000:
                    continue
                exists_lawful = False
                for enc in itertools.product(range(M), repeat=len(vals)):
                    E = dict(zip(vals, enc))
                    for dec in itertools.product(range(len(vals) + 1), repeat=M):
                        D = [vals[d] if d < len(vals) else INVALID for d in dec]
                        decenc = all(D[E[x]] == x for x in vals)
                        canon = all(D[p] is INVALID or E[D[p]] == p for p in range(M))
                        exists_lawful = exists_lawful or (decenc and canon)
                        # size <= payload size, DecEnc  ->  k <= numInvalid
                        tick('le_numInvalid_of_decEnc_of_size_le')
                        if decenc and not k <= ninv:
                            fails.append(('le_numInvalid_of_decEnc_of_size_le', N, M, V, k, enc, dec))
                        if k != 1 or M != N:
                            continue
                        none = ('tag', 0)
                        frombytes = all(D[p] is not INVALID for p in range(N))
                        tick('opt_canonical_and_fromBytes_of_size_eq_of_numInvalid_le_one_of_decEnc')
                        if ninv <= 1 and decenc and not (frombytes and canon):
                            fails.append(('opt_canonical_and_fromBytes_...', N, V, enc, dec))
                        tick('dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_size_eq_...')
                        if ninv <= 1 and decenc and E[none] == 0:
                            if not all((D[p] == none) == (p == 0) for p in range(N)):
                                fails.append(('dec_eq_some_none_iff_..._size_eq_...', N, V, enc, dec))
                        tick('dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_decEnc_of_canonical')
                        if decenc and canon and E[none] == 0:
                            if not all((D[p] == none) == (p == 0) for p in range(N)):
                                fails.append(('dec_eq_some_none_iff_..._canonical', N, V, enc, dec))
                        st = all(E[('v', p)] == p for p in V)
                        dst = all(D[p] == ('v', p) for p in V)
                        q = E[none]
                        tick('isNiche_enc_none_of_decSomeTransparent_of_decEnc')
                        if dst and decenc and q in V:
                            fails.append(('isNiche_enc_none_of_decSomeTransparent_of_decEnc', N, V, enc, dec))
                        niche_dec = [none if p == q else (('v', p) if p in V else INVALID)
                                     for p in range(N)]
                        tick('someTransparent_lawful_iff_eq_nicheLayout')
                        lhs = st and decenc and canon
                        rhs = (q not in V) and st and D == niche_dec
                        if lhs != rhs:
                            fails.append(('someTransparent_lawful_iff_eq_nicheLayout', N, V, enc, dec))
                        if V == list(range(1, N)):
                            tick('nonZero_layout_eq_nicheLayout_zero_of_decSomeTransparent_of_decEnc')
                            nz_dec = [none if p == 0 else ('v', p) for p in range(N)]
                            if dst and decenc and not (q == 0 and st and D == nz_dec):
                                fails.append(('nonZero_layout_eq_nicheLayout_zero_...', N, enc, dec))
                if M == N:
                    # existence half of the cardinality characterization
                    tick('le_numInvalid_iff_exists_lawful_layout_... (exists)')
                    if exists_lawful != (k <= ninv):
                        fails.append(('le_numInvalid_iff_exists_lawful_layout_...', N, V, k))

# nicheLayoutK lawful iff tags injective and all niches; firstNiches lemma; exposed witness.
for N in range(1, 5):
    for vmask in range(1 << N):
        V = [p for p in range(N) if vmask >> p & 1]
        inv = [p for p in range(N) if p not in V]
        for k in range(0, 4):
            def lawful_nicheK(t):
                vals = [('tag', i) for i in range(k)] + [('v', p) for p in V]
                E = {('tag', i): t[i] for i in range(k)}
                E.update({('v', p): p for p in V})

                def dec(p):
                    for i in range(k):
                        if t[i] == p:
                            return ('tag', i)
                    return ('v', p) if p in V else INVALID
                D = [dec(p) for p in range(N)]
                return (all(D[E[x]] == x for x in vals)
                        and all(D[p] is INVALID or E[D[p]] == p for p in range(N)))
            for t in itertools.product(range(N), repeat=k):
                tick('nicheLayoutK_lawful_iff_injective_and_isNiche')
                rhs = len(set(t)) == k and all(x not in V for x in t)
                if lawful_nicheK(t) != rhs:
                    fails.append(('nicheLayoutK_lawful_iff_injective_and_isNiche', N, V, t))
            fn = [inv[i] if i < len(inv) else 0 for i in range(k)]
            if k <= len(inv):
                tick('firstNiches_injective_and_isNiche_of_le_numInvalid')
                if not (len(set(fn)) == k and all(x not in V for x in fn)):
                    fails.append(('firstNiches_injective_and_isNiche_of_le_numInvalid', N, V, k))
            tick('le_numInvalid_iff_exists_lawful_layout_... (witness)')
            if lawful_nicheK(fn) != (k <= len(inv)):
                fails.append(('le_numInvalid_iff_..._lawful_nicheLayoutK_firstNiches', N, V, k))

for name in sorted(checked):
    print(f'{name}: {checked[name]} cases')
print('failures:', len(fails))
print(fails[:5])
