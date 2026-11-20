"""Toy model of invertible syntax descriptions (Rendel-Ostermann style).

This is a TOY MODEL written for this report. It is not the Haskell
`invertible-syntax` package, not FliPpr, and not Danielsson's Agda library.
It reproduces only the structural idea: one description is interpreted both
as a list-of-successes parser and as a first-success printer, with partial
isomorphisms (apply/unapply) between concrete and abstract values. Every
grammar below is right-recursive because a naive top-down list-of-successes
parser does not terminate on left recursion (see T0).

Run:  python3 toy_invertible_syntax.py
"""
import sys
from typing import Callable, Optional, List, Any


class Iso:
    def __init__(self, apply: Callable[[Any], Optional[Any]], unapply: Callable[[Any], Optional[Any]]):
        self.apply, self.unapply = apply, unapply   # parser direction, printer direction


class Syn:
    """parse(s) -> list of (value, rest); prin(v) -> str or None."""
    def __init__(self, parse, prin):
        self.parse, self.prin = parse, prin

    def __or__(self, other):   # parser: union of results; printer: left-biased first success
        def q(v):
            r = self.prin(v)
            return r if r is not None else other.prin(v)
        return Syn(lambda s: self.parse(s) + other.parse(s), q)

    def __mul__(self, other):  # sequencing
        def p(s):
            return [((a, b), r2) for (a, r1) in self.parse(s) for (b, r2) in other.parse(r1)]
        def q(v):
            x, y = self.prin(v[0]), other.prin(v[1])
            return None if x is None or y is None else x + y
        return Syn(p, q)

    def iso(self, i: Iso):     # <$>
        def p(s):
            out = []
            for (a, r) in self.parse(s):
                b = i.apply(a)
                if b is not None:
                    out.append((b, r))
            return out
        def q(v):
            a = i.unapply(v)
            return None if a is None else self.prin(a)
        return Syn(p, q)


class Ref(Syn):  # recursion knot
    def __init__(self):
        self.t = None
        super().__init__(lambda s: self.t.parse(s), lambda v: self.t.prin(v))


def tok(t):
    return Syn(lambda s: [((), s[len(t):])] if s.startswith(t) else [],
               lambda v: t if v == () else None)


DIGIT = Syn(lambda s: [(s[0], s[1:])] if s[:1].isdigit() else [],
            lambda v: v if isinstance(v, str) and len(v) == 1 and v.isdigit() else None)


def full(d, s):
    return [v for (v, r) in d.parse(s) if r == ""]


cons = Iso(lambda t: [t[0]] + t[1], lambda l: (l[0], l[1:]) if l else None)
one = Iso(lambda x: [x], lambda l: l[0] if len(l) == 1 else None)

# number ::= digit | digit number      (value: int)
digits = Ref()
digits.t = (DIGIT * digits).iso(cons) | DIGIT.iso(one)
number = digits.iso(Iso(lambda ds: int("".join(ds)),
                        lambda n: list(str(n)) if isinstance(n, int) and n >= 0 else None))

# G_amb: list ::= number list | number    (no separator printed or required)
g_amb = Ref()
g_amb.t = (number * g_amb).iso(cons) | number.iso(one)

# G_sep: list ::= number ' ' list | number
g_sep = Ref()
g_sep.t = (number * (tok(" ") * g_sep)).iso(Iso(lambda t: [t[0]] + t[1][1],
                                               lambda l: (l[0], ((), l[1:])) if len(l) > 1 else None)) \
          | number.iso(one)

# Lawful vs non-lawful iso for pairs "a,b" -> ('pair', a, b)
pair_ok = Iso(lambda t: ('pair', t[0], t[1][1]), lambda p: (p[1], ((), p[2])))
pair_bad = Iso(lambda t: ('pair', t[0], t[1][1]), lambda p: (p[2], ((), p[1])))  # unapply swaps
g_pair_ok = (number * (tok(",") * number)).iso(pair_ok)
g_pair_bad = (number * (tok(",") * number)).iso(pair_bad)

# Biased choice: atom ::= number | '(' atom ')'  -- printer always takes the first branch
atom = Ref()
atom.t = number | (tok("(") * (atom * tok(")"))).iso(Iso(lambda t: t[1][0], lambda v: ((), (v, ()))))

# Left recursion: lr ::= lr 'x' | 'x'
lr = Ref()
lr.t = (lr * tok("x")).iso(Iso(lambda t: t[0] + 1, lambda n: (n - 1, ()) if n > 1 else None)) \
       | tok("x").iso(Iso(lambda _: 1, lambda n: () if n == 1 else None))

if __name__ == "__main__":
    sys.setrecursionlimit(2000)
    try:
        full(lr, "xxx")
        print("T0 left recursion: terminated")
    except RecursionError:
        print("T0 left-recursive description: naive top-down parser does not terminate (RecursionError)")

    v = [1, 2]
    s = g_amb.prin(v)
    print("T1 no-separator grammar: print([1,2]) =", repr(s), "; parses =", full(g_amb, s),
          "; print([12]) =", repr(g_amb.prin([12])))
    counts = [len(full(g_amb, "1" * n)) for n in range(1, 11)]
    print("T2 number of parses of '1'*n, n=1..10:", counts)
    s = g_sep.prin(v)
    print("T3 separator grammar: print([1,2]) =", repr(s), "; parses =", full(g_sep, s))
    p = ('pair', 1, 2)
    print("T4 lawful iso: print =", repr(g_pair_ok.prin(p)), "; parse(print) =", full(g_pair_ok, g_pair_ok.prin(p)))
    sb = g_pair_bad.prin(p)
    print("T5 non-lawful iso: print =", repr(sb), "; parse(print) =", full(g_pair_bad, sb),
          "; round trip holds:", p in full(g_pair_bad, sb))
    print("T6 biased choice: print(7) =", repr(atom.prin(7)), "; parse('((7))') =", full(atom, "((7))"),
          "; so print(parse(s)) != s for s='((7))'")
    print("T7 partial printer: print(-3) =", repr(number.prin(-3)), "(no string denotes -3 in this description)")
