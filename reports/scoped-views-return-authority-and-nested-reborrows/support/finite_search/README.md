# Finite search over the toy model (supporting evidence, not kernel-checked)

`model.py` is a Python reference implementation of the Lean definitions in `ToyViews/Basic.lean`,
`ToyViews/Laws.lean` and `ToyViews/Authority.lean` (views, cells, the seven loan-tree laws,
write exclusivity, proper descendants, return authority, the naive end `endRaw`,
no-resurrection) and of `borrow`/`share` (plus an `alloc` used only to build initial states).
States are tuples of views `(parent, mode, active, cells)`, cells `('own', depth, byte)` or
`('loan', child)` or `None`.

* `reach.py` — states reachable by alloc/borrow/share/end, with ends authorized by return
  authority, by the local return check, or by the naive rule alone.
* `brute2.py N A D P` — all states with `N` views, `A` addresses, depths `<= D` (`P = 1`: parent
  ids ordered and loan targets above the owner); for write-exclusive states, ends under return
  authority that break write exclusivity or no-resurrection, grouped by the set of violated laws.
* `brute3.py N A D P` — the same with the seven laws as the only filter; reports safety-step and
  invariant-step violations by violated law.
* `brute_we.py N A D P` — states violating write exclusivity, grouped by violated laws.
* `brute_closed.py` — return-authority preservation across closed-views pairs, and the effect of
  dropping each closed-views condition or parent existence.

Run with `python3 <script> ...` (Python 3, standard library only). These searches cover small
universes only. They are supporting evidence, not proofs: every theorem of the package is proved in
Lean (see `REPORT.md`). Preservation of the loan-tree laws by `borrow` and `share` along reachable
traces (`reach.py`; `write` is not explored there) rests on these searches alone; no theorem of
the package states it.

The naive end in `model.py` mirrors the Lean `endRaw`: the ended view and its parent must be
active, and the parent must hold each of the child's cells as an outstanding loan (`loaned child`,
or a depth above the parent's own baseline for a shared child). Every end this rule allows is also
allowed, with the same result, by a more permissive variant of the rule (no parent activity check,
any positive parent depth for shared children), under which the searches of `brute2.py`/`brute3.py`
were originally run; their "no counterexample" results therefore carry over.
