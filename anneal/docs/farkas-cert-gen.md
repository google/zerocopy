<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Linear Arithmetic Certificate Generator (`farkas_cert_gen.py`)

Synthesizes `Anneal.LinearArith` Farkas and Chvatal-Gomory cut certificates
(`NatCutGoal`, `IntCutGoal`, `List CutStep`) checked by `rfl` via
`checkNatCutGoal_sound` or `checkIntCutGoal_sound`.

## When to Use

Use `Anneal.LinearArith` together with `ci/farkas_cert_gen.py` when:

1. A lemma depends on **multi-variable linear `Nat`/`Int` inequalities**
   (bounds chaining, slice-offset arithmetic, or alignment/parity cuts like
   `2 * i <= 2 * n + 1` and `2 * n + 1 <= 2 * i`).
2. `omega` is **disallowed** (such as inside Pass-1 `anneal/theory/` modules
   or `prelude` + `Init.*`-only target proofs) or kernel tactic reduction
   stalls on algebraic case splits.

By contrast, use concrete bitvector reasoning (`Anneal.BitVec` /
`Anneal.BitTrieLrat`) for bitwise masks/XORs, and plain `rfl` when values are
constant.

## Grammar and Conventions

- Relations: one of `<=`, `<`, `>=`, `>`, `=`, or `==` (`--goal` rejects
  equality operators). Equality hypotheses `a = b` expand into two bounds
  (`h0 : a <= b`, `h1 : b <= a`). Strict `a > b` renders as `b < a`.
- Expressions: linear combinations over Lean identifiers (excluding reserved
  keywords, `h<digits>`, prelude/theorem names), integers, `+`, `(`, `)`, and
  left-scalar `k * expr` (`NatLinExpr.mulC` / `IntLinExpr.mulC` put constants
  on the left). Per-side input ASTs are capped at depth `<= 16` and nodes
  `<= 48` before `<`/`>` `+ 1` desugaring (so emitted `<` sides may reach depth
  `17` / `50` nodes). Post-pruned goals and certificates stay within domain
  bounds (`<= 30` vars, `<= 30` hyps, `<= 176` AST nodes, `<= 88` var
  occurrences, `<= 68` steps, and joint budget
  `2*vars + 2*hyps + nodes + var_occs + steps <= 360` for `nat`; `<= 44` vars,
  `<= 44` hyps, `<= 1000` AST nodes, `<= 500` var occurrences, `<= 96` steps
  for `int`; plus certificate DAG depth `<= 16` across both domains) so
  generated `rfl` proofs verify within Lean's default `maxRecDepth` (`512`)
  and `maxHeartbeats` (`200000`) limits (deeper `.divCut` chains can hit
  `whnf` heartbeats under `rfl`, while Pass-1 `TrustedBoundary` forbids
  `by decide +kernel`).
- Domain rules: `--domain nat` rejects `-` because truncating `Nat.sub` is
  non-linear, and supplies `0 <= v` internally via `checkNatCutGoal_sound`.
  `--domain int` accepts unary `-` and binary `-` inputs, renders Pass-1-safe
  `Int.negOfNat` / `Int.neg` terms, and adds `Int` ascriptions on
  variable-free relations (`(1 : Int) <= (0 : Int)`).
- CLI options and exit codes: accepts `--max-nodes <N>` (default `2500`; dense
  `>= 12`-hyp 3-term systems can hit `--max-nodes` -> raise `--max-nodes` or
  split into helper lemmas), prunes unused `--hyp` bindings automatically
  (recording deduplicated 0-based input `--hyp` indices in JSON
  `kept_hyp_indices`), and balances `.comb` additions into `O(log n)` trees to
  prevent `whnf` timeouts on long chains. Pass `--json` for structured JSON on
  stdout. Exits `0` if solved, `1` if no refutation is found within `magCap128`
  / search bounds (message on stderr in text mode), and `2` on invalid syntax,
  kernel surface bounds, or `magCap128` (`2^128`) overflows.

## How to Use

1. From `anneal/`, run `ci/farkas_cert_gen.py` (hoist
   `import Anneal.LinearArith` and `open Anneal.LinearArith` to file top in
   your Lean module):

```sh
python3 ci/farkas_cert_gen.py \
  --domain nat \
  --hyp "2*i <= 2*n + 1" \
  --hyp "2*n + 1 <= 2*i" \
  --goal "1 <= 0" \
  --name parity_false
```

2. Paste the emitted `NatCutGoal`/`IntCutGoal`, `List CutStep`, and `theorem`
   into your `Proof.lean` (or `anneal/theory/` module). Lean's kernel verifies
   the certificate via `rfl` inside `checkNatCutGoal_sound` or
   `checkIntCutGoal_sound` (wrap `1 <= 0` contradictions with `nomatch`).
