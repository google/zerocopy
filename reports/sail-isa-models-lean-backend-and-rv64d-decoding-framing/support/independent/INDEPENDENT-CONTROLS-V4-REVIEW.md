# Independent Controls-v4 replay and semantic rejection controls

Verdict: **the exact Controls-v4 file independently passes official Lean4.29.0
with -t0**, and its fresh artifact exactly matches the parent's accepted hash.
An additional independently accepted audit proves the negations of four false
counterclaims about the actual generated executor. The corresponding four
well-typed false claims were then rejected in two deliberately failing files.
The semantic evidence is the accepted counterexamples/negations, not a bare
compiler error. No model, support, import, proof input or tool was changed.

## Exact delta and independently verified subject

The v3→v4 source diff is exactly one added proof line, immediately before
sub_differs_from_add's final decide:

```lean
change (some (18446744073709551615 : BitVec 64) : Option (BitVec 64)) ≠ some (3 : BitVec 64)
```

This makes the already intended dependent-map observation's Option/BitVec64 type
explicit for decidability synthesis. It changes neither the theorem statement,
the actual SUB computation, the fixture, nor its observed value. It resolves
the prior ordinary elaboration failure; the rejected v3 file/artifact absence
remain preserved as a separate outcome. No axiom, sorry, admit, native_decide,
substitute executor or new semantic definition was added to Controls-v4.

```text
Controls.lean SHA256
7c9301d8c6080cd8cd1cf1a4ae356532b92de8378e416fd7ed48f35945d5635b
Fresh Controls.olean: 254400 bytes, SHA256
b2fbb76b44f7eb0ad57ca724d959a62dc0ddd7594df0db0a4b26b129fe9aa0b7
```

The accepted artifact is byte-identical to the parent's; it was newly produced
in the create-only independent-controls-v4 root, not copied from the parent's
Controls.olean. The latter was read/hash-checked only as an identity reference.
The previously independently checked Proof.lean/Proof.olean were verified at
f6205748…/a37ef2b0… before copying unchanged as imports. Before the first check,
all143 integration .oleans were independently checked for successful receipt,
size and actual hash; the complete receipt reports143 successes. The selected
compiler executable hash was independently checked as
`e215cbe9eab0914b49761e9e486d388e2e701cf876d1079d1ba733c48edb2d7b`.

The underlying subject remains the original full generated configured RV64D
model, reviewed termination measures, three disclosed abstract external hooks,
and pinned ArchSemSequential interpreter. These controls do not remove that
subject's assumptions or establish fetch/decode/step, ABI, hardware, carry or
Rust-caller correspondence.

## Semantic evidence, accepted before false-claim probes

Controls-v4 checks all13 control theorems: the actual SUB effect/full-state
pair; actual rd4 ADD effect/full-state pair; both missing-register error
theorems; wraparound, SUB, wrong-op inequality, rd4 fixture/observation and two
missing-input fixture theorems. The true fixtures invoke Functions.execute and
the actual interpreter and dependent register map.

The independently accepted SemanticAudit3 adds a **noncomputable observation
projection**, actualX3, which only runs that same executor/interpreter and reads
the returned x3, or none on error. It defines no instruction semantics and
replaces no model transition. Noncomputable matches the official generated
executor's selected proof-oriented definition; it is not a partial definition
or an assumption. The accepted audit proves:

| Counterclaim | Accepted semantic refutation |
|---|---|
| SUB on inputs1,2 gives ADD's x3=3 | actual SUB x3 is2^64−1; sub_differs_from_add and rejects_sub_as_add establish inequality with3 |
| ADD with rd4 has rd3's x3=3 result | actual rd4 execution preserves fixture x3=0 and writes x4=3; rd4_leaves_x3_zero and rejects_rd4_as_rd3 establish the distinction |
| Missing x1 still successfully returns with x3=2 | actual missing-x1 fixture returns Unreachable with the original state; rejects_missing_input_success rules out the specified success constructor |
| Overflow follows unbounded natural addition | actual ADD of BitVec64 max and1 stores0; projecting the stored word to Nat is0, not18446744073709551616; rejects_unbounded_nat_sum establishes this |

The audit retains and prints actual theorem types/terms and axiom lists for all
13 imported control theorems and its five helper/negation theorems. Its own
negations are not desired-result assumptions: they are proved from accepted
control results and constructor/numeric distinctions.

```text
SemanticAudit3.lean SHA256
7c646b5e5a9cee3e4e501e5d2e0fb6bb203c5d80675423133f8b260f1299826c
SemanticAudit3.olean: 52304 bytes, SHA256
ea702e19e7212551f47def3a1dc4cdd769603b74bac7fe706550a5e74814c97a
```

The intentionally false files then attempted the corresponding opposite
equalities. FalsePair1 produces two precise decide failures, proving its reduced
goals `some(max64)=some3` and `some0=some3` false. FalsePair2 produces the expected
failure of rfl on distinct error/success constructors and a decide failure on
`some0=some18446744073709551616` at Option Nat. The missing-input failure alone
would only show that rfl did not solve a goal; the prior accepted negation rules
the claim out semantically. All four statements elaborate with the intended
types; none was rejected for syntax, missing instances, noncomputability or
an unrelated import problem. Neither deliberately failing file emits .olean.

These are concrete witnesses against those four stronger claims. They do not
establish rejection of every mutant, unrestricted operand/destination patterns,
all missing-state configurations, or any artifact/byte-level mutation.

## Diagnosed auxiliary development failures

The first independent audit was not accepted: it omitted noncomputable on the
observation wrapper and tried to use congrArg Prod.fst on rd4_observation where
projection through a match was not definitionally the desired observation.
The second retained audit corrected the projection using the accepted full
rd4_fixture plus the existing map simplification; it still failed the wrapper's
noncomputability check. The final retained version adds only noncomputable to
that wrapper and passes. Earlier auxiliary versions and their streams remain
preserved; printed positive constants inside those failed files are not used
as acceptance evidence. No panic, invariant failure, timeout or OOM occurred.

## Bounded native observations

Exactly six native Lean invocations ran sequentially; total measured native wall
time was12.932568051037379 seconds, below the ten-minute allocation. Each used
timeout120s with five-second TERM grace, -j1, -M4500, --tstack=400000 and -t0.
LEAN_PATH was exactly
`/home/opam/anneal-sail-output/serial-build-integration/olean:/home/opam/anneal-sail-output/independent-controls-v4`.
LEAN_NUM_THREADS was1, with no Lake process or additional heavy build.

| File | Status | Wall seconds | Peak RSS KiB | Outcome |
|---|---:|---:|---:|---|
| Controls | 0 | 2.144861333 | 1555444 | accepted exact v4 |
| SemanticAudit | 1 | 3.383200733 | 1541284 | ordinary declaration/type errors |
| SemanticAudit2 | 1 | 3.387677374 | 1536124 | ordinary noncomputability error |
| SemanticAudit3 | 0 | 3.144951963 | 1546496 | accepted full semantic audit |
| FalsePair1 | 1 | 0.442410513 | 1518804 | two expected numeric counterclaim rejections |
| FalsePair2 | 1 | 0.429466135 | 1519544 | expected constructor/numeric counterclaim rejections |

All native stderr streams were empty; diagnostics were in stdout. The complete
argv, working directory, LEAN_PATH, source/output/stream hashes, process statuses,
user/system time and peak child RSS are preserved per file. There are no further
native invocations available under this grant and no retry is proposed.

## Assumptions and retained artifacts

The accepted SemanticAudit3 prints18 axiom lists: all13 original control
theorems plus five independent helper/negation theorems. Each list has the same
78 distinct names and no sorryAx. These include logical principles and abstract
event/platform/reservation/randomness/floating-point interfaces. Their presence
is disclosed, not equated with invocation on the selected scalar path; the
actual-execute theorem types carry whole-definition syntactic dependencies.
No claim of empty closure is justified.

Host evidence is under [controls-v4-review](controls-v4-review/check-summary.json).
It contains the exact [Controls source](controls-v4-review/Controls.lean), fresh
[Controls artifact](controls-v4-review/Controls.olean), accepted [semantic audit
source](controls-v4-review/SemanticAudit3.lean) and [artifact](controls-v4-review/SemanticAudit3.olean),
[all18 axiom lists](controls-v4-review/all-theorem-axioms.json), all six exact
sources/receipts/streams, and both deliberately false files. Additional authored
but unexecuted preliminary false-file drafts are clearly outside the six-check
receipt list. [File hashes](controls-v4-review/evidence-manifest.json) bind the
retained host bytes. Native sources, accepted artifacts, failed inputs and
streams remain untouched under the new independent-controls-v4 directory.

This verdict supplements the earlier accepted four ADD theorems and records a
now-accepted v4 control suite; it does not rewrite the earlier v3 rejection or
mark the broader cross-foundation objective complete.
