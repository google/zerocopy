# Double fetches against a concurrent writer: single-read discipline, robust refinement and torn snapshots (`Toy.DoubleFetch`)

Lean `leanprover/lean4:v4.34.1`, core Lean and `Std`, no Mathlib. Lake project in `lean/` (one library, `DoubleFetch`). Every Lean statement below is quoted verbatim from the sources with a `file:line` citation; proofs are elided. All results, counterexamples, non-vacuity witnesses, positive controls and examples are proved and kernel-checked.

## Summary

- `snapshot-parse-rstate` (theorem, T0): For every spec `spec : Region n → α` and every writer `adv : Adversary n`, the snapshot parser `snapParse spec` run by `Prog.exec` returns `spec (adv 0)`, the spec of the state at the time of its one atomic access; hence `snapParse spec` is R-state (`RState spec (snapParse spec)`). This is a reference point: it holds because the toy's `snap` primitive is atomic by definition.
- `bytecopy-parse-diagonal-rvalid` (theorem, T1): For every spec `spec : Region n → α` and every writer `adv : Adversary n`, the byte-by-byte copy parser `copyParse spec` (reads address `j` at time `j`, for every address `j` of the region, then applies `spec` to the private copy) returns `spec (fun j => adv j.val j)`, the spec of the diagonal vector of bytes as read; hence it is R-valid (`RValid spec (copyParse spec)`). For every spec, `copyParse spec` is also single-read and implements `spec` in private memory (`copyParse_singleRead_implements`).
- `bytecopy-torn-not-rstate` (counterexample, T1): Against the writer `pairTornAdv` (state `(0,0)` at time `0`, `(1,1)` at every later time), the byte-by-byte copy parser of the pair spec returns `(0, 1)`, which differs from `pairSpec (pairTornAdv t)` for every time `t`; so `copyParse pairSpec` is not R-state.
- `single-read-exec-eq-eval-assemble` (theorem, T1): For every parser `p : Prog n α` that satisfies the single-read discipline `SingleRead p` (on every root-to-leaf path each address is read at most once, a `snap` counting as a read of every address), every writer `adv` and every filler `d : Region n`, the run `p.exec adv` equals the private-memory result `p.eval (p.assemble adv d)` on the assembled vector, which holds at each address read during the run the byte observed there and `d` elsewhere. This covers parsers whose later addresses are computed from earlier bytes, such as `dataDepProg` (`dataDepProg_singleRead`).
- `single-read-rvalid` (theorem, T1): For every spec `spec` and parser `p`, if `p` is single-read (`SingleRead p`) and implements `spec` in private memory (`Implements p spec`: `p.eval s = spec s` for every region `s`), then `p` is R-valid for `spec`: against every writer its result is `spec s'` for some byte vector `s'`.
- `single-read-rsafe` (theorem, T1): For every predicate `safe : α → Prop` on result values (it depends on the result alone, not on the writer's states) and every parser `p`, if `p` is single-read and every private-memory result is safe (`∀ s, safe (p.eval s)`), then `p` is R-safe: against every writer its result satisfies `safe`. In the toy an action such as "copy `len` bytes" is represented by the result value `some len`, so `safe` can constrain the parameters of actions computed from the bytes read.
- `single-read-not-necessary` (counterexample, T1): The re-read-and-compare parser `rereadCompare` on a one-byte region (read the byte twice; return the error result `none` if the two reads differ, otherwise decode the byte with `boolParse`) implements `boolParse` in private memory, is R-valid for `boolParse` and R-safe for `ValidBoolOut`, is not single-read, and is not R-state for `boolParse`.
- `rvalid-iff-robust-refinement-of-single-read-implementation` (characterization, T1): For every spec `spec : Region n → α` and every parser `p`, `p` is R-valid for `spec` iff there is a single-read parser `q` that implements `spec` in private memory such that `p` robustly refines `q` (`RobustRefines p q`: every result `p` returns against some writer, `q` returns against some writer). For every spec, the single-read implementation can be taken to be `copyParse spec`: `p` is R-valid for `spec` iff `RobustRefines p (copyParse spec)`.
- `rvalid-equivalence-readings-refuted` (counterexample, T1): Two equivalence readings of 'R-valid iff equivalent to a single-read parser' fail. (i) Agreement against every writer: `rereadCompare` is R-valid for `boolParse`, but no single-read parser on a one-byte region returns the same result as `rereadCompare` against every writer. (ii) Agreement in private memory: for every region size `m + 1` and capacity `cap` with `cap < 255`, the double-fetch length parser `lenReread m cap` agrees in private memory with `lenOnce m cap` (`PrivRefines (lenReread m cap) (lenOnce m cap)`), which is single-read and R-valid for `lpParse cap`, yet `lenReread m cap` is not R-valid for `lpParse cap`.
- `length-reread-out-of-bounds-and-invalid` (counterexample, T1): For every region size `m + 1` and capacity `cap` with `cap < 255`, against the writer `lenFlipAdv m cap` (length byte `cap` at time `0`, `cap + 1` afterwards) the double-fetch length parser `lenReread m cap` (read the length, check `len ≤ cap`, read the length again, copy the re-read length) returns `some (cap + 1)`: copying `cap + 1` bytes into the buffer of capacity `cap` is out of bounds, and the result equals `lpParse cap s'` for no byte vector `s'`; so `lenReread m cap` is neither R-safe for `CopyInBounds cap` nor R-valid for `lpParse cap`. For every `m` and `cap`, `lenReread m cap` implements `lpParse cap` in private memory, and `lenOnce m cap` is single-read, implements `lpParse cap`, and is R-safe and R-valid.
- `tag-reread-invalid-bool` (counterexample, T1): For every region size `m + 1`, against the writer `tagFlipAdv m` (byte `1` at time `0`, `2` afterwards) the double-fetch `bool` parser `tagReread m` (validate that the byte is `0` or `1`, then read it again and hand on the re-read byte as a `bool`) returns `some 2`, which is not a valid `bool` representation (`¬ ValidBoolOut (some 2)`) and equals `boolParse s'` for no byte vector `s'`; so `tagReread m` is neither R-safe for `ValidBoolOut` nor R-valid for `boolParse`. Both `tagReread m` and the single-read `tagOnce m` implement `boolParse` in private memory, and `tagOnce m` is single-read, R-safe for `ValidBoolOut` and R-valid for `boolParse`.
- `checksum-torn-value-matches-no-state` (counterexample, T1): Against the writer `ckTornAdv` (states `(0,0,0)`, `(1,1,2)`, then `(2,255,1)` from time `2` on, each passing the checksum, which is addition modulo 256), the byte-by-byte copy parser `copyParse ckParse`, which is single-read (`copyParse_singleRead_implements`), returns `some (0, 1)`; this equals `ckParse (reg3 0 1 1)`, the result for a checksum-passing vector, but differs from `ckParse (ckTornAdv t)` for every time `t`. With two states this cannot happen when both pass the checksum: for all regions `A` and `B` that both pass the checksum and every writer whose every state is `A` or `B`, every checksum-passing result of `copyParse ckParse` equals `ckParse A` or `ckParse B` (`copyParse_ckParse_twoValidStates`).
- `torn-value-impossibility` (impossibility, T1): For every region size `n` (including `0` and `1`), every spec `spec : Region n → α` and every parser `p` that uses one-byte reads and no snapshot (`p.NoSnap`): if `spec` has an undetermined state (`HasUndeterminedState spec`: some region state `s0` such that `spec` is not constant and, for every address `i` and every candidate output `r`, some region that agrees with `s0` at `i` has an output different from `r`), then `p` is not R-state for `spec`; the parser need not implement `spec`. Conversely, if `spec` has no undetermined state, some snapshot-free parser is R-state for `spec` (`hasUndeterminedState_iff_no_noSnap_rstate`). The pair spec, the checksum spec, the seqlock spec, two-byte boolean AND and the tagged-value spec `viewSpec k` (for every `k`) have undetermined states; no spec on a region of size `0` or `1` has one.
- `seqlock-rstate-one-step-protocol-writer` (theorem, T0): For every writer `adv : Adversary 3` that follows the version protocol and takes at most one protocol step between consecutive reader accesses (`OneStepVersionWriter adv`: each step leaves the state unchanged, begins a write by incrementing an even version, changes data under an odd version, or ends a write by incrementing an odd version; increments are modulo 256), the seqlock reader `seqlockReader` (read the version; if it is odd, return `none` at once; otherwise read the two data bytes and the version again, and return the data iff the two version reads agree, otherwise `none`) returns `seqSpec (adv t)` for some time `t ≤ 3`.
- `seqlock-accepted-consistent-under-increment-bound` (theorem, T0): For every writer `adv : Adversary 3` that follows the version protocol, with any number of protocol steps between consecutive reader accesses, and increments the version fewer than 256 times in total from time `0` to time `3` (`IncrementBoundedWriter 256 adv`; the version byte wraps modulo 256), and every `d`, if `seqlockReader` accepts with `some d`, then `seqSpec (adv 0) = some d`. Without a bound on increments the protocol constrains nothing: every region state reaches every other by a protocol path (`versionPath_any`).
- `remat-breaks-robustness` (counterexample, T0): For every check-then-use fragment `c : CheckUse n α`, read rematerialization is a refinement in the private-memory semantics (`PrivRefines c.remat c.compile`). For every region size `m + 1` and capacity `cap` with `cap < 255`, the length check-then-use fragment `lenCheck m cap` compiles to a single-read parser that is R-safe for `CopyInBounds cap` and R-valid for `lpParse cap`, while its read rematerialization, a private-memory refinement of it, is neither R-safe nor R-valid.
- `remat-robust-refinement-characterization` (characterization, T1): For every address `a`, check `check : Byte → Bool`, use `u : Byte → α` and failure value `e : α`, the rematerialization of `CheckUse.pure a check u e` (a fragment whose use and failure branch perform no further reads) robustly refines the original iff, whenever the check accepts some byte, every use value `u b'` (for every byte `b'`, including bytes the check rejects) is a result of the original: `u b` for some accepted `b`, or `e` when some byte `b` is rejected. For every region size `m + 1` and capacity `cap` with `cap < 255`, rematerializing `lenCheck m cap` is a private-memory refinement and not a robust refinement.
- `robust-refinement-preserves-exactly-rsafe` (characterization, T0): For all parsers `q` and `p`, `q` robustly refines `p` (`RobustRefines q p`: every result `q` returns against some writer, `p` returns against some writer) iff every predicate `safe : α → Prop` on result values that `p` satisfies against every writer, `q` satisfies against every writer. Hence, for every predicate `safe` and spec `spec`, if `RobustRefines q p` and `p` is R-safe for `safe` (respectively R-valid for `spec`), then `q` is R-safe for `safe` (respectively R-valid for `spec`). Robust refinement relates distinct parsers and does not transfer R-state: `rereadCompare` differs from `tagOnce 0`, robustly refines it, and is not R-state for `boolParse`, while `tagOnce 0` is. Observable-access refinement, in which every memory access is an observable event carrying the bytes seen, is equality of parsers (`ObsRefines q p ↔ q = p`).
- `validated-view-sound-without-foreign-writes` (theorem, T0): For every number `k` of later decodes and every writer `adv : Adversary 2` that changes nothing during the run of the view program (`adv t = adv 0` for every `t < 2 + 2 * k`), every decode returned by `viewProg k` (validate tag and payload once, then decode `k` times through the view, re-reading tag and payload without re-validating) is a valid tagged value (`ViewOK`). For every `k`, `viewProg k` implements `viewSpec k` in private memory.
- `copy-out-and-owned-decode-sound` (theorem, T1): For every number `k` of later decodes, byte-by-byte copy-out (`copyOutProg k`: copy tag and payload into private memory one byte at a time, at times `0` and `1`, then validate the copy and serve all decodes from it) and single-read decoding into an owned value (`ownedProg k`: read the tag; if it exceeds `1`, return the error result without reading the payload; otherwise read the payload once, validate, and serve all decodes from the owned value) are each single-read, implement `viewSpec k` in private memory and agree there with the view program `viewProg k`, and, against every writer, return a result that is `viewSpec k s'` for some byte vector `s'` and whose decodes are all valid tagged values (`RSafe ViewOK`). The two parsers differ in their memory accesses and agree in their results: for every `k` and every writer `adv`, copy-out performs two reads, owned decoding performs one read when the tag `adv 0 0` it reads at time `0` exceeds `1` and two reads otherwise, and both return the same result; for every `k` they are different parsers, and neither observably refines the other (`ObsRefines`). Neither is a consistent snapshot: against `copyTornAdv` (`(0, 2)` at time `0`, `(1, 1)` afterwards, both valid), `copyOutProg 1` and `ownedProg 1` each return `some [(0, 1)]`, a valid decode that is `viewSpec 1` of no state the writer produced; so neither `copyOutProg 1` nor `ownedProg 1` is R-state for `viewSpec 1`.

Non-claims for each result are listed with that result under Findings and again, collected per result, under Boundaries; cross-cutting non-claims and open questions are under Boundaries.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

**Scope.** These are statements about the toy model `Toy.DoubleFetch`; they neither establish nor refute the corresponding claims about real parsers, compilers, kernels, hypervisors, Rust or zerocopy. Model–system relation: none proved.

**Model fidelity.** A toy. Regions are `n` bytes (`Fin 256`); the writer is any function from times to region states; parsers are finite decision trees (`Prog`) with atomic one-byte reads and an atomic whole-region snapshot (`snap`); the clock advances by one per access. Copying a region one byte at a time (`byteCopy`, `copyParse`, `copyOutProg`) is therefore not atomic, and `snap` is an idealized atomic copy; this package neither establishes nor refutes atomicity of any real copy routine. Rematerialization is modelled on a check-then-use fragment (`CheckUse`). Leaves return values; an action such as "copy `len` bytes" is a result value checked by a predicate on results.

**Toolchain.** Lean `leanprover/lean4:v4.34.1` (GitHub `leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean and `Std`; no Mathlib and no other dependency. The Lake project in `lean/` declares one library, `DoubleFetch`, whose declarations live in the namespace `Toy.DoubleFetch`.

**Subjects and how they relate.** `REPORT.json` lists the Lean toolchain release that checks every proof, the papers cited as prior art, and the pinned documentation pages, advisory, patch and source file whose documented behaviour is quoted in modeling-bridge prose. The findings are statements about the toy model as checked by that toolchain. The papers are compared with the toy under each result's Prior art; the documentation, advisory, patch and source file are cited as documented behaviour of real systems. None of them is modelled, and no relation between any of them and the toy is proved.

**Relation to standard notions.** `RValid spec p` is a condition on each result: it is `spec s'` for some byte vector `s'`, which need not agree with any byte the writer wrote; per-byte provenance is the content of `singleRead_exec_eq_eval_assemble`. `RState spec p` asks that each result be `spec` of a state the writer actually produced, at any time `t` (not necessarily during the run). It differs from linearizability and from the regular and atomic registers of the distributed-computing literature in three ways (not proved here): it constrains one run in isolation, so it says nothing about the order of results of several runs; its witness time may lie outside the run; and an error result must also match a state whose spec is the error. `RSafe safe p` constrains result values through a predicate `safe : α → Prop`, which cannot mention the writer's states. `RobustRefines q p` compares the sets of results reachable against some writer; it is the toy instance of robust preservation of result properties.

**Real systems (derived (modeling bridge)).** The toy does not model data races. The Rust Reference (Rust 1.83.0, "Behavior considered undefined", https://doc.rust-lang.org/1.83.0/reference/behavior-considered-undefined.html) lists "Data races." as undefined behaviour, and the documentation of `core::ptr::read_volatile` (Rust core 1.83.0, https://doc.rust-lang.org/1.83.0/core/ptr/fn.read_volatile.html) states in its Safety section: "Just like in C, whether an operation is volatile has no bearing whatsoever on questions involving concurrent access from multiple threads. Volatile accesses behave exactly like non-atomic accesses in that regard. In particular, a race between a read_volatile and any write operation to the same location is undefined behavior." So in Rust a parser that reads memory another thread writes, through `&[u8]` or `read_volatile`, has undefined behaviour even if it reads each byte once; the toy results concern the values such a parser could observe if each access were atomic, and they neither establish nor refute anything about that undefined behaviour. Xen XSA-155 and the Linux memory-barriers documentation (quoted under Findings) describe compiler-generated double fetches and reloads; zerocopy's `TryFromBytes` methods are cited for their API shapes; no zerocopy position on concurrently written memory is asserted.

**Degenerate edges.** `n = 0`: `byteCopy` performs no access, a snapshot reads no address (`singleRead_zero_double_snap`), and no spec has an undetermined state (`not_hasUndeterminedState_of_region_zero`); `n = 1`: no spec has an undetermined state (`not_hasUndeterminedState_of_region_one`); length parsers use regions of `m + 1 ≥ 1` bytes, with `m = 0` meaning no payload; `cap = 0` is a zero-capacity buffer; `cap ≥ 255` makes the length check vacuous (`lenReread_rsafe_rvalid_of_255_le_cap`); `k = 0` later decodes makes `ViewOK` hold against every writer (`viewProg_zero_rsafe`). Version increments and checksums use wrapping addition modulo 256 (`Fin 256`).

## Findings

### Definitions

#### `Byte`, `Region`, `Adversary`, `Adversary.const`

```lean
-- lean/DoubleFetch/Basic.lean:31
abbrev Byte := Fin 256
```

```lean
-- lean/DoubleFetch/Basic.lean:34
abbrev Region (n : Nat) := Fin n → Byte
```

```lean
-- lean/DoubleFetch/Basic.lean:38
abbrev Adversary (n : Nat) := Nat → Region n
```

```lean
-- lean/DoubleFetch/Basic.lean:41
def Adversary.const {n : Nat} (s : Region n) : Adversary n := fun _ => s
```

*Captures.* A byte is `Fin 256`; the shared region is `n` bytes; a writer is the region state at each time step (the parser's `k`-th memory access sees `adv k`). `Adversary.const s` never writes. No constraint is placed on how the states change.

*Examples.* Computation examples `exec_example` (positive: the second access sees time `1`) and `exec_ne_eval_example` (negative: a changing writer is not private memory), both with the one-byte writer `sevenNine` (`7` at time `0`, `9` afterwards).

#### `Prog`

```lean
-- lean/DoubleFetch/Basic.lean:50-53
inductive Prog (n : Nat) (α : Type) : Type where
  | ret : α → Prog n α
  | read : Fin n → (Byte → Prog n α) → Prog n α
  | snap : (Region n → Prog n α) → Prog n α
```

*Captures.* A parser as a finite decision tree: one-byte reads whose continuation may pick later addresses from earlier bytes, atomic whole-region snapshots, and leaves. Every `Prog` terminates; retrying loops and randomized parsers are not expressible.

*Examples.* Instances throughout, for example `readTwice` (two reads of one address) and `dataDepProg` (second address chosen from the first byte).

#### `Prog.execFrom`, `Prog.exec`, `Prog.eval`

```lean
-- lean/DoubleFetch/Basic.lean:61-64
def execFrom : Prog n α → Adversary n → Nat → α
  | ret a, _, _ => a
  | read i k, adv, t => (k (adv t i)).execFrom adv (t + 1)
  | snap k, adv, t => (k (adv t)).execFrom adv (t + 1)
```

```lean
-- lean/DoubleFetch/Basic.lean:67
def exec (p : Prog n α) (adv : Adversary n) : α := p.execFrom adv 0
```

```lean
-- lean/DoubleFetch/Basic.lean:70-73
def eval : Prog n α → Region n → α
  | ret a, _ => a
  | read i k, s => (k (s i)).eval s
  | snap k, s => (k s).eval s
```

*Captures.* `exec` runs a parser against a writer, the clock advancing by one per access; `eval` runs it on private memory (no writer). `Prog.exec_const` shows they agree for the writer that never writes.

*Examples.* Positive: `exec_example`, `eval_example`. Negative: `exec_ne_eval_example`.

#### `Event`, `Prog.obsFrom`, `Prog.obs`

```lean
-- lean/DoubleFetch/Basic.lean:78-80
inductive Event (n : Nat) : Type where
  | rd : Fin n → Byte → Event n
  | sn : Region n → Event n
```

```lean
-- lean/DoubleFetch/Basic.lean:88-95
def obsFrom : Prog n α → Adversary n → Nat → List (Event n) × α
  | ret a, _, _ => ([], a)
  | read i k, adv, t =>
      let r := (k (adv t i)).obsFrom adv (t + 1)
      (Event.rd i (adv t i) :: r.1, r.2)
  | snap k, adv, t =>
      let r := (k (adv t)).obsFrom adv (t + 1)
      (Event.sn (adv t) :: r.1, r.2)
```

```lean
-- lean/DoubleFetch/Basic.lean:98
def obs (p : Prog n α) (adv : Adversary n) : List (Event n) × α := p.obsFrom adv 0
```

*Captures.* Observable-access semantics: every access is an event carrying the bytes seen; `Prog.obs_snd` shows the result component is `exec`.

*Examples.* Positive: `obs_example` (two events for two reads).

#### `Prog.SingleReadFrom`, `SingleRead`

```lean
-- lean/DoubleFetch/Basic.lean:105-109
def SingleReadFrom : Prog n α → (Fin n → Bool) → Prop
  | ret _, _ => True
  | read i k, vis =>
      vis i = false ∧ ∀ b, (k b).SingleReadFrom (fun j => if j = i then true else vis j)
  | snap k, vis => (∀ j, vis j = false) ∧ ∀ s, (k s).SingleReadFrom (fun _ => true)
```

```lean
-- lean/DoubleFetch/Basic.lean:136
def SingleRead (p : Prog n α) : Prop := p.SingleReadFrom (fun _ => false)
```

*Captures.* Single-read discipline: each address at most once per root-to-leaf path; a snapshot reads every address. Degenerate edge `n = 0`: a snapshot of the empty region reads no address, so repeated snapshots are single-read (`singleRead_zero_double_snap`); this is harmless because `Region 0` has exactly one element.

*Examples.* Positive: `lenOnce 0 4`, `dataDepProg` (`dataDepProg_singleRead`). Negative: `lenReread 0 4` (`singleRead_examples`), a read followed by a snapshot (`singleRead_read_then_snap_rejected`).

#### `Prog.NoSnap`

```lean
-- lean/DoubleFetch/Basic.lean:112-115
def NoSnap : Prog n α → Prop
  | ret _ => True
  | read _ k => ∀ b, (k b).NoSnap
  | snap _ => False
```

*Captures.* The parser uses one-byte reads and no snapshot.

*Examples.* Positive: `readFst`. Negative: `snapParse pairSpec` (`noSnap_examples`).

#### `Prog.assembleFrom`, `Prog.assemble`

```lean
-- lean/DoubleFetch/Basic.lean:120-124
def assembleFrom : Prog n α → Adversary n → Nat → Region n → Region n
  | ret _, _, _, d => d
  | read i k, adv, t, d =>
      fun j => if j = i then adv t i else (k (adv t i)).assembleFrom adv (t + 1) d j
  | snap _, adv, t, _ => adv t
```

```lean
-- lean/DoubleFetch/Basic.lean:127
def assemble (p : Prog n α) (adv : Adversary n) (d : Region n) : Region n := p.assembleFrom adv 0 d
```

*Captures.* The vector assembled from a run: bytes as read at the addresses read, a filler elsewhere (after a snapshot, the snapshot).

*Examples.* Computation: `assemble_example` (read address holds the byte read; unread address holds the filler).

#### `Prog.addrAt`

```lean
-- lean/DoubleFetch/Theory.lean:105-110
def addrAt : Prog n α → Region n → Nat → Option (Fin n)
  | ret _, _, _ => none
  | read i _, _, 0 => some i
  | read i k, s, m + 1 => (k (s i)).addrAt s m
  | snap _, _, 0 => none
  | snap k, s, m + 1 => (k s).addrAt s m
```

*Captures.* The address of the `m`-th access of the private-memory run on `s` (`none` after the run or at a snapshot). Used by the torn-value impossibility to build its writer (`Prog.execFrom_eq_eval_of_agree`).

*Examples.* Used in the proof of `not_rstate_of_noSnap_of_hasUndeterminedState`.

#### `RSafe`, `RValid`, `RState`, `RStateUnder`

```lean
-- lean/DoubleFetch/Basic.lean:140
def RSafe (safe : α → Prop) (p : Prog n α) : Prop := ∀ adv : Adversary n, safe (p.exec adv)
```

```lean
-- lean/DoubleFetch/Basic.lean:144-145
def RValid (spec : Region n → α) (p : Prog n α) : Prop :=
  ∀ adv : Adversary n, ∃ s' : Region n, p.exec adv = spec s'
```

```lean
-- lean/DoubleFetch/Basic.lean:151-152
def RState (spec : Region n → α) (p : Prog n α) : Prop :=
  ∀ adv : Adversary n, ∃ t : Nat, p.exec adv = spec (adv t)
```

```lean
-- lean/DoubleFetch/Basic.lean:155-156
def RStateUnder (W : Adversary n → Prop) (spec : Region n → α) (p : Prog n α) : Prop :=
  ∀ adv : Adversary n, W adv → ∃ t : Nat, p.exec adv = spec (adv t)
```

*Captures.* Robustness notions against every writer (or every writer satisfying `W`): the result satisfies a predicate `safe` on result values; the result is `spec s'` for some byte vector `s'`; the result is `spec (adv t)` for a state the writer produced at some time `t`. `safe` depends on the result value alone, not on the writer's states. `rstateUnder_true_iff` relates `RStateUnder` to `RState`.

*Examples.* `rsafe_examples`, `rvalid_examples`, `rstate_examples`, `rstateUnder_examples` (each with a positive and a negative instance).

#### `Implements`, `PrivRefines`, `ObsRefines`, `RobustRefines`

```lean
-- lean/DoubleFetch/Basic.lean:160
def Implements (p : Prog n α) (spec : Region n → α) : Prop := ∀ s : Region n, p.eval s = spec s
```

```lean
-- lean/DoubleFetch/Basic.lean:164
def PrivRefines (q p : Prog n α) : Prop := ∀ s : Region n, q.eval s = p.eval s
```

```lean
-- lean/DoubleFetch/Basic.lean:170-171
def ObsRefines (q p : Prog n α) : Prop :=
  ∀ adv : Adversary n, ∃ adv' : Adversary n, q.obs adv = p.obs adv'
```

```lean
-- lean/DoubleFetch/Basic.lean:176-177
def RobustRefines (q p : Prog n α) : Prop :=
  ∀ adv : Adversary n, ∃ adv' : Adversary n, q.exec adv = p.exec adv'
```

*Captures.* Private-memory correctness; refinement in private memory (equal results on every region); refinement in the observable-access semantics, which in this deterministic model is equality of parsers (`obsRefines_iff_eq`); robust result refinement: every result `q` returns against some writer, `p` returns against some writer. `RobustRefines q p` holds iff every R-safety property of `p` holds for `q` (`robustRefines_iff_preserves_rsafe`).

*Examples.* `implements_examples`, `privRefines_examples`, `obsRefines_examples`, `robustRefines_examples` (positive and negative each; the positive `RobustRefines` instance relates two distinct parsers).

#### `snapParse`, `readSeq`, `byteCopy`, `copyParse`

```lean
-- lean/DoubleFetch/Specs.lean:23
def snapParse (spec : Region n → α) : Prog n α := .snap fun s => .ret (spec s)
```

```lean
-- lean/DoubleFetch/Specs.lean:27-29
def readSeq : List (Fin n) → Region n → (Region n → Prog n α) → Prog n α
  | [], acc, k => k acc
  | i :: is, acc, k => .read i fun b => readSeq is (fun j => if j = i then b else acc j) k
```

```lean
-- lean/DoubleFetch/Specs.lean:33
def byteCopy (k : Region n → Prog n α) : Prog n α := readSeq (List.finRange n) (fun _ => 0) k
```

```lean
-- lean/DoubleFetch/Specs.lean:36
def copyParse (spec : Region n → α) : Prog n α := byteCopy fun s => .ret (spec s)
```

*Captures.* Snapshot parser; reading a list of addresses one byte at a time into an accumulator; copying the region byte by byte (address `j` at time `j`); parsing the private byte-by-byte copy. Degenerate edge `n = 0`: `List.finRange 0` is empty, so `byteCopy` performs no access.

*Examples.* `rvalid_examples` and `rstate_examples` use `copyParse pairSpec` and `snapParse pairSpec`.

#### `CheckUse`, `CheckUse.compile`, `CheckUse.remat`, `CheckUse.pure`

```lean
-- lean/DoubleFetch/Specs.lean:40-44
structure CheckUse (n : Nat) (α : Type) where
  addr : Fin n
  check : Byte → Bool
  use : Byte → Prog n α
  onFail : Prog n α
```

```lean
-- lean/DoubleFetch/Specs.lean:48-49
def CheckUse.compile (c : CheckUse n α) : Prog n α :=
  .read c.addr fun b => if c.check b then c.use b else c.onFail
```

```lean
-- lean/DoubleFetch/Specs.lean:53-54
def CheckUse.remat (c : CheckUse n α) : Prog n α :=
  .read c.addr fun b => if c.check b then .read c.addr c.use else c.onFail
```

```lean
-- lean/DoubleFetch/Specs.lean:58-59
def CheckUse.pure (addr : Fin n) (check : Byte → Bool) (u : Byte → α) (e : α) : CheckUse n α :=
  { addr := addr, check := check, use := fun b => .ret (u b), onFail := .ret e }
```

*Captures.* A check-then-use fragment; its compilation with one read; read rematerialization, where the use sees a fresh read of the same address instead of the local; the fragment whose use and failure branch perform no further reads.

*Examples.* `lenOnce`/`lenReread` and `tagOnce`/`tagReread` are `compile`/`remat` of `lenCheck` and `tagCheck`.

#### `lpParse`, `CopyInBounds`, `lenCheck`, `lenOnce`, `lenReread`, `lenFlipAdv`

```lean
-- lean/DoubleFetch/Specs.lean:75-76
def lpParse (cap : Nat) {m : Nat} (s : Region (m + 1)) : Option Nat :=
  if (s 0).val ≤ cap then some (s 0).val else none
```

```lean
-- lean/DoubleFetch/Specs.lean:80-82
def CopyInBounds (cap : Nat) : Option Nat → Prop
  | some len => len ≤ cap
  | none => True
```

```lean
-- lean/DoubleFetch/Specs.lean:86-87
def lenCheck (m cap : Nat) : CheckUse (m + 1) (Option Nat) :=
  CheckUse.pure 0 (fun b => decide (b.val ≤ cap)) (fun b => some b.val) none
```

```lean
-- lean/DoubleFetch/Specs.lean:90
def lenOnce (m cap : Nat) : Prog (m + 1) (Option Nat) := (lenCheck m cap).compile
```

```lean
-- lean/DoubleFetch/Specs.lean:94
def lenReread (m cap : Nat) : Prog (m + 1) (Option Nat) := (lenCheck m cap).remat
```

```lean
-- lean/DoubleFetch/Specs.lean:98-99
def lenFlipAdv (m cap : Nat) : Adversary (m + 1) :=
  fun t _ => if t = 0 then Fin.ofNat 256 cap else Fin.ofNat 256 (cap + 1)
```

*Captures.* A length-prefixed record header checked against a destination buffer of capacity `cap` (the source-side bound is not modelled); the in-bounds predicate on the action "copy `len` bytes"; single-read and double-fetch length parsers; the writer that raises the length after the check. `lenFlipAdv` reduces lengths modulo 256 (`Fin.ofNat 256`), which is the identity for `cap < 255`.

*Examples.* `lpParse_examples`, `copyInBounds_examples`.

#### `boolParse`, `ValidBoolOut`, `tagCheck`, `tagOnce`, `tagReread`, `tagFlipAdv`, `rereadCompare`, `rereadFallback`, `dataDepProg`

```lean
-- lean/DoubleFetch/Specs.lean:105-106
def boolParse {m : Nat} (s : Region (m + 1)) : Option Byte :=
  if (s 0).val ≤ 1 then some (s 0) else none
```

```lean
-- lean/DoubleFetch/Specs.lean:109-111
def ValidBoolOut : Option Byte → Prop
  | some b => b.val ≤ 1
  | none => True
```

```lean
-- lean/DoubleFetch/Specs.lean:115-116
def tagCheck (m : Nat) : CheckUse (m + 1) (Option Byte) :=
  CheckUse.pure 0 (fun b => decide (b.val ≤ 1)) (fun b => some b) none
```

```lean
-- lean/DoubleFetch/Specs.lean:119
def tagOnce (m : Nat) : Prog (m + 1) (Option Byte) := (tagCheck m).compile
```

```lean
-- lean/DoubleFetch/Specs.lean:123
def tagReread (m : Nat) : Prog (m + 1) (Option Byte) := (tagCheck m).remat
```

```lean
-- lean/DoubleFetch/Specs.lean:126
def tagFlipAdv (m : Nat) : Adversary (m + 1) := fun t _ => if t = 0 then 1 else 2
```

```lean
-- lean/DoubleFetch/Specs.lean:130-132
def rereadCompare : Prog 1 (Option Byte) :=
  .read 0 fun b => .read 0 fun b' =>
    .ret (if b = b' then boolParse (m := 0) (fun _ => b) else none)
```

```lean
-- lean/DoubleFetch/Specs.lean:63-65
def rereadFallback (spec : Region 1 → α) : Prog 1 α :=
  .read 0 fun b => .read 0 fun b' =>
    .ret (if b = b' then spec (fun _ => b) else spec (fun _ => 0))
```

```lean
-- lean/DoubleFetch/Specs.lean:136-137
def dataDepProg : Prog 3 Byte :=
  .read 0 fun b => if b.val = 0 then .read 1 .ret else .read 2 .ret
```

*Captures.* A byte later reinterpreted as a `bool` (the result is the raw byte, so the invalid byte `2` is representable); validity of the result; single-read and double-fetch `bool` parsers; the writer that flips `1` to `2`; re-read-and-compare; re-read with a fallback value on mismatch; a parser whose second address depends on the first byte.

*Examples.* `boolParse_examples`, `validBoolOut_examples`, `dataDepProg_examples`.

#### `pairSpec`, `ckParse`, `pairTornAdv`, `ckTornAdv`, `ckMixAdv`, `NoByteDeterminesOutput`, `HasUndeterminedState`, `andSpec`

```lean
-- lean/DoubleFetch/Specs.lean:142
def pairSpec (s : Region 2) : Byte × Byte := (s 0, s 1)
```

```lean
-- lean/DoubleFetch/Specs.lean:147-148
def ckParse (s : Region 3) : Option (Byte × Byte) :=
  if s 2 = s 0 + s 1 then some (s 0, s 1) else none
```

```lean
-- lean/DoubleFetch/Specs.lean:151
def pairTornAdv : Adversary 2 := fun t => if t = 0 then reg2 0 0 else reg2 1 1
```

```lean
-- lean/DoubleFetch/Specs.lean:155-156
def ckTornAdv : Adversary 3 :=
  fun t => if t = 0 then reg3 0 0 0 else if t = 1 then reg3 1 1 2 else reg3 2 255 1
```

```lean
-- lean/DoubleFetch/Specs.lean:176
def ckMixAdv : Adversary 3 := fun t => if t = 0 then reg3 0 0 0 else reg3 1 1 1
```

```lean
-- lean/DoubleFetch/Specs.lean:160-161
def NoByteDeterminesOutput {n : Nat} {α : Type} (spec : Region n → α) : Prop :=
  ∀ (i : Fin n) (v : Byte) (r : α), ∃ σ : Region n, σ i = v ∧ spec σ ≠ r
```

```lean
-- lean/DoubleFetch/Specs.lean:167-169
def HasUndeterminedState {n : Nat} {α : Type} (spec : Region n → α) : Prop :=
  ∃ s0 : Region n, (∀ r : α, ∃ σ : Region n, spec σ ≠ r) ∧
    ∀ (i : Fin n) (r : α), ∃ σ : Region n, σ i = s0 i ∧ spec σ ≠ r
```

```lean
-- lean/DoubleFetch/Specs.lean:172
def andSpec (s : Region 2) : Bool := decide (s 0 = 1) && decide (s 1 = 1)
```

*Captures.* Two-byte pair; a two-field record with a checksum computed by addition modulo 256 (wrapping `Fin 256` addition); writers used by the torn-value counterexamples; "no single byte value determines the output" (a sufficient condition on nonempty regions, `hasUndeterminedState_of_pos_of_noByteDeterminesOutput`); "some state has no byte that determines the output, and the spec is not constant" (the exact condition of the torn-value impossibility); two-byte boolean AND.

*Examples.* `ckParse_examples`, `noByteDeterminesOutput_examples`, `seqSpec_not_noByteDeterminesOutput`, `hasUndeterminedState_examples`, `andSpec_examples`.

#### `seqSpec`, `seqlockReader`, `VersionStep`, `OneStepVersionWriter`, `TwoStepVersionWriter`, `VersionPath`, `IncrementBoundedWriter`, `seqRogueAdv`, `seqTwoStepAdv`, `seqWrapAdv`

```lean
-- lean/DoubleFetch/Specs.lean:182-183
def seqSpec (s : Region 3) : Option (Byte × Byte) :=
  if (s 0).val % 2 = 0 then some (s 1, s 2) else none
```

```lean
-- lean/DoubleFetch/Specs.lean:187-192
def seqlockReader : Prog 3 (Option (Byte × Byte)) :=
  .read 0 fun v1 =>
    if v1.val % 2 = 0 then
      .read 1 fun d1 => .read 2 fun d2 => .read 0 fun v2 =>
        .ret (if v2 = v1 then some (d1, d2) else none)
    else .ret none
```

```lean
-- lean/DoubleFetch/Specs.lean:197-201
def VersionStep (s s' : Region 3) : Prop :=
  s' = s ∨
  ((s 0).val % 2 = 0 ∧ s' 0 = s 0 + 1 ∧ s' 1 = s 1 ∧ s' 2 = s 2) ∨
  ((s 0).val % 2 = 1 ∧ s' 0 = s 0) ∨
  ((s 0).val % 2 = 1 ∧ s' 0 = s 0 + 1 ∧ s' 1 = s 1 ∧ s' 2 = s 2)
```

```lean
-- lean/DoubleFetch/Specs.lean:205
def OneStepVersionWriter (adv : Adversary 3) : Prop := ∀ t, VersionStep (adv t) (adv (t + 1))
```

```lean
-- lean/DoubleFetch/Specs.lean:209-210
def TwoStepVersionWriter (adv : Adversary 3) : Prop :=
  ∀ t, ∃ mid : Region 3, VersionStep (adv t) mid ∧ VersionStep mid (adv (t + 1))
```

```lean
-- lean/DoubleFetch/Specs.lean:214-219
inductive VersionPath : Nat → Region 3 → Region 3 → Prop
  | refl (s : Region 3) : VersionPath 0 s s
  | stay {c : Nat} {s s' s'' : Region 3} :
      VersionStep s s' → s' 0 = s 0 → VersionPath c s' s'' → VersionPath c s s''
  | bump {c : Nat} {s s' s'' : Region 3} :
      VersionStep s s' → s' 0 = s 0 + 1 → VersionPath c s' s'' → VersionPath (c + 1) s s''
```

```lean
-- lean/DoubleFetch/Specs.lean:224-226
def IncrementBoundedWriter (B : Nat) (adv : Adversary 3) : Prop :=
  ∃ c0 c1 c2 : Nat, VersionPath c0 (adv 0) (adv 1) ∧ VersionPath c1 (adv 1) (adv 2) ∧
    VersionPath c2 (adv 2) (adv 3) ∧ c0 + c1 + c2 < B
```

```lean
-- lean/DoubleFetch/Specs.lean:229
def seqRogueAdv : Adversary 3 := fun t => reg3 0 (Fin.ofNat 256 t) (Fin.ofNat 256 t)
```

```lean
-- lean/DoubleFetch/Specs.lean:233
def seqTwoStepAdv : Adversary 3 := fun t => if t = 0 then reg3 0 0 0 else reg3 2 0 0
```

```lean
-- lean/DoubleFetch/Specs.lean:240
def seqWrapAdv : Adversary 3 := fun t => if t < 2 then reg3 0 0 0 else reg3 0 1 1
```

*Captures.* A versioned record (odd version: write in progress, error result); the seqlock-style reader, which returns at once on an odd first version and does not retry; one protocol step (version increments modulo 256); writers taking at most one or two protocol steps between reader accesses; protocol paths counting version increments; writers with fewer than `B` increments from time `0` to time `3`; writers used by counterexamples.

*Examples.* `versionStep_examples`, `oneStepVersionWriter_examples`, `twoStepVersionWriter_examples`, `versionPath_examples`, `incrementBoundedWriter_examples`, `rstateUnder_examples`.

#### `ValidE`, `ViewOK`, `viewUses`, `viewProg`, `viewSpec`, `copyOutProg`, `ownedProg`, `viewFlipAdv`, `copyTornAdv`, `validSwitchAdv`

```lean
-- lean/DoubleFetch/Specs.lean:246
def ValidE (tag payload : Byte) : Prop := tag.val = 0 ∨ (tag.val = 1 ∧ payload.val ≤ 1)
```

```lean
-- lean/DoubleFetch/Specs.lean:252-254
def ViewOK : Option (List (Byte × Byte)) → Prop
  | some l => ∀ x ∈ l, ValidE x.1 x.2
  | none => True
```

```lean
-- lean/DoubleFetch/Specs.lean:258-260
def viewUses : Nat → List (Byte × Byte) → Prog 2 (Option (List (Byte × Byte)))
  | 0, acc => .ret (some acc)
  | k + 1, acc => .read 0 fun t => .read 1 fun p => viewUses k ((t, p) :: acc)
```

```lean
-- lean/DoubleFetch/Specs.lean:263-264
def viewProg (k : Nat) : Prog 2 (Option (List (Byte × Byte))) :=
  .read 0 fun t => .read 1 fun p => if ValidE t p then viewUses k [] else .ret none
```

```lean
-- lean/DoubleFetch/Specs.lean:268-269
def viewSpec (k : Nat) (s : Region 2) : Option (List (Byte × Byte)) :=
  if ValidE (s 0) (s 1) then some (List.replicate k (s 0, s 1)) else none
```

```lean
-- lean/DoubleFetch/Specs.lean:274
def copyOutProg (k : Nat) : Prog 2 (Option (List (Byte × Byte))) := copyParse (viewSpec k)
```

```lean
-- lean/DoubleFetch/Specs.lean:281-284
def ownedProg (k : Nat) : Prog 2 (Option (List (Byte × Byte))) :=
  .read 0 fun t =>
    if 1 < t.val then .ret none
    else .read 1 fun p => if ValidE t p then .ret (some (List.replicate k (t, p))) else .ret none
```

```lean
-- lean/DoubleFetch/Specs.lean:288
def viewFlipAdv : Adversary 2 := fun t => if t < 2 then reg2 0 2 else reg2 1 2
```

```lean
-- lean/DoubleFetch/Specs.lean:292
def copyTornAdv : Adversary 2 := fun t => if t = 0 then reg2 0 2 else reg2 1 1
```

```lean
-- lean/DoubleFetch/Specs.lean:297
def validSwitchAdv : Adversary 2 := fun t => if t < 3 then reg2 1 1 else reg2 0 2
```

*Captures.* Validity of a tagged value (tag `0`, or tag `1` with a `bool` payload); every decode valid; later decodes through a view that re-read without re-validating; validate once then decode through the view; the spec of the decodes; byte-by-byte copy-out (`copyParse (viewSpec k)`: two one-byte reads at times `0` and `1` against every writer, then validation of the private copy; not an atomic snapshot); single-read decoding into an owned value that validates while it reads (it reads the tag at time `0` and, when the tag exceeds `1`, returns the error result without reading the payload; otherwise it reads the payload at time `1`); writers used by counterexamples (`validSwitchAdv` has a valid tagged value in every state).

*Examples.* `validE_examples`, `viewOK_examples`, `viewProg_example`, `viewSpec_examples`, `copyOutProg_example`, `ownedProg_examples` (positive: a valid decode; negative: the invalid tag `2` gives the error result after one access).

#### `reg2`, `reg3`, `fstSpec`, `readFst`, `seqSlowAdv`, `incr`

```lean
-- lean/DoubleFetch/Basic.lean:182
def reg2 (a b : Byte) : Region 2 := fun i => if i.val = 0 then a else b
```

```lean
-- lean/DoubleFetch/Basic.lean:185
def reg3 (a b c : Byte) : Region 3 := fun i => if i.val = 0 then a else if i.val = 1 then b else c
```

```lean
-- lean/DoubleFetch/Results.lean:896
def fstSpec (s : Region 2) : Byte := s 0
```

```lean
-- lean/DoubleFetch/Results.lean:899
def readFst : Prog 2 Byte := .read 0 .ret
```

```lean
-- lean/DoubleFetch/Results.lean:1244-1246
def seqSlowAdv : Adversary 3 := fun t =>
  if t = 0 then reg3 0 0 0 else if t = 1 then reg3 1 0 0 else if t = 2 then reg3 1 5 5
  else reg3 2 5 5
```

```lean
-- lean/DoubleFetch/Results.lean:1115-1117
def incr : Nat → Byte → Byte
  | 0, v => v
  | k + 1, v => incr k (v + 1)
```

*Captures.* Region literals and helpers used by examples, counterexamples and non-vacuity witnesses.

*Examples.* Used in the examples above.

Basis: execution (Lean kernel check), for every example theorem quoted in this section.

### Results

### `snapshot-parse-rstate`

- **Kind:** theorem. **Tier:** T0. **Depth:** definitional.
- **Lean:** `Toy.DoubleFetch.snapParse_exec_eq_and_rstate`

```lean
-- lean/DoubleFetch/Results.lean:22-24
theorem snapParse_exec_eq_and_rstate (spec : Region n → α) :
    (∀ adv : Adversary n, (snapParse spec).exec adv = spec (adv 0)) ∧
      RState spec (snapParse spec) := …
```

Unfolded (prose): for all `adv`, `(snapParse spec).exec adv = spec (adv 0)`, and for all `adv` there is a time `t` (namely `0`) with `(snapParse spec).exec adv = spec (adv t)`.

**Plain claim.** For every spec `spec : Region n → α` and every writer `adv : Adversary n`, the snapshot parser `snapParse spec` run by `Prog.exec` returns `spec (adv 0)`, the spec of the state at the time of its one atomic access; hence `snapParse spec` is R-state (`RState spec (snapParse spec)`). This is a reference point: it holds because the toy's `snap` primitive is atomic by definition.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| (none: the statements are unconditional in their displayed variables) | Records that nothing is assumed beyond the displayed types. | harmless |

**Non-vacuity witness.** Hypothesis-free; instantiated at the pair spec in `snapParse_pair_rstate_counterexample`. (`snapParse_pair_rstate_counterexample`)

**Non-claims.**

- R-state here follows from the toy's `snap` primitive, which copies all `n` bytes in one memory access by definition. This result neither establishes nor refutes atomicity of any real copy routine (`memcpy`, `copy_from_user`, a Rust slice copy, a struct assignment through a volatile pointer); in the toy, copying one byte at a time is `byteCopy`, which is not R-state (`copyParse_pair_torn_not_rstate`).
- Covers the parser that applies `spec` to the snapshot and reads nothing else; a parser that reads shared memory again after the snapshot is not `snapParse spec`.
- `RState` checks a single run against one writer, and its witness time ranges over all of `Nat` (here it is `0`, inside the run). It is not linearizability across several invocations and says nothing about the order of results of consecutive runs.
- The writer model is the full function space `Adversary n = Nat → Region n`: it fixes the region state seen by each memory access of the parser. Each one-byte `read` and each whole-region `snap` is atomic, and the clock advances by exactly one per access. Writes during a byte read, weak-memory reordering, and real timing are not modelled.
- These are statements about the toy model `Toy.DoubleFetch`; they neither establish nor refute the corresponding claims about real parsers, compilers, kernels, hypervisors, Rust or zerocopy. Model–system relation: none proved.

**Prior art.**

- Y. Afek, H. Attiya, D. Dolev, E. Gafni, M. Merritt, N. Shavit, "Atomic snapshots of shared memory", J. ACM 40(4):873-890, 1993, doi:10.1145/153724.153741 (author's copy: https://people.csail.mit.edu/shanir/publications/AADGMS.pdf): "This paper presents three wait-free implementations of atomic snapshot memory." There the memory is updated through the implementation's own update operation, so every writer follows a protocol; cited as contrast with the unconstrained writer here.
- M. P. Herlihy, J. M. Wing, "Linearizability: a correctness condition for concurrent objects", ACM TOPLAS 12(3):463-492, 1990, doi:10.1145/78969.78972 (bibliographic data checked against Crossref; not quoted). Cited for contrast: linearizability orders the operations of several concurrent invocations, whereas `RState` constrains one run in isolation.

**Design question.** When a parser must act on a state that actually existed in memory another party can write, does copying the whole region in one atomic step suffice? (Reference point: the atomicity is assumed by the model.)

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). The first non-claim, about real copy routines, rests on the definition of `snap` (one memory access returns all `n` bytes) and on the sources quoted in this report: none of the quoted passages states that `memcpy`, `copy_from_user`, a Rust slice copy or a struct assignment through a volatile pointer is atomic with respect to a concurrent writer, and the XSA-155 patch (quoted under `bytecopy-parse-diagonal-rvalid`) does not describe its volatile struct-assignment copy as atomic.

### `bytecopy-parse-diagonal-rvalid`

- **Kind:** theorem. **Tier:** T1. **Depth:** shallow.
- **Lean:** `Toy.DoubleFetch.copyParse_exec_eq_diagonal_and_rvalid`, `Toy.DoubleFetch.copyParse_singleRead_implements`

```lean
-- lean/DoubleFetch/Results.lean:30-32
theorem copyParse_exec_eq_diagonal_and_rvalid (spec : Region n → α) :
    (∀ adv : Adversary n, (copyParse spec).exec adv = spec (fun j => adv j.val j)) ∧
      RValid spec (copyParse spec) := by …
-- lean/DoubleFetch/Results.lean:41-42
theorem copyParse_singleRead_implements (spec : Region n → α) :
    SingleRead (copyParse spec) ∧ Implements (copyParse spec) spec := by …
```

Unfolded (prose): for all `adv`, `(copyParse spec).exec adv = spec (fun j => adv j.val j)`, and for all `adv` there is a byte vector `s'` with `(copyParse spec).exec adv = spec s'`; moreover `SingleRead (copyParse spec)` and `∀ s, (copyParse spec).eval s = spec s`.

**Plain claim.** For every spec `spec : Region n → α` and every writer `adv : Adversary n`, the byte-by-byte copy parser `copyParse spec` (reads address `j` at time `j`, for every address `j` of the region, then applies `spec` to the private copy) returns `spec (fun j => adv j.val j)`, the spec of the diagonal vector of bytes as read; hence it is R-valid (`RValid spec (copyParse spec)`). For every spec, `copyParse spec` is also single-read and implements `spec` in private memory (`copyParse_singleRead_implements`).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| (none: the statements are unconditional in their displayed variables) | Records that nothing is assumed beyond the displayed types. | harmless |

**Non-vacuity witness.** Hypothesis-free; computed on the pair spec in `copyParse_pair_torn_not_rstate`. (`copyParse_pair_torn_not_rstate`)

**Non-claims.**

- The diagonal vector need not be any state the writer produced; see `copyParse_pair_torn_not_rstate`.
- The access order `0, 1, …, n - 1` is a choice of `byteCopy`; another order gives another mix of times.
- Degenerate edge `n = 0`: `List.finRange 0` is empty, so `byteCopy` performs no memory access and the statement reduces to `spec` of the unique empty region (by unfolding the definitions; no separate theorem).
- The writer model is the full function space `Adversary n = Nat → Region n`: it fixes the region state seen by each memory access of the parser. Each one-byte `read` and each whole-region `snap` is atomic, and the clock advances by exactly one per access. Writes during a byte read, weak-memory reordering, and real timing are not modelled.
- These are statements about the toy model `Toy.DoubleFetch`; they neither establish nor refute the corresponding claims about real parsers, compilers, kernels, hypervisors, Rust or zerocopy. Model–system relation: none proved.

**Prior art.**

- XSA-155 patch "xsa155-xen-0001-xen-Add-RING_COPY_REQUEST.patch" (SHA-256 of the fetched file: `e52467fcec73bcc86d3e96d06f8ca8085ae56a83d2c42a30c16bc3dc630d8f8a`), https://xenbits.xen.org/xsa/xsa155-xen-0001-xen-Add-RING_COPY_REQUEST.patch: "Safe usage of a request generally requires taking a local copy." (xsa155-xen-0001-xen-Add-RING_COPY_REQUEST.patch:8-9) and, in the macro comment, "Use this in preference to RING_GET_REQUEST() so all processing is done on a local copy that cannot be modified by the other end." (xsa155-xen-0001-xen-Add-RING_COPY_REQUEST.patch:40-41, where each line carries the comment prefix "+ * ") The macro copies the request by a struct assignment from a volatile source; the patch does not describe the copy as atomic. In the toy, taking a local copy and parsing the copy instead of the shared bytes corresponds to `copyParse` (one-byte reads), not to `snap` (derived (modeling bridge)).
- P. Wang, J. Krinke, K. Lu, G. Li, S. Dodier-Lazaro, "How Double-Fetch Situations turn into Double-Fetch Vulnerabilities: A Study of Double Fetches in the Linux Kernel", 26th USENIX Security Symposium (USENIX Security 17), Vancouver, 2017, pp. 1-16, https://www.usenix.org/conference/usenixsecurity17/technical-sessions/presentation/wang-pengfei. Empirical study of double fetches in the Linux kernel and a static detector; informal.

**Design question.** Does copying shared bytes one at a time into private memory give the parser a consistent state, or merely some byte vector?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). Reading the XSA-155 local copy as `copyParse` rather than as `snapParse` rests on the patch text quoted under Prior art: `RING_COPY_REQUEST` copies a request by a struct assignment from a volatile source, and the patch does not describe the copy as atomic, so the toy represents the copy by one-byte reads (`byteCopy`). How a compiler emits that assignment (one access or several, and in which order) is not examined. The double-fetch studies under Prior art are cited for the bug class; they are informal, and no kernel code is modelled.

### `bytecopy-torn-not-rstate`

- **Kind:** counterexample. **Tier:** T1. **Depth:** definitional.
- **Lean:** `Toy.DoubleFetch.copyParse_pair_torn_not_rstate`

```lean
-- lean/DoubleFetch/Results.lean:54-57
theorem copyParse_pair_torn_not_rstate :
    (copyParse pairSpec).exec pairTornAdv = (0, 1) ∧
      (∀ t : Nat, (copyParse pairSpec).exec pairTornAdv ≠ pairSpec (pairTornAdv t)) ∧
      ¬ RState pairSpec (copyParse pairSpec) := by …
```

Unfolded (prose): `(copyParse pairSpec).exec pairTornAdv = (0, 1)`; for every `t`, `(copyParse pairSpec).exec pairTornAdv ≠ pairSpec (pairTornAdv t)`; and `¬ RState pairSpec (copyParse pairSpec)`.

**Plain claim.** Against the writer `pairTornAdv` (state `(0,0)` at time `0`, `(1,1)` at every later time), the byte-by-byte copy parser of the pair spec returns `(0, 1)`, which differs from `pairSpec (pairTornAdv t)` for every time `t`; so `copyParse pairSpec` is not R-state.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| (none: the statements are unconditional in their displayed variables) | Records that nothing is assumed beyond the displayed types. | harmless |

**Non-vacuity witness.** Closed concrete statement. (`copyParse_pair_torn_not_rstate`)

**Non-claims.**

- Does not say every writer tears the copy: against the writer that never writes, every parser returns its private-memory result (`Prog.exec_const`).
- The torn value `(0, 1)` reflects the access order `0, 1`; with the reverse order the same writer would yield `(1, 0)` (not proved here).
- The toy has one-byte reads and whole-region snapshots; a hardware load that reads an aligned multi-byte value in one access is not modelled.
- The writer model is the full function space `Adversary n = Nat → Region n`: it fixes the region state seen by each memory access of the parser. Each one-byte `read` and each whole-region `snap` is atomic, and the clock advances by exactly one per access. Writes during a byte read, weak-memory reordering, and real timing are not modelled.
- These are statements about the toy model `Toy.DoubleFetch`; they neither establish nor refute the corresponding claims about real parsers, compilers, kernels, hypervisors, Rust or zerocopy. Model–system relation: none proved.

**Prior art.**

- Folklore in systems security: validating shared bytes and then reading them again (time-of-check to time-of-use) is unsafe against a concurrent writer; no source states this toy formulation.

**Design question.** Is a byte-by-byte copy of shared memory a consistent snapshot?

Basis: execution (Lean kernel check).

### `single-read-exec-eq-eval-assemble`

- **Kind:** theorem. **Tier:** T1. **Depth:** substantive.
- **Lean:** `Toy.DoubleFetch.singleRead_exec_eq_eval_assemble`

```lean
-- lean/DoubleFetch/Results.lean:78-79
theorem singleRead_exec_eq_eval_assemble (p : Prog n α) (hp : SingleRead p)
    (adv : Adversary n) (d : Region n) : p.exec adv = p.eval (p.assemble adv d) := …
```

Unfolded (prose): if `SingleRead p` then for all `adv` and `d`, `p.exec adv = p.eval (p.assemble adv d)`.

**Plain claim.** For every parser `p : Prog n α` that satisfies the single-read discipline `SingleRead p` (on every root-to-leaf path each address is read at most once, a `snap` counting as a read of every address), every writer `adv` and every filler `d : Region n`, the run `p.exec adv` equals the private-memory result `p.eval (p.assemble adv d)` on the assembled vector, which holds at each address read during the run the byte observed there and `d` elsewhere. This covers parsers whose later addresses are computed from earlier bytes, such as `dataDepProg` (`dataDepProg_singleRead`).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hp : SingleRead p` | Rules out a second read of an address whose first read already steered the path or result. | tight: counterexample `lenReread_exec_ne_eval_assemble` (witness class: the double-fetch length parser `lenReread m cap` for any `m` and any `cap < 255`) |

**Non-vacuity witness.** `dataDepProg`, a single-read parser whose second address depends on the first byte (`dataDepProg_singleRead`); also `lenOnce m cap` and `copyParse spec`. (`dataDepProg_singleRead`)

**Non-claims.**

- The assembled vector is generally not a state the writer produced (`copyParse_pair_torn_not_rstate`), so the theorem yields R-valid, not R-state.
- `SingleRead` is sufficient for the R-valid conclusion, not necessary (`rereadCompare_implements_rvalid_rsafe_not_singleRead_not_rstate`).
- Parsers here read and return a value at a leaf; programs that write to the region or emit effects before finishing are not covered.
- Degenerate edge `n = 0`: a snapshot of the empty region reads no address, so `SingleRead` admits repeated snapshots there (`singleRead_zero_double_snap`); harmless, since `Region 0` has one element.
- In Rust, C and C++, a non-atomic read of a shared byte (for example through `&[u8]`), or a `core::ptr::read_volatile`, that races with a concurrent write to the same location is undefined behaviour (a data race), even if each byte is read once. The toy has no notion of a data race, so this result says nothing about avoiding that undefined behaviour (derived (modeling bridge); the Rust sources are quoted under Applicability).
- Source-level single reads need not survive compilation: a private-memory refinement can turn a single-read parser into a double fetch (`remat_lenCheck_singleRead_robust_to_not_rsafe_not_rvalid`). Which access semantics (volatile, atomic) prevent this in a real compiler is not modelled.
- The writer model is the full function space `Adversary n = Nat → Region n`: it fixes the region state seen by each memory access of the parser. Each one-byte `read` and each whole-region `snap` is atomic, and the clock advances by exactly one per access. Writes during a byte read, weak-memory reordering, and real timing are not modelled.
- These are statements about the toy model `Toy.DoubleFetch`; they neither establish nor refute the corresponding claims about real parsers, compilers, kernels, hypervisors, Rust or zerocopy. Model–system relation: none proved.

**Prior art.**

- N. Swamy, T. Ramananandro, A. Rastogi, I. Spiridonova, H. Ni, D. Malloy, J. Vazquez, M. Tang, O. Cardona, A. Gupta, "Hardening Attack Surfaces with Formally Proven Binary Format Parsers", PLDI 2022, pp. 31-45, doi:10.1145/3519939.3523708 (author's copy: http://www.normalesup.org/~ramanana/research/everparse/pldi2022/paper.pdf): "Adhering to this discipline ensures that the host observes a single logical snapshot of the packet even in the presence of concurrent mutations by the guest, inasmuch as what the host sees after a concurrent mutation, the untrusted guest could just as well have put in the packet to begin with." and "Our input streams are designed with a permission model that allows us to prove that validators are double-fetch free. In particular, reading a byte from the stream advances it and makes it provably impossible to read that byte again." The informal "single logical snapshot" there is what the toy calls R-valid (some byte vector), not R-state; EverParse3D mechanizes double-fetch freedom of generated validators, and the semantic statement here is not claimed to appear there in this form.
- P. Wang, J. Krinke, K. Lu, G. Li, S. Dodier-Lazaro, "How Double-Fetch Situations turn into Double-Fetch Vulnerabilities: A Study of Double Fetches in the Linux Kernel", 26th USENIX Security Symposium (USENIX Security 17), Vancouver, 2017, pp. 1-16, https://www.usenix.org/conference/usenixsecurity17/technical-sessions/presentation/wang-pengfei. Empirical study of double fetches in the Linux kernel and a static detector; informal.
- M. Jurczyk and G. Coldwind, "Identifying and Exploiting Windows Kernel Race Conditions via Memory Access Patterns", whitepaper accompanying the SyScan 2013 talk on Bochspwn, April 2013, https://research.google.com/pubs/archive/42189.pdf (also listed at https://research.google/pubs/identifying-and-exploiting-windows-kernel-race-conditions-via-memory-access-patterns/ and on the authors' talk page https://j00ru.vexillium.org/talks/syscan-bochspwn-exploiting-kernel-race-conditions/; title, authors and date checked against a search index, the PDF itself could not be fetched on the observation date). Describes double fetches of user-mode memory by kernel code and a memory-access-pattern detector; informal.

**Design question.** Is 'read each shared byte at most once' enough for a parser to behave as on some byte vector, even when addresses depend on earlier reads?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). For Rust, the data-race non-claim rests on the Rust Reference ("Data races." is listed as undefined behaviour) and on the Safety section of `core::ptr::read_volatile`, both quoted under Applicability; the statements about C and C++ in that non-claim are background and are not backed by a source quoted in this report. The toy's `read` is atomic and the toy has no notion of a data race. The comparison with EverParse3D interprets the informal sentences of Swamy et al. 2022 quoted under Prior art; no EverParse3D artifact is modelled. The double-fetch studies under Prior art are cited for the bug class; they are informal, and no kernel code is modelled.

### `single-read-rvalid`

- **Kind:** theorem. **Tier:** T1. **Depth:** shallow.
- **Lean:** `Toy.DoubleFetch.rvalid_of_singleRead_of_implements`

```lean
-- lean/DoubleFetch/Results.lean:84-85
theorem rvalid_of_singleRead_of_implements (spec : Region n → α) (p : Prog n α)
    (hp : SingleRead p) (himpl : Implements p spec) : RValid spec p := …
```

Unfolded (prose): if `SingleRead p` and `∀ s, p.eval s = spec s`, then `∀ adv, ∃ s', p.exec adv = spec s'`.

**Plain claim.** For every spec `spec` and parser `p`, if `p` is single-read (`SingleRead p`) and implements `spec` in private memory (`Implements p spec`: `p.eval s = spec s` for every region `s`), then `p` is R-valid for `spec`: against every writer its result is `spec s'` for some byte vector `s'`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hp : SingleRead p` | Excludes double fetches. | tight: counterexample `singleRead_hyp_counterexample_rvalid` (witness class: the double-fetch length parser on a one-byte region with `cap = 0`) |
| `himpl : Implements p spec` | Ties the parser to the spec on private memory. | tight: counterexample `implements_hyp_counterexample_rvalid` (witness class: a constant parser on a one-byte region) |

**Non-vacuity witness.** `lenOnce m cap` with `lpParse cap` (`lenOnce_singleRead_implements` states both hypotheses). (`lenOnce_singleRead_implements`)

**Non-claims.**

- R-valid allows a vector the writer never produced; it does not imply R-state.
- `SingleRead` is sufficient for `RValid`, not necessary (`rereadCompare_implements_rvalid_rsafe_not_singleRead_not_rstate`).
- `RValid spec p` is a condition on each result: it is `spec s'` for some byte vector `s'`, which need not agree with any byte the writer wrote; for example `Prog.ret r` is R-valid whenever `r` is in the image of `spec` (by the definition of `RValid`; no separate theorem). The per-byte provenance statement is `singleRead_exec_eq_eval_assemble`.
- In Rust, C and C++, a non-atomic read of a shared byte (for example through `&[u8]`), or a `core::ptr::read_volatile`, that races with a concurrent write to the same location is undefined behaviour (a data race), even if each byte is read once. The toy has no notion of a data race, so this result says nothing about avoiding that undefined behaviour (derived (modeling bridge); the Rust sources are quoted under Applicability).
- Source-level single reads need not survive compilation: a private-memory refinement can turn a single-read parser into a double fetch (`remat_lenCheck_singleRead_robust_to_not_rsafe_not_rvalid`). Which access semantics (volatile, atomic) prevent this in a real compiler is not modelled.
- The writer model is the full function space `Adversary n = Nat → Region n`: it fixes the region state seen by each memory access of the parser. Each one-byte `read` and each whole-region `snap` is atomic, and the clock advances by exactly one per access. Writes during a byte read, weak-memory reordering, and real timing are not modelled.
- These are statements about the toy model `Toy.DoubleFetch`; they neither establish nor refute the corresponding claims about real parsers, compilers, kernels, hypervisors, Rust or zerocopy. Model–system relation: none proved.

**Prior art.**

- N. Swamy, T. Ramananandro, A. Rastogi, I. Spiridonova, H. Ni, D. Malloy, J. Vazquez, M. Tang, O. Cardona, A. Gupta, "Hardening Attack Surfaces with Formally Proven Binary Format Parsers", PLDI 2022, pp. 31-45, doi:10.1145/3519939.3523708 (author's copy: http://www.normalesup.org/~ramanana/research/everparse/pldi2022/paper.pdf): "Adhering to this discipline ensures that the host observes a single logical snapshot of the packet even in the presence of concurrent mutations by the guest, inasmuch as what the host sees after a concurrent mutation, the untrusted guest could just as well have put in the packet to begin with." and "Our input streams are designed with a permission model that allows us to prove that validators are double-fetch free. In particular, reading a byte from the stream advances it and makes it provably impossible to read that byte again." The informal "single logical snapshot" there is what the toy calls R-valid (some byte vector), not R-state; EverParse3D mechanizes double-fetch freedom of generated validators, and the semantic statement here is not claimed to appear there in this form.
- Folklore in systems security: validating shared bytes and then reading them again (time-of-check to time-of-use) is unsafe against a concurrent writer; no source states this toy formulation.

**Design question.** Does every result of a single-read parser that is correct on private memory come from some byte vector?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). For Rust, the data-race non-claim rests on the Rust Reference ("Data races." is listed as undefined behaviour) and on the Safety section of `core::ptr::read_volatile`, both quoted under Applicability; the statements about C and C++ in that non-claim are background and are not backed by a source quoted in this report. The toy's `read` is atomic and the toy has no notion of a data race. The comparison with EverParse3D interprets the informal sentences of Swamy et al. 2022 quoted under Prior art; no EverParse3D artifact is modelled.

### `single-read-rsafe`

- **Kind:** theorem. **Tier:** T1. **Depth:** shallow.
- **Lean:** `Toy.DoubleFetch.rsafe_of_singleRead_of_staticSafe`

```lean
-- lean/DoubleFetch/Results.lean:91-92
theorem rsafe_of_singleRead_of_staticSafe (safe : α → Prop) (p : Prog n α)
    (hp : SingleRead p) (hsafe : ∀ s : Region n, safe (p.eval s)) : RSafe safe p := …
```

Unfolded (prose): if `SingleRead p` and `∀ s, safe (p.eval s)`, then `∀ adv, safe (p.exec adv)`.

**Plain claim.** For every predicate `safe : α → Prop` on result values (it depends on the result alone, not on the writer's states) and every parser `p`, if `p` is single-read and every private-memory result is safe (`∀ s, safe (p.eval s)`), then `p` is R-safe: against every writer its result satisfies `safe`. In the toy an action such as "copy `len` bytes" is represented by the result value `some len`, so `safe` can constrain the parameters of actions computed from the bytes read.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hp : SingleRead p` | Excludes double fetches. | tight: counterexample `singleRead_hyp_counterexample_rsafe` (witness class: the double-fetch length parser on a one-byte region with `cap = 0`) |
| `hsafe : ∀ s : Region n, safe (p.eval s)` | Safety on private memory. | tight: counterexample `staticSafe_hyp_counterexample_rsafe` (witness class: a constant parser on a one-byte region) |

**Non-vacuity witness.** `lenOnce 0 4` with `CopyInBounds 4` satisfies both hypotheses (`rsafe_of_singleRead_hyps_nonvacuous`). (`rsafe_of_singleRead_hyps_nonvacuous`)

**Non-claims.**

- `safe` is a predicate on the returned value. Relational properties that link the result to the writer's states (of type `Region n → α → Prop`), and actions that read shared memory again after the parser returns (for example copying `len` payload bytes from the shared region), are not covered.
- In Rust, C and C++, a non-atomic read of a shared byte (for example through `&[u8]`), or a `core::ptr::read_volatile`, that races with a concurrent write to the same location is undefined behaviour (a data race), even if each byte is read once. The toy has no notion of a data race, so this result says nothing about avoiding that undefined behaviour (derived (modeling bridge); the Rust sources are quoted under Applicability).
- Source-level single reads need not survive compilation: a private-memory refinement can turn a single-read parser into a double fetch (`remat_lenCheck_singleRead_robust_to_not_rsafe_not_rvalid`). Which access semantics (volatile, atomic) prevent this in a real compiler is not modelled.
- The writer model is the full function space `Adversary n = Nat → Region n`: it fixes the region state seen by each memory access of the parser. Each one-byte `read` and each whole-region `snap` is atomic, and the clock advances by exactly one per access. Writes during a byte read, weak-memory reordering, and real timing are not modelled.
- These are statements about the toy model `Toy.DoubleFetch`; they neither establish nor refute the corresponding claims about real parsers, compilers, kernels, hypervisors, Rust or zerocopy. Model–system relation: none proved.

**Prior art.**

- N. Swamy, T. Ramananandro, A. Rastogi, I. Spiridonova, H. Ni, D. Malloy, J. Vazquez, M. Tang, O. Cardona, A. Gupta, "Hardening Attack Surfaces with Formally Proven Binary Format Parsers", PLDI 2022, pp. 31-45, doi:10.1145/3519939.3523708 (author's copy: http://www.normalesup.org/~ramanana/research/everparse/pldi2022/paper.pdf): "Adhering to this discipline ensures that the host observes a single logical snapshot of the packet even in the presence of concurrent mutations by the guest, inasmuch as what the host sees after a concurrent mutation, the untrusted guest could just as well have put in the packet to begin with." and "Our input streams are designed with a permission model that allows us to prove that validators are double-fetch free. In particular, reading a byte from the stream advances it and makes it provably impossible to read that byte again." The informal "single logical snapshot" there is what the toy calls R-valid (some byte vector), not R-state; EverParse3D mechanizes double-fetch freedom of generated validators, and the semantic statement here is not claimed to appear there in this form.
- Folklore in systems security: validating shared bytes and then reading them again (time-of-check to time-of-use) is unsafe against a concurrent writer; no source states this toy formulation.

**Design question.** Does private-memory safety of a single-read parser carry over to a concurrent writer?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). For Rust, the data-race non-claim rests on the Rust Reference ("Data races." is listed as undefined behaviour) and on the Safety section of `core::ptr::read_volatile`, both quoted under Applicability; the statements about C and C++ in that non-claim are background and are not backed by a source quoted in this report. The toy's `read` is atomic and the toy has no notion of a data race. The comparison with EverParse3D interprets the informal sentences of Swamy et al. 2022 quoted under Prior art; no EverParse3D artifact is modelled.

### `single-read-not-necessary`

- **Kind:** counterexample. **Tier:** T1. **Depth:** shallow.
- **Lean:** `Toy.DoubleFetch.rereadCompare_implements_rvalid_rsafe_not_singleRead_not_rstate`

```lean
-- lean/DoubleFetch/Results.lean:261-264
theorem rereadCompare_implements_rvalid_rsafe_not_singleRead_not_rstate :
    Implements rereadCompare boolParse ∧ RValid boolParse rereadCompare ∧
      RSafe ValidBoolOut rereadCompare ∧ ¬ SingleRead rereadCompare ∧
      ¬ RState boolParse rereadCompare := by …
```

Unfolded (prose): `∀ s, rereadCompare.eval s = boolParse s`; `∀ adv, ∃ s', rereadCompare.exec adv = boolParse s'`; `∀ adv, ValidBoolOut (rereadCompare.exec adv)`; `¬ SingleRead rereadCompare`; and `¬ ∀ adv, ∃ t, rereadCompare.exec adv = boolParse (adv t)`.

**Plain claim.** The re-read-and-compare parser `rereadCompare` on a one-byte region (read the byte twice; return the error result `none` if the two reads differ, otherwise decode the byte with `boolParse`) implements `boolParse` in private memory, is R-valid for `boolParse` and R-safe for `ValidBoolOut`, is not single-read, and is not R-state for `boolParse`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| (none: the statements are unconditional in their displayed variables) | Records that nothing is assumed beyond the displayed types. | harmless |

**Non-vacuity witness.** Closed concrete statement. (`rereadCompare_implements_rvalid_rsafe_not_singleRead_not_rstate`)

**Non-claims.**

- It does not show that re-reading is as good as reading once: `rereadCompare` is not R-state (against a writer showing `0` then `1` it returns `none`, although every state the writer produced is a valid `bool`).
- The mismatch branch returns `none`, which lies in the image of `boolParse`. Specs without an error result admit the same phenomenon: for every spec on a one-byte region, `rereadFallback spec` returns `spec` of the zero byte on a mismatch, implements `spec`, is R-valid for it, and is not single-read (`rereadFallback_implements_rvalid_not_singleRead`).
- The writer model is the full function space `Adversary n = Nat → Region n`: it fixes the region state seen by each memory access of the parser. Each one-byte `read` and each whole-region `snap` is atomic, and the clock advances by exactly one per access. Writes during a byte read, weak-memory reordering, and real timing are not modelled.
- These are statements about the toy model `Toy.DoubleFetch`; they neither establish nor refute the corresponding claims about real parsers, compilers, kernels, hypervisors, Rust or zerocopy. Model–system relation: none proved.

**Prior art.**

- Folklore in systems security: validating shared bytes and then reading them again (time-of-check to time-of-use) is unsafe against a concurrent writer; no source states this toy formulation.

**Design question.** Is reading each byte at most once necessary for robustness, or a sufficient condition that robust parsers may violate?

Basis: execution (Lean kernel check).

### `rvalid-iff-robust-refinement-of-single-read-implementation`

- **Kind:** characterization. **Tier:** T1. **Depth:** shallow.
- **Lean:** `Toy.DoubleFetch.rvalid_iff_robustRefines_singleRead_implementation`, `Toy.DoubleFetch.rvalid_iff_robustRefines_copyParse`

```lean
-- lean/DoubleFetch/Results.lean:220-221
theorem rvalid_iff_robustRefines_singleRead_implementation (spec : Region n → α) (p : Prog n α) :
    RValid spec p ↔ ∃ q : Prog n α, SingleRead q ∧ Implements q spec ∧ RobustRefines p q := by …
-- lean/DoubleFetch/Results.lean:234-235
theorem rvalid_iff_robustRefines_copyParse (spec : Region n → α) (p : Prog n α) :
    RValid spec p ↔ RobustRefines p (copyParse spec) := by …
```

Unfolded (prose): `(∀ adv, ∃ s', p.exec adv = spec s') ↔ ∃ q, SingleRead q ∧ (∀ s, q.eval s = spec s) ∧ ∀ adv, ∃ adv', p.exec adv = q.exec adv'`, and `(∀ adv, ∃ s', p.exec adv = spec s') ↔ ∀ adv, ∃ adv', p.exec adv = (copyParse spec).exec adv'`.

**Plain claim.** For every spec `spec : Region n → α` and every parser `p`, `p` is R-valid for `spec` iff there is a single-read parser `q` that implements `spec` in private memory such that `p` robustly refines `q` (`RobustRefines p q`: every result `p` returns against some writer, `q` returns against some writer). For every spec, the single-read implementation can be taken to be `copyParse spec`: `p` is R-valid for `spec` iff `RobustRefines p (copyParse spec)`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| (none: the statements are unconditional in their displayed variables) | Records that nothing is assumed beyond the displayed types. | harmless |

**Non-vacuity witness.** Both sides hold for `rereadCompare` and `boolParse` with `q = tagOnce 0` (`robustRefines_transfer_nonvacuous`), and both fail for `lenReread 0 4` and `lpParse 4` (`rvalid_examples`). (`robustRefines_transfer_nonvacuous`)

**Non-claims.**

- It characterizes R-valid, not R-state: `rereadCompare` robustly refines the single-read `tagOnce 0` and is R-valid, but it is not R-state (`robustRefines_rereadCompare_tagOnce_not_preserves_rstate`).
- Refinement here is one-directional. The two equivalence readings, agreement against every writer and agreement in private memory, fail (`rvalid_equivalence_readings_refuted`).
- The characterization is close to the definitions: every byte vector is the diagonal vector of some writer. Its use is to name the notion of 'behaves like a single-read parser' under which the folklore statement holds.
- The writer model is the full function space `Adversary n = Nat → Region n`: it fixes the region state seen by each memory access of the parser. Each one-byte `read` and each whole-region `snap` is atomic, and the clock advances by exactly one per access. Writes during a byte read, weak-memory reordering, and real timing are not modelled.
- These are statements about the toy model `Toy.DoubleFetch`; they neither establish nor refute the corresponding claims about real parsers, compilers, kernels, hypervisors, Rust or zerocopy. Model–system relation: none proved.

**Prior art.**

- N. Swamy, T. Ramananandro, A. Rastogi, I. Spiridonova, H. Ni, D. Malloy, J. Vazquez, M. Tang, O. Cardona, A. Gupta, "Hardening Attack Surfaces with Formally Proven Binary Format Parsers", PLDI 2022, pp. 31-45, doi:10.1145/3519939.3523708 (author's copy: http://www.normalesup.org/~ramanana/research/everparse/pldi2022/paper.pdf): "Adhering to this discipline ensures that the host observes a single logical snapshot of the packet even in the presence of concurrent mutations by the guest, inasmuch as what the host sees after a concurrent mutation, the untrusted guest could just as well have put in the packet to begin with." and "Our input streams are designed with a permission model that allows us to prove that validators are double-fetch free. In particular, reading a byte from the stream advances it and makes it provably impossible to read that byte again." The informal "single logical snapshot" there is what the toy calls R-valid (some byte vector), not R-state; EverParse3D mechanizes double-fetch freedom of generated validators, and the semantic statement here is not claimed to appear there in this form.
- C. Abate, R. Blanco, D. Garg, C. Hritcu, M. Patrignani, J. Thibault, "Journey Beyond Full Abstraction: Exploring Robust Property Preservation for Secure Compilation", 2019 IEEE 32nd Computer Security Foundations Symposium (CSF), doi:10.1109/CSF.2019.00025 (long version arXiv:1807.04603): "We are the first to thoroughly explore a large space of formal secure compilation criteria based on robust property preservation, i.e., the preservation of properties satisfied against arbitrary adversarial contexts." and "For each of the studied criteria we propose an equivalent "property-free" characterization that clarifies which proof techniques apply." The toy's `robustRefines_iff_preserves_rsafe` is a property-free characterization of this kind for result properties, with the writer as the adversarial context.

**Design question.** Is 'R-valid' the same as 'behaves like some single-read parser', and under which notion of 'behaves like'?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). The comparison with EverParse3D interprets the informal sentences of Swamy et al. 2022 quoted under Prior art; no EverParse3D artifact is modelled.

### `rvalid-equivalence-readings-refuted`

- **Kind:** counterexample. **Tier:** T1. **Depth:** shallow.
- **Lean:** `Toy.DoubleFetch.rvalid_equivalence_readings_refuted`

```lean
-- lean/DoubleFetch/Results.lean:424-428
theorem rvalid_equivalence_readings_refuted (m cap : Nat) (hcap : cap < 255) :
    (RValid boolParse rereadCompare ∧
      ¬ ∃ q : Prog 1 (Option Byte), SingleRead q ∧ ∀ adv, q.exec adv = rereadCompare.exec adv) ∧
    (SingleRead (lenOnce m cap) ∧ RValid (lpParse cap) (lenOnce m cap) ∧
      PrivRefines (lenReread m cap) (lenOnce m cap) ∧ ¬ RValid (lpParse cap) (lenReread m cap)) := …
```

Unfolded (prose): if `cap < 255`: `RValid boolParse rereadCompare` and no `q : Prog 1 (Option Byte)` with `SingleRead q` has `q.exec adv = rereadCompare.exec adv` for all `adv`; and `SingleRead (lenOnce m cap)`, `RValid (lpParse cap) (lenOnce m cap)`, `∀ s, (lenReread m cap).eval s = (lenOnce m cap).eval s`, `¬ RValid (lpParse cap) (lenReread m cap)`.

**Plain claim.** Two equivalence readings of 'R-valid iff equivalent to a single-read parser' fail. (i) Agreement against every writer: `rereadCompare` is R-valid for `boolParse`, but no single-read parser on a one-byte region returns the same result as `rereadCompare` against every writer. (ii) Agreement in private memory: for every region size `m + 1` and capacity `cap` with `cap < 255`, the double-fetch length parser `lenReread m cap` agrees in private memory with `lenOnce m cap` (`PrivRefines (lenReread m cap) (lenOnce m cap)`), which is single-read and R-valid for `lpParse cap`, yet `lenReread m cap` is not R-valid for `lpParse cap`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hcap : cap < 255` | Some byte fails the length check, so the re-read can exceed the capacity. | tight: counterexample `lenReread_cap255_counterexample` (witness class: an instance with `m = 0` and `cap = 255`) |

**Non-vacuity witness.** `cap = 4` satisfies `hcap` (`lenReread_cap_lt_255_nonvacuous`). (`lenReread_cap_lt_255_nonvacuous`)

**Non-claims.**

- The theorem refutes the backward direction of reading (ii): for `cap < 255`, agreeing in private memory with the single-read parser `lenOnce m cap`, which is R-valid for `lpParse cap`, does not make `lenReread m cap` R-valid for `lpParse cap`. Whether the forward direction holds depends on what the single-read witness must satisfy. With a witness that is R-valid for the spec, it holds: for every spec `spec` and every parser `p`, if `RValid spec p`, then `copyParse (fun s => p.eval s)` is single-read, is R-valid for `spec`, and agrees with `p` in private memory (`rvalid_imp_exists_singleRead_rvalid_privRefines`). With a witness that implements the spec in private memory, it fails: for every spec `spec` and every parser `p`, a single-read parser that implements `spec` and agrees with `p` in private memory exists iff `p` itself implements `spec` (`exists_singleRead_implements_privRefines_iff_implements`; when `p` implements `spec`, `copyParse spec` is such a parser, by `copyParse_singleRead_implements`), and the constant parser `Prog.ret (0, 0)` is R-valid for `pairSpec` but agrees in private memory with no single-read parser that implements `pairSpec` (`rvalid_not_imp_exists_singleRead_implements_privRefines`).
- The characterization that holds uses one-directional robust refinement (`rvalid_iff_robustRefines_singleRead_implementation`).
- Degenerate edge `cap ≥ 255`: every byte passes the length check and `lenReread m cap` is R-safe and R-valid (`lenReread_rsafe_rvalid_of_255_le_cap`).
- The writer model is the full function space `Adversary n = Nat → Region n`: it fixes the region state seen by each memory access of the parser. Each one-byte `read` and each whole-region `snap` is atomic, and the clock advances by exactly one per access. Writes during a byte read, weak-memory reordering, and real timing are not modelled.
- These are statements about the toy model `Toy.DoubleFetch`; they neither establish nor refute the corresponding claims about real parsers, compilers, kernels, hypervisors, Rust or zerocopy. Model–system relation: none proved.

**Prior art.**

- Folklore in systems security: validating shared bytes and then reading them again (time-of-check to time-of-use) is unsafe against a concurrent writer; no source states this toy formulation.

**Design question.** Which readings of 'R-valid iff equivalent to some single-read parser' are false?

Basis: execution (Lean kernel check).

### `length-reread-out-of-bounds-and-invalid`

- **Kind:** counterexample. **Tier:** T1. **Depth:** shallow.
- **Lean:** `Toy.DoubleFetch.lenReread_flip_out_of_bounds_and_invalid`, `Toy.DoubleFetch.lenReread_not_rsafe_not_rvalid`, `Toy.DoubleFetch.lenReread_implements`, `Toy.DoubleFetch.lenOnce_singleRead_implements`, `Toy.DoubleFetch.lenOnce_rsafe_rvalid`

```lean
-- lean/DoubleFetch/Results.lean:367-370
theorem lenReread_flip_out_of_bounds_and_invalid (m cap : Nat) (hcap : cap < 255) :
    (lenReread m cap).exec (lenFlipAdv m cap) = some (cap + 1) ∧
      ¬ CopyInBounds cap ((lenReread m cap).exec (lenFlipAdv m cap)) ∧
      ∀ s' : Region (m + 1), (lenReread m cap).exec (lenFlipAdv m cap) ≠ lpParse cap s' := by …
-- lean/DoubleFetch/Results.lean:386-387
theorem lenReread_not_rsafe_not_rvalid (m cap : Nat) (hcap : cap < 255) :
    ¬ RSafe (CopyInBounds cap) (lenReread m cap) ∧ ¬ RValid (lpParse cap) (lenReread m cap) := by …
-- lean/DoubleFetch/Results.lean:359
theorem lenReread_implements (m cap : Nat) : Implements (lenReread m cap) (lpParse cap) := by …
-- lean/DoubleFetch/Results.lean:339-340
theorem lenOnce_singleRead_implements (m cap : Nat) :
    SingleRead (lenOnce m cap) ∧ Implements (lenOnce m cap) (lpParse cap) := by …
-- lean/DoubleFetch/Results.lean:347-348
theorem lenOnce_rsafe_rvalid (m cap : Nat) :
    RSafe (CopyInBounds cap) (lenOnce m cap) ∧ RValid (lpParse cap) (lenOnce m cap) := by …
```

Unfolded (prose): if `cap < 255`: `(lenReread m cap).exec (lenFlipAdv m cap) = some (cap + 1)`, which violates `CopyInBounds cap` and differs from `lpParse cap s'` for every `s'`, so `¬ RSafe (CopyInBounds cap) (lenReread m cap)` and `¬ RValid (lpParse cap) (lenReread m cap)`; for all `m cap`, `Implements (lenReread m cap) (lpParse cap)`, `SingleRead (lenOnce m cap)`, `Implements (lenOnce m cap) (lpParse cap)`, `RSafe (CopyInBounds cap) (lenOnce m cap)` and `RValid (lpParse cap) (lenOnce m cap)`.

**Plain claim.** For every region size `m + 1` and capacity `cap` with `cap < 255`, against the writer `lenFlipAdv m cap` (length byte `cap` at time `0`, `cap + 1` afterwards) the double-fetch length parser `lenReread m cap` (read the length, check `len ≤ cap`, read the length again, copy the re-read length) returns `some (cap + 1)`: copying `cap + 1` bytes into the buffer of capacity `cap` is out of bounds, and the result equals `lpParse cap s'` for no byte vector `s'`; so `lenReread m cap` is neither R-safe for `CopyInBounds cap` nor R-valid for `lpParse cap`. For every `m` and `cap`, `lenReread m cap` implements `lpParse cap` in private memory, and `lenOnce m cap` is single-read, implements `lpParse cap`, and is R-safe and R-valid.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hcap : cap < 255` (first two theorems) | Some byte fails the length check; bytes are below 256. | tight: counterexample `lenReread_cap255_counterexample` (witness class: an instance with `m = 0` and `cap = 255`) |

**Non-vacuity witness.** `m = 0`, `cap = 4` (`lenReread_cap_lt_255_nonvacuous`: `4 < 255` and the parser returns `some 5`). (`lenReread_cap_lt_255_nonvacuous`)

**Non-claims.**

- Degenerate edges: the region has `m + 1 ≥ 1` bytes, so the empty region is excluded; at `m = 0` the region holds the length byte and no payload; at `cap = 0` every nonzero length is out of bounds; for `cap ≥ 255` every byte passes the check and `lenReread m cap` is R-safe and R-valid (`lenReread_rsafe_rvalid_of_255_le_cap`).
- The toy models the destination bound `len ≤ cap`, not the source-side bound that `len` payload bytes are present.
- The writer model is the full function space `Adversary n = Nat → Region n`: it fixes the region state seen by each memory access of the parser. Each one-byte `read` and each whole-region `snap` is atomic, and the clock advances by exactly one per access. Writes during a byte read, weak-memory reordering, and real timing are not modelled.
- These are statements about the toy model `Toy.DoubleFetch`; they neither establish nor refute the corresponding claims about real parsers, compilers, kernels, hypervisors, Rust or zerocopy. Model–system relation: none proved.

**Prior art.**

- P. Wang, J. Krinke, K. Lu, G. Li, S. Dodier-Lazaro, "How Double-Fetch Situations turn into Double-Fetch Vulnerabilities: A Study of Double Fetches in the Linux Kernel", 26th USENIX Security Symposium (USENIX Security 17), Vancouver, 2017, pp. 1-16, https://www.usenix.org/conference/usenixsecurity17/technical-sessions/presentation/wang-pengfei. Empirical study of double fetches in the Linux kernel and a static detector; informal.
- M. Xu, C. Qian, K. Lu, M. Backes, T. Kim, "Precise and Scalable Detection of Double-Fetch Bugs in OS Kernels", IEEE Symposium on Security and Privacy 2018, pp. 661-678, doi:10.1109/SP.2018.00017 (bibliographic data checked against Crossref; not quoted). Cited for the bug class (a value checked after one fetch and used after another).
- M. Jurczyk and G. Coldwind, "Identifying and Exploiting Windows Kernel Race Conditions via Memory Access Patterns", whitepaper accompanying the SyScan 2013 talk on Bochspwn, April 2013, https://research.google.com/pubs/archive/42189.pdf (also listed at https://research.google/pubs/identifying-and-exploiting-windows-kernel-race-conditions-via-memory-access-patterns/ and on the authors' talk page https://j00ru.vexillium.org/talks/syscan-bochspwn-exploiting-kernel-race-conditions/; title, authors and date checked against a search index, the PDF itself could not be fetched on the observation date). Describes double fetches of user-mode memory by kernel code and a memory-access-pattern detector; informal.

**Design question.** Does a bounds check on a shared length protect a copy that re-reads the length?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). The double-fetch studies under Prior art are cited for the bug class; they are informal, and no kernel code is modelled.

### `tag-reread-invalid-bool`

- **Kind:** counterexample. **Tier:** T1. **Depth:** shallow.
- **Lean:** `Toy.DoubleFetch.tagReread_flip_invalid_bool`, `Toy.DoubleFetch.tagReread_not_rsafe_not_rvalid`, `Toy.DoubleFetch.tagReread_implements`, `Toy.DoubleFetch.tagOnce_singleRead_implements`, `Toy.DoubleFetch.tagOnce_rsafe_rvalid`

```lean
-- lean/DoubleFetch/Results.lean:466-469
theorem tagReread_flip_invalid_bool (m : Nat) :
    (tagReread m).exec (tagFlipAdv m) = some 2 ∧
      ¬ ValidBoolOut ((tagReread m).exec (tagFlipAdv m)) ∧
      ∀ s' : Region (m + 1), (tagReread m).exec (tagFlipAdv m) ≠ boolParse s' := by …
-- lean/DoubleFetch/Results.lean:487-488
theorem tagReread_not_rsafe_not_rvalid (m : Nat) :
    ¬ RSafe ValidBoolOut (tagReread m) ∧ ¬ RValid boolParse (tagReread m) := by …
-- lean/DoubleFetch/Results.lean:458
theorem tagReread_implements (m : Nat) : Implements (tagReread m) boolParse := by …
-- lean/DoubleFetch/Results.lean:438-439
theorem tagOnce_singleRead_implements (m : Nat) :
    SingleRead (tagOnce m) ∧ Implements (tagOnce m) boolParse := by …
-- lean/DoubleFetch/Results.lean:446-447
theorem tagOnce_rsafe_rvalid (m : Nat) :
    RSafe ValidBoolOut (tagOnce m) ∧ RValid boolParse (tagOnce m) := by …
```

Unfolded (prose): `(tagReread m).exec (tagFlipAdv m) = some 2`, which violates `ValidBoolOut` and differs from `boolParse s'` for every `s'`, so `¬ RSafe ValidBoolOut (tagReread m)` and `¬ RValid boolParse (tagReread m)`; `Implements (tagReread m) boolParse`, `SingleRead (tagOnce m)`, `Implements (tagOnce m) boolParse`, `RSafe ValidBoolOut (tagOnce m)` and `RValid boolParse (tagOnce m)`.

**Plain claim.** For every region size `m + 1`, against the writer `tagFlipAdv m` (byte `1` at time `0`, `2` afterwards) the double-fetch `bool` parser `tagReread m` (validate that the byte is `0` or `1`, then read it again and hand on the re-read byte as a `bool`) returns `some 2`, which is not a valid `bool` representation (`¬ ValidBoolOut (some 2)`) and equals `boolParse s'` for no byte vector `s'`; so `tagReread m` is neither R-safe for `ValidBoolOut` nor R-valid for `boolParse`. Both `tagReread m` and the single-read `tagOnce m` implement `boolParse` in private memory, and `tagOnce m` is single-read, R-safe for `ValidBoolOut` and R-valid for `boolParse`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| (none: the statements are unconditional in their displayed variables) | Records that nothing is assumed beyond the displayed types. | harmless |

**Non-vacuity witness.** Closed in `m`; holds for every `m`. (`tagReread_flip_invalid_bool`)

**Non-claims.**

- The result is the raw byte (`Option Byte`), so the invalid `bool` byte `2` is representable in the toy. In Rust, producing a `bool` other than `0` or `1` is undefined behaviour (Rust Reference, "Invalid values", quoted below), so the toy's `some 2` corresponds to a value a Rust program must never produce (derived (modeling bridge)).
- The writer model is the full function space `Adversary n = Nat → Region n`: it fixes the region state seen by each memory access of the parser. Each one-byte `read` and each whole-region `snap` is atomic, and the clock advances by exactly one per access. Writes during a byte read, weak-memory reordering, and real timing are not modelled.
- These are statements about the toy model `Toy.DoubleFetch`; they neither establish nor refute the corresponding claims about real parsers, compilers, kernels, hypervisors, Rust or zerocopy. Model–system relation: none proved.

**Prior art.**

- The Rust Reference (Rust 1.83.0), "Behavior considered undefined", https://doc.rust-lang.org/1.83.0/reference/behavior-considered-undefined.html, section "Invalid values": "The Rust compiler assumes that all values produced during program execution are “valid”, and producing an invalid value is hence immediate UB." and "A bool value must be false (0) or true (1)."
- zerocopy 0.8.64, https://docs.rs/zerocopy/0.8.64/zerocopy/trait.TryFromBytes.html: `fn try_ref_from_bytes(source: &[u8]) -> Result<&Self, TryCastError<&[u8], Self>> where Self: KnownLayout + Immutable`, "If the bytes of source are a valid instance of Self, this method returns a reference to those bytes interpreted as a Self." Cited for the shape validate-then-reference; no zerocopy position on concurrently written memory is asserted.
- Folklore in systems security: validating shared bytes and then reading them again (time-of-check to time-of-use) is unsafe against a concurrent writer; no source states this toy formulation.

**Design question.** Does a validity check on a shared byte protect a typed use that re-reads the byte?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). Reading the toy's `some 2` as an invalid Rust `bool` rests on the Rust Reference's "Invalid values" rule quoted under Prior art ("A bool value must be false (0) or true (1)."); the toy returns the raw byte and models no Rust type. zerocopy's `try_ref_from_bytes` is cited for its validate-then-reference API shape, from its documentation; no zerocopy position on concurrently written memory is asserted.

### `checksum-torn-value-matches-no-state`

- **Kind:** counterexample. **Tier:** T1. **Depth:** shallow.
- **Lean:** `Toy.DoubleFetch.ckParse_torn_passes_checksum_matches_no_state`, `Toy.DoubleFetch.copyParse_ckParse_twoValidStates`, `Toy.DoubleFetch.copyParse_singleRead_implements`

```lean
-- lean/DoubleFetch/Results.lean:499-503
theorem ckParse_torn_passes_checksum_matches_no_state :
    (∀ t : Nat, ckParse (ckTornAdv t) ≠ none) ∧
      (copyParse ckParse).exec ckTornAdv = some (0, 1) ∧
      (copyParse ckParse).exec ckTornAdv = ckParse (reg3 0 1 1) ∧
      ∀ t : Nat, (copyParse ckParse).exec ckTornAdv ≠ ckParse (ckTornAdv t) := by …
-- lean/DoubleFetch/Results.lean:544-547
theorem copyParse_ckParse_twoValidStates (A B : Region 3) (hA : A 2 = A 0 + A 1)
    (hB : B 2 = B 0 + B 1) (adv : Adversary 3) (hadv : ∀ t, adv t = A ∨ adv t = B)
    (hpass : (copyParse ckParse).exec adv ≠ none) :
    (copyParse ckParse).exec adv = ckParse A ∨ (copyParse ckParse).exec adv = ckParse B := by …
-- lean/DoubleFetch/Results.lean:41-42
theorem copyParse_singleRead_implements (spec : Region n → α) :
    SingleRead (copyParse spec) ∧ Implements (copyParse spec) spec := by …
```

Unfolded (prose): every `ckParse (ckTornAdv t)` is not `none`; `(copyParse ckParse).exec ckTornAdv = some (0, 1) = ckParse (reg3 0 1 1)`; and for every `t` it differs from `ckParse (ckTornAdv t)`. If `A 2 = A 0 + A 1`, `B 2 = B 0 + B 1`, every `adv t` is `A` or `B`, and the result is not `none`, then the result is `ckParse A` or `ckParse B`. For every `spec`: `SingleRead (copyParse spec)` and `∀ s, (copyParse spec).eval s = spec s` (`Implements (copyParse spec) spec`).

**Plain claim.** Against the writer `ckTornAdv` (states `(0,0,0)`, `(1,1,2)`, then `(2,255,1)` from time `2` on, each passing the checksum, which is addition modulo 256), the byte-by-byte copy parser `copyParse ckParse`, which is single-read (`copyParse_singleRead_implements`), returns `some (0, 1)`; this equals `ckParse (reg3 0 1 1)`, the result for a checksum-passing vector, but differs from `ckParse (ckTornAdv t)` for every time `t`. With two states this cannot happen when both pass the checksum: for all regions `A` and `B` that both pass the checksum and every writer whose every state is `A` or `B`, every checksum-passing result of `copyParse ckParse` equals `ckParse A` or `ckParse B` (`copyParse_ckParse_twoValidStates`).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hA : A 2 = A 0 + A 1` (in `copyParse_ckParse_twoValidStates`) | The first state passes the checksum. | tight: counterexample `copyParse_ckParse_twoValidStates_hA_counterexample` (witness class: two states `(1,1,1)` (failing) and `(0,0,0)`) |
| `hB : B 2 = B 0 + B 1` | The second state passes the checksum. | tight: counterexample `copyParse_ckParse_twoValidStates_hA_counterexample` (witness class: the same instance with `A` and `B` exchanged) |
| `hadv : ∀ t, adv t = A ∨ adv t = B` | The writer shows two states. | tight: counterexample `copyParse_ckParse_twoValidStates_hadv_counterexample` (witness class: the three-state writer `ckTornAdv`) |
| `hpass : (copyParse ckParse).exec adv ≠ none` | The torn result passes the checksum. | tight: counterexample `copyParse_ckParse_twoValidStates_hpass_counterexample` (witness class: two passing states `(0,0,0)` and `(1,1,2)` whose diagonal mix fails the checksum) |

**Non-vacuity witness.** The first theorem is closed; all hypotheses of `copyParse_ckParse_twoValidStates` hold for the passing states `(0,0,0)` and `(1,1,2)` and a writer that switches between them after time `2` (`copyParse_ckParse_twoValidStates_nonvacuous`). (`ckParse_torn_passes_checksum_matches_no_state`, `copyParse_ckParse_twoValidStates_nonvacuous`)

**Non-claims.**

- With one checksum-passing and one failing state, a checksum-passing torn result can match neither state (`copyParse_ckParse_twoValidStates_hA_counterexample`), so the two-state statement fails without `hA` (or `hB`).
- The toy's checksum is unkeyed addition modulo 256 against an unbounded writer; whether a keyed cryptographic MAC against a computationally bounded writer prevents torn accepted results is not addressed (not proved either way).
- The cancellation used by the two-state statement holds for addition modulo 256; other checksum functions are not covered.
- The writer model is the full function space `Adversary n = Nat → Region n`: it fixes the region state seen by each memory access of the parser. Each one-byte `read` and each whole-region `snap` is atomic, and the clock advances by exactly one per access. Writes during a byte read, weak-memory reordering, and real timing are not modelled.
- These are statements about the toy model `Toy.DoubleFetch`; they neither establish nor refute the corresponding claims about real parsers, compilers, kernels, hypervisors, Rust or zerocopy. Model–system relation: none proved.

**Prior art.**

- Folklore in systems security: validating shared bytes and then reading them again (time-of-check to time-of-use) is unsafe against a concurrent writer; no source states this toy formulation.

**Design question.** Does an integrity check over the bytes read guarantee a state that actually existed?

Basis: execution (Lean kernel check).

### `torn-value-impossibility`

- **Kind:** impossibility. **Tier:** T1. **Depth:** substantive.
- **Lean:** `Toy.DoubleFetch.not_rstate_of_noSnap_of_hasUndeterminedState`, `Toy.DoubleFetch.hasUndeterminedState_iff_no_noSnap_rstate`, `Toy.DoubleFetch.pairSpec_hasUndeterminedState`, `Toy.DoubleFetch.ckParse_hasUndeterminedState`, `Toy.DoubleFetch.seqSpec_hasUndeterminedState`, `Toy.DoubleFetch.andSpec_hasUndeterminedState`, `Toy.DoubleFetch.viewSpec_hasUndeterminedState`, `Toy.DoubleFetch.not_hasUndeterminedState_of_region_zero`, `Toy.DoubleFetch.not_hasUndeterminedState_of_region_one`

```lean
-- lean/DoubleFetch/Results.lean:648-649
theorem not_rstate_of_noSnap_of_hasUndeterminedState (spec : Region n → α)
    (hspec : HasUndeterminedState spec) (p : Prog n α) (hp : p.NoSnap) : ¬ RState spec p := by …
-- lean/DoubleFetch/Results.lean:735-736
theorem hasUndeterminedState_iff_no_noSnap_rstate (spec : Region n → α) :
    HasUndeterminedState spec ↔ ∀ p : Prog n α, p.NoSnap → ¬ RState spec p := by …
-- lean/DoubleFetch/Results.lean:819
theorem pairSpec_hasUndeterminedState : HasUndeterminedState pairSpec := …
-- lean/DoubleFetch/Results.lean:824
theorem ckParse_hasUndeterminedState : HasUndeterminedState ckParse := …
-- lean/DoubleFetch/Results.lean:830
theorem seqSpec_hasUndeterminedState : HasUndeterminedState seqSpec := by …
-- lean/DoubleFetch/Results.lean:856
theorem andSpec_hasUndeterminedState : HasUndeterminedState andSpec := by …
-- lean/DoubleFetch/Results.lean:873
theorem viewSpec_hasUndeterminedState (k : Nat) : HasUndeterminedState (viewSpec k) := by …
-- lean/DoubleFetch/Results.lean:770-771
theorem not_hasUndeterminedState_of_region_zero {α : Type} (spec : Region 0 → α) :
    ¬ HasUndeterminedState spec := by …
-- lean/DoubleFetch/Results.lean:777-778
theorem not_hasUndeterminedState_of_region_one {α : Type} (spec : Region 1 → α) :
    ¬ HasUndeterminedState spec := by …
```

Unfolded (prose): if `∃ s0, (∀ r, ∃ σ, spec σ ≠ r) ∧ ∀ i r, ∃ σ, σ i = s0 i ∧ spec σ ≠ r` and `p.NoSnap`, then `¬ ∀ adv, ∃ t, p.exec adv = spec (adv t)`; and that condition on `spec` holds iff `∀ p, p.NoSnap → ¬ RState spec p`.

**Plain claim.** For every region size `n` (including `0` and `1`), every spec `spec : Region n → α` and every parser `p` that uses one-byte reads and no snapshot (`p.NoSnap`): if `spec` has an undetermined state (`HasUndeterminedState spec`: some region state `s0` such that `spec` is not constant and, for every address `i` and every candidate output `r`, some region that agrees with `s0` at `i` has an output different from `r`), then `p` is not R-state for `spec`; the parser need not implement `spec`. Conversely, if `spec` has no undetermined state, some snapshot-free parser is R-state for `spec` (`hasUndeterminedState_iff_no_noSnap_rstate`). The pair spec, the checksum spec, the seqlock spec, two-byte boolean AND and the tagged-value spec `viewSpec k` (for every `k`) have undetermined states; no spec on a region of size `0` or `1` has one.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hspec : HasUndeterminedState spec` (in `not_rstate_of_noSnap_of_hasUndeterminedState`) | Lets the writer surround each byte the parser reads with bytes that move the spec away from the parser's result. | tight: counterexample `readFst_rstate_counterexample` (witness class: a two-byte region with the spec returning byte `0`) |
| `hp : p.NoSnap` (in `not_rstate_of_noSnap_of_hasUndeterminedState`) | Excludes the atomic whole-region read. | tight: counterexample `snapParse_pair_rstate_counterexample` (witness class: the snapshot parser of the pair spec on a two-byte region) |

**Non-vacuity witness.** `n = 2`, `pairSpec`, and the snapshot-free `copyParse pairSpec` (`torn_impossibility_nonvacuous`). (`torn_impossibility_nonvacuous`)

**Positive control.** Nearby settings in which R-state holds, each changing one condition: the snapshot parser of the pair spec (it drops `hp`; `snapParse_pair_rstate_counterexample`), and the snapshot-free seqlock reader for the seqlock spec, which has an undetermined state, against writers that follow the version protocol with one step per access (the writer constraint is the one change; `seqlock_positive_control`).

**Non-claims.**

- Proved escape hatches, each of which defeats the impossibility in the toy: (a) an atomic whole-region read (`snap`; `snapParse_exec_eq_and_rstate`, `snapParse_pair_rstate_counterexample`); (b) a constrained writer, such as one following a version protocol with one step per access (`seqlock_positive_control`); (c) a spec with no undetermined state, for example one determined by a single byte (`readFst_rstate_counterexample`, and in general the converse direction of `hasUndeterminedState_iff_no_noSnap_rstate`). Relaxations that are unaddressed or unmodelled, and are neither proved nor refuted to defeat the impossibility: (d) a weaker consistency notion, such as accepted-result consistency (`p.exec adv = some v → ∃ t, spec (adv t) = some v`): the writer built in the proof may use states whose output is the error result, and accepted-result consistency against writers restricted to valid or authenticated states is not addressed (not proved either way), although `ckParse_torn_passes_checksum_matches_no_state` shows that `copyParse ckParse` violates it for a writer whose states all pass the checksum; (e) parsers outside `Prog`: retrying loops (every `Prog` terminates), randomized parsers, and atomic reads of several but not all addresses are not modelled.
- `RState` lets the time `t` range over all of `Nat`, beyond the parser's run; the impossibility therefore also excludes the notion restricted to the access window.
- The R-state parser built for the converse direction reads bytes one at a time until one byte determines the output; it is a construction for the proof, not a recommended parser.
- The writer model is the full function space `Adversary n = Nat → Region n`: it fixes the region state seen by each memory access of the parser. Each one-byte `read` and each whole-region `snap` is atomic, and the clock advances by exactly one per access. Writes during a byte read, weak-memory reordering, and real timing are not modelled.
- These are statements about the toy model `Toy.DoubleFetch`; they neither establish nor refute the corresponding claims about real parsers, compilers, kernels, hypervisors, Rust or zerocopy. Model–system relation: none proved.

**Prior art.**

- Y. Afek, H. Attiya, D. Dolev, E. Gafni, M. Merritt, N. Shavit, "Atomic snapshots of shared memory", J. ACM 40(4):873-890, 1993, doi:10.1145/153724.153741 (author's copy: https://people.csail.mit.edu/shanir/publications/AADGMS.pdf): "This paper presents three wait-free implementations of atomic snapshot memory." There the memory is updated through the implementation's own update operation, so every writer follows a protocol; cited as contrast with the unconstrained writer here.
- L. Lamport, "Concurrent reading and writing", Communications of the ACM 20(11):806-811, 1977, doi:10.1145/359863.359878 (author's copy: https://lamport.azurewebsites.net/pubs/rd-wr.pdf). "Our algorithm maintains two version numbers for the data: v1 and v2. The writer increments v1 before writing the data item and increments v2 after writing. The reader reads v2 before reading the data item and v1 after reading it. If it finds them equal, then it knows that it read a single version of the data." On bounded counters: "Suppose we know that at most P write operations can occur during a single iteration of the reading loop, and a single digit can assume P + 1 distinct values. Then we can let v1 and v2 be single-digit variables which cycle through P + 1 or more values". (The PDF text extraction renders "v1" as "vl".) The paper assumes that reading and writing a single digit are atomic, and its reader repeats on a mismatch. The toy uses one counter with odd/even phases (the seqlock form) instead of two counters, and its reader returns an error instead of repeating.
- M. P. Herlihy, J. M. Wing, "Linearizability: a correctness condition for concurrent objects", ACM TOPLAS 12(3):463-492, 1990, doi:10.1145/78969.78972 (bibliographic data checked against Crossref; not quoted). Cited for contrast: linearizability orders the operations of several concurrent invocations, whereas `RState` constrains one run in isolation.
- Folklore in systems security: validating shared bytes and then reading them again (time-of-check to time-of-use) is unsafe against a concurrent writer; no source states this toy formulation.

**Design question.** For which specs can a byte-at-a-time parser recover a state that actually existed, when the writer is untrusted?

Basis: execution (Lean kernel check).

### `seqlock-rstate-one-step-protocol-writer`

- **Kind:** theorem. **Tier:** T0. **Depth:** shallow.
- **Lean:** `Toy.DoubleFetch.seqlock_rstate_of_oneStepVersionWriter`

```lean
-- lean/DoubleFetch/Results.lean:969-971
theorem seqlock_rstate_of_oneStepVersionWriter (adv : Adversary 3)
    (hW : OneStepVersionWriter adv) :
    ∃ t : Nat, t ≤ 3 ∧ seqlockReader.exec adv = seqSpec (adv t) := by …
```

Unfolded (prose): if `∀ t, VersionStep (adv t) (adv (t + 1))` then `∃ t, t ≤ 3 ∧ seqlockReader.exec adv = seqSpec (adv t)`.

**Plain claim.** For every writer `adv : Adversary 3` that follows the version protocol and takes at most one protocol step between consecutive reader accesses (`OneStepVersionWriter adv`: each step leaves the state unchanged, begins a write by incrementing an even version, changes data under an odd version, or ends a write by incrementing an odd version; increments are modulo 256), the seqlock reader `seqlockReader` (read the version; if it is odd, return `none` at once; otherwise read the two data bytes and the version again, and return the data iff the two version reads agree, otherwise `none`) returns `seqSpec (adv t)` for some time `t ≤ 3`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hW : OneStepVersionWriter adv` | The writer follows the version protocol, one step per reader access. | tight: counterexample `seqlock_not_rstate_rogueWriter`, `seqlock_not_rstateUnder_twoStepVersionWriter` (witness class: a writer that changes the data under an unchanged even version (torn `some` result); a protocol writer taking two steps between two accesses, with no data change and no wraparound (error result while no state of the writer has an odd version)) |

**Non-vacuity witness.** `seqSlowAdv`, a one-step protocol writer that writes during the read (`seqlock_oneStep_nonvacuous`). (`seqlock_oneStep_nonvacuous`)

**Non-claims.**

- The one-step bound serves the error case of a reader that does not retry: when the version changes between two accesses, R-state needs some state of the writer with an odd version to match the result `none`. Two protocol steps between accesses, with no data change and no wraparound, already break R-state (`seqlock_not_rstateUnder_twoStepVersionWriter`). This bound is unrelated to counter wraparound; consistency of accepted results under a bound on version increments is `seqlock-accepted-consistent-under-increment-bound`.
- The writer's transitions after time `3` do not affect the reader's run; `OneStepVersionWriter` quantifies over all times, which is more than the proof uses.
- The protocol is a hypothesis about the writer; the theorem gives nothing against a writer that ignores it, such as an untrusted party (`seqlock_not_rstate_rogueWriter`).
- Memory-model requirements of real seqlocks are not modelled: in C11, C++11 and Rust, reading the protected data non-atomically while a writer modifies it is a data race, and implementations use atomic accesses with acquire/release ordering or fences. The toy's accesses are atomic and sequentially ordered by construction (derived (modeling bridge)).
- The writer model is the full function space `Adversary n = Nat → Region n`: it fixes the region state seen by each memory access of the parser. Each one-byte `read` and each whole-region `snap` is atomic, and the clock advances by exactly one per access. Writes during a byte read, weak-memory reordering, and real timing are not modelled.
- These are statements about the toy model `Toy.DoubleFetch`; they neither establish nor refute the corresponding claims about real parsers, compilers, kernels, hypervisors, Rust or zerocopy. Model–system relation: none proved.

**Prior art.**

- L. Lamport, "Concurrent reading and writing", Communications of the ACM 20(11):806-811, 1977, doi:10.1145/359863.359878 (author's copy: https://lamport.azurewebsites.net/pubs/rd-wr.pdf). "Our algorithm maintains two version numbers for the data: v1 and v2. The writer increments v1 before writing the data item and increments v2 after writing. The reader reads v2 before reading the data item and v1 after reading it. If it finds them equal, then it knows that it read a single version of the data." On bounded counters: "Suppose we know that at most P write operations can occur during a single iteration of the reading loop, and a single digit can assume P + 1 distinct values. Then we can let v1 and v2 be single-digit variables which cycle through P + 1 or more values". (The PDF text extraction renders "v1" as "vl".) The paper assumes that reading and writing a single digit are atomic, and its reader repeats on a mismatch. The toy uses one counter with odd/even phases (the seqlock form) instead of two counters, and its reader returns an error instead of repeating.
- H.-J. Boehm, "Can seqlocks get along with programming language memory models?", Proceedings of the 2012 ACM SIGPLAN Workshop on Memory Systems Performance and Correctness (MSPC 2012), pp. 12-20, doi:10.1145/2247684.2247688 (bibliographic data checked against Crossref; not quoted). Cited for the memory-model side of seqlocks, which the toy does not model.

**Design question.** What must a writer promise for a version check to give a non-retrying reader a state that actually existed?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). The memory-model non-claim rests on the Rust Reference's listing of data races as undefined behaviour (quoted under Applicability) and on Boehm 2012 (cited under Prior art, not quoted) for seqlocks under language memory models; the statements about C11 and C++11 and about how implementations order their accesses are background and are not backed by a source quoted in this report. The toy's accesses are atomic and sequentially ordered by construction.

### `seqlock-accepted-consistent-under-increment-bound`

- **Kind:** theorem. **Tier:** T0. **Depth:** shallow.
- **Lean:** `Toy.DoubleFetch.seqlock_accepted_eq_seqSpec_adv0_of_incrementBound`, `Toy.DoubleFetch.versionPath_any`

```lean
-- lean/DoubleFetch/Results.lean:1173-1175
theorem seqlock_accepted_eq_seqSpec_adv0_of_incrementBound (adv : Adversary 3)
    (hW : IncrementBoundedWriter 256 adv) (d : Byte × Byte)
    (hacc : seqlockReader.exec adv = some d) : seqSpec (adv 0) = some d := by …
-- lean/DoubleFetch/Results.lean:1149
theorem versionPath_any (s s' : Region 3) : ∃ c : Nat, VersionPath c s s' := by …
```

Unfolded (prose): if `∃ c0 c1 c2, VersionPath c0 (adv 0) (adv 1) ∧ VersionPath c1 (adv 1) (adv 2) ∧ VersionPath c2 (adv 2) (adv 3) ∧ c0 + c1 + c2 < 256` and `seqlockReader.exec adv = some d`, then `seqSpec (adv 0) = some d`; and for all `s s'`, `∃ c, VersionPath c s s'`.

**Plain claim.** For every writer `adv : Adversary 3` that follows the version protocol, with any number of protocol steps between consecutive reader accesses, and increments the version fewer than 256 times in total from time `0` to time `3` (`IncrementBoundedWriter 256 adv`; the version byte wraps modulo 256), and every `d`, if `seqlockReader` accepts with `some d`, then `seqSpec (adv 0) = some d`. Without a bound on increments the protocol constrains nothing: every region state reaches every other by a protocol path (`versionPath_any`).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hW : IncrementBoundedWriter 256 adv` (in `seqlock_accepted_eq_seqSpec_adv0_of_incrementBound`) | Fewer increments than counter values, so an unchanged version means no write began. | tight: counterexample `seqlock_accepted_torn_of_256Increments` (witness class: a protocol writer, bounded by `257`, that takes exactly 256 version increments between the reader's reads of the first and the second data byte (times `1` and `2`; `IncrementBoundedWriter` allows any number of protocol steps between consecutive accesses); the reader accepts the torn pair `some (0, 1)`, which is `seqSpec` of the writer's state at no time `t`) |
| `hacc : seqlockReader.exec adv = some d` (in `seqlock_accepted_eq_seqSpec_adv0_of_incrementBound`) | The result is accepted. | tight: counterexample `seqlock_accepted_hacc_counterexample` (witness class: the writer that never writes, with an odd version) |

**Non-vacuity witness.** The writer that never writes, with version `0`, is bounded and accepted with `some (5, 5)` (`seqlock_incrementBound_nonvacuous`). (`seqlock_incrementBound_nonvacuous`)

**Non-claims.**

- The theorem concerns accepted results: it says nothing about the result `none`. A reader that retries on `none`, as in Lamport's algorithm, is outside the model (every `Prog` terminates).
- The bound counts version increments, not complete writes; a complete write increments the version twice. The toy fixes an 8-bit version; other counter widths are not modelled (not proved either way).
- Memory-model requirements of real seqlocks are not modelled: in C11, C++11 and Rust, reading the protected data non-atomically while a writer modifies it is a data race, and implementations use atomic accesses with acquire/release ordering or fences. The toy's accesses are atomic and sequentially ordered by construction (derived (modeling bridge)).
- The writer model is the full function space `Adversary n = Nat → Region n`: it fixes the region state seen by each memory access of the parser. Each one-byte `read` and each whole-region `snap` is atomic, and the clock advances by exactly one per access. Writes during a byte read, weak-memory reordering, and real timing are not modelled.
- These are statements about the toy model `Toy.DoubleFetch`; they neither establish nor refute the corresponding claims about real parsers, compilers, kernels, hypervisors, Rust or zerocopy. Model–system relation: none proved.

**Prior art.**

- L. Lamport, "Concurrent reading and writing", Communications of the ACM 20(11):806-811, 1977, doi:10.1145/359863.359878 (author's copy: https://lamport.azurewebsites.net/pubs/rd-wr.pdf). "Our algorithm maintains two version numbers for the data: v1 and v2. The writer increments v1 before writing the data item and increments v2 after writing. The reader reads v2 before reading the data item and v1 after reading it. If it finds them equal, then it knows that it read a single version of the data." On bounded counters: "Suppose we know that at most P write operations can occur during a single iteration of the reading loop, and a single digit can assume P + 1 distinct values. Then we can let v1 and v2 be single-digit variables which cycle through P + 1 or more values". (The PDF text extraction renders "v1" as "vl".) The paper assumes that reading and writing a single digit are atomic, and its reader repeats on a mismatch. The toy uses one counter with odd/even phases (the seqlock form) instead of two counters, and its reader returns an error instead of repeating.
- H.-J. Boehm, "Can seqlocks get along with programming language memory models?", Proceedings of the 2012 ACM SIGPLAN Workshop on Memory Systems Performance and Correctness (MSPC 2012), pp. 12-20, doi:10.1145/2247684.2247688 (bibliographic data checked against Crossref; not quoted). Cited for the memory-model side of seqlocks, which the toy does not model.

**Design question.** Which bound on writer progress does a wrapping version counter need for accepted reads to be consistent?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). The memory-model non-claim rests on the Rust Reference's listing of data races as undefined behaviour (quoted under Applicability) and on Boehm 2012 (cited under Prior art, not quoted) for seqlocks under language memory models; the statements about C11 and C++11 and about how implementations order their accesses are background and are not backed by a source quoted in this report. The toy's accesses are atomic and sequentially ordered by construction.

### `remat-breaks-robustness`

- **Kind:** counterexample. **Tier:** T0. **Depth:** shallow.
- **Lean:** `Toy.DoubleFetch.remat_lenCheck_singleRead_robust_to_not_rsafe_not_rvalid`, `Toy.DoubleFetch.remat_privRefines_compile`

```lean
-- lean/DoubleFetch/Results.lean:1333-1339
theorem remat_lenCheck_singleRead_robust_to_not_rsafe_not_rvalid (m cap : Nat)
    (hcap : cap < 255) :
    SingleRead (lenCheck m cap).compile ∧ RSafe (CopyInBounds cap) (lenCheck m cap).compile ∧
      RValid (lpParse cap) (lenCheck m cap).compile ∧
      PrivRefines (lenCheck m cap).remat (lenCheck m cap).compile ∧
      ¬ RSafe (CopyInBounds cap) (lenCheck m cap).remat ∧
      ¬ RValid (lpParse cap) (lenCheck m cap).remat := …
-- lean/DoubleFetch/Results.lean:1281
theorem remat_privRefines_compile (c : CheckUse n α) : PrivRefines c.remat c.compile := by …
```

Unfolded (prose): if `cap < 255`: `SingleRead (lenCheck m cap).compile`, `RSafe (CopyInBounds cap) (lenCheck m cap).compile`, `RValid (lpParse cap) (lenCheck m cap).compile`, `∀ s, (lenCheck m cap).remat.eval s = (lenCheck m cap).compile.eval s`, `¬ RSafe (CopyInBounds cap) (lenCheck m cap).remat` and `¬ RValid (lpParse cap) (lenCheck m cap).remat`; and for every `c`, `∀ s, c.remat.eval s = c.compile.eval s`.

**Plain claim.** For every check-then-use fragment `c : CheckUse n α`, read rematerialization is a refinement in the private-memory semantics (`PrivRefines c.remat c.compile`). For every region size `m + 1` and capacity `cap` with `cap < 255`, the length check-then-use fragment `lenCheck m cap` compiles to a single-read parser that is R-safe for `CopyInBounds cap` and R-valid for `lpParse cap`, while its read rematerialization, a private-memory refinement of it, is neither R-safe nor R-valid.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hcap : cap < 255` (first theorem) | Some byte fails the length check. | tight: counterexample `lenReread_cap255_counterexample` (witness class: an instance with `m = 0` and `cap = 255`) |

**Non-vacuity witness.** `m = 0`, `cap = 4` (`lenReread_cap_lt_255_nonvacuous`). (`lenReread_cap_lt_255_nonvacuous`)

**Non-claims.**

- `CheckUse.remat` is defined on the check-then-use fragment, not as a general transformation of all parsers; it models a compiler that re-loads a local from shared memory instead of keeping it in a register.
- Which real compilers perform this transformation, and under which conditions, is not addressed; the sources quoted below say that a compiler may reload a variable and describe compiler-generated double fetches (derived (modeling bridge)).
- Volatile or atomic accesses as a remedy are not modelled; in Rust, C and C++ a non-atomic or volatile read that races with a write is undefined behaviour in any case (Applicability).
- The writer model is the full function space `Adversary n = Nat → Region n`: it fixes the region state seen by each memory access of the parser. Each one-byte `read` and each whole-region `snap` is atomic, and the clock advances by exactly one per access. Writes during a byte read, weak-memory reordering, and real timing are not modelled.
- These are statements about the toy model `Toy.DoubleFetch`; they neither establish nor refute the corresponding claims about real parsers, compilers, kernels, hypervisors, Rust or zerocopy. Model–system relation: none proved.

**Prior art.**

- Xen Security Advisory CVE-2015-8550 / XSA-155 (version 6, public release 2015-12-17), "paravirtualized drivers incautious about shared memory contents", https://xenbits.xen.org/xsa/advisory-155.html: "The compiler can emit optimizations in the PV backend drivers which can lead to double fetch vulnerabilities. Specifically the shared memory between the frontend and backend can be fetched twice (during which time the frontend can alter the contents) possibly leading to arbitrary code execution in backend."
- Linux kernel, `torvalds/linux` tag v6.12 (commit adc218676eef25575469234709c2d87185ca223a), Documentation/memory-barriers.txt, COMPILER BARRIER section, https://raw.githubusercontent.com/torvalds/linux/adc218676eef25575469234709c2d87185ca223a/Documentation/memory-barriers.txt: "The READ_ONCE() and WRITE_ONCE() functions can prevent any number of optimizations that, while perfectly safe in single-threaded code, can be fatal in concurrent code." (Documentation/memory-barriers.txt@adc218676eef25575469234709c2d87185ca223a:1555-1557) and "The compiler is within its rights to reload a variable, for example, in cases where high register pressure prevents the compiler from keeping all data of interest in registers." (Documentation/memory-barriers.txt@adc218676eef25575469234709c2d87185ca223a:1597-1599)
- J. Ševčík, "Safe optimisations for shared-memory concurrent programs", PLDI 2011, pp. 306-316, doi:10.1145/1993498.1993534 (author's copy: https://www.cl.cam.ac.uk/~pes20/weakmemory/transsafety.pdf): "We also show that, perhaps surprisingly, redundant read introduction invalidates some optimisations that are otherwise safe for the DRF-guarantee." A trace-semantics study of which transformations preserve the DRF guarantee; the toy's rematerialization result concerns robustness against an unconstrained writer instead.
- X. Leroy, "A Formally Verified Compiler Back-end", Journal of Automated Reasoning 43(4):363-446, 2009, doi:10.1007/s10817-009-9155-4 (bibliographic data checked against Crossref; not quoted). Cited for contrast: semantic preservation of sequential programs, the analogue of the toy's private-memory refinement, which does not preserve robustness here.

**Design question.** Which compiler transformations are valid for private memory but destroy robustness?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). Relating read rematerialization to compiler behaviour rests on the sources quoted under Prior art: the Linux memory-barriers documentation ("The compiler is within its rights to reload a variable, ...") and the XSA-155 advisory ("The compiler can emit optimizations in the PV backend drivers which can lead to double fetch vulnerabilities."). Which compilers perform the transformation, and under which conditions, is not examined. The non-claim about volatile and atomic accesses rests, for Rust, on the sources quoted under Applicability; the statements about C and C++ in that non-claim are background and are not backed by a source quoted in this report.

### `remat-robust-refinement-characterization`

- **Kind:** characterization. **Tier:** T1. **Depth:** shallow.
- **Lean:** `Toy.DoubleFetch.remat_pure_robustRefines_iff`, `Toy.DoubleFetch.remat_lenCheck_privRefines_not_robustRefines`

```lean
-- lean/DoubleFetch/Results.lean:1291-1294
theorem remat_pure_robustRefines_iff (a : Fin n) (check : Byte → Bool) (u : Byte → α) (e : α) :
    RobustRefines (CheckUse.pure a check u e).remat (CheckUse.pure a check u e).compile ↔
      ((∃ b, check b = true) →
        ∀ b', ∃ b, (check b = true ∧ u b = u b') ∨ (check b = false ∧ e = u b')) := by …
-- lean/DoubleFetch/Results.lean:1346-1348
theorem remat_lenCheck_privRefines_not_robustRefines (m cap : Nat) (hcap : cap < 255) :
    PrivRefines (lenCheck m cap).remat (lenCheck m cap).compile ∧
      ¬ RobustRefines (lenCheck m cap).remat (lenCheck m cap).compile := …
```

Unfolded (prose): `(∀ adv, ∃ adv', (CheckUse.pure a check u e).remat.exec adv = (CheckUse.pure a check u e).compile.exec adv') ↔ ((∃ b, check b = true) → ∀ b', ∃ b, (check b = true ∧ u b = u b') ∨ (check b = false ∧ e = u b'))`; and if `cap < 255`, `PrivRefines (lenCheck m cap).remat (lenCheck m cap).compile ∧ ¬ RobustRefines (lenCheck m cap).remat (lenCheck m cap).compile`.

**Plain claim.** For every address `a`, check `check : Byte → Bool`, use `u : Byte → α` and failure value `e : α`, the rematerialization of `CheckUse.pure a check u e` (a fragment whose use and failure branch perform no further reads) robustly refines the original iff, whenever the check accepts some byte, every use value `u b'` (for every byte `b'`, including bytes the check rejects) is a result of the original: `u b` for some accepted `b`, or `e` when some byte `b` is rejected. For every region size `m + 1` and capacity `cap` with `cap < 255`, rematerializing `lenCheck m cap` is a private-memory refinement and not a robust refinement.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hcap : cap < 255` (second theorem) | Some byte fails the length check. | tight: counterexample `remat_lenCheck_cap255_robustRefines` (witness class: an instance with `m = 0` and `cap = 255`) |

**Non-vacuity witness.** Robust case: a use that ignores its byte (`remat_pure_robustRefines_const_use`); non-robust case and `hcap`: `lenCheck 0 4` (`lenReread_cap_lt_255_nonvacuous`). (`remat_pure_robustRefines_const_use`, `lenReread_cap_lt_255_nonvacuous`)

**Non-claims.**

- For fragments whose use or failure branch reads memory again, no closed form is given (not addressed); robust refinement is then decided by its definition.
- Robust refinement compares results; it does not preserve R-state (`robustRefines_rereadCompare_tagOnce_not_preserves_rstate`).
- The writer model is the full function space `Adversary n = Nat → Region n`: it fixes the region state seen by each memory access of the parser. Each one-byte `read` and each whole-region `snap` is atomic, and the clock advances by exactly one per access. Writes during a byte read, weak-memory reordering, and real timing are not modelled.
- These are statements about the toy model `Toy.DoubleFetch`; they neither establish nor refute the corresponding claims about real parsers, compilers, kernels, hypervisors, Rust or zerocopy. Model–system relation: none proved.

**Prior art.**

- J. Ševčík, "Safe optimisations for shared-memory concurrent programs", PLDI 2011, pp. 306-316, doi:10.1145/1993498.1993534 (author's copy: https://www.cl.cam.ac.uk/~pes20/weakmemory/transsafety.pdf): "We also show that, perhaps surprisingly, redundant read introduction invalidates some optimisations that are otherwise safe for the DRF-guarantee." A trace-semantics study of which transformations preserve the DRF guarantee; the toy's rematerialization result concerns robustness against an unconstrained writer instead.
- C. Abate, R. Blanco, D. Garg, C. Hritcu, M. Patrignani, J. Thibault, "Journey Beyond Full Abstraction: Exploring Robust Property Preservation for Secure Compilation", 2019 IEEE 32nd Computer Security Foundations Symposium (CSF), doi:10.1109/CSF.2019.00025 (long version arXiv:1807.04603): "We are the first to thoroughly explore a large space of formal secure compilation criteria based on robust property preservation, i.e., the preservation of properties satisfied against arbitrary adversarial contexts." and "For each of the studied criteria we propose an equivalent "property-free" characterization that clarifies which proof techniques apply." The toy's `robustRefines_iff_preserves_rsafe` is a property-free characterization of this kind for result properties, with the writer as the adversarial context.

**Design question.** Which read rematerializations preserve every robust safety property?

Basis: execution (Lean kernel check).

### `robust-refinement-preserves-exactly-rsafe`

- **Kind:** characterization. **Tier:** T0. **Depth:** shallow.
- **Lean:** `Toy.DoubleFetch.robustRefines_iff_preserves_rsafe`, `Toy.DoubleFetch.rsafe_of_robustRefines`, `Toy.DoubleFetch.rvalid_of_robustRefines`, `Toy.DoubleFetch.robustRefines_rereadCompare_tagOnce_not_preserves_rstate`, `Toy.DoubleFetch.obsRefines_iff_eq`

```lean
-- lean/DoubleFetch/Results.lean:107-108
theorem robustRefines_iff_preserves_rsafe (q p : Prog n α) :
    RobustRefines q p ↔ ∀ safe : α → Prop, RSafe safe p → RSafe safe q := by …
-- lean/DoubleFetch/Results.lean:119-120
theorem rsafe_of_robustRefines (safe : α → Prop) (q p : Prog n α) (hqp : RobustRefines q p)
    (hp : RSafe safe p) : RSafe safe q := …
-- lean/DoubleFetch/Results.lean:124-125
theorem rvalid_of_robustRefines (spec : Region n → α) (q p : Prog n α) (hqp : RobustRefines q p)
    (hp : RValid spec p) : RValid spec q := …
-- lean/DoubleFetch/Results.lean:1364-1366
theorem robustRefines_rereadCompare_tagOnce_not_preserves_rstate :
    rereadCompare ≠ tagOnce 0 ∧ RobustRefines rereadCompare (tagOnce 0) ∧
      RState boolParse (tagOnce 0) ∧ ¬ RState boolParse rereadCompare := by …
-- lean/DoubleFetch/Results.lean:147
theorem obsRefines_iff_eq (q p : Prog n α) : ObsRefines q p ↔ q = p := by …
```

Unfolded (prose): `(∀ adv, ∃ adv', q.exec adv = p.exec adv') ↔ ∀ safe, (∀ adv, safe (p.exec adv)) → ∀ adv, safe (q.exec adv)`; transfers of `RSafe` and `RValid` along `RobustRefines q p`; `rereadCompare ≠ tagOnce 0`, `RobustRefines rereadCompare (tagOnce 0)`, `RState boolParse (tagOnce 0)` and `¬ RState boolParse rereadCompare`; and `ObsRefines q p ↔ q = p`.

**Plain claim.** For all parsers `q` and `p`, `q` robustly refines `p` (`RobustRefines q p`: every result `q` returns against some writer, `p` returns against some writer) iff every predicate `safe : α → Prop` on result values that `p` satisfies against every writer, `q` satisfies against every writer. Hence, for every predicate `safe` and spec `spec`, if `RobustRefines q p` and `p` is R-safe for `safe` (respectively R-valid for `spec`), then `q` is R-safe for `safe` (respectively R-valid for `spec`). Robust refinement relates distinct parsers and does not transfer R-state: `rereadCompare` differs from `tagOnce 0`, robustly refines it, and is not R-state for `boolParse`, while `tagOnce 0` is. Observable-access refinement, in which every memory access is an observable event carrying the bytes seen, is equality of parsers (`ObsRefines q p ↔ q = p`).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hqp : RobustRefines q p` (in `rsafe_of_robustRefines`, `rvalid_of_robustRefines`) | Every result of `q` is a result of `p`. | tight: counterexample `robustRefines_hqp_counterexample` (witness class: the rematerialized length parser with `cap = 0`, a private-memory refinement) |
| `hp : RSafe safe p` / `hp : RValid spec p` | The source is robust. | tight: counterexample `robustRefines_source_counterexample` (witness class: the double-fetch length parser with `cap = 0`, refining itself) |

**Non-vacuity witness.** `rereadCompare` robustly refines the distinct parser `tagOnce 0`, which is R-valid for `boolParse` and R-safe for `ValidBoolOut` (`robustRefines_transfer_nonvacuous`). (`robustRefines_transfer_nonvacuous`)

**Non-claims.**

- Robust refinement compares results, not memory accesses or writer states; it is too weak for R-state (`robustRefines_rereadCompare_tagOnce_not_preserves_rstate`).
- `ObsRefines` treats every access as observable with the bytes seen; in this deterministic model that leaves no freedom for any transformation (`obsRefines_iff_eq`). Refinement notions with internal unobservable steps, or with reads that are not observable, are not modelled.
- Which real compiler-correctness criteria imply robust refinement is not addressed (not proved either way).
- The writer model is the full function space `Adversary n = Nat → Region n`: it fixes the region state seen by each memory access of the parser. Each one-byte `read` and each whole-region `snap` is atomic, and the clock advances by exactly one per access. Writes during a byte read, weak-memory reordering, and real timing are not modelled.
- These are statements about the toy model `Toy.DoubleFetch`; they neither establish nor refute the corresponding claims about real parsers, compilers, kernels, hypervisors, Rust or zerocopy. Model–system relation: none proved.

**Prior art.**

- C. Abate, R. Blanco, D. Garg, C. Hritcu, M. Patrignani, J. Thibault, "Journey Beyond Full Abstraction: Exploring Robust Property Preservation for Secure Compilation", 2019 IEEE 32nd Computer Security Foundations Symposium (CSF), doi:10.1109/CSF.2019.00025 (long version arXiv:1807.04603): "We are the first to thoroughly explore a large space of formal secure compilation criteria based on robust property preservation, i.e., the preservation of properties satisfied against arbitrary adversarial contexts." and "For each of the studied criteria we propose an equivalent "property-free" characterization that clarifies which proof techniques apply." The toy's `robustRefines_iff_preserves_rsafe` is a property-free characterization of this kind for result properties, with the writer as the adversarial context.
- X. Leroy, "A Formally Verified Compiler Back-end", Journal of Automated Reasoning 43(4):363-446, 2009, doi:10.1007/s10817-009-9155-4 (bibliographic data checked against Crossref; not quoted). Cited for contrast: semantic preservation of sequential programs, the analogue of the toy's private-memory refinement, which does not preserve robustness here.
- Rust core 1.83.0, `core::ptr::read_volatile`, https://doc.rust-lang.org/1.83.0/core/ptr/fn.read_volatile.html: "Volatile operations are intended to act on I/O memory, and are guaranteed to not be elided or reordered by the compiler across other volatile operations.", "The compiler shouldn’t change the relative order or number of volatile memory operations." and, in its Safety section, "Just like in C, whether an operation is volatile has no bearing whatsoever on questions involving concurrent access from multiple threads. Volatile accesses behave exactly like non-atomic accesses in that regard. In particular, a race between a read_volatile and any write operation to the same location is undefined behavior." The toy's observable-access semantics `Prog.obs` mirrors the first two sentences; the third sentence means that volatile reads of memory a concurrent writer modifies are not a remedy in Rust (derived (modeling bridge)).

**Design question.** Which notion of compiler correctness preserves robustness against a concurrent writer?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). The analogy between the observable-access semantics `Prog.obs` (every access is an observable event) and volatile accesses rests on the `core::ptr::read_volatile` documentation quoted under Prior art: volatile operations are not elided or reordered across other volatile operations, and their number is not changed. The same documentation's Safety section states that a race between a volatile read and a write is undefined behaviour, so the analogy concerns the number and order of accesses, not freedom from data races.

### `validated-view-sound-without-foreign-writes`

- **Kind:** theorem. **Tier:** T0. **Depth:** shallow.
- **Lean:** `Toy.DoubleFetch.viewProg_viewOK_of_noForeignWrites`, `Toy.DoubleFetch.viewProg_implements`

```lean
-- lean/DoubleFetch/Results.lean:1448-1449
theorem viewProg_viewOK_of_noForeignWrites (k : Nat) (adv : Adversary 2)
    (hno : ∀ t, t < 2 + 2 * k → adv t = adv 0) : ViewOK ((viewProg k).exec adv) := by …
-- lean/DoubleFetch/Results.lean:1438
theorem viewProg_implements (k : Nat) : Implements (viewProg k) (viewSpec k) := by …
```

Unfolded (prose): if `∀ t, t < 2 + 2 * k → adv t = adv 0`, then `ViewOK ((viewProg k).exec adv)`; and `∀ s, (viewProg k).eval s = viewSpec k s`.

**Plain claim.** For every number `k` of later decodes and every writer `adv : Adversary 2` that changes nothing during the run of the view program (`adv t = adv 0` for every `t < 2 + 2 * k`), every decode returned by `viewProg k` (validate tag and payload once, then decode `k` times through the view, re-reading tag and payload without re-validating) is a valid tagged value (`ViewOK`). For every `k`, `viewProg k` implements `viewSpec k` in private memory.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hno : ∀ t, t < 2 + 2 * k → adv t = adv 0` (in `viewProg_viewOK_of_noForeignWrites`) | No foreign write during the run. | tight: counterexample `viewProg_tagFlip_invalid` (witness class: an instance with `k = 1` and a writer that flips the tag after validation) |

**Non-vacuity witness.** The writer that never writes, with `k = 2` (`viewProg_nonvacuous`). (`viewProg_nonvacuous`)

**Non-claims.**

- Degenerate edge `k = 0`: with no later decodes, `viewProg 0` satisfies `ViewOK` against every writer (`viewProg_zero_rsafe`), so `hno` is not needed there.
- The hypothesis forbids every write during the run, and for `k = 1` it cannot be weakened to 'every state of the writer is a valid tagged value': `validSwitchAdv` has a valid tagged value in every state and switches once, atomically, from `(1, 1)` to `(0, 2)` between the view's read of the tag (time `2`) and of the payload (time `3`); against it, the one later decode of `viewProg 1` is the invalid `(1, 2)` (`viewProg_validSwitch_breaks_viewOK`). Rust treats the bytes behind a live shared reference as immutable and counts any overlapping write as a mutation, even one that keeps the bytes unchanged (Rust Reference, quoted below; derived (modeling bridge)).
- The writer model is the full function space `Adversary n = Nat → Region n`: it fixes the region state seen by each memory access of the parser. Each one-byte `read` and each whole-region `snap` is atomic, and the clock advances by exactly one per access. Writes during a byte read, weak-memory reordering, and real timing are not modelled.
- These are statements about the toy model `Toy.DoubleFetch`; they neither establish nor refute the corresponding claims about real parsers, compilers, kernels, hypervisors, Rust or zerocopy. Model–system relation: none proved.

**Prior art.**

- zerocopy 0.8.64, https://docs.rs/zerocopy/0.8.64/zerocopy/trait.TryFromBytes.html: `fn try_ref_from_bytes(source: &[u8]) -> Result<&Self, TryCastError<&[u8], Self>> where Self: KnownLayout + Immutable`, "If the bytes of source are a valid instance of Self, this method returns a reference to those bytes interpreted as a Self." Cited for the shape validate-then-reference; no zerocopy position on concurrently written memory is asserted.
- The Rust Reference (Rust 1.83.0), "Behavior considered undefined", https://doc.rust-lang.org/1.83.0/reference/behavior-considered-undefined.html: "Moreover, the bytes pointed to by a shared reference, including transitively through other references (both shared and mutable) and Boxes, are immutable" and "A mutation is any write of more than 0 bytes which overlaps with any of the relevant bytes (even if that write does not change the memory contents)."

**Design question.** When is 'validate once, then hand out a typed reference' sound?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). Relating the no-write hypothesis to Rust's rule for shared references rests on the Rust Reference text quoted under Prior art (the bytes behind a shared reference are immutable, and any overlapping write counts as a mutation). zerocopy's `try_ref_from_bytes` is cited for its validate-then-reference API shape, from its documentation; no zerocopy position on concurrently written memory is asserted.

### `copy-out-and-owned-decode-sound`

- **Kind:** theorem. **Tier:** T1. **Depth:** shallow.
- **Lean:** `Toy.DoubleFetch.copyOutProg_singleRead_implements_rvalid_rsafe_viewOK`, `Toy.DoubleFetch.ownedProg_singleRead_implements_rvalid_rsafe_viewOK`, `Toy.DoubleFetch.ownedProg_exec_eq_copyOutProg_exec`, `Toy.DoubleFetch.copyOutProg_ownedProg_access_counts`, `Toy.DoubleFetch.ownedProg_ne_copyOutProg`, `Toy.DoubleFetch.copyOutProg_torn_valid_not_rstate`, `Toy.DoubleFetch.ownedProg_torn_valid_not_rstate`

```lean
-- lean/DoubleFetch/Results.lean:1524-1527
theorem copyOutProg_singleRead_implements_rvalid_rsafe_viewOK (k : Nat) :
    SingleRead (copyOutProg k) ∧ Implements (copyOutProg k) (viewSpec k) ∧
      PrivRefines (copyOutProg k) (viewProg k) ∧ RValid (viewSpec k) (copyOutProg k) ∧
      RSafe ViewOK (copyOutProg k) := by …
-- lean/DoubleFetch/Results.lean:1542-1545
theorem ownedProg_singleRead_implements_rvalid_rsafe_viewOK (k : Nat) :
    SingleRead (ownedProg k) ∧ Implements (ownedProg k) (viewSpec k) ∧
      PrivRefines (ownedProg k) (viewProg k) ∧ RValid (viewSpec k) (ownedProg k) ∧
      RSafe ViewOK (ownedProg k) := by …
-- lean/DoubleFetch/Results.lean:1594-1595
theorem ownedProg_exec_eq_copyOutProg_exec (k : Nat) (adv : Adversary 2) :
    (ownedProg k).exec adv = (copyOutProg k).exec adv := by …
-- lean/DoubleFetch/Results.lean:1606-1608
theorem copyOutProg_ownedProg_access_counts (k : Nat) (adv : Adversary 2) :
    ((copyOutProg k).obs adv).1.length = 2 ∧
      ((ownedProg k).obs adv).1.length = (if 1 < (adv 0 0).val then 1 else 2) := by …
-- lean/DoubleFetch/Results.lean:1622-1624
theorem ownedProg_ne_copyOutProg (k : Nat) :
    ownedProg k ≠ copyOutProg k ∧ ¬ ObsRefines (ownedProg k) (copyOutProg k) ∧
      ¬ ObsRefines (copyOutProg k) (ownedProg k) := by …
-- lean/DoubleFetch/Results.lean:1570-1574
theorem copyOutProg_torn_valid_not_rstate :
    (copyOutProg 1).exec copyTornAdv = some [(0, 1)] ∧
      ViewOK ((copyOutProg 1).exec copyTornAdv) ∧
      (∀ t : Nat, (copyOutProg 1).exec copyTornAdv ≠ viewSpec 1 (copyTornAdv t)) ∧
      ¬ RState (viewSpec 1) (copyOutProg 1) := by …
-- lean/DoubleFetch/Results.lean:1638-1642
theorem ownedProg_torn_valid_not_rstate :
    (ownedProg 1).exec copyTornAdv = some [(0, 1)] ∧
      ViewOK ((ownedProg 1).exec copyTornAdv) ∧
      (∀ t : Nat, (ownedProg 1).exec copyTornAdv ≠ viewSpec 1 (copyTornAdv t)) ∧
      ¬ RState (viewSpec 1) (ownedProg 1) := by …
```

Unfolded (prose): for each of `copyOutProg k` and `ownedProg k`: `SingleRead`, `Implements _ (viewSpec k)`, `PrivRefines _ (viewProg k)`, `RValid (viewSpec k) _` and `RSafe ViewOK _`; for every `adv`, `(ownedProg k).exec adv = (copyOutProg k).exec adv`, `((copyOutProg k).obs adv).1.length = 2` and `((ownedProg k).obs adv).1.length = if 1 < (adv 0 0).val then 1 else 2`; `ownedProg k ≠ copyOutProg k` and `ObsRefines` fails between them in both directions; and for each `p` of `copyOutProg 1` and `ownedProg 1`, `p.exec copyTornAdv = some [(0, 1)]`, which satisfies `ViewOK` and differs from `viewSpec 1 (copyTornAdv t)` for every `t`, so `¬ RState (viewSpec 1) p`.

**Plain claim.** For every number `k` of later decodes, byte-by-byte copy-out (`copyOutProg k`: copy tag and payload into private memory one byte at a time, at times `0` and `1`, then validate the copy and serve all decodes from it) and single-read decoding into an owned value (`ownedProg k`: read the tag; if it exceeds `1`, return the error result without reading the payload; otherwise read the payload once, validate, and serve all decodes from the owned value) are each single-read, implement `viewSpec k` in private memory and agree there with the view program `viewProg k`, and, against every writer, return a result that is `viewSpec k s'` for some byte vector `s'` and whose decodes are all valid tagged values (`RSafe ViewOK`). The two parsers differ in their memory accesses and agree in their results: for every `k` and every writer `adv`, copy-out performs two reads, owned decoding performs one read when the tag `adv 0 0` it reads at time `0` exceeds `1` and two reads otherwise, and both return the same result; for every `k` they are different parsers, and neither observably refines the other (`ObsRefines`). Neither is a consistent snapshot: against `copyTornAdv` (`(0, 2)` at time `0`, `(1, 1)` afterwards, both valid), `copyOutProg 1` and `ownedProg 1` each return `some [(0, 1)]`, a valid decode that is `viewSpec 1` of no state the writer produced; so neither `copyOutProg 1` nor `ownedProg 1` is R-state for `viewSpec 1`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| (none: the statements are unconditional in their displayed variables) | Records that nothing is assumed beyond the displayed types. | harmless |

**Non-vacuity witness.** Hypothesis-free; `copyOutProg_example` and `ownedProg_examples` compute non-error results. (`copyOutProg_example`, `ownedProg_examples`)

**Non-claims.**

- Copy-out and owned decoding here are non-atomic: they give validity of every decode (R-safe, R-valid), not a state that existed (`copyOutProg_torn_valid_not_rstate`, `ownedProg_torn_valid_not_rstate`). An atomic copy of the whole region is the toy's `snap`, for which `snapParse (viewSpec k)` is R-state (`snapParse_exec_eq_and_rstate`). This result neither establishes nor refutes atomicity of real copy routines (`memcpy`, `copy_from_user`, the XSA-155 `RING_COPY_REQUEST` macro, `zerocopy::TryFromBytes::try_read_from_bytes`).
- In this toy the two strategies differ in the number of reads they perform, not in their results (`ownedProg_exec_eq_copyOutProg_exec`, `copyOutProg_ownedProg_access_counts`): rejecting an invalid tag early saves one read and does not prevent tearing (`ownedProg_torn_valid_not_rstate`). The toy does not model allocation, copying cost or timing, so it gives no reason to prefer either strategy over the other (not addressed).
- In Rust, a non-atomic read of memory that another thread writes concurrently is a data race and undefined behaviour; this applies to reading the source of `try_read_from_bytes(source: &[u8])` while it is concurrently written (derived (modeling bridge) from the Rust Reference; Applicability). The toy has no data races.
- This result does not show that copy-out and owned decoding are the sole sound strategies: in the R-valid sense `rereadCompare` reads twice and is robust (`rereadCompare_implements_rvalid_rsafe_not_singleRead_not_rstate`).
- The writer model is the full function space `Adversary n = Nat → Region n`: it fixes the region state seen by each memory access of the parser. Each one-byte `read` and each whole-region `snap` is atomic, and the clock advances by exactly one per access. Writes during a byte read, weak-memory reordering, and real timing are not modelled.
- These are statements about the toy model `Toy.DoubleFetch`; they neither establish nor refute the corresponding claims about real parsers, compilers, kernels, hypervisors, Rust or zerocopy. Model–system relation: none proved.

**Prior art.**

- XSA-155 patch "xsa155-xen-0001-xen-Add-RING_COPY_REQUEST.patch" (SHA-256 of the fetched file: `e52467fcec73bcc86d3e96d06f8ca8085ae56a83d2c42a30c16bc3dc630d8f8a`), https://xenbits.xen.org/xsa/xsa155-xen-0001-xen-Add-RING_COPY_REQUEST.patch: "Safe usage of a request generally requires taking a local copy." (xsa155-xen-0001-xen-Add-RING_COPY_REQUEST.patch:8-9) and, in the macro comment, "Use this in preference to RING_GET_REQUEST() so all processing is done on a local copy that cannot be modified by the other end." (xsa155-xen-0001-xen-Add-RING_COPY_REQUEST.patch:40-41, where each line carries the comment prefix "+ * ") The macro copies the request by a struct assignment from a volatile source; the patch does not describe the copy as atomic. In the toy, taking a local copy and parsing the copy instead of the shared bytes corresponds to `copyParse` (one-byte reads), not to `snap` (derived (modeling bridge)).
- zerocopy 0.8.64, https://docs.rs/zerocopy/0.8.64/zerocopy/trait.TryFromBytes.html: `fn try_read_from_bytes(source: &[u8]) -> Result<Self, TryReadError<&[u8], Self>> where Self: Sized`, "Attempts to read the given source as a Self." Cited for the shape validate-then-copy; no zerocopy position on concurrently written memory is asserted.
- N. Swamy, T. Ramananandro, A. Rastogi, I. Spiridonova, H. Ni, D. Malloy, J. Vazquez, M. Tang, O. Cardona, A. Gupta, "Hardening Attack Surfaces with Formally Proven Binary Format Parsers", PLDI 2022, pp. 31-45, doi:10.1145/3519939.3523708 (author's copy: http://www.normalesup.org/~ramanana/research/everparse/pldi2022/paper.pdf): "Adhering to this discipline ensures that the host observes a single logical snapshot of the packet even in the presence of concurrent mutations by the guest, inasmuch as what the host sees after a concurrent mutation, the untrusted guest could just as well have put in the packet to begin with." and "Our input streams are designed with a permission model that allows us to prove that validators are double-fetch free. In particular, reading a byte from the stream advances it and makes it provably impossible to read that byte again." The informal "single logical snapshot" there is what the toy calls R-valid (some byte vector), not R-state; EverParse3D mechanizes double-fetch freedom of generated validators, and the semantic statement here is not claimed to appear there in this form.

**Design question.** What should replace 'validate once, then hand out a reference' when the writer is untrusted?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). Relating `copyOutProg` to taking a local copy rests on the XSA-155 patch text quoted under Prior art, which does not describe the copy as atomic, so the toy copies one byte at a time. zerocopy's `try_read_from_bytes` is cited for its validate-then-copy API shape, from its documentation; no zerocopy position on concurrently written memory is asserted. The data-race non-claim rests, for Rust, on the sources quoted under Applicability. The comparison with EverParse3D interprets the informal sentences of Swamy et al. 2022 quoted under Prior art; no EverParse3D artifact is modelled.

## Boundaries

### Non-claims

These are statements about the toy model `Toy.DoubleFetch`; they neither establish nor refute the corresponding claims about real parsers, compilers, kernels, hypervisors, Rust or zerocopy. Model–system relation: none proved.

**Attractive stronger conclusions that are not established:** that any real copy routine is atomic; that volatile accesses make a racing parser well-defined in Rust or C; that the toy seqlock results describe real seqlock implementations under a language memory model; that copy-out and owned decoding are the sole sound strategies.

**Known not to apply (within the toy):** single reads do not give R-state (`copyParse_pair_torn_not_rstate`, `copyOutProg_torn_valid_not_rstate`, `ownedProg_torn_valid_not_rstate`); validating once and then decoding through a view does not preserve `ViewOK` against a writer whose every state is a valid tagged value (`viewProg_validSwitch_breaks_viewOK`, for `k = 1`); a protocol writer taking 256 version increments between the reader's two data reads can make the seqlock reader accept a torn pair (`seqlock_accepted_torn_of_256Increments`); private-memory refinement does not preserve robustness (`remat_lenCheck_singleRead_robust_to_not_rsafe_not_rvalid`); robust refinement does not preserve R-state (`robustRefines_rereadCompare_tagOnce_not_preserves_rstate`); `SingleRead` is not necessary for R-valid (`rereadCompare_implements_rvalid_rsafe_not_singleRead_not_rstate`).

**A non-claim of every result:** The writer model is the full function space `Adversary n = Nat → Region n`: it fixes the region state seen by each memory access of the parser. Each one-byte `read` and each whole-region `snap` is atomic, and the clock advances by exactly one per access. Writes during a byte read, weak-memory reordering, and real timing are not modelled.

**Non-claims of each result** (the same text is listed with each result under Findings; the two non-claims stated above for every result are not repeated):

**`snapshot-parse-rstate`**

- R-state here follows from the toy's `snap` primitive, which copies all `n` bytes in one memory access by definition. This result neither establishes nor refutes atomicity of any real copy routine (`memcpy`, `copy_from_user`, a Rust slice copy, a struct assignment through a volatile pointer); in the toy, copying one byte at a time is `byteCopy`, which is not R-state (`copyParse_pair_torn_not_rstate`).
- Covers the parser that applies `spec` to the snapshot and reads nothing else; a parser that reads shared memory again after the snapshot is not `snapParse spec`.
- `RState` checks a single run against one writer, and its witness time ranges over all of `Nat` (here it is `0`, inside the run). It is not linearizability across several invocations and says nothing about the order of results of consecutive runs.

**`bytecopy-parse-diagonal-rvalid`**

- The diagonal vector need not be any state the writer produced; see `copyParse_pair_torn_not_rstate`.
- The access order `0, 1, …, n - 1` is a choice of `byteCopy`; another order gives another mix of times.
- Degenerate edge `n = 0`: `List.finRange 0` is empty, so `byteCopy` performs no memory access and the statement reduces to `spec` of the unique empty region (by unfolding the definitions; no separate theorem).

**`bytecopy-torn-not-rstate`**

- Does not say every writer tears the copy: against the writer that never writes, every parser returns its private-memory result (`Prog.exec_const`).
- The torn value `(0, 1)` reflects the access order `0, 1`; with the reverse order the same writer would yield `(1, 0)` (not proved here).
- The toy has one-byte reads and whole-region snapshots; a hardware load that reads an aligned multi-byte value in one access is not modelled.

**`single-read-exec-eq-eval-assemble`**

- The assembled vector is generally not a state the writer produced (`copyParse_pair_torn_not_rstate`), so the theorem yields R-valid, not R-state.
- `SingleRead` is sufficient for the R-valid conclusion, not necessary (`rereadCompare_implements_rvalid_rsafe_not_singleRead_not_rstate`).
- Parsers here read and return a value at a leaf; programs that write to the region or emit effects before finishing are not covered.
- Degenerate edge `n = 0`: a snapshot of the empty region reads no address, so `SingleRead` admits repeated snapshots there (`singleRead_zero_double_snap`); harmless, since `Region 0` has one element.
- In Rust, C and C++, a non-atomic read of a shared byte (for example through `&[u8]`), or a `core::ptr::read_volatile`, that races with a concurrent write to the same location is undefined behaviour (a data race), even if each byte is read once. The toy has no notion of a data race, so this result says nothing about avoiding that undefined behaviour (derived (modeling bridge); the Rust sources are quoted under Applicability).
- Source-level single reads need not survive compilation: a private-memory refinement can turn a single-read parser into a double fetch (`remat_lenCheck_singleRead_robust_to_not_rsafe_not_rvalid`). Which access semantics (volatile, atomic) prevent this in a real compiler is not modelled.

**`single-read-rvalid`**

- R-valid allows a vector the writer never produced; it does not imply R-state.
- `SingleRead` is sufficient for `RValid`, not necessary (`rereadCompare_implements_rvalid_rsafe_not_singleRead_not_rstate`).
- `RValid spec p` is a condition on each result: it is `spec s'` for some byte vector `s'`, which need not agree with any byte the writer wrote; for example `Prog.ret r` is R-valid whenever `r` is in the image of `spec` (by the definition of `RValid`; no separate theorem). The per-byte provenance statement is `singleRead_exec_eq_eval_assemble`.
- In Rust, C and C++, a non-atomic read of a shared byte (for example through `&[u8]`), or a `core::ptr::read_volatile`, that races with a concurrent write to the same location is undefined behaviour (a data race), even if each byte is read once. The toy has no notion of a data race, so this result says nothing about avoiding that undefined behaviour (derived (modeling bridge); the Rust sources are quoted under Applicability).
- Source-level single reads need not survive compilation: a private-memory refinement can turn a single-read parser into a double fetch (`remat_lenCheck_singleRead_robust_to_not_rsafe_not_rvalid`). Which access semantics (volatile, atomic) prevent this in a real compiler is not modelled.

**`single-read-rsafe`**

- `safe` is a predicate on the returned value. Relational properties that link the result to the writer's states (of type `Region n → α → Prop`), and actions that read shared memory again after the parser returns (for example copying `len` payload bytes from the shared region), are not covered.
- In Rust, C and C++, a non-atomic read of a shared byte (for example through `&[u8]`), or a `core::ptr::read_volatile`, that races with a concurrent write to the same location is undefined behaviour (a data race), even if each byte is read once. The toy has no notion of a data race, so this result says nothing about avoiding that undefined behaviour (derived (modeling bridge); the Rust sources are quoted under Applicability).
- Source-level single reads need not survive compilation: a private-memory refinement can turn a single-read parser into a double fetch (`remat_lenCheck_singleRead_robust_to_not_rsafe_not_rvalid`). Which access semantics (volatile, atomic) prevent this in a real compiler is not modelled.

**`single-read-not-necessary`**

- It does not show that re-reading is as good as reading once: `rereadCompare` is not R-state (against a writer showing `0` then `1` it returns `none`, although every state the writer produced is a valid `bool`).
- The mismatch branch returns `none`, which lies in the image of `boolParse`. Specs without an error result admit the same phenomenon: for every spec on a one-byte region, `rereadFallback spec` returns `spec` of the zero byte on a mismatch, implements `spec`, is R-valid for it, and is not single-read (`rereadFallback_implements_rvalid_not_singleRead`).

**`rvalid-iff-robust-refinement-of-single-read-implementation`**

- It characterizes R-valid, not R-state: `rereadCompare` robustly refines the single-read `tagOnce 0` and is R-valid, but it is not R-state (`robustRefines_rereadCompare_tagOnce_not_preserves_rstate`).
- Refinement here is one-directional. The two equivalence readings, agreement against every writer and agreement in private memory, fail (`rvalid_equivalence_readings_refuted`).
- The characterization is close to the definitions: every byte vector is the diagonal vector of some writer. Its use is to name the notion of 'behaves like a single-read parser' under which the folklore statement holds.

**`rvalid-equivalence-readings-refuted`**

- The theorem refutes the backward direction of reading (ii): for `cap < 255`, agreeing in private memory with the single-read parser `lenOnce m cap`, which is R-valid for `lpParse cap`, does not make `lenReread m cap` R-valid for `lpParse cap`. Whether the forward direction holds depends on what the single-read witness must satisfy. With a witness that is R-valid for the spec, it holds: for every spec `spec` and every parser `p`, if `RValid spec p`, then `copyParse (fun s => p.eval s)` is single-read, is R-valid for `spec`, and agrees with `p` in private memory (`rvalid_imp_exists_singleRead_rvalid_privRefines`). With a witness that implements the spec in private memory, it fails: for every spec `spec` and every parser `p`, a single-read parser that implements `spec` and agrees with `p` in private memory exists iff `p` itself implements `spec` (`exists_singleRead_implements_privRefines_iff_implements`; when `p` implements `spec`, `copyParse spec` is such a parser, by `copyParse_singleRead_implements`), and the constant parser `Prog.ret (0, 0)` is R-valid for `pairSpec` but agrees in private memory with no single-read parser that implements `pairSpec` (`rvalid_not_imp_exists_singleRead_implements_privRefines`).
- The characterization that holds uses one-directional robust refinement (`rvalid_iff_robustRefines_singleRead_implementation`).
- Degenerate edge `cap ≥ 255`: every byte passes the length check and `lenReread m cap` is R-safe and R-valid (`lenReread_rsafe_rvalid_of_255_le_cap`).

**`length-reread-out-of-bounds-and-invalid`**

- Degenerate edges: the region has `m + 1 ≥ 1` bytes, so the empty region is excluded; at `m = 0` the region holds the length byte and no payload; at `cap = 0` every nonzero length is out of bounds; for `cap ≥ 255` every byte passes the check and `lenReread m cap` is R-safe and R-valid (`lenReread_rsafe_rvalid_of_255_le_cap`).
- The toy models the destination bound `len ≤ cap`, not the source-side bound that `len` payload bytes are present.

**`tag-reread-invalid-bool`**

- The result is the raw byte (`Option Byte`), so the invalid `bool` byte `2` is representable in the toy. In Rust, producing a `bool` other than `0` or `1` is undefined behaviour (Rust Reference, "Invalid values", quoted below), so the toy's `some 2` corresponds to a value a Rust program must never produce (derived (modeling bridge)).

**`checksum-torn-value-matches-no-state`**

- With one checksum-passing and one failing state, a checksum-passing torn result can match neither state (`copyParse_ckParse_twoValidStates_hA_counterexample`), so the two-state statement fails without `hA` (or `hB`).
- The toy's checksum is unkeyed addition modulo 256 against an unbounded writer; whether a keyed cryptographic MAC against a computationally bounded writer prevents torn accepted results is not addressed (not proved either way).
- The cancellation used by the two-state statement holds for addition modulo 256; other checksum functions are not covered.

**`torn-value-impossibility`**

- Proved escape hatches, each of which defeats the impossibility in the toy: (a) an atomic whole-region read (`snap`; `snapParse_exec_eq_and_rstate`, `snapParse_pair_rstate_counterexample`); (b) a constrained writer, such as one following a version protocol with one step per access (`seqlock_positive_control`); (c) a spec with no undetermined state, for example one determined by a single byte (`readFst_rstate_counterexample`, and in general the converse direction of `hasUndeterminedState_iff_no_noSnap_rstate`). Relaxations that are unaddressed or unmodelled, and are neither proved nor refuted to defeat the impossibility: (d) a weaker consistency notion, such as accepted-result consistency (`p.exec adv = some v → ∃ t, spec (adv t) = some v`): the writer built in the proof may use states whose output is the error result, and accepted-result consistency against writers restricted to valid or authenticated states is not addressed (not proved either way), although `ckParse_torn_passes_checksum_matches_no_state` shows that `copyParse ckParse` violates it for a writer whose states all pass the checksum; (e) parsers outside `Prog`: retrying loops (every `Prog` terminates), randomized parsers, and atomic reads of several but not all addresses are not modelled.
- `RState` lets the time `t` range over all of `Nat`, beyond the parser's run; the impossibility therefore also excludes the notion restricted to the access window.
- The R-state parser built for the converse direction reads bytes one at a time until one byte determines the output; it is a construction for the proof, not a recommended parser.

**`seqlock-rstate-one-step-protocol-writer`**

- The one-step bound serves the error case of a reader that does not retry: when the version changes between two accesses, R-state needs some state of the writer with an odd version to match the result `none`. Two protocol steps between accesses, with no data change and no wraparound, already break R-state (`seqlock_not_rstateUnder_twoStepVersionWriter`). This bound is unrelated to counter wraparound; consistency of accepted results under a bound on version increments is `seqlock-accepted-consistent-under-increment-bound`.
- The writer's transitions after time `3` do not affect the reader's run; `OneStepVersionWriter` quantifies over all times, which is more than the proof uses.
- The protocol is a hypothesis about the writer; the theorem gives nothing against a writer that ignores it, such as an untrusted party (`seqlock_not_rstate_rogueWriter`).
- Memory-model requirements of real seqlocks are not modelled: in C11, C++11 and Rust, reading the protected data non-atomically while a writer modifies it is a data race, and implementations use atomic accesses with acquire/release ordering or fences. The toy's accesses are atomic and sequentially ordered by construction (derived (modeling bridge)).

**`seqlock-accepted-consistent-under-increment-bound`**

- The theorem concerns accepted results: it says nothing about the result `none`. A reader that retries on `none`, as in Lamport's algorithm, is outside the model (every `Prog` terminates).
- The bound counts version increments, not complete writes; a complete write increments the version twice. The toy fixes an 8-bit version; other counter widths are not modelled (not proved either way).
- Memory-model requirements of real seqlocks are not modelled: in C11, C++11 and Rust, reading the protected data non-atomically while a writer modifies it is a data race, and implementations use atomic accesses with acquire/release ordering or fences. The toy's accesses are atomic and sequentially ordered by construction (derived (modeling bridge)).

**`remat-breaks-robustness`**

- `CheckUse.remat` is defined on the check-then-use fragment, not as a general transformation of all parsers; it models a compiler that re-loads a local from shared memory instead of keeping it in a register.
- Which real compilers perform this transformation, and under which conditions, is not addressed; the sources quoted below say that a compiler may reload a variable and describe compiler-generated double fetches (derived (modeling bridge)).
- Volatile or atomic accesses as a remedy are not modelled; in Rust, C and C++ a non-atomic or volatile read that races with a write is undefined behaviour in any case (Applicability).

**`remat-robust-refinement-characterization`**

- For fragments whose use or failure branch reads memory again, no closed form is given (not addressed); robust refinement is then decided by its definition.
- Robust refinement compares results; it does not preserve R-state (`robustRefines_rereadCompare_tagOnce_not_preserves_rstate`).

**`robust-refinement-preserves-exactly-rsafe`**

- Robust refinement compares results, not memory accesses or writer states; it is too weak for R-state (`robustRefines_rereadCompare_tagOnce_not_preserves_rstate`).
- `ObsRefines` treats every access as observable with the bytes seen; in this deterministic model that leaves no freedom for any transformation (`obsRefines_iff_eq`). Refinement notions with internal unobservable steps, or with reads that are not observable, are not modelled.
- Which real compiler-correctness criteria imply robust refinement is not addressed (not proved either way).

**`validated-view-sound-without-foreign-writes`**

- Degenerate edge `k = 0`: with no later decodes, `viewProg 0` satisfies `ViewOK` against every writer (`viewProg_zero_rsafe`), so `hno` is not needed there.
- The hypothesis forbids every write during the run, and for `k = 1` it cannot be weakened to 'every state of the writer is a valid tagged value': `validSwitchAdv` has a valid tagged value in every state and switches once, atomically, from `(1, 1)` to `(0, 2)` between the view's read of the tag (time `2`) and of the payload (time `3`); against it, the one later decode of `viewProg 1` is the invalid `(1, 2)` (`viewProg_validSwitch_breaks_viewOK`). Rust treats the bytes behind a live shared reference as immutable and counts any overlapping write as a mutation, even one that keeps the bytes unchanged (Rust Reference, quoted below; derived (modeling bridge)).

**`copy-out-and-owned-decode-sound`**

- Copy-out and owned decoding here are non-atomic: they give validity of every decode (R-safe, R-valid), not a state that existed (`copyOutProg_torn_valid_not_rstate`, `ownedProg_torn_valid_not_rstate`). An atomic copy of the whole region is the toy's `snap`, for which `snapParse (viewSpec k)` is R-state (`snapParse_exec_eq_and_rstate`). This result neither establishes nor refutes atomicity of real copy routines (`memcpy`, `copy_from_user`, the XSA-155 `RING_COPY_REQUEST` macro, `zerocopy::TryFromBytes::try_read_from_bytes`).
- In this toy the two strategies differ in the number of reads they perform, not in their results (`ownedProg_exec_eq_copyOutProg_exec`, `copyOutProg_ownedProg_access_counts`): rejecting an invalid tag early saves one read and does not prevent tearing (`ownedProg_torn_valid_not_rstate`). The toy does not model allocation, copying cost or timing, so it gives no reason to prefer either strategy over the other (not addressed).
- In Rust, a non-atomic read of memory that another thread writes concurrently is a data race and undefined behaviour; this applies to reading the source of `try_read_from_bytes(source: &[u8])` while it is concurrently written (derived (modeling bridge) from the Rust Reference; Applicability). The toy has no data races.
- This result does not show that copy-out and owned decoding are the sole sound strategies: in the R-valid sense `rereadCompare` reads twice and is robust (`rereadCompare_implements_rvalid_rsafe_not_singleRead_not_rstate`).

### Not examined

- Weak-memory reordering, real timing, writes during a byte read, atomic reads of several but not all addresses, randomized parsers, retrying (non-terminating) parsers, parsers that write to the shared region, and multiple parser invocations.

### Escape hatches

The package has one impossibility result, `torn-value-impossibility` (its plain claim is stated under Summary and Findings). Its first non-claim states its escape hatches:

- Proved escape hatches, each of which defeats the impossibility in the toy: (a) an atomic whole-region read (`snap`; `snapParse_exec_eq_and_rstate`, `snapParse_pair_rstate_counterexample`); (b) a constrained writer, such as one following a version protocol with one step per access (`seqlock_positive_control`); (c) a spec with no undetermined state, for example one determined by a single byte (`readFst_rstate_counterexample`, and in general the converse direction of `hasUndeterminedState_iff_no_noSnap_rstate`). Relaxations that are unaddressed or unmodelled, and are neither proved nor refuted to defeat the impossibility: (d) a weaker consistency notion, such as accepted-result consistency (`p.exec adv = some v → ∃ t, spec (adv t) = some v`): the writer built in the proof may use states whose output is the error result, and accepted-result consistency against writers restricted to valid or authenticated states is not addressed (not proved either way), although `ckParse_torn_passes_checksum_matches_no_state` shows that `copyParse ckParse` violates it for a writer whose states all pass the checksum; (e) parsers outside `Prog`: retrying loops (every `Prog` terminates), randomized parsers, and atomic reads of several but not all addresses are not modelled.

Its positive control, as stated with the result: Nearby settings in which R-state holds, each changing one condition: the snapshot parser of the pair spec (it drops `hp`; `snapParse_pair_rstate_counterexample`), and the snapshot-free seqlock reader for the seqlock spec, which has an undetermined state, against writers that follow the version protocol with one step per access (the writer constraint is the one change; `seqlock_positive_control`).

### Unknown

- Accepted-result consistency for snapshot-free parsers against writers restricted to valid or authenticated states; a closed-form characterization of robust rematerialization for fragments whose use reads memory again; counter widths other than 8 bits.
- Hypothesis tightness: no hypothesis in any ledger has tightness `unknown`; every listed hypothesis is `tight`, with the proved counterexample named in its ledger row.

### Disproved or dropped statements

None. Every result listed in this report is proved as stated; no statement was found false or left unproved.

## Evidence

### Kernel-check record

**Kernel check.** Observed on 2026-11-21 with `leanprover/lean4:v4.34.1` (GitHub `leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean and `Std`, no Mathlib. A fresh copy of `lean/` (without a `.lake` directory) was built with `lake build` with Lake's artifact cache disabled, so every proof was re-elaborated and checked by the kernel; the build reported no errors and no `sorry` warnings. Lean's `collectAxioms` was run on every one of the 441 declarations of the library `DoubleFetch`: each depends on at most `propext`, `Classical.choice` and `Quot.sound` (per-declaration lists in `audit/axioms.json`). No Lean source of the package contains `sorry`, `admit`, `native_decide`, an `axiom` or `opaque` declaration, `implemented_by`, `@[extern]` or `unsafe`.

Basis for every result: execution (Lean kernel check). Every connection to a real system is a separate derived (modeling bridge) claim, marked where it occurs under Findings.

Result numbers used in the hash table below:

| # | Result | Lean theorems |
| :--- | :--- | :--- |
| 1 | `snapshot-parse-rstate` | `snapParse_exec_eq_and_rstate` |
| 2 | `bytecopy-parse-diagonal-rvalid` | `copyParse_exec_eq_diagonal_and_rvalid`, `copyParse_singleRead_implements` |
| 3 | `bytecopy-torn-not-rstate` | `copyParse_pair_torn_not_rstate` |
| 4 | `single-read-exec-eq-eval-assemble` | `singleRead_exec_eq_eval_assemble` |
| 5 | `single-read-rvalid` | `rvalid_of_singleRead_of_implements` |
| 6 | `single-read-rsafe` | `rsafe_of_singleRead_of_staticSafe` |
| 7 | `single-read-not-necessary` | `rereadCompare_implements_rvalid_rsafe_not_singleRead_not_rstate` |
| 8 | `rvalid-iff-robust-refinement-of-single-read-implementation` | `rvalid_iff_robustRefines_singleRead_implementation`, `rvalid_iff_robustRefines_copyParse` |
| 9 | `rvalid-equivalence-readings-refuted` | `rvalid_equivalence_readings_refuted` |
| 10 | `length-reread-out-of-bounds-and-invalid` | `lenReread_flip_out_of_bounds_and_invalid`, `lenReread_not_rsafe_not_rvalid`, `lenReread_implements`, `lenOnce_singleRead_implements`, `lenOnce_rsafe_rvalid` |
| 11 | `tag-reread-invalid-bool` | `tagReread_flip_invalid_bool`, `tagReread_not_rsafe_not_rvalid`, `tagReread_implements`, `tagOnce_singleRead_implements`, `tagOnce_rsafe_rvalid` |
| 12 | `checksum-torn-value-matches-no-state` | `ckParse_torn_passes_checksum_matches_no_state`, `copyParse_ckParse_twoValidStates`, `copyParse_singleRead_implements` |
| 13 | `torn-value-impossibility` | `not_rstate_of_noSnap_of_hasUndeterminedState`, `hasUndeterminedState_iff_no_noSnap_rstate`, `pairSpec_hasUndeterminedState`, `ckParse_hasUndeterminedState`, `seqSpec_hasUndeterminedState`, `andSpec_hasUndeterminedState`, `viewSpec_hasUndeterminedState`, `not_hasUndeterminedState_of_region_zero`, `not_hasUndeterminedState_of_region_one` |
| 14 | `seqlock-rstate-one-step-protocol-writer` | `seqlock_rstate_of_oneStepVersionWriter` |
| 15 | `seqlock-accepted-consistent-under-increment-bound` | `seqlock_accepted_eq_seqSpec_adv0_of_incrementBound`, `versionPath_any` |
| 16 | `remat-breaks-robustness` | `remat_lenCheck_singleRead_robust_to_not_rsafe_not_rvalid`, `remat_privRefines_compile` |
| 17 | `remat-robust-refinement-characterization` | `remat_pure_robustRefines_iff`, `remat_lenCheck_privRefines_not_robustRefines` |
| 18 | `robust-refinement-preserves-exactly-rsafe` | `robustRefines_iff_preserves_rsafe`, `rsafe_of_robustRefines`, `rvalid_of_robustRefines`, `robustRefines_rereadCompare_tagOnce_not_preserves_rstate`, `obsRefines_iff_eq` |
| 19 | `validated-view-sound-without-foreign-writes` | `viewProg_viewOK_of_noForeignWrites`, `viewProg_implements` |
| 20 | `copy-out-and-owned-decode-sound` | `copyOutProg_singleRead_implements_rvalid_rsafe_viewOK`, `ownedProg_singleRead_implements_rvalid_rsafe_viewOK`, `ownedProg_exec_eq_copyOutProg_exec`, `copyOutProg_ownedProg_access_counts`, `ownedProg_ne_copyOutProg`, `copyOutProg_torn_valid_not_rstate`, `ownedProg_torn_valid_not_rstate` |

### Primary sources

Observation date for every source below: 2026-11-21. Quoted sentences were compared with the fetched source on that date.

- Y. Afek, H. Attiya, D. Dolev, E. Gafni, M. Merritt, N. Shavit, "Atomic snapshots of shared memory", J. ACM 40(4):873-890, 1993, doi:10.1145/153724.153741 (author's copy: https://people.csail.mit.edu/shanir/publications/AADGMS.pdf): "This paper presents three wait-free implementations of atomic snapshot memory." There the memory is updated through the implementation's own update operation, so every writer follows a protocol; cited as contrast with the unconstrained writer here.
- M. P. Herlihy, J. M. Wing, "Linearizability: a correctness condition for concurrent objects", ACM TOPLAS 12(3):463-492, 1990, doi:10.1145/78969.78972 (bibliographic data checked against Crossref; not quoted). Cited for contrast: linearizability orders the operations of several concurrent invocations, whereas `RState` constrains one run in isolation.
- XSA-155 patch "xsa155-xen-0001-xen-Add-RING_COPY_REQUEST.patch" (SHA-256 of the fetched file: `e52467fcec73bcc86d3e96d06f8ca8085ae56a83d2c42a30c16bc3dc630d8f8a`), https://xenbits.xen.org/xsa/xsa155-xen-0001-xen-Add-RING_COPY_REQUEST.patch: "Safe usage of a request generally requires taking a local copy." (xsa155-xen-0001-xen-Add-RING_COPY_REQUEST.patch:8-9) and, in the macro comment, "Use this in preference to RING_GET_REQUEST() so all processing is done on a local copy that cannot be modified by the other end." (xsa155-xen-0001-xen-Add-RING_COPY_REQUEST.patch:40-41, where each line carries the comment prefix "+ * ") The macro copies the request by a struct assignment from a volatile source; the patch does not describe the copy as atomic. In the toy, taking a local copy and parsing the copy instead of the shared bytes corresponds to `copyParse` (one-byte reads), not to `snap` (derived (modeling bridge)).
- P. Wang, J. Krinke, K. Lu, G. Li, S. Dodier-Lazaro, "How Double-Fetch Situations turn into Double-Fetch Vulnerabilities: A Study of Double Fetches in the Linux Kernel", 26th USENIX Security Symposium (USENIX Security 17), Vancouver, 2017, pp. 1-16, https://www.usenix.org/conference/usenixsecurity17/technical-sessions/presentation/wang-pengfei. Empirical study of double fetches in the Linux kernel and a static detector; informal.
- N. Swamy, T. Ramananandro, A. Rastogi, I. Spiridonova, H. Ni, D. Malloy, J. Vazquez, M. Tang, O. Cardona, A. Gupta, "Hardening Attack Surfaces with Formally Proven Binary Format Parsers", PLDI 2022, pp. 31-45, doi:10.1145/3519939.3523708 (author's copy: http://www.normalesup.org/~ramanana/research/everparse/pldi2022/paper.pdf): "Adhering to this discipline ensures that the host observes a single logical snapshot of the packet even in the presence of concurrent mutations by the guest, inasmuch as what the host sees after a concurrent mutation, the untrusted guest could just as well have put in the packet to begin with." and "Our input streams are designed with a permission model that allows us to prove that validators are double-fetch free. In particular, reading a byte from the stream advances it and makes it provably impossible to read that byte again." The informal "single logical snapshot" there is what the toy calls R-valid (some byte vector), not R-state; EverParse3D mechanizes double-fetch freedom of generated validators, and the semantic statement here is not claimed to appear there in this form.
- M. Jurczyk and G. Coldwind, "Identifying and Exploiting Windows Kernel Race Conditions via Memory Access Patterns", whitepaper accompanying the SyScan 2013 talk on Bochspwn, April 2013, https://research.google.com/pubs/archive/42189.pdf (also listed at https://research.google/pubs/identifying-and-exploiting-windows-kernel-race-conditions-via-memory-access-patterns/ and on the authors' talk page https://j00ru.vexillium.org/talks/syscan-bochspwn-exploiting-kernel-race-conditions/; title, authors and date checked against a search index, the PDF itself could not be fetched on the observation date). Describes double fetches of user-mode memory by kernel code and a memory-access-pattern detector; informal.
- C. Abate, R. Blanco, D. Garg, C. Hritcu, M. Patrignani, J. Thibault, "Journey Beyond Full Abstraction: Exploring Robust Property Preservation for Secure Compilation", 2019 IEEE 32nd Computer Security Foundations Symposium (CSF), doi:10.1109/CSF.2019.00025 (long version arXiv:1807.04603): "We are the first to thoroughly explore a large space of formal secure compilation criteria based on robust property preservation, i.e., the preservation of properties satisfied against arbitrary adversarial contexts." and "For each of the studied criteria we propose an equivalent "property-free" characterization that clarifies which proof techniques apply." The toy's `robustRefines_iff_preserves_rsafe` is a property-free characterization of this kind for result properties, with the writer as the adversarial context.
- M. Xu, C. Qian, K. Lu, M. Backes, T. Kim, "Precise and Scalable Detection of Double-Fetch Bugs in OS Kernels", IEEE Symposium on Security and Privacy 2018, pp. 661-678, doi:10.1109/SP.2018.00017 (bibliographic data checked against Crossref; not quoted). Cited for the bug class (a value checked after one fetch and used after another).
- The Rust Reference (Rust 1.83.0), "Behavior considered undefined", https://doc.rust-lang.org/1.83.0/reference/behavior-considered-undefined.html, section "Invalid values": "The Rust compiler assumes that all values produced during program execution are “valid”, and producing an invalid value is hence immediate UB." and "A bool value must be false (0) or true (1)."
- zerocopy 0.8.64, https://docs.rs/zerocopy/0.8.64/zerocopy/trait.TryFromBytes.html: `fn try_ref_from_bytes(source: &[u8]) -> Result<&Self, TryCastError<&[u8], Self>> where Self: KnownLayout + Immutable`, "If the bytes of source are a valid instance of Self, this method returns a reference to those bytes interpreted as a Self." Cited for the shape validate-then-reference; no zerocopy position on concurrently written memory is asserted.
- L. Lamport, "Concurrent reading and writing", Communications of the ACM 20(11):806-811, 1977, doi:10.1145/359863.359878 (author's copy: https://lamport.azurewebsites.net/pubs/rd-wr.pdf). "Our algorithm maintains two version numbers for the data: v1 and v2. The writer increments v1 before writing the data item and increments v2 after writing. The reader reads v2 before reading the data item and v1 after reading it. If it finds them equal, then it knows that it read a single version of the data." On bounded counters: "Suppose we know that at most P write operations can occur during a single iteration of the reading loop, and a single digit can assume P + 1 distinct values. Then we can let v1 and v2 be single-digit variables which cycle through P + 1 or more values". (The PDF text extraction renders "v1" as "vl".) The paper assumes that reading and writing a single digit are atomic, and its reader repeats on a mismatch. The toy uses one counter with odd/even phases (the seqlock form) instead of two counters, and its reader returns an error instead of repeating.
- H.-J. Boehm, "Can seqlocks get along with programming language memory models?", Proceedings of the 2012 ACM SIGPLAN Workshop on Memory Systems Performance and Correctness (MSPC 2012), pp. 12-20, doi:10.1145/2247684.2247688 (bibliographic data checked against Crossref; not quoted). Cited for the memory-model side of seqlocks, which the toy does not model.
- Xen Security Advisory CVE-2015-8550 / XSA-155 (version 6, public release 2015-12-17), "paravirtualized drivers incautious about shared memory contents", https://xenbits.xen.org/xsa/advisory-155.html: "The compiler can emit optimizations in the PV backend drivers which can lead to double fetch vulnerabilities. Specifically the shared memory between the frontend and backend can be fetched twice (during which time the frontend can alter the contents) possibly leading to arbitrary code execution in backend."
- Linux kernel, `torvalds/linux` tag v6.12 (commit adc218676eef25575469234709c2d87185ca223a), Documentation/memory-barriers.txt, COMPILER BARRIER section, https://raw.githubusercontent.com/torvalds/linux/adc218676eef25575469234709c2d87185ca223a/Documentation/memory-barriers.txt: "The READ_ONCE() and WRITE_ONCE() functions can prevent any number of optimizations that, while perfectly safe in single-threaded code, can be fatal in concurrent code." (Documentation/memory-barriers.txt@adc218676eef25575469234709c2d87185ca223a:1555-1557) and "The compiler is within its rights to reload a variable, for example, in cases where high register pressure prevents the compiler from keeping all data of interest in registers." (Documentation/memory-barriers.txt@adc218676eef25575469234709c2d87185ca223a:1597-1599)
- J. Ševčík, "Safe optimisations for shared-memory concurrent programs", PLDI 2011, pp. 306-316, doi:10.1145/1993498.1993534 (author's copy: https://www.cl.cam.ac.uk/~pes20/weakmemory/transsafety.pdf): "We also show that, perhaps surprisingly, redundant read introduction invalidates some optimisations that are otherwise safe for the DRF-guarantee." A trace-semantics study of which transformations preserve the DRF guarantee; the toy's rematerialization result concerns robustness against an unconstrained writer instead.
- X. Leroy, "A Formally Verified Compiler Back-end", Journal of Automated Reasoning 43(4):363-446, 2009, doi:10.1007/s10817-009-9155-4 (bibliographic data checked against Crossref; not quoted). Cited for contrast: semantic preservation of sequential programs, the analogue of the toy's private-memory refinement, which does not preserve robustness here.
- Rust core 1.83.0, `core::ptr::read_volatile`, https://doc.rust-lang.org/1.83.0/core/ptr/fn.read_volatile.html: "Volatile operations are intended to act on I/O memory, and are guaranteed to not be elided or reordered by the compiler across other volatile operations.", "The compiler shouldn’t change the relative order or number of volatile memory operations." and, in its Safety section, "Just like in C, whether an operation is volatile has no bearing whatsoever on questions involving concurrent access from multiple threads. Volatile accesses behave exactly like non-atomic accesses in that regard. In particular, a race between a read_volatile and any write operation to the same location is undefined behavior." The toy's observable-access semantics `Prog.obs` mirrors the first two sentences; the third sentence means that volatile reads of memory a concurrent writer modifies are not a remedy in Rust (derived (modeling bridge)).
- The Rust Reference (Rust 1.83.0), "Behavior considered undefined", https://doc.rust-lang.org/1.83.0/reference/behavior-considered-undefined.html: "Moreover, the bytes pointed to by a shared reference, including transitively through other references (both shared and mutable) and Boxes, are immutable" and "A mutation is any write of more than 0 bytes which overlaps with any of the relevant bytes (even if that write does not change the memory contents)."
- zerocopy 0.8.64, https://docs.rs/zerocopy/0.8.64/zerocopy/trait.TryFromBytes.html: `fn try_read_from_bytes(source: &[u8]) -> Result<Self, TryReadError<&[u8], Self>> where Self: Sized`, "Attempts to read the given source as a Self." Cited for the shape validate-then-copy; no zerocopy position on concurrently written memory is asserted.

**Identities of pinned sources** (fetched 2026-11-21): Lean 4 `v4.34.1`: GitHub `leanprover/lean4`, commit `5045d0056413266e57c625dcd7c365b10e377c52`. Linux v6.12: GitHub `torvalds/linux`, tag `v6.12`, commit `adc218676eef25575469234709c2d87185ca223a`. Rust 1.83.0 (source of the `core` documentation): GitHub `rust-lang/rust`, tag `1.83.0`, commit `90b35a6239c3d8bdabc530a6a0816f7ff89a0aaf`; the Rust Reference pages are identified by their versioned URLs. zerocopy 0.8.64: crates.io checksum `ed43f3060383c64b000f3c630550aebdfa9d3b76d48de32390483dd2cc7e0865`, GitHub `google/zerocopy`, tag `v0.8.64`, commit `2a2de7378759cdcc2ccb9e0d4b408cf6d9126b17`; the documentation is identified by its versioned docs.rs URL. XSA-155 patch: SHA-256 of the fetched file as recorded above; the advisory page is identified by its URL and advisory version.

### Auxiliary lemmas and examples cited by name

#### `Prog.execFrom_eq_eval_of_agree`

```lean
-- lean/DoubleFetch/Theory.lean:114-116
theorem execFrom_eq_eval_of_agree (p : Prog n α) (s : Region n) (adv : Adversary n) (t0 : Nat)
    (hp : p.NoSnap) (h : ∀ m i, p.addrAt s m = some i → adv (t0 + m) i = s i) :
    p.execFrom adv t0 = p.eval s := by …
```

#### `Prog.exec_const`

```lean
-- lean/DoubleFetch/Theory.lean:33
theorem exec_const (p : Prog n α) (s : Region n) : p.exec (Adversary.const s) = p.eval s := …
```

#### `Prog.obs_snd`

```lean
-- lean/DoubleFetch/Theory.lean:37
theorem obs_snd (p : Prog n α) (adv : Adversary n) : (p.obs adv).2 = p.exec adv := …
```

#### `andSpec_examples`

```lean
-- lean/DoubleFetch/Examples.lean:181-182
theorem andSpec_examples : andSpec (reg2 1 1) = true ∧ andSpec (reg2 1 0) = false ∧
    andSpec (reg2 0 1) = false := by …
```

#### `assemble_example`

```lean
-- lean/DoubleFetch/Examples.lean:60-63
theorem assemble_example :
    (Prog.read 0 fun a => .ret a : Prog 2 Byte).assemble (fun _ => reg2 5 6) (fun _ => 3) 0 = 5 ∧
      (Prog.read 0 fun a => .ret a : Prog 2 Byte).assemble (fun _ => reg2 5 6) (fun _ => 3) 1
        = 3 := by …
```

#### `boolParse_examples`

```lean
-- lean/DoubleFetch/Examples.lean:143-144
theorem boolParse_examples : boolParse (fun _ : Fin 1 => 1) = some 1 ∧
    boolParse (fun _ : Fin 1 => 2) = none := by …
```

#### `ckParse_examples`

```lean
-- lean/DoubleFetch/Examples.lean:153-154
theorem ckParse_examples : ckParse (reg3 1 2 3) = some (1, 2) ∧ ckParse (reg3 1 2 4) = none ∧
    ckParse (reg3 2 255 1) = some (2, 255) := by …
```

#### `copyInBounds_examples`

```lean
-- lean/DoubleFetch/Examples.lean:138-139
theorem copyInBounds_examples :
    CopyInBounds 4 (some 3) ∧ CopyInBounds 4 none ∧ ¬ CopyInBounds 4 (some 5) := by …
```

#### `copyOutProg_example`

```lean
-- lean/DoubleFetch/Examples.lean:277-278
theorem copyOutProg_example :
    (copyOutProg 1).exec (Adversary.const (reg2 1 1)) = some [(1, 1)] := by …
```

#### `copyParse_ckParse_twoValidStates_hA_counterexample`

```lean
-- lean/DoubleFetch/Results.lean:575-581
theorem copyParse_ckParse_twoValidStates_hA_counterexample :
    ¬ ((reg3 1 1 1) 2 = (reg3 1 1 1) 0 + (reg3 1 1 1) 1) ∧
      (reg3 0 0 0) 2 = (reg3 0 0 0) 0 + (reg3 0 0 0) 1 ∧
      (∀ t, ckMixAdv t = reg3 1 1 1 ∨ ckMixAdv t = reg3 0 0 0) ∧
      (copyParse ckParse).exec ckMixAdv = some (0, 1) ∧
      (copyParse ckParse).exec ckMixAdv ≠ ckParse (reg3 1 1 1) ∧
      (copyParse ckParse).exec ckMixAdv ≠ ckParse (reg3 0 0 0) := by …
```

#### `copyParse_ckParse_twoValidStates_hadv_counterexample`

```lean
-- lean/DoubleFetch/Results.lean:594-600
theorem copyParse_ckParse_twoValidStates_hadv_counterexample :
    (reg3 0 0 0) 2 = (reg3 0 0 0) 0 + (reg3 0 0 0) 1 ∧
      (reg3 1 1 2) 2 = (reg3 1 1 2) 0 + (reg3 1 1 2) 1 ∧
      ¬ (∀ t, ckTornAdv t = reg3 0 0 0 ∨ ckTornAdv t = reg3 1 1 2) ∧
      (copyParse ckParse).exec ckTornAdv = some (0, 1) ∧
      (copyParse ckParse).exec ckTornAdv ≠ ckParse (reg3 0 0 0) ∧
      (copyParse ckParse).exec ckTornAdv ≠ ckParse (reg3 1 1 2) := by …
```

#### `copyParse_ckParse_twoValidStates_hpass_counterexample`

```lean
-- lean/DoubleFetch/Results.lean:610-617
theorem copyParse_ckParse_twoValidStates_hpass_counterexample :
    (reg3 0 0 0) 2 = (reg3 0 0 0) 0 + (reg3 0 0 0) 1 ∧
      (reg3 1 1 2) 2 = (reg3 1 1 2) 0 + (reg3 1 1 2) 1 ∧
      (∀ t, (fun t => if t = 0 then reg3 0 0 0 else reg3 1 1 2 : Adversary 3) t = reg3 0 0 0 ∨
        (fun t => if t = 0 then reg3 0 0 0 else reg3 1 1 2 : Adversary 3) t = reg3 1 1 2) ∧
      (copyParse ckParse).exec (fun t => if t = 0 then reg3 0 0 0 else reg3 1 1 2) = none ∧
      (none : Option (Byte × Byte)) ≠ ckParse (reg3 0 0 0) ∧
      (none : Option (Byte × Byte)) ≠ ckParse (reg3 1 1 2) := by …
```

#### `copyParse_ckParse_twoValidStates_nonvacuous`

```lean
-- lean/DoubleFetch/Results.lean:628-633
theorem copyParse_ckParse_twoValidStates_nonvacuous :
    (reg3 0 0 0) 2 = (reg3 0 0 0) 0 + (reg3 0 0 0) 1 ∧
      (reg3 1 1 2) 2 = (reg3 1 1 2) 0 + (reg3 1 1 2) 1 ∧
      (∀ t, (fun t => if t < 3 then reg3 0 0 0 else reg3 1 1 2 : Adversary 3) t = reg3 0 0 0 ∨
        (fun t => if t < 3 then reg3 0 0 0 else reg3 1 1 2 : Adversary 3) t = reg3 1 1 2) ∧
      (copyParse ckParse).exec (fun t => if t < 3 then reg3 0 0 0 else reg3 1 1 2) ≠ none := by …
```

#### `dataDepProg_examples`

```lean
-- lean/DoubleFetch/Examples.lean:291-292
theorem dataDepProg_examples :
    dataDepProg.eval (reg3 0 7 9) = 7 ∧ dataDepProg.eval (reg3 1 7 9) = 9 := by …
```

#### `dataDepProg_singleRead`

```lean
-- lean/DoubleFetch/Results.lean:1723
theorem dataDepProg_singleRead : SingleRead dataDepProg := by …
```

#### `eval_example`

```lean
-- lean/DoubleFetch/Examples.lean:29
theorem eval_example : readTwice.eval (fun _ => 7) = (7, 7) := by …
```

#### `exec_example`

```lean
-- lean/DoubleFetch/Examples.lean:21
theorem exec_example : readTwice.exec sevenNine = (7, 9) := by …
```

#### `exec_ne_eval_example`

```lean
-- lean/DoubleFetch/Examples.lean:25
theorem exec_ne_eval_example : readTwice.exec sevenNine ≠ readTwice.eval (sevenNine 0) := by …
```

#### `exists_singleRead_implements_privRefines_iff_implements`

```lean
-- lean/DoubleFetch/Readings.lean:43-45
theorem exists_singleRead_implements_privRefines_iff_implements (spec : Region n → α)
    (p : Prog n α) :
    (∃ q : Prog n α, SingleRead q ∧ Implements q spec ∧ PrivRefines p q) ↔ Implements p spec := by …
```

#### `hasUndeterminedState_examples`

```lean
-- lean/DoubleFetch/Examples.lean:174-176
theorem hasUndeterminedState_examples :
    HasUndeterminedState pairSpec ∧ HasUndeterminedState seqSpec ∧
      HasUndeterminedState (viewSpec 1) ∧ ¬ HasUndeterminedState fstSpec := …
```

#### `hasUndeterminedState_of_pos_of_noByteDeterminesOutput`

```lean
-- lean/DoubleFetch/Results.lean:761-762
theorem hasUndeterminedState_of_pos_of_noByteDeterminesOutput (hn : 0 < n) (spec : Region n → α)
    (hspec : NoByteDeterminesOutput spec) : HasUndeterminedState spec := by …
```

#### `implements_examples`

```lean
-- lean/DoubleFetch/Examples.lean:99-100
theorem implements_examples :
    Implements (lenOnce 0 4) (lpParse 4) ∧ ¬ Implements (lenOnce 0 4) (lpParse 5) := by …
```

#### `implements_hyp_counterexample_rvalid`

```lean
-- lean/DoubleFetch/Results.lean:1676-1679
theorem implements_hyp_counterexample_rvalid :
    SingleRead (Prog.ret (some 1) : Prog 1 (Option Nat)) ∧
      ¬ Implements (Prog.ret (some 1) : Prog 1 (Option Nat)) (lpParse 0) ∧
      ¬ RValid (lpParse 0) (Prog.ret (some 1) : Prog 1 (Option Nat)) := by …
```

#### `incrementBoundedWriter_examples`

```lean
-- lean/DoubleFetch/Examples.lean:240-242
theorem incrementBoundedWriter_examples :
    IncrementBoundedWriter 1 (Adversary.const (reg3 0 5 5)) ∧
      ¬ IncrementBoundedWriter 256 seqWrapAdv := …
```

#### `lenReread_cap255_counterexample`

```lean
-- lean/DoubleFetch/Results.lean:406-408
theorem lenReread_cap255_counterexample :
    ¬ (255 < 255) ∧ RSafe (CopyInBounds 255) (lenReread 0 255) ∧
      RValid (lpParse 255) (lenReread 0 255) := …
```

#### `lenReread_cap_lt_255_nonvacuous`

```lean
-- lean/DoubleFetch/Results.lean:413-414
theorem lenReread_cap_lt_255_nonvacuous :
    (4 : Nat) < 255 ∧ (lenReread 0 4).exec (lenFlipAdv 0 4) = some 5 := …
```

#### `lenReread_exec_ne_eval_assemble`

```lean
-- lean/DoubleFetch/Results.lean:1655-1658
theorem lenReread_exec_ne_eval_assemble (m cap : Nat) (hcap : cap < 255) :
    ¬ SingleRead (lenReread m cap) ∧
      ∀ d : Region (m + 1), (lenReread m cap).exec (lenFlipAdv m cap) ≠
        (lenReread m cap).eval ((lenReread m cap).assemble (lenFlipAdv m cap) d) := by …
```

#### `lenReread_rsafe_rvalid_of_255_le_cap`

```lean
-- lean/DoubleFetch/Results.lean:393-394
theorem lenReread_rsafe_rvalid_of_255_le_cap (m cap : Nat) (hcap : 255 ≤ cap) :
    RSafe (CopyInBounds cap) (lenReread m cap) ∧ RValid (lpParse cap) (lenReread m cap) := by …
```

#### `lpParse_examples`

```lean
-- lean/DoubleFetch/Examples.lean:133-134
theorem lpParse_examples : lpParse 4 (fun _ : Fin 1 => 3) = some 3 ∧
    lpParse 4 (fun _ : Fin 1 => 5) = none := by …
```

#### `noByteDeterminesOutput_examples`

```lean
-- lean/DoubleFetch/Examples.lean:158-159
theorem noByteDeterminesOutput_examples :
    NoByteDeterminesOutput pairSpec ∧ ¬ NoByteDeterminesOutput fstSpec := by …
```

#### `noSnap_examples`

```lean
-- lean/DoubleFetch/Examples.lean:54
theorem noSnap_examples : readFst.NoSnap ∧ ¬ (snapParse pairSpec).NoSnap := …
```

#### `obsRefines_examples`

```lean
-- lean/DoubleFetch/Examples.lean:117-118
theorem obsRefines_examples :
    ObsRefines (lenOnce 0 4) (lenOnce 0 4) ∧ ¬ ObsRefines (lenReread 0 4) (lenOnce 0 4) := by …
```

#### `obs_example`

```lean
-- lean/DoubleFetch/Examples.lean:32-33
theorem obs_example :
    (readTwice.obs sevenNine).1.length = 2 ∧ (readTwice.obs sevenNine).2 = (7, 9) := by …
```

#### `oneStepVersionWriter_examples`

```lean
-- lean/DoubleFetch/Examples.lean:199-200
theorem oneStepVersionWriter_examples :
    OneStepVersionWriter (Adversary.const (reg3 0 5 5)) ∧ ¬ OneStepVersionWriter seqTwoStepAdv := …
```

#### `ownedProg_examples`

```lean
-- lean/DoubleFetch/Examples.lean:283-285
theorem ownedProg_examples :
    (ownedProg 1).eval (reg2 1 1) = some [(1, 1)] ∧ (ownedProg 1).eval (reg2 2 0) = none ∧
      ((ownedProg 1).obs (Adversary.const (reg2 2 0))).1.length = 1 := by …
```

#### `privRefines_examples`

```lean
-- lean/DoubleFetch/Examples.lean:108-109
theorem privRefines_examples :
    PrivRefines (lenReread 0 4) (lenOnce 0 4) ∧ ¬ PrivRefines (lenOnce 0 5) (lenOnce 0 4) := by …
```

#### `readFst_rstate_counterexample`

```lean
-- lean/DoubleFetch/Results.lean:903-904
theorem readFst_rstate_counterexample :
    ¬ HasUndeterminedState fstSpec ∧ readFst.NoSnap ∧ RState fstSpec readFst := by …
```

#### `readTwice`

```lean
-- lean/DoubleFetch/Examples.lean:15
def readTwice : Prog 1 (Byte × Byte) := .read 0 fun a => .read 0 fun b => .ret (a, b)
```

#### `remat_lenCheck_cap255_robustRefines`

```lean
-- lean/DoubleFetch/Results.lean:1356-1357
theorem remat_lenCheck_cap255_robustRefines :
    ¬ (255 < 255) ∧ RobustRefines (lenCheck 0 255).remat (lenCheck 0 255).compile := …
```

#### `remat_pure_robustRefines_const_use`

```lean
-- lean/DoubleFetch/Results.lean:1411-1413
theorem remat_pure_robustRefines_const_use :
    RobustRefines (CheckUse.pure (0 : Fin 1) (fun b => decide (b.val ≤ 0)) (fun _ => (1 : Nat)) 2).remat
      (CheckUse.pure (0 : Fin 1) (fun b => decide (b.val ≤ 0)) (fun _ => (1 : Nat)) 2).compile := …
```

#### `rereadFallback_implements_rvalid_not_singleRead`

```lean
-- lean/DoubleFetch/Results.lean:288-290
theorem rereadFallback_implements_rvalid_not_singleRead {α : Type} (spec : Region 1 → α) :
    Implements (rereadFallback spec) spec ∧ RValid spec (rereadFallback spec) ∧
      ¬ SingleRead (rereadFallback spec) := by …
```

#### `robustRefines_examples`

```lean
-- lean/DoubleFetch/Examples.lean:125-126
theorem robustRefines_examples :
    RobustRefines rereadCompare (tagOnce 0) ∧ ¬ RobustRefines (lenReread 0 4) (lenOnce 0 4) := …
```

#### `robustRefines_hqp_counterexample`

```lean
-- lean/DoubleFetch/Results.lean:1379-1383
theorem robustRefines_hqp_counterexample :
    PrivRefines (lenCheck 0 0).remat (lenCheck 0 0).compile ∧
      ¬ RobustRefines (lenCheck 0 0).remat (lenCheck 0 0).compile ∧
      RValid (lpParse 0) (lenCheck 0 0).compile ∧ RSafe (CopyInBounds 0) (lenCheck 0 0).compile ∧
      ¬ RValid (lpParse 0) (lenCheck 0 0).remat ∧ ¬ RSafe (CopyInBounds 0) (lenCheck 0 0).remat := …
```

#### `robustRefines_source_counterexample`

```lean
-- lean/DoubleFetch/Results.lean:1393-1395
theorem robustRefines_source_counterexample :
    RobustRefines (lenReread 0 0) (lenReread 0 0) ∧ ¬ RValid (lpParse 0) (lenReread 0 0) ∧
      ¬ RSafe (CopyInBounds 0) (lenReread 0 0) := …
```

#### `robustRefines_transfer_nonvacuous`

```lean
-- lean/DoubleFetch/Results.lean:1402-1404
theorem robustRefines_transfer_nonvacuous :
    rereadCompare ≠ tagOnce 0 ∧ RobustRefines rereadCompare (tagOnce 0) ∧
      RValid boolParse (tagOnce 0) ∧ RSafe ValidBoolOut (tagOnce 0) := …
```

#### `rsafe_examples`

```lean
-- lean/DoubleFetch/Examples.lean:69-70
theorem rsafe_examples :
    RSafe (CopyInBounds 4) (lenOnce 0 4) ∧ ¬ RSafe (CopyInBounds 4) (lenReread 0 4) := …
```

#### `rsafe_of_singleRead_hyps_nonvacuous`

```lean
-- lean/DoubleFetch/Results.lean:1715-1716
theorem rsafe_of_singleRead_hyps_nonvacuous :
    SingleRead (lenOnce 0 4) ∧ ∀ s : Region 1, CopyInBounds 4 ((lenOnce 0 4).eval s) := by …
```

#### `rstateUnder_examples`

```lean
-- lean/DoubleFetch/Examples.lean:91-93
theorem rstateUnder_examples :
    RStateUnder OneStepVersionWriter seqSpec seqlockReader ∧
      ¬ RStateUnder TwoStepVersionWriter seqSpec seqlockReader := …
```

#### `rstateUnder_true_iff`

```lean
-- lean/DoubleFetch/Examples.lean:85-86
theorem rstateUnder_true_iff {n : Nat} {α : Type} (spec : Region n → α) (p : Prog n α) :
    RStateUnder (fun _ => True) spec p ↔ RState spec p := …
```

#### `rstate_examples`

```lean
-- lean/DoubleFetch/Examples.lean:80-81
theorem rstate_examples :
    RState pairSpec (snapParse pairSpec) ∧ ¬ RState pairSpec (copyParse pairSpec) := …
```

#### `rvalid_examples`

```lean
-- lean/DoubleFetch/Examples.lean:74-75
theorem rvalid_examples :
    RValid pairSpec (copyParse pairSpec) ∧ ¬ RValid (lpParse 4) (lenReread 0 4) := …
```

#### `rvalid_imp_exists_singleRead_rvalid_privRefines`

```lean
-- lean/DoubleFetch/Readings.lean:30-32
theorem rvalid_imp_exists_singleRead_rvalid_privRefines (spec : Region n → α) (p : Prog n α)
    (hp : RValid spec p) :
    ∃ q : Prog n α, SingleRead q ∧ RValid spec q ∧ PrivRefines p q := by …
```

#### `rvalid_not_imp_exists_singleRead_implements_privRefines`

```lean
-- lean/DoubleFetch/Readings.lean:58-61
theorem rvalid_not_imp_exists_singleRead_implements_privRefines :
    RValid pairSpec (Prog.ret (0, 0) : Prog 2 (Byte × Byte)) ∧
      ¬ ∃ q : Prog 2 (Byte × Byte), SingleRead q ∧ Implements q pairSpec ∧
        PrivRefines (Prog.ret (0, 0)) q := by …
```

#### `seqSpec_not_noByteDeterminesOutput`

```lean
-- lean/DoubleFetch/Examples.lean:166
theorem seqSpec_not_noByteDeterminesOutput : ¬ NoByteDeterminesOutput seqSpec := by …
```

#### `seqlock_accepted_hacc_counterexample`

```lean
-- lean/DoubleFetch/Results.lean:1235-1238
theorem seqlock_accepted_hacc_counterexample :
    IncrementBoundedWriter 256 (Adversary.const (reg3 1 0 0)) ∧
      seqlockReader.exec (Adversary.const (reg3 1 0 0)) ≠ some (0, 0) ∧
      seqSpec (Adversary.const (reg3 1 0 0) 0) ≠ some (0, 0) := …
```

#### `seqlock_accepted_torn_of_256Increments`

```lean
-- lean/DoubleFetch/Results.lean:1201-1204
theorem seqlock_accepted_torn_of_256Increments :
    IncrementBoundedWriter 257 seqWrapAdv ∧ ¬ IncrementBoundedWriter 256 seqWrapAdv ∧
      seqlockReader.exec seqWrapAdv = some (0, 1) ∧ seqSpec (seqWrapAdv 0) ≠ some (0, 1) ∧
      ∀ t : Nat, seqSpec (seqWrapAdv t) ≠ some (0, 1) := by …
```

#### `seqlock_incrementBound_nonvacuous`

```lean
-- lean/DoubleFetch/Results.lean:1266-1268
theorem seqlock_incrementBound_nonvacuous :
    IncrementBoundedWriter 256 (Adversary.const (reg3 0 5 5)) ∧
      seqlockReader.exec (Adversary.const (reg3 0 5 5)) = some (5, 5) := …
```

#### `seqlock_not_rstateUnder_twoStepVersionWriter`

```lean
-- lean/DoubleFetch/Results.lean:1052-1056
theorem seqlock_not_rstateUnder_twoStepVersionWriter :
    TwoStepVersionWriter seqTwoStepAdv ∧ ¬ OneStepVersionWriter seqTwoStepAdv ∧
      seqlockReader.exec seqTwoStepAdv = none ∧
      (∀ t : Nat, seqlockReader.exec seqTwoStepAdv ≠ seqSpec (seqTwoStepAdv t)) ∧
      ¬ RStateUnder TwoStepVersionWriter seqSpec seqlockReader := by …
```

#### `seqlock_not_rstate_rogueWriter`

```lean
-- lean/DoubleFetch/Results.lean:1027-1030
theorem seqlock_not_rstate_rogueWriter :
    ¬ OneStepVersionWriter seqRogueAdv ∧ seqlockReader.exec seqRogueAdv = some (1, 2) ∧
      (∀ t : Nat, seqlockReader.exec seqRogueAdv ≠ seqSpec (seqRogueAdv t)) ∧
      ¬ RState seqSpec seqlockReader := by …
```

#### `seqlock_oneStep_nonvacuous`

```lean
-- lean/DoubleFetch/Results.lean:1251-1253
theorem seqlock_oneStep_nonvacuous :
    OneStepVersionWriter seqSlowAdv ∧ seqlockReader.exec seqSlowAdv = none ∧
      seqSpec (seqSlowAdv 1) = none := by …
```

#### `seqlock_positive_control`

```lean
-- lean/DoubleFetch/Results.lean:1019-1021
theorem seqlock_positive_control :
    HasUndeterminedState seqSpec ∧ seqlockReader.NoSnap ∧
      RStateUnder OneStepVersionWriter seqSpec seqlockReader := …
```

#### `sevenNine`

```lean
-- lean/DoubleFetch/Examples.lean:18
def sevenNine : Adversary 1 := fun t _ => if t = 0 then 7 else 9
```

#### `singleRead_examples`

```lean
-- lean/DoubleFetch/Examples.lean:39
theorem singleRead_examples : SingleRead (lenOnce 0 4) ∧ ¬ SingleRead (lenReread 0 4) := by …
```

#### `singleRead_hyp_counterexample_rsafe`

```lean
-- lean/DoubleFetch/Results.lean:1692-1694
theorem singleRead_hyp_counterexample_rsafe :
    (∀ s : Region 1, CopyInBounds 0 ((lenReread 0 0).eval s)) ∧ ¬ SingleRead (lenReread 0 0) ∧
      ¬ RSafe (CopyInBounds 0) (lenReread 0 0) := by …
```

#### `singleRead_hyp_counterexample_rvalid`

```lean
-- lean/DoubleFetch/Results.lean:1668-1670
theorem singleRead_hyp_counterexample_rvalid :
    Implements (lenReread 0 0) (lpParse 0) ∧ ¬ SingleRead (lenReread 0 0) ∧
      ¬ RValid (lpParse 0) (lenReread 0 0) := …
```

#### `singleRead_read_then_snap_rejected`

```lean
-- lean/DoubleFetch/Examples.lean:46-47
theorem singleRead_read_then_snap_rejected :
    ¬ SingleRead (.read 0 fun _ => .snap fun s => .ret (s 0) : Prog 1 Byte) := by …
```

#### `singleRead_zero_double_snap`

```lean
-- lean/DoubleFetch/Results.lean:1733-1734
theorem singleRead_zero_double_snap :
    SingleRead (.snap fun _ => .snap fun _ => .ret () : Prog 0 Unit) := …
```

#### `snapParse_pair_rstate_counterexample`

```lean
-- lean/DoubleFetch/Results.lean:890-892
theorem snapParse_pair_rstate_counterexample :
    HasUndeterminedState pairSpec ∧ ¬ (snapParse pairSpec).NoSnap ∧
      RState pairSpec (snapParse pairSpec) := …
```

#### `staticSafe_hyp_counterexample_rsafe`

```lean
-- lean/DoubleFetch/Results.lean:1705-1708
theorem staticSafe_hyp_counterexample_rsafe :
    SingleRead (Prog.ret (some 1) : Prog 1 (Option Nat)) ∧
      ¬ (∀ s : Region 1, CopyInBounds 0 ((Prog.ret (some 1) : Prog 1 (Option Nat)).eval s)) ∧
      ¬ RSafe (CopyInBounds 0) (Prog.ret (some 1) : Prog 1 (Option Nat)) := by …
```

#### `torn_impossibility_nonvacuous`

```lean
-- lean/DoubleFetch/Results.lean:918-919
theorem torn_impossibility_nonvacuous :
    HasUndeterminedState pairSpec ∧ (copyParse pairSpec).NoSnap := …
```

#### `twoStepVersionWriter_examples`

```lean
-- lean/DoubleFetch/Examples.lean:205-206
theorem twoStepVersionWriter_examples :
    TwoStepVersionWriter seqTwoStepAdv ∧ ¬ TwoStepVersionWriter seqRogueAdv := by …
```

#### `validBoolOut_examples`

```lean
-- lean/DoubleFetch/Examples.lean:148
theorem validBoolOut_examples : ValidBoolOut (some 1) ∧ ¬ ValidBoolOut (some 2) := by …
```

#### `validE_examples`

```lean
-- lean/DoubleFetch/Examples.lean:249-250
theorem validE_examples :
    ValidE 0 7 ∧ ValidE 1 1 ∧ ¬ ValidE 1 2 ∧ ¬ ValidE 2 0 := by …
```

#### `versionPath_examples`

```lean
-- lean/DoubleFetch/Examples.lean:229-230
theorem versionPath_examples :
    VersionPath 1 (reg3 0 5 5) (reg3 1 5 5) ∧ ¬ VersionPath 0 (reg3 0 5 5) (reg3 0 6 6) := by …
```

#### `versionStep_examples`

```lean
-- lean/DoubleFetch/Examples.lean:188-189
theorem versionStep_examples :
    VersionStep (reg3 0 5 5) (reg3 1 5 5) ∧ ¬ VersionStep (reg3 0 5 5) (reg3 0 6 6) := by …
```

#### `viewOK_examples`

```lean
-- lean/DoubleFetch/Examples.lean:254-255
theorem viewOK_examples :
    ViewOK (some [(0, 0)]) ∧ ViewOK none ∧ ¬ ViewOK (some [(1, 2)]) := by …
```

#### `viewProg_example`

```lean
-- lean/DoubleFetch/Examples.lean:267
theorem viewProg_example : (viewProg 2).eval (reg2 1 0) = some [(1, 0), (1, 0)] := by …
```

#### `viewProg_nonvacuous`

```lean
-- lean/DoubleFetch/Results.lean:1739-1741
theorem viewProg_nonvacuous :
    (∀ t, t < 2 + 2 * 2 → Adversary.const (reg2 1 0) t = Adversary.const (reg2 1 0) 0) ∧
      (viewProg 2).exec (Adversary.const (reg2 1 0)) = some [(1, 0), (1, 0)] := …
```

#### `viewProg_tagFlip_invalid`

```lean
-- lean/DoubleFetch/Results.lean:1465-1467
theorem viewProg_tagFlip_invalid :
    ¬ (∀ t, t < 2 + 2 * 1 → viewFlipAdv t = viewFlipAdv 0) ∧
      (viewProg 1).exec viewFlipAdv = some [(1, 2)] ∧ ¬ ViewOK ((viewProg 1).exec viewFlipAdv) := by …
```

#### `viewProg_validSwitch_breaks_viewOK`

```lean
-- lean/DoubleFetch/Results.lean:1485-1488
theorem viewProg_validSwitch_breaks_viewOK :
    (∀ t : Nat, ValidE (validSwitchAdv t 0) (validSwitchAdv t 1)) ∧
      (viewProg 1).exec validSwitchAdv = some [(1, 2)] ∧
      ¬ ViewOK ((viewProg 1).exec validSwitchAdv) := by …
```

#### `viewProg_zero_rsafe`

```lean
-- lean/DoubleFetch/Results.lean:1504
theorem viewProg_zero_rsafe : RSafe ViewOK (viewProg 0) := by …
```

#### `viewSpec_examples`

```lean
-- lean/DoubleFetch/Examples.lean:271-272
theorem viewSpec_examples :
    viewSpec 2 (reg2 1 0) = some [(1, 0), (1, 0)] ∧ viewSpec 2 (reg2 1 2) = none := by …
```

### Statement and closure hashes

**What is hashed.** For every Lean name referenced in `results.json` (fields `lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean`, and the hypothesis `counterexample` fields; 217 names), `audit/statements.json` records `statement_sha256`, the SHA-256 of the UTF-8 text of Lean's `repr` of the declaration's type; `closure_sha256`, the SHA-256 of the sorted, newline-joined entries `name : repr(type)`, followed by ` := repr(value)` for constants that are not theorems, over every package-local constant reachable from that type through types, definition values and inductive constructors (theorem bodies are excluded); and `closure_size`, the number of such entries. For a definition, the statement is its type, so its body enters the closure of every statement that mentions it. The table lists these values with the axioms of each name (`none`: no axiom). Names are relative to the namespace `Toy.DoubleFetch`. Roles: `result` (a theorem of the result), `nonvacuity` (its non-vacuity witness), `control` (a positive control), `ce:h` (the counterexample for hypothesis `h`), `cited` (a definition, example or auxiliary lemma that the result's card lists under `lean_names` because the result uses it: the result's section under Findings names it, possibly in dot notation such as `p.exec`, or it occurs in the statement of a theorem or in the definition of a constant that the card lists), `pkg` (a package-wide definition, example or auxiliary lemma that no result uses in that sense, for example the definition-adequacy examples under Definitions and the auxiliary lemmas they rely on; these names are listed under `lean_names` of the first card in `results.json`, `snapshot-parse-rstate`, solely so that their hashes are recorded, and Result 1 does not use them). The `pkg` rows come last.

| Name (`Toy.DoubleFetch.`) | Result: role | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `snapParse_exec_eq_and_rstate` | 1 result, 13 cited, 20 cited | none | `107a9f81ae5e0ad833c34b0d77480abf330baa6e5d2c0103d8b582e2b6e6a2fa` | `57fa9f8f15ed7f44fc1972e8381dfd03f375c573933eafe1f397f50d71e134a8` (18) |
| `snapParse_pair_rstate_counterexample` | 1 nonvacuity, 1 cited, 13 control, 13 ce:hp, 13 cited | Quot.sound, propext | `5a5d7a942840d5ea6ec9757aa22665d4a7129e4720ab8944f1bcb4c326785784` | `93f30cc194a53e6c415bb24af1dfa7777082aedc695d4357d143e0762c3552ab` (24) |
| `Adversary` | 1 cited, 2 cited, 3 cited, 4 cited, 5 cited, 6 cited, 7 cited, 8 cited, 9 cited, 10 cited, 11 cited, 12 cited, 13 cited, 14 cited, 15 cited, 16 cited, 17 cited, 18 cited, 19 cited, 20 cited | none | `f6f89b1e202b0402af79d58f047c64c0c027411fd8a20194e7a83a70d5bb9d4f` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Prog` | 1 cited, 2 cited, 3 cited, 4 cited, 5 cited, 6 cited, 7 cited, 8 cited, 9 cited, 10 cited, 11 cited, 12 cited, 13 cited, 14 cited, 15 cited, 16 cited, 17 cited, 18 cited, 19 cited, 20 cited | none | `3ab8d5bdfcd56e7d189794f7263111ae33eeadea6ef21c09ca4067e52b2b35b9` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Prog.exec` | 1 cited, 2 cited, 3 cited, 4 cited, 5 cited, 6 cited, 7 cited, 8 cited, 9 cited, 10 cited, 11 cited, 12 cited, 13 cited, 14 cited, 15 cited, 17 cited, 18 cited, 19 cited, 20 cited | none | `d7f519bf16325ee0845ad20a5860034e604da33baab9d6109d7fe6b93e6f287c` | `1df73a30f9bd8c51dc5e2972125a8fc8ddb08d83d3346c1f3973673cb41e7bd8` (7) |
| `Prog.execFrom` | 1 cited, 2 cited, 3 cited, 4 cited, 5 cited, 6 cited, 7 cited, 8 cited, 9 cited, 10 cited, 11 cited, 12 cited, 13 cited, 14 cited, 15 cited, 17 cited, 18 cited, 19 cited, 20 cited | none | `edc7c133062f8609cfcfcfd1af8a5986009770c6bbe8fe375cf7ac175b802d36` | `1df73a30f9bd8c51dc5e2972125a8fc8ddb08d83d3346c1f3973673cb41e7bd8` (7) |
| `RState` | 1 cited, 3 cited, 13 cited, 18 cited, 20 cited | none | `13c934c3d640f8f892ead658269058256435451b25a05ea8ca0cdd659f2bb0d3` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `Region` | 1 cited, 2 cited, 3 cited, 4 cited, 5 cited, 6 cited, 7 cited, 8 cited, 9 cited, 10 cited, 11 cited, 12 cited, 13 cited, 14 cited, 15 cited, 16 cited, 17 cited, 18 cited, 19 cited, 20 cited | none | `f6f89b1e202b0402af79d58f047c64c0c027411fd8a20194e7a83a70d5bb9d4f` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `byteCopy` | 1 cited, 2 cited | propext | `4181b188ad7eb0e4accf8b25294fe90b104f10ebe5baafd4f846cda5c3f7ce64` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `copyParse_pair_torn_not_rstate` | 1 cited, 2 nonvacuity, 2 cited, 3 result, 3 nonvacuity, 4 cited | Quot.sound, propext | `ad9d8ec61847ae81f7caa32cd62eda65ee8ea9fc5c23e3ef0d7f8f370758f798` | `18b2ff7e154c2cbdd1b2649042187561e92dfb9c4f7745822ae2f0e49c997a26` (27) |
| `readSeq` | 1 cited, 2 cited | none | `057083d045c4842eec312306196591cb96326fd9920ed4cd0d71397e694635b9` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `snapParse` | 1 cited, 20 cited | none | `42514efcbd3524f8fb46290fc2dc47029c569689ecd10d67d0e73e4a18cf7a80` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `copyParse_exec_eq_diagonal_and_rvalid` | 2 result | Quot.sound, propext | `a44d81f493494a7f1a253af2e36c36e2685c4c2c1a19864552521e53fb0f1ce0` | `7b88987615678591b76fd7c52e1873663799f2e63bf8948ac1457610117640b8` (23) |
| `copyParse_singleRead_implements` | 2 result, 9 cited, 12 result | Quot.sound, propext | `2fdce7107cfd5cd4711756672a8775cffc8cb0bb8541ec34d9106cdb0c0b2b43` | `61ac3a1735c0a97b98a1ba708fd9902a01544ff341d7b8fede52ddb097dc631d` (25) |
| `Prog.SingleReadFrom` | 2 cited, 4 cited, 5 cited, 6 cited, 7 cited, 8 cited, 9 cited, 10 cited, 11 cited, 16 cited, 20 cited | none | `c1fc47778d7c913907800ff7478f06f7429c4e98626ccc0907266b9eb4ade086` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `Prog.eval` | 2 cited, 4 cited, 5 cited, 6 cited, 7 cited, 8 cited, 9 cited, 16 cited, 19 cited | none | `f7a2a40af2b26dcc21cb1f6a1bb6e0628acb56690ad1657a01cd279497173789` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `RValid` | 2 cited, 5 cited, 9 cited, 10 cited, 11 cited, 16 cited, 18 cited, 20 cited | none | `13c934c3d640f8f892ead658269058256435451b25a05ea8ca0cdd659f2bb0d3` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `SingleRead` | 2 cited, 4 cited, 5 cited, 6 cited, 7 cited, 8 cited, 9 cited, 10 cited, 11 cited, 16 cited, 20 cited | none | `b0db126ec9e70259f996d397ba7a90c1db6fd214da385dc216d597e38f2b5550` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `copyParse` | 2 cited, 3 cited, 4 cited, 8 cited, 9 cited, 12 cited, 13 cited, 20 cited | propext | `42514efcbd3524f8fb46290fc2dc47029c569689ecd10d67d0e73e4a18cf7a80` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `Adversary.const` | 3 cited, 15 cited, 19 cited, 20 cited | none | `2a264a531d606dad8bc866abaf17fe56786fbae83175b145a46ba64607e6fcde` | `b29ed9a094bb433c9afd93d55dcbdd811fb221101f10980e5f9a592b517d3698` (3) |
| `Prog.exec_const` | 3 cited | none | `c919a23aaee739ca6fc6d69c7d6406cca8d464b071af2b5bea33c5b521d59423` | `60fb961a200b1e0afc6a5192acbfc697c731d13302570173a62d9c30a5df8f2f` (20) |
| `pairSpec` | 3 cited, 9 cited, 13 cited | propext | `dd6201d9c7bbf290ec2a7c421bc8bc7f28e682e9cf5e8ce15b4fda9d6ba96d5b` | `d71ff460cc7d8cf6fb0122287406af5a5c7336cd3810e5bee8c21b9132745f69` (2) |
| `pairTornAdv` | 3 cited | propext | `e0b61b0569969deac7d24055b1b1e3d562584be2014e485663db7ad8f6a57fda` | `b29ed9a094bb433c9afd93d55dcbdd811fb221101f10980e5f9a592b517d3698` (3) |
| `reg2` | 3 cited, 19 cited, 20 cited | none | `5ab80e24d9c898ca0b65bb84e1dd531bfb83ffb3bf95ea6ff836ce71023bc1b5` | `d71ff460cc7d8cf6fb0122287406af5a5c7336cd3810e5bee8c21b9132745f69` (2) |
| `singleRead_exec_eq_eval_assemble` | 4 result, 5 cited | Quot.sound, propext | `8be1f37302fc70de0950d9f0bd91820ae4212e64ec461101a529526c55c54ff7` | `5474dbcfa3a97868b6caede96deec2b5f624f0b6c037dded60dac80f456c6e27` (27) |
| `dataDepProg_singleRead` | 4 nonvacuity, 4 cited | Quot.sound, propext | `c05eb73044c3b8a34895dd8f746603f05527150d235ed287ed5dffa759537b5f` | `5601152c8a8fd02c7dcce558ad4d2cc244fc285f7acde731f1620b6c00ceb5e5` (17) |
| `lenReread_exec_ne_eval_assemble` | 4 ce:hp, 4 cited | Quot.sound, propext | `9d6931d5c82ce79bd1592d00439e80d4fad5a281ffe5ec626982e5e6a24992cc` | `910d0b147cb7cf6e28cba05d59ff25ca32a9120927ceaf26b7c0a5da974200c3` (40) |
| `Prog.assemble` | 4 cited | none | `49f4cc59bbceeb9f551fd7b27749bc976462b6306ce0389e1db744944576d31e` | `1df73a30f9bd8c51dc5e2972125a8fc8ddb08d83d3346c1f3973673cb41e7bd8` (7) |
| `Prog.assembleFrom` | 4 cited | none | `4a25154cfbeeba54b48da82e02b14cbff6045d0c187b23ba443e3242ab5e370f` | `1df73a30f9bd8c51dc5e2972125a8fc8ddb08d83d3346c1f3973673cb41e7bd8` (7) |
| `dataDepProg` | 4 cited | propext | `62619047e79a6dd1333df6a527a05ddcad1598188135ddc51e88b21d0c772da0` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `lenOnce` | 4 cited, 5 cited, 6 cited, 9 cited, 10 cited | propext | `2f9a95235d93269817007dff6630d2dcd2cc0419abe3803379fbb08b164a21cf` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `lenReread` | 4 cited, 8 cited, 9 cited, 10 cited | propext | `2f9a95235d93269817007dff6630d2dcd2cc0419abe3803379fbb08b164a21cf` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `remat_lenCheck_singleRead_robust_to_not_rsafe_not_rvalid` | 4 cited, 5 cited, 6 cited, 16 result | Quot.sound, propext | `42a9194488082be02f6d2ec2e4eaa59ed27bfe503b12e6d07e548f4900264bd5` | `ee813d96a8076eecfa7ba31d6e50b5152098359c79fdd44d98b8660e65de1299` (40) |
| `rereadCompare_implements_rvalid_rsafe_not_singleRead_not_rstate` | 4 cited, 5 cited, 7 result, 7 nonvacuity, 20 cited | Quot.sound, propext | `8f69dfd4a9390916a9328331951b4d6a9ce70997fc13b74e0714ce42f36a942f` | `33132bbd2682c4c4cfb1c6f804ab361886167302e3e4649a6bf7e3be30bbbf0e` (33) |
| `singleRead_zero_double_snap` | 4 cited | none | `408242ae36f226c13d19e1b3b64771a90db91e262ec4207f512365b44782b4e6` | `ef85938be8129ca7e05c38413382cd984265f9422c82a70826a4d720c3d7329f` (15) |
| `rvalid_of_singleRead_of_implements` | 5 result | Quot.sound, propext | `6a27c1b518888a9b9c3828f2c3a3cc2ab3783af7f623e8db05b9524c4e8bad5d` | `110aa339321b9c479cb7a0b4668536a60f2a487767c7af42f0a5ebde00fa36a3` (25) |
| `lenOnce_singleRead_implements` | 5 nonvacuity, 5 cited, 10 result | propext | `b3709d38419fa4177490154c2368d51d3579c2e618a7cb80ebbba616bdda911e` | `ad6f82be438ad469db861e567bf05470e526ecceafe6672a8e1b7d23615f4ac4` (31) |
| `implements_hyp_counterexample_rvalid` | 5 ce:himpl, 5 cited | Quot.sound, propext | `e26c354d8b9c5cc9e6ef2d66de9481f041f04a1f63929703cc2820767f3de58f` | `ffe2caf4294121b8a659a97e475cacc83b412be2089af9b399d702956d8a2af5` (27) |
| `singleRead_hyp_counterexample_rvalid` | 5 ce:hp, 5 cited | Quot.sound, propext | `2198f1422b4ce1ab3d56103ca13ad76bfdea43fe6e3dddf82423ae906e89b8f1` | `e7604700a24325e938fdf45e8fc2547af3ce06d0dcc562d9e4347b2872457027` (37) |
| `Implements` | 5 cited, 9 cited, 10 cited, 11 cited, 20 cited | none | `6c532ce436ffc7df6b1b0884c7735a8faeb330a232af3790aae255691f78f4f6` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `lpParse` | 5 cited, 8 cited, 9 cited, 10 cited, 16 cited | propext | `bd8c9c8ce5cd8cdfdddf59aa6075d6b8fe76e66eef945da047cef79166ec69b8` | `d71ff460cc7d8cf6fb0122287406af5a5c7336cd3810e5bee8c21b9132745f69` (2) |
| `rsafe_of_singleRead_of_staticSafe` | 6 result | Quot.sound, propext | `14f3badfedb00c1debd33382addda0a65f2c3e4fd381daa95d3c5a53211706f5` | `ee6963c7e5cdbb4dba1d29705d6dfbfbd4e03d9391428259f2789889761dc642` (24) |
| `rsafe_of_singleRead_hyps_nonvacuous` | 6 nonvacuity, 6 cited | Quot.sound, propext | `ebb2e6e18eade87ad2f8da3ba1a09a73a62f6c8d8e97619232ba4312d0a55974` | `27f6ade6e36ec1166b36adf5850cb933dc33ac4bfae718633f152b3dbec43cb1` (31) |
| `singleRead_hyp_counterexample_rsafe` | 6 ce:hp, 6 cited | Quot.sound, propext | `8b44d111e220174df994084fb6c8c5f708362785201acdb7c8501645db13eb99` | `c15c5a8f4cb6f187e587c0175da86a09cc794dec57a38b5536b7d12df11ded36` (37) |
| `staticSafe_hyp_counterexample_rsafe` | 6 ce:hsafe, 6 cited | propext | `5df29f28ad38bd0585f86f8ae930b2df19bee903b419ed476445a9b175acbce8` | `2a6e26a8b64aac6bcf3c9e4a84489c39b080ec06706b99cd0d6bb377edf201ca` (26) |
| `CopyInBounds` | 6 cited, 10 cited, 16 cited | none | `1b4fd886a3fafac2ac7bb295ce26e5e5ba16a5a0fe135f540fe74a1f6596c32a` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `ValidBoolOut` | 7 cited, 11 cited, 18 cited | none | `303097e1fab8961775a3e1d90d9cdf16f717b83ee4451aed7e468cdfd59b7edd` | `82804c9e2d239f4b0f59dcc2ba5c5e14f957d39d467a1e9f59402fec45a23168` (1) |
| `boolParse` | 7 cited, 8 cited, 9 cited, 11 cited, 18 cited | propext | `c507c5fffb5ee78c7cbc5c75a77f64f50b98a83cfb3ed8c49df4eb2b8e016512` | `d71ff460cc7d8cf6fb0122287406af5a5c7336cd3810e5bee8c21b9132745f69` (2) |
| `rereadCompare` | 7 cited, 8 cited, 9 cited, 18 cited, 20 cited | propext | `6bae8a11b88eba2ae6d19867ff14ab3aaf4ad3a94930f5c46bbe7678dca884db` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `rereadFallback` | 7 cited | propext | `84f75ca30a25a5f4d0fc19c73ceaa3b78a32d4d15a68947a0412b28f54ac9a97` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `rereadFallback_implements_rvalid_not_singleRead` | 7 cited | Quot.sound, propext | `e74dcf6a22f2b3c30ed6ed87d04e75a16797325b5f430973cda17c7e89cfa0bf` | `71cc85a3d19a45299410250358d076d58c7aead129a1c94b0bd5c7bc0133d4a1` (28) |
| `rvalid_iff_robustRefines_copyParse` | 8 result | Quot.sound, propext | `f6f3d0441f3654ef8a98300d6e80f87c19603aaaab580f09491193e8b67bc042` | `22d60926a2de9765e5f3047a2c7f27fadfdf124574e94967954008e00f92e6fc` (24) |
| `rvalid_iff_robustRefines_singleRead_implementation` | 8 result, 9 cited | Quot.sound, propext | `684369250f0037ec2a6c7396b18740d245857460885c10aca5ef7256d78aa563` | `30addd57519927009ff93a7b3857d590ba81d59405b835402365c1f415a2c115` (26) |
| `robustRefines_transfer_nonvacuous` | 8 nonvacuity, 8 cited, 18 nonvacuity, 18 cited | Quot.sound, propext | `c7cc399b5916d544d5996efb79e5d81b23a9251b7461aa2cba0b6d4068486c31` | `5612fff2688263ef33986ec6a42d9a1256d28bfadcd1560edd12fb32ad7cdcd3` (35) |
| `RobustRefines` | 8 cited, 17 cited, 18 cited | none | `419b1b1973d68eab867bff623d50e303ae52686375d7a5348897df918803f76a` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `robustRefines_iff_preserves_rsafe` | 8 cited, 17 cited, 18 result | none | `ea1f28d4a75bb27f657b439c56d4ae254fe1f5cf999ac83968cb9d7e2fb6e245` | `b70bdc96401ad6290d467ac3989ec55125b30bd8ffe6652c21e929ae4cedcc63` (18) |
| `robustRefines_rereadCompare_tagOnce_not_preserves_rstate` | 8 cited, 17 cited, 18 result | Quot.sound, propext | `9ceb24fe69657cabb7bd2b4c25604d40ffabfed66f996903c8c4c33db51b495c` | `d1fc293d16985080dee04f77c24999decce48f50e0d0ddafbd97e2771901f6f3` (32) |
| `rvalid_equivalence_readings_refuted` | 8 cited, 9 result | Quot.sound, propext | `03e31075113a645333fb666ce11bc526543e6a106362da24d61e1e0ea328c298` | `42a78d914ceffe2718423e734751dfa5857d40b45fb1a727f2326cbab8e5ab1d` (42) |
| `rvalid_examples` | 8 cited | Quot.sound, propext | `504e39f4fcf99de36c027c61d7aa56950e42677dfdb9a4aa78d705045db2bafe` | `132b746f1fcc71eb87af0169b8eed547d1ec3579bc59b4073f525d78843aea09` (37) |
| `tagCheck` | 8 cited, 11 cited, 18 cited | propext | `876c21ebeedd0dcb604834486128886344da16e2ad185cb6c00765dbc8829316` | `73f9e7d01afad27fb4a2d6cb44cebb5c492cea6c3da9051a0dd9f8e4cd315214` (8) |
| `tagOnce` | 8 cited, 11 cited, 18 cited | propext | `411d4d4b4e5d91195b58e6a479207409bdb79d83b75e308a0d0ecb1b790fc435` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `lenReread_cap_lt_255_nonvacuous` | 9 nonvacuity, 9 cited, 10 nonvacuity, 10 cited, 16 nonvacuity, 16 cited, 17 nonvacuity, 17 cited | Quot.sound, propext | `d0a87deb265a5e6b0b9ef6a704fd8cd8c86c8c8ed3c9fce190e86ce989bb83c9` | `5e25698a5479f7f5d4377ed29a4b4d60e4f91b47b684aee0ed48886ccc25e4c6` (29) |
| `lenReread_cap255_counterexample` | 9 ce:hcap, 9 cited, 10 ce:hcap, 10 cited, 16 ce:hcap, 16 cited | Quot.sound, propext | `1fe46071862ac575e170be8f6ae5512e0f5ec259eb2f56cb3a47b6fd8a30a7ae` | `d261e0c67ce81f00905d6d91aac2525887e654c6c0da4aa29df58213ebc69edb` (32) |
| `Byte` | 9 cited, 11 cited, 17 cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `PrivRefines` | 9 cited, 16 cited, 17 cited, 20 cited | none | `419b1b1973d68eab867bff623d50e303ae52686375d7a5348897df918803f76a` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `exists_singleRead_implements_privRefines_iff_implements` | 9 cited | Quot.sound, propext | `0c0964830ec665ef8e8fee91634ffa33571b0a5a9544ed719839ffff0d8e8ccb` | `1f133c9aa4fc6e24d0b7f95adb01c1a88e685b3f915fdcb94ab45ed70dc8c252` (20) |
| `lenReread_rsafe_rvalid_of_255_le_cap` | 9 cited, 10 cited | Quot.sound, propext | `c7474e6050b5ce985efbc1708a09568880ab839a86a99d1f2e7d26785d7cbe70` | `d261e0c67ce81f00905d6d91aac2525887e654c6c0da4aa29df58213ebc69edb` (32) |
| `rvalid_imp_exists_singleRead_rvalid_privRefines` | 9 cited | Quot.sound, propext | `e1e82d5c36cab04dbb0d9226e5533922c6110644394cf51e4b6d969238d185fb` | `ce8d025b02e64c8f36a0d04d4cc0b65715ae277cb192dd16238ead2b89ae2a93` (25) |
| `rvalid_not_imp_exists_singleRead_implements_privRefines` | 9 cited | Quot.sound, propext | `acb185a4d9b355dfc129b23d1aefabe0318c7f7410058bc37e99a169174808d2` | `9f8784c3314c870c48b0a4d10f2feda728bf818609784155465b6ab82e94ec3f` (28) |
| `lenOnce_rsafe_rvalid` | 10 result | Quot.sound, propext | `8977a00956f90fe0861f0ffe3b1632efdba1f3effd17a936bc64cbf1ef973baa` | `88ee380a0db2bc0613f8efcee20c0c50949d18633e854b1ac4af9174fd696505` (32) |
| `lenReread_flip_out_of_bounds_and_invalid` | 10 result | Quot.sound, propext | `5684a17ec13ca9ff66de4448c0a134294efda889d7055fcdb7548ac5674ec4b2` | `75ba7738d63ab66ad86650e9137aa517d6ca0583b0164a750b96c836248f0beb` (32) |
| `lenReread_implements` | 10 result | propext | `41752bd6adf548bd9a92965db7569dd02d552bbf48674ab1f5c2f10d6ec6dc7a` | `e7c016a90d33d3b8c2e51298135f68cf5a1b1340e5ff42c7a099d8be710de9ce` (27) |
| `lenReread_not_rsafe_not_rvalid` | 10 result | Quot.sound, propext | `c68ad36679c7082d44ce25009b3bcc9449c046b2da407c51fffeeb8054fced00` | `d261e0c67ce81f00905d6d91aac2525887e654c6c0da4aa29df58213ebc69edb` (32) |
| `RSafe` | 10 cited, 11 cited, 16 cited, 18 cited, 20 cited | none | `aa2502bdeb118f1a06b5e3f79f50cf78c28ba499bb47bd25201f1bd58a7fab68` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `lenFlipAdv` | 10 cited | propext | `0553e8ef6605c1a6301a15c5ac19124c48f554ca61e10ca67c7efabc3ef52a73` | `b29ed9a094bb433c9afd93d55dcbdd811fb221101f10980e5f9a592b517d3698` (3) |
| `tagOnce_rsafe_rvalid` | 11 result | Quot.sound, propext | `1f05d81ceda6bc58cb8eb6e1dd0e4beaee6260edc4597e58a295db8e33e4aa45` | `e41306b423dc3c0a1b12aee49579da2161ab709a68033cc2ad4b69da101b9c8c` (32) |
| `tagOnce_singleRead_implements` | 11 result | propext | `8e3d13294a84f354fd01f17b61c1234262ba48cc5df7915ab89282558fe115a7` | `93054d81e7f81b67a647f54f8196681d45bf31696a8a324948e9351ffb3962eb` (31) |
| `tagReread_flip_invalid_bool` | 11 result, 11 nonvacuity | Quot.sound, propext | `72a89b383dfd8c4547957c48ca7781eac1631fb65f27deebe8375051286b4dcc` | `2186d787d2bb457f6e574d9984662e27943aca6f993cf79a7b1152d4ccf1bd61` (32) |
| `tagReread_implements` | 11 result | propext | `e3596388ac72692877aa997a99960594b9cbac3fcda1525db1921669fcca882e` | `8aed5c21972dfcbf9be6adbdbbc333ab2b5b5dadeebfe6f2f4d80a5e12a8b12a` (27) |
| `tagReread_not_rsafe_not_rvalid` | 11 result | Quot.sound, propext | `6c621e1860bfd8aff2fdf36231023b84abb10eefe6af7286c36e0efe9e877191` | `525cb91315867ff9284f3d4d65b2179a2dd10411510fff3c7f2d07123427ea9d` (32) |
| `tagFlipAdv` | 11 cited | propext | `bd8fe21fbd6aa89a33e7b7a201844837e3d2f68e566fa0e077bbfe712e17f892` | `b29ed9a094bb433c9afd93d55dcbdd811fb221101f10980e5f9a592b517d3698` (3) |
| `tagReread` | 11 cited | propext | `411d4d4b4e5d91195b58e6a479207409bdb79d83b75e308a0d0ecb1b790fc435` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `ckParse_torn_passes_checksum_matches_no_state` | 12 result, 12 nonvacuity, 13 cited | Quot.sound, propext | `39a01eea08504aa1d99a92c6d052979bdc806750a78fcf2b38c8f0a4d0c3fd70` | `ff7ce8a3f90688107e9361e38eb6d980db472350690588cc8740699dfaf5bffd` (26) |
| `copyParse_ckParse_twoValidStates` | 12 result | Quot.sound, propext | `9f0ba0a676f10df096f0199cef35a44ef073b6f93451236b9fd09fc71691e122` | `b8716ca26977566ce35e114682d9c2ddfd076441ab7473d956e5dbcfb17edfc4` (24) |
| `copyParse_ckParse_twoValidStates_nonvacuous` | 12 nonvacuity, 12 cited | Quot.sound, propext | `fbac917c6c12172a526ee03dd7b237b1c6bb20b1dec8ec71c97b99ec87cf537e` | `6ac6feaca262ba69c2a7abb0191b48d9ac0dac92010adfbc5f023f185e7ce5be` (25) |
| `copyParse_ckParse_twoValidStates_hA_counterexample` | 12 ce:hA, 12 ce:hB, 12 cited | Quot.sound, propext | `bff43bb825eb0a2a2937b4c2b8fedba2487bfaf579fa20cc9c65f7d86729e802` | `fbecca542590ecea47a978b776783d66c6aff12771a7111d9dd71d2f9d049557` (26) |
| `copyParse_ckParse_twoValidStates_hadv_counterexample` | 12 ce:hadv, 12 cited | Quot.sound, propext | `66d2418684acdbca8d2ba31f29706b369bc28f135ca59a68101fe4c1c3504140` | `ff7ce8a3f90688107e9361e38eb6d980db472350690588cc8740699dfaf5bffd` (26) |
| `copyParse_ckParse_twoValidStates_hpass_counterexample` | 12 ce:hpass, 12 cited | Quot.sound, propext | `9dca06c4748bf3e388b3ef7b2fd25a2ae97f477de325cb59dc1d295ee4cd3ae8` | `6ac6feaca262ba69c2a7abb0191b48d9ac0dac92010adfbc5f023f185e7ce5be` (25) |
| `ckMixAdv` | 12 cited | propext | `6708d4f63100665dbb3e9ea3bc133a0d097fb11d2f3c15a036d8c85e17ab9477` | `b29ed9a094bb433c9afd93d55dcbdd811fb221101f10980e5f9a592b517d3698` (3) |
| `ckParse` | 12 cited, 13 cited | propext | `1ee611088b7cd768e3b9b47ca6a311699e68c555ea462674b513f620cbc41c97` | `d71ff460cc7d8cf6fb0122287406af5a5c7336cd3810e5bee8c21b9132745f69` (2) |
| `ckTornAdv` | 12 cited | propext | `6708d4f63100665dbb3e9ea3bc133a0d097fb11d2f3c15a036d8c85e17ab9477` | `b29ed9a094bb433c9afd93d55dcbdd811fb221101f10980e5f9a592b517d3698` (3) |
| `reg3` | 12 cited | none | `c785b38f789b4b918c51ac6c6e33ffb75d8e74c43ac86473960a22ec5466d16a` | `d71ff460cc7d8cf6fb0122287406af5a5c7336cd3810e5bee8c21b9132745f69` (2) |
| `andSpec_hasUndeterminedState` | 13 result | propext | `33f4bfd3adee7479173215f9df1c5255783737adc865f31d0312b74a2dac3b97` | `2d42506aad7232efcd17f92b45e104d4870a7ef737b76eb0ee4feac422816a7d` (6) |
| `ckParse_hasUndeterminedState` | 13 result | Quot.sound, propext | `af556a91a9f45055be23f98c557018f40908578cd45985fdfac5afc4f9a8102c` | `33c4ef9f92a8cbdee1434e1198f1dc14fb8afd65c1fb46318186efed50c2a880` (5) |
| `hasUndeterminedState_iff_no_noSnap_rstate` | 13 result | Classical.choice, Quot.sound, propext | `8a9173b00d1d956624a749185cbf05901a991836a53ec856a40365527ec85e68` | `05f80d9914c766809322e4527d28004b9e79ccd29d2e7445f0fcf75ce3ee3999` (21) |
| `not_hasUndeterminedState_of_region_one` | 13 result | Quot.sound, propext | `60cf1cf90d77ea9f762c3bdcb68db9079fb7c4c6af648d20a58baf2064fd2b9d` | `1df701282568902f9e5e5634250f41c25ef1ecb26c5dcb9ad8c4ce062121c9fa` (3) |
| `not_hasUndeterminedState_of_region_zero` | 13 result | Quot.sound | `dabbafe81b786eac9b56c81b4d84c9b4cf4d0e6e08718ca9fa19be98f96fb222` | `1df701282568902f9e5e5634250f41c25ef1ecb26c5dcb9ad8c4ce062121c9fa` (3) |
| `not_rstate_of_noSnap_of_hasUndeterminedState` | 13 result | Classical.choice, Quot.sound, propext | `87917f31b5054aacbaffb5d860f2eefe90d5c6c568a3e9bcb740f86d839ceb9e` | `05f80d9914c766809322e4527d28004b9e79ccd29d2e7445f0fcf75ce3ee3999` (21) |
| `pairSpec_hasUndeterminedState` | 13 result | Quot.sound, propext | `7b0a162e00bd1c4c2356b1ebd7f0179c84f41fc25557ff448014dc7c46a04a46` | `51b71dd7c865c579b029a73ddbafd3b8debf4bdba7243e87e34e57daaad9911e` (5) |
| `seqSpec_hasUndeterminedState` | 13 result | Quot.sound, propext | `294bc14b2707798a8c8267dbec9a1a6b4087f2fa2ffc9427431ba98ad509ee49` | `0665681200ba5379e6d98f67f5491d9d7ec64721f5ac74b77547b348b004a9e5` (5) |
| `viewSpec_hasUndeterminedState` | 13 result | propext | `2fc0fa89495118e5cfa4f251893c95a166bdae0bed51a8d6511eb986aa151b88` | `c1b30faa8274215c3ffc9dbf846e16c20a88402b048c0fda336ee88cb2166f86` (7) |
| `torn_impossibility_nonvacuous` | 13 nonvacuity, 13 cited | Quot.sound, propext | `1dbfa66b9d2d47341e8be66efaf3a9a219ebc184f7453b55ffaa6def7dd10e1e` | `5768b33c3b88fa4512ba124eec75249b638d6e9ccd3d8a50cf65de768a6b8de1` (23) |
| `seqlock_positive_control` | 13 control, 13 cited | Classical.choice, Quot.sound, propext | `5c8ae714a1d475c6ff4647b60ec27dfd8465389411142d1dc44a2c68c5997893` | `c9969ffa079e9fd89ecbf201ce1741f221d11513d973d91c078473dbddea3cec` (27) |
| `readFst_rstate_counterexample` | 13 ce:hspec, 13 cited | propext | `cfaf66c1624db5519f1c082a62d8f56b8aab2a049e1be29ea9749da238b0224b` | `94cacb8efea91577a0f6435f19c0e1f953b683e6b1fe2eb5b45aa3a7f655fe3e` (24) |
| `HasUndeterminedState` | 13 cited | none | `acdfb7d351a565e49979eff151f493dc99105b9a121d075762c87cb68778ae21` | `d71ff460cc7d8cf6fb0122287406af5a5c7336cd3810e5bee8c21b9132745f69` (2) |
| `Prog.NoSnap` | 13 cited | none | `f1fa0a3af3c0ab74a816d8c2f4c657929af52aabe334839f9750adb9c583637d` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `RStateUnder` | 13 cited, 14 cited | none | `e6b2b9a67a4c741b3b4b556338855d4416bf3db946323a9926bd00f77d0fff1a` | `1df73a30f9bd8c51dc5e2972125a8fc8ddb08d83d3346c1f3973673cb41e7bd8` (7) |
| `ValidE` | 13 cited, 19 cited, 20 cited | none | `2d4e552b03dbffc102d8f9fa1446f31010d3ee49a9456f94061fbc59e854c1e3` | `82804c9e2d239f4b0f59dcc2ba5c5e14f957d39d467a1e9f59402fec45a23168` (1) |
| `andSpec` | 13 cited | propext | `7d2855e86b9fe27fd4309a6d7884835523c63a21864d48c2ad08e357f34e8759` | `d71ff460cc7d8cf6fb0122287406af5a5c7336cd3810e5bee8c21b9132745f69` (2) |
| `fstSpec` | 13 cited | propext | `80a3ba36d472c5e623b453a3315e9cfac6343f916374dfee455bcf3df1dc3fbb` | `d71ff460cc7d8cf6fb0122287406af5a5c7336cd3810e5bee8c21b9132745f69` (2) |
| `readFst` | 13 cited | propext | `a745485df461528db07419258746cd08694ffa85772a94798a31c68693dd52f8` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `viewSpec` | 13 cited, 19 cited, 20 cited | propext | `ebde1c50a2667ef68493e4785516cfca10f63d2ed5614f9fb4938ea2a382b5db` | `d71ff460cc7d8cf6fb0122287406af5a5c7336cd3810e5bee8c21b9132745f69` (2) |
| `seqlock_rstate_of_oneStepVersionWriter` | 14 result | Classical.choice, Quot.sound, propext | `1123a7bdf00ce77a80d10aab0d4b61ac42e7a5ca171e609b8d23d6aa3a33a43f` | `6e21ca17c9c39912944f8bdcdd0dcfa1b8cd5df74a735cd84db32c7103e30a23` (22) |
| `seqlock_oneStep_nonvacuous` | 14 nonvacuity, 14 cited | Classical.choice, Quot.sound, propext | `623fc6fedf1f579dd14728a41694128bbaed7282dd9ca575605f92bfb06be9f0` | `8d8acdca502e03f261e0ff8600a6a44abedfb9db72e06f5af000d8adc899cbed` (25) |
| `seqlock_not_rstateUnder_twoStepVersionWriter` | 14 ce:hW, 14 cited | propext | `898e4d1e93506648a45ac6d69f62a08dca6e0623c96be6c70f2c1bfebef59a1d` | `b460435d4703aef3730bd803964409d145c4455c3e38c790bf4e6662ca1ad8ab` (26) |
| `seqlock_not_rstate_rogueWriter` | 14 ce:hW, 14 cited | Classical.choice, Quot.sound, propext | `64d03b05d7603ef266b66fa8a68ea8c667b1a53f2e309e7a55300ef0f4aef809` | `b75da384bed8ed956d35d138cfb3dd33eb9e2c4120f3f64d1288e7ef90a2dc3a` (25) |
| `OneStepVersionWriter` | 14 cited | propext | `e63107c48d0c00eb364e80ac9187d9f7b5484a42ae52c22b000b10a73932e3b2` | `b29ed9a094bb433c9afd93d55dcbdd811fb221101f10980e5f9a592b517d3698` (3) |
| `TwoStepVersionWriter` | 14 cited | propext | `e63107c48d0c00eb364e80ac9187d9f7b5484a42ae52c22b000b10a73932e3b2` | `b29ed9a094bb433c9afd93d55dcbdd811fb221101f10980e5f9a592b517d3698` (3) |
| `VersionStep` | 14 cited | propext | `d90f1ad168391e773e60a7d560ab7fc9185e4f8652d47021cbc7276ebd307b95` | `d71ff460cc7d8cf6fb0122287406af5a5c7336cd3810e5bee8c21b9132745f69` (2) |
| `seqRogueAdv` | 14 cited | propext | `6708d4f63100665dbb3e9ea3bc133a0d097fb11d2f3c15a036d8c85e17ab9477` | `b29ed9a094bb433c9afd93d55dcbdd811fb221101f10980e5f9a592b517d3698` (3) |
| `seqSlowAdv` | 14 cited | propext | `6708d4f63100665dbb3e9ea3bc133a0d097fb11d2f3c15a036d8c85e17ab9477` | `b29ed9a094bb433c9afd93d55dcbdd811fb221101f10980e5f9a592b517d3698` (3) |
| `seqSpec` | 14 cited, 15 cited | propext | `1ee611088b7cd768e3b9b47ca6a311699e68c555ea462674b513f620cbc41c97` | `d71ff460cc7d8cf6fb0122287406af5a5c7336cd3810e5bee8c21b9132745f69` (2) |
| `seqTwoStepAdv` | 14 cited | propext | `6708d4f63100665dbb3e9ea3bc133a0d097fb11d2f3c15a036d8c85e17ab9477` | `b29ed9a094bb433c9afd93d55dcbdd811fb221101f10980e5f9a592b517d3698` (3) |
| `seqlockReader` | 14 cited, 15 cited | propext | `8ce5d9a210aab35b3a698012253bf90e3c62dddd48ebadad16805146aa311cab` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `seqlock_accepted_eq_seqSpec_adv0_of_incrementBound` | 15 result | Classical.choice, Quot.sound, propext | `3f73fbe9c2880afdee20153fc0c71f0df4a2a693c2f3165df950f61ceec405ac` | `50ec4a8e9d55ca41629cb549f6c517136069868afd04640e968db23089205b25` (26) |
| `versionPath_any` | 15 result | Quot.sound, propext | `27f2c7dff1cc41bbbcc638ed62b87a7b33d11d32409c746eb58ea07fac33a333` | `2496fc44aeffabff85dd958031c87f5a8413ca2a74a42953fd19d4f7ea553755` (9) |
| `seqlock_incrementBound_nonvacuous` | 15 nonvacuity, 15 cited | propext | `76e8203e65701c6c06e1f1874d815e16f89d98265af3e640b41e890ce562e707` | `be4f35dcf39556735f2c5f6cb3f4847ba1b98a78c6bfcee5c228ea663d02bea0` (27) |
| `seqlock_accepted_hacc_counterexample` | 15 ce:hacc, 15 cited | propext | `82808ce2a84c3de57ac1a463d97d4ebc852d3d8c4066f3fcdea3f7a6e1714140` | `2a683e43118602738ad2a4cf801cb48905ecafcec097a1833a4a4ded0988e5e7` (28) |
| `seqlock_accepted_torn_of_256Increments` | 15 ce:hW, 15 cited | Classical.choice, Quot.sound, propext | `998d0d12bf5774df924dcc33795853af0ade05fc7e58b67f113e4badae43940b` | `51b8ad9b1a634e72870cdf399eb0c63bd58fc33bd724d89e0eeb21891316e376` (28) |
| `IncrementBoundedWriter` | 15 cited | propext | `a23b38e2fd240cd53ef0bd405ad615e9930ff1a918d23168ad76826b357f6a96` | `b29ed9a094bb433c9afd93d55dcbdd811fb221101f10980e5f9a592b517d3698` (3) |
| `VersionPath` | 15 cited | propext | `44fb863be7c17fa7fa4eb9318a50503ef5869d31778499e3012b442804c1747c` | `d71ff460cc7d8cf6fb0122287406af5a5c7336cd3810e5bee8c21b9132745f69` (2) |
| `seqWrapAdv` | 15 cited | propext | `6708d4f63100665dbb3e9ea3bc133a0d097fb11d2f3c15a036d8c85e17ab9477` | `b29ed9a094bb433c9afd93d55dcbdd811fb221101f10980e5f9a592b517d3698` (3) |
| `remat_privRefines_compile` | 16 result | none | `285caa0cc332336fe6a1356b152808e07c75a9cb559fc67a14cdb186ee035b62` | `47076325f5db8afb4f2680b566e137de9db0c9128059e39ad08222a2630df872` (23) |
| `CheckUse` | 16 cited | none | `3ab8d5bdfcd56e7d189794f7263111ae33eeadea6ef21c09ca4067e52b2b35b9` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `CheckUse.compile` | 16 cited, 17 cited | none | `129fa083f3109df9fdc5fc33122cd11b96d644fbe7804be6977d4b5f78b0205a` | `73f9e7d01afad27fb4a2d6cb44cebb5c492cea6c3da9051a0dd9f8e4cd315214` (8) |
| `CheckUse.remat` | 16 cited, 17 cited | none | `129fa083f3109df9fdc5fc33122cd11b96d644fbe7804be6977d4b5f78b0205a` | `73f9e7d01afad27fb4a2d6cb44cebb5c492cea6c3da9051a0dd9f8e4cd315214` (8) |
| `lenCheck` | 16 cited, 17 cited | propext | `9d5978ad747a3f34df4dde92b33a3d7bc19fb106c423fbb933819f728ab43e3a` | `73f9e7d01afad27fb4a2d6cb44cebb5c492cea6c3da9051a0dd9f8e4cd315214` (8) |
| `remat_lenCheck_privRefines_not_robustRefines` | 17 result | Quot.sound, propext | `f283cfe025ec3931757b51a62d56490d4a03c1f400785577ada12f027c8761ab` | `2ddb2b73ff869966c97c860dd4fc0d1adab6bb9c2d76adaad30a6f2793f93939` (32) |
| `remat_pure_robustRefines_iff` | 17 result | Quot.sound, propext | `c0e6fc8220371d36d01b0a1afcffed4d093aaa6af402ff577b0d9d6eb46b91a1` | `532028f8f1bb303470c207a49ca51812ec25e55e49469a157a81da2ab8948e0e` (26) |
| `remat_pure_robustRefines_const_use` | 17 nonvacuity, 17 cited | Quot.sound, propext | `55d634daab376a0a1b8579f5114487c6157693ee410c73d8e8b5b147e25ee230` | `532028f8f1bb303470c207a49ca51812ec25e55e49469a157a81da2ab8948e0e` (26) |
| `remat_lenCheck_cap255_robustRefines` | 17 ce:hcap, 17 cited | Quot.sound, propext | `116b07b8dcd142ffe53ba806f56c949c7f101f25bec8a87a313c2995c2d469f6` | `6041ca322a0f404846128ef4510f682db33020661c95e581e3f4a4527b62b0e9` (28) |
| `CheckUse.pure` | 17 cited | none | `cdee41da948f4be3136fdefe33e9508ad0e28eea9c55536a7aae8c8e526a8369` | `73f9e7d01afad27fb4a2d6cb44cebb5c492cea6c3da9051a0dd9f8e4cd315214` (8) |
| `obsRefines_iff_eq` | 18 result | Quot.sound, propext | `1eda218d501f95624930dcd30a13b5bf0c641b669fb40d41fd12cd38c910564a` | `23b9718a3435ce4a9b302dc9b9820d2522a7ab71ade8f5c9a9c94bfe1b901c6c` (20) |
| `rsafe_of_robustRefines` | 18 result | none | `ed2841b12f430532fdc21dd97d4e444572f5e027721c0e1c1bb444ff04681c76` | `b70bdc96401ad6290d467ac3989ec55125b30bd8ffe6652c21e929ae4cedcc63` (18) |
| `rvalid_of_robustRefines` | 18 result | none | `a5f55625d230481ba25851315bd2649d608be486b307ecd5a09f44c2f792eb98` | `73d4d873c9b9753622bffbb10e7a568cac727f0149535047ee48819133737fbd` (18) |
| `robustRefines_hqp_counterexample` | 18 ce:hqp, 18 cited | Quot.sound, propext | `656f6de03026a76f87521d5e4dd636a5b5500fc3d211a55c5196e35c8ac5a567` | `7fe07ea2082d1cfc2596f560c1bef9e9597245d094e2dfb77b1a84842769545b` (37) |
| `robustRefines_source_counterexample` | 18 ce:hp, 18 cited | Quot.sound, propext | `5a95058fe58974f9e4e99e36d2f1d1bb1da8851e144a373e994e11fc23bdac05` | `2ce60c969ad6394b2c8bf7aeabd5e17389254fe9270653e3fa53a5949dd078da` (33) |
| `Event` | 18 cited, 20 cited | none | `f6f89b1e202b0402af79d58f047c64c0c027411fd8a20194e7a83a70d5bb9d4f` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `ObsRefines` | 18 cited, 20 cited | none | `419b1b1973d68eab867bff623d50e303ae52686375d7a5348897df918803f76a` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `Prog.obs` | 18 cited, 20 cited | none | `bf325d9d3b9f1f37941200d6b20d2fd7224fa0eabde558eb9bbc6258639d6cd0` | `57b4ee1643ae0cb82e680dfd6976883b1c92860a202cf733f5d0c5a3d8afa454` (10) |
| `Prog.obsFrom` | 18 cited, 20 cited | none | `5f076894bc0bcf9485e05fd04261bef258bfba8ea31d79b2c9af5b10e064b9fb` | `57b4ee1643ae0cb82e680dfd6976883b1c92860a202cf733f5d0c5a3d8afa454` (10) |
| `viewProg_implements` | 19 result | propext | `a31989dc3d1e6535370f55b234f27e4432c088fffb664bffb9364470c22b22b5` | `907c30e4d7dcb727ee29078452fb62ff66e7914d6214b180a008f60e5500a337` (23) |
| `viewProg_viewOK_of_noForeignWrites` | 19 result | Quot.sound, propext | `dfdc15cc7b64056e045bdcadac2899b083e5a1da666ce67670d08cf07aa6a70a` | `e94415b80468dfcef31e4a1268639de698b533148d7a2e0a5edd3c4020ba43d6` (25) |
| `viewProg_nonvacuous` | 19 nonvacuity, 19 cited | propext | `8b815a8e9d711984968f37def121d2a7c74f05198f9fa389fe6268474dcfd06d` | `a4785e5ae430e32dfaa6e621759dfe480bcdb6b9101850091b02a633d0f14132` (25) |
| `viewProg_tagFlip_invalid` | 19 ce:hno, 19 cited | Quot.sound, propext | `8537d3a9e030de115e9600c1c2d94fea10b59ad4ed749148d196bde41f1d0077` | `35abac6f1ce7cac32ed184802e055640e8c9d5c3a782fecf9cde9bf85ef99ebe` (28) |
| `ViewOK` | 19 cited, 20 cited | none | `20d1065fcd41052593cfe6207e911fa570bea3da7d4d6fda01142fcb15e06cb5` | `82804c9e2d239f4b0f59dcc2ba5c5e14f957d39d467a1e9f59402fec45a23168` (1) |
| `validSwitchAdv` | 19 cited | propext | `e0b61b0569969deac7d24055b1b1e3d562584be2014e485663db7ad8f6a57fda` | `b29ed9a094bb433c9afd93d55dcbdd811fb221101f10980e5f9a592b517d3698` (3) |
| `viewFlipAdv` | 19 cited | propext | `e0b61b0569969deac7d24055b1b1e3d562584be2014e485663db7ad8f6a57fda` | `b29ed9a094bb433c9afd93d55dcbdd811fb221101f10980e5f9a592b517d3698` (3) |
| `viewProg` | 19 cited, 20 cited | propext | `fed0970a2b783d8c1725b3add4cbafa56bf018065ad6ec8d5aae90f7849d7215` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `viewProg_validSwitch_breaks_viewOK` | 19 cited | propext | `30003a3dbdabdc46323689dd798b55d3f530498a87222086cefadcaf4b8c5354` | `ef084307870e5f62caf583cce87c89657127ca9603221603c86c84e8b0475d47` (28) |
| `viewProg_zero_rsafe` | 19 cited | propext | `e0d30c3ca3b353d7174355e5c2d6f054ec1142b297bfb58bd193486ac0ab1a4f` | `07e323bcbea42b5d7f758c9edd6477ced6bb1d669b128c3951e0d655c8ffa629` (26) |
| `viewUses` | 19 cited, 20 cited | propext | `5da63211be76ed6b0c7ad13384d4f421ea7c69de3c2232f329fc0a6c78f6c494` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `copyOutProg_ownedProg_access_counts` | 20 result | Quot.sound, propext | `1f5797c37743d71baee4f0abaf7d9a6934eb79096fff740a96d482dc39e0e912` | `08d36ceadce4561c2a550d722c032312dc9452ef3207980e1da7c352c3b24cdb` (31) |
| `copyOutProg_singleRead_implements_rvalid_rsafe_viewOK` | 20 result | Quot.sound, propext | `25d5fbc0f30c17955e1bb1d11a07a4aae2f6a9eeabb6bf39fbb217bea78f338b` | `c29e81dd151ec3794bff2c09681b090b29e387aa55c31bcae3128551ce78af6f` (44) |
| `copyOutProg_torn_valid_not_rstate` | 20 result | Quot.sound, propext | `fee2eed8ba6bc807bb63d1b5c018086f0eff17fe528c941977f8299b8ae3d04b` | `38733e17d93ecea760c93ff5c0f2f77619be34e5a6a742046a067cf8045f647e` (32) |
| `ownedProg_exec_eq_copyOutProg_exec` | 20 result | Quot.sound, propext | `6874ee7be5877348f89ff32d503626a49349572f5eb4a30100c7f0bd39c3dd9c` | `ad2c05bfb6c9e9bb93dba6cfe56db3d8810df6fc6806ebf40d5d11001d044819` (28) |
| `ownedProg_ne_copyOutProg` | 20 result | Quot.sound, propext | `1df5f038fff661db874d62abb50fc7f071a7ed3e8fedfdfa391653c1c54eccdc` | `987aa9b91cd69820d1644d886bab89c66ef3149be408724d95fbfff6f537c232` (32) |
| `ownedProg_singleRead_implements_rvalid_rsafe_viewOK` | 20 result | Quot.sound, propext | `3bf71c9480e30c959d6b8d265cab5b6c4beeaae347e5d2886e767104af58041a` | `78b9e82ea5e52607b37b28708b7a8e2102bd49b43a62906c0f9c43265aa65fa2` (38) |
| `ownedProg_torn_valid_not_rstate` | 20 result | Quot.sound, propext | `6130029225d1091220105ecb7ae0c0e57f2651a99695a124524debc3e0f1e51a` | `21f18905d47a61c8a49f0429c4badffd460297d918eb665221dd4382199c2885` (27) |
| `copyOutProg_example` | 20 nonvacuity, 20 cited | propext | `be92c794a10a4dbde720f8f2055a436fca4da314cf1fa3640631e3f77da0a70c` | `caedf3f5afa76c1f28a88465579e50225b1ac553bddbba5781e3a61f9bfb0325` (29) |
| `ownedProg_examples` | 20 nonvacuity, 20 cited | Quot.sound, propext | `bd736b437b822f27ef346767e1a29e588f73dac5b77c557b83f8993f54977cce` | `0f74f4c3b8b034335bfc3f5f90ede03d8a1778e5ab53d6629d9acf463705231d` (28) |
| `copyOutProg` | 20 cited | propext | `fed0970a2b783d8c1725b3add4cbafa56bf018065ad6ec8d5aae90f7849d7215` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `copyTornAdv` | 20 cited | propext | `e0b61b0569969deac7d24055b1b1e3d562584be2014e485663db7ad8f6a57fda` | `b29ed9a094bb433c9afd93d55dcbdd811fb221101f10980e5f9a592b517d3698` (3) |
| `ownedProg` | 20 cited | propext | `fed0970a2b783d8c1725b3add4cbafa56bf018065ad6ec8d5aae90f7849d7215` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `NoByteDeterminesOutput` | pkg | none | `acdfb7d351a565e49979eff151f493dc99105b9a121d075762c87cb68778ae21` | `d71ff460cc7d8cf6fb0122287406af5a5c7336cd3810e5bee8c21b9132745f69` (2) |
| `Prog.addrAt` | pkg | none | `1b51bfbabd65fa4571660276b26b9d32ba99ba0baafaf0fe5b911fb1d7bfc59b` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `Prog.execFrom_eq_eval_of_agree` | pkg | Quot.sound, propext | `9dc1608ead862d4be50ebc9206469ecf695bdaef6fe7ccc0b756a76604b50c59` | `874fc49dd580537e036fcb38cb09024cdb1776e001c5a6efd8ad2c19b5c5ede3` (24) |
| `Prog.obs_snd` | pkg | none | `2cf0983a8bc84532f26d5c61bac4f61719d7b77895d4ffbae8ce9373842557ed` | `d7a7027c0216adab53f18808a87470cca98701f9ad172c87147491ba91b2a392` (22) |
| `andSpec_examples` | pkg | propext | `eb68f4b5fd19da827975344195a7628ac189643368b47baebd30f7460b952220` | `224d5eb6b7b424e6a47f0da6cf120af154aa6817271a2a350edcff15271e4611` (6) |
| `assemble_example` | pkg | propext | `a8298e47b338a04c3602a5bd8b187e0a8ae616f5d6b1b6ef5a020cc73f319037` | `ffd2fdb7ef199fb6c79087e9d1ba9e6a3431f4b5a9198aad87c865699d1fafa2` (17) |
| `boolParse_examples` | pkg | propext | `6acf4ae38d8c43d16755807442f9657560201c0550b6d4d60aa1d26a944ae1a4` | `256f62f641e1f8aebe959eaedb427e52c4ad58c65c1ed9a7b3395d084059b3d7` (4) |
| `ckParse_examples` | pkg | propext | `354887dc07fc54520e0c4494273fcb1924369955f860fd30983463a46981c76e` | `6e64dc8029419023e8994c1c1b00b165d88bb202cb3e73bb6921e4d518c435f6` (5) |
| `copyInBounds_examples` | pkg | propext | `bf587fb1d2b80a7b75e12609fb61a9d0fbe379a90b8e4a9bdfc95ec60000105d` | `b5fcce97762ca5cbecb4efcaf13e6fafb022c5759e8d826b74a56248c5d3b1e6` (2) |
| `dataDepProg_examples` | pkg | propext | `c1d2f2291084202a77b0a88c360befdbba6f4f6b36fb422b79878e692d7e7b75` | `f4b7db721e4559f40533d9a858e7d0e726afb9ae98bb00080f33db304a8f8fdd` (17) |
| `eval_example` | pkg | propext | `14c547d8cc313fc9532efa7de0435e92ce936494d374c577fb14104ecc0493d9` | `7ba0426d8bd8ee88a33780dff9d19c246cfe917362ee1ee9ed3d77823d24df4b` (16) |
| `exec_example` | pkg | propext | `71b9a16f3a91cd6e108e0beb83dbfb0e05f245933012c3dd20d106b05fa208d4` | `46076052ebb2c144bb7c99f37d5e9898a39bc6a5e51a43dc7281e442d7f2c1e4` (20) |
| `exec_ne_eval_example` | pkg | propext | `1415aa85b7ec86825901dd15c1234c5e4fc7d2ba300c89190cf49d1028fb5c34` | `8a2fd37d8d324e42656e1a7d7ac9331fc89ea3e9c3dc54b953bb31b42d46936e` (23) |
| `hasUndeterminedState_examples` | pkg | Quot.sound, propext | `fe5f9f28cd390d96f6c2cb2d01256a98c622373093d3bec82ba35ed2b2cd4d25` | `2b5468ebcec3d7cd8bf0450daf6d24c65dd68dd28760a1212ae9aa84c125cba6` (12) |
| `hasUndeterminedState_of_pos_of_noByteDeterminesOutput` | pkg | propext | `4469f3c62395d321da2a6fe5660ba752f8c2ddaa206ed1886ec1ec14513b6fb7` | `38417069609bf01c6236cd9b923a5e9a053a10e608683f5db982d0309d12169b` (4) |
| `implements_examples` | pkg | propext | `d28d52494d84b3d335eab8866d8671a6f1420b623427f2739f9aa3c6330bc442` | `a2c9252e2d70cdf192a46c175a7f0bc00eeffbb79f69471e22441858684fe3c9` (27) |
| `incr` | pkg | propext | `9153483aab3c417f215478a80d68aa841193219d6d7f8f8c4ae15d184638dfd0` | `82804c9e2d239f4b0f59dcc2ba5c5e14f957d39d467a1e9f59402fec45a23168` (1) |
| `incrementBoundedWriter_examples` | pkg | Classical.choice, Quot.sound, propext | `94d51a586ea2c39033d1eedb06bebda4bc7d6b5ea586a3f22eda9d1c230ecaaa` | `122b0f9f22afe2030d51e54b4e52b823633df5a15f489509d1066781de520cbf` (14) |
| `lpParse_examples` | pkg | propext | `5ed8c2e52130ed6d70fa6ea240f0ee91d219ab1b6de3d261745d10f8db34db2e` | `7cee74406b0044d7ebc0d354d662327d0071b86b0d2eb1c6fdcfeb532319b2ab` (4) |
| `noByteDeterminesOutput_examples` | pkg | Quot.sound, propext | `c15ccf3ec909065cc392d7f18caa69077d938c9f7d7da52e828f242bc48219c9` | `14b0055d3c3a250e7a6b38ce6e84b3024ae79fdd71a9f695b6400f9b89817f6c` (7) |
| `noSnap_examples` | pkg | propext | `5c5246cae0756c8e2c68b86cfb05ff7a14a9745cc0ff8afe7003f4715bb412ef` | `98b87fa0b650419a7b084422f8c4141bb6252dd3b1b514e601b08eb2bff7b4e3` (19) |
| `obsRefines_examples` | pkg | Quot.sound, propext | `83efd23e268f1870ddb5a9f53361be18c7d8133ea5c6d9e8742da2ab2924246e` | `e4fafc6992eff58e5b6bb46389cfcda61d73318fc58f058cea4d845b06c3f6d5` (33) |
| `obs_example` | pkg | propext | `b978a40ceb9a8baede50d483339a8ff06e367e348575793a21039713e145c0aa` | `4e40fc3f218b5b6c102f7dc405f931d2da991db133439c2dfa9698a8b1e0e4e6` (23) |
| `oneStepVersionWriter_examples` | pkg | propext | `62114d7bc99f5317b614319a1ba5f7b32e1a91bd114bf1e49bcf0025254cb316` | `d0b06644d917717041fcef9089defe9d3871b740f01f90441cce450107ccecdb` (10) |
| `privRefines_examples` | pkg | propext | `bd4da9fb0f50e8e519e1cc721b398838fbd098cb6b124b83efeb9034fa4e9bca` | `7898d962fc3aad504b7fbe6740206ac771fc8c7bfd22590eab4ca085532bca37` (28) |
| `readTwice` | pkg | propext | `93df50211a44cc81e7eba39194654e5a4909730949ed00afff28ad0e62b3b791` | `b5fc8e4d5515a862408c69587615d1e39ff803fe8ab5f986eacf9df27f62c458` (6) |
| `robustRefines_examples` | pkg | Quot.sound, propext | `e7ef58084c7701318479826b336cbb3ba62bafc1e1d15143f6893c7251be2c05` | `3e56d15abee79741dbe486b2888e6dc1bdaba13d487f68057389c094dd7c0bd9` (35) |
| `rsafe_examples` | pkg | Quot.sound, propext | `d104b8de19b0469d31d2e8a218a4400c33982392962994061c7c7d1d6b4fc42c` | `1855442d91e8d8f4e002c868b676b7e0f90da267906cc1c2b8311bbb5351fb38` (32) |
| `rstateUnder_examples` | pkg | Classical.choice, Quot.sound, propext | `88ac47b425e631a314ccc6a1a6a6b7c294375944bb28fda7598d9a057232026f` | `db996586cf559d54a280f10c9440db8a185a8c490144e62fb9c83ed9e5c839c9` (24) |
| `rstateUnder_true_iff` | pkg | none | `9fa54f159d00fadcd2363af40c4d2480a33098697cee4bb5a9ac8ba6cbdf69d7` | `331c036e918aac778680e33a074c38b6643bf855b5c0a9d321d097dead8deba6` (18) |
| `rstate_examples` | pkg | Quot.sound, propext | `40decb06b8ede99b546d68341b1da9bf69dbb98f2c0c47379c900cea8490c20a` | `3c3267b68e4a53e731f2f0d5a8c93805d40e80dcc504ffd709d95ec859baf426` (26) |
| `seqSpec_not_noByteDeterminesOutput` | pkg | propext | `fcd6e720dd155004ea664930a580eee83e782fc8f5c63f5a141486ff74c7ae7d` | `830f87cfc0836d9f7f14c6e4d9109822c610d6ea3a1c2e3232d38512cda27b32` (5) |
| `sevenNine` | pkg | propext | `e2b018de8c0fef8716cd8b0ebb490cba74f0115d7e982ed9fd0e24df928a2dd6` | `b29ed9a094bb433c9afd93d55dcbdd811fb221101f10980e5f9a592b517d3698` (3) |
| `singleRead_examples` | pkg | propext | `11602f313b1c73b48ef037eb4058c4d7ab149b1ac7f8fc4ed0ea88a95786a5ee` | `df8356bd3227a938e8c7d3264210ae0a00635bdad70b9977058f50a1e63f3b5f` (28) |
| `singleRead_read_then_snap_rejected` | pkg | propext | `df54e784a6b4a4ec667d29e5d1fd36773b6228ea71dcb53e9e410d240f2df817` | `ef85938be8129ca7e05c38413382cd984265f9422c82a70826a4d720c3d7329f` (15) |
| `twoStepVersionWriter_examples` | pkg | Classical.choice, Quot.sound, propext | `06fd62731d352a3602fab24e53dd1786407ee55e8999faeafbbe18b8c8dad78c` | `cc6174de42fd690bdb9630c602299d83686661b27b4a8ba42c3f3b7d66196f5a` (10) |
| `validBoolOut_examples` | pkg | Quot.sound, propext | `ca7287edf1fa87cf11be16f5233428e1368b3c469513793a525b04a35d79e437` | `75f3df2d8c57b0a9fadea284309c5bce84349f69e10e6a72482d5ba010a8d223` (3) |
| `validE_examples` | pkg | propext | `8197bf17357c045676d76d9dac714617c0c38211f34c757adc48c6410e81a5d0` | `df142c2fa334ac5f03c1dbb3a9388df802decdcff08abcbc3de97457ffe63ca0` (2) |
| `versionPath_examples` | pkg | Classical.choice, Quot.sound, propext | `c9775283d2f0edb43f03badf38baf98ef1d6ddcc0699e7f0b77908e812ff5eef` | `56b271f5b5746499e0119fe57874c429ad50a3a10f05ba00736f63c276a94e73` (10) |
| `versionStep_examples` | pkg | propext | `cef136c6edd48546775dbb0d3002089d1bd09b246063bf95ae5816af9632c01c` | `a631362fa0d954f2717a116087cc9b5492799a44c96e19da601908a46aded1a1` (6) |
| `viewOK_examples` | pkg | propext | `393f942cb112a6b6287028f8a48969d5b4897411f6bf9521b65dfd37255734f5` | `1b61220c3870e59d428c87bfd1afed5faacb344870219288071c676094786d61` (4) |
| `viewProg_example` | pkg | propext | `96c3b16f17ac5bdc89e481a320551c95a09918c6412c199caaf50a2c97904e6d` | `9e0bdf4185f66cabf3cfbc4c8a6fa519be9a162ed423e7eddc5d3e2498c0b213` (22) |
| `viewSpec_examples` | pkg | propext | `c380103895516a9ae30cf2541085392436ced496f58462cd9d80f8bc5392121f` | `213b59ef197faf4df2811ba348f7670f6f1b52c9d928277bbac59eb91e7441f8` (7) |

## Revalidation

Requirements: `elan` (the Lean toolchain manager, so that `lake` uses the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. The Lean project has no dependencies (no Mathlib, no `[[require]]`).

Primary check, run from the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` never modifies the package: it copies `lean/` to a temporary directory and there (1) runs `lake build`; (2) scans every Lean source of the package for `sorry`, `admit`, `native_decide` and `axiom` declarations; (3) runs a generated Lean program that calls `Lean.collectAxioms` on every declaration of the library `DoubleFetch` and fails if any axiom other than `propext`, `Classical.choice`, `Quot.sound` occurs; and (4) for every Lean name referenced by `results.json` or recorded in `audit/statements.json`, recomputes `statement_sha256`, `closure_sha256` and `closure_size` as described under Evidence ("What is hashed") and compares them with the recorded values. It prints `REVALIDATED` and exits with status 0 when every check passes, and with a non-zero status otherwise.

Manual build and axiom spot check, run from the package directory (the file `lean/AxiomSpotCheck.lean` is not part of the library and contains one `#print axioms` command for the first theorem of each result):

```sh
cd lean
lake build
lake env lean AxiomSpotCheck.lean
```

Each `#print axioms` line must report at most `propext`, `Classical.choice` and `Quot.sound` (or no axioms at all).

A passing run establishes that the recorded statements still build and kernel-check with the recorded axioms under the pinned toolchain; it re-establishes nothing about real systems. Under a different toolchain the statement hashes may change even when the mathematics does not (they hash Lean's `repr` of terms); in that case compare the statements in `lean/DoubleFetch/` with the ones quoted under Findings by reading them. The modeling-bridge claims and the quoted external sources are not revalidated by any command: to recheck a quotation, re-fetch the source at the URL, tag, commit or line range listed under Evidence ("Primary sources") and compare the quoted sentences.
