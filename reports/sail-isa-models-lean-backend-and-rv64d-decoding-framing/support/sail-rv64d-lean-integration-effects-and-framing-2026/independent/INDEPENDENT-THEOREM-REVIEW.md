# Independent actual-generated ADD theorem review and native replay

Result: **the exact Proof-v6 file independently checks with official Lean4.29.0
at trust level zero (`-t0`)**. Its fresh Proof.olean hash exactly matches the
author's artifact. The four actual-execute/effect/full-state/frame claims are
appropriately scoped and their source proof follows the generated operations.
All four printed axiom closures contain the same78 names, with no sorryAx.
This is not an empty closure or a byte-fetch/ABI theorem.

The separately authorized Controls-v3 check **failed** an ordinary elaboration
obligation. There is no accepted Controls.olean, and printed positive theorems
from inside that failed file are not an accepted control suite. No changed proof
or control was retried. The two native checks exhausted this grant.

## Inputs, independent identity gate and kernel-import boundary

The task reserved the existing Sail container
`0af066858d96349334304f51ea631ea4c2496694952ea17f7dca1b5e8ecf6715` and granted
writes only under its NEW
`/home/opam/anneal-sail-output/independent-proof` directory. No source, support,
model, tool, installed dependency or existing artifact was modified or cleaned.
The initial default-sandbox Docker socket access failed before any remote
process ran. The parent diagnosed it and explicitly authorized a
require_escalated retry; that succeeded. This was not an automatic approval-review
rejection. The failed host streams remain preserved separately.

The subsequent independent read-only identity gate checked successful
serial-build-integration/complete.json (status0,143 modules) and all143 result
records. Each status was0 and each existing .olean's actual size and SHA256
matched its original build receipt. The retained receipt is
`independent-identities-02.stdout`, including every artifact identity. It records
the prior model-build328.40535146801267s and peak3348632KiB as the original
producer's observation, not a new model build by this reviewer.

The executable identity was independently checked:

```text
/home/opam/anneal-sail-tools/lean-4.29.0-linux_aarch64/bin/lean
SHA256 e215cbe9eab0914b49761e9e486d388e2e701cf876d1079d1ba733c48edb2d7b
```

The original Proof.lean source hash was verified before copying its exact bytes
to the fresh independent directory. The explicit LEAN_PATH was only the fixed
143-module artifact directory plus that new proof directory. The fresh replay
uses -t0 and ordinary .olean output, not Lake, quick/admitted mode, native_decide,
a substitute executor, or a reused proof artifact. Official core/Std artifacts
remain part of the selected official Lean installation. Hash-checking143 files
does not itself prove a theorem: the separate successful native proof check is
the checker observation. This review did not rebuild all143 source modules.

The subject remains the full official-generated configured RV64D model with the
reviewed termination-ranking repair and three abstract external-hook support
declarations, plus the pinned lean-sail sequential interpreter. It must not be
described as untouched upstream source or a third Sail generation. Local
retained generated BaseInsts, InstsEnd, Regs and Defs and the selected
ArchSemSequential source were also independently hash-compared with the actual
successful integration build's source-plan hashes; every inspected match held.

## The theorem follows actual generated execution

`Functions.execute` in InstsEnd.lean:73740/73752 dispatches the selected
`RTYPE (rs2,rs1,rd,op)` to execute_RTYPE. For the theorem's AST the constructor
order is `(2,1,3,ADD)`, so the actual source operands are x1 then x2 and the
destination is x3. execute_RTYPE:69362–69366 reads rX_bits rs1, then rs2, adds
the64-bit values, writes through wX_bits, and returns RETIRE_SUCCESS. Regs.lean
defines rX_bits/wX_bits by extracting Regidx into the actual register helpers.
For these fixed nonzero indices they select x1/x2/x3. The generated write
callback terminates in the existing Callbacks.lean:251 pure Unit body; no new
callback implementation was introduced by this proof.

`execute_add_effects` states equality of the actual top-level execute computation
with exactly two register-read effects, one x3 write of `a+b`, and pure success.
Its proof is rfl; the independently accepted printed term is Eq.refl of the
actual execute expression. It therefore checks the whole selected computation's
definitional normal form, rather than assuming that a separate toy ADD transition
implements execute. The effect tree contains no memory effect, ignored event,
choice or error branch. This is particularly useful because the general
interpreter ignores some system effects: their absence here is established
before interpretation, not inferred from unchanged final state.

`execute_add_full_state` quantifies over arbitrary BitVec64 inputs and the entire
actual SequentialState. Its only state-domain premises require the two source
register lookups to return those inputs. ArchSemSequential's regRead raises
Unreachable for a missing register; h1 and h2 are therefore meaningful premises,
not silently assumed initialized total maps. Read effects leave the state
unchanged, so the same initial h2 is valid after the first read. The write
inserts x3 and does not require a prior x3 entry. BitVec64 addition denotes the
modulo2^64 result; the theorem does not return a carry bit.

The simp proof first rewrites by the checked effect equality, then unfolds the
actual FreeM/EStateM interpretation and uses h1/h2. Its accepted printed proof
performs those lookup rewrites followed by equality of the resulting state.
The exact result is success and `{s with regs := s.regs.insert x3 (a+b)}`.
Consequently memory, tags, cycleCount and sailOutput are preserved along with
all other state fields. This is whole-state equality, stronger than an isolated
result-register assertion. It still concerns this selected interpreter and AST
execution, not a physical machine or all possible external-hook executions.

`execute_add_register_frame` specializes that accepted full-state equality and
uses the real dependent-map insertion theorem with r≠x3; unrelated absent
register entries remain absent. Its equality handles errors by matching them
to none, but the full-state theorem has already established success under the
premises. `execute_add_pc_frame` is the PC specialization with constructor
distinctness discharged by decide. Thus PC and nextPC are framed; this is not
the PC+4 behavior of fetch/decode/step. No memory availability, privilege/CSR
setup, ABI stack/return, executable bytes or Rust caller relation is claimed.

## Actual assumption closure

`independent-proof-axioms.json` preserves all four exact printed lists. Each has
78 distinct names and the lists are equal. They include propext,
Classical.choice, Quot.sound and abstract platform/reservation/randomness,
event and floating-point constants. No sorryAx appears. The supported claim is
kernel acceptance relative to this recorded environment, not an axiom-free
proof or an audit that every imported assumption is a hardware fact.

These are syntactic whole-definition dependencies: the theorem TYPE mentions
the actual whole Functions.execute, so unused execute branches can contribute
abstract-hook names to collection even when the proved effect normal form
does not invoke those hooks. Keep both facts. Do not remove the actual execute
binding or hide the78-name list to manufacture a smaller closure. The three
reviewed added support declarations assert data/computation interfaces, not a
desired ADD theorem; their presence must nevertheless remain disclosed.

## Native commands and measured outcomes

Both native invocations used this exact prefix, with -R and -o paths beneath
the fresh independent-proof root:

```text
timeout --signal=TERM --kill-after=5 120
/home/opam/anneal-sail-tools/lean-4.29.0-linux_aarch64/bin/lean
-j1 -M4500 --tstack=400000 -t0
```

LEAN_PATH was exactly
`/home/opam/anneal-sail-output/serial-build-integration/olean:/home/opam/anneal-sail-output/independent-proof`;
LEAN_NUM_THREADS=1. Each complete argv, working directory, source/artifact/stream
hash, status and measured child usage is in its retained native JSON receipt.

| Check | Status | Wall seconds | Peak child RSS KiB | Accepted artifact |
|---|---:|---:|---:|---|
| Exact Proof-v6 as Proof.lean | 0 | 1.4954981859773397 | 1552348 | Proof.olean,297080 bytes |
| Exact Controls-v3 as Controls.lean | 1 | 1.7412980049848557 | 1547604 | none |

Proof source SHA256:
`f62057489d30152c39dcfab87c5b7ecbb43dd2e6bbe14d0368c4cbc832b6f2d4`.
Fresh independently emitted Proof.olean SHA256:
`a37ef2b0d8f2ed3613a85ae666e89771464e2453df0929f9f80fb44397faa3bf`;
this exactly matches the author's prior artifact. Native stderr was empty;
stdout includes harmless unused-simp-argument warnings, two printed theorem
terms/types and all four axiom lists. The retained exact Proof source contains
the statements of all four constants.

Controls source SHA256:
`54103c89a020f3c46fd4fe327250790ae3c4b8f87d727107cc151f7bde3098ec`.
Its only error is Controls.lean:159:2, the final decide in
sub_differs_from_add after dependent-map simplification:

```text
failed to synthesize
  Decidable (some 18446744073709551615 ≠ some 3)
```

This is an ordinary missing-decidability elaboration obligation for the
simplified observation expression. It is not a counterexample to the accepted
ADD theorem, a timeout, an OOM or a kernel panic. No Controls.olean was created.
The printed later positive controls/axiom lists do not make the failing file
accepted. No diagnostics rerun, source repair or third native check occurred;
the parent was notified with the exact error and determines any next action.

## Preserved review evidence

All host evidence is in this reviewer's scratch only: independent-Proof.lean,
independent-Controls.lean, independent-proof-native.json,
independent-controls-native.json, independent-proof.stdout,
independent-controls.stdout/stderr, independent-proof-axioms.json and both
identity-attempt streams. Native files, full streams, proof artifact and receipts
remain in the new independent-proof directory without cleanup. Source-level
review supports acceptance of the four main theorem statements within their
actual scope; the control-suite acceptance remains unresolved.
