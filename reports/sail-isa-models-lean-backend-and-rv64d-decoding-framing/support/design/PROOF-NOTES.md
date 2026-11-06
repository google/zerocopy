# Actual generated ADD draft

`Proof.lean` is a concrete source-derived draft, NOT a checked theorem result. No Lean invocation ran here. It imports the complete `LeanRV64D` root and real `Sail.ArchSemSequential`, with no manual reduced model copies. Parent's verified generated-project identity/generation-census binds the generated subject; the assigned revisions and prior source manifest bind generator/model/support.

Actual pointers under `work/execution/sail-runtime/generated-project`:

- `LeanRV64D/InstsEnd.lean:69362–69391`: execute_RTYPE ADD reads rs1 before rs2 and then wX_bits; :73740–73752 top-level execute dispatches product-valued RTYPE.
- `LeanRV64D/Defs.lean:38`: Regidx5-bit wrapper; :772 RTYPE product; :1801ff actual result is Retire_Success Unit; :2285–2287 register dependent types are BitVec64; :2420 SailM aliases PreSailM exception.
- `LeanRV64D/Regs.lean:646–735`: callback, rX/wX and bit-index wrappers; actual write callback computes a monadic register name.
- `LeanRV64D/PlatformConfig.lean:907–1012`: encdec_reg_forwards and name mapping; `Prelude.lean:270` fixed false use_abi_names; :349 to_bits; `Callbacks.lean:251` actual callback returns Unit; `RegType.lean:236–240` conversions identity; `InstsBegin.lean:235` RETIRE_SUCCESS is Retire_Success(). All callback computation on fixed rd3 is closed and should definitionally reduce to pure().
- Real support `Sail/ArchSem.lean:131–150` FreeM constructors/bind/liftM; :282–287 actual register effects.
- Real support `Sail/ArchSemSequential.lean:17–25` full state; :51–58 register interpreter; :83–90 interpreter.

The first theorem states the precise free-effect tree and uses rfl: two register reads, one x3 write, success. This both binds the top-level generated executor and excludes ignored side effects or choices. It is an equality proved about the real generated program, not a replacement transition.

The second theorem interprets that exact tree and uses the two register-presence assumptions; final entire state is old s with only regs.insert x3(a+b). It leaves every other generated register, memory, tags, cycle count and output unchanged. The final projection theorem explicitly states PC preservation. No PC+4 claim is made.

Expected remaining ordinary elaboration uncertainties: definitional reduction cost of top-level execute and generated callback; inferred effect constructor typing in the free tree; whether existing Std.ExtDHashMap simp lemmas close the dependent get?-insert frame projection. These are not observed errors. No mathematical premise beyond x1/x2 presence appears necessary from actual source. If frame simplification needs an explicitly named Std lemma, inspect official Std source rather than changing the main assertion. The universal full-state theorem remains the principal acceptance statement.

After parent's serial import build completes, use its verified official absolute Lean binary and actual owned output directories. Proposed check shape (not executed):

```sh
LEAN_PATH="$OWNED_SUPPORT_OLEANS:$OWNED_MODEL_OLEANS" \
  "$OFFICIAL_LEAN/bin/lean" -j1 --tstack=400000 \
  -R "$OWNED_PROOF_ROOT" "$OWNED_PROOF_ROOT/Proof.lean"
```

Copy this exact draft into a fresh parent-owned proof root; preserve original draft, copied hash, command, separate stdout/stderr, exit/resource observations. Explicitly allow only already identified imported artifacts. #print statements emit the exact main theorem and free tree, while #print axioms separately audits all four theorems. Require no sorryAx, platform/FP/random/reservation/desired-result axioms; report any core logical axioms exactly. Native execution/evaluation is not requested. Parent still owns negative controls and final report updates.

A tactic/elaboration failure is a failed draft, not a proof or evidence that the theorem is false. Unexpected assertion/invariant requires stop and diagnosis before retry/repair under the existing rule. No such assertion occurred here.
