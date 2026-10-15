# Source-derived semantic controls, uncompiled

`Controls.lean` imports unchanged Proof as a module. Parent therefore must compile its approved Proof.lean with `-o <owned proof artifacts>/Proof.olean` (or equivalent Lake module build) before checking Controls.lean with that directory added to LEAN_PATH. The earlier check-only command does not produce an importable Proof.olean. No compiler ran for this source-only task. Original Proof.lean remains unmodified.

Controls bind real Functions.execute and interpreter in every execution assertion. Auxiliary free-effect equalities are proved about the real executor by proposed rfl; they do not replace it. Fixtures use actual SequentialState and Std.ExtDHashMap insertion, with empty memory and unrelated registers absent. ADD wrap uses allones/1; SUB1/2 produces allones and a theorem states observed x3 ≠ some3; rd4 ADD1/2 preserves x3=0 and writes x4=3; missing x1 and missing x2 produce .error .Unreachable with unchanged full state. #print axioms audits every concrete acceptance witness. Ordinary decide is used only for closed BitVec numeral arithmetic; no native_decide or runtime evaluator is used.

The draft's outstanding uncertainty is the same as Proof: actual elaboration/definitional normalization and Std dependent-map simp closure have not run. These are draft risks, not measured failures. If general theorem checks but fixture simplification fails, inspect actual Std get?-insert/empty lemmas, keeping fixtures and assertions fixed. No desired-result assumption or axiom is permitted.

Later separate expected-rejection files should retain actual false counterclaims, not simply invoke a tactic expected to fail. For SUB, retain equality of actual observed x3 with some3 under fixture12; proved sub_differs_from_add refutes it. For wrong rd, retain observed pair=(some3,some0), refuted by rd4_observation and closed BitVec0≠3. For missing source, retain success/full-state claim, refuted by missing1_fixture/missing2_fixture and disjoint EStateM.Result constructors. Parent can prove rejection witnesses constructively and separately attempt false proof files; a false file's nonzero exit must be accompanied by matching semantic witness and diagnostics, not treated as sufficient evidence by itself.

Decoder follow-up is optional here. Actual generated `InstsEnd.lean:298` defines noncomputable encdec_backwards; the ADD branch at553–577 tests funct7=0/funct3=0/opcode0x33 and extracts rd11:7,rs119:15,rs224:20, then returns product-valued RTYPE. `DecodeExt.lean:234–235` ext_decode delegates directly to encdec_backwards. Thus target is the actual free-program equality

```
Functions.ext_decode (0x002081b3 : BitVec 32) =
  FreeM.pure (instruction.RTYPE
    (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 3, rop.ADD))
```

This is source-supported as a candidate, not a checked decoder theorem. A future bounded draft can try rfl reduction of the actual full decoder, preserving every preceding branch. If reduction is costly, prove exact closed branch conditions rather than replace the decoder. Do not add it as an untested mandatory theorem to the AST control file. Word-to-byte relation is little-endian b3 81 20 00; it still needs explicit byte observation/assembly mapping before claiming fetched execution. rd4 mutant is0x00208233, bytes33 82 20 00. No fetch/PC+4 theorem follows from any of these controls.
