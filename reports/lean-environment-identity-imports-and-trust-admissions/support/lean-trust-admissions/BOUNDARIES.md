# Boundaries

- No fresh Lean elaboration, compilation, `#print axioms`, native-evaluation, or kernel experiment was run.
- The package describes exactly Lean `v4.30.0-rc2`; adjacent-version continuity is not assumed.
- The package characterizes kernel behavior from source; it does not prove the Lean kernel correct.
- A clean axiom dependency set does not establish Charon/Aeneas/Anneal source-model adequacy or correctness of user specifications.
- A clean axiom dependency set does not establish correctness of compiled executable behavior. Native-evaluation proof mechanisms are an explicit compiled-execution trust path.
- The package does not inventory every command that can introduce an axiom or every tactic that can use native computation.
- It does not prescribe which axioms Anneal should permit. That belongs in Anneal's result/TCB policy.
- Lean `unsafe` is not Rust `unsafe`; the guarantees and mechanisms differ.
- `noncomputable` is characterized only at the trust-boundary level, not as a complete compiler-behavior inventory.
- `debug.skipKernelTC` is included because it directly bypasses the claimed kernel-check boundary; other debug/compiler options are not exhaustively cataloged.
- The source account of `@[implemented_by]` establishes that equivalence is unchecked; it does not imply that every use is incorrect.
