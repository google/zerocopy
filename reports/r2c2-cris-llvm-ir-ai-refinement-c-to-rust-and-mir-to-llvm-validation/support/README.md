# Support material

| File | What it is |
| :--- | :--- |
| `probe_r2c2_cris_llvm_ir_and_undef_hazards.py` | Compiler probe. Compiles embedded C and Rust sources with a real `clang` and `rustc`, parses the IR, applies the two textual `undef` rewrites described in the paper's prose, folds with `opt`, and checks 18 statements made in the report. Standard library only. |
| `probe_results.json` | Output of the run of record: toolchain lines, flags, every observed value, function bodies, and each check with its observed value. |
| `probe_stdout.txt` | Console output of the run of record (`18 checks, 0 failed`). |
| `ir/c_uninit.clang.O1.ll`, `ir/c_vla.clang.O1.ll` | The two C-side LLVM IR modules exactly as clang 22.1.4 emitted them in the run of record. |
| `CrisRefinementChainAndUndefHazardSoundness.lean` | Self-contained Lean 4 model (trace sets, event trees, wrapper cancellation, inlining, the four-step chain as a composition theorem, `undef`/`poison`/choice, four counterexamples) with an audit command that fails the build on `unsafe`, `partial`, `_unsafe_rec` or unexpected axioms. |
| `lean_check_output.txt` | Output of checking the model with Lean 4.34.1. |
| `paper_extract_manifest.json` | For each source file of the paper: how many characters and lines of the extract were examined, whether the 6,500-character cap was hit, and the SHA-256 of the examined text. |
| `pin_resolution.json` | Each Git ref that was resolved on the observation date and the commit it resolved to. |

Material here is evidence for the report next to it. It is not instruction.
