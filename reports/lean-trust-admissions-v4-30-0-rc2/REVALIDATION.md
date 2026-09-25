# Revalidation

For a later Lean pin, resolve the exact commit behind the selected toolchain. Recheck `sorryAx`; declaration safety and kernel dependency checks; transitive axiom collection and `#print axioms`; the default and dispatch of `debug.skipKernelTC`; and the `implemented_by` / `csimp` / native-proof boundary.

On a capable execution surface, create a small module at that exact revision containing: an ordinary proof with no added axioms; a user axiom and dependent theorem; a theorem containing `sorry`; an unsafe axiom plus a safe declaration that attempts to reference it; a safe logical definition with a deliberately different `@[implemented_by]` implementation; and one `native_decide` proof.

Run Lean with default options and record diagnostics. Run `#print axioms` on each accepted theorem. Check that the ordinary proof has no new assumption, the user-axiom theorem reports that axiom, the `sorry` theorem reports `sorryAx`, the direct safe-to-unsafe dependency is rejected, and the native proof reports its generated assumption. Separately, enable `debug.skipKernelTC` only as a negative control and demonstrate that it bypasses a check performed by the default configuration.

Preserve the module, commands, exact revision, diagnostics, and axiom reports. These probes revalidate behavior for that revision; they do not prove the Lean implementation correct or determine which assumptions Anneal should accept.
