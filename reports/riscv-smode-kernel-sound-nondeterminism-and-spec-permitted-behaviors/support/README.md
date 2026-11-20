# Probe support material

Two standalone Lean 4 files. They use only the core prelude (no Lake project, no imports, no Mathlib), and every
theorem is proved by `decide`.

| File | What it checks | Theorems |
| --- | --- | --- |
| `PerLevelStaleTranslation.lean` | A 2-level page-table history. Caching each level's step-2 PTE read separately (the priv-spec algorithm reading) admits a translation that no single memory snapshot ever maps. The "valid at some time since the last SFENCE.VMA" reading excludes it. Adding an `sfence.vma rs1=x0` before the old table frame is reused removes the difference. | `validAtSomeTime_eq`, `perLevel_admits_never_valid`, `fenced_no_gap` |
| `LrScContextSwitch.lean` | One hart. Thread A runs `lr.w`, the kernel switches to thread B, B makes a same-hart store, the kernel switches back, and A runs `sc.w`. Without a dummy SC, the spec permits an implementation choice under which A's SC may succeed, losing B's update. With a dummy SC on each switch, no choice permits success. A QEMU-like choice (clear the reservation on every trap and xRET) hides the bug. | `lost_update_permitted`, `dummy_sc_sound`, `qemu_like_masks_bug` |

Run:

```console
LEAN=/path/to/lean ./run_probes.sh
```

Observed on 2026-11-20 with `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit
5045d0056413266e57c625dcd7c365b10e377c52, Release)`. The script exited 0 and printed `probe_output.txt`. Each theorem
reports "does not depend on any axioms".

The probes are counterfactual formulations of spec clauses. They are not models of any upstream implementation, and
a passing run establishes only the stated finite facts.
