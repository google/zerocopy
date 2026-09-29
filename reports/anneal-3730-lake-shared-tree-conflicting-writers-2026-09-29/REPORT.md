# Two conflicting Lake writers in one writable package tree

## Result

At pinned Lake/Lean 4.30.0-rc2, two Lake processes entered real Lean `run_cmd` gates while building the same `Dep.lean` path and `.lake` output tree. Writer A had read a source definition `depValue := 7`; the file was then changed to `depValue := 9` before writer B entered. The harness killed one writer at the gate and released the other. The two reverse schedules produced different intermediate states:

| Killed writer | Surviving build | Immediate `lake --no-build build Dep` | Fresh direct Lean before retry | Ordinary retry and fresh Lean afterward |
| --- | --- | --- | --- | --- |
| A (old 7) | B exited 0 | Exit 0, up to date | 9 accepted; 7 rejected | 9 accepted; 7 rejected |
| B (new 9) | A exited 0 | Exit 3, out of date | Old 7 accepted; current 9 rejected | 9 accepted; 7 rejected |

The kill-B schedule is a concrete warning against treating a surviving writer's exit 0 as current-source verification. Lake's subsequent no-build check did reject that state as out of date; the ordinary retry repaired it. The experiment does not show a silent Lake freshness failure in the tested schedule.

## Method and evidence

`support/probe.py` used one private package with no registry downloads or cache sharing. Each writer had a distinct marker and release file. A source write occurred after A's gate marker and before B's launch; both markers existed before either process group was killed or released. At most two Lake processes and their Lean children ran concurrently. The highest sampled summed tree RSS was 3,643,280 KiB, under the 4,400,000 KiB guard; this sum can double-count shared memory and miss between-sample peaks. The script also required more than 10 GiB free disk and bounded each wait/command. It killed only its own process groups.

`support/results.json` and `support/results-kill-B.json` retain event order, CLI arguments, exits, streams, binary and source hashes, sampled process trees, and before/after package inventories. `support/work` and `support/work-kill-B` retain both package trees, the generated source, OLean/trace/setup artifacts, proof controls and gate markers. The Lean proof control used a fresh direct process for each claim and looked up the local `.lake/build/lib/lean` output. It checks only this small module; it is not an Anneal generation or a general Lake locking guarantee.

This extends the earlier shared writable producer report, which saw a compiled-configuration race and one early kill without conflicting simultaneous definitions. It closes one bounded I151/F12 conflict-and-crash cell. It does not cover interruption during the artifact or trace write syscall, more than two writers, power loss, native filesystems beyond host APFS, or a positive protocol for shared package ownership.

## Recheck

Run `python3 support/check.py` to validate the saved bytes and outcomes offline. To reacquire, run `python3 support/probe.py`, then `PROBE_KILL=B python3 support/probe.py`, then the checker. Each run clears only its matching `support/work` directory. The exact local Lake and Lean binary hashes are in the result files; changes in revision require a new subject comparison.
