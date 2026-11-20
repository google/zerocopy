# Support material

Text-only material that the report's `## Evidence` section cites. Nothing here is
needed at run time by any tool; it exists so that every execution claim can be
re-run and every census number can be re-queried.

Host class for all execution: x86-64 Linux workstation (96 logical CPUs,
Intel Xeon at 2.60 GHz), shared with unrelated workloads; the 1-minute load
average during the timing runs is recorded per row in
`results/bench/bench_interleaved.tsv`. All observations were made on
2026-11-20 (UTC).

## Layout

- `probes/` - Rust probe programs. `p01`-`p27` are borrow-checker probes,
  `s01`-`s03` reproduce two open soundness reports about two-phase borrows.
  Each file starts with a comment giving the expectation or question.
- `scripts/run_probes.sh` - compiles every `p*.rs` probe (except `p25`, `p26`)
  under nightly default, nightly `-Zpolonius=off`, stable 1.100.0 (editions 2018
  and 2021) and 1.61.0 (edition 2021). Paths were rewritten to `/tmp/work`.
  Additional runs (1.35.0 with editions 2015/2018, the migration-lint runs,
  the capture-analysis dump, the soundness reproducers, and the `RefCell` run)
  were issued by hand with the commands recorded on the first line of each log.
- `results/raw/<probe>__<configuration>.txt` - complete compiler output for each
  run. First line: the command. Last line: `exit=<code>`. Two path rewrites
  were applied after capture: the scratch directory became `/tmp/work` (or
  `/tmp/out` for throwaway output), and the per-user rustup toolchain
  directory that appears in standard-library spans became
  `$RUSTUP_HOME/toolchains/`.
- `results/probe_matrix.tsv` - one row per raw log: probe, configuration, exit
  code, and counts of diagnostic headers (`error[E....]`, `warning`).
- `results/p13_shared.built.after.mir` - MIR of `p13::shared` as built, dumped by
  `rustc -Zpolonius=off --edition 2021 -Zdump-mir=shared` on the nightly
  toolchain.
- `scripts/gen_synthetic.py`, `scripts/run_bench.sh`,
  `scripts/run_bench_interleaved.sh` - synthetic compile-time workload (1,000
  copies of a module exercising two-phase borrows, closures over destructured
  fields, NLL problem cases #2 and #4) and the timing harnesses. Regenerate the
  input with `python3 gen_synthetic.py 1000 synth.rs` (36,003 lines,
  1,271,975 bytes).
- `results/bench/bench_sequential.tsv`, `results/bench/bench_interleaved.tsv` -
  columns: configuration, round, wall seconds, max RSS KiB (from
  `/usr/bin/time -f "%e %M"`), `MIR_checking` seconds and `type_check_crate`
  seconds (from `-Ztime-passes`), and (interleaved only) 1-minute load average.
- `results/census/census_queries.tsv` - GitHub issue-search query strings and
  the `total_count` each returned on 2026-11-20.
- `results/census/census_lists.tsv` - issue number, state, creation date,
  closing date, and title for five of those queries.

## Toolchains

| Configuration label | `rustc -V` |
|---|---|
| `nightly-default-*`, `nightly-polonius-off-*` | `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` |
| `stable-1.100.0-*` | `rustc 1.100.0 (0ef1bc386 2026-11-09)` |
| `1.61.0-*` | `rustc 1.61.0 (fe5b13d68 2022-05-18)` |
| `1.56.0-*` | `rustc 1.56.0 (09c42c458 2021-10-18)` |
| `1.35.0-*` | `rustc 1.35.0 (3c235d560 2019-05-20)` |

The suffix `-e2015`, `-e2018` or `-e2021` is the `--edition` value.
All borrow-checker probes are compiled with
`--crate-type lib --emit=metadata`, which runs type checking and borrow
checking but no code generation.
