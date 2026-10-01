# R522 conditional compilation in HIR and MIR, two Rust nightlies

## Scope and result

The [published R522 source report](../rust-conditional-compilation-nightly-2026-05-31/REPORT.md) (REPORT.md SHA-256 `15169eac9a2b64e7aec58b9fa626983eab95fee120039f05a1c4fd870ce33737`) explains that false `#[cfg]` items are removed before HIR and MIR, while `cfg_attr(path = ...)` can select a module file. It did not retain a runnable Rust fixture or execute rustc. This supplement uses a **new, reconstructed** three-file fixture to test that narrow compiler-output claim on the host target. It does not replay original fixture bytes, because none were retained.

The [main file](fixture/main.rs) has mutually exclusive feature items, a custom-cfg item and fallback, a macro emitting cfg-decorated items, `cfg_attr(path = ...)` choosing [selected_a.rs](fixture/selected_a.rs) or [selected_b.rs](fixture/selected_b.rs), and an `if cfg!(feature = "a")` control. Direct rustc `--cfg` arguments independently toggle `feature="a"` and `custom_from_build`, yielding four configurations. Each was inspected as HIR and emitted MIR under two locally installed nightlies: **16 serial child processes**. All exited 0.

For both compiler versions, each HIR dump contains exactly the expected configured item owners and source spans from only the selected module file. Each MIR file contains the corresponding functions and selected module constants. No cfg-excluded item or unselected module function appears in that configuration's HIR owner set or MIR function set. The custom cfg was supplied directly through `--cfg`; the experiment does **not** run Cargo or a build script, so it does not retest Cargo's forwarding of build-script output.

| Direct cfg arguments | HIR/MIR feature item | HIR/MIR custom item | Selected file and unique function | Macro-generated item | `cfg!` in emitted opt-level-0 MIR |
| --- | --- | --- | --- | --- | --- |
| none | `feature_off_only` | `no_custom_cfg_only` | `selected_b.rs`, `selected_b_only` | `macro_off_only` | `false` |
| `feature="a"` | `feature_a_only` | `no_custom_cfg_only` | `selected_a.rs`, `selected_a_only` | `macro_a_only` | `true` |
| `custom_from_build` | `feature_off_only` | `custom_cfg_only` | `selected_b.rs`, `selected_b_only` | `macro_off_only` | `false` |
| both | `feature_a_only` | `custom_cfg_only` | `selected_a.rs`, `selected_a_only` | `macro_a_only` | `true` |

The HIR owner sets and selected-file spans agree across the two toolchains for each case, but full HIR dump bytes differ. The four emitted MIR files are **byte-identical across versions** at the recorded `-Zmir-opt-level=0` setting. In the `cfg_control` MIR, the selected `cfg!` Boolean is a constant `true` or `false`, while both ordinary `if` arms (`70` and `80`) and a `switchInt` remain. That directly distinguishes early `#[cfg]` deletion from this later unoptimized MIR control flow. It does not promise the branches survive optimized MIR or machine code.

## Version and provenance boundary

The R522 source report pins `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and associated Rust Reference/Cargo source. The installed **May 31** binary instead reports compiler commit `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`rustc 1.98.0-nightly`), executable SHA-256 `2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc`. The installed **September 30** binary reports `5c543b0b8c73c7b72bc8284ced4fb22ead15734d` (`rustc 1.101.0-nightly`), executable SHA-256 `29f8ccc9aa7b0d8798eda854fa7f0e4ba3867c8c336b87d52dbb3b24b3f0878d`. Both are `aarch64-apple-darwin`; their full `rustc -Vv` output is in [results.json](results.json).

This is a **toolchain-era runtime comparison**, not a byte-for-byte execution of the report's `14210df…` source pin. The original inventory also named stable Rust 1.98.1 as a comparison target; this experiment runs the two named nightlies only. It uses no foreign target because neither local nightly has a non-host standard-library target installed. It does not run Charon, Aeneas, or Anneal, and it cannot show what a filesystem scanner might read: the claim is about the configured HIR/MIR representations.

## Evidence and replay

[results.json](results.json) preserves exact argv, fixture and executable hashes, admission inputs, exits, elapsed times, sampled child RSS, and stream/artifact hashes for every cell. [Raw HIR and MIR](raw/) and [analysis.json](analysis.json) preserve the outputs and extracted owner/function sets. The runner used direct rustc in serial with a fresh per-child gate of >20% estimated reclaimable RAM, >1 GiB free disk, and <100 MB package output; children were capped at 1 GiB sampled RSS and 30 seconds. The minimum recorded admission was **25.3458%** RAM and **5,883,711,488** free disk bytes; maximum owned package bytes at admission were **697,527**, maximum sampled child RSS **80,160 KiB**, and maximum child duration **0.152 s**. Very short children can finish before an RSS poll, so zero is possible for an individual sampled peak. No install, download, network access, server, or shared-checkout edit occurred.

From this package, `python3 -B support/check.py` verifies the exact fixture, tool identities, all 16 commands and raw outputs, gate arithmetic, cfg-specific HIR/MIR assertions, and cross-version MIR bytes without invoking rustc. It works after relocating the package. `python3 -B support/probe.py` actively repeats the local matrix with the same guarded binaries. The text formats of `-Zunpretty=hir-tree` and `--emit=mir` are compiler debugging surfaces, so these observations apply to the recorded versions and flags.
