# R562: rustc diagnostic-width outputs at the pinned and newer toolchains

## Result

The published [pinned rustc report](../rustc-diagnostic-width-format-nightly-2026-05-31/REPORT.md) establishes the source-level `--diagnostic-width`, human-format, and JSON controls at nightly 2026-05-31. Its checked-in upstream `flag-json.rs` fixture is identified by Git blob but **its bytes and exact run command are not retained locally**. This report therefore runs a clearly [reconstructed small specimen](fixture/Width.rs), not a reproduction of that upstream UI test. It compares the installed pinned nightly, stable 1.98.1, and nightly 2026-09-30 with fixed widths 40 and 100.

All three compilers accepted `--diagnostic-width=40` and `=100` in ordinary JSON and human modes, and accepted `--json=diagnostic-short` at width 100. All 15 serial commands exited **1**, as intended for the erroneous fixture. Ordinary JSON emitted 12 line-delimited records: eight `E0308` mismatched-type errors at line 11, one `E0277` trait error at line 12, an aborting summary, and two failure notes. The eight `E0308` primary source spans, messages, and error codes matched across the three versions. The `E0277` primary span remained line 12, columns 22–31, at both widths in all versions.

Fixed width changed **structured** `E0277` text, not just `rendered`: at width 40 the pinned nightly and stable 1.98.1 said `` `Vec<...>` is not an iterator ``, whereas nightly 2026-09-30 said `` `Vec<_>` is not an iterator ``. At width 100 the earlier two said `` `Vec<BTreeMap<String, Vec<Option<...>>>>` is not an iterator `` and the newer nightly said `` `Vec<BTreeMap<String, Vec<Option<_>>>>` is not an iterator ``. The primary span label and the help child's trait text changed in the same way. Thus pinning width and source bytes does **not** make this diagnostic's wording identical across compiler versions. Each width also changed the human/embedded rendering within a version. The `--json=diagnostic-short` cell kept a one-line `rendered` form and emitted 10 records, omitting the two ordinary JSON failure-note records on this fixture; it is a separate output mode, not a pure byte-level rendering toggle here.

## Exact inputs and raw evidence

| Compiler | Exact identity from `rustc -Vv` | Executable SHA-256 |
| --- | --- | --- |
| Pinned `nightly-2026-05-31` | `rustc 1.98.0-nightly`, commit `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` | `2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc` |
| Stable 1.98.1 | `rustc 1.98.1`, commit `48a229ceaefd4985c50990b14116b6d856af0985` | `2814fb55fb9cfb3eef5848a8104d77e3de7fd95394661144a12ee90cd4405340` |
| `nightly-2026-09-30` | `rustc 1.101.0-nightly`, commit `5c543b0b8c73c7b72bc8284ced4fb22ead15734d` | `29f8ccc9aa7b0d8798eda854fa7f0e4ba3867c8c336b87d52dbb3b24b3f0878d` |

The specimen declares a long nested `BTreeMap` type, eight explicit `u8` literals in a `u64` tuple, and a `Vec<Long>` supplied to an `Iterator<Item=Long>` bound. It was designed from the pinned report's suggested *kind* of discriminator, not copied from rustc's `flag-json.rs`; its SHA-256 is checked by the [offline checker](support/check.py). Every invocation used `--edition=2021 --emit=metadata --crate-name width_probe --out-dir <private cell>`. The JSON cells passed `--error-format=json --diagnostic-width=<40|100>`; human cells passed `--error-format=human --color=never --diagnostic-width=<40|100>`; the extra width-100 cell passed `--error-format=json --json=diagnostic-short`. There was no JSON/color combination.

The [probe](support/probe.py) and [results manifest](results.json) preserve commands, exact compiler version strings and hashes, return codes, elapsed time, admission samples, and SHA-256 values for every raw stream and generated long-type file. [Raw output](raw/) retains stdout and stderr bytes for all 15 cells; [out](out/) retains the generated long-type text files. JSON's path-bearing notes include those compiler-generated filenames. The checker compares the relevant structured fields and source spans while retaining raw bytes for audit; it does not pretend that ephemeral long-type filenames are a semantic identity.

## Bounds and revalidation

Fresh admission for the final run recorded **22.35%** estimated reclaimable RAM and **8,584,843,264** free disk bytes. Each child required >20% RAM, >1 GiB disk, and <100 MiB owned scratch before launch; commands were serial with a 10-second timeout. All completed in at most **0.31767 s**; minimum admission RAM was **22.41%**, minimum disk **8,584,318,976** bytes, and maximum admission scratch **251,978** bytes. No install, download, network dependency, or shared checkout change occurred.

This run demonstrates output behavior for one reconstructed fixture and does not establish what the unavailable upstream UI fixture would emit, all width-dependent construction paths, terminal-width precedence without an explicit flag, or cross-version JSON schema stability. Recheck the retained evidence with `python3 -B support/check.py`. An active repeat needs the three exact local binaries: `python3 -B support/probe.py --nightly-2026-05-31 /path/to/pinned/rustc --stable-1.98.1 /path/to/stable/rustc --nightly-2026-09-30 /path/to/newer/rustc`; it resets only this package's `raw/` and `out/` trees.
