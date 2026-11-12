# Subprocess-Tree Supervision, ELF `DT_RUNPATH` vs. `DT_RPATH` Closure, Nix `rust-lld` Sandbox Execution, and Precompiled Toolchain Packaging

## Summary

This report establishes the process-supervision, ELF dynamic-loader, Nix sandbox linker, and archive-packaging invariants governing multi-process verification toolchains across `joshlf/anneal@aa325aa43af936a97932e0e1c14755edf1a9136d`, `joshlf/anneal@f2bc17e9be87b777d63c785b31f3370ff058d69b`, `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`1.98.0-nightly`), and `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`):

1. **Subprocess-Tree Termination, Synchronous Descendant Reaping, and Replay Signal Forwarding**:
   - *Direct-child-only timeout (`child.kill()` + `child.wait()`) leaks grandchildren and locks*: When a supervisor spawns a multi-process command (`cargo-anneal`, `cargo`, `rustc`, `anneal-audit`, or `sh`) in the parent's process group and enforces a deadline via `child.kill()` (`kill(child_pid, SIGKILL)`), only the direct child `P1` terminates (`163 µs`). Any grandchild `P2` (`lean`, `rustc`, `cc1`, `ld`) survives as an orphan (`p2_alive_after_reap = true`) and continues holding open file descriptors and exclusive advisory `flock` locks inside the temporary run directory (`lock_held_by_orphan_after_reap = true`).
   - *Why Linux `PR_SET_PDEATHSIG(SIGKILL)` alone fails on 2-level trees*: Because Linux `copy_process()` (`kernel/fork.c`) resets `p->pdeath_signal = 0` on every `fork()`, setting `prctl(PR_SET_PDEATHSIG, SIGKILL)` in `CommandExt::pre_exec` applies only to direct child `P1` when the *supervisor* dies. When the supervisor kills `P1` at a deadline, `P2` has `pdeath_signal == 0` and survives (`p2_alive_after_reap = true`, reparented to the subreaper). Conversely, setting `PR_SET_PDEATHSIG(SIGKILL)` inside every descendant causes `P2` to receive `SIGKILL` prematurely if an intermediate launcher process `P1` (or spawning thread in a multi-threaded parent) exits `0` before `P2` finishes.
   - *Combined `process_group(0)` + `PR_SET_CHILD_SUBREAPER` + `waitpid(-pgid)` until `ECHILD`*: Spawning `P1` in an isolated process group (`CommandExt::process_group(0)` / `setpgid(0, 0)`) with `prctl(PR_SET_CHILD_SUBREAPER, 1)` on the supervisor (plus `PR_SET_PDEATHSIG(SIGKILL)` on `P1` in case the supervisor itself is `SIGKILL`ed) and executing `kill(-pgid, SIGKILL)` followed by a blocking `waitpid(-pgid, &mut status, 0)` loop until `errno == ECHILD` synchronously terminates and reaps both `P1` and reparented grandchildren in `157 µs` (`p2_alive_after_reap = false`, `lock_held_by_orphan_after_reap = false`).
   - *Interactive `SIGINT` (`Ctrl-C`) vs. `process_group=0` in replay scripts (`reproduce.py`)*: Calling `subprocess.run(..., timeout=timeout)` without `process_group=0` leaks grandchildren on `TimeoutExpired` (`exit 124`, `p2_alive_after_exit = true`). However, placing the child in `process_group=0` removes it from the controlling terminal's foreground process group, so a naive `subprocess.Popen(..., process_group=0)` without signal handlers exits `-2` on `SIGINT` while leaving both `P1` and `P2` alive (`p1_alive_after_sigint = true`, `p2_alive_after_sigint = true`). Installing `SIGINT`/`SIGTERM` handlers that forward `os.killpg(proc.pid, signum)` and calling `os.killpg(proc.pid, signal.SIGKILL)` on `TimeoutExpired` and `finally` cleanly terminates and reaps the entire tree under both timeouts (`exit 124`) and `SIGINT` (`exit -2`).

2. **ELF `DT_RUNPATH` vs. `DT_RPATH` Ancestor Suppression (`glibc` `elf/dl-load.c`) and `rustlib` Deduplication**:
   - *Why `DT_RPATH` (`--force-rpath`) on `anneal-rustc-capture` is blocked by `libLLVM.so`'s `DT_RUNPATH`*: In GNU `glibc`'s `elf/dl-load.c:_dl_map_object(struct link_map *loader, ...)`, the ancestor `DT_RPATH` walk (which walks `loader->l_loader` up to `main_map->l_rpath_dirs`) is gated by `if (loader == NULL || loader->l_info[DT_RUNPATH] == NULL)`. Because upstream `libLLVM.so.22.1-rust-1.98.0-nightly` carries its own `DT_RUNPATH` (`$ORIGIN/../lib`), `loader->l_info[DT_RUNPATH] != NULL` holds when `libLLVM.so` requests `libz.so.1`, completely disabling `main_map`'s `DT_RPATH` even if `anneal-rustc-capture` is linked with `--disable-new-dtags` (`DT_RPATH` `0x0f`). In a 5-cell controlled ELF matrix (`main -> libmid.so -> libleaf.so -> libdep.so`), `main` with `DT_RPATH` fails (`exit 127`) when `libleaf.so` has `DT_RUNPATH` (Cell 2) and succeeds (`exit 0`) when `libleaf.so` uses `DT_RPATH` instead (Cell 3).
   - *Consumer-side `--add-needed libz.so.1` vs. producer-side `rust/lib/` co-location*: Inside `/nix/store`, `packages.rust-toolchain` is an immutable Fixed-Output Derivation (`outputHashMode = "recursive"`) whose `lib/` directory lacks `libz.so.1`, and Nix's `fixupPhase` (`patchelf --shrink-rpath`) strips `zlib` from `anneal-rustc-capture`'s `DT_RUNPATH` unless `libz.so.1` is a direct `DT_NEEDED` entry. Thus `/nix/store/...-anneal-rustc-capture` requires `patchelf --add-needed libz.so.1` (Cell 4). By contrast, once `omnibus-archive` copies `libz.so.1` and `libgcc_s.so.1` directly into `rust/lib/` (`joshlf/anneal@aa325aa43af936a97932e0e1c14755edf1a9136d`, `flake.nix:271-274`), `rust/lib/libLLVM.so.22.1-rust-1.98.0-nightly`'s own upstream `DT_RUNPATH` (`$ORIGIN/../lib`, which resolves to `rust/lib/`) locates `rust/lib/libz.so.1` for all consumers (`rustc`, `rustdoc`, `rust-lld`, and `anneal-rustc-capture`) without requiring `--add-needed libz.so.1` on the consumer executable (Cell 5).
   - *`357.6 MB` duplicate shared libraries in `rust-toolchain`*: Upstream `rustc` and `rustc-dev` tarballs unpack byte-identical copies of `libLLVM.so.22.1-rust-1.98.0-nightly` (`199,489,904` B, SHA-256 `10b13617...`) and `librustc_driver-5d5a3c5207375ffc.so` (`158,109,664` B, SHA-256 `1f3ac596...`) into both `rust/lib/` and `rust/lib/rustlib/x86_64-unknown-linux-gnu/lib/` (`357,599,568` B total duplication). Moreover, for the `rustlib/x86_64-unknown-linux-gnu/lib/` copy, `$ORIGIN/../lib` resolves to `rustlib/x86_64-unknown-linux-gnu/lib/` (where `libz.so.1` is absent). Replacing the two `rustlib/.../lib/*.so` copies with relative symlinks (`../../../libLLVM.so.22.1-rust-1.98.0-nightly` and `../../../librustc_driver-5d5a3c5207375ffc.so`) saves `357.6 MB` unpacked and ensures `$ORIGIN` resolves to `rust/lib/`.

3. **Why `rustc` 1.98 Nightly Fails Inside Nix Sandboxes Without `-Clinker-features=-lld`**:
   - In `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`1.98.0-nightly`), `x86_64-unknown-linux-gnu` enables `rust-lld` by default, causing `rustc` to pass `-B<sysroot>/lib/rustlib/x86_64-unknown-linux-gnu/bin/gcc-ld -fuse-ld=lld` to `cc`.
   - Even when `rustc` itself is launched via Nix's explicit dynamic linker (`${pkgs.stdenv.cc.bintools.dynamicLinker} --library-path ... ${rustToolchain}/bin/rustc` in `anneal-build-rustc`), child processes spawned by `cc` (`collect2`) do not inherit the explicit `ld-linux` wrapper. When `collect2` calls `posix_spawnp` on `<sysroot>/.../bin/gcc-ld/ld.lld` (whose ELF `PT_INTERP` is `/lib64/ld-linux-x86-64.so.2`), the Linux kernel's `load_elf_binary` fails with `ENOENT` inside Nix's `/lib64`-less build sandbox (`collect2: fatal error: posix_spawnp: No such file or directory`). Passing `-Clinker-features=-lld` suppresses `-B.../gcc-ld -fuse-ld=lld` so `collect2` invokes Nix's `binutils-wrapper` `ld`.

4. **Toolchain Packaging Architecture Comparison (`5.88x` Verification Speedup with Precompiled `share/anneal/` `.olean`s)**:
   - Comparing four packaging designs across environment-variable surface, test-runner coupling, and per-run compilation cost shows that:
     - *Variant 1 (Split Archive + 5 Manual Env Vars + Test-Binary Re-Exec)* (`joshlf/anneal@aa325aa43af936a97932e0e1c14755edf1a9136d` CI/test harness) requires callers to manually export `5` build/test environment variables (`RUSTC`, `RUSTDOC`, `LD_LIBRARY_PATH`, `RUSTFLAGS`, `ANNEAL_TEST_RUST_SYSROOT`) plus `4` smoke-test variables, omits `anneal-audit` and `TrustedBoundary.lean` from the archive, and re-executes the ephemeral test binary (`std::env::current_exe() --exact install_archive_worker --ignored`) to install into a test-owned directory.
     - *Variant 2 (`include_str!` Embedded Sources + Per-Run Recompilation)* embeds 11 files (`TrustedBoundary.lean`, `library-lock.json`, `foundation-lock.json`, `lean-toolchain`, and 7 `Trusted`/`Anneal` `.lean` files) into `cargo-anneal` and recompiles all 7 `Trusted`/`Anneal` modules from scratch on every `verify` call (`7,154.61 ms` for the 7 prefix modules + `1,445.60 ms` for the 4 target modules = `8,600.21 ms` total).
     - *Variant 3 (Embedded SHA-256 Manifests + `/tmp` Hardlink Snapshot + Lazy Runtime Compilation)* requires an external `--anneal-root` source checkout, hardlinks `7,853` toolchain files into `/tmp`, and compiles `anneal-rustc-capture` and the 7 `Trusted`/`Anneal` `.lean` modules lazily at runtime on every cold CLI process.
     - *Variant 4 (Unified, Zero-Env-Var, Precompiled Omnibus Archive + `--install-dir`)* bundles `bin/{anneal-rustc-capture,anneal-audit}`, deduplicated `rust/`, `lean/`, and `share/anneal/` containing `foundation-lock.json`, `library-lock.json`, `TrustedBoundary.{lean,olean}`, and precompiled `.olean` + `.lean` files for `Trusted` and `Anneal`. Authenticating the 7 precompiled prefix `.olean`s via SHA-256 takes `0.441 ms` (`441 µs`) and compiling only the 4 crate-local target modules takes `1,463.33 ms` (`1,463.78 ms` total, a **`5.88x` speedup** over Variant 2), while `cargo-anneal setup --local-archive <path> --install-dir <dest>` eliminates test-binary self-re-execution.

## Applicability

These findings apply to:

- **Anneal Toolchain Packaging, Driver, and CI/Verifier Implementations**: `joshlf/anneal@aa325aa43af936a97932e0e1c14755edf1a9136d` (`flake.nix`, `.github/workflows/ci.yml`, `trusted/rustc-capture/`) and `joshlf/anneal@f2bc17e9be87b777d63c785b31f3370ff058d69b` (`flake.nix`, `trusted/cargo-anneal/`, `trusted/audit/`), together with the four packaging variants and five subprocess-supervision strategies defined and benchmarked in this report.
- **Bundled Rust and Lean Toolchains**: `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`1.98.0-nightly (2026-05-30)`) and `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`).
- **Nixpkgs and Dynamic Loader Environment**: `NixOS/nixpkgs@549bd84d6279f9852cae6225e372cc67fb91a4c1` (`patchelf-0.15.2`, `gcc-wrapper-15.2.0`, `binutils-wrapper-2.45`, `glibc-2.42`) on `x86_64-linux` (Linux `6.17.11`, GNU `glibc 2.42`, `bwrap` user-namespace sandboxes).

**Shared behavior vs. version deltas across `joshlf/anneal@f2bc17e9be87b777d63c785b31f3370ff058d69b` and `joshlf/anneal@aa325aa43af936a97932e0e1c14755edf1a9136d`**:
- Both revisions bundle `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` and `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` with `dontPatchELF = true` and patch `bin/anneal-rustc-capture` with `--add-needed libz.so.1` and `--set-rpath '$ORIGIN/../rust/lib'`.
- At `f2bc17e9be87b777d63c785b31f3370ff058d69b`, `packages.toolchain-omnibus` did not copy `libz.so.1` or `libgcc_s.so.1` into `rust/lib/`, whereas `aa325aa43af936a97932e0e1c14755edf1a9136d` (`flake.nix:271-274`) copies dereferenced `${pkgs.zlib}/lib/libz.so.1` and `${pkgs.stdenv.cc.cc.lib}/lib/libgcc_s.so.1` into `rust/lib/` and introduces `anneal-build-rustc` (`flake.nix:81-96`) with `-Clinker-features=-lld`.

## Findings

### 1. Subprocess-Tree Termination, Reaping, and Signal Forwarding

#### 1.1 Why direct-child `child.kill()` and `PR_SET_PDEATHSIG` alone fail on multi-process toolchains
When a test runner or CLI supervisor spawns a multi-process command (`P1`, such as `cargo-anneal`, `cargo`, `rustc`, or a shell wrapper) that in turn spawns a long-running child (`P2`, such as `lean`, `rustc`, `cc1`, or `ld`), three distinct failure modes arise across naive supervision strategies:

1. **Direct-child-only `child.kill()` (`Strategy A`)**: Calling `child.kill()` (`kill(p1_pid, SIGKILL)`) followed by `child.wait()` terminates and reaps only `P1`. Because `P1` and `P2` share the supervisor's process group, `P2` is never signaled; it is reparented to the nearest subreaper (or `init`) and continues running while holding open file descriptors and advisory locks inside the test case directory.
2. **`PR_SET_PDEATHSIG(SIGKILL)` on `P1` only (`Strategy C1`)**: In the Linux kernel (`kernel/fork.c:copy_process`), `p->pdeath_signal = 0` is unconditionally cleared in every newly forked child. Setting `prctl(PR_SET_PDEATHSIG, SIGKILL)` inside `CommandExt::pre_exec` therefore arms `pdeath_signal` on `P1` (firing if the *supervisor* dies), but `P2` inherits `pdeath_signal = 0`. When the supervisor kills `P1` at a deadline, `P2` receives no signal and survives.
3. **`PR_SET_PDEATHSIG(SIGKILL)` on every descendant (`Strategy C2`)**: Even if `P2` itself calls `prctl(PR_SET_PDEATHSIG, SIGKILL)`, `PR_SET_PDEATHSIG` fires whenever the *creating thread* (or parent process `P1`) terminates for *any* reason—including when a wrapper process `P1` exits `0` after launching `P2` or when a worker thread in a multi-threaded parent exits while the parent process remains alive.

#### 1.2 Synchronous group reaping via `process_group(0)` + `PR_SET_CHILD_SUBREAPER` (`Strategy D`)
Combining process-group isolation (`CommandExt::process_group(0)` / `setpgid(0, 0)`) with `prctl(PR_SET_CHILD_SUBREAPER, 1)` on the supervisor (and `PR_SET_PDEATHSIG(SIGKILL)` on `P1` as a backstop if the supervisor itself is `SIGKILL`ed) closes both gaps:
- On timeout, `kill(-pgid, SIGKILL)` delivers an uncatchable `SIGKILL` atomically to every process in `pgid` (`P1`, `P2`, and any deeper descendants that have not called `setsid` / `setpgid`).
- Because the supervisor is marked `PR_SET_CHILD_SUBREAPER`, orphaned grandchildren (`P2`) are reparented to the supervisor rather than `init`. After `child.wait()` reaps `P1`, the supervisor loops on blocking `waitpid(-pgid, &mut status, 0)` until it returns `-1` with `errno == ECHILD`. That `ECHILD` return guarantees that every process in `pgid` has completed kernel `do_exit()` (`exit_files()`) and released all open file descriptors and locks before the function returns. On non-Linux POSIX hosts (such as macOS, which lacks `PR_SET_CHILD_SUBREAPER`), polling `kill(-pgid, 0)` until `errno == ESRCH` after `kill(-pgid, SIGKILL)` waits until `launchd` reaps all group members (`Strategy B`).

Using [`support/process-tree-supervision/supervisor_probe.rs`](support/process-tree-supervision/supervisor_probe.rs) and [`support/process-tree-supervision/probe.py`](support/process-tree-supervision/probe.py), we executed all five strategies against a 2-level process tree (`supervisor -> P1 -> P2`) where `P2` acquires an exclusive `flock(LOCK_EX | LOCK_NB)` on `case.lock`:

| Strategy | Supervision Mechanism | `P1` Alive After Reap | `P2` Alive After Reap | `case.lock` Held by Orphan | Reap Latency (`µs`) |
| :--- | :--- | :---: | :---: | :---: | :---: |
| **`A_direct_child_kill`** | `child.kill()` + `child.wait()` (direct child PID only) | `false` | **`true` (leaked)** | **`true` (locked)** | `163` |
| **`B_process_group_killpg`** | `process_group(0)` + `kill(-pgid, SIGKILL)` + `kill(-pgid, 0)` poll until `ESRCH` | `false` | `false` | `false` | `425` |
| **`C1_subreaper_pdeathsig_on_p1_only`** | `PR_SET_CHILD_SUBREAPER` + `PR_SET_PDEATHSIG(SIGKILL)` in `P1` `pre_exec`; `child.kill()` at timeout | `false` | **`true` (reparented to subreaper)** | **`true` (locked)** | `141` |
| **`C2_pdeathsig_on_p2_early_p1_exit`** | `PR_SET_PDEATHSIG(SIGKILL)` on `P2` when `P1` exits `0` after `20 ms` | `false` (`exit 0`) | `false` (**prematurely killed by `SIGKILL`**) | `false` | — |
| **`D_combined_pgroup_and_subreaper_waitpid`** | `PR_SET_CHILD_SUBREAPER` + `process_group(0)` + `kill(-pgid, SIGKILL)` + blocking `waitpid(-pgid)` until `ECHILD` | `false` | `false` (`1` descendant synchronously reaped) | `false` | **`157`** |

Basis: **source** (`linux/kernel/fork.c:copy_process`) + **execution** ([`support/process-tree-supervision/results.json`](support/process-tree-supervision/results.json)).

#### 1.3 Interactive `SIGINT` (`Ctrl-C`) vs. `process_group=0` in replay scripts (`reproduce.py`)
When a failure-replay script (`reproduce.py`) runs `subprocess.run(..., timeout=timeout)` without `process_group=0` (`Case E1`), Python's `subprocess.run` kills only `P1` on `TimeoutExpired` (`exit 124`), leaving `P2` alive and holding `case.lock`. However, if `reproduce.py` spawns `P1` with `process_group=0` (`setpgid(0, 0)`) without updating the terminal foreground process group (`tcsetpgrp`) or installing signal handlers (`Case E2`), pressing `Ctrl-C` in an interactive terminal sends `SIGINT` only to the terminal's foreground process group (`reproduce.py`), terminating `reproduce.py` with `KeyboardInterrupt` (`exit -2`) while leaving both `P1` and `P2` running in their background process group!

Installing `SIGINT` and `SIGTERM` handlers in `reproduce.py` that forward `os.killpg(p.pid, signum)` before escalating to `os.killpg(p.pid, signal.SIGKILL)` and `p.wait()` (`Cases E3a` and `E3b` in [`support/process-tree-supervision/probe.py`](support/process-tree-supervision/probe.py)) resolves both failure modes:

| Replay Script Case | Trigger Event | Exit Code | `P1` Alive After Exit | `P2` Alive After Exit | `case.lock` Held After Exit |
| :--- | :--- | :---: | :---: | :---: | :---: |
| **`E1_unfixed_reproduce_timeout`** | `0.15 s` timeout (`subprocess.run` without `process_group=0`) | `124` | `false` | **`true` (leaked)** | **`true` (locked)** |
| **`E2_pgroup_reproduce_sigint_without_forwarding`** | Foreground `SIGINT` (`process_group=0` without signal handler) | `-2` | **`true` (leaked)** | **`true` (leaked)** | **`true` (locked)** |
| **`E3a_fixed_pgroup_reproduce_timeout`** | `0.15 s` timeout (`process_group=0` + `os.killpg(SIGKILL)` on timeout) | `124` | `false` | `false` | `false` |
| **`E3b_fixed_pgroup_reproduce_sigint`** | Foreground `SIGINT` (`process_group=0` + `SIGINT`/`SIGTERM` forwarding to `-pgid`) | `-2` | `false` | `false` | `false` |

Basis: **execution** ([`support/process-tree-supervision/probe.py`](support/process-tree-supervision/probe.py), [`support/process-tree-supervision/results.json`](support/process-tree-supervision/results.json)).

---

### 2. ELF `DT_RUNPATH` vs. `DT_RPATH` Ancestor Suppression (`glibc` `elf/dl-load.c`) and `rustlib` Deduplication

#### 2.1 Why `DT_RPATH` (`--force-rpath`) on `anneal-rustc-capture` is suppressed by `libLLVM.so`'s `DT_RUNPATH`
In `joshlf/anneal@aa325aa43af936a97932e0e1c14755edf1a9136d` (`flake.nix:220-227`), `packages.rustc-capture` runs:

```nix
postFixup = pkgs.lib.optionalString pkgs.stdenv.isLinux ''
  ${pkgs.patchelf}/bin/patchelf --add-needed libz.so.1 \
    --set-rpath ${rustRuntimeLibraryPath} \
    "$out/bin/anneal-rustc-capture"
'';
```

Why does `bin/anneal-rustc-capture` fail to load `libz.so.1` inside `/nix/store` without `--add-needed libz.so.1`, even if `patchelf --force-rpath` (`DT_RPATH`, tag `0x0f`) is used instead of `DT_RUNPATH` (tag `0x1d`)?
1. **Nix `fixupPhase` `--shrink-rpath` pruning**: During `stdenv.mkDerivation`'s `fixupPhase`, `patchelf --shrink-rpath` inspects only the direct `DT_NEEDED` entries of `$out/bin/anneal-rustc-capture` (`librustc_driver-5d5a3c5207375ffc.so`, `libgcc_s.so.1`, `libc.so.6`, `ld-linux-x86-64.so.2`) and deletes `${pkgs.zlib}/lib` from `DT_RUNPATH` because `libz.so.1` is needed only indirectly by `libLLVM.so.22.1-rust-1.98.0-nightly`.
2. **`glibc` `_dl_map_object` suppression of `DT_RPATH` when `loader` carries `DT_RUNPATH`**: Even if `${pkgs.zlib}/lib` is written into `anneal-rustc-capture` after `fixupPhase` as a deprecated **`DT_RPATH` (`0x0f`)** tag (`patchelf --force-rpath`), GNU `glibc`'s `elf/dl-load.c:_dl_map_object(struct link_map *loader, const char *name, ...)` gates the entire ancestor `DT_RPATH` walk (which walks `loader->l_loader` up to `main_map->l_rpath_dirs`) behind:

   ```c
   if (loader == NULL || loader->l_info[DT_RUNPATH] == NULL)
     {
       /* Search loader..main_map l_rpath_dirs (DT_RPATH) */
     }
   ```

   Because upstream `libLLVM.so.22.1-rust-1.98.0-nightly` (`loader`) has its own `DT_RUNPATH = [$ORIGIN/../lib]` (`loader->l_info[DT_RUNPATH] != NULL`), `_dl_map_object` **skips the `DT_RPATH` ancestor walk completely** and searches only `libLLVM.so`'s own `DT_RUNPATH` (`$ORIGIN/../lib` = `/nix/store/...-rust-toolchain/lib`, which lacks `libz.so.1`).

#### 2.2 Five-cell empirical verification (`support/elf-runpath-and-nix-lld/`)
In [`support/elf-runpath-and-nix-lld/probe.py`](support/elf-runpath-and-nix-lld/probe.py) ([`support/elf-runpath-and-nix-lld/results.json`](support/elf-runpath-and-nix-lld/results.json)), we constructed a 3-tier ELF shared-library chain (`bin/main -> lib_main/libmid.so -> lib_main/libleaf.so -> libdep.so`) mirroring `anneal-rustc-capture -> librustc_driver.so -> libLLVM.so -> libz.so.1` and executed all five configurations under `env -i`:

| Cell | `bin/main` Dynamic Tags | `lib_main/libleaf.so` Dynamic Tags | `libdep.so` Location | Exit Code | `stdout` / Loader Outcome |
| :--- | :--- | :--- | :--- | :---: | :--- |
| **`1_main_runpath_leaf_runpath_uncolocated`** | `DT_RUNPATH: $ORIGIN/../lib_main:$ORIGIN/../lib_dep`; `NEEDED: [libmid.so, libc.so.6]` | `DT_RUNPATH: $ORIGIN`; `NEEDED: [libdep.so]` | `lib_dep/libdep.so` only | `127` | Fails: `libdep.so: cannot open shared object file` (`DT_RUNPATH` is non-transitive) |
| **`2_main_rpath_blocked_by_leaf_runpath`** | **`DT_RPATH: $ORIGIN/../lib_main:$ORIGIN/../lib_dep`** (`--disable-new-dtags`); `NEEDED: [libmid.so, libc.so.6]` | **`DT_RUNPATH: $ORIGIN`**; `NEEDED: [libdep.so]` | `lib_dep/libdep.so` only | **`127`** | **Fails**: `libleaf.so`'s `DT_RUNPATH != NULL` suppresses `_dl_map_object`'s walk to `main`'s `DT_RPATH` |
| **`3_main_rpath_succeeds_when_leaf_has_no_runpath`** | `DT_RPATH: $ORIGIN/../lib_main:$ORIGIN/../lib_dep`; `NEEDED: [libmid.so, libc.so.6]` | **`DT_RPATH: $ORIGIN`** (`DT_RUNPATH == NULL`); `NEEDED: [libdep.so]` | `lib_dep/libdep.so` only | **`0`** | **`44`** (`libleaf.so` has `DT_RUNPATH == NULL`, so `_dl_map_object` walks up to `main`'s `DT_RPATH`) |
| **`4_consumer_add_needed_on_main`** | `DT_RUNPATH: $ORIGIN/../lib_main:$ORIGIN/../lib_dep`; **`NEEDED: [libdep.so, libmid.so, libc.so.6]`** | `DT_RUNPATH: $ORIGIN`; `NEEDED: [libdep.so]` | `lib_dep/libdep.so` only | **`0`** | **`44`** (`main` preloads `libdep.so` into the global link map at startup via `main`'s `DT_RUNPATH`) |
| **`5_producer_colocation_in_leaf_runpath_without_add_needed`** | `DT_RUNPATH: $ORIGIN/../lib_main`; **`NEEDED: [libmid.so, libc.so.6]`** (no `--add-needed`) | `DT_RUNPATH: $ORIGIN`; `NEEDED: [libdep.so]` | Co-located in **`lib_main/libdep.so`** | **`0`** | **`44`** (`libleaf.so`'s own `DT_RUNPATH = $ORIGIN` resolves `lib_main/libdep.so` for all consumers) |

Consequently:
- Inside `/nix/store` (`packages.rustc-capture`), where `packages.rust-toolchain` is an immutable FOD whose `lib/` directory cannot be modified to add `libz.so.1`, **Cell 4 (`patchelf --add-needed libz.so.1`)** is required so `anneal-rustc-capture` preloads `libz.so.1` from `${pkgs.zlib}/lib`.
- Inside the staged `omnibus-archive` (`dist_staging`), where `libz.so.1` and `libgcc_s.so.1` are copied directly into `rust/lib/` (`joshlf/anneal@aa325aa43af936a97932e0e1c14755edf1a9136d`, `flake.nix:271-274`), **Cell 5 holds automatically**: `rust/lib/libLLVM.so.22.1-rust-1.98.0-nightly`'s own `DT_RUNPATH` (`$ORIGIN/../lib` $\rightarrow$ `rust/lib/`) resolves `rust/lib/libz.so.1` and `rust/lib/libgcc_s.so.1` for every consumer (`rustc`, `rustdoc`, `rust-lld`, and `anneal-rustc-capture`) without requiring `--add-needed libz.so.1`.

#### 2.3 Duplicate `357.6 MB` shared libraries in `rust/lib/` vs. `rust/lib/rustlib/x86_64-unknown-linux-gnu/lib/`
Inspecting `packages.rust-toolchain` (`rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) reveals that unpacking both the `rustc` component and the `rustc-dev` component creates two byte-identical copies of the two largest shared objects in the toolchain ([`support/elf-runpath-and-nix-lld/results.json`](support/elf-runpath-and-nix-lld/results.json)):
- `libLLVM.so.22.1-rust-1.98.0-nightly`: `199,489,904` bytes (`SHA-256: 10b13617cc45091d9707991b67fda2993cbaece5c55165a9d055d0403233d481`) in both `rust/lib/` and `rust/lib/rustlib/x86_64-unknown-linux-gnu/lib/`.
- `librustc_driver-5d5a3c5207375ffc.so`: `158,109,664` bytes (`SHA-256: 1f3ac5968782c12fbf9df6701ed5915242abb8455044e5dac8ab2a68fd155547`) in both `rust/lib/` and `rust/lib/rustlib/x86_64-unknown-linux-gnu/lib/`.

Besides adding `357,599,568` bytes (`341.0 MiB`) to the unpacked toolchain, the copy under `rust/lib/rustlib/x86_64-unknown-linux-gnu/lib/` has `$ORIGIN/../lib` equal to `rust/lib/rustlib/x86_64-unknown-linux-gnu/lib/` rather than `rust/lib/`. Replacing the two files in `rust/lib/rustlib/x86_64-unknown-linux-gnu/lib/` with relative symlinks (`../../../libLLVM.so.22.1-rust-1.98.0-nightly` and `../../../librustc_driver-5d5a3c5207375ffc.so`) eliminates `357.6 MB` of unpacked duplication while ensuring that `dlopen` / `DT_NEEDED` resolution against either path resolves `$ORIGIN` to `rust/lib/`.

Basis: **source** (`glibc` `elf/dl-load.c`, `joshlf/anneal@aa325aa43af936a97932e0e1c14755edf1a9136d` `flake.nix`) + **execution** ([`support/elf-runpath-and-nix-lld/results.json`](support/elf-runpath-and-nix-lld/results.json)).

---

### 3. Why `rustc` 1.98 Nightly Fails Inside Nix Sandboxes Without `-Clinker-features=-lld`

In `joshlf/anneal@aa325aa43af936a97932e0e1c14755edf1a9136d` (`flake.nix:81-96`), `packages.rustc-capture` compiles `anneal-rustc-capture` inside Nix using a wrapper script `anneal-build-rustc`:

```sh
exec ${pkgs.stdenv.cc.bintools.dynamicLinker} \
  --library-path ${rustRuntimeLibraryPath} \
  ${rustToolchain}/bin/rustc --sysroot ${rustToolchain} \
  -Clinker-features=-lld "$@"
```

Both flags are load-bearing for distinct reasons when executing an unpatched upstream `rustToolchain` FOD inside a Nix Linux build sandbox (where `/lib64/ld-linux-x86-64.so.2` does not exist):
1. **Parent compiler startup (`dynamicLinker --library-path`)**: `${rustToolchain}/bin/rustc` has `PT_INTERP = /lib64/ld-linux-x86-64.so.2`. Invoking `${pkgs.stdenv.cc.bintools.dynamicLinker}` (`/nix/store/...-glibc-2.42-.../lib/ld-linux-x86-64.so.2`) directly with `--library-path ${rustRuntimeLibraryPath}` loads `rustc`, `librustc_driver`, `libLLVM`, `libgcc_s`, and `libz` without `/lib64/ld-linux-x86-64.so.2`.
2. **Child linker spawn (`-Clinker-features=-lld`)**: In `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`1.98.0-nightly`), `x86_64-unknown-linux-gnu` enables `rust-lld` by default. As captured via `--print link-args` and verified inside an unprivileged `bwrap` sandbox without `/lib64` ([`support/elf-runpath-and-nix-lld/probe.py`](support/elf-runpath-and-nix-lld/probe.py)):
   - With default linker features (`-Clinker-features=+lld`), `rustc` passes `-B<sysroot>/lib/rustlib/x86_64-unknown-linux-gnu/bin/gcc-ld -fuse-ld=lld` to Nix's `cc` (`gcc-wrapper-15.2.0`).
   - Inside `gcc`, `collect2` honors `-B.../gcc-ld` + `-fuse-ld=lld` and calls `posix_spawnp` on `<sysroot>/lib/rustlib/x86_64-unknown-linux-gnu/bin/gcc-ld/ld.lld` (which in turn execs `<sysroot>/lib/rustlib/x86_64-unknown-linux-gnu/bin/rust-lld`).
   - Both `gcc-ld/ld.lld` and `bin/rust-lld` in the unpatched `rustToolchain` FOD carry `PT_INTERP = /lib64/ld-linux-x86-64.so.2` (`readelf -l` in [`support/elf-runpath-and-nix-lld/results.json`](support/elf-runpath-and-nix-lld/results.json)). Because `posix_spawnp` does not inherit the parent `rustc`'s explicit `ld-linux` invocation, the kernel fails to open `/lib64/ld-linux-x86-64.so.2` and aborts linking with `collect2: fatal error: posix_spawnp: No such file or directory` (`exit 1`).
   - Passing `-Clinker-features=-lld` removes `-B<sysroot>/.../bin/gcc-ld` and `-fuse-ld=lld` from the `cc` invocation so `collect2` invokes Nix's `binutils-wrapper` `ld` (whose `PT_INTERP` points to `/nix/store/...-glibc-.../lib/ld-linux-x86-64.so.2`), succeeding with `exit 0`.

Basis: **source** (`joshlf/anneal@aa325aa43af936a97932e0e1c14755edf1a9136d` `flake.nix`) + **execution** ([`support/elf-runpath-and-nix-lld/probe.py`](support/elf-runpath-and-nix-lld/probe.py), [`support/elf-runpath-and-nix-lld/results.json`](support/elf-runpath-and-nix-lld/results.json)).

---

### 4. Comparative Analysis and Benchmark of Toolchain Packaging Models

We compared four toolchain packaging architectures across required manual environment variables, test-runner coupling, binary/archive footprint, and per-run `cargo-anneal verify` latency ([`support/toolchain-packaging-comparison/probe.py`](support/toolchain-packaging-comparison/probe.py), [`support/toolchain-packaging-comparison/results.json`](support/toolchain-packaging-comparison/results.json)):

| Dimension | Variant 1: Split Archive + Manual Env + Test Re-Exec | Variant 2: `include_str!` Embedded Sources + Per-Run Recompile | Variant 3: Embedded SHA-256 Lock + `/tmp` Hardlink Snapshot | Variant 4: Unified Zero-Env Precompiled Archive + `--install-dir` |
| :--- | :--- | :--- | :--- | :--- |
| **Archive Contents** | `bin/anneal-rustc-capture`, `rust/`, `lean/`, `share/anneal/trusted/lean/{foundation-lock.json,lean-toolchain,*.lean}` | `bin/anneal-rustc-capture`, `rust/`, `lean/`, `share/anneal/{trusted,theory}` | `bin/anneal-rustc-capture`, `rust/`, `lean/`, `share/anneal/{trusted,theory}` | `bin/{anneal-rustc-capture,anneal-audit}`, deduplicated `rust/` (`-357.6 MB`), `lean/`, `share/anneal/{foundation-lock.json,library-lock.json,TrustedBoundary.{lean,olean},src/lean/*,lib/lean/*.olean}` |
| **Manual Env Vars Required** | **`5` workspace** (`RUSTC`, `RUSTDOC`, `LD_LIBRARY_PATH`, `RUSTFLAGS`, `ANNEAL_TEST_RUST_SYSROOT`) + **`4` smoke test** | `0` | `0` (requires `--anneal-root` outside checkout) | **`0`** (all tools & paths resolved relative to `<install_root>`) |
| **Isolated Test Setup Mechanism** | Re-execs `std::env::current_exe() --exact install_archive_worker --ignored` (bakes transient `installed_smoke-<hash>` path into `reproduce.py`) | `XDG_CACHE_HOME` override | `XDG_CACHE_HOME` override | Direct `cargo-anneal setup --local-archive <path> --install-dir <dest>` (or in-process `setup::install_at` before command recording) |
| **`Trusted` + `Anneal` Prefix `lean` Invocations per `verify`** | — (scaffold only) | **`7` subprocesses** (recompiles all 7 `.lean` files from `.rodata` on every run) | **`7` subprocesses** on every cold CLI process (cached only in-process) | **`0` subprocesses** (verifies SHA-256 of precompiled `.olean`s in **`0.441 ms`**) |
| **Target Crate `lean` Invocations per `verify`** | — | `4` (`Captured`, `Spec`, `Proof`, `Expected`) + `1` (`TrustedBoundary`) | `2` (`Mir`, `Proof`) | `4` (`Captured`, `Spec`, `Proof`, `Expected`) + `1` (`TrustedBoundary`) |
| **Measured Lean Compile Time per `verify` (`v4.34.1`)** | — | **`8,600.21 ms`** (`7,154.61 ms` prefix + `1,445.60 ms` target) | **`8,600.21 ms`** cold (`1,445.60 ms` warm in-process) | **`1,463.78 ms`** (`0.441 ms` SHA-256 auth + `1,463.33 ms` target; **`5.88x` speedup**) |

Key architectural takeaways:
1. **Eliminating `7.15 s` (`83.2%`) of redundant per-run Lean compilation**: Recompiling the 7 `Trusted` and `Anneal` `.lean` sources from `include_str!` on every `cargo-anneal verify` invocation (Variant 2) spends `7,154.61 ms` out of `8,600.21 ms` (`83.2%` of total compilation time) rebuilding immutable model and theory modules. Precompiling those modules into `share/anneal/lib/lean/` during `nix build .#omnibus-archive` and authenticating their `.lean` and `.olean` SHA-256 digests against `library-lock.json` at runtime (Variant 4) takes `0.441 ms` and reduces total compilation time to `1,463.78 ms` (`5.88x` faster) while preserving identical cryptographic source-and-artifact admission guarantees.
2. **Eliminating test-binary self-re-execution (`install_archive_worker`)**: Adding an explicit `--install-dir <path>` option to `cargo-anneal setup` allows both users and integration tests (`installed_smoke`) to install an archive into an isolated directory via the real `cargo-anneal` binary, so `invocation.json` and `reproduce.py` record `cargo-anneal setup --local-archive <archive> --install-dir <dest>` instead of an ephemeral `target/debug/deps/installed_smoke-<hash>` test binary.

Basis: **source** and **execution** ([`support/toolchain-packaging-comparison/probe.py`](support/toolchain-packaging-comparison/probe.py), [`support/toolchain-packaging-comparison/results.json`](support/toolchain-packaging-comparison/results.json)).

## Boundaries

- **Known not to apply (`process_group(0)` against daemonized grandchildren calling `setsid`)**: Process-group signaling (`kill(-pgid, SIGKILL)`) terminates all descendants that remain in `pgid`; if an untrusted grandchild explicitly creates a new session or process group (`setsid()` or `setpgid(0, 0)`), killing the entire tree requires a Linux cgroup (`cgroup.kill` in cgroup v2, as used by `anneal-lean-run`) or PID namespace (`bwrap --unshare-pid`).
- **Known not to apply (`DT_RPATH` as a workaround for indirect dependencies of `DT_RUNPATH` libraries)**: Setting `DT_RPATH` (`--force-rpath` / `--disable-new-dtags`) on a main executable does not propagate to indirect dependencies loaded by an intermediate shared object that carries its own `DT_RUNPATH` (such as `libLLVM.so.22.1-rust-1.98.0-nightly`).
- **Not examined (macOS `proc_track_dirty` / kqueue or Windows Job Objects)**: The subprocess-tree supervision probes in `support/process-tree-supervision/` were executed on Linux `x86_64` (`prctl(PR_SET_CHILD_SUBREAPER)` is Linux-specific; macOS supports `process_group(0)` + `kill(-pgid, SIGKILL)` + `kill(-pgid, 0)` `ESRCH` polling).

## Evidence

All standalone probes, Rust/C sources, execution outputs, and offline verification scripts are preserved under `support/`:

1. **Subprocess-Tree Supervision and `reproduce.py` Signal Forwarding (`support/process-tree-supervision/`)**:
   - [`support/process-tree-supervision/supervisor_probe.rs`](support/process-tree-supervision/supervisor_probe.rs): Standalone Rust probe implementing Strategies A, B, C1, C2, and D across a 2-level process tree holding an exclusive `flock` lock.
   - [`support/process-tree-supervision/probe.py`](support/process-tree-supervision/probe.py), [`support/process-tree-supervision/results.json`](support/process-tree-supervision/results.json), and [`support/process-tree-supervision/check.py`](support/process-tree-supervision/check.py): Driver script and verified results for Strategies A..D and `reproduce.py` Cases E1, E2, E3a, and E3b.
2. **ELF `DT_RUNPATH` / `DT_RPATH` 5-Cell Matrix, `rustlib` Deduplication, and Nix `rust-lld` Sandbox Probe (`support/elf-runpath-and-nix-lld/`)**:
   - [`support/elf-runpath-and-nix-lld/probe.py`](support/elf-runpath-and-nix-lld/probe.py), [`support/elf-runpath-and-nix-lld/results.json`](support/elf-runpath-and-nix-lld/results.json), and [`support/elf-runpath-and-nix-lld/check.py`](support/elf-runpath-and-nix-lld/check.py): 5-cell synthetic 3-tier ELF shared-library probe (`main -> libmid.so -> libleaf.so -> libdep.so`), SHA-256 duplicate inventory of `rust/lib/` vs. `rust/lib/rustlib/x86_64-unknown-linux-gnu/lib/`, and `bwrap` Nix-sandbox reproducer for `rustc 1.98.0-nightly` with and without `-Clinker-features=-lld`.
3. **Toolchain Packaging Architecture Comparison and Precompiled `.olean` Benchmark (`support/toolchain-packaging-comparison/`)**:
   - [`support/toolchain-packaging-comparison/probe.py`](support/toolchain-packaging-comparison/probe.py), [`support/toolchain-packaging-comparison/results.json`](support/toolchain-packaging-comparison/results.json), and [`support/toolchain-packaging-comparison/check.py`](support/toolchain-packaging-comparison/check.py): Lean `v4.34.1` compilation benchmark comparing Variant 2 (per-run recompilation of 7 `Trusted`/`Anneal` prefix modules + 4 target modules) against Variant 4 (SHA-256 authentication of precompiled `share/anneal/lib/lean/` `.olean`s + 4 target modules).

## Revalidation

Run the three offline verification scripts (requiring only Python 3.10+ standard library) to validate all retained observations and invariants:

```sh
python3 support/process-tree-supervision/check.py
python3 support/elf-runpath-and-nix-lld/check.py
python3 support/toolchain-packaging-comparison/check.py
```

To re-run the live empirical probes on a Linux `x86_64` host with `rustc`, `cc`, `patchelf`, `bwrap`, and the pinned Nix store toolchains installed:

```sh
python3 support/process-tree-supervision/probe.py
python3 support/elf-runpath-and-nix-lld/probe.py
python3 support/toolchain-packaging-comparison/probe.py
```
