# `bwrap`, User-Namespace Restrictions, Docker, and Landlock Confinement on GitHub-Hosted Ubuntu Runners

## Summary

- **`bwrap --unshare-all` does NOT work out-of-the-box on GitHub-hosted `ubuntu-24.04` runners:** `actions/runner-images` leaves Ubuntu 24.04's `kernel.apparmor_restrict_unprivileged_userns = 1` intact, does not preinstall `bubblewrap`, and Ubuntu 24.04 (`noble`/`noble-updates`) ships neither `/etc/apparmor.d/bwrap` nor `/etc/apparmor.d/bwrap-userns-restrict` (which arrives only in Ubuntu 25.04+/26.04 `resolute`). Unprivileged `bwrap` therefore fails after `apt-get install bubblewrap` unless the workflow runs `sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0` or installs a path-matching AppArmor profile.
- **Non-`/usr/bin/bwrap` binaries fail even on Ubuntu 25.04+/26.04:** AppArmor attachment is strictly path-based, so `/nix/store/<hash>-bubblewrap-<ver>/bin/bwrap` or static custom-path binaries remain `unconfined` and are blocked whenever `kernel.apparmor_restrict_unprivileged_userns = 1`. On Ubuntu 26.04, `/etc/apparmor.d/bwrap-userns-restrict` also stacks children into `unpriv_bwrap` (`audit deny capability,`), breaking *nested* `bwrap`.
- **`bwrap` inside a standard (non-`--privileged`) Docker container is blocked by five independent layers:** Docker's default seccomp profile gates `unshare`/`clone(CLONE_NEW*)`/`mount`/`umount2` on `CAP_SYS_ADMIN` and **unconditionally omits `pivot_root` even WITH `--cap-add=SYS_ADMIN`**; `docker-default` AppArmor enforces `deny mount,`; default containers drop `CAP_SYS_ADMIN`; `MaskedPaths`/`ReadonlyPaths` overmounting `/proc` breaks `bwrap --proc /proc`; and Ubuntu 24.04's host `kernel.apparmor_restrict_unprivileged_userns = 1` still traps unconfined containers lacking `CAP_SYS_ADMIN`. In GitHub Actions `container:` jobs, the container starts before any host step can lower host `sysctl`, and `actions/runner` forces `--network github_network_<guid>` (conflicting with `--network=none`).
- **Landlock (ABI v4–v8) + `seccomp-bpf` works inside a stock unprivileged Docker container with zero extra flags:** `moby/moby` unconditionally permits `landlock_create_ruleset`, `landlock_add_rule`, `landlock_restrict_self`, `prctl`, and `seccomp` in Rule #0 of `default.json` (since Docker 23.0; `ubuntu-24.04` runs Docker `28.0.4` on kernel `7.0.0-1017-azure`, corresponding to Landlock ABI v8). Landlock alone cannot remap/hide paths, scrub env/FDs, hide `/proc`, or block UDP/raw sockets on Linux `6.8`–`7.0`; pairing it with a `CLONE_THREAD`-preserving `seccomp-bpf` filter closes network and `ptrace` gaps, while host-step `docker run --network=none --read-only --mount type=bind,readonly` provides full namespace isolation with zero `sysctl` changes.

## Applicability

This report characterizes the interaction of:

1. **GitHub-hosted `ubuntu-24.04` runner images** (`actions/runner-images@0e63d4f9d2c29043b4cf1d2f40d1812a7cde1369`, image `20261116.376.1`: Ubuntu `24.04.5 LTS`, kernel `7.0.0-1017-azure`, Docker `28.0.4`) and **`actions/runner`** (`7e211dc69c347b78fc398e630e74facb11a13235`).
2. **Docker / Moby container defaults** (`moby/moby@8b0c45e42959ea5322cfb33bfb97a40ed64d4a07`, `docker/cli@01a20278d3603af41da9a1b62c0d942d67066672`) and **`containers/bubblewrap`** (`1fb0aa26d3eb66254f7742e704add7f82f41a582`).
3. **Ubuntu `apparmor` / `bubblewrap` packaging** (`noble`, `noble-updates`, and `resolute` filelists) and **Linux kernel Landlock LSM** (`torvalds/linux` tags `v6.8`, `v6.10`, `v6.12`, `v6.15`, `v7.0`).

Findings apply to Linux CI runners (specifically GitHub-hosted `ubuntu-24.04` and Docker Engine `>= 23.0`). Ubuntu `noble` vs. `resolute` (`26.04`) differences and Linux `v6.8` vs. `v7.0` Landlock ABI differences are stated explicitly.

## Findings

### 1. `bwrap` and User Namespaces on GitHub-Hosted `ubuntu-24.04` Runners

Basis: source (`actions/runner-images@0e63d4f9`, `packages.ubuntu.com`, `containers/bubblewrap@1fb0aa26`, upstream AppArmor `unprivileged_userns`) + derived

1. **Zero runner-image overrides:** Inspecting `images/ubuntu/templates/build.ubuntu-24_04.pkr.hcl` and `images/ubuntu/scripts/build/{configure-system.sh,configure-limits.sh,install-docker.sh,install-container-tools.sh,install-apt-common.sh,install-apt-vital.sh}` confirms `actions/runner-images` applies **no** `sysctl` or AppArmor overrides for user namespaces. Runners therefore inherit Ubuntu 24.04's default **`kernel.apparmor_restrict_unprivileged_userns = 1`** (transitioning unconfined unprivileged `CLONE_NEWUSER` callers into `/etc/apparmor.d/unprivileged_userns`, which enforces `audit deny capability,` and `audit deny change_profile,`). Note that `kernel.unprivileged_userns_clone` is the legacy Debian/older-Ubuntu switch, not Ubuntu 24.04's enforcement mechanism.
2. **`bubblewrap` is not preinstalled and Ubuntu 24.04 ships no `bwrap` AppArmor profile:**
   - Neither `images/ubuntu/toolsets/toolset-2404.json` nor `images/ubuntu/Ubuntu2404-Readme.md` includes `bubblewrap`.
   - On `packages.ubuntu.com`, `noble`/`noble-updates` `bubblewrap` ships only `/usr/bin/bwrap`, completions, and `bwrap.1.gz`, and `noble`/`noble-updates` `apparmor` ships profiles for `flatpak`, `podman`, `buildah`, `crun`, `runc`, `opam`, `mmdebstrap`, etc., but **no** `/etc/apparmor.d/bwrap` or `/etc/apparmor.d/bwrap-userns-restrict`.
   - `/etc/apparmor.d/bwrap-userns-restrict` arrives in Ubuntu 25.04+ / 26.04 (`resolute`, `apparmor` package).
3. **Failure mode and host-level mitigations:**
   - Invoking `bwrap --unshare-all` (which already sets `opt_unshare_net = true` at `bubblewrap.c:1874-1876`, making `--unshare-net` redundant) calls `raw_clone(CLONE_NEWUSER | ...)` (`bubblewrap.c:3059, 3115`), transitions into `unprivileged_userns`, and fails at UID-map or loopback setup (`Permission denied` / `Failed RTM_NEWADDR: Operation not permitted`).
   - On ephemeral GitHub-hosted `ubuntu-24.04` VMs (which grant passwordless `sudo`), workflows must either run:
     ```bash
     sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0
     ```
     or install a targeted AppArmor profile matching the binary path (e.g., `abi <abi/4.0>, profile bwrap /usr/bin/bwrap flags=(unconfined) { userns, }` loaded with `sudo apparmor_parser -r`).
4. **Non-`/usr/bin/bwrap` binaries and Ubuntu 26.04 nested-sandbox trap:**
   - AppArmor attachment is strictly path-based. A Nix-store binary (`/nix/store/<hash>-bubblewrap-<ver>/bin/bwrap`) or custom static `bwrap` binary does **not** match `/usr/bin/bwrap` and fails even on Ubuntu 26.04 unless `kernel.apparmor_restrict_unprivileged_userns = 0` or a matching path glob (e.g., `/nix/store/*-bubblewrap-*/bin/bwrap`) is installed.
   - On Ubuntu 26.04, `bwrap-userns-restrict` stacks spawned children into `unpriv_bwrap` (`audit deny capability,`), allowing single-level `/usr/bin/bwrap` while breaking *nested* `bwrap` or inner user-namespace sandboxes.

### 2. `bwrap` Inside a Standard (Non-`--privileged`) Docker Container

Basis: normative + source (`moby/moby@8b0c45e4`, `docker/cli@01a20278`, `containers/bubblewrap@1fb0aa26`, `actions/runner@7e211dc6`) + derived

Five independent layers block `bwrap --unshare-all` inside a default Docker container on `ubuntu-24.04`:

1. **Docker default seccomp (`vendor/github.com/moby/profiles/seccomp/default.json` & `default_linux.go`):**
   - `defaultAction: SCMP_ACT_ERRNO` (`EPERM`).
   - `unshare`, `mount`, `umount`, `umount2`, `setns`, `fsopen`, `fsconfig`, `fsmount`, `move_mount`, `open_tree` (Rule #44, `default_linux.go:783-813`) require `CAP_SYS_ADMIN`.
   - `clone` (Rule #45, `default_linux.go:818-837`) blocks mask `0x7e020000` (all 7 `CLONE_NEW*` flags) without `CAP_SYS_ADMIN`; `clone3` (Rule #47, `default_linux.go:862-871`) returns `ENOSYS`.
   - **`pivot_root` is completely absent from `default.json` even WITH `CAP_SYS_ADMIN`.** Because `bwrap` unconditionally calls `pivot_root(base_path, "oldroot")` (`bubblewrap.c:3322`) and `pivot_root(".", ".")` (`bubblewrap.c:3366`), **`--cap-add=SYS_ADMIN` alone cannot unblock `bwrap` under Docker's default seccomp profile.**
2. **Docker default AppArmor (`docker-default`, `vendor/github.com/moby/profiles/apparmor/template.go:74`):** Enforces `deny mount,`, unconditionally blocking `bwrap`'s bind/`tmpfs`/`proc` mounts even inside a child user+mount namespace and even with `CAP_SYS_ADMIN`.
3. **Default capabilities (`daemon/pkg/oci/caps/defaults.go:4-21`):** Default containers receive 14 capabilities excluding `CAP_SYS_ADMIN`. (`bwrap`'s `prctl(PR_SET_NO_NEW_PRIVS, 1, ...)` at `bubblewrap.c:2928` is allowed unconditionally in Rule #0.)
4. **`MaskedPaths` & `ReadonlyPaths` (`daemon/pkg/oci/defaults.go:109-116, 194-219`):** Overmounted `/proc/*` paths trigger Linux's `mnt_already_visible` / `MNT_LOCKED` rejection when `bwrap --proc /proc` mounts a fresh `procfs` (`Can't mount proc on /newroot/proc: Operation not permitted`), requiring `--security-opt systempaths=unconfined` (`docker/cli` `cli/command/container/opts.go:972-983`) or dropping `--proc /proc`.
5. **Host `kernel.apparmor_restrict_unprivileged_userns = 1`:** Even with `--security-opt seccomp=unconfined --security-opt apparmor=unconfined`, a container process lacking `CAP_SYS_ADMIN` in the initial user namespace still hits Ubuntu 24.04's host userns restriction.

| Host `apparmor_restrict_unprivileged_userns` | Minimal Docker Flags (Without `--privileged`) | Trade-Off |
| :--- | :--- | :--- |
| **`0`** (after host `sysctl -w ...=0`, or Debian) | `--security-opt seccomp=unconfined --security-opt apparmor=unconfined` *(+ `--security-opt systempaths=unconfined` for `--proc /proc`)* | No `CAP_SYS_ADMIN` needed; a custom seccomp profile allowing `pivot_root`/`unshare`/`clone`/`mount`/`umount2` can replace `seccomp=unconfined`. |
| **`1`** (default `ubuntu-24.04`, no host sysctl change) | `--security-opt seccomp=unconfined --security-opt apparmor=unconfined --cap-add=SYS_ADMIN` *(+ `--security-opt systempaths=unconfined` for `--proc /proc`)* | Near-`--privileged` host-escape surface for the outer container. |

**GitHub Actions `container: options:` constraints (`actions/runner@7e211dc6`):**
- `DockerCommandManager.DockerCreate` (`src/Runner.Worker/Container/DockerCommandManager.cs:132`) passes `container.ContainerCreateOptions` verbatim to `docker create` (no flag sanitizer).
- **Host-sysctl timing trap:** The job container starts *before* any workflow `steps:` execute, so a `container:` job cannot lower host `sysctl` beforehand.
- **`--network=none` conflict:** `ContainerOperationProvider.cs:96-104` unconditionally creates `github_network_<guid>` and `DockerCommandManager.cs:122` emits `--network github_network_<guid>`, conflicting with `--network=none` in `container: options:`. Use `docker run --network=none ...` from a normal host step instead.

### 3. Alternatives: Landlock (+ `seccomp-bpf`) vs. Docker `--mount` + `--network=none` vs. `bwrap`

Basis: normative + source (`moby/moby@8b0c45e4`, `torvalds/linux` `v6.8`–`v7.0`) + derived

- **Landlock works inside a stock unprivileged Docker container with ZERO extra flags:** Verified in `moby/moby@8b0c45e4` (`default.json:198-200, 269, 322`; `default_linux.go:380-382, 451`; added in `moby/moby#43199`, Docker 23.0+): `landlock_create_ruleset`, `landlock_add_rule`, `landlock_restrict_self`, `prctl`, and `seccomp` are all unconditionally allowed in **Rule #0 (`SCMP_ACT_ALLOW`)** with no capability gates and no `docker-default` AppArmor restriction.
- **Landlock ABI versions (`torvalds/linux`, `security/landlock/syscalls.c` & `Documentation/userspace-api/landlock.rst`):** `v6.8` → ABI v4 (FS + `FS_REFER` + `FS_TRUNCATE` + TCP `BIND_TCP`/`CONNECT_TCP`), `v6.10` → ABI v5 (`FS_IOCTL_DEV`), `v6.12` → ABI v6 (`SCOPE_ABSTRACT_UNIX_SOCKET`, `SCOPE_SIGNAL`), `v6.15` → ABI v7 (audit flags), `v7.0` (matching GHA `ubuntu-24.04`'s `7.0.0-1017-azure`) → ABI v8. Landlock enforces a hard cap of 16 stacked ruleset layers (`E2BIG` on layer 17).

| Dimension | `bwrap --unshare-all --ro-bind ...` | Host-Step `docker run --network=none --read-only --mount type=bind,readonly` | Landlock *(alone)* / Landlock + `seccomp-bpf` |
| :--- | :--- | :--- | :--- |
| **Works on GHA `ubuntu-24.04` host OOTB?** | **No** (`apt-get install bubblewrap` + `sysctl` or AppArmor profile required) | **Yes** (Docker `28.0.4` preinstalled) | **Yes** (no `sudo`, no `sysctl`) |
| **Works inside default Docker container OOTB?** | **No** (5 blocking layers above) | N/A (is the container boundary) | **Yes** (Rule #0 of Docker default seccomp; zero extra flags) |
| **FS read/write confinement** | Strong (mount-namespace allowlist) | Strong (container rootfs + explicit RO bind mounts) | Strong (path-hierarchy allowlist) |
| **Path hiding / remapping** | **Yes** (`ENOENT` for unmounted paths; arbitrary remapping) | **Yes** (only mounted paths exist; arbitrary remapping) | **No** (returns `EACCES`, not `ENOENT`; no remapping) |
| **Network isolation** | **Complete** (`CLONE_NEWNET`, loopback-only) | **Complete** (`--network=none`, loopback-only) | **Landlock alone:** TCP only on Linux `6.8`–`7.0` (UDP/raw not blocked). **+ `seccomp-bpf`:** blocking `SYS_socket`/`SYS_connect` blocks TCP, UDP, raw, and `AF_UNIX`. |
| **PID / `/proc` / `ptrace` / signal isolation** | **Yes** (`CLONE_NEWPID`, `--proc /proc`, `CLONE_NEWIPC`) | **Yes** (PID/IPC/UTS namespaces + `docker-default`) | **Landlock alone:** ABI v6+ scopes signals & abstract Unix sockets, but does not hide `/proc` or block `ptrace`. **+ `seccomp-bpf`:** blocks `ptrace`/`process_vm_readv`/`fork` while preserving `CLONE_THREAD`. |
| **Env / FD scrubbing** | Built-in (`--clearenv`, `--setenv`) | Built-in (fresh container) | Caller must scrub `envp` and close FDs before `execve` |
| **Granularity** | Per-subprocess (~few ms) | Per-container (~100–500 ms startup) | Per-subprocess (~few ms) |

## Boundaries

- **Live GitHub-hosted `ubuntu-24.04` kernel Landlock boot configuration (`not examined` by live execution):** Source analysis confirms `ubuntu-24.04` image `20261116.376.1` boots kernel `7.0.0-1017-azure` (ABI v8 upstream) and Ubuntu's `linux-azure` kernels enable Landlock by default since 22.04/24.04, but a live `landlock_create_ruleset(NULL, 0, LANDLOCK_CREATE_RULESET_VERSION)` syscall probe was not executed on a live GitHub Actions VM.
- **Non-Ubuntu Linux runners (`not examined`):** Debian, Fedora, and custom self-hosted runners may differ in `kernel.apparmor_restrict_unprivileged_userns` or preinstalled `bubblewrap` profiles.
- **Podman / Buildah inside `ubuntu-24.04` (`not examined`):** While `ubuntu-24.04` preinstalls Podman `4.9.3` with `/etc/apparmor.d/podman`, rootless Podman sub-confinement was not evaluated as a `bwrap` substitute.
- **Stronger conclusions not established:** Neither `bwrap` nor Landlock + `seccomp-bpf` replaces a hardware-virtualized microVM boundary for adversarial untrusted code running alongside host secrets (all share the host Linux kernel).

## Evidence

All evidence was gathered on `2026-11-21`:

- **`actions/runner-images@0e63d4f9d2c29043b4cf1d2f40d1812a7cde1369`:** `images/ubuntu/Ubuntu2404-Readme.md` (image `20261116.376.1`, Ubuntu `24.04.5 LTS`, kernel `7.0.0-1017-azure`, Docker `28.0.4`), `images/ubuntu/toolsets/toolset-2404.json`, `images/ubuntu/templates/build.ubuntu-24_04.pkr.hcl`, and `images/ubuntu/scripts/build/{configure-system.sh,configure-limits.sh,install-docker.sh,install-container-tools.sh,install-apt-common.sh,install-apt-vital.sh}` (zero userns `sysctl`/AppArmor overrides; no `bubblewrap`).
- **Ubuntu package filelists (`packages.ubuntu.com`, queried `2026-11-21`):** `noble`/`noble-updates` `bubblewrap` and `apparmor` (no `/etc/apparmor.d/bwrap*`); `resolute` `apparmor` (`/etc/apparmor.d/bwrap-userns-restrict`).
- **`containers/bubblewrap@1fb0aa26d3eb66254f7742e704add7f82f41a582`:** `bubblewrap.c` L1874–1876 (`--unshare-all` sets `opt_unshare_net`), L2928 (`PR_SET_NO_NEW_PRIVS`), L3059/3115 (`raw_clone`), L3322/3366 (mandatory `pivot_root`).
- **`moby/moby@8b0c45e42959ea5322cfb33bfb97a40ed64d4a07`:** `vendor/github.com/moby/profiles/seccomp/default.json` (Rule #0 L198–200 `landlock_*`, L269 `prctl`, L322 `seccomp`; absence of `pivot_root`) & `default_linux.go` (L380–382, L451, L783–813, L818–837, L862–871); `vendor/github.com/moby/profiles/apparmor/template.go` (L74 `deny mount,`); `daemon/pkg/oci/caps/defaults.go` (L4–21); `daemon/pkg/oci/defaults.go` (L109–116, L194–219).
- **`docker/cli@01a20278d3603af41da9a1b62c0d942d67066672`:** `cli/command/container/opts.go` (L972–983, `--security-opt systempaths=unconfined`).
- **`actions/runner@7e211dc69c347b78fc398e630e74facb11a13235`:** `src/Runner.Worker/Container/DockerCommandManager.cs` (L110–147, verbatim `ContainerCreateOptions`, `--network`), `src/Runner.Worker/ContainerOperationProvider.cs` (L96–104, `github_network_<guid>`).
- **`torvalds/linux` (`v6.8`, `v6.10`, `v6.12`, `v6.15`, `v7.0`):** `security/landlock/syscalls.c` (`LANDLOCK_ABI_VERSION` / `landlock_abi_version`) and `Documentation/userspace-api/landlock.rst` (16-layer stack cap).

## Revalidation

1. **GitHub-hosted runner `sysctl` / `bwrap` / Landlock live check:** Run a 5-line step on `ubuntu-24.04` (and `ubuntu-26.04` / `ubuntu-latest`):
   ```bash
   sysctl kernel.apparmor_restrict_unprivileged_userns || true
   ls -la /etc/apparmor.d/*bwrap* || true
   python3 -c 'import ctypes; libc=ctypes.CDLL(None); print("landlock_abi:", libc.syscall(444, 0, 0, 1))'
   ```
2. **Docker default seccomp & AppArmor drift:** Diff `vendor/github.com/moby/profiles/seccomp/default_linux.go` (checking `pivot_root` and `landlock_*`) and `vendor/github.com/moby/profiles/apparmor/template.go` (`deny mount,`) in `moby/moby` against `8b0c45e42959ea5322cfb33bfb97a40ed64d4a07`.
3. **`actions/runner` `container:` behavior:** Diff `src/Runner.Worker/Container/DockerCommandManager.cs` and `ContainerOperationProvider.cs` against `7e211dc69c347b78fc398e630e74facb11a13235`.
