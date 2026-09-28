# Lean 4.30.0-rc2 `linux_aarch64` bundled leantar anomaly

## Summary

Reinspection of the official Lean 4.30.0-rc2 linux_aarch64 archive confirmed its bundled `bin/leantar` is x86-64, while the separately released aarch64 leantar is AArch64. The foreign binary was inspected but never executed.

## Applicability

The exact upstream Lean and leantar release assets are identified by URL, size, and SHA-256; ELF machine IDs were read from extracted helper headers on macOS arm64. Related corpus reports: [lean-lake-cross-platform-artifact-portability-v4-30-0-rc2](../lean-lake-cross-platform-artifact-portability-v4-30-0-rc2/REPORT.md), [leantar-archive-format-v0-1-16-v0-1-19](../leantar-archive-format-v0-1-16-v0-1-19/REPORT.md).

## Findings


Revalidated 2026-09-27. **Confirmed:** the official Lean 4.30.0-rc2 `linux_aarch64` archive contains an x86-64 `bin/leantar`. The separately released `aarch64-unknown-linux-musl` leantar is an AArch64 ELF. No foreign binary was executed, and this investigation did not invoke Nix.

### Scope and sources

- The local flake is [`anneal/flake.nix`](https://github.com/google/zerocopy/blob/bd0956be95c5f798f0c0484921b9b9d1fc6e9988/anneal/flake.nix). It selects `linux_aarch64` for Lean on `aarch64-linux`, separately fetches leantar v0.1.16 for `aarch64-unknown-linux-musl`, and comments on the bundled x86-64 helper at lines 372–375.
- Official Lean [release page](https://github.com/leanprover/lean4/releases/tag/v4.30.0-rc2) and [release metadata](https://api.github.com/repos/leanprover/lean4/releases/tags/v4.30.0-rc2) identify the archive, size, and SHA256. The flake URL at `https://releases.lean-lang.org/lean4/v4.30.0-rc2/lean-4.30.0-rc2-linux_aarch64.tar.zst` returned HTTP 302 to the official GitHub release asset URL below.
- Official leantar [v0.1.16 release metadata](https://api.github.com/repos/digama0/leangz/releases/tags/v0.1.16) identifies the separate native asset, size, and SHA256.
- The already installed macOS Lean 4.30.0-rc2 `bin/leantar` is Mach-O arm64 (`file`) with SHA256 `9bddd23bcddf44b27cf3a79e38dde45c53278721980695abdc76587fc3c89d41`. This shows the local Darwin installation is native, but does not itself establish the Linux archive contents.

### Budget and procedure

Before downloading, `df -h` showed 78 GiB available on the project volume. `memory_pressure -Q` reported 8 GiB total RAM and 48% system-wide memory free. The upstream Lean archive was listed at **529,196,053 bytes**, and the separate leantar archive at **1,103,097 bytes**. Both fit the 1 GiB added-disk budget. The four scratch files total **535,456,366 bytes** of payload (about 511 MiB); `du -ch` reports 519 MiB allocated. They are under `tmp/lean-archive-anomaly/`.

Commands used (the `tar` operations read only the named member, rather than unpacking the full Lean tree):

```sh
curl -fL --retry 2 --max-time 180 --max-filesize 600000000 \
  -o tmp/lean-archive-anomaly/lean-4.30.0-rc2-linux_aarch64.tar.zst \
  https://github.com/leanprover/lean4/releases/download/v4.30.0-rc2/lean-4.30.0-rc2-linux_aarch64.tar.zst
sha256sum tmp/lean-archive-anomaly/lean-4.30.0-rc2-linux_aarch64.tar.zst
zstd -dc tmp/lean-archive-anomaly/lean-4.30.0-rc2-linux_aarch64.tar.zst | tar -tf - | rg '(^|/)leantar$|(^|/)bin/lean$'
zstd -dc tmp/lean-archive-anomaly/lean-4.30.0-rc2-linux_aarch64.tar.zst | \
  tar -xOf - lean-4.30.0-rc2-linux_aarch64/bin/leantar > tmp/lean-archive-anomaly/bundled-leantar
curl -fL --retry 2 --max-time 30 --max-filesize 2000000 \
  -o tmp/lean-archive-anomaly/leantar-v0.1.16-aarch64-unknown-linux-musl.tar.gz \
  https://github.com/digama0/leangz/releases/download/v0.1.16/leantar-v0.1.16-aarch64-unknown-linux-musl.tar.gz
tar -xOf tmp/lean-archive-anomaly/leantar-v0.1.16-aarch64-unknown-linux-musl.tar.gz \
  leantar-v0.1.16-aarch64-unknown-linux-musl/leantar > tmp/lean-archive-anomaly/native-aarch64-leantar
file tmp/lean-archive-anomaly/{bundled-leantar,native-aarch64-leantar}
sha256sum tmp/lean-archive-anomaly/{bundled-leantar,native-aarch64-leantar}
```

The pipeline extraction was run with `set -o pipefail`. The archive listing also found `lean-4.30.0-rc2-linux_aarch64/bin/lean`; it was not extracted. The ELF `e_machine` values below were read from header bytes 18–19 with Python, without executing either helper.

### Direct evidence

| Item | Path or URL | Size | SHA256 | Identity |
| --- | --- | ---: | --- | --- |
| Official Lean archive | [GitHub asset](https://github.com/leanprover/lean4/releases/download/v4.30.0-rc2/lean-4.30.0-rc2-linux_aarch64.tar.zst) | 529,196,053 B | `b196f41da23960e842fc0fc04749d1639d44839feafc0414e53cb2db6b16790f` | Matches release metadata exactly |
| Bundled helper | `lean-4.30.0-rc2-linux_aarch64/bin/leantar` | 2,653,464 B | `89ef0c3bd2c40e727191bcd406ef3dac95e0b9000ac93cb7f8c681031ad486be` | ELF 64-bit little-endian, x86-64, static PIE, `e_machine=62` |
| Native leantar archive | [GitHub asset](https://github.com/digama0/leangz/releases/download/v0.1.16/leantar-v0.1.16-aarch64-unknown-linux-musl.tar.gz) | 1,103,097 B | `26eb775436883e3d5cdad27af35b9c37212c73106316863ea1fc5f8ec2cc9de4` | Matches release metadata and flake `aarch64-linux` `pkgs.fetchurl` hash |
| Native helper | `leantar-v0.1.16-aarch64-unknown-linux-musl/leantar` | 2,503,752 B | `d99c68938b90d323ca4987ffb31d42d717e7a2dbd2148d1870c0b36542a637e9` | ELF 64-bit little-endian, AArch64, static, `e_machine=183` |

The bundled helper's tar entry is executable (`-rwxr-xr-x`) and is dated 2026-03-16. The standalone native helper's tar entry is executable and dated 2025-10-23. A byte comparison found that the two extracted helpers differ. The data proves an architecture mismatch in the bundled helper; it does not establish why upstream packaged it this way or the bundled helper's source version.

### Flake consistency

- The flake constructs `lean-4.30.0-rc2-{linux,linux_aarch64,darwin,darwin_aarch64}.tar.zst` URLs. All four names appear in the official Lean release metadata. The `releases.lean-lang.org` URL for `linux_aarch64` redirects to the corresponding GitHub release asset.
- The four flake `leantarPlatform` names map to four assets in the official leantar v0.1.16 release. Decoding each `leantarSha256` SRI value to hex matched that asset's published SHA256: `x86_64-linux` `2cbc40ca…fbd3d1`, `aarch64-linux` `26eb7754…cc9de4`, `x86_64-darwin` `e7c78d60…65996c`, `aarch64-darwin` `b5b590d2…ee5e35`. The downloaded aarch64 archive independently matched its published digest.
- All four `leanToolchainSha256` strings decode to 32-byte SHA256 values. The flake uses `outputHashMode = "recursive"` for the **extracted output tree**, so those values cannot be compared to the published SHA256 of the compressed Lean archives. Their correctness as Nix output hashes was not revalidated in this no-Nix investigation.
- The flake's comment and use of the separately fetched leantar for Mathlib cache unpacking are consistent with the observed archive contents. This check did not assess whether any other helper in the archive has the wrong architecture.

### Recommendation

Keep the explicit native leantar dependency. For future toolchain updates, add a setup or research-prompt step that checks the archive's `bin/leantar` member with `file` or ELF `e_machine` before using it, records the upstream archive digest and the helper digest, and preserves the no-execution rule for foreign binaries. If a new Lean release is confirmed to ship a native helper, the workaround can be reconsidered for that version. Confidence in this specific v4.30.0-rc2 anomaly is high because the downloaded archive digest matches official release metadata and the architecture is verified independently by `file` and ELF header bytes.

## Boundaries

The report does not establish why upstream packaged the helper this way, whether other helpers are mismatched, or whether newer releases corrected it. Nix was not invoked; the flake was read only to check its workaround and hashes.

## Evidence

This report's subject identities are recorded in `REPORT.json`. Source links in the Findings are pinned to immutable upstream or zerocopy revisions where available. The upstream archive is not mirrored because it is large; its official URL/hash and the extracted helper identities are recorded in `support/archive-identities.json`.

## Revalidation

Download only the pinned archive; verify its whole-archive SHA-256 against official release metadata; list and extract `bin/leantar` without executing; inspect ELF `e_machine` and compare with the native leantar asset. Repeat for each new Lean release.
