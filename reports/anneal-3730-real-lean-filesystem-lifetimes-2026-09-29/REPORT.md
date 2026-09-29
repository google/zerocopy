# Real Lean artifact path identity and reader lifetimes on APFS and overlayfs

## Summary

A pinned Lean 4.30.0-rc2 compiled two distinct `Dep.olean` generations and a separate `Plugin.olean` containing a tactic macro. On the Mac's APFS data volume, fresh Lean processes resolved symlink, hardlink, relative, case, and Unicode directory aliases. A resident Lean process that had already imported generation 7 returned `7` after an atomic path replacement with generation 9; a fresh process imported and proved against generation 9. An open file descriptor and read-only `mmap` continued to read generation 7 after replacement and unlink, while a fresh import failed during the missing-path interval. Republishing generation 9 restored fresh imports; the old hardlink still imported generation 7.

The same compiled `.olean` bytes were copied into the cached Ubuntu 24.04 container's overlayfs, where open and mapped readers retained generation 7 through replacement and unlink. Distinct case and Unicode spellings stayed distinct there. The container did not have Lean, so this is a byte-level overlayfs lifetime test of real Lean artifacts. Lean on the host accepted both generations after their round trip through overlayfs. This bounded slice addresses [#3731](https://github.com/google/zerocopy/issues/3731) I123/I124 and the corresponding [#3730](https://github.com/google/zerocopy/issues/3730) L14 filesystem identity/lifetime concern; it establishes no Anneal implementation behavior.

## Fixture and identities

The host was macOS 26.6.2 arm64, 8 GiB RAM, with the experiment on `/System/Volumes/Data` (APFS). The exact Lean binary SHA-256 was `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, from pinned `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`). `Dep7.olean` is 4,552 bytes, SHA-256 `7ae5507721d0d228cfdb0c2399d6ef858bc918e48376470954b3600e40862cb3`; `Dep9.olean` is 4,456 bytes, SHA-256 `0f0fbd523ef1ce3fce88465a688f7a786beb38969ff690b97c51778d5da30ec0`. `Plugin.olean`, containing a Lean `probe_decide` tactic macro, is 45,272 bytes, SHA-256 `24d1cf9fcaa36b2d918eb2985e517153a537958e7f4393bfbf768966a2084bbc`. This is a Lean macro extension, not a native dynamic library.

Each consumer imports `Dep` and `Plugin`, proves the selected `depValue` with `probe_decide`, and evaluates the value. The probe invokes fresh `lean --json` processes with explicit `LEAN_PATH` roots. The resident process imports both modules before signalling readiness and sleeping. The separate reader opens and maps the **actual compiled** `Dep.olean` before replacement. The staged replacement is moved over the path in the same directory; this tests one successful rename schedule, not crash durability or universal atomicity.

The container used the already cached image `ubuntu:24.04`, image ID `sha256:224a1869083a311ef3f13648a154ba79832fbef6364d31493642ca03082da254`, as `linux/amd64` on the arm64 OrbStack host. `/tmp` reported `overlayfs`. It was capped at 512 MiB and one CPU, run with `--pull=never --network=none`, and populated by `docker cp`; no image pull, install, or host bind mount occurred. The process was removed on completion. The Linux reader uses the x86-64 `mmap`/`munmap` syscalls and reads mapped bytes through `/proc/self/mem`.

## Observations

| Surface | Before replacement | After replacement | After unlink |
| --- | --- | --- | --- |
| APFS fresh Lean | All tested `LEAN_PATH` aliases imported generation 7; the proof exited 0 and `#eval` returned 7. | New pathname imported generation 9 and proved the 9 theorem; the old 7 theorem failed. The resident Lean process later returned 7. | Fresh import failed because `Dep.olean` was absent. After republishing, the 9 theorem passed; the hardlink to the old inode still proved 7. |
| APFS open fd and `mmap` | Both held the 7 artifact inode. | Both yielded the generation 7 hash while the pathname yielded the generation 9 hash. | Both still yielded the generation 7 hash while the pathname did not exist. |
| Ubuntu overlayfs open fd and `mmap` | Both held genuine generation 7 `.olean` bytes. | The pathname yielded generation 9; all mapped and fd snapshots yielded generation 7. | The pathname was absent; mapped and fd snapshots again yielded generation 7. |

On APFS, `Case` and `case` resolved to the same directory, as did NFC `é` and NFD `e\u0301`; each alternate spelling successfully served as a `LEAN_PATH` root. The directory symlink, hardlink directory, and relative `LEAN_PATH=live` also passed. The hardlink and live `Dep.olean` initially shared device/inode `16777229/24422673` with link count 2. After replacement, the new pathname had inode `24422690`; the old hardlink still referred to `24422673` with link count 1. These numbers describe this run, not portable cache identifiers. On overlayfs, `Case`/`case` and the two Unicode spellings were distinct (`case=0 unicode=0`). The symlink and hardlink were created there; no Linux Lean import was run against them.

Copies of the overlayfs new pathname, old hardlink, and plugin returned to APFS with their original hashes. Fresh host Lean processes then proved the generation 9 and generation 7 theorems against their respective round-tripped files. This confirms byte preservation and host acceptability after the overlayfs exercise; it does not substitute for a Linux Lean loader test.

## Exact coverage and residuals

| Issue item | Evidence added | Still unresolved |
| --- | --- | --- |
| I123: path and alias identity | Real Lean batch import through APFS relative, symlink, hardlink, case, and Unicode roots; case/Unicode distinction observed on overlayfs; device/inode and hashes tracked across replacement. | Canonicalization inside an Anneal cache key, editor URI/document routing, live server session aliasing, Linux Lean module import, network volumes, and collision behavior across mixed normalization policies. |
| I124: publication and reader lifetimes | One APFS resident Lean import and open/mapped `.olean` reader survive same-directory rename and unlink; fresh Lean changes to generation 9, fails when absent, then succeeds after republish. Overlayfs open/mapped reader repeats the byte-level transition. | Native/plugin `.dylib` loader behavior, filesystem locks, multi-reader schedules, deletion while indexers or antivirus hold files, Windows and network filesystems, process crash or power-loss durability, garbage-collection policy, and Linux native Lean loader behavior. |

Neither the APFS nor overlayfs result proves a general lock-free publication scheme. An implementation still needs to define its path keys, generation ownership, and cleanup boundary, and test its actual consumers. No backup volume was accessed.

## Evidence and replay

`support/results.json` (SHA-256 `282d27c4d5c0db7c7827abb0ec267adbfae7c82872abd9d9c664df4cd36f0e40`) retains 54 labelled commands/process records, exits, output, artifact identities, aliases, filesystem facts, and reader phase hashes. `support/artifacts/` retains both compiled generations, the tactic extension, APFS reader phase JSON, republished bytes, overlayfs round-trip bytes, and four overlayfs reader snapshots. All four snapshots have generation 7's SHA-256; the round-tripped new file has generation 9's SHA-256.

Replay with `python3 support/probe.py --work /absolute/absent/owned/path`, from this package, on the documented host with the pinned Lean binary and cached Ubuntu image. The work path must be absent and its parent must have at least 15 GiB free. The script's assertions check every critical exit, value, and hash, and clean up its container in a `finally` block. It intentionally regenerates `support/results.json` and `support/artifacts/`, so copy the package first when preserving the recorded run. Timing and temporary inode numbers will vary.

Source SHA-256: `support/probe.py` `e83dbaad6a5e5133bb540692aa36f48d63c71ad022108c462e2444f0143585b0`; `support/host_reader.py` `936e9bd93a5d84d6b3709eb16b642a957220cbc11e32ee9261daad138a3a59ac`; `support/overlay_reader.pl` `646ddddeca7af22902c08b89946dc7135b26fd766702ce7ba093da92d873b8a7`.
