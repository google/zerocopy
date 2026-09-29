# I094 installed Lean/Lake upgrade-candidate inventory

## Result

At reference commit `40b3024d5a3c73357abb6e90f10fcaf713768cd4`, a read-only local inventory found no Lean/Lake tuple later than the examined `v4.30.0-rc2` pin in the installed tool bundle or local Nix store. The bundle contains `v4.29.0` and `v4.30.0-rc2`; 4.29 is earlier. The one Lean toolchain path in `/nix/store` is `4.30.0-rc2`, and its `lean` and `lake` executable hashes match the bundled 4.30 pair. The Aeneas release and source `backends/lean/lean-toolchain` files both select `leanprover/lean4:v4.30.0-rc2`.

This is an **absence finding within inspected local installation locations**, not proof that no compatible later release exists. I094 remains **partial**. Its requested comparison of Lake ownership and read-only behavior at the examined 4.30 pin versus a deliberately selected later compatible tuple was not run. The exact version-specific workaround and stable architectural requirement cannot be separated by this inventory alone.

## Installed identities

| Location | Lean SHA-256 | Lake SHA-256 |
| --- | --- | --- |
| Bundled Elan `v4.29.0` | `2974847fff2e2621502841f4c2dbac4035b4847d6060a4f2087cbc0d04005e37` | `0e56506385ec20d56bffd7c031c4d48573ab5fdb74e5246ec8c45a220bebc68b` |
| Bundled Elan `v4.30.0-rc2` | `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997` | `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb` |
| Nix store `wf1mr6pak9n88v5bwm6y749d8k19r0mw-lean-toolchain-aarch64-darwin-4.30.0-rc2` | `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997` | `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb` |

The local Nix-store name search also returned `leantar-aarch64-darwin-0.1.16`, which is not a Lean/Lake tuple. `/Users/josh/.elan/toolchains` was absent. The inventory did not inspect unrelated project roots, user services, remote caches, or remote release availability.

## Evidence and method

[`support/inventory.json`](support/inventory.json) retains seven exact local discovery commands, their working directories and exits, normalized stdout/stderr, and hashes of the normalized streams. Commands used only `git rev-parse`, `find`, `test -d`, `shasum`, and `cat`. Paths in outputs are normalized to `$TOOLS`, `$NIX_STORE`, and `$USER_HOME`; each command's exact absolute arguments remain recorded. [`support/collect.py`](support/collect.py) is the capture specification. It performed no flake query/evaluation, build, download, install, cache preparation, or Lean/Lake execution. No `.local/` path was inspected.

The inventory is bounded to the installed Elan toolchains under the local Anneal tool bundle, the `/nix/store` top-level directories whose names contain `lean`, the two local Aeneas pin files, and the existence check for the usual home Elan toolchain directory. A store directory whose name does not contain `lean`, or another installation outside these locations, is outside the finding. The Nix store was listed directly; Nix was not invoked.

## Revalidation

Run `python3 -B support/check.py` from this package directory. It checks the retained command/output hashes, exact tuple inventory, executable identities, matching Nix/bundle 4.30 pair, Aeneas pins, and report metadata without rerunning discovery or modifying installed state. `support/collect.py` can recapture the local state deliberately, but would replace `support/inventory.json`; it is not part of the offline check. A later upgrade comparison requires an explicitly chosen compatible tuple and a separate controlled experiment.
