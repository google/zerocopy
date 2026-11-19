# Signed Git Commits, SHA-256 Object Migration, Gitsign, and Tarball Divergence

## Summary

Git commit and tag signatures authenticate the serialized bytes of a single Git object—and, transitively, the content-addressed DAG reachable from its `tree` and `parent` links—using `gpgsig` (SHA-1 object form) or `gpgsig-sha256` (SHA-256 object form) headers, OpenPGP armor, OpenSSH `SSHSIG` (`namespace = "git"`), or X.509 CMS/PKCS#7 envelopes (`sigstore/gitsign` backed by Fulcio ephemeral OIDC certificates and Rekor inclusion proofs). Because cryptographic signatures depend directly on the collision resistance of object identifiers, practical SHA-1 collisions undermine historical SHA-1 Merkle trees and motivate Git's `extensions.objectFormat = sha256` transition with bidirectional pack-index v3 and `loose-object-idx` mapping tables. Even with SHA-256 objects and valid signatures, commit and tag signatures alone do not authenticate branch/ref state, prevent ref rollbacks without server-verified signed push certificates (`git push --signed`), cover external submodule repository availability or `.gitmodules` URL bindings, or guarantee equivalence between a signed Git tree and release archives produced via `git archive` (`.gitattributes` `export-subst` / `export-ignore`) or out-of-tree `make dist` packaging (exemplified by XZ Utils `CVE-2024-3094`). Extended tree-checksumming tools (`git-evtag`, `ostree`) close archive-format ambiguity over tracked content, but distribution consumers must still verify either the tagged Git tree itself or an end-to-end build provenance attestation linking source tree to tarball.

## Applicability

This report examines source-tree integrity and object-signing semantics across five pinned repository snapshots and two foundational peer-reviewed specifications:

| Subject | Pinned Identity | Role in Analysis |
| --- | --- | --- |
| `git/git` | `e1ec09b23c8e0deb21a0b95ac5996422277395d4` | Commit/tag/mergetag signatures, `objectFormat = sha256` transition, `push-cert`, `git archive` attributes |
| `openssh/openssh-portable` | `fa4b2a82be7df9768272cfabc2d78e4a12c2b3c0` | `PROTOCOL.sshsig` binary wire format and domain-separated signing payload |
| `sigstore/gitsign` | `0366e85aa541a35abc8107a754b6690333c5fc35` | Keyless OIDC X.509 CMS verification and Rekor inclusion / legacy object-hash fallback |
| `cgwalters/git-evtag` | `34c930a5128ac90abe040e5d908f7c639f1680a2` | Recursive `Git-EVTag-v0-SHA512` tree and submodule object checksums |
| `ostreedev/ostree` | `d3fa64ae856cb682ba9e67f41c2b0e73ba6632b6` | SHA-256 `GVariant` content-addressed filesystem object schemas |
| CRYPTO 2017 (SHAttered) | `10.1007/978-3-319-63688-7_19` | Practical full SHA-1 collision parameters ($2^{63.1}$ compressions) |
| ACM CCS 2022 (Sigstore) | `10.1145/3548606.3560596` | Fulcio ephemeral OIDC certificates and Rekor transparency architecture |

Executed verification commands ran locally on Linux using Git `2.56.1` (`--object-format=sha256`), OpenSSH `10.6p1` (`ssh-keygen`), and Python `3.13.15`. Findings about `gpgsig-sha256` and `archive.c` generalize to modern Git implementations adhering to `Documentation/gitformat-signature.adoc` and `Documentation/technical/hash-function-transition.adoc`; `gitsign` verification findings apply specifically to the inspected Go codebase (`pkg/git/verify.go`).

## Findings

### 1. SHA-1 Collision Exposure and the `objectFormat = sha256` Transition

- **Merkle-DAG vulnerability under SHA-1 collisions** (`Basis: documentation`): Stevens et al. (CRYPTO 2017, `DOI: 10.1007/978-3-319-63688-7_19`) demonstrated the first identical-prefix collision for full SHA-1 at $2^{63.1}$ compression calls, and Leurent & Peyrin (USENIX Security 2020) lowered practical chosen-prefix SHA-1 collisions to commodity GPU budgets. Because a Git commit or tag signature binds only to serialized object headers containing 40-hex SHA-1 names (`tree <oid>`), an adversary holding two colliding blobs or subtrees with identical SHA-1 digest can substitute one object for another in an object store or fetch stream without invalidating any upstream `gpgsig` signature. Since Git `v2.13.0`, Git uses collision-detecting SHA-1 (`sha1dc`) by default to reject known cryptanalytic collision patterns, yet `Documentation/technical/hash-function-transition.adoc` notes that hardened SHA-1 remains fragile against undisclosed attacks and selects SHA-256 (64 hex chars) as Git's successor hash.
- **Repository format gating and content separation** (`Basis: normative + source`): A SHA-256 repository sets `core.repositoryFormatVersion = 1`, `extensions.objectFormat = sha256`, and optionally `extensions.compatObjectFormat = sha1` (`Documentation/technical/hash-function-transition.adoc:151-174`). Pre-extension Git clients fail closed (`Expected git repo version <= 0` or `unknown repository extensions found`). Blobs share identical raw bytes across both object formats because blobs contain no object references, whereas trees, commits, and tags embed referenced OIDs in 20-byte/40-hex (SHA-1) or 32-byte/64-hex (SHA-256) form (`hash-function-transition.adoc:192-204`). Invalid historical structures (e.g., non-canonical tree modes or unsorted tree entries) are preserved verbatim across format translation so conversions round-trip deterministically (`hash-function-transition.adoc:526-536`).
- **Bidirectional mapping tables and lookup complexity** (`Basis: normative + source`): When `compatObjectFormat = sha1` is active, Git maintains bidirectional SHA-1 <-> SHA-256 translation across two storage structures (`hash-function-transition.adoc:213-346`):

| Storage Layer | File Format / Location | Bidirectional Mapping Layout | Lookup Complexity & Caveats |
| --- | --- | --- | --- |
| Packed objects | `.idx` v3 (`\377t0c`, version `3`) | Sorted shortened OID tables + pack-order full OID tables for both formats + `PSRC` source tags (`1..5`, including `PACK_SOURCE_UNREACHABLE_GARBAGE = 4`) | $O(\text{packs} \times \log N_{\text{pack}})$ binary search; avoids loose-object fanout on `gc` |
| Loose objects | `$GIT_OBJECT_DIR/loose-object-idx` | Unsorted lines `(sha256-name SP sha1-name LF)*` guarded by `O_CREAT \| O_EXCL` `.lock` file | $O(N_{\text{loose}})$ linear scan; requires low loose-object count |

- **Topological rewriting on SHA-1 interoperability** (`Basis: normative`): Because converting a tree, commit, or tag from SHA-1 content to SHA-256 content requires substituting all child OIDs in the translation table, fetches from SHA-1 servers must index incoming objects, reverse-topologically sort non-blob objects, rewrite objects bottom-up into SHA-256 form, and discard extraneous unreachable objects (`hash-function-transition.adoc:364-390`). Pushes reverse this step using the local translation table (`hash-function-transition.adoc:405-412`). Signed payloads do not encode an explicit algorithm tag, relying solely on OID string length (`40` vs. `64` hex digits) to disambiguate object identifiers (`hash-function-transition.adoc:573-596`).

### 2. Signature Envelopes, Payload Canonicalization, and Keyless `gitsign`

- **Object embedding and stripping rules** (`Basis: normative + source + execution`): In `git/git`, signed objects store ASCII-armored detached signatures embedded directly inside the object bytes (`Documentation/gitformat-signature.adoc:17-57`, `commit.c:1147-1266`):
  1. **Commits (`gpgsig` / `gpgsig-sha256`)**: `add_header_signature` (`commit.c:1153-1158`) indexes `gpg_sig_headers[]` by hash algorithm (`"gpgsig"` for SHA-1, `"gpgsig-sha256"` for SHA-256), continuing multi-line headers with a leading `0x20` (`SP`) byte—including originally empty lines. A local `git init --object-format=sha256` execution probe confirms `commit` objects emit `gpgsig-sha256` even when `compatObjectFormat` is unset. During signing and verification (`commit.c:1250-1266`), Git strips *both* `gpgsig` and `gpgsig-sha256` header blocks so dual-signed commits sign identical non-signature payloads under their respective hash representations (`hash-function-transition.adoc:415-430`).
  2. **Tags and Mergetags**: Annotated tags (`git tag -s`) append the signature body after the unsigned tag message; dual-hashed tags keep the primary-format signature in-body and the compatibility-format signature in a `gpgsig` / `gpgsig-sha256` header (`hash-function-transition.adoc:431-445`). `git merge` of a signed tag embeds the entire signed tag verbatim (SP-continued) inside a `mergetag` commit header (`gitformat-signature.adoc:153-225`).
- **Cryptographic envelope formats (`gpg`, `ssh`, `x509`)** (`Basis: normative + source + execution`): `gitformat-signature.adoc:24-38` defines three signature families via `gpg.format`:

| `gpg.format` | Armor Delimiters | Signed Domain / Trust Anchor | Cross-Protocol Isolation Mechanism |
| --- | --- | --- | --- |
| `gpg` (OpenPGP) | `-----BEGIN PGP SIGNATURE-----` | Detached OpenPGP packet over raw stripped payload; Web of Trust / keyring fingerprint | OpenPGP signature type `0x00` binary document |
| `ssh` (`SSHSIG`) | `-----BEGIN SSH SIGNATURE-----` | `openssh-portable/PROTOCOL.sshsig:34-98`; verified via `gpg.ssh.allowedSignersFile` | 6-byte `"SSHSIG"` preamble + `namespace = "git"` string before `H(message)` (`sha256`/`sha512`) |
| `x509` (CMS/PKCS#7) | `-----BEGIN SIGNED MESSAGE-----` | `gpgsm` or `gitsign` CMS/PKCS#7 `SignedData` over stripped payload | X.509 EKU `id-kp-codeSigning` + Fulcio OIDC SAN / issuer extensions |

  Parsing the `SSHSIG` armoring generated by `git commit -S` with `gpg.format=ssh` in our execution probe verified exact field order (`PROTOCOL.sshsig:34-98`): `MAGIC_PREAMBLE` (`"SSHSIG"`), `SIG_VERSION` (`uint32 = 1`), serialized `ssh-ed25519` public key, `namespace` (`"git"`), empty `reserved` (`0` bytes), `hash_algorithm` (`"sha512"`), and the SSH signature over `b"SSHSIG" || string("git") || string("") || string("sha512") || string(SHA512(stripped_payload))`. Requiring a non-empty `namespace` prevents an SSH signature over a Git object from colliding with SSH user or host authentication transcripts (`PROTOCOL.sshsig:53-57, 89-91`).
- **Keyless OIDC `sigstore/gitsign` verification and SHA-256 asymmetry** (`Basis: source + documentation`): In Sigstore (`CCS 2022, DOI: 10.1145/3548606.3560596`), a signer exchanges an OIDC identity token with Fulcio for an ephemeral short-lived X.509 code-signing certificate binding OIDC `sub` and `issuer` extensions, signs the Git commit/tag payload as CMS/PKCS#7, and records the entry in Rekor so verifiers accept an expired certificate if Rekor's signed timestamp falls within `[NotBefore, NotAfter]`. Inspecting `sigstore/gitsign` (`pkg/git/verify.go:72-173`) shows two Rekor lookup paths:
  1. The primary path (`rekor.VerifyInclusion(ctx, sig, cert)` at `verify.go:81`) verifies inclusion directly from the signature and Fulcio certificate (or Sigstore bundle when `EnableSigstoreGo` is enabled).
  2. The legacy fallback (`verify.go:89-150`) calls `ObjectHashFromSignature(data, sig)` to reconstruct raw object bytes via `JoinCommit(&CommitSig{Payload: data, Gpgsig: sig})` or `JoinTag` and computes a `go-git/v5` SHA-1 object hash (`plumbing.MemoryObject`). Source comments (`verify.go:89-94`) explicitly observe that for `gpgsig-sha256` signatures there are no legacy Rekor object-hash entries and `ObjectHashFromSignature` assumes SHA-1 object formatting.

### 3. What Commit and Tag Signatures Fail to Authenticate

A valid signature on a commit or tag proves only that a holder of the signing key endorsed those exact serialized object bytes (and transitively whatever tree/parent objects uniquely hash to the embedded OIDs). Five structural repository and release boundaries fall outside commit/tag signature coverage:

| Boundary / Threat | Root Cause Outside Commit/Tag Payload | Mitigating Control |
| --- | --- | --- |
| **Branch rollback, deletion, or ref swap** | Refs (`refs/heads/*`, `refs/tags/*`) map refnames to OIDs outside signed objects; re-pointing `main` to an older validly signed commit leaves all commit signatures valid | `git push --signed` (`push-cert` nonce + `old-id new-id refname` commands verified in `pre-receive`, `git-receive-pack.adoc:70-120`) + signed transparency/ref logs |
| **Submodule drift & availability** | Parent tree `160000` gitlink stores only child commit OID; `.gitmodules` URL mutations or upstream submodule rewrites rely on unauthenticated mutable mappings and child hash strength | Pin `.gitmodules` review + verify child commit signatures recursively or via `git-evtag` |
| **`.gitattributes` `export-ignore` omissions** | `archive.c:131-145` filters tracked tree entries matching `export-ignore` out of `git archive` output without altering the committed `tree` OID | Compare archive file manifest against `git ls-tree -r` or avoid `export-ignore` on build-critical files |
| **`.gitattributes` `export-subst` mutation** | `archive.c:136` expands `$Format:...$` placeholders during `git archive`, causing tarball file bytes to differ from the signed Git `blob` OID | Prohibit `export-subst` on executable/parsed files or attest the archive digest directly |
| **Out-of-tree `make dist` packaging (`CVE-2024-3094`)** | Autotools `make dist` tarballs inject generated `configure` and `m4` artifacts omitted from Git; a malicious release tarball can embed payload triggers invisible in signed Git tags | Build releases directly from verified Git trees, inspect diffs between `git archive` and release tarballs, or attest reproducible builds |

In our execution probe on a signed SHA-256 commit (`adbc53ea19c3361f4d87272d17f00f987e16fb2fb80a955dab2cdba2364f8875`), the Git tree contained `excluded.txt`, a `160000` gitlink (`deps/sub` -> `1f800cd4...`), and literal `version = "$Format:%H$"` in `version.py`, whereas `git archive --format=tar HEAD` dropped `excluded.txt`, emitted an empty `deps/sub/` directory, and rewrote `version.py` to `version = "adbc53ea19c3361f4d87272d17f00f987e16fb2fb80a955dab2cdba2364f8875"`. Only the tar PAX global header recorded the commit OID (`git get-tar-commit-id`), which itself carries no signature independent of the repository.

### 4. Extended Recursive Tree Checksums (`git-evtag` and `ostree`)

- **`cgwalters/git-evtag` (`Git-EVTag-v0-SHA512`)** (`Basis: source`): To strengthen SHA-1 Git tags against blob/tree collisions and replace non-reproducible release tarballs (`README.md:3-85`), `git-evtag` embeds a `Git-EVTag-v0-SHA512: <128-hex>` line inside a GPG-signed annotated tag (`src/git-evtag.c:34`). Walking from the target commit (`checksum_commit_contents`, `src/git-evtag.c:299-335`), it feeds canonical Git object headers (`"<type> <size>\0"`) plus raw object bodies (`checksum_odb_object`, `src/git-evtag.c:176-210`) sequentially into SHA-512 across the commit object, root tree, and preorder `GIT_TREEWALK_PRE` children (`checksum_tree_callback`, `src/git-evtag.c:247-296`). When encountering a `GIT_OBJ_COMMIT` tree entry (submodule gitlink), `checksum_submodule` (`src/git-evtag.c:338-374`) opens the initialized submodule working repository and hashes `git_submodule_wd_id(sub)` recursively—implying that submodule-bearing tags cannot be computed or verified on bare repositories without checked-out, clean (`status_cb`, `src/git-evtag.c:456-474`) submodule worktrees.
- **`ostreedev/ostree` content-addressed SHA-256 trees** (`Basis: source`): Rather than hashing tar byte streams whose compression and header padding vary across tool versions, `ostree` separates filesystem data from POSIX metadata inside immutable SHA-256 `GVariant` objects (`src/libostree/ostree-core.h:49-155`). Regular files and symlinks live in `.file` objects (`OSTREE_OBJECT_TYPE_FILE = 1`), POSIX uid/gid/mode/xattrs live in `.dirmeta` `(uuua(ayay))` (`OSTREE_OBJECT_TYPE_DIR_META = 3`), directory trees map filenames and subdirectories to 32-byte SHA-256 digests in `.dirtree` `(a(say)a(sayay))` (`OSTREE_OBJECT_TYPE_DIR_TREE = 2`), and signed `.commit` objects `(a{sv}aya(say)sstayay)` bind root tree contents, root tree metadata, parents, and detached commit metadata (`.commitmeta`) under canonical `GVariant` serialization.

## Boundaries

- **Known not to apply**:
  - Standard `git verify-commit` and `git verify-tag` do not authenticate branch-head freshness, tag-name binding to a specific refname (`git tag -s` embeds the tag string inside the tag object, but does not prevent omitting or delaying tag updates on remotes), or `git archive` tarball byte equivalence when `.gitattributes` `export-ignore` or `export-subst` rules exist (`archive.c:131-145`, confirmed by execution probe).
  - `sigstore/gitsign`'s `ObjectHashFromSignature` legacy Rekor lookup path (`pkg/git/verify.go:89-150`) assumes 20-byte SHA-1 Git objects via `go-git/v5` and does not apply to `gpgsig-sha256` commits.
- **Unsupported**:
  - In `git/git` (`Documentation/technical/hash-function-transition.adoc:538-549`), SHA-256 repositories with `compatObjectFormat = sha1` do not support shallow clones/fetches, unfetched submodules, or `objects/info/alternates` borrowing across SHA-1 and SHA-256 object stores because full topological translation tables are required locally.
  - `cgwalters/git-evtag` (`src/git-evtag.c:348-364, 456-474`) requires a clean working directory (`--force-unclean` otherwise) and initialized submodules (`git submodule update --init`) when submodules are present; verification over a bare object store with submodules is unsupported.
- **Not examined**:
  - Wire-level Git protocol v2 native SHA-256 negotiation behavior across specific third-party hosting providers, and `sigstore/gitsign`'s experimental `EnableSigstoreGo` bundle path outside `pkg/git/verify.go`.

## Evidence

- **Normative specifications & peer-reviewed papers**:
  - `git/git` @ `e1ec09b23c8e0deb21a0b95ac5996422277395d4`: `Documentation/gitformat-signature.adoc` (lines 1–229), `Documentation/technical/hash-function-transition.adoc` (lines 1–650), `Documentation/git-receive-pack.adoc` (lines 60–125), `Documentation/gitprotocol-pack.adoc` (lines 535–578).
  - `openssh/openssh-portable` @ `fa4b2a82be7df9768272cfabc2d78e4a12c2b3c0`: `PROTOCOL.sshsig` (lines 1–100).
  - Marc Stevens, Elie Bursztein, Pierre Karpman, Ange Albertini, Yarik Markov, *"The First Collision for Full SHA-1"*, CRYPTO 2017 (`DOI: 10.1007/978-3-319-63688-7_19`).
  - Gaëtan Leurent and Thomas Peyrin, *"SHA-1 is a Shambles: First Chosen-Prefix Collision on SHA-1 and Application to the PGP Web of Trust"*, USENIX Security 2020.
  - Zachary Newman, John Speed Meyers, Santiago Torres-Arias (`Sigstore`), *"Sigstore: Software Signing for Everybody"*, ACM CCS 2022 (`DOI: 10.1145/3548606.3560596`).
- **Source inspection**:
  - `git/git` @ `e1ec09b23c8e0deb21a0b95ac5996422277395d4`: `commit.c` (`gpg_sig_headers`, `add_header_signature`, signature extraction/stripping at lines 1147–1266); `archive.c` (`get_archive_attrs` at lines 131–144).
  - `sigstore/gitsign` @ `0366e85aa541a35abc8107a754b6690333c5fc35`: `pkg/git/verify.go` (`Verify`, `ObjectHashFromSignature`, `ObjectHash` at lines 72–173).
  - `cgwalters/git-evtag` @ `34c930a5128ac90abe040e5d908f7c639f1680a2`: `README.md` (lines 1–180) and `src/git-evtag.c` (`EVTAG_SHA512`, `checksum_odb_object`, `checksum_tree_callback`, `checksum_commit_contents`, `checksum_submodule`, `status_cb` at lines 34, 176–374, 456–474).
  - `ostreedev/ostree` @ `d3fa64ae856cb682ba9e67f41c2b0e73ba6632b6`: `src/libostree/ostree-core.h` (`OSTREE_SHA256_DIGEST_LEN`, `OstreeObjectType`, `OSTREE_DIRMETA_GVARIANT_FORMAT`, `OSTREE_TREE_GVARIANT_FORMAT`, `OSTREE_COMMIT_GVARIANT_FORMAT` at lines 49–170).
- **Execution probe (`2026-11-19`)**:
  - Local probe running `git init --object-format=sha256`, `ssh-keygen -t ed25519`, `git commit -S` (`gpg.format=ssh`), binary `SSHSIG` parsing, and `git archive --format=tar HEAD` inspection produced:
    `HEAD_OID=adbc53ea19c3361f4d87272d17f00f987e16fb2fb80a955dab2cdba2364f8875`, `HEADER_NAME=gpgsig-sha256`, `SSHSIG_MAGIC=SSHSIG VERSION=1 NS=git RESERVED_LEN=0 HASH_ALG=sha512 BLOB_CONSUMED=True`, `TAR_MEMBERS=['.gitattributes', 'deps', 'deps/sub', 'version.py']`, `PAX_COMMIT_ID_MATCHES_HEAD=True`, `BLOB_VERSION_PY=version = "$Format:%H$"`, `TAR_VERSION_PY=version = "adbc53ea19c3361f4d87272d17f00f987e16fb2fb80a955dab2cdba2364f8875"`.

## Revalidation

To revalidate Git SHA-256 signature headers, `SSHSIG` payload framing, and `git archive` divergence on a newer Git or OpenSSH toolchain:

```bash
tmpdir=$(mktemp -d)
ssh-keygen -t ed25519 -N "" -f "$tmpdir/k" -C "probe@example.org" >/dev/null
echo "probe@example.org $(cat "$tmpdir/k.pub")" > "$tmpdir/allowed"
git init --object-format=sha256 "$tmpdir/r" >/dev/null
git -C "$tmpdir/r" config user.name Probe
git -C "$tmpdir/r" config user.email probe@example.org
git -C "$tmpdir/r" config gpg.format ssh
git -C "$tmpdir/r" config gpg.ssh.program ssh-keygen
git -C "$tmpdir/r" config user.signingkey "$tmpdir/k"
git -C "$tmpdir/r" config gpg.ssh.allowedSignersFile "$tmpdir/allowed"
printf 'v = "$Format:%%H$"\n' > "$tmpdir/r/v.py"
printf 'v.py export-subst\nskip.txt export-ignore\n' > "$tmpdir/r/.gitattributes"
printf 'ignored\n' > "$tmpdir/r/skip.txt"
git -C "$tmpdir/r" add v.py .gitattributes skip.txt
SSH_AUTH_SOCK="" git -C "$tmpdir/r" commit -S -m test >/dev/null
git -C "$tmpdir/r" verify-commit HEAD
git -C "$tmpdir/r" cat-file commit HEAD | grep -E '^(gpgsig|gpgsig-sha256) '
git -C "$tmpdir/r" archive HEAD | tar -t
git -C "$tmpdir/r" archive HEAD v.py | tar -xO
rm -rf "$tmpdir"
```

Revalidation passes if `git verify-commit HEAD` succeeds, `gpgsig-sha256` appears as the commit signature header, `skip.txt` is absent from `tar -t`, and `v.py` in the archive expands `$Format:%H$` to the 64-hex SHA-256 commit OID while `git cat-file blob HEAD:v.py` retains the literal `$Format:%H$` string. For `gitsign`, inspect `pkg/git/verify.go` (`ObjectHashFromSignature` and `VerifyInclusion`) on newer commits to check whether SHA-256 `gpgsig-sha256` reconstruction has been added.
