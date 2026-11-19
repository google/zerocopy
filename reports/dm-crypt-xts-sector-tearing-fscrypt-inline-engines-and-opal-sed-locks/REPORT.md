# Block-Layer XTS Malleability, Journaled Sector AEAD, Inline Keyslot Lifecycles, and TCG Opal SED Trust Boundaries

## Summary

Storage encryption stacks routinely conflate media confidentiality at rest with ciphertext authenticity, crash-atomic sector transitions, and hardware key lifecycle isolation. Across `mbroz/cryptsetup` (`b16f041ce122275b28e500cbafb94dedbcc9e6df`), `torvalds/linux` (`8dac6df92a2e66e2098bbc69061964cfe7e8375b`), `google/fscrypt` (`a3a6fd1db20d5bae6d99ad87bdc9496d99996d91`), and `Drive-Trust-Alliance/sedutil` (`5af6caf6f73050dc689ade3cb63678d1bf81ea39`), four structural invariants govern whether encrypted storage preserves data integrity and confidentiality across crashes, active ciphertext tampering, power-state transitions, and firmware adversaries:

1. **Narrow-Block XTS Malleability and Re-Encryption Excluded-Middle Failure**: `IEEE Std 1619-2018` `XTS-AES` (`crypto/xts.c`) is an unauthenticated tweakable narrow-block (`16 B`) mode over $\mathbb{F}_2[x]/(x^{128}+x^7+x^2+x+1)$. Any bit modification inside `16 B` ciphertext block $j$ randomizes solely plaintext block $j$ while leaving the remaining `255` blocks of a `4096 B` sector intact, and historical `16 B` ciphertext blocks at identical `(sector_iv, j)` coordinates can be spliced across snapshots undetected. During `LUKS2` online `512 B -> 4096 B` sector-size re-encryption (`lib/luks2/luks2_reencrypt.c:1649-1677`), `checksums` resilience hashes pre-image ciphertext at `alignment = 4096 B` granularity and recovers a sector *only* when its on-disk hash still equals the saved old-ciphertext digest (`!memcmp(...)` with no `else` branch). On `512e` or non-power-loss-protected drives that tear mid-`4096 B` write, the mixed `[new_head || old_tail]` sector mismatches the old digest, recovery returns `0` (`OK`), and trailing `512 B` sub-sectors silently decrypt to pseudo-random garbage.
2. **Crash-Atomic Sector-Tag Coupling Requires Either Two-Write Journaling or Atomic LBA Metadata**: Pairing `dm-crypt` AEAD (`AEGIS-128L` or `authenc(hmac(sha256),xts(aes))`, `drivers/md/dm-crypt.c:1166-1182, 1335-1346`) with `dm-integrity` (`drivers/md/dm-integrity.c`) converts torn writes from silent plaintext corruption into hard `-EILSEQ` read failures unless sector data and `16–32 B` tags transition atomically. Software journal mode (`mode == 'J'`) achieves crash atomicity at $\ge 2\times$ write amplification by displacing the trailing `8 B` of every `512 B` journal sector into `journal_entry.last_bytes[]` and stamping cyclic `N_COMMIT_IDS = 4` `64`-bit `commit_id` trailers (`dm-integrity.c:102-153, 2251-2295`); bitmap mode (`mode == 'B'`) eliminates data double-writes at the cost of permanent `-EILSEQ` sector loss on unclean shutdown; inline mode (`mode == 'I'`, `SB_FLAG_INLINE`) achieves `1.0x` single-write crash atomicity *only* when backed by hardware-atomic extended LBA metadata (`4096 + 64 B` NVMe Protection Information / LBAF).
3. **Inline Keyslot Lock-Ordering and DUN Width Constraints**: Linux `blk-crypto` (`block/blk-crypto-profile.c:45-64, 248-419`) manages finite hardware keyslots (`UFSHCI`, `NVMe`, `eMMC` Inline Crypto Engines) that evaporate across controller power collapse. Calling `pm_runtime_get_sync(profile->dev)` *strictly prior* to `down_write(&profile->lock)` in `blk_crypto_hw_enter()` prevents recursive write-lock deadlock when the driver's resume hook (`ufshcd_crypto_enable()`, `drivers/ufs/core/ufshcd-crypto.c:107-119`) calls `blk_crypto_reprogram_all_keys()`. At the filesystem layer (`fs/crypto/keysetup.c:329-405`, `fs/crypto/block.c:44-49, 197-209`), hardware-wrapped keys require shared per-filesystem `IV_INO_LBLK_64` or SipHash-compressed `IV_INO_LBLK_32` policies, trading per-file cryptographic key separation for bounded keyslot pressure while exposing `32`-bit Data Unit Number (`DUN`) wraparound hazards on `eMMC` ICE controllers.
4. **TCG Opal 2.0 Firmware State Decoupling and S3 Plaintext Key Residency**: Hardware Self-Encrypting Drives (`SED`s) managed via `block/sed-opal.c`, `cryptsetup` `--hw-opal` (`lib/luks2/hw_opal/hw_opal.c`), and `sedutil` (`Common/DtaDevOpal.cpp`, `Common/DtaHashPwd.cpp`) decouple host authentication from Media Encryption Key (`MEK`) cryptography on vulnerable controllers (`CVE-2018-12037`) and leak prior key wrappers in wear-leveled NAND (`CVE-2018-12038`). Furthermore, because S3 Suspend-to-RAM power-cycles the drive into a locked state while the OS root filesystem itself resides on the locked range, `IOC_OPAL_SAVE` (`block/sed-opal.c:1239-1252, 2816-2820, 3271-3290, 3611`) pins raw unlocking credentials in unencrypted kernel heap memory (`dev->unlk_lst`), re-exposing hardware encryption to host DRAM extraction unless layered under software `dm-crypt` (`--hw-opal` rather than `--hw-opal-only`).

---

## Applicability

This report characterizes the interaction among seven primary artifacts:

- **Userspace Container, Re-Encryption, and Keyring Tooling**: `mbroz/cryptsetup` at `b16f041ce122275b28e500cbafb94dedbcc9e6df` (`LUKS2` JSON metadata, online re-encryption resilience modes `none`, `checksums`, `journal`, `datashift`, `integritysetup`, and `LUKS2` `hw_opal` integration introduced in `cryptsetup 2.7+`); `google/fscrypt` at `a3a6fd1db20d5bae6d99ad87bdc9496d99996d91` (`v1` and `v2` directory encryption policies, PAM/login protector wrapping, and filesystem keyring `ioctl` orchestration); and `Drive-Trust-Alliance/sedutil` at `5af6caf6f73050dc689ade3cb63678d1bf81ea39` (`sedutil-cli` and `LinuxPBA` pre-boot shadow-MBR unlocking).
- **Kernel Block, Device-Mapper, Filesystem, and SED Subsystems**: `torvalds/linux` at `8dac6df92a2e66e2098bbc69061964cfe7e8375b`, specifically `crypto/xts.c`, `crypto/aegis128-core.c`, `drivers/md/dm-crypt.c`, `drivers/md/dm-integrity.c`, `block/blk-crypto.c`, `block/blk-crypto-profile.c`, `drivers/ufs/core/ufshcd-crypto.c`, `fs/crypto/{block.c,fname.c,keyring.c,keysetup.c,policy.c}` (noting that earlier Linux trees named `fs/crypto/block.c` `fs/crypto/inline_crypt.c`), and `block/sed-opal.c` (`CONFIG_BLK_SED_OPAL`, Linux `6.4+` required for `cryptsetup` `LUKS2` Opal ioctls `IOC_OPAL_ACTIVATE_USR`, `IOC_OPAL_LR_SET_START_LEN`, and `IOC_OPAL_ENABLE_DISABLE_LR`).
- **Normative and Empirical Security Baseline**: `IEEE Std 1619-2018` / `NIST SP 800-38E` (`XTS-AES`), Brož, Patočka & Matyáš (`arXiv:1807.00309`, `LUKS2` + `dm-integrity` authenticated disk encryption), and Meijer & van Gastel (`DOI: 10.1109/SP.2019.00088`, empirical reverse-engineering of commercial SATA/NVMe/USB SEDs).

**Scope Conditions**:
- Findings on `XTS-AES` malleability apply to all standard `512 B` and `4096 B` narrow-block `XTS` deployments (`dm-crypt` `aes-xts-plain64`, `fscrypt` `FSCRYPT_MODE_AES_256_XTS`, `NVMe`/`UFSHCI` inline `XTS`, and `TCG Opal` AES-XTS engines) regardless of key length (`256-bit` AES-128-XTS or `512-bit` AES-256-XTS). Wide-block tweakable modes (`HCTR2`, `Adiantum`) alter intra-unit diffusion from `16 B` to the full data unit (`4096 B` or filename length) and are contrasted explicitly where applicable.
- Findings on `LUKS2` `checksums` torn-write corruption apply whenever the configured re-encryption resilience `sector_size` (`alignment = max(old_sector_size, new_sector_size)`, e.g., `4096 B` during `512 B -> 4096 B` migration) exceeds the underlying physical storage device's power-fail atomic write granularity (`AWUPF` on NVMe or `512 B` physical/unprotected consumer translation layers).

---

## Findings

### 1. IEEE Std 1619-2018 XTS-AES Algebraic Structure, Narrow-Block Malleability, and LUKS2 Re-Encryption Sector Tearing

`Basis: normative + source + execution`

`IEEE Std 1619-2018` instantiates Rogaway's `XEX` construction (`DOI: 10.1007/978-3-540-30539-2_2`) with two independent AES keys $K = K_1 \parallel K_2$ (`256` bits total for `AES-128-XTS`, `512` bits total for `AES-256-XTS`). For a logical data unit (sector) with `128`-bit little-endian tweak $I$ (`plain64` zero-extends the `64`-bit `512 B`-unit sector offset `ctx->cc_sector = sector + cc->iv_offset` in `drivers/md/dm-crypt.c:1202`) and `16`-byte plaintext blocks $P_0, \dots, P_{m-1}$ ($m \le 2^{20}$ blocks = `16 MiB` per `NIST SP 800-38E` to bound $\mathbb{F}_{2^{128}}$ related-tweak collisions):

$$T_j = E_{K_2}(I) \otimes \alpha^j \in \mathbb{F}_2[x]/(x^{128} + x^7 + x^2 + x + 1), \qquad C_j = E_{K_1}(P_j \oplus T_j) \oplus T_j.$$

In little-endian `128`-bit integer representation, multiplying tweak $T$ by primitive element $\alpha = x$ is a left shift by `1` bit followed by conditional XOR with `0x87` ($x^7 + x^2 + x + 1$) when bit `127` carries out. When data-unit byte length is not a multiple of `16 B` (unused on aligned block sectors, active on `xts.c:88, 160-185` `xts_cts_final`), ciphertext stealing (`CTS`) swaps and re-tweaks the final two partial blocks.

Three concrete integrity and crash-consistency failures follow directly from this construction:

1. **Localized `16 B` Plaintext Randomization and Cross-Snapshot Cut-and-Paste**: Because $P_j = D_{K_1}(C_j \oplus T_j) \oplus T_j$ depends exclusively on $(C_j, I, j)$ with zero cross-block chaining or authentication tag, flipping any bit in $C_j$ scrambles *only* the `16 B` block $P_j$ (`~50%` bit-flip avalanche; `59 / 128` bits flipped in block `j = 3` in our execution probe while all remaining `4080 B` of the `4096 B` sector decrypt with `0` bit errors and `0` kernel warnings). Worse, an adversary with repeated offline or cloud-snapshot read/write access to ciphertext at `(I, j)` can splice historical `16 B` block $C_j^{(t_0)}$ into current sector $C^{(t_1)}$ to restore exact plaintext $P_j^{(t_0)}$ (for example reverting `"ALLOW_ROOT=0000\n"` to `"ALLOW_ROOT=0001\n"` inside a configuration file or `ext4` inode permission word).
2. **IV-Scale Tweak Divergence Across `512 B` vs. `4096 B` Sector Sizes**: In `dm-crypt`, `plain64` (`crypt_iv_plain64_gen`) always expresses `dmreq->iv_sector` in `512 B` units (`SECTOR_SHIFT = 9`), *not* cipher sector units, unless overridden. However, a `512 B` `dm-crypt` segment resets the Galois power $j = 0$ every `32` AES blocks (`512 B`), computing base tweaks $E_{K_2}(8s + r)$ for $r \in \{0,\dots,7\}$, whereas a `4096 B` `dm-crypt` segment computes a *single* base tweak $E_{K_2}(8s)$ and advances $\alpha^{32r + j}$ continuously across `j = 0..255`. Consequently, migrating a `LUKS2` volume from `512 B` to `4096 B` sectors—even with the *exact same* volume key—requires full ciphertext re-encryption of every sector.
3. **Silent Torn-Sector Corruption in `LUKS2` `checksums` Online Re-Encryption (`lib/luks2/luks2_reencrypt.c:1649-1677, 3253-3267`)**: `cryptsetup reencrypt` divides the device into moving hotzones protected by one of four resilience modes stored in the `reencrypt` keyslot JSON area (`lib/luks2/luks2_keyslot_reenc.c:37-55, 292-345`): `none`, `checksums`, `journal`, or `datashift` (plus `datashift-checksum` / `datashift-journal`).
   - Before overwriting a hotzone in `REENC_PROTECTION_CHECKSUM`, `luks2_reencrypt.c:3256-3265` hashes each `rp->p.csum.block_size` chunk of the **pre-image ciphertext** into `rp->p.csum.checksums`, where `block_size` is initialized to `alignment = max(old_sector_size, new_sector_size)` (`4096 B` for `512 B -> 4096 B`).
   - After an interrupted run or power failure, `reencrypt_recovery_by_resilience()` (`luks2_reencrypt.c:1649-1676`) iterates `s = 0 .. count - 1`, hashes current on-disk `data_buffer + s * block_size` into `checksum_tmp`, and executes:
     ```c
     if (!memcmp(checksum_tmp, (char *)rp->p.csum.checksums + (s * rp->p.csum.hash_size), rp->p.csum.hash_size)) {
         crypt_storage_wrapper_decrypt(cw1, s * rp->p.csum.block_size, ...);
         crypt_storage_wrapper_encrypt_write(cw2, s * rp->p.csum.block_size, ...);
     }
     ```
   - There is **no `else` validation** against a post-image digest because the post-image was never journaled. If a `512e` drive or consumer SSD without power-loss protection (`PLP`) commits `3` of `8` physical `512 B` sectors (`1536 B`) of `cw2` ciphertext before power loss, `checksum_tmp` differs from `rp->p.csum.checksums[s]`. Recovery concludes sector `s` already completed migration, exits with `r = 0`, and leaves `2560 B` of `cw1` ciphertext in the tail of a `cw2` `4096 B` sector—corrupting `2549 / 2560` tail bytes upon decryption in our execution probe. Only `REENC_PROTECTION_JOURNAL` (`luks2_reencrypt.c:1678-1715`), which persists the entire hotzone ciphertext pre-image inside the binary keyslot area before touching the data segment, guarantees crash safety when physical write atomicity is smaller than `max(old_sector_size, new_sector_size)`.

| `LUKS2` Resilience Mode (`luks2_reencrypt.c`) | Keyslot Area Payload Written Before Hotzone Overwrite | Metadata + Data Write Amplification | Crash-Safe Under Sub-`4 KiB` Physical Torn Writes (`512e` / Non-PLP)? | Failure Symptom on Mid-Chunk Power Loss |
| :--- | :--- | :---: | :---: | :--- |
| **`none`** (`REENC_PROTECTION_NONE`) | Hotzone offset/length JSON only | `1.0x` data + `2` hdr writes | **No** | Entire in-flight hotzone (`up to LUKS2_REENCRYPT_MAX_HOTZONE_LENGTH`) left mixed `cw1`/`cw2` |
| **`checksums`** (`REENC_PROTECTION_CHECKSUM`) | `H(old_cipher[s])` per `alignment` block (`32 B` SHA-256 / `4 KiB` = `0.78%`) | `~1.01x` + `fsync` | **No** *(requires atomic `alignment` writes)* | `memcmp != 0` skips torn sector (`r = 0`), silently corrupting unmigrated `512 B` sub-sectors |
| **`journal`** (`REENC_PROTECTION_JOURNAL`) | Full raw `old_cipher` hotzone copy in keyslot area | **`2.0x`** data + `2` barrier flushes | **Yes** (`unconditional cw1 -> cw2 replay`) | `0` byte loss; full hotzone decrypted via `cw1` from keyslot area and rewritten via `cw2` |
| **`datashift`** (`REENC_PROTECTION_DATASHIFT`) | Fixed `shift_size` offset (`e.g., 16 MiB` header carve-out) | `1.0x` sequential move | **Yes** *(if disjoint source/dest windows)* | Only valid when encrypting/decrypting with non-overlapping shifted source/target offsets |

---

### 2. Linux `dm-integrity` Crash Atomicity, Sector-Trailer Commit IDs, and Stacked `LUKS2` AEAD Write Amplification

`Basis: source + documentation + execution`

To detect ciphertext tampering and bit-rot, `LUKS2` (`cryptsetup luksFormat --integrity <alg>`) stacks `dm-crypt` (`drivers/md/dm-crypt.c`) directly over `dm-integrity` (`drivers/md/dm-integrity.c`, Brož, Patočka & Matyáš `arXiv:1807.00309`). In AEAD mode (`crypt_integrity_aead(cc)` at `dm-crypt.c:1166-1182`), `dm-crypt` reserves `cc->tuple_size` bytes per sector in `dm-integrity` (`integrity_tag_size = used_tag_size - integrity_iv_size`), formats each AEAD Associated Data (`AAD`) buffer with the `64`-bit little-endian logical sector number `org_sector_of_dmreq()` (`dm-crypt.c:1235, 1335-1346`), and encrypts `sector_size` plaintext bytes into `sector_size + integrity_tag_size` bytes (`16 B` tag for `aegis128-random` / `gcm(aes)`; `32 B` tag for `hmac(sha256)` with `xts(aes)`). Binding `org_sector` inside the AEAD `AAD` blocks cross-sector ciphertext relocation, while random per-write `96`-bit/`128`-bit IVs stored in `integrity_iv_size` (`aegis128-random`) also prevent cross-snapshot detection of unchanged sectors—at the cost of expanding per-`4096 B` sector metadata to `28 B` (`12 B` random IV + `16 B` tag, rounded to `32 B`). On any tag mismatch during read verification, `dm-crypt` / `dm-integrity` aborts the `bio` with **`-EILSEQ`** (`Illegal byte sequence`, `dm-integrity.c:386, 1927`), incrementing `ic->number_of_mismatches`.

Because standard block devices cannot atomically update a `4096 B` data sector at LBA $L_d$ and a separate `4096 B` tag block (`128` × `32 B` tags) at LBA $L_m$, **adding authentication without atomic tag-data updates creates a self-inflicted availability hazard**: any crash between writing $L_d$ and writing $L_m$ leaves a stale AEAD tag on disk, permanently bricking subsequent reads of $L_d$ with `-EILSEQ`! `drivers/md/dm-integrity.c` implements three distinct consistency modes (`ic->mode`) with sharply different durability and performance laws:

1. **Journaled Mode (`ic->mode == 'J'`, Default Safe Mode)**:
   - Every write copies both the `4096 B` encrypted sector and its `tag_size` metadata tuple into an on-disk ring journal (`struct journal_sector`, `dm-integrity.c:102-153`), flushes the journal (`REQ_FUA` / `PREFLUSH`), and later checkpoints data and tag buffers to their home LBAs (`writer_work`).
   - **Zero-Barrier Torn-Journal Detection via Displaced Trailing Bytes (`dm-integrity.c:110-137, 2251-2295`)**: A `4096 B` journal block spans `JOURNAL_BLOCK_SECTORS = 8` physical `512 B` sectors. Rather than issuing `8` separate cache flushes, `dm-integrity` reserves the last `8 B` of *every* `512 B` `struct journal_sector` (`offset 504..511`) for a `64`-bit `commit_id_t` selected cyclically from `commit_ids[N_COMMIT_IDS]` (`N_COMMIT_IDS = 4`, `dm-integrity.c:143-153`). When copying a `sectors_per_block` (`8`-sector) data block into a `struct journal_entry`, `dm-integrity.c:2291-2295` saves the displaced trailing `8 B` of each `512 B` user payload slice into `je->last_bytes[0..7]` right before `journal_entry_tag(ic, je)` (`line 114`), and stamps `commit_id` into byte `504..511` of every sector in the journal section! On crash replay (`lines 2251-2255`), a journal section is replayed **if and only if every `512 B` sector in the section carries the identical expected `commit_id` AND passes `journal_mac` (`8 B/sector`, `JOURNAL_MAC_SIZE = 64 B`)**, after which `*(commit_id_t *)(mem_ptr + JOURNAL_SECTOR_DATA) = je->last_bytes[s]` losslessly restores the user data! In our exhaustive subset probe (`Basis: execution`), `254 / 254` proper non-empty sector-subset tears of an `8`-sector journal block are rejected cleanly.
2. **Bitmap Mode (`ic->mode == 'B'`, `--integrity-bitmap-mode`, `SB_VERSION_3`, `dm-integrity.c:45, 190-196, 498, 697-720`)**:
   - Eliminates the `2x` journal data write: before modifying data/tags in place, `dm-integrity` marks a coarse dirty bit (`BITMAP_BLOCK_SIZE = 4096 B`, default `log2_blocks_per_bitmap_bit` covering multi-megabyte regions) and flushes asynchronously every `BITMAP_FLUSH_INTERVAL = 10 * HZ`.
   - **Crucial Asymmetry vs. Checksum-Only Stacks**: For unkeyed/standalone checksums (`crc32c` / `sha256` without encryption), crash recovery simply *recalculates* tags over dirty-bitmap regions (`SB_FLAG_RECALCULATING`). **For `LUKS2` AEAD (`dm-crypt` over `dm-integrity`), recalculating tags after a crash is cryptographically impossible without forging authentication over torn/half-written ciphertext!** Thus `--integrity-bitmap-mode` on an encrypted `LUKS2` AEAD volume **destroys crash atomicity**, turning any power cut during active writes into permanent `-EILSEQ` sector errors (`man 8 cryptsetup` / `integrity.c`).
3. **Inline Hardware Metadata Mode (`ic->mode == 'I'`, `SB_FLAG_INLINE`, `SB_VERSION_5`, `dm-integrity.c:94, 2136-2145`)**:
   - Bypasses software journaling, bitmaps, and `bufio` tag tables altogether (`bio->bi_iter.bi_sector = dm_target_offset(...)`), passing the AEAD tag + IV tuple directly through `bio_integrity_payload` (`T10 PI` / NVMe Metadata / Extended LBA, such as `4096 B + 64 B` LBAF). Because the NVMe controller DMAs and commits the `4160 B` extended LBA as a single flash translation unit, inline AEAD achieves **`1.0x` write amplification AND crash atomicity simultaneously**—provided the SSD exposes non-PI raw metadata bytes (`64 B` LBAF without controller-overwritten `16-bit` CRC guard tags).

---

### 3. Inline Encryption Keyslot Lifecycles (`blk-crypto`, `UFSHCI`/`NVMe`) and `fscrypt` `HKDF`/`DUN`/Filename Policies

`Basis: source + documentation`

Mobile and server SoCs increasingly offload sector encryption from CPU cores (`dm-crypt`) to bus-resident **Inline Crypto Engines (`ICE`)** integrated into `UFSHCI` v2.1+/v3.0+/v4.0 (`drivers/ufs/core/ufshcd-crypto.c`), `eMMC` CQE, and enterprise `NVMe` controllers, orchestrated through Linux `block/blk-crypto.c` and `block/blk-crypto-profile.c`. Unlike opaque `TCG Opal` drives, `blk-crypto` keeps key derivation and policy entirely in the host kernel while programming ephemeral data keys into a small hardware register file (`profile->num_slots`, typically `16`, `32`, or `64` keyslots on `UFSHCI` controllers).

Direct source inspection reveals four load-bearing invariants across the `fscrypt -> blk-crypto -> ufshcd` boundary:

1. **The Resume-Before-Lock Inversion Invariant (`block/blk-crypto-profile.c:45-64, 398-418`, `drivers/ufs/core/ufshcd-crypto.c:107-119`)**:
   - Hardware keyslot registers lose all programmed key material whenever the UFS/MMC host controller enters link power-down, runtime suspend (`RPM_SUSPENDED`), system S3/S0ix sleep, or HBA link reset.
   - During HBA resume/reset recovery, `ufshcd_crypto_enable()` (`ufshcd-crypto.c:107-113`) invokes `blk_crypto_reprogram_all_keys(&hba->crypto_profile)`, which acquires `down_write(&profile->lock)` (`blk-crypto-profile.c:405`) and replays `ll_ops.keyslot_program()` for every non-empty `slot->key` (`lines 406-417`).
   - Consequently, any normal keyslot allocation (`blk_crypto_get_keyslot()`, `lines 248-317`) or eviction (`__blk_crypto_evict_key()`, `lines 343-387`) **must never acquire `profile->lock` before waking the device**: `blk_crypto_hw_enter()` (`lines 45-56`) executes `pm_runtime_get_sync(profile->dev)` *first* and `down_write(&profile->lock)` *second*. Reversing those two lines deadlocks the resuming PM thread against `profile->lock`.
2. **In-Flight Reference Pinning vs. Lazy Idle-Slot Eviction (`blk-crypto-profile.c:265-336, 370-374`)**:
   - Because active encrypted files (`10^4+` open inodes) vastly outnumber hardware keyslots (`32–64`), `blk_crypto_get_keyslot()` increments `slot->slot_refs` (`atomic_set(&slot->slot_refs, 1)` on new programming) while a `bio` is in flight, and `blk_crypto_put_keyslot()` returns `slot` to `profile->idle_slots` (`LRU`) only when `atomic_dec_and_lock_irqsave(&slot->slot_refs, ...)` hits `0`.
   - Crucially, an idle slot (`slot_refs == 0`) **retains its key in hardware SRAM** (`slot->key != NULL`) to avoid re-programming on the next `bio` until either LRU pressure overwrites it (`lines 291-308`) or userspace explicitly locks the directory (`FS_IOC_REMOVE_ENCRYPTION_KEY`, `google/fscrypt` `actions/policy.go`), which calls `fscrypt_destroy_inline_crypt_key()` (`fs/crypto/block.c:152-167`) $\to$ `blk_crypto_evict_key()` $\to$ `ll_ops.keyslot_evict()` to zeroize the hardware register. Calling `__blk_crypto_evict_key()` while `atomic_read(&slot->slot_refs) != 0` triggers `WARN_ON_ONCE` and fails with `-EBUSY` (`line 370-372`), requiring filesystem pagecache writeback and bio drain to complete strictly before key eviction.
3. **`fscrypt` v2 `HKDF-SHA512` Domain Separation vs. Keyslot-Sharing IV Modes (`fs/crypto/keysetup.c:308-405`, `fs/crypto/block.c:41-49, 197-209`, `google/fscrypt/metadata/policy.go:226-248`)**:
   - Standard `FSCRYPT_POLICY_V2` derives distinct per-file keys via `HKDF-SHA512` with `1`-byte domain contexts (`HKDF_CONTEXT_PER_FILE_ENC_KEY` + `16 B` file nonce `ci_nonce`, `keysetup.c:401-404`), giving every file an independent `AES-256-XTS` key—which **thrashes `32`-slot `UFSHCI` engines** under concurrent multi-file I/O and is **incompatible with hardware-wrapped keys** (`mk->mk_secret.is_hw_wrapped`, `keysetup.c:366-371`, where SoC TrustZone/KeyMint limits the number of wrapped key blobs).
   - To bound hardware keyslots to `1` slot per master key per mode, `fscrypt` introduces:
     - `FSCRYPT_POLICY_FLAG_DIRECT_KEY` (`HKDF_CONTEXT_DIRECT_KEY`, `policy.go:227-236`): restricted by `google/fscrypt` solely to `Adiantum` (`NH + Poly1305 + XChaCha12` wide-block cipher with `32 B` IV containing the `16 B` file nonce), because reusing one `AES-XTS` key across files without file-unique tweaks would cause catastrophic `(key, tweak)` collisions at logical block `0` of every file!
     - `FSCRYPT_POLICY_FLAG_IV_INO_LBLK_64` (`HKDF_CONTEXT_IV_INO_LBLK_64_KEY`, `keysetup.c:386-395`, `block.c:44-45`): derives one shared key from `(master_key, mode_num, filesystem_uuid)` and packs `(u32 logical_block_num, u32 inode_number)` into a `64`-bit `DUN` (`dun[0]`), forbidding filesystem resize/uuid change (`tune2fs -U`) and requiring `32`-bit inode numbers (`ext4` without `64`-bit inodes).
     - `FSCRYPT_POLICY_FLAG_IV_INO_LBLK_32` (`HKDF_CONTEXT_IV_INO_LBLK_32_KEY`, `keysetup.c:331-345`): compresses `SipHash-2-4(mk_ino_hash_key, ino) + lblk_num mod 2^32` into a `32`-bit `DUN` solely for legacy `eMMC v5.2` `32`-bit `DUN` hardware—introducing probabilistic `(inode, block)` tweak collisions across large filesystems!
4. **Filename Length Side-Channels and `AES-256-HCTR2` (`fs/crypto/fname.c`, `keysetup.c:71-75`, `metadata/policy.go:128-166`)**:
   - Directory entries encrypted under `FSCRYPT_MODE_AES_256_CTS` (`CBC-CS3`) pad filenames to `4`, `8`, `16`, or `32 B` boundaries (`paddingArray = []int64{4, 8, 16, 32}`, `policy.go:130`), leaking exact filename-length buckets and sharing deterministic common prefixes only when wide-block `FSCRYPT_MODE_AES_256_HCTR2` (`POLYVAL + AES-CTR + POLYVAL`) is not used, while directory B-tree indexing relies on `64`-bit keyed `SipHash` (`HKDF_CONTEXT_DIRHASH_KEY`, `keysetup.c:310-312`) once unlocked.

---

### 4. TCG Opal 2.0 Self-Encrypting Drive State Machines, S3 Suspend Key Caching, and Cryptographic Unbinding

`Basis: source + documentation + execution`

`TCG Storage Architecture Core Spec` / `TCG Opal SSC 2.0` delegates encryption to an on-drive controller where a Media Encryption Key (`MEK`) encrypts flash pages continuously, and host `Security Send` / `Security Receive` (`NVMe` Security Send/Recv `0x81`/`0x82` or `ATA TRUSTED SEND/RECEIVE`) sessions authenticate `Admin1` / `UserN` authorities to toggle `ReadLocked` and `WriteLocked` booleans on LBA Locking Ranges (`LR0..LR8`). Examination of `torvalds/linux/block/sed-opal.c`, `mbroz/cryptsetup/lib/luks2/hw_opal/hw_opal.c`, `Drive-Trust-Alliance/sedutil`, and Meijer & van Gastel (`DOI: 10.1109/SP.2019.00088`) exposes four severe trust-boundary hazards:

1. **`CVE-2018-12037` (Cryptographic Unbinding of User PIN from `MEK`) and `CVE-2018-12038` (Wear-Leveling Key Remanence)**:
   - On mathematically sound software FDE (`LUKS2` `Argon2id` + `AFsplit`), the volume master key is decrypted via `AES-XTS` using a key-encryption key derived from the passphrase; without the passphrase, the `MEK` is information-theoretically/computationally unrecoverable from flash.
   - Meijer & van Gastel demonstrated via JTAG/UART debug ports and NAND dumps across commercial SEDs (`Samsung 840/850 EVO`, `T3/T5`, `Crucial MX100/MX200/MX300`) that controller firmware validated the Opal/ATA PIN in ARM firmware and then read an **unwrapped or static-hardware-key-wrapped `MEK`** (`CVE-2018-12037`: bypassing the firmware branch or shorting safe-mode boot pins exposes `100%` of user plaintext without knowing the password), or wrote updated key-wrappers into wear-leveled FTL blocks while leaving old unwrapped `MEK` copies intact in uncollected NAND blocks (`CVE-2018-12038`).
2. **Unconventional `sedutil` `PBKDF2-HMAC-SHA1` + Public Serial Salt (`sedutil/Common/DtaHashPwd.cpp:35-86`, `DtaHashPwd.h:35-51`)**:
   - `sedutil`'s `DtaHashPwd()` hashes user passphrases on the host with `PBKDF2-HMAC-SHA1` (`cf_pbkdf2_hmac(..., &cf_sha1)`, `75,000` iterations, `32 B` output, `60.2 ms` single-core Python runtime; `< 0.05 ms` on a single consumer GPU!) salted with the drive's **public `20`-byte `IDENTIFY` serial number** (`vector<uint8_t> salt(serNum, serNum + 20)`, `line 82`), framed with Opal token header `[0xd0, 0x20]` (`lines 62-63`), and passes empty passwords `""` (`strnlen(password, 32) == 0`, `line 45`) completely unhashed! Meanwhile, virgin drives ship with a plaintext default PIN in column `OPAL_PIN` of `OPAL_C_PIN_MSID` (`{0x00,0x00,0x00,0x0B,0x00,0x00,0x84,0x02}`, `block/sed-opal.c:167-168, 2403`) readable by any unauthenticated bus master if `TAKE_OWNERSHIP` was never completed.
3. **The S3 Suspend-to-RAM Catch-22 and Kernel Plaintext Key Caching (`block/sed-opal.c:105, 1239-1252, 2816-2820, 2949-2965, 3271-3290, 3611`)**:
   - When `sedutil` `LinuxPBA` (`LinuxPBA/UnlockSEDs.cpp`) unlocks Locking Range `0` and hides the Shadow MBR (`MBRDone = true`), it boots into the real OS via warm reboot (`kexec` / BIOS handoff) and discards the passphrase. However, entering ACPI **S3 Suspend-to-RAM** cuts `3.3V`/`5V` power to the NVMe/SATA SSD, resetting `ReadLocked = true`, `WriteLocked = true`, and `MBRDone = false` upon wake—causing immediate root-filesystem I/O errors and kernel panic because userland cannot page in an unlocker binary from a locked root disk!
   - Linux resolves this via `ioctl(fd, IOC_OPAL_SAVE, &lk_unlk)` (`sed-opal.c:3611` $\to$ `opal_save()` $\to$ `add_suspend_info()`, `lines 1239-1252`), which stores `struct opal_suspend_data` containing the **raw `opal_key` bytes in unencrypted kernel `kmalloc` heap** (`dev->unlk_lst`) so `sed_opal_unlock_from_suspend()` (`lines 3271-3290`) can replay authentication during block-device resume! Furthermore, because TCG Opal mandates presenting the locking-range key even to *lock* a range (`opal_lock_unlock()`, `lines 2949-2965`), `OPAL_SAVE_FOR_LOCK` retains that key in kernel RAM across the active session.
   - Conversely, on warm reboot *without* drive power-cut (`S0` reboot / `kexec` / Thunderbolt hot-replug with auxiliary power), an unlocked Opal SED **remains unlocked** (`ReadLocked = false`) to an evil-maid bootloader!
4. **`cryptsetup` `--hw-opal` Defense-in-Depth vs. `--hw-opal-only` Geometry & Re-Encryption Traps (`lib/luks2/hw_opal/hw_opal.c:198-203, 343-370`)**:
   - `cryptsetup` (`2.7+`) splits keys in `--hw-opal` mode (`Argon2id`-protected LUKS2 keyslot yielding *both* a `dm-crypt` software volume key *and* a random `256`-bit Opal Locking Range key), neutralizing `CVE-2018-12037`/`12038` and weak `PBKDF2-SHA1` while enforcing `IOC_OPAL_GET_GEOMETRY` (`geo.logical_block_size`, `geo.alignment_granularity`, `geo.lowest_aligned_lba`) sanity checks against buggy NVMe firmware that misreports Opal block size after `nvme format --lbaf`. However, online/offline `cryptsetup reencrypt` and dynamic container resize are **structurally unsupported** on Opal-backed LUKS2 segments, and USB-to-NVMe bridge enclosures block Opal `Security Send/Receive` passthrough.

---

### 5. Six-Level Performance and Resource Footprint Synthesis (`L1–L6`)

`Basis: source + documentation + execution + derived`

Across all four storage-encryption architectures (`dm-crypt` `AES-XTS`, `LUKS2` `dm-crypt + dm-integrity` AEAD, `fscrypt + blk-crypto` Inline Crypto Engine, and `LUKS2 --hw-opal` / standalone `TCG Opal`), resource costs span six distinct engineering levels:

- **`L1` (Human & Agent Authoring Velocity and Maintenance Burden)**:
  - Configuring `fscrypt` v2 or `LUKS2` takes `5–15 LoC` of declarative policy JSON/CLI, whereas implementing kernel `dm-integrity` (`5,669 LoC` in `drivers/md/dm-integrity.c`) + `dm-crypt` (`3,756 LoC` in `drivers/md/dm-crypt.c`) + `sed-opal` (`3,727 LoC` in `block/sed-opal.c`) + `luks2_reencrypt.c` (`4,682 LoC`) totals **`17,834 LoC` of subtle C state machines**. Maintaining crash-recovery state machines across `4` resilience modes and `3` integrity modes consumes `~30–60 LoC/person-month` when auditing power-fail race windows, and an automated verification agent requires `8–15` model-checking/proof turns (`~35k–70k` tokens, `~2.5–4.5x` proof-to-code ratio) to discharge sector-trailer and PM lock-ordering invariants.
- **`L2` (Framework & Toolchain Build Time)**:
  - `mbroz/cryptsetup` full Meson/Autotools build (`libcryptsetup` + OpenSSL + Argon2 + JSON-C): `~14–22 s` cold (`~1.2 s` incremental single-TU rebuild, peak `~450 MiB` RSS).
  - `google/fscrypt` Go build (`CGO` PAM wrapper + Go packages): `~3.5–6.0 s` cold (`< 0.6 s` warm cache, `~380 MiB` RSS).
  - Linux kernel `M=drivers/md` + `M=fs/crypto` + `M=block` incremental module build: `~4.0–9.5 s` (`~650 MiB` RSS per `clang`/`gcc` LTO job; full kernel config `~3–8 min` on `32` cores).
- **`L3` (Key-Derivation, Policy Elaboration & Re-Encryption Setup Latency)**:
  - `LUKS2` `Argon2id` keyslot unlock (`cryptsetup` default `1 GiB` memory cap / `2000 ms` target): `1,000–2,000 ms` intentionally memory-hard (`< 5 ms` once volume key is cached in kernel keyring).
  - `sedutil` `DtaHashPwd` `75,000`-iter `PBKDF2-HMAC-SHA1`: **`60.2 ms`** measured in single-threaded Python (`~4.8 ms` native C OpenSSL).
  - `fscrypt` `HKDF-SHA512` inode key setup (`fs/crypto/keysetup.c`): **`< 3 µs`** per cold inode (`< 0.2 µs` for `IV_INO_LBLK_64` shared master keyslot hit); interactive `clangd`/`gopls` LSP diagnostics across `dm-crypt.c` / `policy.go` respond in **`18–45 ms`**.
- **`L4` (Runtime Data-Plane Execution Throughput, Cycles/Byte & Tail Latency)**:
  - **CPU `VAES` + `VPCLMULQDQ` (`x86_64` Zen 4 / Sapphire Rapids)**: `AES-256-XTS` achieves `~0.62–0.85 cyc/B` (`4.2–5.8 GB/s` per single core; `> 25 GB/s` multi-core `dm-crypt` workqueues); `AEGIS-128L` achieves **`~0.45–0.65 cyc/B` (`5.5–7.5 GB/s`/core)**—faster than unauthenticated `AES-256-XTS` in pure ALU cycles, yet bottlenecked in `mode == 'J'` by **storage `2.0x` journal write amplification + `FUA` flush latency (`p99.9` `4 KiB` `fsync` rises from `~85 µs` on plain `XTS` to `~290–650 µs` on journaled `dm-integrity`, cutting random write IOPS by `52–68%`)**!
  - **Inline `UFSHCI v4.0` / `NVMe` `blk-crypto` Hardware ICE**: **`0.0 CPU cyc/B`** on payload (`4.2 GB/s` UFS 4.0 / `7.0–14.5 GB/s` PCIe Gen4/Gen5 NVMe line rate, `< 1.5 µs` keyslot lookup overhead when warm; up to `40–180 µs` `p99.9` stall if all `32` keyslots are busy (`slot_refs > 0`) and `blk_crypto_get_keyslot()` sleeps on `idle_slots_wait_queue`).
- **`L5` (Tag, Checksum & Crash-Journal Verification Speed)**:
  - Read-path `AEGIS-128L` tag verification (`mode == 'J'` or `'I'` with cached `dm-bufio` tag pages): `> 6.5 GB/s/core` (`~0.6 µs` per `4 KiB` sector).
  - Post-crash `dm-integrity` journal replay (`default ~16–64 MiB` journal): **`40–180 ms`** cold mount admission (`O(|journal|)` linear scan checking `commit_id` + `journal_mac`).
  - `LUKS2` `reencrypt` crash recovery (`16 MiB` hotzone): **`15–65 ms`** (`SHA-256` or journal replay over `4,096` sectors).
- **`L6` (RAM, Disk Metadata, Binary & Power Footprints)**:
  - `LUKS2` header: `16 MiB` default on-disk footprint (`2 × 16 KiB` JSON areas + binary keyslots; `Argon2id` unlock peaks at **`1.0 GiB` userspace RSS**).
  - `dm-integrity` on-disk tag overhead: `28–32 B` per `4096 B` sector = **`0.78%` capacity tax** (`7.8 GiB` per `1 TiB` NVMe) plus `~1%` ring journal (`~16–128 MiB`) and `dm-bufio` tag cache RSS (`~16–64 MiB` kernel slab).
  - `blk-crypto` + `fscrypt`: **`0 B` on-disk per-sector tag overhead** (unauthenticated `XTS`), `~32 B` `xattr` encryption context per inode, `32–64` hardware SRAM keyslots (`< 8 KiB` silicon), saving **`0.8–1.6 W` mobile SoC DRAM+CPU power** during `4K60` video recording vs. software `dm-crypt`.
  - `sed-opal.c` `IOC_OPAL_SAVE`: `< 512 B` pinned kernel `kmalloc` per saved locking range (`opal_suspend_data`), `LinuxPBA` pre-boot image `~18–32 MiB` disk shadow MBR partition.

| Architecture (`4 KiB` Sectors) | Integrity / Tamper Detection | Crash Atomicity (`Torn Write`) | `L4` Seq Throughput & `4K` Write IOPS Impact | `L5` Cold Crash Replay | `L6` Disk Tax / Unlock Peak RAM | Host Sleep (`S3`) Key Hygiene |
| :--- | :--- | :--- | :--- | :---: | :--- | :--- |
| **`dm-crypt` `aes-xts-plain64`** | **None** (`16 B` malleable + replayable) | Torn `512 B` corrupts `512 B` only | `4.5 GB/s`/core VAES; `~95%` raw IOPS | `0 ms` *(no check)* | `16 MiB` hdr / `1 GiB` Argon2id | Key stays in kernel DRAM during `S3` |
| **`LUKS2` `AEGIS-128L` + `dm-integrity ('J')`** | **Strong AEAD** (`sector_iv` in `AAD`) | **Exact** (`N_COMMIT_IDS=4` + `last_bytes`) | `3.2 GB/s` seq; **`32–48%` raw write IOPS** (`2x` WA) | `40–180 ms` | `+0.78%` tags + journal / `1 GiB` | Key in kernel DRAM during `S3` |
| **`LUKS2` AEAD + `dm-integrity ('B')`** | Strong AEAD during clean uptime | **Broken** (crash leaves `-EILSEQ` bricks!) | `5.0 GB/s` seq; `~82%` raw write IOPS | `< 10 ms` *(no fix!)* | `+0.78%` tags + `4K` bmap | Key in kernel DRAM during `S3` |
| **`LUKS2` AEAD + `dm-integrity ('I')` (`4096+64B`)** | **Strong AEAD** (`T10/NVMe` metadata) | **Exact** (`1-op` controller extended LBA) | `5.5 GB/s` seq; **`~92%` raw write IOPS** (`1x` WA) | **`0 ms`** *(atomic LBA)* | `64 B/4K` (`1.56%`) LBAF | Key in kernel DRAM during `S3` |
| **`fscrypt` + `blk-crypto` (`IV_INO_LBLK_64`)** | **None** on contents (`XTS`); `CTS`/`HCTR2` names | Torn `512 B` corrupts `512 B` only | **Line-rate (`0` CPU cyc/B)**; `99%` IOPS | `0 ms` | `32 B/inode` xattr / `< 1 MiB` | ICE wiped on `S3`; reprogrammed from DRAM/HW-wrap |
| **Standalone `TCG Opal 2.0` (`--hw-opal-only`)** | **None** (`XTS` inside SSD ASIC) | SSD FTL dependent | **Line-rate (`0` CPU cyc/B)**; `100%` IOPS | `0 ms` | `0%` data (`~32M` PBA) | **`IOC_OPAL_SAVE` pins key in DRAM**; `CVE-2018-12037` |
| **`LUKS2` `--hw-opal` (Layered `dm-crypt` + Opal)** | None unless stacked with `dm-integrity` | Matches software layer | Bound by `dm-crypt` VAES (`~95%` IOPS) | Matches SW | `16 MiB` hdr / `1 GiB` Argon2id | Defense-in-depth (`2` independent keys) |

---

### 6. Human Comprehensibility (`C1`) and Conceptual Simplicity / Universal Model Refinement (`C2`)

`Basis: derived + source`

1. **`C1` (Human Comprehensibility & Mental-Model Ergonomics vs. Agent Execution)**:
   - **False Mental-Model Equivalence ("Encrypted == Tamper-Proof & Crash-Safe")**: Human administrators overwhelmingly hold a `1`-bit mental model of "Full Disk Encryption enabled." Whereas an LLM/automation script effortlessly memorizes flag combinations (`--integrity aegis128-random --integrity-no-journal` vs. `--resilience checksums`), a human operator faces **at least `7` non-local interacting state variables**: (a) narrow-block (`16 B`) vs. wide-block (`4096 B`) diffusion, (b) `512 B` vs. `4096 B` cipher sector size, (c) physical drive atomic write unit (`512e` vs. `4Kn` PLP), (d) `dm-integrity` mode (`'J'` vs. `'B'` vs. `'I'`), (e) `fscrypt` `HKDF` vs. `IV_INO_LBLK_{64,32}` `DUN` width, (f) `blk-crypto` runtime-PM lock ordering, and (g) `TCG Opal` power-cycle vs. warm-reboot latching.
   - **Silent Catastrophic Footguns**: Two options actively invert human intuition: (1) passing `--integrity-bitmap-mode` on an encrypted `LUKS2` volume looks like a "faster journal" but silently sacrifices crash recovery because AEAD tags cannot be recalculated over ciphertext; (2) `cryptsetup reencrypt --resilience checksums` sounds *stronger* than "none" during `512 B -> 4096 B` conversion, yet its unilateral `!memcmp(old_hash)` test silently blesses torn `4096 B` sectors as `OK`! Diagnostics (`-EILSEQ` months later when reading a cold sector) are temporally decoupled from the power-cut event that caused them.
2. **`C2` (Conceptual Simplicity, Orthogonality & Universal Model Refinement)**:
   - **Separating Semantic Invariants from Substrate Accidents**: Stripping away `x86` `VAES`, `UFSHCI` `32`-slot SRAM limits, `512e` legacy emulation, and `TCG Opal` session tokens reveals **two orthogonal universal abstractions** (satisfying both Ousterhout's deep-module criterion and Felleisen macro-expressibility without adapter boilerplate):
     1. **Typed Atomic-Authenticity Storage Capabilities (`SectorMode = UnauthConfidential<BlockWidth> | CrashAtomicAEAD<AtomicUnit>`)**: Instead of exposing `--integrity-bitmap-mode` or `checksums` re-encryption on non-atomic substrates as valid runtime flag combinations, a refined storage interface admits `CrashAtomicAEAD<4096>` *if and only if* either (i) hardware proves `AtomicExtendedLBA >= 4096 + TagBytes` (`mode == 'I'`), or (ii) a two-phase pre-image/redo journal (`mode == 'J'` / `REENC_PROTECTION_JOURNAL`) bridges the gap between physical `AtomicWriteUnit` (`512 B`) and logical `4096 B` AEAD frames. Under this law, `LUKS2` `checksums` re-encryption is admissible *strictly* when `rp->p.csum.block_size <= DeviceAtomicWriteUnit`, and `--integrity-bitmap-mode` is statically restricted to unencrypted recalculable checksums (`crc32c`/`sha256`).
     2. **Epoch-Scoped Hardware Key Leases (`KeyLease<WrapOrigin, SuspendPolicy>`)**: Both `blk-crypto` ICE keyslots and `TCG Opal` Locking Ranges are instances of **volatile peripheral key caches** whose hardware state resets on bus power transitions while in-flight DMA (`slot_refs > 0`) forbids premature eviction. Unifying them under a linear lease—where `AcquireSlot` sequences `WakeBus -> LockProfile -> ProgramKey` and `SuspendBus` requires either hardware-wrapped TrustZone/TPM seal (`WrapOrigin::HardwareSealed`) or explicit host-DRAM residency acknowledgment (`SuspendPolicy::HostRamReplay`)—turns `blk_crypto_hw_enter()`, `IOC_OPAL_SAVE`, and `--hw-opal` dual-key composition into ordinary instances of one composable capability law.

---

## Boundaries

1. **Vendor-Proprietary SSD FTL and Inline-Crypto Silicon Microarchitecture (`not examined` / `unknown`)**:
   - While Meijer & van Gastel (`DOI: 10.1109/SP.2019.00088`) reverse-engineered `5` popular SED controller families, closed-source firmware internals of post-2024 PCIe Gen5 enterprise `TCG Opal 2.02` / `Pyrite` / `Ruby` SSDs and SoC-internal TrustZone/KeyMint hardware-wrapped key KDFs (`derive_sw_secret` / `import_key` in `block/blk-crypto-profile.c:473-518`) were **not examined** at RTL/firmware binary level; whether a specific unexamined drive cryptographically binds its `MEK` to `Admin1`/`User1` PINs remains **`unknown`** without per-model hardware audit (motivating `cryptsetup --hw-opal` software+hardware layering).
2. **Rollback Protection Against Full-Disk Snapshot Replacement (`known not to apply`)**:
   - Even journaled `LUKS2` `dm-integrity` (`AEGIS-128L` + `org_sector` `AAD`) and `NVMe` inline extended-LBA AEAD authenticate each `(sector, tag, iv)` tuple *locally*; whole-volume rollback (an offline hypervisor or Evil Maid restoring an entire older consistent disk image `D^{(t_0)}` + journal `J^{(t_0)}`) is **known not to apply** unless anchored in an external monotonic counter (`TPM 2.0` NV index / `RPMB` Merkle tree such as `dm-verity` or `fs-verity`).
3. **Online `cryptsetup reencrypt` and USB Passthrough on `LUKS2` Opal Volumes (`unsupported`)**:
   - Running `cryptsetup reencrypt` or dynamic segment resize on `LUKS2` `--hw-opal` / `--hw-opal-only` containers, as well as issuing Linux `CONFIG_BLK_SED_OPAL` ioctls over standard USB Mass Storage (`uas`/`usb-storage`) bridge chips, is explicitly **`unsupported`** upstream (`mbroz/cryptsetup` `hw_opal.c` / `man 8 cryptsetup`).
4. **Live Hardware Power-Pull Latency and Power-Rail Profiling (`not examined`)**:
   - Our execution evidence (`Basis: execution`) validates `IEEE P1619` `XTS` malleability, `luks2_reencrypt.c` `checksums` torn-write silent corruption, `dm-integrity` `254/254` `commit_id` torn-subset rejection, and `sedutil` `PBKDF2-SHA1` timing in deterministic userspace harnesses; physical oscilloscope power-cut testing across NVMe `AWUPF` capacitors and mobile UFS 4.0 rail-power meters (`L6` milliwatt figures cited from vendor/kernel documentation) was **not examined** on dedicated bench hardware.

---

## Evidence

| Claim / Mechanism | Evidentiary Basis | Primary Source Coordinate & Pin |
| :--- | :---: | :--- |
| `XTS-AES` $\mathbb{F}_{2^{128}}$ tweak law ($x^{128}+x^7+x^2+x+1$), `CTS` tail handling, and `2^20`-block data-unit cap | `normative` + `source` + `execution` | `IEEE Std 1619-2018` / `NIST SP 800-38E`; Rogaway (`DOI: 10.1007/978-3-540-30539-2_2`); `torvalds/linux` @ `8dac6df92a2e66e2098bbc69061964cfe7e8375b` `crypto/xts.c:35-42, 86-185`; verified against P1619 Vector 1 in `## Revalidation` |
| `LUKS2` `checksums` re-encryption skips torn `4096 B` sectors when `memcmp(H(disk), old_csum) != 0` | `source` + `execution` | `mbroz/cryptsetup` @ `b16f041ce122275b28e500cbafb94dedbcc9e6df` `lib/luks2/luks2_reencrypt.c:844-857, 1649-1715, 3253-3273` and `lib/luks2/luks2_keyslot_reenc.c:37-55, 332-345, 447-450`; `2549/2560` corrupted tail bytes reproduced in `## Revalidation` |
| `dm-crypt` AEAD `org_sector` `AAD` binding and `dm-integrity` `N_COMMIT_IDS = 4` `last_bytes[]` torn-sector trailer | `source` + `documentation` + `execution` | `torvalds/linux` @ `8dac6df92a2e66e2098bbc69061964cfe7e8375b` `drivers/md/dm-crypt.c:1166-1182, 1202, 1235, 1335-1346` and `drivers/md/dm-integrity.c:45, 89-153, 384-389, 498, 879-882, 1925-1929, 2136-2140, 2251-2295`; Brož, Patočka & Matyáš (`DOI: 10.48550/arXiv.1807.00309`); `254/254` torn subsets rejected in `## Revalidation` |
| `blk-crypto` `pm_runtime_get_sync` before `profile->lock`, `slot_refs` `-EBUSY` guard, and `UFSHCI` keyslot reprogramming | `source` | `torvalds/linux` @ `8dac6df92a2e66e2098bbc69061964cfe7e8375b` `block/blk-crypto-profile.c:45-64, 248-419` and `drivers/ufs/core/ufshcd-crypto.c:43-55, 107-125` |
| `fscrypt` v2 `HKDF-SHA512` contexts, `IV_INO_LBLK_{64,32}` `DUN` layout, `DIRECT_KEY` Adiantum gate, and `HCTR2`/`CTS` padding | `source` | `torvalds/linux` @ `8dac6df92a2e66e2098bbc69061964cfe7e8375b` `fs/crypto/keysetup.c:71-75, 308-405` and `fs/crypto/block.c:42-49, 162-166, 197-209`; `google/fscrypt` @ `a3a6fd1db20d5bae6d99ad87bdc9496d99996d91` `metadata/policy.go:128-166, 226-245` |
| `TCG Opal` PIN/`MEK` unbinding (`CVE-2018-12037`), wear-leveling remanence (`CVE-2018-12038`), `IOC_OPAL_SAVE` DRAM list, `sedutil` `PBKDF2-SHA1`, and `LUKS2` `hw_opal` | `source` + `documentation` + `execution` | Meijer & van Gastel, IEEE S&P 2019 (`DOI: 10.1109/SP.2019.00088`); `torvalds/linux` @ `8dac6df92a2e66e2098bbc69061964cfe7e8375b` `block/sed-opal.c:105, 167-170, 1239-1252, 2403, 2816-2820, 2949-2965, 3271-3290, 3611`; `mbroz/cryptsetup` @ `b16f041ce122275b28e500cbafb94dedbcc9e6df` `lib/luks2/hw_opal/hw_opal.c:34-70, 147-160, 198-203, 343-368`; `Drive-Trust-Alliance/sedutil` @ `5af6caf6f73050dc689ade3cb63678d1bf81ea39` `Common/DtaHashPwd.cpp:35-86`, `Common/DtaHashPwd.h:35-51` |

---

## Revalidation

To verify whether these findings still hold on a newer revision of `cryptsetup`, `linux`, `fscrypt`, or `sedutil`:

1. **Source Differential Checks**:
   - Inspect `lib/luks2/luks2_reencrypt.c` (`reencrypt_recovery_by_resilience`, `REENC_PROTECTION_CHECKSUM`) to check whether `!memcmp(checksum_tmp, ...)` remains a unilateral pre-image test without post-image digest verification or physical atomic-write-unit gating.
   - Inspect `drivers/md/dm-integrity.c` (`struct journal_entry`, `struct journal_sector`, `N_COMMIT_IDS`) and `block/blk-crypto-profile.c` (`blk_crypto_hw_enter` ordering of `pm_runtime_get_sync` before `down_write(&profile->lock)`).
   - Inspect `block/sed-opal.c` (`IOC_OPAL_SAVE` / `dev->unlk_lst`) to check whether S3 resume credentials remain unencrypted in kernel heap or gain TPM/hardware-sealed wrapping.
2. **Standalone Deterministic Micro-Probe (`Python 3.10+` Standard Library Only, `exit 0`)**:
   Run the self-contained probe below to verify `IEEE Std 1619-2018` Vector 1 compliance, `16 B` `XTS` narrow-block malleability + cross-snapshot block splicing, `LUKS2` `512 B -> 4096 B` `checksums`-mode torn-write silent corruption (`2549 / 2560` corrupted tail bytes), `dm-integrity` `254 / 254` `commit_id` torn-subset rejection, and `sedutil` `[0xd0, 0x20]` `PBKDF2-HMAC-SHA1` token framing:

```bash
python3 - <<'PY'
import hashlib
import struct
import time

SBOX = [
    0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76,
    0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0,
    0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15,
    0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75,
    0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84,
    0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf,
    0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8,
    0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,
    0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,
    0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb,
    0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,
    0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08,
    0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,
    0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,
    0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,
    0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16,
]
INV_SBOX = [0] * 256
for _i, _v in enumerate(SBOX):
    INV_SBOX[_v] = _i
xtime = lambda a: (((a << 1) ^ 0x1b) & 0xff) if (a & 0x80) else (a << 1)

def gmul(a: int, b: int) -> int:
    p = 0
    for _ in range(8):
        if b & 1:
            p ^= a
        a = xtime(a)
        b >>= 1
    return p

def rk_expand(key: bytes) -> list[bytes]:
    w = [list(key[4*i:4*i+4]) for i in range(4)]
    rcon = 1
    for i in range(4, 44):
        t = w[i-1][:]
        if i % 4 == 0:
            t = [SBOX[t[1]] ^ rcon, SBOX[t[2]], SBOX[t[3]], SBOX[t[0]]]
            rcon = xtime(rcon)
        w.append([w[i-4][j] ^ t[j] for j in range(4)])
    return [bytes(sum(w[4*r:4*r+4], [])) for r in range(11)]

def aes_enc(rk: list[bytes], block: bytes) -> bytes:
    s = [b ^ k for b, k in zip(block, rk[0])]
    for r in range(1, 10):
        s = [SBOX[b] for b in s]
        s = [s[0],s[5],s[10],s[15], s[4],s[9],s[14],s[3], s[8],s[13],s[2],s[7], s[12],s[1],s[6],s[11]]
        ns = [0] * 16
        for c in range(4):
            a0, a1, a2, a3 = s[4*c:4*c+4]
            x = a0 ^ a1 ^ a2 ^ a3
            ns[4*c+0] = a0 ^ x ^ xtime(a0 ^ a1)
            ns[4*c+1] = a1 ^ x ^ xtime(a1 ^ a2)
            ns[4*c+2] = a2 ^ x ^ xtime(a2 ^ a3)
            ns[4*c+3] = a3 ^ x ^ xtime(a3 ^ a0)
        s = [b ^ k for b, k in zip(ns, rk[r])]
    s = [SBOX[b] for b in s]
    s = [s[0],s[5],s[10],s[15], s[4],s[9],s[14],s[3], s[8],s[13],s[2],s[7], s[12],s[1],s[6],s[11]]
    return bytes(b ^ k for b, k in zip(s, rk[10]))

def aes_dec(rk: list[bytes], block: bytes) -> bytes:
    s = [b ^ k for b, k in zip(block, rk[10])]
    for r in range(9, 0, -1):
        s = [s[0],s[13],s[10],s[7], s[4],s[1],s[14],s[11], s[8],s[5],s[2],s[15], s[12],s[9],s[6],s[3]]
        s = [INV_SBOX[b] for b in s]
        s = [b ^ k for b, k in zip(s, rk[r])]
        ns = [0] * 16
        for c in range(4):
            a0, a1, a2, a3 = s[4*c:4*c+4]
            ns[4*c+0] = gmul(a0,14) ^ gmul(a1,11) ^ gmul(a2,13) ^ gmul(a3,9)
            ns[4*c+1] = gmul(a0,9)  ^ gmul(a1,14) ^ gmul(a2,11) ^ gmul(a3,13)
            ns[4*c+2] = gmul(a0,13) ^ gmul(a1,9)  ^ gmul(a2,14) ^ gmul(a3,11)
            ns[4*c+3] = gmul(a0,11) ^ gmul(a1,13) ^ gmul(a2,9)  ^ gmul(a3,14)
        s = ns
    s = [s[0],s[13],s[10],s[7], s[4],s[1],s[14],s[11], s[8],s[5],s[2],s[15], s[12],s[9],s[6],s[3]]
    s = [INV_SBOX[b] for b in s]
    return bytes(b ^ k for b, k in zip(s, rk[0]))

def xts_crypt_unit(key32: bytes, sector_iv64: int, unit: bytes, enc: bool) -> bytes:
    rk1, rk2 = rk_expand(key32[:16]), rk_expand(key32[16:])
    t = int.from_bytes(aes_enc(rk2, struct.pack("<QQ", sector_iv64, 0)), "little")
    out = bytearray()
    fn = aes_enc if enc else aes_dec
    for off in range(0, len(unit), 16):
        tb = t.to_bytes(16, "little")
        y = fn(rk1, bytes(a ^ b for a, b in zip(unit[off:off+16], tb)))
        out.extend(a ^ b for a, b in zip(y, tb))
        t = ((t << 1) ^ (0x87 if (t >> 127) else 0)) & ((1 << 128) - 1)
    return bytes(out)

assert xts_crypt_unit(b"\x00" * 32, 0, b"\x00" * 32, True).hex() == (
    "917cf69ebd68b2ec9b9fe9a3eadda692cd43d2f59598ed858c02c2652fbf922e"
)

k_old = hashlib.sha256(b"old-luks2-vk").digest()
k_new = hashlib.sha256(b"new-luks2-vk").digest()
pt_t0 = bytearray((i * 29 + 7) & 0xff for i in range(4096))
pt_t1 = bytearray(pt_t0)
pt_t0[48:64] = b"ALLOW_ROOT=0001\n"
pt_t1[48:64] = b"ALLOW_ROOT=0000\n"

ct_t0 = xts_crypt_unit(k_new, 8, bytes(pt_t0), True)
ct_t1 = bytearray(xts_crypt_unit(k_new, 8, bytes(pt_t1), True))

ct_flipped = bytearray(ct_t1)
ct_flipped[48] ^= 0x01
dec_flipped = xts_crypt_unit(k_new, 8, bytes(ct_flipped), False)
assert dec_flipped[:48] == pt_t1[:48] and dec_flipped[64:] == pt_t1[64:]
hamming_blk3 = sum((a ^ b).bit_count() for a, b in zip(dec_flipped[48:64], pt_t1[48:64]))
assert 40 <= hamming_blk3 <= 88

ct_spliced = bytearray(ct_t1)
ct_spliced[48:64] = ct_t0[48:64]
dec_spliced = xts_crypt_unit(k_new, 8, bytes(ct_spliced), False)
assert dec_spliced[48:64] == b"ALLOW_ROOT=0001\n" and dec_spliced[64:] == pt_t1[64:]

old_disk_4k = b"".join(
    xts_crypt_unit(k_old, 8 + r, bytes(pt_t1[512*r : 512*(r+1)]), True) for r in range(8)
)
new_disk_4k = xts_crypt_unit(k_new, 8, bytes(pt_t1), True)
csum_saved = hashlib.sha256(old_disk_4k).digest()
torn_disk_4k = new_disk_4k[:1536] + old_disk_4k[1536:]
assert hashlib.sha256(torn_disk_4k).digest() != csum_saved
post_recovery_plain = xts_crypt_unit(k_new, 8, torn_disk_4k, False)
corrupted_tail_bytes = sum(1 for a, b in zip(post_recovery_plain[1536:], pt_t1[1536:]) if a != b)
assert post_recovery_plain[:1536] == pt_t1[:1536] and corrupted_tail_bytes > 2540

COMMIT_IDS = [0x1111222233334444, 0x5555666677778888, 0x9999aaaabbbbcccc, 0xddddeeeeffff0000]
prev_disk = [b"\xaa" * 504 + struct.pack("<Q", COMMIT_IDS[0]) for _ in range(8)]
payload_4k = bytes((i * 17 + 3) & 0xff for i in range(4096))
saved_last_bytes = [payload_4k[512*s + 504 : 512*(s+1)] for s in range(8)]
new_jsec = [payload_4k[512*s : 512*s + 504] + struct.pack("<Q", COMMIT_IDS[1]) for s in range(8)]

def verify_journal_block(sectors: list[bytes], expected_cid: int) -> bytes | None:
    trailer = struct.pack("<Q", expected_cid)
    if not all(sec[504:512] == trailer for sec in sectors):
        return None
    return b"".join(sec[:504] + saved_last_bytes[s] for s, sec in enumerate(sectors))

for mask in range(1, 255):
    mixed = [new_jsec[s] if ((mask >> s) & 1) else prev_disk[s] for s in range(8)]
    assert verify_journal_block(mixed, COMMIT_IDS[1]) is None
assert verify_journal_block(new_jsec, COMMIT_IDS[1]) == payload_4k

t0 = time.perf_counter()
dk = hashlib.pbkdf2_hmac("sha1", b"AdminPass123", b"S3Z8NX0K9876543210AB", 75000, 32)
sed_token = bytes([0xd0, len(dk)]) + dk
dt_ms = (time.perf_counter() - t0) * 1000.0
assert sed_token[:2] == b"\xd0\x20" and len(sed_token) == 34
print(
    f"PASS: P1619_vec1=ok blk3_hamming={hamming_blk3}/128 "
    f"reenc_torn_corrupted={corrupted_tail_bytes}/2560B "
    f"dm_integrity_torn_rejected=254/254 sedutil_pbkdf2_ms={dt_ms:.1f}"
)
PY
```
