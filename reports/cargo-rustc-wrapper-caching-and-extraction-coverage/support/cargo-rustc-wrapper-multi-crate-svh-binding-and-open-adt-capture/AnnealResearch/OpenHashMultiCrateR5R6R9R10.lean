import AnnealResearch.SubstantiveMirByteParser
import AnnealResearch.SemanticVerticalSliceCore
import AnnealResearch.CargoWorkspaceIntegrationControls

set_option maxHeartbeats 400000
set_option maxRecDepth 65536
set_option Elab.async false

namespace AnnealResearch.OpenHashMultiCrateR5R6R9R10

open AnnealResearch.SubstantiveMirByteParser
open AnnealResearch.SemanticVerticalSlice
open AnnealResearch.CargoWorkspaceIntegrationControls

/-!
# R5, R6, R9, & R10: Non-Trivial Multi-Crate Open-Hash Acquisition, Compiler-Verified Endorsement, Cross-Crate Drop Glue, and ABI/Layout Witnesses (`#89`)

This module mechanizes the Wave B deliverables of `joshlf/anneal#89`:
1. **`R5` (`U5`, `#89` §11):** Non-trivial 3-crate `open_hash_mode` acquisition
   (`r5_inner_lib` -> `r5_outer_lib` -> `r5_client_app`) with zero source-name or
   type-spelling dispatch tables, exercising 4 distinct multi-field cross-crate ADTs
   (`AuditCounter` `tyTag = 7`, `ScopedTicket` `tyTag = 8`, `WindowSpec` `tyTag = 17`,
   `QuotaPair` `tyTag = 13`), multiple generic instantiations
   (`scale_window_aligned::<u32, 4>` `symId = 168` vs `scale_window_aligned::<u64, 8>`
   `symId = 179`), a trait method call (`WindowPolicy::adjust_quota` `symId = 121`),
   cross-crate drop glue (`DropGlue<ScopedTicket>` `symId = 152` ->
   `<ScopedTicket as Drop>::drop` `symId = 205` -> `AuditCounter::record_drop_event`
   `symId = 211`), and `-Z mir-preserve-ub` `PlaceMention` (`_1` deref in `symId = 112` and `117`),
   together with refactor stability (`r5_client_app_refactored_open_hash.amir`),
   forced-collision resolution (`--driver-open-hash-force-collision-mod=10`), and
   fail-closed negative controls (`5e`–`5h`).
2. **`R6` (`U6`, `#89` §12):** Compiler-verified post-run endorsement (`after_analysis`
   returns `Compilation::Continue`, checks `tcx.dcx().has_errors().is_none()` after
   `run_compiler` returns, and writes `"post_run_compiler_verified": true` atomically)
   and strict phase separation (`0x03` `Runtime(PostCleanup)`, `0x04` `ExternalRlibOptimized`,
   `0x05` `Runtime(Initial)`), with negative controls `6a`–`6e`.
3. **`R9` (`#89` §15):** Cross-crate post-cleanup sidecar vs. `.rlib` `optimized_mir`
   discriminator on `r5_client_app` (`verify_multi_crate_pipeline` `symId = 208`), showing
   that linking against the `Runtime(PostCleanup)` (`0x03`) sidecars catches both
   client-side (`ptrValid0 = false`) and cross-crate (`ptrValid1 = false`) raw-pointer
   `PlaceMention` UB and executes the cross-crate `DropGlue<ScopedTicket>` chain,
   whereas linking against `.rlib` `optimized_mir` (`0x04`) loses `PlaceMention` UB
   detection when `mir_preserve_ub = false`.
4. **`R10` (`#89` §16):** Compiler-queried `LayoutOf` witnesses from `r5_inner_lib`
   covering a niche-optimized `Option<NonZeroU32>` (`size = 4, align = 4`), a
   `#[repr(C)]` struct with padding (`ReprCPaddedHeader`, `size = 12, align = 4`,
   `fieldOffsets = [0, 4, 8]`), a packed struct (`PackedHeader`, `size = 6, align = 1`,
   `fieldOffsets = [0, 1, 5]`), and a slice-tail DST (`PacketWithTail`,
   `headSize = 8, align = 4, fieldOffsets = [0, 4, 8], tailElemSize = 4`).
-/

def r5InnerLibOpenHashBytes : List Nat := [
  65, 77, 73, 82, 3, 3, 11, 196, 79, 3, 1, 121, 1, 3, 9, 2, 4, 1, 6, 3, 3, 3, 3, 3,
  3, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 1, 252, 68, 0, 129, 1, 0,
  7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6,
  0, 2, 252, 71, 0, 129, 16, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 3, 252,
  70, 0, 72, 0, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 17, 0, 0, 131, 0, 64, 2,
  158, 1, 3, 6, 1, 2, 1, 22, 1, 6, 3, 6, 0, 6, 32, 2, 32, 3, 16, 5, 0, 1, 6, 19,
  3, 0, 1, 5, 4, 32, 4, 17, 4, 0, 1, 5, 75, 121, 2, 0, 1, 252, 67, 0, 68, 0, 0, 4,
  33, 4, 33, 3, 33, 2, 17, 0, 0, 131, 0, 64, 3, 152, 1, 3, 4, 1, 2, 4, 17, 4, 4, 0,
  4, 32, 2, 17, 2, 0, 1, 1, 32, 3, 17, 3, 0, 1, 2, 75, 40, 0, 0, 1, 252, 66, 0, 67,
  0, 0, 2, 33, 3, 33, 2, 64
]

def r5ClientAppOpenHashBytes : List Nat := [
  65, 77, 73, 82, 3, 3, 11, 45, 98, 10, 1, 208, 1, 3, 25, 5, 13, 4, 6, 5, 5, 4, 2, 1,
  6, 8, 6, 17, 4, 17, 5, 17, 17, 5, 17, 13, 2, 17, 17, 4, 4, 4, 0, 3, 32, 6, 32, 7,
  19, 7, 0, 1, 1, 4, 75, 121, 6, 0, 1, 252, 71, 0, 129, 5, 0, 17, 33, 7, 33, 6, 32, 8,
  32, 9, 19, 9, 0, 1, 1, 4, 25, 8, 0, 1, 129, 9, 73, 0, 33, 9, 32, 10, 32, 11, 17, 11,
  0, 4, 0, 25, 10, 0, 4, 75, 0, 130, 10, 33, 11, 32, 12, 32, 13, 17, 13, 0, 2, 0, 32, 14,
  17, 14, 0, 74, 0, 75, 168, 12, 0, 2, 11, 77, 0, 78, 0, 0, 7, 33, 14, 33, 13, 32, 15, 32,
  16, 17, 16, 0, 3, 0, 32, 17, 17, 17, 0, 76, 0, 75, 179, 15, 0, 3, 11, 80, 0, 81, 0, 0,
  5, 33, 17, 33, 16, 32, 18, 32, 19, 17, 19, 0, 5, 0, 69, 83, 0, 0, 6, 4, 0, 2, 32, 20,
  17, 20, 0, 79, 0, 76, 112, 18, 0, 5, 11, 84, 0, 130, 2, 130, 6, 0, 1, 33, 20, 68, 8, 0,
  2, 32, 21, 17, 21, 0, 79, 0, 76, 112, 18, 0, 7, 11, 85, 0, 130, 3, 130, 12, 0, 1, 33, 21,
  68, 8, 0, 6, 33, 19, 32, 22, 32, 23, 17, 23, 0, 18, 1, 32, 24, 17, 24, 0, 18, 2, 75, 40,
  22, 0, 9, 11, 87, 0, 88, 0, 0, 8, 33, 24, 33, 23, 17, 0, 0, 22, 0, 33, 22, 33, 18, 33,
  15, 33, 12, 33, 10, 71, 8, 0, 117, 10, 12, 0, 1, 33, 8, 64, 1, 0, 71, 8, 0, 117, 12, 255,
  1, 0, 65, 2, 168, 1, 3, 9, 2, 4, 17, 5, 17, 4, 4, 4, 4, 4, 4, 0, 2, 48, 1, 4,
  32, 3, 73, 211, 3, 0, 1, 252, 0, 5, 32, 4, 32, 5, 17, 5, 0, 2, 1, 32, 6, 17, 6, 0,
  3, 0, 75, 40, 4, 0, 2, 252, 69, 0, 70, 0, 0, 5, 33, 6, 33, 5, 32, 7, 32, 8, 17, 8,
  0, 2, 2, 75, 40, 7, 0, 3, 252, 72, 0, 130, 4, 0, 5, 33, 8, 25, 0, 0, 4, 68, 0, 71,
  0, 33, 7, 33, 4, 33, 3, 64, 3, 179, 1, 3, 9, 2, 4, 17, 5, 17, 4, 4, 4, 4, 4, 4,
  0, 2, 48, 1, 4, 32, 3, 73, 162, 3, 0, 1, 252, 0, 5, 32, 4, 32, 5, 17, 5, 0, 2, 1,
  32, 6, 17, 6, 0, 3, 0, 75, 40, 4, 0, 2, 252, 69, 0, 70, 0, 0, 5, 33, 6, 33, 5, 32,
  7, 32, 8, 17, 8, 0, 2, 2, 75, 40, 7, 0, 3, 252, 72, 0, 130, 8, 0, 5, 33, 8, 25, 0,
  0, 4, 68, 0, 71, 0, 33, 7, 33, 4, 33, 3, 64, 4, 117, 2, 4, 4, 1, 2, 1, 22, 22, 1,
  0, 1, 17, 2, 0, 1, 0, 74, 205, 3, 0, 1, 252, 66, 0, 0, 0, 64, 5, 121, 3, 4, 8, 2,
  4, 1, 6, 3, 3, 3, 3, 3, 3, 0, 1, 17, 4, 0, 1, 5, 75, 20, 3, 0, 1, 252, 68, 0,
  129, 1, 0, 2, 17, 1, 5, 67, 0, 17, 7, 0, 1, 6, 75, 21, 6, 0, 2, 252, 71, 0, 129, 16,
  0, 0, 75, 20, 5, 0, 3, 252, 70, 0, 2, 0, 0, 1, 17, 1, 6, 69, 0, 64, 6, 112, 3, 4,
  7, 3, 4, 13, 17, 4, 4, 4, 4, 4, 0, 0, 74, 152, 4, 0, 1, 252, 1, 0, 0, 0, 75, 40,
  5, 0, 2, 252, 4, 0, 2, 0, 0, 0, 75, 40, 6, 0, 3, 252, 3, 0, 2, 0, 0, 1, 25, 0,
  0, 2, 69, 0, 70, 0, 64, 7, 205, 3, 4, 5, 1, 2, 1, 22, 1, 3, 6, 0, 2, 16, 4, 0,
  1, 6, 17, 3, 0, 1, 5, 75, 121, 2, 0, 1, 252, 4, 0, 67, 0, 0, 0, 64, 8, 152, 3, 4,
  4, 1, 2, 4, 17, 4, 4, 0, 2, 17, 2, 0, 1, 1, 17, 3, 0, 1, 2, 75, 40, 0, 0, 1,
  252, 66, 0, 67, 0, 0, 0, 64, 9, 211, 2, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64,
  10, 162, 2, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 8, 64
]

def r5ClientAppRefactoredOpenHashBytes : List Nat := [
  65, 77, 73, 82, 3, 3, 11, 17, 90, 10, 1, 208, 1, 3, 25, 5, 13, 4, 6, 5, 5, 4, 2, 1,
  6, 8, 6, 17, 4, 17, 5, 17, 17, 5, 17, 13, 2, 17, 17, 4, 4, 4, 0, 3, 32, 6, 32, 7,
  19, 7, 0, 1, 1, 4, 75, 121, 6, 0, 1, 252, 71, 0, 129, 5, 0, 17, 33, 7, 33, 6, 32, 8,
  32, 9, 19, 9, 0, 1, 1, 4, 25, 8, 0, 1, 129, 9, 73, 0, 33, 9, 32, 10, 32, 11, 17, 11,
  0, 4, 0, 25, 10, 0, 4, 75, 0, 130, 10, 33, 11, 32, 12, 32, 13, 17, 13, 0, 2, 0, 32, 14,
  17, 14, 0, 74, 0, 75, 168, 12, 0, 2, 11, 77, 0, 78, 0, 0, 7, 33, 14, 33, 13, 32, 15, 32,
  16, 17, 16, 0, 3, 0, 32, 17, 17, 17, 0, 76, 0, 75, 179, 15, 0, 3, 11, 80, 0, 81, 0, 0,
  5, 33, 17, 33, 16, 32, 18, 32, 19, 17, 19, 0, 5, 0, 69, 83, 0, 0, 6, 4, 0, 2, 32, 20,
  17, 20, 0, 79, 0, 76, 112, 18, 0, 5, 11, 84, 0, 130, 2, 130, 6, 0, 1, 33, 20, 68, 8, 0,
  2, 32, 21, 17, 21, 0, 79, 0, 76, 112, 18, 0, 7, 11, 85, 0, 130, 3, 130, 12, 0, 1, 33, 21,
  68, 8, 0, 6, 33, 19, 32, 22, 32, 23, 17, 23, 0, 18, 1, 32, 24, 17, 24, 0, 18, 2, 75, 40,
  22, 0, 9, 11, 87, 0, 88, 0, 0, 8, 33, 24, 33, 23, 17, 0, 0, 22, 0, 33, 22, 33, 18, 33,
  15, 33, 12, 33, 10, 71, 8, 0, 117, 10, 12, 0, 1, 33, 8, 64, 1, 0, 71, 8, 0, 117, 12, 255,
  1, 0, 65, 2, 168, 1, 3, 11, 2, 4, 17, 5, 17, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 48,
  1, 4, 32, 3, 73, 211, 3, 0, 1, 252, 0, 3, 32, 4, 32, 5, 17, 5, 0, 2, 2, 75, 40, 4,
  0, 2, 252, 69, 0, 130, 4, 0, 6, 33, 5, 32, 6, 32, 7, 17, 7, 0, 2, 1, 32, 8, 17, 8,
  0, 3, 0, 75, 40, 6, 0, 3, 252, 71, 0, 72, 0, 0, 12, 33, 8, 33, 7, 32, 9, 17, 9, 0,
  6, 0, 32, 10, 17, 10, 0, 4, 0, 25, 0, 0, 4, 73, 0, 74, 0, 33, 10, 33, 9, 33, 6, 33,
  4, 33, 3, 64, 3, 179, 1, 3, 11, 2, 4, 17, 5, 17, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2,
  48, 1, 4, 32, 3, 73, 162, 3, 0, 1, 252, 0, 3, 32, 4, 32, 5, 17, 5, 0, 2, 2, 75, 40,
  4, 0, 2, 252, 69, 0, 130, 8, 0, 6, 33, 5, 32, 6, 32, 7, 17, 7, 0, 2, 1, 32, 8, 17,
  8, 0, 3, 0, 75, 40, 6, 0, 3, 252, 71, 0, 72, 0, 0, 12, 33, 8, 33, 7, 32, 9, 17, 9,
  0, 6, 0, 32, 10, 17, 10, 0, 4, 0, 25, 0, 0, 4, 73, 0, 74, 0, 33, 10, 33, 9, 33, 6,
  33, 4, 33, 3, 64, 4, 117, 2, 4, 4, 1, 2, 1, 22, 22, 1, 0, 1, 17, 2, 0, 1, 0, 74,
  205, 3, 0, 1, 252, 66, 0, 0, 0, 64, 5, 121, 3, 4, 8, 2, 4, 1, 6, 3, 3, 3, 3, 3,
  3, 0, 1, 17, 4, 0, 1, 5, 75, 20, 3, 0, 1, 252, 68, 0, 129, 1, 0, 2, 17, 1, 5, 67,
  0, 17, 7, 0, 1, 6, 75, 21, 6, 0, 2, 252, 71, 0, 129, 16, 0, 0, 75, 20, 5, 0, 3, 252,
  70, 0, 2, 0, 0, 1, 17, 1, 6, 69, 0, 64, 6, 112, 3, 4, 7, 3, 4, 13, 17, 4, 4, 4,
  4, 4, 0, 0, 74, 152, 4, 0, 1, 252, 1, 0, 0, 0, 75, 40, 5, 0, 2, 252, 4, 0, 2, 0,
  0, 0, 75, 40, 6, 0, 3, 252, 3, 0, 2, 0, 0, 1, 25, 0, 0, 2, 69, 0, 70, 0, 64, 7,
  205, 3, 4, 5, 1, 2, 1, 22, 1, 3, 6, 0, 2, 16, 4, 0, 1, 6, 17, 3, 0, 1, 5, 75,
  121, 2, 0, 1, 252, 4, 0, 67, 0, 0, 0, 64, 8, 152, 3, 4, 4, 1, 2, 4, 17, 4, 4, 0,
  2, 17, 2, 0, 1, 1, 17, 3, 0, 1, 2, 75, 40, 0, 0, 1, 252, 66, 0, 67, 0, 0, 0, 64,
  9, 211, 2, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64, 10, 162, 2, 4, 1, 0, 1, 4,
  0, 1, 17, 0, 0, 130, 8, 64
]

def r5ClientAppForcedCollisionMod10Bytes : List Nat := [
  65, 77, 73, 82, 3, 3, 11, 254, 116, 10, 1, 78, 1, 3, 25, 5, 13, 4, 6, 5, 5, 4, 2, 1,
  6, 8, 6, 17, 4, 17, 5, 17, 17, 5, 17, 13, 2, 17, 17, 4, 4, 4, 0, 3, 32, 6, 32, 7,
  19, 7, 0, 1, 1, 4, 75, 71, 6, 0, 1, 252, 71, 0, 129, 5, 0, 17, 33, 7, 33, 6, 32, 8,
  32, 9, 19, 9, 0, 1, 1, 4, 25, 8, 0, 1, 129, 9, 73, 0, 33, 9, 32, 10, 32, 11, 17, 11,
  0, 4, 0, 25, 10, 0, 4, 75, 0, 130, 10, 33, 11, 32, 12, 32, 13, 17, 13, 0, 2, 0, 32, 14,
  17, 14, 0, 74, 0, 75, 79, 12, 0, 2, 11, 77, 0, 78, 0, 0, 7, 33, 14, 33, 13, 32, 15, 32,
  16, 17, 16, 0, 3, 0, 32, 17, 17, 17, 0, 76, 0, 75, 70, 15, 0, 3, 11, 80, 0, 81, 0, 0,
  5, 33, 17, 33, 16, 32, 18, 32, 19, 17, 19, 0, 5, 0, 69, 83, 0, 0, 6, 4, 0, 2, 32, 20,
  17, 20, 0, 79, 0, 76, 72, 18, 0, 5, 11, 84, 0, 130, 2, 130, 6, 0, 1, 33, 20, 68, 8, 0,
  2, 32, 21, 17, 21, 0, 79, 0, 76, 72, 18, 0, 7, 11, 85, 0, 130, 3, 130, 12, 0, 1, 33, 21,
  68, 8, 0, 6, 33, 19, 32, 22, 32, 23, 17, 23, 0, 18, 1, 32, 24, 17, 24, 0, 18, 2, 75, 40,
  22, 0, 9, 11, 87, 0, 88, 0, 0, 8, 33, 24, 33, 23, 17, 0, 0, 22, 0, 33, 22, 33, 18, 33,
  15, 33, 12, 33, 10, 71, 8, 0, 77, 10, 12, 0, 1, 33, 8, 64, 1, 0, 71, 8, 0, 77, 12, 255,
  1, 0, 65, 2, 79, 1, 3, 9, 2, 4, 17, 5, 17, 4, 4, 4, 4, 4, 4, 0, 2, 48, 1, 4,
  32, 3, 73, 73, 3, 0, 1, 252, 0, 5, 32, 4, 32, 5, 17, 5, 0, 2, 1, 32, 6, 17, 6, 0,
  3, 0, 75, 40, 4, 0, 2, 252, 69, 0, 70, 0, 0, 5, 33, 6, 33, 5, 32, 7, 32, 8, 17, 8,
  0, 2, 2, 75, 40, 7, 0, 3, 252, 72, 0, 130, 4, 0, 5, 33, 8, 25, 0, 0, 4, 68, 0, 71,
  0, 33, 7, 33, 4, 33, 3, 64, 3, 70, 1, 3, 9, 2, 4, 17, 5, 17, 4, 4, 4, 4, 4, 4,
  0, 2, 48, 1, 4, 32, 3, 73, 74, 3, 0, 1, 252, 0, 5, 32, 4, 32, 5, 17, 5, 0, 2, 1,
  32, 6, 17, 6, 0, 3, 0, 75, 40, 4, 0, 2, 252, 69, 0, 70, 0, 0, 5, 33, 6, 33, 5, 32,
  7, 32, 8, 17, 8, 0, 2, 2, 75, 40, 7, 0, 3, 252, 72, 0, 130, 8, 0, 5, 33, 8, 25, 0,
  0, 4, 68, 0, 71, 0, 33, 7, 33, 4, 33, 3, 64, 4, 77, 2, 4, 4, 1, 2, 1, 22, 22, 1,
  0, 1, 17, 2, 0, 1, 0, 74, 75, 3, 0, 1, 252, 66, 0, 0, 0, 64, 5, 71, 3, 4, 8, 2,
  4, 1, 6, 3, 3, 3, 3, 3, 3, 0, 1, 17, 4, 0, 1, 5, 75, 20, 3, 0, 1, 252, 68, 0,
  129, 1, 0, 2, 17, 1, 5, 67, 0, 17, 7, 0, 1, 6, 75, 21, 6, 0, 2, 252, 71, 0, 129, 16,
  0, 0, 75, 20, 5, 0, 3, 252, 70, 0, 2, 0, 0, 1, 17, 1, 6, 69, 0, 64, 6, 72, 3, 4,
  7, 3, 4, 13, 17, 4, 4, 4, 4, 4, 0, 0, 74, 76, 4, 0, 1, 252, 1, 0, 0, 0, 75, 40,
  5, 0, 2, 252, 4, 0, 2, 0, 0, 0, 75, 40, 6, 0, 3, 252, 3, 0, 2, 0, 0, 1, 25, 0,
  0, 2, 69, 0, 70, 0, 64, 7, 75, 3, 4, 5, 1, 2, 1, 22, 1, 3, 6, 0, 2, 16, 4, 0,
  1, 6, 17, 3, 0, 1, 5, 75, 71, 2, 0, 1, 252, 4, 0, 67, 0, 0, 0, 64, 8, 76, 3, 4,
  4, 1, 2, 4, 17, 4, 4, 0, 2, 17, 2, 0, 1, 1, 17, 3, 0, 1, 2, 75, 40, 0, 0, 1,
  252, 66, 0, 67, 0, 0, 0, 64, 9, 73, 2, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64,
  10, 74, 2, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 8, 64
]

def r5ControlSwappedGenericCalleeBytes : List Nat := [
  65, 77, 73, 82, 3, 3, 11, 45, 98, 10, 1, 208, 1, 3, 25, 5, 13, 4, 6, 5, 5, 4, 2, 1,
  6, 8, 6, 17, 4, 17, 5, 17, 17, 5, 17, 13, 2, 17, 17, 4, 4, 4, 0, 3, 32, 6, 32, 7,
  19, 7, 0, 1, 1, 4, 75, 121, 6, 0, 1, 252, 71, 0, 129, 5, 0, 17, 33, 7, 33, 6, 32, 8,
  32, 9, 19, 9, 0, 1, 1, 4, 25, 8, 0, 1, 129, 9, 73, 0, 33, 9, 32, 10, 32, 11, 17, 11,
  0, 4, 0, 25, 10, 0, 4, 75, 0, 130, 10, 33, 11, 32, 12, 32, 13, 17, 13, 0, 2, 0, 32, 14,
  17, 14, 0, 74, 0, 75, 179, 12, 0, 2, 11, 77, 0, 78, 0, 0, 7, 33, 14, 33, 13, 32, 15, 32,
  16, 17, 16, 0, 3, 0, 32, 17, 17, 17, 0, 76, 0, 75, 179, 15, 0, 3, 11, 80, 0, 81, 0, 0,
  5, 33, 17, 33, 16, 32, 18, 32, 19, 17, 19, 0, 5, 0, 69, 83, 0, 0, 6, 4, 0, 2, 32, 20,
  17, 20, 0, 79, 0, 76, 112, 18, 0, 5, 11, 84, 0, 130, 2, 130, 6, 0, 1, 33, 20, 68, 8, 0,
  2, 32, 21, 17, 21, 0, 79, 0, 76, 112, 18, 0, 7, 11, 85, 0, 130, 3, 130, 12, 0, 1, 33, 21,
  68, 8, 0, 6, 33, 19, 32, 22, 32, 23, 17, 23, 0, 18, 1, 32, 24, 17, 24, 0, 18, 2, 75, 40,
  22, 0, 9, 11, 87, 0, 88, 0, 0, 8, 33, 24, 33, 23, 17, 0, 0, 22, 0, 33, 22, 33, 18, 33,
  15, 33, 12, 33, 10, 71, 8, 0, 117, 10, 12, 0, 1, 33, 8, 64, 1, 0, 71, 8, 0, 117, 12, 255,
  1, 0, 65, 2, 168, 1, 3, 9, 2, 4, 17, 5, 17, 4, 4, 4, 4, 4, 4, 0, 2, 48, 1, 4,
  32, 3, 73, 211, 3, 0, 1, 252, 0, 5, 32, 4, 32, 5, 17, 5, 0, 2, 1, 32, 6, 17, 6, 0,
  3, 0, 75, 40, 4, 0, 2, 252, 69, 0, 70, 0, 0, 5, 33, 6, 33, 5, 32, 7, 32, 8, 17, 8,
  0, 2, 2, 75, 40, 7, 0, 3, 252, 72, 0, 130, 4, 0, 5, 33, 8, 25, 0, 0, 4, 68, 0, 71,
  0, 33, 7, 33, 4, 33, 3, 64, 3, 179, 1, 3, 9, 2, 4, 17, 5, 17, 4, 4, 4, 4, 4, 4,
  0, 2, 48, 1, 4, 32, 3, 73, 162, 3, 0, 1, 252, 0, 5, 32, 4, 32, 5, 17, 5, 0, 2, 1,
  32, 6, 17, 6, 0, 3, 0, 75, 40, 4, 0, 2, 252, 69, 0, 70, 0, 0, 5, 33, 6, 33, 5, 32,
  7, 32, 8, 17, 8, 0, 2, 2, 75, 40, 7, 0, 3, 252, 72, 0, 130, 8, 0, 5, 33, 8, 25, 0,
  0, 4, 68, 0, 71, 0, 33, 7, 33, 4, 33, 3, 64, 4, 117, 2, 4, 4, 1, 2, 1, 22, 22, 1,
  0, 1, 17, 2, 0, 1, 0, 74, 205, 3, 0, 1, 252, 66, 0, 0, 0, 64, 5, 121, 3, 4, 8, 2,
  4, 1, 6, 3, 3, 3, 3, 3, 3, 0, 1, 17, 4, 0, 1, 5, 75, 20, 3, 0, 1, 252, 68, 0,
  129, 1, 0, 2, 17, 1, 5, 67, 0, 17, 7, 0, 1, 6, 75, 21, 6, 0, 2, 252, 71, 0, 129, 16,
  0, 0, 75, 20, 5, 0, 3, 252, 70, 0, 2, 0, 0, 1, 17, 1, 6, 69, 0, 64, 6, 112, 3, 4,
  7, 3, 4, 13, 17, 4, 4, 4, 4, 4, 0, 0, 74, 152, 4, 0, 1, 252, 1, 0, 0, 0, 75, 40,
  5, 0, 2, 252, 4, 0, 2, 0, 0, 0, 75, 40, 6, 0, 3, 252, 3, 0, 2, 0, 0, 1, 25, 0,
  0, 2, 69, 0, 70, 0, 64, 7, 205, 3, 4, 5, 1, 2, 1, 22, 1, 3, 6, 0, 2, 16, 4, 0,
  1, 6, 17, 3, 0, 1, 5, 75, 121, 2, 0, 1, 252, 4, 0, 67, 0, 0, 0, 64, 8, 152, 3, 4,
  4, 1, 2, 4, 17, 4, 4, 0, 2, 17, 2, 0, 1, 1, 17, 3, 0, 1, 2, 75, 40, 0, 0, 1,
  252, 66, 0, 67, 0, 0, 0, 64, 9, 211, 2, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64,
  10, 162, 2, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 8, 64
]

def r5ControlUnclosedExternalBytes : List Nat := [
  65, 77, 73, 82, 3, 3, 11, 45, 98, 10, 1, 208, 1, 3, 25, 5, 13, 4, 6, 5, 5, 4, 2, 1,
  6, 8, 6, 17, 4, 17, 5, 17, 17, 5, 17, 13, 2, 17, 17, 4, 4, 4, 0, 3, 32, 6, 32, 7,
  19, 7, 0, 1, 1, 4, 75, 121, 6, 0, 1, 252, 71, 0, 129, 5, 0, 17, 33, 7, 33, 6, 32, 8,
  32, 9, 19, 9, 0, 1, 1, 4, 25, 8, 0, 1, 129, 9, 73, 0, 33, 9, 32, 10, 32, 11, 17, 11,
  0, 4, 0, 25, 10, 0, 4, 75, 0, 130, 10, 33, 11, 32, 12, 32, 13, 17, 13, 0, 2, 0, 32, 14,
  17, 14, 0, 74, 0, 75, 199, 12, 0, 2, 11, 77, 0, 78, 0, 0, 7, 33, 14, 33, 13, 32, 15, 32,
  16, 17, 16, 0, 3, 0, 32, 17, 17, 17, 0, 76, 0, 75, 179, 15, 0, 3, 11, 80, 0, 81, 0, 0,
  5, 33, 17, 33, 16, 32, 18, 32, 19, 17, 19, 0, 5, 0, 69, 83, 0, 0, 6, 4, 0, 2, 32, 20,
  17, 20, 0, 79, 0, 76, 112, 18, 0, 5, 11, 84, 0, 130, 2, 130, 6, 0, 1, 33, 20, 68, 8, 0,
  2, 32, 21, 17, 21, 0, 79, 0, 76, 112, 18, 0, 7, 11, 85, 0, 130, 3, 130, 12, 0, 1, 33, 21,
  68, 8, 0, 6, 33, 19, 32, 22, 32, 23, 17, 23, 0, 18, 1, 32, 24, 17, 24, 0, 18, 2, 75, 40,
  22, 0, 9, 11, 87, 0, 88, 0, 0, 8, 33, 24, 33, 23, 17, 0, 0, 22, 0, 33, 22, 33, 18, 33,
  15, 33, 12, 33, 10, 71, 8, 0, 117, 10, 12, 0, 1, 33, 8, 64, 1, 0, 71, 8, 0, 117, 12, 255,
  1, 0, 65, 2, 168, 1, 3, 9, 2, 4, 17, 5, 17, 4, 4, 4, 4, 4, 4, 0, 2, 48, 1, 4,
  32, 3, 73, 211, 3, 0, 1, 252, 0, 5, 32, 4, 32, 5, 17, 5, 0, 2, 1, 32, 6, 17, 6, 0,
  3, 0, 75, 40, 4, 0, 2, 252, 69, 0, 70, 0, 0, 5, 33, 6, 33, 5, 32, 7, 32, 8, 17, 8,
  0, 2, 2, 75, 40, 7, 0, 3, 252, 72, 0, 130, 4, 0, 5, 33, 8, 25, 0, 0, 4, 68, 0, 71,
  0, 33, 7, 33, 4, 33, 3, 64, 3, 179, 1, 3, 9, 2, 4, 17, 5, 17, 4, 4, 4, 4, 4, 4,
  0, 2, 48, 1, 4, 32, 3, 73, 162, 3, 0, 1, 252, 0, 5, 32, 4, 32, 5, 17, 5, 0, 2, 1,
  32, 6, 17, 6, 0, 3, 0, 75, 40, 4, 0, 2, 252, 69, 0, 70, 0, 0, 5, 33, 6, 33, 5, 32,
  7, 32, 8, 17, 8, 0, 2, 2, 75, 40, 7, 0, 3, 252, 72, 0, 130, 8, 0, 5, 33, 8, 25, 0,
  0, 4, 68, 0, 71, 0, 33, 7, 33, 4, 33, 3, 64, 4, 117, 2, 4, 4, 1, 2, 1, 22, 22, 1,
  0, 1, 17, 2, 0, 1, 0, 74, 205, 3, 0, 1, 252, 66, 0, 0, 0, 64, 5, 121, 3, 4, 8, 2,
  4, 1, 6, 3, 3, 3, 3, 3, 3, 0, 1, 17, 4, 0, 1, 5, 75, 20, 3, 0, 1, 252, 68, 0,
  129, 1, 0, 2, 17, 1, 5, 67, 0, 17, 7, 0, 1, 6, 75, 21, 6, 0, 2, 252, 71, 0, 129, 16,
  0, 0, 75, 20, 5, 0, 3, 252, 70, 0, 2, 0, 0, 1, 17, 1, 6, 69, 0, 64, 6, 112, 3, 4,
  7, 3, 4, 13, 17, 4, 4, 4, 4, 4, 0, 0, 74, 152, 4, 0, 1, 252, 1, 0, 0, 0, 75, 40,
  5, 0, 2, 252, 4, 0, 2, 0, 0, 0, 75, 40, 6, 0, 3, 252, 3, 0, 2, 0, 0, 1, 25, 0,
  0, 2, 69, 0, 70, 0, 64, 7, 205, 3, 4, 5, 1, 2, 1, 22, 1, 3, 6, 0, 2, 16, 4, 0,
  1, 6, 17, 3, 0, 1, 5, 75, 121, 2, 0, 1, 252, 4, 0, 67, 0, 0, 0, 64, 8, 152, 3, 4,
  4, 1, 2, 4, 17, 4, 4, 0, 2, 17, 2, 0, 1, 1, 17, 3, 0, 1, 2, 75, 40, 0, 0, 1,
  252, 66, 0, 67, 0, 0, 0, 64, 9, 211, 2, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64,
  10, 162, 2, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 8, 64
]

/-- Real on-disk `.amir` v3 capture of `r5_client_app.rs` compiled WITHOUT `-Z mir-preserve-ub`
    (`artifacts/r5_client_app_default_no_preserve_ub.amir`, `778` B, `fp16 = [151, 248]`). -/
def r5ClientAppDefaultNoPreserveUbBytes : List Nat := [
  65, 77, 73, 82, 3, 3, 9, 151, 248, 10, 1, 208, 1, 3, 25, 5, 13, 4, 6, 5, 5, 4, 2, 1,
  6, 8, 6, 17, 4, 17, 5, 17, 17, 5, 17, 13, 2, 17, 17, 4, 4, 4, 0, 3, 32, 6, 32, 7,
  19, 7, 0, 1, 1, 4, 75, 121, 6, 0, 1, 252, 71, 0, 129, 5, 0, 17, 33, 7, 33, 6, 32, 8,
  32, 9, 19, 9, 0, 1, 1, 4, 25, 8, 0, 1, 129, 9, 73, 0, 33, 9, 32, 10, 32, 11, 17, 11,
  0, 4, 0, 25, 10, 0, 4, 75, 0, 130, 10, 33, 11, 32, 12, 32, 13, 17, 13, 0, 2, 0, 32, 14,
  17, 14, 0, 74, 0, 75, 168, 12, 0, 2, 11, 77, 0, 78, 0, 0, 7, 33, 14, 33, 13, 32, 15, 32,
  16, 17, 16, 0, 3, 0, 32, 17, 17, 17, 0, 76, 0, 75, 179, 15, 0, 3, 11, 80, 0, 81, 0, 0,
  5, 33, 17, 33, 16, 32, 18, 32, 19, 17, 19, 0, 5, 0, 69, 83, 0, 0, 6, 4, 0, 2, 32, 20,
  17, 20, 0, 79, 0, 76, 112, 18, 0, 5, 11, 84, 0, 130, 2, 130, 6, 0, 1, 33, 20, 68, 8, 0,
  2, 32, 21, 17, 21, 0, 79, 0, 76, 112, 18, 0, 7, 11, 85, 0, 130, 3, 130, 12, 0, 1, 33, 21,
  68, 8, 0, 6, 33, 19, 32, 22, 32, 23, 17, 23, 0, 18, 1, 32, 24, 17, 24, 0, 18, 2, 75, 40,
  22, 0, 9, 11, 87, 0, 88, 0, 0, 8, 33, 24, 33, 23, 17, 0, 0, 22, 0, 33, 22, 33, 18, 33,
  15, 33, 12, 33, 10, 71, 8, 0, 117, 10, 12, 0, 1, 33, 8, 64, 1, 0, 71, 8, 0, 117, 12, 255,
  1, 0, 65, 2, 168, 1, 3, 9, 2, 4, 17, 5, 17, 4, 4, 4, 4, 4, 4, 0, 1, 32, 3, 73,
  211, 3, 0, 1, 252, 0, 5, 32, 4, 32, 5, 17, 5, 0, 2, 1, 32, 6, 17, 6, 0, 3, 0, 75,
  40, 4, 0, 2, 252, 69, 0, 70, 0, 0, 5, 33, 6, 33, 5, 32, 7, 32, 8, 17, 8, 0, 2, 2,
  75, 40, 7, 0, 3, 252, 72, 0, 130, 4, 0, 5, 33, 8, 25, 0, 0, 4, 68, 0, 71, 0, 33, 7,
  33, 4, 33, 3, 64, 3, 179, 1, 3, 9, 2, 4, 17, 5, 17, 4, 4, 4, 4, 4, 4, 0, 1, 32,
  3, 73, 162, 3, 0, 1, 252, 0, 5, 32, 4, 32, 5, 17, 5, 0, 2, 1, 32, 6, 17, 6, 0, 3,
  0, 75, 40, 4, 0, 2, 252, 69, 0, 70, 0, 0, 5, 33, 6, 33, 5, 32, 7, 32, 8, 17, 8, 0,
  2, 2, 75, 40, 7, 0, 3, 252, 72, 0, 130, 8, 0, 5, 33, 8, 25, 0, 0, 4, 68, 0, 71, 0,
  33, 7, 33, 4, 33, 3, 64, 4, 117, 2, 4, 4, 1, 2, 1, 22, 22, 1, 0, 1, 17, 2, 0, 1,
  0, 74, 205, 3, 0, 1, 252, 66, 0, 0, 0, 64, 5, 121, 3, 4, 8, 2, 4, 1, 6, 3, 3, 3,
  3, 3, 3, 0, 1, 17, 4, 0, 1, 5, 75, 20, 3, 0, 1, 252, 68, 0, 129, 1, 0, 2, 17, 1,
  5, 67, 0, 17, 7, 0, 1, 6, 75, 21, 6, 0, 2, 252, 71, 0, 129, 16, 0, 0, 75, 20, 5, 0,
  3, 252, 70, 0, 2, 0, 0, 1, 17, 1, 6, 69, 0, 64, 6, 112, 3, 4, 7, 3, 4, 13, 17, 4,
  4, 4, 4, 4, 0, 0, 74, 152, 4, 0, 1, 252, 1, 0, 0, 0, 75, 40, 5, 0, 2, 252, 4, 0,
  2, 0, 0, 0, 75, 40, 6, 0, 3, 252, 3, 0, 2, 0, 0, 1, 25, 0, 0, 2, 69, 0, 70, 0,
  64, 7, 205, 3, 4, 5, 1, 2, 1, 22, 1, 3, 6, 0, 2, 16, 4, 0, 1, 6, 17, 3, 0, 1,
  5, 75, 121, 2, 0, 1, 252, 4, 0, 67, 0, 0, 0, 64, 8, 152, 3, 4, 4, 1, 2, 4, 17, 4,
  4, 0, 2, 17, 2, 0, 1, 1, 17, 3, 0, 1, 2, 75, 40, 0, 0, 1, 252, 66, 0, 67, 0, 0,
  0, 64, 9, 211, 2, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64, 10, 162, 2, 4, 1, 0,
  1, 4, 0, 1, 17, 0, 0, 130, 8, 64
]

/-- Real on-disk `.amir` v3 capture of `ext_phase_lib.rs` as a `Runtime(PostCleanup)` (`0x03`)
    sidecar with `-Z mir-preserve-ub` (`artifacts/n5_ext_phase_lib_sidecar.amir`, `58` B, `fp16 = [96, 214]`). -/
def r9ExtPhaseLibPostCleanupSidecarBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 96, 214, 1, 1, 222, 1, 3, 5, 2, 2, 4, 5, 4, 4, 4, 0, 4, 48, 1, 4, 32, 3, 32, 4, 17, 4, 0, 2, 0, 75, 40, 3, 0, 1, 252, 68, 0, 130, 4, 0, 3, 33, 4, 17, 0, 0, 3, 0, 33, 3, 64]

/-- Real on-disk `.amir` v3 capture of `ext_phase_client.rs` importing `libext_phase_lib_default.rlib`
    (`artifacts/n5_ext_phase_client_from_default_rlib.amir`, `107` B, `fp16 = [62, 67]`). -/
def r9ExtPhaseClientFromDefaultRlibBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 62, 67, 2, 1, 220, 1, 3, 7, 2, 3, 4, 5, 4, 4, 5, 4, 4, 0, 5, 32, 3, 32, 4, 17, 4, 0, 1, 0, 32, 5, 17, 5, 0, 2, 0, 75, 222, 3, 0, 1, 252, 68, 0, 69, 0, 0, 4, 33, 5, 33, 4, 32, 6, 17, 6, 0, 3, 0, 75, 40, 0, 0, 2, 252, 70, 0, 130, 10, 0, 2, 33, 6, 33, 3, 64, 2, 222, 3, 4, 3, 2, 2, 4, 5, 4, 0, 0, 75, 40, 0, 0, 1, 252, 2, 0, 130, 4, 0, 0, 64]

/-- Real on-disk `.amir` v3 capture of `ext_phase_client.rs` importing matching-SVH
    `libext_phase_lib_preserve_ub.rlib` (`artifacts/n5_ext_phase_client_from_preserve_ub_rlib.amir`,
    `110` B, `fp16 = [70, 87]`), where `tcx.optimized_mir` (`0x04`) strips `StorageLive`/`StorageDead`. -/
def r9ExtPhaseClientFromPreserveUbRlibBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 70, 87, 2, 1, 220, 1, 3, 7, 2, 3, 4, 5, 4, 4, 5, 4, 4, 0, 5, 32, 3, 32, 4, 17, 4, 0, 1, 0, 32, 5, 17, 5, 0, 2, 0, 75, 222, 3, 0, 1, 252, 68, 0, 69, 0, 0, 4, 33, 5, 33, 4, 32, 6, 17, 6, 0, 3, 0, 75, 40, 0, 0, 2, 252, 70, 0, 130, 10, 0, 2, 33, 6, 33, 3, 64, 2, 222, 3, 4, 3, 2, 2, 4, 5, 4, 0, 1, 48, 1, 4, 75, 40, 0, 0, 1, 252, 2, 0, 130, 4, 0, 0, 64]


def r5InnerLibBodies : List WireBody :=
  decodePackageBodies r5InnerLibOpenHashBytes

def r5ClientAppBodies : List WireBody :=
  decodePackageBodies r5ClientAppOpenHashBytes

def r5ClientAppRefactoredBodies : List WireBody :=
  decodePackageBodies r5ClientAppRefactoredOpenHashBytes

def r5ClientAppForcedCollisionMod10Bodies : List WireBody :=
  decodePackageBodies r5ClientAppForcedCollisionMod10Bytes

def r5ControlSwappedGenericCalleeBodies : List WireBody :=
  decodePackageBodies r5ControlSwappedGenericCalleeBytes

def r5ControlCollapsedCrossCrateAdtBodies : List WireBody :=
  r5ClientAppBodies.map (fun b =>
    if b.symId == 168 then { b with localTypes := b.localTypes.map (fun _ => .refMutEffectLog) } else b)

def r5ClientAppDefaultNoPreserveUbBodies : List WireBody :=
  decodePackageBodies r5ClientAppDefaultNoPreserveUbBytes

def r9ExtPhaseLibPostCleanupSidecarBodies : List WireBody :=
  decodePackageBodies r9ExtPhaseLibPostCleanupSidecarBytes

def r9ExtPhaseClientFromDefaultRlibBodies : List WireBody :=
  decodePackageBodies r9ExtPhaseClientFromDefaultRlibBytes

def r9ExtPhaseClientFromPreserveUbRlibBodies : List WireBody :=
  decodePackageBodies r9ExtPhaseClientFromPreserveUbRlibBytes

/-- Evaluate `verify_multi_crate_pipeline` (`_1: &mut AuditCounter`, `_2: *const u32`,
    `_3: *const u32`, `_4: u32`, `_5: bool`) using `SemanticVerticalSliceCore.runSteps`. -/
def evalOpenHashPipelineWithEntry
    (bodies : List WireBody) (entrySym : Nat)
    (ptr0Valid ptr1Valid : Bool) (rawUnits : Nat) (earlyDrop : Bool) :
    ExecStatus × List HeapLogSlot :=
  let initSt := initEntryStateWithHeap bodies entrySym
    [ .heapPtr 0
    , .extPtr ptr0Valid
    , .extPtr ptr1Valid
    , .scalar rawUnits
    , .scalar (if earlyDrop then 1 else 0) ]
    [{ stepCount := 0, traceAcc := 0 }]
  let st := runSteps bodies 96 initSt
  (st.status, st.heap)

/-- Check whether the 4 cross-crate ADTs in `bodies` (`_1` `AuditCounter`,
    `DropGlue<ScopedTicket>` `_1` `ScopedTicket`, `scale_window_aligned::<u32, 4>` `_1` `WindowSpec`,
    and `execute_outer_pipeline` `_6` `QuotaPair`) carry 4 pairwise-distinct `MirTypeTag`s. -/
def hasDistinctFourCrossCrateAdtTags (bodies : List WireBody) (sEntry sScale32 sOuter sDropTicket : Nat) : Bool :=
  match findBodyBySym bodies sEntry, findBodyBySym bodies sScale32, findBodyBySym bodies sOuter, findBodyBySym bodies sDropTicket with
  | some bEntry, some bScale, some bOuter, some bDrop =>
      let tCounter := getLocalTypeAt bEntry.localTypes 1
      let tWindow := getLocalTypeAt bScale.localTypes 1
      let tQuota := getLocalTypeAt bOuter.localTypes 0
      let tTicket := getLocalTypeAt bDrop.localTypes 1
      !(tCounter == tWindow) && !(tCounter == tQuota) && !(tCounter == tTicket) &&
      !(tWindow == tQuota) && !(tWindow == tTicket) && !(tQuota == tTicket)
  | _, _, _, _ => false

/-- UTF-8 bytes of `"r5_client_app"` and exact 16-bit payload fingerprint recomputation
    matching `compute_fp16` in `direct_mir_driver_v4.rs`. -/
def r5ClientAppCrateNameBytes : List Nat :=
  [114, 53, 95, 99, 108, 105, 101, 110, 116, 95, 97, 112, 112]

def fp16CrateLoop (acc : Nat) : List Nat → Nat
  | [] => acc
  | b :: bs => fp16CrateLoop (((acc * 31) + b) % 65536) bs

def fp16PayloadLoop (acc : Nat) : List Nat → Nat
  | [] => acc
  | b :: bs => fp16PayloadLoop (((acc * 131) + b) % 65536) bs

def recomputeR6PayloadFp16 (crateNameBytes : List Nat) (rawBytes : List Nat) : Nat × Nat :=
  let acc0 := fp16CrateLoop 0x5A3C crateNameBytes
  let acc := fp16PayloadLoop acc0 (rawBytes.drop 10)
  ((acc / 256) % 256, acc % 256)

/-- Compiler-verified post-run endorsement record (`R6`, `U9`, `#89` §12), bound directly to
    the admitted `.amir` v3 package bytes and recomputed payload fingerprint `expectedFp16`. -/
structure PostRunEndorsedArtifactRecord where
  phaseByte : Nat
  preserveUb : Bool
  monoComplete : Bool
  compilerRunExitZero : Bool
  postRunCompilerVerified : Bool
  noDelayedDiagErrors : Bool
  amirBytesPresentOnDisk : Bool
  outJsonWriteSucceeded : Bool
  expectedFp16 : Nat × Nat
  packageBytes : List Nat
  deriving DecidableEq, Repr

def verifyPostRunEndorsedArtifact (r : PostRunEndorsedArtifactRecord) : Bool :=
  (r.phaseByte == 3) &&
  r.preserveUb &&
  r.monoComplete &&
  r.compilerRunExitZero &&
  r.postRunCompilerVerified &&
  r.noDelayedDiagErrors &&
  r.amirBytesPresentOnDisk &&
  r.outJsonWriteSucceeded &&
  isAdmittedPackageBytes r.packageBytes &&
  (recomputeR6PayloadFp16 r5ClientAppCrateNameBytes r.packageBytes == r.expectedFp16) &&
  (r.packageBytes.getD 5 0 == 3)

def r6EndorsedClientAppRecord : PostRunEndorsedArtifactRecord :=
  { phaseByte := 3
  , preserveUb := true
  , monoComplete := true
  , compilerRunExitZero := true
  , postRunCompilerVerified := true
  , noDelayedDiagErrors := true
  , amirBytesPresentOnDisk := true
  , outJsonWriteSucceeded := true
  , expectedFp16 := (45, 98)
  , packageBytes := r5ClientAppOpenHashBytes }

def r6Control6aRuntimeInitialRecord : PostRunEndorsedArtifactRecord :=
  { r6EndorsedClientAppRecord with phaseByte := 5, postRunCompilerVerified := false, amirBytesPresentOnDisk := false }

def r6Control6bEarlyCompileErrorRecord : PostRunEndorsedArtifactRecord :=
  { r6EndorsedClientAppRecord with compilerRunExitZero := false, postRunCompilerVerified := false, amirBytesPresentOnDisk := false }

def r6Control6cInterruptedBeforeEndorsementRecord : PostRunEndorsedArtifactRecord :=
  { r6EndorsedClientAppRecord with postRunCompilerVerified := false }

def r6Control6dPostAnalysisErrorRecord : PostRunEndorsedArtifactRecord :=
  { r6EndorsedClientAppRecord with compilerRunExitZero := false, postRunCompilerVerified := false, noDelayedDiagErrors := false, amirBytesPresentOnDisk := false }

def r6Control6eOutJsonWriteErrorRecord : PostRunEndorsedArtifactRecord :=
  { r6EndorsedClientAppRecord with compilerRunExitZero := false, postRunCompilerVerified := false, outJsonWriteSucceeded := false }

def r6Control6fTamperedFp16Record : PostRunEndorsedArtifactRecord :=
  { r6EndorsedClientAppRecord with expectedFp16 := (45, 99) }

/-- Compiler-queried `LayoutOf` descriptor (`R10`, `#89` §16) matching `computed_layouts`
    in `out_r5_inner_lib_open_hash.json`. -/
structure QueriedLayoutRecord where
  typeNameId : Nat
  sizeBytes : Nat
  alignBytes : Nat
  fieldOffsetsBytes : List Nat
  isUnsizedSliceTail : Bool
  tailElemSizeBytes : Nat
  tailElemAlignBytes : Nat
  hasNiche : Bool
  deriving DecidableEq, Repr

def r5WindowSpecLayout : QueriedLayoutRecord :=
  { typeNameId := 1
  , sizeBytes := 16
  , alignBytes := 8
  , fieldOffsetsBytes := [0, 8]
  , isUnsizedSliceTail := false
  , tailElemSizeBytes := 0
  , tailElemAlignBytes := 0
  , hasNiche := false }

def r5AuditCounterLayout : QueriedLayoutRecord :=
  { typeNameId := 2
  , sizeBytes := 8
  , alignBytes := 4
  , fieldOffsetsBytes := [0, 4]
  , isUnsizedSliceTail := false
  , tailElemSizeBytes := 0
  , tailElemAlignBytes := 0
  , hasNiche := false }

def r5ScopedTicketLayout : QueriedLayoutRecord :=
  { typeNameId := 3
  , sizeBytes := 16
  , alignBytes := 8
  , fieldOffsetsBytes := [8, 0]
  , isUnsizedSliceTail := false
  , tailElemSizeBytes := 0
  , tailElemAlignBytes := 0
  , hasNiche := false }

def r10OptionNonZeroU32Layout : QueriedLayoutRecord :=
  { typeNameId := 101
  , sizeBytes := 4
  , alignBytes := 4
  , fieldOffsetsBytes := [0]
  , isUnsizedSliceTail := false
  , tailElemSizeBytes := 0
  , tailElemAlignBytes := 0
  , hasNiche := true }

def r10ReprCPaddedHeaderLayout : QueriedLayoutRecord :=
  { typeNameId := 102
  , sizeBytes := 12
  , alignBytes := 4
  , fieldOffsetsBytes := [0, 4, 8]
  , isUnsizedSliceTail := false
  , tailElemSizeBytes := 0
  , tailElemAlignBytes := 0
  , hasNiche := false }

def r10PackedHeaderLayout : QueriedLayoutRecord :=
  { typeNameId := 103
  , sizeBytes := 6
  , alignBytes := 1
  , fieldOffsetsBytes := [0, 1, 5]
  , isUnsizedSliceTail := false
  , tailElemSizeBytes := 0
  , tailElemAlignBytes := 0
  , hasNiche := false }

def r10PacketWithTailDstLayout : QueriedLayoutRecord :=
  { typeNameId := 104
  , sizeBytes := 8
  , alignBytes := 4
  , fieldOffsetsBytes := [0, 4, 8]
  , isUnsizedSliceTail := true
  , tailElemSizeBytes := 4
  , tailElemAlignBytes := 4
  , hasNiche := false }

/-- Complete 7-entry `computed_layouts` table from `out_r5_inner_lib_open_hash.json:24`. -/
def r5InnerLibComputedLayouts : List QueriedLayoutRecord :=
  [ r5WindowSpecLayout
  , r5AuditCounterLayout
  , r5ScopedTicketLayout
  , r10OptionNonZeroU32Layout
  , r10ReprCPaddedHeaderLayout
  , r10PackedHeaderLayout
  , r10PacketWithTailDstLayout ]

def computeDstTotalSizeChecked (d : QueriedLayoutRecord) (elemCount : Nat) : Option Nat :=
  if !d.isUnsizedSliceTail || d.alignBytes == 0 then none
  else
    let rawBytes := d.sizeBytes + elemCount * d.tailElemSizeBytes
    let rem := rawBytes % d.alignBytes
    let pad := if rem == 0 then 0 else d.alignBytes - rem
    some (rawBytes + pad)

theorem r5_packages_admitted_part1 :
    isAdmittedPackageBytes r5InnerLibOpenHashBytes = true ∧
    isAdmittedPackageBytes r5ClientAppOpenHashBytes = true := by
  decide

theorem r5_packages_admitted_part2 :
    isAdmittedPackageBytes r5ClientAppRefactoredOpenHashBytes = true ∧
    isAdmittedPackageBytes r5ClientAppForcedCollisionMod10Bytes = true := by
  decide

theorem r5_open_hash_packages_admitted :
    isAdmittedPackageBytes r5InnerLibOpenHashBytes = true ∧
    isAdmittedPackageBytes r5ClientAppOpenHashBytes = true ∧
    isAdmittedPackageBytes r5ClientAppRefactoredOpenHashBytes = true ∧
    isAdmittedPackageBytes r5ClientAppForcedCollisionMod10Bytes = true :=
  ⟨r5_packages_admitted_part1.1, r5_packages_admitted_part1.2,
   r5_packages_admitted_part2.1, r5_packages_admitted_part2.2⟩

theorem r5_exec_baseline_normal :
    evalOpenHashPipelineWithEntry r5ClientAppBodies 208 true true 10 true =
      (.returned (.scalar 54), [{ stepCount := 2, traceAcc := 89 }]) ∧
    evalOpenHashPipelineWithEntry r5ClientAppBodies 208 true true 10 false =
      (.returned (.scalar 62), [{ stepCount := 2, traceAcc := 89 }]) := by
  decide

theorem r5_exec_baseline_ub :
    evalOpenHashPipelineWithEntry r5ClientAppBodies 208 false true 10 true =
      (.ub, [{ stepCount := 1, traceAcc := 5 }]) ∧
    evalOpenHashPipelineWithEntry r5ClientAppBodies 208 true false 10 true =
      (.ub, [{ stepCount := 1, traceAcc := 5 }]) := by
  decide

theorem r5_exec_refactored_and_collision :
    evalOpenHashPipelineWithEntry r5ClientAppRefactoredBodies 208 true true 10 true =
      (.returned (.scalar 54), [{ stepCount := 2, traceAcc := 89 }]) ∧
    evalOpenHashPipelineWithEntry r5ClientAppRefactoredBodies 208 true true 10 false =
      (.returned (.scalar 62), [{ stepCount := 2, traceAcc := 89 }]) ∧
    evalOpenHashPipelineWithEntry r5ClientAppForcedCollisionMod10Bodies 78 true true 10 true =
      (.returned (.scalar 54), [{ stepCount := 2, traceAcc := 89 }]) ∧
    evalOpenHashPipelineWithEntry r5ClientAppForcedCollisionMod10Bodies 78 true true 10 false =
      (.returned (.scalar 62), [{ stepCount := 2, traceAcc := 89 }]) := by
  decide

theorem r5_open_hash_multi_crate_execution_and_refactor_and_collision_verified :
    evalOpenHashPipelineWithEntry r5ClientAppBodies 208 true true 10 true =
      (.returned (.scalar 54), [{ stepCount := 2, traceAcc := 89 }]) ∧
    evalOpenHashPipelineWithEntry r5ClientAppBodies 208 true true 10 false =
      (.returned (.scalar 62), [{ stepCount := 2, traceAcc := 89 }]) ∧
    evalOpenHashPipelineWithEntry r5ClientAppBodies 208 false true 10 true =
      (.ub, [{ stepCount := 1, traceAcc := 5 }]) ∧
    evalOpenHashPipelineWithEntry r5ClientAppBodies 208 true false 10 true =
      (.ub, [{ stepCount := 1, traceAcc := 5 }]) ∧
    evalOpenHashPipelineWithEntry r5ClientAppRefactoredBodies 208 true true 10 true =
      (.returned (.scalar 54), [{ stepCount := 2, traceAcc := 89 }]) ∧
    evalOpenHashPipelineWithEntry r5ClientAppRefactoredBodies 208 true true 10 false =
      (.returned (.scalar 62), [{ stepCount := 2, traceAcc := 89 }]) ∧
    evalOpenHashPipelineWithEntry r5ClientAppForcedCollisionMod10Bodies 78 true true 10 true =
      (.returned (.scalar 54), [{ stepCount := 2, traceAcc := 89 }]) ∧
    evalOpenHashPipelineWithEntry r5ClientAppForcedCollisionMod10Bodies 78 true true 10 false =
      (.returned (.scalar 62), [{ stepCount := 2, traceAcc := 89 }]) :=
  ⟨r5_exec_baseline_normal.1, r5_exec_baseline_normal.2,
   r5_exec_baseline_ub.1, r5_exec_baseline_ub.2,
   r5_exec_refactored_and_collision.1, r5_exec_refactored_and_collision.2.1,
   r5_exec_refactored_and_collision.2.2.1, r5_exec_refactored_and_collision.2.2.2⟩

theorem r5_controls_part1 :
    hasDistinctFourCrossCrateAdtTags r5ClientAppBodies 208 168 117 152 = true ∧
    hasDistinctFourCrossCrateAdtTags r5ControlCollapsedCrossCrateAdtBodies 208 168 117 152 = false ∧
    isAdmittedPackageBytes r5ControlUnclosedExternalBytes = false := by
  decide

theorem r5_controls_part2 :
    isAdmittedPackageBytes r5ControlSwappedGenericCalleeBytes = true ∧
    evalOpenHashPipelineWithEntry r5ControlSwappedGenericCalleeBodies 208 true true 10 true =
      (.returned (.scalar 62), [{ stepCount := 2, traceAcc := 89 }]) ∧
    (evalOpenHashPipelineWithEntry r5ControlSwappedGenericCalleeBodies 208 true true 10 true !=
      evalOpenHashPipelineWithEntry r5ClientAppBodies 208 true true 10 true) = true := by
  decide

theorem r5_all_negative_controls_verified :
    hasDistinctFourCrossCrateAdtTags r5ClientAppBodies 208 168 117 152 = true ∧
    hasDistinctFourCrossCrateAdtTags r5ControlCollapsedCrossCrateAdtBodies 208 168 117 152 = false ∧
    isAdmittedPackageBytes r5ControlSwappedGenericCalleeBytes = true ∧
    evalOpenHashPipelineWithEntry r5ControlSwappedGenericCalleeBodies 208 true true 10 true =
      (.returned (.scalar 62), [{ stepCount := 2, traceAcc := 89 }]) ∧
    (evalOpenHashPipelineWithEntry r5ControlSwappedGenericCalleeBodies 208 true true 10 true !=
      evalOpenHashPipelineWithEntry r5ClientAppBodies 208 true true 10 true) = true ∧
    isAdmittedPackageBytes r5ControlUnclosedExternalBytes = false :=
  ⟨r5_controls_part1.1, r5_controls_part1.2.1,
   r5_controls_part2.1, r5_controls_part2.2.1, r5_controls_part2.2.2,
   r5_controls_part1.2.2⟩

theorem r6_post_run_endorsement_and_five_controls_verified :
    verifyPostRunEndorsedArtifact r6EndorsedClientAppRecord = true ∧
    verifyPostRunEndorsedArtifact r6Control6aRuntimeInitialRecord = false ∧
    verifyPostRunEndorsedArtifact r6Control6bEarlyCompileErrorRecord = false ∧
    verifyPostRunEndorsedArtifact r6Control6cInterruptedBeforeEndorsementRecord = false ∧
    verifyPostRunEndorsedArtifact r6Control6dPostAnalysisErrorRecord = false ∧
    verifyPostRunEndorsedArtifact r6Control6eOutJsonWriteErrorRecord = false ∧
    verifyPostRunEndorsedArtifact r6Control6fTamperedFp16Record = false := by
  decide

theorem r9_cross_crate_postcleanup_sidecar_vs_rlib_optimized_mir_discriminator :
    isAdmittedPackageBytes r5ClientAppDefaultNoPreserveUbBytes = true ∧
    isAdmittedPackageBytes r9ExtPhaseLibPostCleanupSidecarBytes = true ∧
    isAdmittedPackageBytes r9ExtPhaseClientFromDefaultRlibBytes = true ∧
    isAdmittedPackageBytes r9ExtPhaseClientFromPreserveUbRlibBytes = true ∧
    evalOpenHashPipelineWithEntry r5ClientAppBodies 208 true false 10 true =
      (.ub, [{ stepCount := 1, traceAcc := 5 }]) ∧
    evalOpenHashPipelineWithEntry r5ClientAppDefaultNoPreserveUbBodies 208 true false 10 true =
      (.returned (.scalar 54), [{ stepCount := 2, traceAcc := 89 }]) ∧
    (evalOpenHashPipelineWithEntry r5ClientAppBodies 208 true false 10 true !=
      evalOpenHashPipelineWithEntry r5ClientAppDefaultNoPreserveUbBodies 208 true false 10 true) = true ∧
    ((findBodyBySym r9ExtPhaseLibPostCleanupSidecarBodies 222).map (fun b => (b.mirPhase, b.localCount)) ==
      some (MirPhaseTag.runtimePostCleanup, 5)) = true ∧
    ((findBodyBySym r9ExtPhaseClientFromPreserveUbRlibBodies 222).map (fun b => (b.mirPhase, b.localCount)) ==
      some (MirPhaseTag.runtimeOptimized, 3)) = true := by
  decide

theorem r10_queried_layout_and_abi_witnesses_verified :
    r5InnerLibComputedLayouts.length = 7 ∧
    r5WindowSpecLayout.sizeBytes = 16 ∧
    r5AuditCounterLayout.sizeBytes = 8 ∧
    r5ScopedTicketLayout.fieldOffsetsBytes = [8, 0] ∧
    r10OptionNonZeroU32Layout.sizeBytes = 4 ∧
    r10OptionNonZeroU32Layout.hasNiche = true ∧
    r10ReprCPaddedHeaderLayout.sizeBytes = 12 ∧
    r10ReprCPaddedHeaderLayout.fieldOffsetsBytes = [0, 4, 8] ∧
    r10PackedHeaderLayout.sizeBytes = 6 ∧
    r10PackedHeaderLayout.alignBytes = 1 ∧
    r10PackedHeaderLayout.fieldOffsetsBytes = [0, 1, 5] ∧
    computeDstTotalSizeChecked r10PacketWithTailDstLayout 0 = some 8 ∧
    computeDstTotalSizeChecked r10PacketWithTailDstLayout 3 = some 20 ∧
    computeDstTotalSizeChecked r10ReprCPaddedHeaderLayout 3 = none := by
  decide

#print axioms r5_open_hash_packages_admitted
#print axioms r5_open_hash_multi_crate_execution_and_refactor_and_collision_verified
#print axioms r5_all_negative_controls_verified
#print axioms r6_post_run_endorsement_and_five_controls_verified
#print axioms r9_cross_crate_postcleanup_sidecar_vs_rlib_optimized_mir_discriminator
#print axioms r10_queried_layout_and_abi_witnesses_verified

/-! ## 5. `Q3` (`F3`, `#93` §8): Repaired 4-ADT Local Type Witness & Two-Nominal-Pair Cross-Crate Challenge (`MeterReading` vs `LimitThreshold`) -/

/-- Extracts the actual 4 cross-crate ADT local type tags in `r5ClientAppBodies`
    (`symId = 208` `_1: &mut AuditCounter`, `_8: ScopedTicket`, `_10: WindowSpec`, `_18: QuotaPair`),
    together with their cross-body occurrences in `symId = 168` (`_0: WindowSpec`, `_2: WindowSpec`),
    `symId = 112` (`_0: QuotaPair`), and `symId = 117` (`_1: *mut ScopedTicket`). -/
def extractFourActualCrossCrateAdtTagsQ3 (bodies : List WireBody) : Option (List MirTypeTag) :=
  match findBodyBySym bodies 208, findBodyBySym bodies 168, findBodyBySym bodies 112, findBodyBySym bodies 117 with
  | some bEntry, some bScale, some bQuota, some bDrop =>
      let tCounter := getLocalTypeAt bEntry.localTypes 1
      let tTicket := getLocalTypeAt bEntry.localTypes 8
      let tWindowEntry := getLocalTypeAt bEntry.localTypes 10
      let tQuotaEntry := getLocalTypeAt bEntry.localTypes 18
      let tWindowRet := getLocalTypeAt bScale.localTypes 0
      let tWindowArg := getLocalTypeAt bScale.localTypes 2
      let tQuotaRet := getLocalTypeAt bQuota.localTypes 0
      let tTicketRef := getLocalTypeAt bDrop.localTypes 1
      if (tWindowEntry == tWindowRet) && (tWindowRet == tWindowArg) &&
         (tQuotaEntry == tQuotaRet) && (tTicketRef == .refGuard) &&
         !(tCounter == .unit) && !(tCounter == .rawPtrU32) &&
         !(tTicket == .unit) && !(tTicket == .rawPtrU32) &&
         !(tWindowRet == .unit) && !(tWindowRet == .rawPtrU32) &&
         !(tQuotaRet == .unit) && !(tQuotaRet == .rawPtrU32) then
        some [tCounter, tTicket, tWindowRet, tQuotaRet]
      else
        none
  | _, _, _, _ => none

def hasDistinctFourActualCrossCrateAdtTagsQ3 (bodies : List WireBody) : Bool :=
  match extractFourActualCrossCrateAdtTagsQ3 bodies with
  | some [t1, t2, t3, t4] =>
      !(t1 == t2) && !(t1 == t3) && !(t1 == t4) &&
      !(t2 == t3) && !(t2 == t4) && !(t3 == t4)
  | _ => false

/-- Real on-disk `.amir` v3 capture of `q3_nominal_pair_lib.rs` (`artifacts/q3_nominal_pair_lib.amir`, `218` B),
    defining two same-shaped `{u32, u32}` nominal structs `MeterReading` (`tyTag = 7`, `agg2Tag = 3`)
    and `LimitThreshold` (`tyTag = 12`, `agg2Tag = 4`). -/
def q3NominalPairLibBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 235, 49, 3, 1, 104, 1, 3, 6, 2, 2, 7, 3, 3, 3, 3, 3, 0, 5, 32, 3, 32, 4, 17, 4, 0, 1, 0, 32, 5, 17, 5, 0, 2, 0, 75, 20, 3, 0, 1, 252, 68, 0, 69, 0, 0, 4, 33, 5, 33, 4, 25, 0, 0, 3, 67, 0, 129, 1, 33, 3, 64, 2, 162, 1, 3, 7, 2, 2, 12, 3, 3, 3, 3, 3, 3, 0, 7, 32, 3, 17, 3, 0, 1, 0, 32, 4, 32, 5, 17, 5, 0, 1, 0, 32, 6, 17, 6, 0, 2, 0, 75, 20, 4, 0, 1, 252, 69, 0, 70, 0, 0, 5, 33, 6, 33, 5, 25, 0, 0, 4, 67, 0, 68, 0, 33, 4, 33, 3, 64, 3, 166, 1, 3, 8, 2, 3, 3, 7, 12, 3, 3, 3, 3, 3, 0, 5, 32, 3, 32, 4, 17, 4, 0, 1, 1, 32, 5, 17, 5, 0, 2, 1, 75, 20, 3, 0, 1, 252, 68, 0, 69, 0, 0, 6, 33, 5, 33, 4, 32, 6, 17, 6, 0, 3, 0, 32, 7, 17, 7, 0, 2, 2, 75, 20, 0, 0, 2, 252, 70, 0, 71, 0, 0, 3, 33, 7, 33, 6, 33, 3, 64]

/-- Real on-disk `.amir` v3 capture of `q3_nominal_pair_client.rs` (`artifacts/q3_nominal_pair_client.amir`, `280` B). -/
def q3NominalPairClientBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 162, 63, 4, 1, 176, 1, 3, 13, 2, 5, 3, 3, 3, 7, 3, 3, 3, 12, 3, 7, 12, 3, 3, 0, 5, 32, 3, 32, 4, 17, 4, 0, 1, 0, 32, 5, 17, 5, 0, 2, 0, 75, 104, 3, 0, 1, 252, 68, 0, 69, 0, 0, 5, 33, 5, 33, 4, 32, 6, 17, 6, 0, 3, 2, 32, 7, 75, 162, 7, 0, 2, 252, 129, 10, 129, 20, 0, 5, 32, 8, 32, 9, 17, 9, 0, 67, 0, 32, 10, 17, 10, 0, 71, 0, 75, 166, 8, 0, 3, 252, 73, 0, 74, 0, 0, 6, 33, 10, 33, 9, 32, 11, 17, 11, 0, 8, 0, 32, 12, 17, 12, 0, 6, 0, 75, 20, 0, 0, 4, 252, 75, 0, 76, 0, 0, 6, 33, 12, 33, 11, 33, 8, 33, 7, 33, 6, 33, 3, 64, 2, 104, 3, 4, 4, 2, 2, 7, 3, 3, 3, 0, 0, 75, 20, 3, 0, 1, 252, 1, 0, 2, 0, 0, 1, 25, 0, 0, 3, 67, 0, 129, 1, 64, 3, 162, 3, 4, 4, 2, 2, 12, 3, 3, 3, 0, 0, 75, 20, 3, 0, 1, 252, 1, 0, 2, 0, 0, 1, 25, 0, 0, 4, 1, 0, 67, 0, 64, 4, 166, 3, 4, 7, 2, 3, 3, 7, 12, 3, 3, 3, 3, 0, 2, 17, 4, 0, 1, 1, 17, 5, 0, 2, 1, 75, 20, 3, 0, 1, 252, 68, 0, 69, 0, 0, 1, 17, 6, 0, 2, 2, 75, 20, 0, 0, 2, 252, 3, 0, 70, 0, 0, 0, 64]

/-- Real on-disk `.amir` v3 capture of `q3_nominal_pair_client_refactored.rs` (`artifacts/q3_nominal_pair_client_refactored.amir`, `290` B). -/
def q3NominalPairClientRefactoredBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 93, 34, 4, 1, 176, 1, 3, 14, 2, 5, 3, 3, 3, 7, 3, 3, 3, 12, 3, 7, 12, 3, 3, 3, 0, 5, 32, 3, 32, 4, 17, 4, 0, 1, 0, 32, 5, 17, 5, 0, 2, 0, 75, 104, 3, 0, 1, 252, 68, 0, 69, 0, 0, 5, 33, 5, 33, 4, 32, 6, 17, 6, 0, 3, 2, 32, 7, 75, 162, 7, 0, 2, 252, 129, 10, 129, 20, 0, 5, 32, 8, 32, 9, 17, 9, 0, 67, 0, 32, 10, 17, 10, 0, 71, 0, 75, 166, 8, 0, 3, 252, 73, 0, 74, 0, 0, 7, 33, 10, 33, 9, 32, 11, 32, 12, 17, 12, 0, 8, 0, 32, 13, 17, 13, 0, 6, 0, 75, 20, 11, 0, 4, 252, 76, 0, 77, 0, 0, 8, 33, 13, 33, 12, 17, 0, 0, 11, 0, 33, 11, 33, 8, 33, 7, 33, 6, 33, 3, 64, 2, 104, 3, 4, 4, 2, 2, 7, 3, 3, 3, 0, 0, 75, 20, 3, 0, 1, 252, 1, 0, 2, 0, 0, 1, 25, 0, 0, 3, 67, 0, 129, 1, 64, 3, 162, 3, 4, 4, 2, 2, 12, 3, 3, 3, 0, 0, 75, 20, 3, 0, 1, 252, 1, 0, 2, 0, 0, 1, 25, 0, 0, 4, 1, 0, 67, 0, 64, 4, 166, 3, 4, 7, 2, 3, 3, 7, 12, 3, 3, 3, 3, 0, 2, 17, 4, 0, 1, 1, 17, 5, 0, 2, 1, 75, 20, 3, 0, 1, 252, 68, 0, 69, 0, 0, 1, 17, 6, 0, 2, 2, 75, 20, 0, 0, 2, 252, 3, 0, 70, 0, 0, 0, 64]

/-- Real on-disk `.amir` v3 capture of `q3_nominal_pair_client_swapped_sig.rs` (`artifacts/q3_nominal_pair_client_swapped_sig.amir`, `280` B). -/
def q3NominalPairClientSwappedSigBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 213, 14, 4, 1, 176, 1, 3, 13, 2, 5, 3, 3, 3, 7, 3, 12, 3, 3, 3, 12, 7, 3, 3, 0, 1, 32, 3, 75, 162, 3, 0, 1, 252, 129, 10, 129, 20, 0, 7, 32, 4, 17, 4, 0, 3, 1, 32, 5, 32, 6, 17, 6, 0, 1, 0, 32, 7, 17, 7, 0, 2, 0, 75, 104, 5, 0, 2, 252, 70, 0, 71, 0, 0, 7, 33, 7, 33, 6, 32, 8, 32, 9, 17, 9, 0, 69, 0, 32, 10, 17, 10, 0, 67, 0, 75, 166, 8, 0, 3, 252, 73, 0, 74, 0, 0, 6, 33, 10, 33, 9, 32, 11, 17, 11, 0, 8, 0, 32, 12, 17, 12, 0, 4, 0, 75, 20, 0, 0, 4, 252, 75, 0, 76, 0, 0, 6, 33, 12, 33, 11, 33, 8, 33, 5, 33, 4, 33, 3, 64, 2, 162, 3, 4, 4, 2, 2, 7, 3, 3, 3, 0, 0, 75, 20, 3, 0, 1, 252, 1, 0, 2, 0, 0, 1, 25, 0, 0, 3, 1, 0, 67, 0, 64, 3, 104, 3, 4, 4, 2, 2, 12, 3, 3, 3, 0, 0, 75, 20, 3, 0, 1, 252, 1, 0, 2, 0, 0, 1, 25, 0, 0, 4, 67, 0, 129, 1, 64, 4, 166, 3, 4, 7, 2, 3, 3, 12, 7, 3, 3, 3, 3, 0, 2, 17, 4, 0, 1, 1, 17, 5, 0, 2, 1, 75, 20, 3, 0, 1, 252, 68, 0, 69, 0, 0, 1, 17, 6, 0, 2, 2, 75, 20, 0, 0, 2, 252, 3, 0, 70, 0, 0, 0, 64]

def q3NominalPairClientBodies : List WireBody :=
  decodePackageBodies q3NominalPairClientBytes

def q3NominalPairClientRefactoredBodies : List WireBody :=
  decodePackageBodies q3NominalPairClientRefactoredBytes

def q3NominalPairClientSwappedSigBodies : List WireBody :=
  decodePackageBodies q3NominalPairClientSwappedSigBytes

def evalNominalPairPipelineQ3 (bodies : List WireBody) (seed delta : Nat) : ExecStatus :=
  let initSt := initEntryStateWithHeap bodies 176 [.scalar seed, .scalar delta] []
  (runSteps bodies 48 initSt).status

def checkNominalPairClientTypesQ3 (bodies : List WireBody) : Bool :=
  match findBodyBySym bodies 176, findBodyBySym bodies 104, findBodyBySym bodies 162, findBodyBySym bodies 166 with
  | some b176, some b104, some b162, some b166 =>
      (getLocalTypeAt b176.localTypes 3 == .effectLog) &&
      (getLocalTypeAt b176.localTypes 7 == .optUsize) &&
      (getLocalTypeAt b176.localTypes 9 == .effectLog) &&
      (getLocalTypeAt b176.localTypes 10 == .optUsize) &&
      (getLocalTypeAt b104.localTypes 0 == .effectLog) &&
      (getLocalTypeAt b162.localTypes 0 == .optUsize) &&
      (getLocalTypeAt b166.localTypes 1 == .effectLog) &&
      (getLocalTypeAt b166.localTypes 2 == .optUsize) &&
      !(getLocalTypeAt b104.localTypes 0 == getLocalTypeAt b162.localTypes 0)
  | _, _, _, _ => false

theorem q3_four_actual_adt_tags_verified :
    extractFourActualCrossCrateAdtTagsQ3 r5ClientAppBodies =
      some [.refMutEffectLog, .guard, .pairUsize, .optPairUsize] ∧
    hasDistinctFourActualCrossCrateAdtTagsQ3 r5ClientAppBodies = true ∧
    hasDistinctFourActualCrossCrateAdtTagsQ3 r5ClientAppRefactoredBodies = true ∧
    hasDistinctFourActualCrossCrateAdtTagsQ3 r5ControlCollapsedCrossCrateAdtBodies = false := by
  decide

theorem q3_nominal_pair_packages_admitted :
    isAdmittedPackageBytes q3NominalPairLibBytes = true ∧
    isAdmittedPackageBytes q3NominalPairClientBytes = true ∧
    isAdmittedPackageBytes q3NominalPairClientRefactoredBytes = true ∧
    isAdmittedPackageBytes q3NominalPairClientSwappedSigBytes = true := by
  decide

theorem q3_nominal_pair_types_and_execution :
    checkNominalPairClientTypesQ3 q3NominalPairClientBodies = true ∧
    checkNominalPairClientTypesQ3 q3NominalPairClientRefactoredBodies = true ∧
    checkNominalPairClientTypesQ3 q3NominalPairClientSwappedSigBodies = false ∧
    evalNominalPairPipelineQ3 q3NominalPairClientBodies 100 5 = .returned (.scalar 146) ∧
    evalNominalPairPipelineQ3 q3NominalPairClientRefactoredBodies 100 5 = .returned (.scalar 146) ∧
    evalNominalPairPipelineQ3 q3NominalPairClientSwappedSigBodies 100 5 = .returned (.scalar 155) ∧
    (evalNominalPairPipelineQ3 q3NominalPairClientSwappedSigBodies 100 5 !=
      evalNominalPairPipelineQ3 q3NominalPairClientBodies 100 5) = true := by
  decide

theorem q3_nominal_pair_cross_crate_challenge_and_four_adt_witness_verified :
    extractFourActualCrossCrateAdtTagsQ3 r5ClientAppBodies =
      some [.refMutEffectLog, .guard, .pairUsize, .optPairUsize] ∧
    hasDistinctFourActualCrossCrateAdtTagsQ3 r5ClientAppBodies = true ∧
    hasDistinctFourActualCrossCrateAdtTagsQ3 r5ControlCollapsedCrossCrateAdtBodies = false ∧
    isAdmittedPackageBytes q3NominalPairLibBytes = true ∧
    isAdmittedPackageBytes q3NominalPairClientBytes = true ∧
    isAdmittedPackageBytes q3NominalPairClientRefactoredBytes = true ∧
    isAdmittedPackageBytes q3NominalPairClientSwappedSigBytes = true ∧
    checkNominalPairClientTypesQ3 q3NominalPairClientBodies = true ∧
    checkNominalPairClientTypesQ3 q3NominalPairClientRefactoredBodies = true ∧
    checkNominalPairClientTypesQ3 q3NominalPairClientSwappedSigBodies = false ∧
    evalNominalPairPipelineQ3 q3NominalPairClientBodies 100 5 = .returned (.scalar 146) ∧
    evalNominalPairPipelineQ3 q3NominalPairClientRefactoredBodies 100 5 = .returned (.scalar 146) ∧
    evalNominalPairPipelineQ3 q3NominalPairClientSwappedSigBodies 100 5 = .returned (.scalar 155) :=
  ⟨q3_four_actual_adt_tags_verified.1,
   q3_four_actual_adt_tags_verified.2.1,
   q3_four_actual_adt_tags_verified.2.2.2,
   q3_nominal_pair_packages_admitted.1,
   q3_nominal_pair_packages_admitted.2.1,
   q3_nominal_pair_packages_admitted.2.2.1,
   q3_nominal_pair_packages_admitted.2.2.2,
   q3_nominal_pair_types_and_execution.1,
   q3_nominal_pair_types_and_execution.2.1,
   q3_nominal_pair_types_and_execution.2.2.1,
   q3_nominal_pair_types_and_execution.2.2.2.1,
   q3_nominal_pair_types_and_execution.2.2.2.2.1,
   q3_nominal_pair_types_and_execution.2.2.2.2.2.1⟩

/-! ## 6. `Q4` (`F4`, `#93` §9): Header-Bound Post-Run Endorsement (`verifyPostRunEndorsedArtifactBoundQ4`) -/

/-- Repaired post-run endorsement check (`Q4` / `F4`, `#93` §9):
    Requires `verifyPostRunEndorsedArtifact r` AND binds the endorsement record's
    `preserveUb` and `monoComplete` booleans directly to the decoded `.amir` v3 package
    header (`pkg.defaultPhase == .runtimePostCleanup`, `pkg.monoComplete == r.monoComplete`,
    and `pkg.preserveUb == r.preserveUb`). -/
def verifyPostRunEndorsedArtifactBoundQ4 (r : PostRunEndorsedArtifactRecord) : Bool :=
  verifyPostRunEndorsedArtifact r &&
  match parseWirePackage r.packageBytes with
  | .accepted pkg =>
      (pkg.defaultPhase == .runtimePostCleanup) &&
      (pkg.monoComplete == r.monoComplete) &&
      (pkg.preserveUb == r.preserveUb)
  | _ => false

/-- Counterexample record from `#93` Appendix B (`F4`): claims `preserveUb = true` while binding
    `r5ClientAppDefaultNoPreserveUbBytes` (whose header flags byte is `9`, so `pkg.preserveUb = false`). -/
def falselyPreservedEndorsementQ4 : PostRunEndorsedArtifactRecord :=
  { r6EndorsedClientAppRecord with
    expectedFp16 := (151, 248)
    packageBytes := r5ClientAppDefaultNoPreserveUbBytes }

theorem q4_header_bound_post_run_endorsement_verified :
    verifyPostRunEndorsedArtifactBoundQ4 r6EndorsedClientAppRecord = true ∧
    verifyPostRunEndorsedArtifact falselyPreservedEndorsementQ4 = true ∧
    verifyPostRunEndorsedArtifactBoundQ4 falselyPreservedEndorsementQ4 = false ∧
    verifyPostRunEndorsedArtifactBoundQ4 r6Control6aRuntimeInitialRecord = false ∧
    verifyPostRunEndorsedArtifactBoundQ4 r6Control6bEarlyCompileErrorRecord = false ∧
    verifyPostRunEndorsedArtifactBoundQ4 r6Control6cInterruptedBeforeEndorsementRecord = false ∧
    verifyPostRunEndorsedArtifactBoundQ4 r6Control6dPostAnalysisErrorRecord = false ∧
    verifyPostRunEndorsedArtifactBoundQ4 r6Control6eOutJsonWriteErrorRecord = false ∧
    verifyPostRunEndorsedArtifactBoundQ4 r6Control6fTamperedFp16Record = false := by
  decide

/-! ## 7. `Q5` (`F5`, `#93` §10): Universal `n : Nat` Law on Captured `r10PacketWithTailDstLayout` -/

theorem q5_r10_captured_descriptor_universal_size_law (n : Nat) :
    computeDstTotalSizeChecked r10PacketWithTailDstLayout n = some (8 + n * 4) := by
  unfold computeDstTotalSizeChecked r10PacketWithTailDstLayout
  dsimp only
  have hMod : (8 + n * 4) % 4 = 0 := by
    rw [Nat.add_mul_mod_self_right]
  rw [hMod]
  rfl

/-! ## 8. `Q8` (`#93` §13): Joined End-to-End Multi-Crate Open-Hash Evidence Path -/

theorem q8_joined_open_hash_evidence_path_verified :
    verifyPostRunEndorsedArtifactBoundQ4 r6EndorsedClientAppRecord = true ∧
    isAdmittedPackageBytes r5ClientAppOpenHashBytes = true ∧
    hasDistinctFourActualCrossCrateAdtTagsQ3 r5ClientAppBodies = true ∧
    evalOpenHashPipelineWithEntry r5ClientAppBodies 208 true true 10 true =
      (.returned (.scalar 54), [{ stepCount := 2, traceAcc := 89 }]) ∧
    evalOpenHashPipelineWithEntry r5ClientAppBodies 208 false true 10 true =
      (.ub, [{ stepCount := 1, traceAcc := 5 }]) ∧
    evalOpenHashPipelineWithEntry r5ClientAppBodies 208 true false 10 true =
      (.ub, [{ stepCount := 1, traceAcc := 5 }]) ∧
    checkNominalPairClientTypesQ3 q3NominalPairClientBodies = true ∧
    evalNominalPairPipelineQ3 q3NominalPairClientBodies 100 5 = .returned (.scalar 146) :=
  ⟨q4_header_bound_post_run_endorsement_verified.1,
   r5_open_hash_packages_admitted.2.1,
   q3_four_actual_adt_tags_verified.2.1,
   r5_exec_baseline_normal.1,
   r5_exec_baseline_ub.1,
   r5_exec_baseline_ub.2,
   q3_nominal_pair_types_and_execution.1,
   q3_nominal_pair_types_and_execution.2.2.2.1⟩

#print axioms q3_nominal_pair_cross_crate_challenge_and_four_adt_witness_verified
#print axioms q4_header_bound_post_run_endorsement_verified
#print axioms q5_r10_captured_descriptor_universal_size_law
#print axioms q8_joined_open_hash_evidence_path_verified

/-! ## 9. `C2` & `C3` (`#95` §§5–6 `D1`–`D3` & Companion §C): Per-Compilation `open_adt_table` Consumer Join, Header-Checksum-Consistent Endorsement, Captured-Layout-to-`repr(C)` Recurrence Binding, and Traced Evidence Path -/

/-- Entry in the per-compilation `open_adt_table` emitted by `direct_mir_driver_v4.rs`
    (`out_q3_nominal_pair_client.json:21` and `out_q3_nominal_pair_client_swapped_sig.json:21`). -/
structure OpenAdtTableEntryC2 where
  defPathHashHi : Nat
  defPathHashLo : Nat
  fieldsCount : Nat
  needsDrop : Bool
  ownedTyTag : MirTypeTag
  refTyTag : MirTypeTag
  agg2Tag : Nat
  deriving DecidableEq, Repr

def meterReadingDefPathHashHiC2 : Nat := 6971513911418584772
def meterReadingDefPathHashLoC2 : Nat := 12106348439045982925

def limitThresholdDefPathHashHiC2 : Nat := 6971513911418584772
def limitThresholdDefPathHashLoC2 : Nat := 3272573844775167984

/-- Exact `open_adt_table` from `artifacts/out_q3_nominal_pair_client.json:21` and
    `artifacts/out_q3_nominal_pair_client_refactored.json:21`. -/
def q3BaselineOpenAdtTableC2 : List OpenAdtTableEntryC2 :=
  [ { defPathHashHi := meterReadingDefPathHashHiC2
    , defPathHashLo := meterReadingDefPathHashLoC2
    , fieldsCount := 2
    , needsDrop := false
    , ownedTyTag := .effectLog
    , refTyTag := .refMutEffectLog
    , agg2Tag := 3 }
  , { defPathHashHi := limitThresholdDefPathHashHiC2
    , defPathHashLo := limitThresholdDefPathHashLoC2
    , fieldsCount := 2
    , needsDrop := false
    , ownedTyTag := .optUsize
    , refTyTag := .closureOrOther
    , agg2Tag := 4 } ]

/-- Exact `open_adt_table` from `artifacts/out_q3_nominal_pair_client_swapped_sig.json:21`,
    where `LimitThreshold` is encountered first (`ownedTyTag = .effectLog` `7`) and
    `MeterReading` second (`ownedTyTag = .optUsize` `12`). -/
def q3SwappedSigOpenAdtTableC2 : List OpenAdtTableEntryC2 :=
  [ { defPathHashHi := limitThresholdDefPathHashHiC2
    , defPathHashLo := limitThresholdDefPathHashLoC2
    , fieldsCount := 2
    , needsDrop := false
    , ownedTyTag := .effectLog
    , refTyTag := .refMutEffectLog
    , agg2Tag := 3 }
  , { defPathHashHi := meterReadingDefPathHashHiC2
    , defPathHashLo := meterReadingDefPathHashLoC2
    , fieldsCount := 2
    , needsDrop := false
    , ownedTyTag := .optUsize
    , refTyTag := .closureOrOther
    , agg2Tag := 4 } ]

/-- Negative control `open_adt_table` collapsing both `DefPathHash` entries to the same `ownedTyTag`. -/
def q3CollapsedOpenAdtTableC2 : List OpenAdtTableEntryC2 :=
  [ { defPathHashHi := meterReadingDefPathHashHiC2
    , defPathHashLo := meterReadingDefPathHashLoC2
    , fieldsCount := 2
    , needsDrop := false
    , ownedTyTag := .effectLog
    , refTyTag := .refMutEffectLog
    , agg2Tag := 3 }
  , { defPathHashHi := limitThresholdDefPathHashHiC2
    , defPathHashLo := limitThresholdDefPathHashLoC2
    , fieldsCount := 2
    , needsDrop := false
    , ownedTyTag := .effectLog
    , refTyTag := .refMutEffectLog
    , agg2Tag := 3 } ]

def lookupOpenAdtEntryByHashC2 : List OpenAdtTableEntryC2 → Nat → Nat → Option OpenAdtTableEntryC2
  | [], _, _ => none
  | e :: rest, hi, lo =>
      if (e.defPathHashHi == hi) && (e.defPathHashLo == lo) then some e
      else lookupOpenAdtEntryByHashC2 rest hi lo

/-- `C2` (`D1`, `#95` §5 `D1`): Resolves compilation-local `.amir` type tags for `MeterReading`
    and `LimitThreshold` from the consumed per-compilation `open_adt_table` (`tbl`) by their
    `DefPathHash` keys before checking `b104`, `b162`, `b166`, and `b176`. -/
def checkNominalPairClientBoundToOpenAdtTableC2
    (tbl : List OpenAdtTableEntryC2) (bodies : List WireBody) : Bool :=
  match lookupOpenAdtEntryByHashC2 tbl meterReadingDefPathHashHiC2 meterReadingDefPathHashLoC2,
        lookupOpenAdtEntryByHashC2 tbl limitThresholdDefPathHashHiC2 limitThresholdDefPathHashLoC2,
        findBodyBySym bodies 176, findBodyBySym bodies 104,
        findBodyBySym bodies 162, findBodyBySym bodies 166 with
  | some eMeter, some eLimit, some b176, some b104, some b162, some b166 =>
      let tMeter := eMeter.ownedTyTag
      let tLimit := eLimit.ownedTyTag
      (eMeter.fieldsCount == 2) && !eMeter.needsDrop &&
      (eLimit.fieldsCount == 2) && !eLimit.needsDrop &&
      !(tMeter == tLimit) &&
      (getLocalTypeAt b104.localTypes 0 == tMeter) &&
      (getLocalTypeAt b162.localTypes 0 == tLimit) &&
      (getLocalTypeAt b166.localTypes 1 == tMeter) &&
      (getLocalTypeAt b166.localTypes 2 == tLimit) &&
      (getLocalTypeAt b176.localTypes 9 == tMeter) &&
      (getLocalTypeAt b176.localTypes 10 == tLimit)
  | _, _, _, _, _, _ => false

theorem c2_d1_bound_open_adt_table_consumer_join_and_substitutions_verified :
    checkNominalPairClientBoundToOpenAdtTableC2 q3BaselineOpenAdtTableC2 q3NominalPairClientBodies = true ∧
    checkNominalPairClientBoundToOpenAdtTableC2 q3BaselineOpenAdtTableC2 q3NominalPairClientRefactoredBodies = true ∧
    checkNominalPairClientBoundToOpenAdtTableC2 q3SwappedSigOpenAdtTableC2 q3NominalPairClientSwappedSigBodies = true ∧
    checkNominalPairClientBoundToOpenAdtTableC2 q3SwappedSigOpenAdtTableC2 q3NominalPairClientBodies = false ∧
    checkNominalPairClientBoundToOpenAdtTableC2 q3BaselineOpenAdtTableC2 q3NominalPairClientSwappedSigBodies = false ∧
    checkNominalPairClientBoundToOpenAdtTableC2 q3CollapsedOpenAdtTableC2 q3NominalPairClientBodies = false := by
  decide

/-- Counterexample record from `#95#issuecomment-6250515087` §C (`D2`): replaces only header
    checksum bytes `7` and `8` of `r5ClientAppOpenHashBytes` with `[0, 0]` while leaving the
    payload and `expectedFp16 = (45, 98)` unchanged. -/
def mismatchedHeaderQ4 : PostRunEndorsedArtifactRecord :=
  { r6EndorsedClientAppRecord with
    packageBytes := r5ClientAppOpenHashBytes.take 7 ++ [0, 0] ++ r5ClientAppOpenHashBytes.drop 9 }

/-- `C2` (`D2`, `#95` §5 `D2`): Header-checksum-consistent post-run endorsement check.
    Verifies record/package consistency conditional on the producer/runner premise by requiring
    `verifyPostRunEndorsedArtifactBoundQ4 r` AND exact equality between the decoded `.amir` v3
    header checksum `pkg.payloadFp16`, the recorded checksum `r.expectedFp16`, and the recomputed
    payload checksum `recomputeR6PayloadFp16`. -/
def verifyPostRunEndorsedArtifactHeaderConsistentC2 (r : PostRunEndorsedArtifactRecord) : Bool :=
  verifyPostRunEndorsedArtifactBoundQ4 r &&
  match parseWirePackage r.packageBytes with
  | .accepted pkg =>
      ((pkg.fpHi, pkg.fpLo) == r.expectedFp16) &&
      (recomputeR6PayloadFp16 r5ClientAppCrateNameBytes r.packageBytes == (pkg.fpHi, pkg.fpLo))
  | _ => false

theorem c2_d2_header_consistent_endorsement_rejects_mismatched_header_q4 :
    verifyPostRunEndorsedArtifactHeaderConsistentC2 r6EndorsedClientAppRecord = true ∧
    verifyPostRunEndorsedArtifactBoundQ4 mismatchedHeaderQ4 = true ∧
    verifyPostRunEndorsedArtifactHeaderConsistentC2 mismatchedHeaderQ4 = false ∧
    verifyPostRunEndorsedArtifactHeaderConsistentC2 falselyPreservedEndorsementQ4 = false ∧
    verifyPostRunEndorsedArtifactHeaderConsistentC2 r6Control6aRuntimeInitialRecord = false ∧
    verifyPostRunEndorsedArtifactHeaderConsistentC2 r6Control6bEarlyCompileErrorRecord = false ∧
    verifyPostRunEndorsedArtifactHeaderConsistentC2 r6Control6cInterruptedBeforeEndorsementRecord = false ∧
    verifyPostRunEndorsedArtifactHeaderConsistentC2 r6Control6dPostAnalysisErrorRecord = false ∧
    verifyPostRunEndorsedArtifactHeaderConsistentC2 r6Control6eOutJsonWriteErrorRecord = false ∧
    verifyPostRunEndorsedArtifactHeaderConsistentC2 r6Control6fTamperedFp16Record = false := by
  decide

def effectiveFieldAlignC2 (rawAlign : Nat) (packCapOpt : Option Nat) : Nat :=
  match packCapOpt with
  | none => rawAlign
  | some cap => bif Nat.ble cap rawAlign then cap else rawAlign

def alignUpToC2 (offset align : Nat) : Nat :=
  let rem := offset % align
  bif Nat.beq rem 0 then offset else offset + (align - rem)

def accumReprCFieldsC2
    (packCapOpt : Option Nat) :
    List (Nat × Nat) → List Nat → Nat → Nat → Option (List Nat × Nat × Nat)
  | [], revOffsets, curOffset, maxAlign =>
      some (revOffsets.reverse, curOffset, maxAlign)
  | (fSize, fAlign) :: rest, revOffsets, curOffset, maxAlign =>
      let effAlign := effectiveFieldAlignC2 fAlign packCapOpt
      bif Nat.beq effAlign 0 then
        none
      else
        let alignedOff := alignUpToC2 curOffset effAlign
        let nextMax := bif Nat.ble maxAlign effAlign then effAlign else maxAlign
        accumReprCFieldsC2 packCapOpt rest (alignedOff :: revOffsets) (alignedOff + fSize) nextMax

def computeReprCStructAndSliceTailLayoutC2
    (headerFields : List (Nat × Nat))
    (tailElemSize tailElemAlign : Nat)
    (packCapOpt : Option Nat)
    (sliceLen : Nat) : Option (List Nat × Nat × Nat × Nat × Nat) :=
  match accumReprCFieldsC2 packCapOpt headerFields [] 0 1 with
  | none => none
  | some (fieldOffsets, afterHeaderOffset, headerMaxAlign) =>
      let effTailAlign := effectiveFieldAlignC2 tailElemAlign packCapOpt
      bif Nat.beq effTailAlign 0 then
        none
      else
        let structAlign := bif Nat.ble headerMaxAlign effTailAlign then effTailAlign else headerMaxAlign
        let tailOffset := alignUpToC2 afterHeaderOffset effTailAlign
        let rawExtent := tailOffset + sliceLen * tailElemSize
        let totalAlignedSize := alignUpToC2 rawExtent structAlign
        some (fieldOffsets, tailOffset, rawExtent, totalAlignedSize, structAlign)

def x86_64LinuxTargetTripleBytesC2 : List Nat :=
  [120, 56, 54, 95, 54, 52, 45, 117, 110, 107, 110, 111, 119, 110, 45, 108, 105, 110, 117, 120, 45, 103, 110, 117]

def r10PacketWithTailHeaderFieldsC2 : List (Nat × Nat) :=
  [(4, 4), (2, 2)]

/-- `C2` (`D3`, `#95` §5 `D3`): Binds the captured `PacketWithTail` layout description `d` and
    compilation target-triple context directly to the independent `#[repr(C)]` recurrence
    `computeReprCStructAndSliceTailLayoutC2`, ensuring that any captured tail-offset, tail-element
    layout, or target-context mutation is rejected before consuming `computeDstTotalSizeChecked d`. -/
def checkCapturedSliceTailDstLayoutAgainstReprCC2
    (expectedTargetTripleBytes actualTargetTripleBytes : List Nat)
    (headerFields : List (Nat × Nat))
    (expectedTailElemSize expectedTailElemAlign : Nat)
    (d : QueriedLayoutRecord) : Bool :=
  (expectedTargetTripleBytes == actualTargetTripleBytes) &&
  physicalBytesValid actualTargetTripleBytes &&
  (d.typeNameId == 104) &&
  d.isUnsizedSliceTail &&
  !d.hasNiche &&
  (d.tailElemSizeBytes == expectedTailElemSize) &&
  (d.tailElemAlignBytes == expectedTailElemAlign) &&
  match computeReprCStructAndSliceTailLayoutC2 headerFields expectedTailElemSize expectedTailElemAlign none 0 with
  | some (hdrOffsets, tailOffset, _, alignedBaseSize, overallAlign) =>
      (d.fieldOffsetsBytes == hdrOffsets ++ [tailOffset]) &&
      (d.sizeBytes == alignedBaseSize) &&
      (d.alignBytes == overallAlign)
  | none => false

def mutatedTailOffsetDstLayoutC2 : QueriedLayoutRecord :=
  { r10PacketWithTailDstLayout with fieldOffsetsBytes := [0, 4, 12], sizeBytes := 12 }

def mutatedTailElemLayoutC2 : QueriedLayoutRecord :=
  { r10PacketWithTailDstLayout with tailElemSizeBytes := 8 }

def mutatedTargetTripleBytesC2 : List Nat :=
  x86_64LinuxTargetTripleBytesC2.drop 1

theorem c2_d3_captured_layout_to_repr_c_recurrence_and_mutations_verified :
    checkCapturedSliceTailDstLayoutAgainstReprCC2
      x86_64LinuxTargetTripleBytesC2 x86_64LinuxTargetTripleBytesC2
      r10PacketWithTailHeaderFieldsC2 4 4 r10PacketWithTailDstLayout = true ∧
    checkCapturedSliceTailDstLayoutAgainstReprCC2
      x86_64LinuxTargetTripleBytesC2 x86_64LinuxTargetTripleBytesC2
      r10PacketWithTailHeaderFieldsC2 4 4 mutatedTailOffsetDstLayoutC2 = false ∧
    checkCapturedSliceTailDstLayoutAgainstReprCC2
      x86_64LinuxTargetTripleBytesC2 x86_64LinuxTargetTripleBytesC2
      r10PacketWithTailHeaderFieldsC2 4 4 mutatedTailElemLayoutC2 = false ∧
    checkCapturedSliceTailDstLayoutAgainstReprCC2
      x86_64LinuxTargetTripleBytesC2 mutatedTargetTripleBytesC2
      r10PacketWithTailHeaderFieldsC2 4 4 r10PacketWithTailDstLayout = false := by
  decide

theorem c2_d3_repr_c_universal_law (n : Nat) :
    computeReprCStructAndSliceTailLayoutC2 r10PacketWithTailHeaderFieldsC2 4 4 none n =
      some ([0, 4], 8, 8 + n * 4, 8 + n * 4, 4) := by
  have hAcc : accumReprCFieldsC2 none r10PacketWithTailHeaderFieldsC2 [] 0 1 = some ([0, 4], 6, 4) := rfl
  unfold computeReprCStructAndSliceTailLayoutC2
  rw [hAcc]
  change some ([0, 4], 8, 8 + n * 4, alignUpToC2 (8 + n * 4) 4, 4) =
    some ([0, 4], 8, 8 + n * 4, 8 + n * 4, 4)
  unfold alignUpToC2
  have hMod : (8 + n * 4) % 4 = 0 := by
    rw [Nat.add_mul_mod_self_right]
  rw [hMod]
  rfl

theorem c2_d3_captured_layout_bound_universal_size_law (n : Nat) :
    checkCapturedSliceTailDstLayoutAgainstReprCC2
      x86_64LinuxTargetTripleBytesC2 x86_64LinuxTargetTripleBytesC2
      r10PacketWithTailHeaderFieldsC2 4 4 r10PacketWithTailDstLayout = true ∧
    computeDstTotalSizeChecked r10PacketWithTailDstLayout n = some (8 + n * 4) ∧
    computeReprCStructAndSliceTailLayoutC2 r10PacketWithTailHeaderFieldsC2 4 4 none n =
      some ([0, 4], 8, 8 + n * 4, 8 + n * 4, 4) :=
  ⟨c2_d3_captured_layout_to_repr_c_recurrence_and_mutations_verified.1,
   q5_r10_captured_descriptor_universal_size_law n,
   c2_d3_repr_c_universal_law n⟩

/-- `C3` (`#95` §6 `C3`): Repaired end-to-end evidence conjunction over the existing captured
    3-crate `r5_client_app` and 2-crate `q3_nominal_pair_client` subjects, using the repaired
    `C2` gates (`verifyPostRunEndorsedArtifactHeaderConsistentC2`,
    `checkNominalPairClientBoundToOpenAdtTableC2`, and `checkCapturedSliceTailDstLayoutAgainstReprCC2`). -/
theorem c3_traced_open_hash_and_nominal_evidence_path_verified :
    verifyPostRunEndorsedArtifactHeaderConsistentC2 r6EndorsedClientAppRecord = true ∧
    isAdmittedPackageBytes r5ClientAppOpenHashBytes = true ∧
    hasDistinctFourActualCrossCrateAdtTagsQ3 r5ClientAppBodies = true ∧
    evalOpenHashPipelineWithEntry r5ClientAppBodies 208 true true 10 true =
      (.returned (.scalar 54), [{ stepCount := 2, traceAcc := 89 }]) ∧
    evalOpenHashPipelineWithEntry r5ClientAppBodies 208 false true 10 true =
      (.ub, [{ stepCount := 1, traceAcc := 5 }]) ∧
    evalOpenHashPipelineWithEntry r5ClientAppBodies 208 true false 10 true =
      (.ub, [{ stepCount := 1, traceAcc := 5 }]) ∧
    checkNominalPairClientBoundToOpenAdtTableC2 q3BaselineOpenAdtTableC2 q3NominalPairClientBodies = true ∧
    checkNominalPairClientBoundToOpenAdtTableC2 q3SwappedSigOpenAdtTableC2 q3NominalPairClientBodies = false ∧
    evalNominalPairPipelineQ3 q3NominalPairClientBodies 100 5 = .returned (.scalar 146) ∧
    checkCapturedSliceTailDstLayoutAgainstReprCC2
      x86_64LinuxTargetTripleBytesC2 x86_64LinuxTargetTripleBytesC2
      r10PacketWithTailHeaderFieldsC2 4 4 r10PacketWithTailDstLayout = true :=
  ⟨c2_d2_header_consistent_endorsement_rejects_mismatched_header_q4.1,
   r5_open_hash_packages_admitted.2.1,
   q3_four_actual_adt_tags_verified.2.1,
   r5_exec_baseline_normal.1,
   r5_exec_baseline_ub.1,
   r5_exec_baseline_ub.2,
   c2_d1_bound_open_adt_table_consumer_join_and_substitutions_verified.1,
   c2_d1_bound_open_adt_table_consumer_join_and_substitutions_verified.2.2.2.1,
   q3_nominal_pair_types_and_execution.2.2.2.1,
   c2_d3_captured_layout_to_repr_c_recurrence_and_mutations_verified.1⟩

#print axioms c2_d1_bound_open_adt_table_consumer_join_and_substitutions_verified
#print axioms c2_d2_header_consistent_endorsement_rejects_mismatched_header_q4
#print axioms c2_d3_captured_layout_to_repr_c_recurrence_and_mutations_verified
#print axioms c2_d3_captured_layout_bound_universal_size_law
#print axioms c3_traced_open_hash_and_nominal_evidence_path_verified

end AnnealResearch.OpenHashMultiCrateR5R6R9R10
