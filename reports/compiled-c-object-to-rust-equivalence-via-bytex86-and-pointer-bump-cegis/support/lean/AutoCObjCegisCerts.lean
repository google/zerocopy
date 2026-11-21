-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import ByteX86Gcc
import RustFfiSpecs
import CompiledCObjImages
import UntrustedCObjHints
import UntrustedCObjBlockDecodes
import UntrustedCObjScalarLoops
import UntrustedCObjMutLoops
import UntrustedCObjBugRefutations
import UntrustedCObjXorAvx2
import UntrustedCObjDotSimd
import UntrustedCObjDotAvx2
import AutoCertFnv1a
import AutoCertAdler32
import AutoCertChecksumRol
import AutoCertAsciiTolower
import AutoCertDotO2
import AutoCertXorO2
import AutoCertDotAvx2
import AutoCertXorAvx2

/-!
# `AutoCObjCegisCerts`

Top-level umbrella module uniting all 12 kernel-checked `gcc 15.2.0`
(`-O2` and `-O3 -mavx2`) `CObjectMatchesRustContract` equivalence theorems,
the `Tree Borrows` overlap-guard discharge theorem, all 4 C-FFI bug
refutation theorems, and all 12 `CaDiCaL 2.1.2` `Pass1GmpLrat` certificates.
-/

namespace AutoCObjCegisCerts

open ByteX86Gcc
open RustFfiSpecs
open CompiledCObjImages
open UntrustedCObjHints

def cert_c_fnv1a64_o3 : CObjEquivCert := AutoCertFnv1a.cert_c_fnv1a64_o2
theorem cert_c_fnv1a64_o3_ok : checkCObjEquivCert cert_c_fnv1a64_o3 1 0 = true :=
  AutoCertFnv1a.cert_c_fnv1a64_o2_ok

def cert_c_adler32_chunk_o3 : CObjEquivCert := AutoCertAdler32.cert_c_adler32_chunk_o2
theorem cert_c_adler32_chunk_o3_ok : checkCObjEquivCert cert_c_adler32_chunk_o3 1 0 = true :=
  AutoCertAdler32.cert_c_adler32_chunk_o2_ok

def cert_c_checksum_rol_u8_o3 : CObjEquivCert := AutoCertChecksumRol.cert_c_checksum_rol_u8_o2
theorem cert_c_checksum_rol_u8_o3_ok : checkCObjEquivCert cert_c_checksum_rol_u8_o3 1 0 = true :=
  AutoCertChecksumRol.cert_c_checksum_rol_u8_o2_ok

def cert_c_ascii_tolower_o3 : CObjEquivCert := AutoCertAsciiTolower.cert_c_ascii_tolower_o2
theorem cert_c_ascii_tolower_o3_ok : checkCObjEquivCert cert_c_ascii_tolower_o3 1 0 = true :=
  AutoCertAsciiTolower.cert_c_ascii_tolower_o2_ok

/-- Top-level kernel-checked umbrella theorem uniting all 12 compiled `gcc 15.2.0`
    C object equivalence proofs (`-O2` & `-O3 -mavx2`), the `Tree Borrows` alias-guard
    discharge theorem, all 4 C-FFI bug refutations, and all 12 `CaDiCaL 2.1.2`
    `Pass1GmpLrat` certificates (`by rfl`). -/
theorem all_12_c_objs_equiv_and_4_bugs_refuted :
    CObjectMatchesRustContract cFfiKernelsO2Obj 0x0#64 (Fnv1a64Pre 0) (Fnv1a64Post 0) ∧
    CObjectMatchesRustContract cFfiKernelsO2Obj 0x50#64 (Adler32Pre 0) (Adler32Post 0) ∧
    CObjectMatchesRustContract cFfiKernelsO2Obj 0xd0#64 (ChecksumRolPre 0) (ChecksumRolPost 0) ∧
    CObjectMatchesRustContract cFfiKernelsO2Obj 0x100#64 (AsciiTolowerPre 0) (AsciiTolowerContractPost 0) ∧
    CObjectMatchesRustContract cFfiKernelsO2Obj 0x140#64 (DotU8U16Pre 0) (DotU8U16Post 0) ∧
    CObjectMatchesRustContract cFfiKernelsO2Obj 0x230#64 (XorStreamPre 0) (XorStreamContractPost 0) ∧
    CObjectMatchesRustContract cFfiKernelsO3Avx2Obj 0x0#64 (Fnv1a64Pre 0) (Fnv1a64Post 0) ∧
    CObjectMatchesRustContract cFfiKernelsO3Avx2Obj 0x50#64 (Adler32Pre 0) (Adler32Post 0) ∧
    CObjectMatchesRustContract cFfiKernelsO3Avx2Obj 0xd0#64 (ChecksumRolPre 0) (ChecksumRolPost 0) ∧
    CObjectMatchesRustContract cFfiKernelsO3Avx2Obj 0x100#64 (AsciiTolowerPre 0) (AsciiTolowerContractPost 0) ∧
    CObjectMatchesRustContract cFfiKernelsO3Avx2Obj 0x140#64 (DotU8U16Pre 0) (DotU8U16Post 0) ∧
    CObjectMatchesRustContract cFfiKernelsO3Avx2Obj 0x450#64 (XorStreamPre 16) (XorStreamContractPost 16) ∧
    (∀ (s0 : X64State) (nd : Nat → UndefChoice), s0.halted = false → s0.fault = false → s0.rip = 0x400450#64 → XorStreamPre 16 s0 → 32 ≤ (s0.regs .rdx).toNat → 0 < (s0.regs .rdi).toNat → (s0.regs .rsi).toNat + 31 < 2 ^ 64 → (runX64 cFfiKernelsO3Avx2Obj 7 nd s0).rip = 0x40046d#64) ∧
    ¬ CObjectMatchesRustContract cFfiBugsO2Obj 0x0#64 (Bug1EndpointsPre 0) (Bug1EndpointsPost 0) ∧
    ¬ CObjectMatchesRustContract cFfiBugsO2Obj 0x20#64 (Fnv1a64Pre 0) (Fnv1a64Post 0) ∧
    ¬ CObjectMatchesRustContract cFfiBugsO2Obj 0x70#64 (XorStreamPre 0) (XorStreamContractPost 0) ∧
    ¬ CObjectMatchesRustContract cFfiBugsO2Obj 0xa0#64 (Bug4SumPre 0) (Bug4SumPost 0) ∧
    checkCObjEquivCert AutoCertFnv1a.cert_c_fnv1a64_o2 1 0 = true ∧
    checkCObjEquivCert AutoCertAdler32.cert_c_adler32_chunk_o2 1 0 = true ∧
    checkCObjEquivCert AutoCertChecksumRol.cert_c_checksum_rol_u8_o2 1 0 = true ∧
    checkCObjEquivCert AutoCertAsciiTolower.cert_c_ascii_tolower_o2 1 0 = true ∧
    checkCObjEquivCert AutoCertDotO2.cert_c_dot_u8_u16_o2 16 0 = true ∧
    checkCObjEquivCert AutoCertXorO2.cert_c_xor_stream_o2 1 0 = true ∧
    checkCObjEquivCert cert_c_fnv1a64_o3 1 0 = true ∧
    checkCObjEquivCert cert_c_adler32_chunk_o3 1 0 = true ∧
    checkCObjEquivCert cert_c_checksum_rol_u8_o3 1 0 = true ∧
    checkCObjEquivCert cert_c_ascii_tolower_o3 1 0 = true ∧
    checkCObjEquivCert AutoCertDotAvx2.cert_c_dot_u8_u16_o3_avx2 32 0 = true ∧
    checkCObjEquivCert AutoCertXorAvx2.cert_c_xor_stream_o3_avx2 32 16 = true :=
  let _ := And.intro
    UntrustedCObjBugRefutations.bug4_functional_rax_matches_yet_abi_violated
    UntrustedCObjBugRefutations.refute_bug4_dirty_upper_ymm
  ⟨UntrustedCObjScalarLoops.prove_c_fnv1a64_o2,
   UntrustedCObjScalarLoops.prove_c_adler32_chunk_o2,
   UntrustedCObjScalarLoops.prove_c_checksum_rol_o2,
   UntrustedCObjMutLoops.prove_c_ascii_tolower_o2,
   UntrustedCObjDotSimd.prove_c_dot_u8_u16_o2,
   UntrustedCObjMutLoops.prove_c_xor_stream_o2,
   UntrustedCObjScalarLoops.prove_c_fnv1a64_o3,
   UntrustedCObjScalarLoops.prove_c_adler32_chunk_o3,
   UntrustedCObjScalarLoops.prove_c_checksum_rol_o3,
   UntrustedCObjMutLoops.prove_c_ascii_tolower_o3,
   UntrustedCObjDotAvx2.prove_c_dot_u8_u16_o3_avx2,
   UntrustedCObjXorAvx2.prove_c_xor_stream_o3_avx2,
   UntrustedCObjXorAvx2.c_xor_stream_o3_avx2_overlap_guard_discharged,
   UntrustedCObjBugRefutations.refute_bug1_int_len_endpoints,
   UntrustedCObjBugRefutations.refute_bug2_signed_char_fnv1a,
   UntrustedCObjBugRefutations.refute_bug3_off_by_one_xor,
   UntrustedCObjBugRefutations.refute_bug4_asm_clobber_abi,
   AutoCertFnv1a.cert_c_fnv1a64_o2_ok,
   AutoCertAdler32.cert_c_adler32_chunk_o2_ok,
   AutoCertChecksumRol.cert_c_checksum_rol_u8_o2_ok,
   AutoCertAsciiTolower.cert_c_ascii_tolower_o2_ok,
   AutoCertDotO2.cert_c_dot_u8_u16_o2_ok,
   AutoCertXorO2.cert_c_xor_stream_o2_ok,
   cert_c_fnv1a64_o3_ok,
   cert_c_adler32_chunk_o3_ok,
   cert_c_checksum_rol_u8_o3_ok,
   cert_c_ascii_tolower_o3_ok,
   AutoCertDotAvx2.cert_c_dot_u8_u16_o3_avx2_ok,
   AutoCertXorAvx2.cert_c_xor_stream_o3_avx2_ok⟩

end AutoCObjCegisCerts
