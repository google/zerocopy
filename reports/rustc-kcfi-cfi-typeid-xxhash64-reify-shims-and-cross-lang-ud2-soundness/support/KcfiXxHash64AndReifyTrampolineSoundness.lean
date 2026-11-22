/-!
# KCFI type identifiers, the x86-64 call-site guard, and the reify trampoline

A self-contained model (Lean core only, no imports) of four things:

1. `xxHash64Seed0` — XXH64 with seed 0 as an executable total function on
   byte lists.  A KCFI type identifier is the low 32 bits of this hash of an
   Itanium type-id string.
2. The x86-64 call-site guard `movl $-id, %r10d ; addl -4(%target), %r10d ;
   je ; ud2` as arithmetic on `UInt32`, including LLVM's `MaskKCFIType`.
3. The type-id string encoders of rustc and of Clang for a first-order
   fragment (integers, `bool`, `char`, floats, unit/void, raw pointers,
   `#[repr(transparent)]` wrappers, zero-sized arguments), with Itanium
   substitution (`S_`, `S0_`, ...).
4. A code image in which every address carries exactly one 32-bit tag, the
   indirect-call semantics on it, and the layouts with and without the
   `reify_fnptr` trampoline.

Concrete strings and identifiers that appear in theorems are evaluated by the
kernel from these definitions; none is assumed.  Which of them were also
observed in compiler output is recorded in the accompanying report, not here.
-/

namespace KcfiReify

/-! ## 1. XXH64 with seed 0 -/

def prime1 : UInt64 := 0x9E3779B185EBCA87
def prime2 : UInt64 := 0xC2B2AE3D27D4EB4F
def prime3 : UInt64 := 0x165667B19E3779F9
def prime4 : UInt64 := 0x85EBCA77C2B2AE63
def prime5 : UInt64 := 0x27D4EB2F165667C5

def rotl (x r : UInt64) : UInt64 := (x <<< r) ||| (x >>> (64 - r))

def round (acc inp : UInt64) : UInt64 := rotl (acc + inp * prime2) 31 * prime1

def mergeRound (h v : UInt64) : UInt64 := (h ^^^ round 0 v) * prime1 + prime4

/-- Little-endian value of the first `n` bytes (missing bytes read as 0). -/
noncomputable def readLE : Nat → List UInt8 → UInt64
  | 0, _ => 0
  | _ + 1, [] => 0
  | n + 1, b :: bs => b.toUInt64 ||| (readLE n bs <<< 8)

structure Lanes where
  v1 : UInt64
  v2 : UInt64
  v3 : UInt64
  v4 : UInt64

/-- Consume 32-byte stripes while at least 32 bytes remain (`fuel` bounds the
number of stripes; the caller passes the input length). -/
noncomputable def stripes : Nat → List UInt8 → Lanes → Lanes × List UInt8
  | 0, bs, a => (a, bs)
  | fuel + 1, bs, a =>
    if 32 ≤ bs.length then
      stripes fuel (bs.drop 32)
        ⟨round a.v1 (readLE 8 bs), round a.v2 (readLE 8 (bs.drop 8)),
         round a.v3 (readLE 8 (bs.drop 16)), round a.v4 (readLE 8 (bs.drop 24))⟩
    else (a, bs)

noncomputable def tail8 : Nat → List UInt8 → UInt64 → UInt64 × List UInt8
  | 0, bs, h => (h, bs)
  | fuel + 1, bs, h =>
    if 8 ≤ bs.length then
      tail8 fuel (bs.drop 8) (rotl (h ^^^ round 0 (readLE 8 bs)) 27 * prime1 + prime4)
    else (h, bs)

noncomputable def tail4 (bs : List UInt8) (h : UInt64) : UInt64 × List UInt8 :=
  if 4 ≤ bs.length then (rotl (h ^^^ (readLE 4 bs * prime1)) 23 * prime2 + prime3, bs.drop 4)
  else (h, bs)

noncomputable def tail1 : List UInt8 → UInt64 → UInt64
  | [], h => h
  | b :: bs, h => tail1 bs (rotl (h ^^^ (b.toUInt64 * prime5)) 11 * prime1)

def avalanche (h : UInt64) : UInt64 :=
  let h := h ^^^ (h >>> 33)
  let h := h * prime2
  let h := h ^^^ (h >>> 29)
  let h := h * prime3
  h ^^^ (h >>> 32)

/-- XXH64 of a byte list with seed 0. -/
noncomputable def xxHash64Seed0 (bs : List UInt8) : UInt64 :=
  let n := bs.length
  let start : UInt64 × List UInt8 :=
    if 32 ≤ n then
      let r := stripes n bs ⟨prime1 + prime2, prime2, 0, 0 - prime1⟩
      let a := r.1
      (mergeRound (mergeRound (mergeRound (mergeRound
          (rotl a.v1 1 + rotl a.v2 7 + rotl a.v3 12 + rotl a.v4 18) a.v1) a.v2) a.v3) a.v4, r.2)
    else (prime5, bs)
  let t8 := tail8 n start.2 (start.1 + n.toUInt64)
  let t4 := tail4 t8.2 t8.1
  avalanche (tail1 t4.2 t4.1)

/-- The UTF-8 bytes of a string. -/
def utf8Bytes (s : String) : List UInt8 := s.toUTF8.data.toList

/-- KCFI type identifier of a type-id string: low 32 bits of XXH64(seed 0). -/
noncomputable def kcfiTypeId (s : String) : UInt32 := (xxHash64Seed0 (utf8Bytes s)).toUInt32

/-! Reference vectors of XXH64 (seed 0); the last one is 39 bytes long and so
runs the 32-byte stripe loop. -/

theorem xxh64_empty : xxHash64Seed0 [] = 0xEF46DB3751D8E999 := rfl
theorem xxh64_a : xxHash64Seed0 (utf8Bytes "a") = 0xD24EC4F1A98C6E5B := rfl
theorem xxh64_abc : xxHash64Seed0 (utf8Bytes "abc") = 0x44BC2CF5AD770999 := rfl
theorem xxh64_39_bytes :
    xxHash64Seed0 (utf8Bytes "Nobody inspects the spammish repetition") = 0xFBCEA83C8A378BF1 := by
  repeat constructor

/-! Type-id strings and their identifiers. -/

theorem kcfi_u64_i32_normalized : kcfiTypeId "_ZTSFu3u64u3i32E.normalized" = 2701021033 := rfl
theorem kcfi_u32_u32_normalized : kcfiTypeId "_ZTSFu3u32S_E.normalized" = 2010610996 := rfl
theorem kcfi_u64_i32_rust_default : kcfiTypeId "_ZTSFu3u64u3i32E" = 3837184471 := rfl
theorem kcfi_u32_u32_rust_default : kcfiTypeId "_ZTSFu3u32S_E" = 2751902716 := rfl
theorem kcfi_ulong_int_c_default : kcfiTypeId "_ZTSFmiE" = 3945929266 := rfl
theorem kcfi_ullong_int_c_default : kcfiTypeId "_ZTSFyiE" = 2900422046 := rfl
theorem kcfi_uint_uint_c_default : kcfiTypeId "_ZTSFjjE" = 1731883814 := rfl

/-! ## 2. The x86-64 call-site guard -/

/-- LLVM `X86AsmPrinter::MaskKCFIType`: a type id equal to the ENDBR64 or
ENDBR32 byte pattern, or to the two's-complement negation of either, is
replaced by its successor, both in the prefix word and at call sites. -/
def maskKCFIType (v : UInt32) : UInt32 :=
  if v = 0xFA1E0FF3 ∨ v = 0 - 0xFA1E0FF3 ∨ v = 0xFB1E0FF3 ∨ v = 0 - 0xFB1E0FF3 then v + 1 else v

/-- Value left in `%r10d` by `movl $(-expected), %r10d ; addl -4(%target), %r10d`
when the word at `target - 4` is `found`. -/
def guardSum (expected found : UInt32) : UInt32 := (0 - expected) + found

/-- The zero flag after the `addl`: `je` skips the `ud2` exactly when it is set. -/
def guardPasses (expected found : UInt32) : Bool := guardSum expected found == 0

/-- Exactness of the negate-and-add comparison in 32-bit two's complement. -/
theorem kcfi_negated_add_zero_iff_hash_eq (h m : UInt32) : (0 - h) + m = 0 ↔ m = h := by
  constructor
  · intro hz
    have h1 : (0 - h) + h = 0 := UInt32.sub_add_cancel 0 h
    calc m = m + 0 := (UInt32.add_zero m).symm
      _ = m + ((0 - h) + h) := by rw [h1]
      _ = (m + (0 - h)) + h := (UInt32.add_assoc m (0 - h) h).symm
      _ = ((0 - h) + m) + h := by rw [UInt32.add_comm m (0 - h)]
      _ = 0 + h := by rw [hz]
      _ = h := UInt32.zero_add h
  · intro hm
    subst hm
    exact UInt32.sub_add_cancel 0 m

theorem guardPasses_iff (expected found : UInt32) :
    guardPasses expected found = true ↔ found = expected := by
  unfold guardPasses guardSum
  rw [beq_iff_eq]
  exact kcfi_negated_add_zero_iff_hash_eq expected found

/-- The same statement on natural numbers below `2^32`. -/
theorem kcfi_negated_add_zero_iff_hash_eq_nat (h m : UInt32) :
    ((4294967296 - h.toNat) % 4294967296 + m.toNat) % 4294967296 = 0 ↔ m.toNat = h.toNat := by
  rw [UInt32.toNat_inj, ← kcfi_negated_add_zero_iff_hash_eq h m, ← UInt32.toNat_inj,
    UInt32.toNat_add, UInt32.toNat_sub, UInt32.toNat_zero, Nat.add_zero]

/-- The immediates `0x5f01b097` (call site) and `0xa0fe4f69` (prefix) are
negations of each other, and `0xa0fe4f69` is the identifier of
`_ZTSFu3u64u3i32E.normalized`. -/
theorem guard_constants_u64_i32_normalized :
    (0 : UInt32) - kcfiTypeId "_ZTSFu3u64u3i32E.normalized" = 0x5f01b097
      ∧ (0x5f01b097 : UInt32) + 0xa0fe4f69 = 0
      ∧ maskKCFIType (kcfiTypeId "_ZTSFu3u64u3i32E.normalized") = 0xa0fe4f69 := by
  repeat constructor

/-- With masking on both sides the guard compares masked identifiers. -/
theorem masked_guard_iff (expected found : UInt32) :
    guardPasses (maskKCFIType expected) (maskKCFIType found) = true
      ↔ maskKCFIType found = maskKCFIType expected :=
  guardPasses_iff _ _

/-- Masking is not injective: the ENDBR64 pattern and its successor are
distinct identifiers that the guard cannot tell apart. -/
theorem maskKCFIType_not_injective :
    (0xFA1E0FF3 : UInt32) ≠ 0xFA1E0FF4
      ∧ guardPasses (maskKCFIType 0xFA1E0FF3) (maskKCFIType 0xFA1E0FF4) = true := by
  decide

/-! ## 3. Itanium type-id strings with substitution

Both compilers emit `_ZTSF<return><parameters>E` followed by `.normalized`
when integer normalisation is on.  Components that are substitution
candidates are entered into a dictionary in order of first completion; a
later occurrence of the same candidate is written `S_` (index 0), `S0_`
(index 1), `S1_`, ... -/

noncomputable def findIdx {α : Type} [DecidableEq α] (k : α) : List α → Option Nat
  | [] => none
  | x :: xs => if x = k then some 0 else (findIdx k xs).map (· + 1)

def base36Digit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (55 + n)

/-- Upper-case base-36 digits, most significant first (`fuel` bounds the length). -/
noncomputable def base36 : Nat → Nat → List Char
  | 0, _ => []
  | fuel + 1, n => if n < 36 then [base36Digit n] else base36 fuel (n / 36) ++ [base36Digit (n % 36)]

/-- Itanium `<seq-id>`: empty for index 0, otherwise `index - 1` in base 36. -/
noncomputable def seqId (i : Nat) : String := if i = 0 then "" else String.ofList (base36 i (i - 1))

noncomputable def substitution (i : Nat) : String := "S" ++ seqId i ++ "_"

/-- Replace a component by a back-reference if its key is already in the
dictionary; otherwise keep it and append the key. -/
noncomputable def compress {κ : Type} [DecidableEq κ] (d : List κ) (k : κ) (comp : String) : String × List κ :=
  match findIdx k d with
  | some i => (substitution i, d)
  | none => (comp, d ++ [k])

theorem substitution_examples :
    substitution 0 = "S_" ∧ substitution 1 = "S0_" ∧ substitution 2 = "S1_"
      ∧ substitution 11 = "SA_" ∧ substitution 36 = "SZ_" ∧ substitution 37 = "S10_" := by repeat constructor

/-! ### 3a. rustc -/

inductive IntTy where
  | i8 | i16 | i32 | i64 | i128 | isize | u8 | u16 | u32 | u64 | u128 | usize
  deriving DecidableEq

/-- The modelled fragment of Rust types. `transparent t` is a
`#[repr(transparent)]` struct whose only non-zero-sized field has type `t`;
`zst` is any zero-sized type passed as an argument. -/
inductive RTy where
  | bool | char | int (t : IntTy) | f32 | f64 | unit | cVoid
  | rawPtr (isMut : Bool) (pointee : RTy)
  | transparent (inner : RTy)
  | zst

noncomputable def decEqRTy : (a b : RTy) → Decidable (a = b)
  | .bool, .bool => isTrue rfl
  | .char, .char => isTrue rfl
  | .int a, .int b => match decEq a b with
    | isTrue h => isTrue (congrArg RTy.int h)
    | isFalse h => isFalse (fun e => by injection e with e'; exact h e')
  | .f32, .f32 => isTrue rfl
  | .f64, .f64 => isTrue rfl
  | .unit, .unit => isTrue rfl
  | .cVoid, .cVoid => isTrue rfl
  | .rawPtr m1 p1, .rawPtr m2 p2 =>
    match decEq m1 m2, decEqRTy p1 p2 with
    | isTrue hm, isTrue hp => isTrue (by subst hm; subst hp; rfl)
    | isFalse hm, _ => isFalse (fun e => by injection e with e1 _; exact hm e1)
    | _, isFalse hp => isFalse (fun e => by injection e with _ e2; exact hp e2)
  | .transparent p1, .transparent p2 =>
    match decEqRTy p1 p2 with
    | isTrue hp => isTrue (congrArg RTy.transparent hp)
    | isFalse hp => isFalse (fun e => by injection e with e1; exact hp e1)
  | .zst, .zst => isTrue rfl
  | .bool, .char | .bool, .int _ | .bool, .f32 | .bool, .f64 | .bool, .unit | .bool, .cVoid | .bool, .rawPtr _ _ | .bool, .transparent _ | .bool, .zst
  | .char, .bool | .char, .int _ | .char, .f32 | .char, .f64 | .char, .unit | .char, .cVoid | .char, .rawPtr _ _ | .char, .transparent _ | .char, .zst
  | .int _, .bool | .int _, .char | .int _, .f32 | .int _, .f64 | .int _, .unit | .int _, .cVoid | .int _, .rawPtr _ _ | .int _, .transparent _ | .int _, .zst
  | .f32, .bool | .f32, .char | .f32, .int _ | .f32, .f64 | .f32, .unit | .f32, .cVoid | .f32, .rawPtr _ _ | .f32, .transparent _ | .f32, .zst
  | .f64, .bool | .f64, .char | .f64, .int _ | .f64, .f32 | .f64, .unit | .f64, .cVoid | .f64, .rawPtr _ _ | .f64, .transparent _ | .f64, .zst
  | .unit, .bool | .unit, .char | .unit, .int _ | .unit, .f32 | .unit, .f64 | .unit, .cVoid | .unit, .rawPtr _ _ | .unit, .transparent _ | .unit, .zst
  | .cVoid, .bool | .cVoid, .char | .cVoid, .int _ | .cVoid, .f32 | .cVoid, .f64 | .cVoid, .unit | .cVoid, .rawPtr _ _ | .cVoid, .transparent _ | .cVoid, .zst
  | .rawPtr _ _, .bool | .rawPtr _ _, .char | .rawPtr _ _, .int _ | .rawPtr _ _, .f32 | .rawPtr _ _, .f64 | .rawPtr _ _, .unit | .rawPtr _ _, .cVoid | .rawPtr _ _, .transparent _ | .rawPtr _ _, .zst
  | .transparent _, .bool | .transparent _, .char | .transparent _, .int _ | .transparent _, .f32 | .transparent _, .f64 | .transparent _, .unit | .transparent _, .cVoid | .transparent _, .rawPtr _ _ | .transparent _, .zst
  | .zst, .bool | .zst, .char | .zst, .int _ | .zst, .f32 | .zst, .f64 | .zst, .unit | .zst, .cVoid | .zst, .rawPtr _ _ | .zst, .transparent _ =>
    isFalse (fun h => nomatch h)

noncomputable instance : DecidableEq RTy := decEqRTy

/-- Substitution-dictionary keys: a type, or a `const`-qualified pointee. -/
inductive RKey where
  | ty (t : RTy)
  | constOf (t : RTy)

noncomputable instance : DecidableEq RKey := fun a b =>
  match a, b with
  | .ty x, .ty y => match decEq x y with
    | isTrue h => isTrue (congrArg RKey.ty h)
    | isFalse h => isFalse (fun e => by injection e with e'; exact h e')
  | .constOf x, .constOf y => match decEq x y with
    | isTrue h => isTrue (congrArg RKey.constOf h)
    | isFalse h => isFalse (fun e => by injection e with e'; exact h e')
  | .ty _, .constOf _ | .constOf _, .ty _ => isFalse (fun h => nomatch h)

/-- Vendor-extended names of the integer types (`u<length><name>`). -/
def intVendor : IntTy → String
  | .i8 => "u2i8" | .i16 => "u3i16" | .i32 => "u3i32" | .i64 => "u3i64"
  | .i128 => "u4i128" | .isize => "u5isize"
  | .u8 => "u2u8" | .u16 => "u3u16" | .u32 => "u3u32" | .u64 => "u3u64"
  | .u128 => "u4u128" | .usize => "u5usize"

/-- Integer normalisation of one integer type on a 64-bit target. -/
def fixWidth : IntTy → IntTy
  | .isize => .i64
  | .usize => .u64
  | t => t

/-- The type transformation applied before encoding: `c_void` becomes unit,
transparent wrappers are replaced by their field, and with `norm` set `bool`
becomes `u8`, `char` becomes `u32`, `isize`/`usize` become `i64`/`u64`. -/
noncomputable def transform (norm : Bool) : RTy → RTy
  | .bool => if norm then .int .u8 else .bool
  | .char => if norm then .int .u32 else .char
  | .int t => if norm then .int (fixWidth t) else .int t
  | .cVoid => .unit
  | .transparent t => transform norm t
  | .rawPtr m p => .rawPtr m (transform norm p)
  | .f32 => .f32
  | .f64 => .f64
  | .unit => .unit
  | .zst => .zst

/-- Encode one (already transformed) type, threading the dictionary. -/
noncomputable def encodeTy : RTy → List RKey → String × List RKey
  | .bool, d => ("b", d)
  | .int t, d => compress d (.ty (.int t)) (intVendor t)
  | .f32, d => ("f", d)
  | .f64, d => ("d", d)
  | .char, d => compress d (.ty .char) "u4char"
  | .unit, d => ("v", d)
  | .cVoid, d => ("v", d)
  | .zst, d => ("", d)
  | .transparent t, d => encodeTy t d
  | .rawPtr m p, d =>
    let r := encodeTy p d
    let q := if m then r else compress r.2 (.constOf p) ("K" ++ r.1)
    compress q.2 (.ty (.rawPtr m p)) ("P" ++ q.1)

def isZst : RTy → Bool
  | .zst => true
  | _ => false

/-- Parameters in order; zero-sized arguments are skipped. -/
noncomputable def encodeArgs (norm : Bool) : List RTy → List RKey → String
  | [], _ => ""
  | a :: as, d =>
    if isZst a then encodeArgs norm as d
    else
      let r := encodeTy (transform norm a) d
      r.1 ++ encodeArgs norm as r.2

/-- rustc's type-id string for a function with the given return and
parameter types; `v` stands for an empty parameter list after skipping. -/
noncomputable def rustTypeId (norm : Bool) (ret : RTy) (args : List RTy) : String :=
  let r := encodeTy (transform norm ret) []
  "_ZTSF" ++ r.1 ++ (if args.all isZst then "v" else encodeArgs norm args r.2) ++ "E"
    ++ (if norm then ".normalized" else "")

/-! ### 3b. Clang, C function types on an LP64 target with signed `char` -/

inductive CInt where
  | bool | char | schar | uchar | short | ushort | int | uint | long | ulong | llong | ullong
  deriving DecidableEq

inductive CTy where
  | void | int (t : CInt) | float | double
  | ptr (constPointee : Bool) (pointee : CTy)

noncomputable def decEqCTy : (a b : CTy) → Decidable (a = b)
  | .void, .void => isTrue rfl
  | .int a, .int b => match decEq a b with
    | isTrue h => isTrue (congrArg CTy.int h)
    | isFalse h => isFalse (fun e => by injection e with e'; exact h e')
  | .float, .float => isTrue rfl
  | .double, .double => isTrue rfl
  | .ptr k1 p1, .ptr k2 p2 =>
    match decEq k1 k2, decEqCTy p1 p2 with
    | isTrue hk, isTrue hp => isTrue (by subst hk; subst hp; rfl)
    | isFalse hk, _ => isFalse (fun e => by injection e with e1 _; exact hk e1)
    | _, isFalse hp => isFalse (fun e => by injection e with _ e2; exact hp e2)
  | .void, .int _ | .void, .float | .void, .double | .void, .ptr _ _
  | .int _, .void | .int _, .float | .int _, .double | .int _, .ptr _ _
  | .float, .void | .float, .int _ | .float, .double | .float, .ptr _ _
  | .double, .void | .double, .int _ | .double, .float | .double, .ptr _ _
  | .ptr _ _, .void | .ptr _ _, .int _ | .ptr _ _, .float | .ptr _ _, .double =>
    isFalse (fun h => nomatch h)

noncomputable instance : DecidableEq CTy := decEqCTy

/-- Dictionary keys.  Normalised integers share one representative per
signedness and width; every compound type is keyed by the C type itself. -/
inductive CKey where
  | norm (signed : Bool) (bits : Nat)
  | ty (t : CTy)
  | constOf (t : CTy)

noncomputable instance : DecidableEq CKey := fun a b =>
  match a, b with
  | .norm s1 b1, .norm s2 b2 =>
    match decEq s1 s2, decEq b1 b2 with
    | isTrue hs, isTrue hb => isTrue (by subst hs; subst hb; rfl)
    | isFalse hs, _ => isFalse (fun e => by injection e with e1 _; exact hs e1)
    | _, isFalse hb => isFalse (fun e => by injection e with _ e2; exact hb e2)
  | .ty x, .ty y => match decEq x y with
    | isTrue h => isTrue (congrArg CKey.ty h)
    | isFalse h => isFalse (fun e => by injection e with e'; exact h e')
  | .constOf x, .constOf y => match decEq x y with
    | isTrue h => isTrue (congrArg CKey.constOf h)
    | isFalse h => isFalse (fun e => by injection e with e'; exact h e')
  | .norm _ _, .ty _ | .norm _ _, .constOf _
  | .ty _, .norm _ _ | .ty _, .constOf _
  | .constOf _, .norm _ _ | .constOf _, .ty _ => isFalse (fun h => nomatch h)

def cSigned : CInt → Bool
  | .char | .schar | .short | .int | .long | .llong => true
  | .bool | .uchar | .ushort | .uint | .ulong | .ullong => false

def cBits : CInt → Nat
  | .bool | .char | .schar | .uchar => 8
  | .short | .ushort => 16
  | .int | .uint => 32
  | .long | .ulong | .llong | .ullong => 64

/-- Itanium builtin codes. -/
def cCode : CInt → String
  | .bool => "b" | .char => "c" | .schar => "a" | .uchar => "h"
  | .short => "s" | .ushort => "t" | .int => "i" | .uint => "j"
  | .long => "l" | .ulong => "m" | .llong => "x" | .ullong => "y"

def normVendor (signed : Bool) (bits : Nat) : String :=
  if bits = 8 then (if signed then "u2i8" else "u2u8")
  else if bits = 16 then (if signed then "u3i16" else "u3u16")
  else if bits = 32 then (if signed then "u3i32" else "u3u32")
  else if bits = 64 then (if signed then "u3i64" else "u3u64")
  else (if signed then "u4i128" else "u4u128")

noncomputable def cEncodeTy (norm : Bool) : CTy → List CKey → String × List CKey
  | .void, d => ("v", d)
  | .float, d => ("f", d)
  | .double, d => ("d", d)
  | .int t, d =>
    if norm then compress d (.norm (cSigned t) (cBits t)) (normVendor (cSigned t) (cBits t))
    else (cCode t, d)
  | .ptr k p, d =>
    let r := cEncodeTy norm p d
    let q := if k then compress r.2 (.constOf p) ("K" ++ r.1) else r
    compress q.2 (.ty (.ptr k p)) ("P" ++ q.1)

noncomputable def cEncodeArgs (norm : Bool) : List CTy → List CKey → String
  | [], _ => ""
  | a :: as, d =>
    let r := cEncodeTy norm a d
    r.1 ++ cEncodeArgs norm as r.2

noncomputable def clangTypeId (norm : Bool) (ret : CTy) (args : List CTy) : String :=
  let r := cEncodeTy norm ret []
  "_ZTSF" ++ r.1 ++ (if args.isEmpty then "v" else cEncodeArgs norm args r.2) ++ "E"
    ++ (if norm then ".normalized" else "")

/-! ### 3c. Evaluated type-id strings -/

theorem rust_u64_i32 :
    rustTypeId false (.int .u64) [.int .i32] = "_ZTSFu3u64u3i32E"
      ∧ rustTypeId true (.int .u64) [.int .i32] = "_ZTSFu3u64u3i32E.normalized" := by repeat constructor

/-- A `#[repr(transparent)]` wrapper of `u32` is encoded as `u32`, here as a
back-reference to the return type. -/
theorem rust_transparent_u32 :
    rustTypeId false (.int .u32) [.transparent (.int .u32)] = "_ZTSFu3u32S_E"
      ∧ rustTypeId true (.int .u32) [.transparent (.int .u32)] = "_ZTSFu3u32S_E.normalized"
      ∧ rustTypeId true (.int .u32) [.transparent (.transparent (.int .u32))]
          = "_ZTSFu3u32S_E.normalized" := by repeat constructor

theorem rust_substitutions :
    rustTypeId false (.int .u32) [.int .u32, .int .u32, .int .u32] = "_ZTSFu3u32S_S_S_E"
      ∧ rustTypeId false .unit [.int .i8, .int .u8, .int .i8, .int .u8] = "_ZTSFvu2i8u2u8S_S0_E"
      ∧ rustTypeId false .unit
          [.int .i8, .int .i16, .int .i32, .int .i64, .int .u8, .int .u16, .int .u32, .int .u64,
           .int .i8, .int .u64]
          = "_ZTSFvu2i8u3i16u3i32u3i64u2u8u3u16u3u32u3u64S_S6_E" := by repeat constructor

theorem rust_pointers :
    rustTypeId false .unit [.rawPtr false (.int .i32), .rawPtr false (.int .i32), .int .i32]
        = "_ZTSFvPKu3i32S1_S_E"
      ∧ rustTypeId false .unit [.rawPtr true (.int .i32), .rawPtr false (.int .i32)]
        = "_ZTSFvPu3i32PKS_E"
      ∧ rustTypeId false (.rawPtr false (.rawPtr false (.int .u8))) [.rawPtr false (.int .u8)]
        = "_ZTSFPKPKu2u8S1_E"
      ∧ rustTypeId false .unit [.rawPtr true .cVoid, .rawPtr false .cVoid] = "_ZTSFvPvPKvE"
      ∧ rustTypeId true .unit [.rawPtr true (.int .i64), .rawPtr true (.int .i64)]
        = "_ZTSFvPu3i64S0_E.normalized" := by repeat constructor

/-- Zero-sized arguments leave no trace; a list of only such arguments is `v`. -/
theorem rust_zero_sized_arguments :
    rustTypeId false .unit [.zst, .zst] = "_ZTSFvvE"
      ∧ rustTypeId false .unit [] = "_ZTSFvvE"
      ∧ rustTypeId false .unit [.zst, .int .u16] = "_ZTSFvu3u16E" := by repeat constructor

theorem rust_integer_normalisation :
    rustTypeId false .bool [.bool, .char, .int .usize, .int .isize] = "_ZTSFbbu4charu5usizeu5isizeE"
      ∧ rustTypeId true .bool [.bool, .char, .int .usize, .int .isize]
          = "_ZTSFu2u8S_u3u32u3u64u3i64E.normalized"
      ∧ rustTypeId false (.int .u64) [.int .usize, .int .u64] = "_ZTSFu3u64u5usizeS_E"
      ∧ rustTypeId true (.int .u64) [.int .usize, .int .u64] = "_ZTSFu3u64S_S_E.normalized" := by repeat constructor

theorem clang_u64_i32 :
    clangTypeId false (.int .ulong) [.int .int] = "_ZTSFmiE"
      ∧ clangTypeId false (.int .ullong) [.int .int] = "_ZTSFyiE"
      ∧ clangTypeId true (.int .ulong) [.int .int] = "_ZTSFu3u64u3i32E.normalized"
      ∧ clangTypeId true (.int .ullong) [.int .int] = "_ZTSFu3u64u3i32E.normalized" := by repeat constructor

theorem clang_u32_u32 :
    clangTypeId false (.int .uint) [.int .uint] = "_ZTSFjjE"
      ∧ clangTypeId true (.int .uint) [.int .uint] = "_ZTSFu3u32S_E.normalized" := by repeat constructor

theorem clang_pointers :
    clangTypeId false .void [.ptr false (.int .long), .ptr false (.int .long)] = "_ZTSFvPlS_E"
      ∧ clangTypeId false .void [.ptr true (.int .char), .ptr true (.int .schar)] = "_ZTSFvPKcPKaE"
      ∧ clangTypeId true .void [.int .long, .int .llong] = "_ZTSFvu3i64S_E.normalized"
      ∧ clangTypeId true .void [.ptr false (.int .long), .ptr false (.int .long)]
          = "_ZTSFvPu3i64S0_E.normalized"
      ∧ clangTypeId true .void [.ptr false (.int .long), .ptr false (.int .llong)]
          = "_ZTSFvPu3i64PS_E.normalized"
      ∧ clangTypeId true .void [.ptr true (.int .ulong), .ptr true (.int .ullong), .int .ullong]
          = "_ZTSFvPKu3u64PKS_S_E.normalized" := by repeat constructor

/-! ### 3d. Agreement of the two encoders on integer signatures under normalisation -/

/-- Signedness and width of a Rust integer type on a 64-bit target. -/
def rWB : IntTy → Bool × Nat
  | .i8 => (true, 8) | .i16 => (true, 16) | .i32 => (true, 32) | .i64 => (true, 64)
  | .i128 => (true, 128) | .isize => (true, 64)
  | .u8 => (false, 8) | .u16 => (false, 16) | .u32 => (false, 32) | .u64 => (false, 64)
  | .u128 => (false, 128) | .usize => (false, 64)

/-- Signedness and width of a C integer type (LP64, signed `char`). -/
def cWB (c : CInt) : Bool × Nat := (cSigned c, cBits c)

/-- Dictionary key rustc uses for a normalised integer. -/
def rKey (r : IntTy) : RKey := .ty (.int (fixWidth r))

/-- Dictionary key Clang uses for a normalised integer. -/
def cKey (c : CInt) : CKey := .norm (cSigned c) (cBits c)

theorem rKey_eq_iff (a b : IntTy) : rKey a = rKey b ↔ rWB a = rWB b := by
  cases a <;> cases b <;> constructor <;> intro h <;> cases h <;> rfl

theorem cKey_eq_iff (a b : CInt) : cKey a = cKey b ↔ cWB a = cWB b := by
  cases a <;> cases b <;> constructor <;> intro h <;> cases h <;> rfl

theorem vendor_names_agree (r : IntTy) (c : CInt) :
    rWB r = cWB c → intVendor (fixWidth r) = normVendor (cSigned c) (cBits c) := by
  cases r <;> cases c <;> decide

theorem findIdx_append {α : Type} [DecidableEq α] (k x : α) (d : List α) :
    findIdx k (d ++ [x]) =
      match findIdx k d with
      | some i => some i
      | none => if x = k then some d.length else none := by
  induction d with
  | nil => by_cases hx : x = k <;> simp [findIdx, hx]
  | cons y ys ih =>
    by_cases hy : y = k
    · simp [findIdx, hy]
    · simp only [List.cons_append, findIdx, hy, ite_false, ih, List.length_cons]
      cases findIdx k ys with
      | some i => rfl
      | none => by_cases hx : x = k <;> simp [hx]

/-- The two dictionaries answer every pair of ABI-compatible integer lookups alike. -/
def Sim (d : List RKey) (d' : List CKey) : Prop :=
  d.length = d'.length ∧ ∀ r c, rWB r = cWB c → findIdx (rKey r) d = findIdx (cKey c) d'

theorem sim_nil : Sim [] [] := ⟨rfl, fun _ _ _ => rfl⟩

theorem sim_step (d : List RKey) (d' : List CKey) (hs : Sim d d') (r : IntTy) (c : CInt)
    (h : rWB r = cWB c) :
    (compress d (rKey r) (intVendor (fixWidth r))).1
        = (compress d' (cKey c) (normVendor (cSigned c) (cBits c))).1
      ∧ Sim (compress d (rKey r) (intVendor (fixWidth r))).2
          (compress d' (cKey c) (normVendor (cSigned c) (cBits c))).2 := by
  obtain ⟨hlen, hfind⟩ := hs
  unfold compress
  rw [hfind r c h]
  cases findIdx (cKey c) d' with
  | some i => exact ⟨rfl, hlen, hfind⟩
  | none =>
    refine ⟨vendor_names_agree r c h, ?_, ?_⟩
    · simp [hlen]
    · intro r1 c1 h1
      rw [findIdx_append, findIdx_append, hfind r1 c1 h1]
      cases findIdx (cKey c1) d' with
      | some i => rfl
      | none =>
        have hk : rKey r = rKey r1 ↔ cKey c = cKey c1 := by
          rw [rKey_eq_iff, cKey_eq_iff, h, h1]
        by_cases hr : rKey r = rKey r1
        · simp [hr, hk.1 hr, hlen]
        · have hc' : ¬ cKey c = cKey c1 := fun e => hr (hk.2 e)
          simp [hr, hc']

theorem args_agree (ps : List (IntTy × CInt)) (hps : ∀ p ∈ ps, rWB p.1 = cWB p.2) :
    ∀ (d : List RKey) (d' : List CKey), Sim d d' →
      encodeArgs true (ps.map fun p => RTy.int p.1) d
        = cEncodeArgs true (ps.map fun p => CTy.int p.2) d' := by
  induction ps with
  | nil => intro d d' _; rfl
  | cons p ps ih =>
    intro d d' hs
    have hstep := sim_step d d' hs p.1 p.2 (hps p (List.mem_cons_self))
    have ih' := ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) _ _ hstep.2
    show (compress d (rKey p.1) (intVendor (fixWidth p.1))).1
          ++ encodeArgs true (ps.map fun p => RTy.int p.1)
              (compress d (rKey p.1) (intVendor (fixWidth p.1))).2
        = (compress d' (cKey p.2) (normVendor (cSigned p.2) (cBits p.2))).1
          ++ cEncodeArgs true (ps.map fun p => CTy.int p.2)
              (compress d' (cKey p.2) (normVendor (cSigned p.2) (cBits p.2))).2
    rw [hstep.1, ih']

/-- **Cross-language agreement.** For every function type whose return type
and parameters are integers, if each Rust integer has the same signedness and
width as the C integer in the same position (LP64), rustc and Clang produce
the same normalised type-id string, for any arity and any pattern of
repetition. -/
theorem normalized_integer_signatures_agree (r : IntTy) (c : CInt) (ps : List (IntTy × CInt))
    (hret : rWB r = cWB c) (hargs : ∀ p ∈ ps, rWB p.1 = cWB p.2) :
    rustTypeId true (.int r) (ps.map fun p => RTy.int p.1)
      = clangTypeId true (.int c) (ps.map fun p => CTy.int p.2) := by
  have hstep := sim_step [] [] sim_nil r c hret
  have hbody := args_agree ps hargs _ _ hstep.2
  cases ps with
  | nil =>
    show "_ZTSF" ++ (compress [] (rKey r) (intVendor (fixWidth r))).1 ++ "v" ++ "E" ++ ".normalized"
        = "_ZTSF" ++ (compress [] (cKey c) (normVendor (cSigned c) (cBits c))).1 ++ "v" ++ "E"
          ++ ".normalized"
    rw [hstep.1]
  | cons p ps =>
    show "_ZTSF" ++ (compress [] (rKey r) (intVendor (fixWidth r))).1
          ++ encodeArgs true ((p :: ps).map fun p => RTy.int p.1)
              (compress [] (rKey r) (intVendor (fixWidth r))).2 ++ "E" ++ ".normalized"
        = "_ZTSF" ++ (compress [] (cKey c) (normVendor (cSigned c) (cBits c))).1
          ++ cEncodeArgs true ((p :: ps).map fun p => CTy.int p.2)
              (compress [] (cKey c) (normVendor (cSigned c) (cBits c))).2 ++ "E" ++ ".normalized"
    rw [hstep.1, hbody]

/-- Hence the call-site guard passes for such a cross-language call. -/
theorem normalized_integer_signature_passes_guard (r : IntTy) (c : CInt)
    (ps : List (IntTy × CInt)) (hret : rWB r = cWB c) (hargs : ∀ p ∈ ps, rWB p.1 = cWB p.2) :
    guardPasses (kcfiTypeId (clangTypeId true (.int c) (ps.map fun p => CTy.int p.2)))
      (kcfiTypeId (rustTypeId true (.int r) (ps.map fun p => RTy.int p.1))) = true := by
  rw [guardPasses_iff, normalized_integer_signatures_agree r c ps hret hargs]

/-- **Divergence without normalisation.** For a function that returns an
integer and takes no parameters, no pairing of a Rust integer type with a C
integer type gives equal identifiers: rustc writes a vendor-extended name
(`u3u64`), Clang a builtin code (`m`, `y`). -/
theorem unnormalized_integer_return_never_agrees (r : IntTy) (c : CInt) :
    kcfiTypeId (rustTypeId false (.int r) []) ≠ kcfiTypeId (clangTypeId false (.int c) []) := by
  cases r <;> cases c <;> decide +kernel

/-! ## 4. One tag per address -/

/-- What the code at an entry does. -/
inductive Body where
  /-- the function's own body -/
  | code
  /-- a direct jump to another entry; direct transfers are not checked -/
  | jmp (target : Nat)

/-- A function entry: the 32-bit word at `entry - 4` and the code. -/
structure Entry where
  tag : UInt32
  body : Body

/-- A code image.  Each address has at most one entry, hence at most one tag. -/
abbrev Image := Nat → Option Entry

inductive Outcome where
  | returned (v : Nat)
  /-- `ud2` after a failed guard -/
  | trap
  /-- control reached an address that is not a function entry -/
  | fault
  deriving DecidableEq

/-- Run from an entry, following at most `fuel` direct jumps.  `sem a x` is
the value the `code` body at address `a` returns for argument `x`. -/
noncomputable def exec (img : Image) (sem : Nat → Nat → Nat) : Nat → Nat → Nat → Outcome
  | 0, _, _ => .fault
  | fuel + 1, addr, arg =>
    match img addr with
    | none => .fault
    | some e =>
      match e.body with
      | .code => .returned (sem addr arg)
      | .jmp t => exec img sem fuel t arg

/-- An indirect call with the expected identifier of the call site. -/
noncomputable def indirectCall (img : Image) (sem : Nat → Nat → Nat) (expected : UInt32) (target arg : Nat) :
    Outcome :=
  match img target with
  | none => .fault
  | some e => if guardPasses expected e.tag then exec img sem 2 target arg else .trap

theorem guardPasses_self (e : UInt32) : guardPasses e e = true := (guardPasses_iff e e).2 rfl

theorem guardPasses_of_ne {expected found : UInt32} (h : found ≠ expected) :
    guardPasses expected found = false := by
  cases hg : guardPasses expected found with
  | false => rfl
  | true => exact absurd ((guardPasses_iff expected found).1 hg) h

theorem exec_ne_trap (img : Image) (sem : Nat → Nat → Nat) (fuel addr arg : Nat) :
    exec img sem fuel addr arg ≠ .trap := by
  induction fuel generalizing addr with
  | zero => intro h; cases h
  | succ n ih =>
    unfold exec
    split
    · intro h; cases h
    · split
      · intro h; cases h
      · exact ih _

/-- The guard is sound and complete for the tag: an indirect call to an entry
traps exactly when the entry's tag differs from the identifier the call site
expects. -/
theorem indirectCall_traps_iff (img : Image) (sem : Nat → Nat → Nat) (expected : UInt32)
    (target arg : Nat) (e : Entry) (h : img target = some e) :
    indirectCall img sem expected target arg = .trap ↔ e.tag ≠ expected := by
  unfold indirectCall
  rw [h]
  by_cases hg : guardPasses expected e.tag = true
  · have he : e.tag = expected := (guardPasses_iff _ _).1 hg
    simp [he, guardPasses_self, exec_ne_trap]
  · have hne : e.tag ≠ expected := fun he => hg ((guardPasses_iff _ _).2 he)
    simp [hg, hne]

/-- A method at `aM` tagged with the self-erased identifier, and a trampoline
at `aS` tagged with the concrete-self identifier that jumps to it. -/
def withTrampoline (aM aS : Nat) (idErased idConcrete : UInt32) : Image := fun a =>
  if a = aM then some ⟨idErased, .code⟩
  else if a = aS then some ⟨idConcrete, .jmp aM⟩
  else none

/-- A single entry at `a` with one tag. -/
def singleEntry (a : Nat) (tag : UInt32) : Image := fun b =>
  if b = a then some ⟨tag, .code⟩ else none

/-- **The trampoline bridges the two uses of a method.**  With distinct
identifiers for the self-erased and the concrete-self signature:
the vtable slot (method entry) passes the `dyn` call site; the function
pointer (trampoline entry) passes the function-pointer call site and returns
exactly what the method returns; and each entry is rejected at the other
call site. -/
theorem reifyFnPtr_trampoline_bridges_vtable_and_fnptr_kcfi
    (aM aS : Nat) (hA : aS ≠ aM) (idErased idConcrete : UInt32) (hne : idErased ≠ idConcrete)
    (sem : Nat → Nat → Nat) (x : Nat) :
    indirectCall (withTrampoline aM aS idErased idConcrete) sem idErased aM x
        = .returned (sem aM x)
      ∧ indirectCall (withTrampoline aM aS idErased idConcrete) sem idConcrete aS x
        = .returned (sem aM x)
      ∧ indirectCall (withTrampoline aM aS idErased idConcrete) sem idConcrete aM x = .trap
      ∧ indirectCall (withTrampoline aM aS idErased idConcrete) sem idErased aS x = .trap := by
  have hne' : idConcrete ≠ idErased := fun h => hne h.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [indirectCall, withTrampoline, exec, guardPasses_self]
  · simp [indirectCall, withTrampoline, exec, guardPasses_self, hA]
  · simp [indirectCall, withTrampoline, guardPasses_of_ne hne]
  · simp [indirectCall, withTrampoline, hA, guardPasses_of_ne hne']

/-- **Counterexample 2.** Without a trampoline the method has one entry and
therefore one tag; whatever that tag is, the `dyn` call site or the
function-pointer call site traps on it. -/
theorem ce2_omitting_reify_fnptr_trampoline_breaks_either_vtable_or_fnptr_kcfi
    (aM : Nat) (tag idErased idConcrete : UInt32) (hne : idErased ≠ idConcrete)
    (sem : Nat → Nat → Nat) (x : Nat) :
    indirectCall (singleEntry aM tag) sem idErased aM x = .trap
      ∨ indirectCall (singleEntry aM tag) sem idConcrete aM x = .trap := by
  by_cases ht : tag = idErased
  · right
    have h2 : tag ≠ idConcrete := ht ▸ hne
    simp [indirectCall, singleEntry, guardPasses_of_ne h2]
  · left
    simp [indirectCall, singleEntry, guardPasses_of_ne ht]

/-! ### 4a. The method `<Counter as Step>::step` and its trampoline

Type-id strings of `fn step(&self, x: u32) -> u32` for a crate named
`reify_kcfi`: with `Self` erased to `dyn Step` (the method's own tag and what
a `dyn` call site expects), and with the concrete `Self = Counter` (the
trampoline's tag and what a `fn(&Counter, u32) -> u32` call site expects).
The crate disambiguator after `C` depends on the compiler build. -/

def stepErased : String :=
  "_ZTSFu3u32u3refIu3dynIu33NtCskdnFWz4JOn6_10reify_kcfi4Stepu6regionEES_E"

def stepConcrete : String :=
  "_ZTSFu3u32u3refIu36NtCskdnFWz4JOn6_10reify_kcfi7CounterES_E"

theorem step_ids :
    kcfiTypeId stepErased = 68117223 ∧ kcfiTypeId stepConcrete = 1587319811 := by
  repeat constructor

/-- The same two strings with crate disambiguator `kSCH9d8WqNd`. -/
theorem step_ids_other_disambiguator :
    kcfiTypeId "_ZTSFu3u32u3refIu3dynIu33NtCskSCH9d8WqNd_10reify_kcfi4Stepu6regionEES_E"
        = 1701147868
      ∧ kcfiTypeId "_ZTSFu3u32u3refIu36NtCskSCH9d8WqNd_10reify_kcfi7CounterES_E" = 551552321 := by
  repeat constructor

/-- The trampoline theorem at these identifiers. -/
theorem step_trampoline (aM aS : Nat) (hA : aS ≠ aM) (sem : Nat → Nat → Nat) (x : Nat) :
    indirectCall (withTrampoline aM aS (kcfiTypeId stepErased) (kcfiTypeId stepConcrete)) sem
        (kcfiTypeId stepErased) aM x = .returned (sem aM x)
      ∧ indirectCall (withTrampoline aM aS (kcfiTypeId stepErased) (kcfiTypeId stepConcrete)) sem
        (kcfiTypeId stepConcrete) aS x = .returned (sem aM x)
      ∧ indirectCall (withTrampoline aM aS (kcfiTypeId stepErased) (kcfiTypeId stepConcrete)) sem
        (kcfiTypeId stepConcrete) aM x = .trap
      ∧ indirectCall (withTrampoline aM aS (kcfiTypeId stepErased) (kcfiTypeId stepConcrete)) sem
        (kcfiTypeId stepErased) aS x = .trap :=
  reifyFnPtr_trampoline_bridges_vtable_and_fnptr_kcfi aM aS hA _ _
    (by rw [step_ids.1, step_ids.2]; decide) sem x

/-! ## 5. Counterexamples -/

theorem ce1_ids :
    kcfiTypeId (rustTypeId false (.int .u64) [.int .i32]) = 3837184471
      ∧ kcfiTypeId (clangTypeId false (.int .ulong) [.int .int]) = 3945929266
      ∧ kcfiTypeId (clangTypeId false (.int .ullong) [.int .int]) = 2900422046
      ∧ kcfiTypeId (rustTypeId true (.int .u64) [.int .i32]) = 2701021033
      ∧ kcfiTypeId (clangTypeId true (.int .ulong) [.int .int]) = 2701021033
      ∧ kcfiTypeId (clangTypeId true (.int .ullong) [.int .int]) = 2701021033 := by
  repeat constructor

/-- **Counterexample 1.** A C caller holding `uint64_t (*)(int32_t)` calls a
Rust `extern "C" fn(i32) -> u64`.  Without integer normalisation the call
traps, whether `uint64_t` is `unsigned long` or `unsigned long long`; with
normalisation on both sides it returns. -/
theorem ce1_unnormalized_lp64_uint64_c_rust_ffi_triggers_ud2_trap
    (a : Nat) (sem : Nat → Nat → Nat) (x : Nat) :
    indirectCall (singleEntry a (kcfiTypeId (rustTypeId false (.int .u64) [.int .i32]))) sem
        (kcfiTypeId (clangTypeId false (.int .ulong) [.int .int])) a x = .trap
      ∧ indirectCall (singleEntry a (kcfiTypeId (rustTypeId false (.int .u64) [.int .i32]))) sem
        (kcfiTypeId (clangTypeId false (.int .ullong) [.int .int])) a x = .trap
      ∧ indirectCall (singleEntry a (kcfiTypeId (rustTypeId true (.int .u64) [.int .i32]))) sem
        (kcfiTypeId (clangTypeId true (.int .ulong) [.int .int])) a x = .returned (sem a x) := by
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := ce1_ids
  rw [h1, h2, h3, h4, h5]
  refine ⟨?_, ?_, ?_⟩
  · simp [indirectCall, singleEntry, guardPasses_of_ne (show (3837184471 : UInt32) ≠ 3945929266 by decide)]
  · simp [indirectCall, singleEntry, guardPasses_of_ne (show (3837184471 : UInt32) ≠ 2900422046 by decide)]
  · simp [indirectCall, singleEntry, exec, guardPasses_self]

/-- **Counterexample 3.** Two different function types whose 64-bit hashes
differ and whose 32-bit identifiers coincide: `fn(isize, bool, usize, f32, i64)`
and `fn(u8, u64, f64, u16, i8)`. -/
theorem ce3_xxhash64_truncation_collision_boundary :
    rustTypeId false .unit [.int .isize, .bool, .int .usize, .f32, .int .i64]
        = "_ZTSFvu5isizebu5usizefu3i64E"
      ∧ rustTypeId false .unit [.int .u8, .int .u64, .f64, .int .u16, .int .i8]
        = "_ZTSFvu2u8u3u64du3u16u2i8E"
      ∧ xxHash64Seed0 (utf8Bytes "_ZTSFvu5isizebu5usizefu3i64E") = 0xa62274beba801ccf
      ∧ xxHash64Seed0 (utf8Bytes "_ZTSFvu2u8u3u64du3u16u2i8E") = 0xc41a702dba801ccf
      ∧ kcfiTypeId "_ZTSFvu5isizebu5usizefu3i64E" = 3128958159
      ∧ kcfiTypeId "_ZTSFvu2u8u3u64du3u16u2i8E" = 3128958159 := by
  repeat constructor

/-- A call through the second type to a function of the first type is not trapped. -/
theorem ce3_wrong_signature_call_is_not_trapped (a : Nat) (sem : Nat → Nat → Nat) (x : Nat) :
    indirectCall (singleEntry a (kcfiTypeId "_ZTSFvu5isizebu5usizefu3i64E")) sem
      (kcfiTypeId "_ZTSFvu2u8u3u64du3u16u2i8E") a x = .returned (sem a x) := by
  obtain ⟨_, _, _, _, h5, h6⟩ := ce3_xxhash64_truncation_collision_boundary
  rw [h5, h6]
  simp [indirectCall, singleEntry, exec, guardPasses_self]

theorem ce4_ids :
    rustTypeId false (.int .u32) [.rawPtr true (.int .i32), .rawPtr false (.int .i32)]
        = "_ZTSFu3u32Pu3i32PKS0_E"
      ∧ rustTypeId false (.int .u32) [.rawPtr true (.int .u8), .rawPtr false (.int .u8)]
        = "_ZTSFu3u32Pu2u8PKS0_E"
      ∧ kcfiTypeId "_ZTSFu3u32Pu3i32PKS0_E" = 2077473701
      ∧ kcfiTypeId "_ZTSFu3u32Pu2u8PKS0_E" = 1133697259 := by
  repeat constructor

/-- **Counterexample 4.** `fn(*mut i32, *const i32) -> u32` and
`fn(*mut u8, *const u8) -> u32` have different identifiers.  If two such
functions are folded into one entry that keeps the second identifier, a
type-correct call through the first type traps. -/
theorem ce4_folding_differently_typed_functions_traps_a_type_correct_call
    (a : Nat) (sem : Nat → Nat → Nat) (x : Nat) :
    indirectCall (singleEntry a (kcfiTypeId "_ZTSFu3u32Pu2u8PKS0_E")) sem
        (kcfiTypeId "_ZTSFu3u32Pu2u8PKS0_E") a x = .returned (sem a x)
      ∧ indirectCall (singleEntry a (kcfiTypeId "_ZTSFu3u32Pu2u8PKS0_E")) sem
        (kcfiTypeId "_ZTSFu3u32Pu3i32PKS0_E") a x = .trap := by
  obtain ⟨_, _, h3, h4⟩ := ce4_ids
  rw [h3, h4]
  refine ⟨?_, ?_⟩
  · simp [indirectCall, singleEntry, exec, guardPasses_self]
  · simp [indirectCall, singleEntry, guardPasses_of_ne (show (1133697259 : UInt32) ≠ 2077473701 by decide)]

theorem ce5_ids :
    rustTypeId true .unit [.rawPtr true (.int .i64), .rawPtr true (.int .i64)]
        = "_ZTSFvPu3i64S0_E.normalized"
      ∧ clangTypeId true .void [.ptr false (.int .long), .ptr false (.int .long)]
        = "_ZTSFvPu3i64S0_E.normalized"
      ∧ clangTypeId true .void [.ptr false (.int .long), .ptr false (.int .llong)]
        = "_ZTSFvPu3i64PS_E.normalized"
      ∧ kcfiTypeId "_ZTSFvPu3i64S0_E.normalized" = 1309558340
      ∧ kcfiTypeId "_ZTSFvPu3i64PS_E.normalized" = 293747588 := by
  repeat constructor

/-- **Counterexample 5.** Integer normalisation does not extend to pointers:
`void (*)(long *, long long *)` and Rust `extern "C" fn(*mut i64, *mut i64)`
have different normalised identifiers, so that call traps, while the
prototype `void (*)(long *, long *)` agrees with rustc. -/
theorem ce5_normalized_pointers_to_long_and_long_long_still_trap
    (a : Nat) (sem : Nat → Nat → Nat) (x : Nat) :
    indirectCall (singleEntry a (kcfiTypeId "_ZTSFvPu3i64S0_E.normalized")) sem
        (kcfiTypeId "_ZTSFvPu3i64S0_E.normalized") a x = .returned (sem a x)
      ∧ indirectCall (singleEntry a (kcfiTypeId "_ZTSFvPu3i64S0_E.normalized")) sem
        (kcfiTypeId "_ZTSFvPu3i64PS_E.normalized") a x = .trap := by
  obtain ⟨_, _, _, h4, h5⟩ := ce5_ids
  rw [h4, h5]
  refine ⟨?_, ?_⟩
  · simp [indirectCall, singleEntry, exec, guardPasses_self]
  · simp [indirectCall, singleEntry, guardPasses_of_ne (show (1309558340 : UInt32) ≠ 293747588 by decide)]

end KcfiReify

/-! ## 6. Axiom audit

Every theorem above, and the main definitions.  The expected output lists
only `propext` and `Quot.sound` (or no axioms). -/

#print axioms KcfiReify.xxHash64Seed0
#print axioms KcfiReify.kcfiTypeId
#print axioms KcfiReify.rustTypeId
#print axioms KcfiReify.clangTypeId
#print axioms KcfiReify.indirectCall
#print axioms KcfiReify.xxh64_empty
#print axioms KcfiReify.xxh64_a
#print axioms KcfiReify.xxh64_abc
#print axioms KcfiReify.xxh64_39_bytes
#print axioms KcfiReify.kcfi_u64_i32_normalized
#print axioms KcfiReify.kcfi_u32_u32_normalized
#print axioms KcfiReify.kcfi_u64_i32_rust_default
#print axioms KcfiReify.kcfi_u32_u32_rust_default
#print axioms KcfiReify.kcfi_ulong_int_c_default
#print axioms KcfiReify.kcfi_ullong_int_c_default
#print axioms KcfiReify.kcfi_uint_uint_c_default
#print axioms KcfiReify.kcfi_negated_add_zero_iff_hash_eq
#print axioms KcfiReify.guardPasses_iff
#print axioms KcfiReify.kcfi_negated_add_zero_iff_hash_eq_nat
#print axioms KcfiReify.guard_constants_u64_i32_normalized
#print axioms KcfiReify.masked_guard_iff
#print axioms KcfiReify.maskKCFIType_not_injective
#print axioms KcfiReify.substitution_examples
#print axioms KcfiReify.rust_u64_i32
#print axioms KcfiReify.rust_transparent_u32
#print axioms KcfiReify.rust_substitutions
#print axioms KcfiReify.rust_pointers
#print axioms KcfiReify.rust_zero_sized_arguments
#print axioms KcfiReify.rust_integer_normalisation
#print axioms KcfiReify.clang_u64_i32
#print axioms KcfiReify.clang_u32_u32
#print axioms KcfiReify.clang_pointers
#print axioms KcfiReify.rKey_eq_iff
#print axioms KcfiReify.cKey_eq_iff
#print axioms KcfiReify.vendor_names_agree
#print axioms KcfiReify.findIdx_append
#print axioms KcfiReify.sim_nil
#print axioms KcfiReify.sim_step
#print axioms KcfiReify.args_agree
#print axioms KcfiReify.normalized_integer_signatures_agree
#print axioms KcfiReify.normalized_integer_signature_passes_guard
#print axioms KcfiReify.unnormalized_integer_return_never_agrees
#print axioms KcfiReify.guardPasses_self
#print axioms KcfiReify.guardPasses_of_ne
#print axioms KcfiReify.exec_ne_trap
#print axioms KcfiReify.indirectCall_traps_iff
#print axioms KcfiReify.reifyFnPtr_trampoline_bridges_vtable_and_fnptr_kcfi
#print axioms KcfiReify.ce2_omitting_reify_fnptr_trampoline_breaks_either_vtable_or_fnptr_kcfi
#print axioms KcfiReify.step_ids
#print axioms KcfiReify.step_ids_other_disambiguator
#print axioms KcfiReify.step_trampoline
#print axioms KcfiReify.ce1_ids
#print axioms KcfiReify.ce1_unnormalized_lp64_uint64_c_rust_ffi_triggers_ud2_trap
#print axioms KcfiReify.ce3_xxhash64_truncation_collision_boundary
#print axioms KcfiReify.ce3_wrong_signature_call_is_not_trapped
#print axioms KcfiReify.ce4_ids
#print axioms KcfiReify.ce4_folding_differently_typed_functions_traps_a_type_correct_call
#print axioms KcfiReify.ce5_ids
#print axioms KcfiReify.ce5_normalized_pointers_to_long_and_long_long_still_trap
