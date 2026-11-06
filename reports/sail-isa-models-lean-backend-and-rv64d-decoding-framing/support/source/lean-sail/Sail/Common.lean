import Sail.Attr

/-
This notation, unlike the default `++` notation, in not elaborated as a `binop`,
which leads to Lean inserting bad coercions.
-/
infixl:65 " +++ "  => HAppend.hAppend

def String.takeStr (s : String) (n : Nat) : String :=
  s.take n |>.toString

def String.dropStr (s : String) (n : Nat) : String :=
  s.drop n |>.toString

namespace Sail

namespace BitVec

abbrev length {w : Nat} (_ : BitVec w) : Nat := w

@[simp_sail]
def toNatInt {w : Nat} (x : BitVec w) : Int :=
  Int.ofNat x.toNat

@[simp_sail]
def signExtend {w : Nat} (x : BitVec w) (w' : Nat) : BitVec w' :=
  x.signExtend w'

@[simp_sail]
def zeroExtend {w : Nat} (x : BitVec w) (w' : Nat) : BitVec w' :=
  x.zeroExtend w'

@[simp_sail]
def truncate {w : Nat} (x : BitVec w) (w' : Nat) : BitVec w' :=
  x.truncate w'

@[simp_sail]
def truncateLsb {w : Nat} (x : BitVec w) (w' : Nat) : BitVec w' :=
  x.extractLsb' (w - w') w'

@[simp_sail]
def extractLsb {w : Nat} (x : BitVec w) (hi lo : Nat) : BitVec (hi - lo + 1) :=
  x.extractLsb hi lo

@[simp_sail]
def updateSubrange' {w : Nat} (x : BitVec w) (start len : Nat) (y : BitVec len) : BitVec w :=
  let mask := ~~~(((BitVec.allOnes len).zeroExtend w) <<< start)
  let y' := ((y.zeroExtend w) <<< start)
  (mask &&& x) ||| y'

@[simp_sail]
def slice {w : Nat} (x : BitVec w) (start len : Nat) : BitVec len :=
  x.extractLsb' start len

@[simp_sail]
def sliceBE {w : Nat} (x : BitVec w) (start len : Nat) : BitVec len :=
  x.extractLsb' (w - start - len) len

@[simp_sail]
def subrangeBE {w : Nat} (x : BitVec w) (lo hi : Nat) : BitVec (hi - lo + 1) :=
  x.extractLsb' (w - hi - 1) _

@[simp_sail]
def updateSubrange {w : Nat} (x : BitVec w) (hi lo : Nat) (y : BitVec (hi - lo + 1)) : BitVec w :=
  updateSubrange' x lo _ y

@[simp_sail]
def updateSubrangeBE {w : Nat} (x : BitVec w) (lo hi : Nat) (y : BitVec (hi - lo + 1)) : BitVec w :=
  updateSubrange' x (w - hi - 1) _ y

@[simp_sail]
def replicateBits {w : Nat} (x : BitVec w) (i : Nat) := BitVec.replicate i x

@[simp_sail]
def access {w : Nat} (x : BitVec w) (i : Nat) : BitVec 1 :=
  BitVec.ofBool x[i]!

@[simp_sail]
def accessBE {w : Nat} (x : BitVec w) (i : Nat) : BitVec 1 :=
  BitVec.ofBool x[w - i - 1]!

@[simp_sail]
def addInt {w : Nat} (x : BitVec w) (i : Int) : BitVec w :=
  x + BitVec.ofInt w i

@[simp_sail]
def subInt (x : BitVec w) (i : Int) : BitVec w :=
  x - BitVec.ofInt w i

@[simp_sail]
def countLeadingZeros (x : BitVec w) : Nat := x.clz.toNat

@[simp_sail]
def countTrailingZeros (x : BitVec w) : Nat :=
  countLeadingZeros (x.reverse)

@[simp_sail]
def append' (x : BitVec n) (y : BitVec m) {mn}
    (hmn : mn = n + m := by (conv => rhs; simp); try rfl) : BitVec mn :=
  (x.append y).cast hmn.symm

@[simp_sail]
def update (x : BitVec m) (n : Nat) (b : BitVec 1) := updateSubrange' x n _ b

@[simp_sail]
def updateBE (x : BitVec m) (n : Nat) (b : BitVec 1) := updateSubrange' x (m - n - 1) _ b

def toBin {w : Nat} (x : BitVec w) : String :=
  String.ofList (List.map (fun c => if c then '1' else '0') (List.ofFn (BitVec.getMsb x)))

def toFormatted {w : Nat} (x : BitVec w) : String :=
  if (length x % 4) == 0 then
    s!"0x{String.toUpper (BitVec.toHex x)}"
  else
    s!"0b{BitVec.toBin x}"

@[simp_sail]
def join1 (xs : List (BitVec 1)) : BitVec xs.length :=
  (BitVec.ofBoolListBE (xs.map fun x => x[0])).cast (by simp)

instance (priority := low) : Coe (BitVec (1 * n)) (BitVec n) where
  coe x := x.cast (by simp)

end BitVec

-- These byte conversion functions use little endian vectors.
def vecbytes_to_bitvec (vec : Vector (BitVec 8) n) : BitVec (8 * n) :=
  vec.foldl
    (fun (i, acc) x => (i+1, acc.or ((x.zeroExtend (8*n)).shiftLeft (i*8))) )
    (0, BitVec.zero (8 * n))
  |> Prod.snd
def bitvec_to_vecbytes (bitvec : BitVec (8 * n)) : Vector (BitVec 8) n :=
  Vector.ofFn (fun i => Sail.BitVec.slice bitvec (8 * i) 8)
def vecbool_to_bitvec (vec : Vector Bool n) : BitVec n :=
  vec.foldl
    (fun (i, acc) b => (i+1, acc.or (((BitVec.ofBool b).zeroExtend n).shiftLeft i) ))
    (0, BitVec.zero n)
  |> Prod.snd
def bitvec_to_vecbool (bitvec : BitVec n) : Vector Bool n :=
  Vector.ofFn (fun i => BitVec.getLsb bitvec i)

def charToHex (c : Char) : BitVec 4 :=
  match c.toLower with
  | '0' => 0 | '1' => 1 | '2' => 2 | '3' => 3 | '4' => 4
  | '5' => 5 | '6' => 6 | '7' => 7 | '8' => 8 | '9' => 9
  | 'a' => 10 | 'b' => 11 | 'c' => 12 | 'd' => 13
  | 'e' => 14 | 'f' => 15 | _ => 0

def round4 (n : Nat) := ((n - 1) / 4) * 4 + 4

def parse_hex_bits_digits (n : Nat) (str : String) : BitVec n :=
  let len := str.length
  if h : n < 4 || len = 0 then BitVec.zero n else
    let bv := parse_hex_bits_digits (n-4) (str.take (len-1)).toString
    let c := String.Pos.Raw.get! str ⟨len-1⟩ |> charToHex
    BitVec.append bv c |>.cast (by simp_all)
decreasing_by simp_all <;> omega

def parse_dec_bits (n : Nat) (str : String) : BitVec n :=
  go str.length str
where
  -- TODO: when there are lemmas about `String.take`, replace with WF induction
  go (fuel : Nat) (str : String) :=
    if fuel = 0 then 0 else
      let lsd := String.Pos.Raw.get! str ⟨str.length - 1⟩
      let rest := str.take (str.length - 1)
      (charToHex lsd).setWidth n + 10#n * go (fuel-1) rest.toString

def parse_hex_bits (n : Nat) (str : String) : BitVec n :=
  let bv := parse_hex_bits_digits (round4 n) (str.drop 2).toString
  bv.setWidth n

def valid_hex_bits (n : Nat) (str : String) : Bool :=
  if str.length < 2 then false else
  let str := str.drop 2 |>.toString
  str.all fun x => x.toLower ∈
    ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f'] &&
  2 ^ n > (parse_hex_bits_digits (round4 n) str).toNat

def valid_dec_bits (_ : Nat) (str : String) : Bool :=
  str.all fun (x : Char) => x.toLower ∈
    ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']

@[simp_sail]
def shift_bits_left (bv : BitVec n) (sh : BitVec m) : BitVec n :=
  bv <<< sh

@[simp_sail]
def shift_bits_right (bv : BitVec n) (sh : BitVec m) : BitVec n :=
  bv >>> sh

@[simp_sail]
def shiftl (bv : BitVec n) (m : Nat) : BitVec n :=
  bv <<< m

@[simp_sail]
def shiftr (bv : BitVec n) (m : Nat) : BitVec n :=
  bv >>> m

@[simp_sail]
def pow2 := (2 ^ ·)

namespace Nat

-- NB: below is taken from Mathlib.Logic.Function.Iterate
/-- Iterate a function. -/
def iterate {α : Sort u} (op : α → α) : Nat → α → α
  | 0, a => a
  | Nat.succ k, a => iterate op k (op a)

def toHex (n : Nat) : String :=
  have nbv : BitVec (Nat.log2 n + 1) := BitVec.ofNat _ n
  "0x" ++ nbv.toHex

def toHexUpper (n : Nat) : String :=
  have nbv : BitVec (Nat.log2 n + 1) := BitVec.ofNat _ n
  "0x" ++ nbv.toHex.toUpper

end Nat

namespace Int

def intAbs (x : Int) : Int := Int.ofNat (Int.natAbs x)

@[simp_sail]
def shiftl (a : Int) (n : Int) : Int :=
  match n with
  | Int.ofNat n => Sail.Nat.iterate (fun x => x * 2) n a
  | Int.negSucc n => Sail.Nat.iterate (fun x => x / 2) (n+1) a

@[simp_sail]
def shiftr (a : Int) (n : Int) : Int :=
  match n with
  | Int.ofNat n => Sail.Nat.iterate (fun x => x / 2) n a
  | Int.negSucc n => Sail.Nat.iterate (fun x => x * 2) (n+1) a


def toHex (i : Int) : String :=
  match i with
  | Int.ofNat n => Nat.toHex n
  | Int.negSucc n => "-" ++ Nat.toHex (n+1)

def toHexUpper (i : Int) : String :=
  match i with
  | Int.ofNat n => Nat.toHexUpper n
  | Int.negSucc n => "-" ++ Nat.toHexUpper (n+1)

end Int

@[simp_sail]
def get_slice_int (len : Nat) (n : Int) (lo : Nat) : BitVec len :=
  BitVec.extractLsb' lo len (BitVec.ofInt (lo + len + 1) n)

@[simp_sail]
def set_slice_int (len : Nat) (n : Int) (lo : Nat) (x : BitVec len) : Int :=
  BitVec.toInt (BitVec.updateSubrange' (BitVec.ofInt len n) lo len x)

@[simp_sail]
def set_slice {n : Nat} (m : Nat) (bv : BitVec n) (start : Nat) (bv' : BitVec m) : BitVec n :=
  BitVec.updateSubrange' bv start m bv'

def String.leadingSpaces (s : String) : Nat :=
  s.length - (s.dropWhile (· = ' ')).positions.length

abbrev Vector.length (_v : Vector α n) : Nat := n

@[simp_sail]
def vectorInit {n : Nat} (a : α) : Vector α n := Vector.replicate n a

@[simp_sail]
def vectorUpdate (v : Vector α m) (n : Nat) (a : α) := v.set! n a

@[simp_sail]
instance : HShiftLeft (BitVec w) Int (BitVec w) where
  hShiftLeft b i :=
    match i with
    | .ofNat n => BitVec.shiftLeft b n
    | .negSucc n => BitVec.ushiftRight b (n + 1)

@[simp_sail]
instance : HShiftRight (BitVec w) Int (BitVec w) where
  hShiftRight b i := b <<< (- i)

inductive Primitive where
  | bool
  | bit
  | int
  | nat
  | string
  | fin (n : Nat)
  | bitvector (n : Nat)

abbrev Primitive.reflect : Primitive → Type
  | bool => Bool
  | bit => BitVec 1
  | int => Int
  | nat => Nat
  | string => String
  | fin n => Fin (n + 1)
  | bitvector n => BitVec n

inductive Error (ue: Type) where
  | Exit
  | Unreachable
  | InfiniteNondeterminisim
  | OutOfMemoryRange (n : Nat)
  | Assertion (s : String)
  | User (e : ue)
open Error

def Error.print : Error UE → String
  | Exit => "Exit"
  | Unreachable => "Unreachable"
  | InfiniteNondeterminisim => "Infinite Nondeterminisim"
  | OutOfMemoryRange n => s!"{n} Out of Memory Range"
  | Assertion s => s!"Assertion failed: {s}"
  | User _ => "Uncaught user exception"

/- TODO: Use Except type from the lean4 standard library. -/
inductive Result (α : Type) (β : Type) where
  | Ok (_ : α)
  | Err (_ : β)
  deriving Repr
export Result(Ok Err)

def Result.map (f: α → β) (r : Result α ε) : Result β ε := match r with
| Result.Ok v => Result.Ok (f v)
| Result.Err e => Result.Err e

end Sail
