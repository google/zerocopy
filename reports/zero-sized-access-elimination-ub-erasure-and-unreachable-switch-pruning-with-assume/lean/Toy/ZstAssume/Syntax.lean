/-!
# Syntax of the toy CFG language

A small control-flow-graph language over integer locals and a byte-granular memory
map. It is a toy: it is meant to capture the *undefined-behaviour (UB) footprint* of
memory accesses, `assume` statements and `Unreachable` terminators, which is what the
results of this package are about. Loaded values are discarded and stored values are
not modelled; the memory component is a map recording which byte addresses are
dereferenceable.

Nothing here mirrors a production definition. Model–system relation: none proved.
-/

namespace Toy.ZstAssume

/-- Names of integer locals. -/
abbrev Var := Nat

/-- Basic-block labels (indices into the block list of a program). -/
abbrev Label := Nat

/-- The layout of an accessed type: its size in bytes and its alignment. The intended
well-formedness convention is `1 ≤ align`; it is not enforced. With `align = 0` the
`Int` remainder gives `p % 0 = p`, so exactly the address `0` counts as aligned. -/
structure Ty where
  size : Nat
  align : Nat
deriving DecidableEq, Repr

/-- `aligned a p`: the address `p` is a multiple of `a`, computed with the `Int`
remainder (`p % a = 0`). Degenerate edge: for `a = 0` exactly the address `p = 0` is aligned. -/
def aligned (a : Nat) (p : Int) : Bool := p % (a : Int) == 0

/-- The precondition `pre₀ p` that a contract imposes on a pointer `p` used for an
access of size zero (or a copy of zero bytes). The type has exactly three constructors:
* `anyPtr` — `pre₀ p = True` (every pointer, including null);
* `aligned` — `pre₀ p = aligned p`;
* `nonnullAligned` — `pre₀ p = (p ≠ 0 ∧ aligned p)`; the address `0` models null.

A fourth shape, "non-null but no alignment requirement", is not a constructor; it
coincides with `nonnullAligned` at alignment `1` only. Within this type,
`K ≠ .nonnullAligned` means "the contract permits null". -/
inductive ZContract where
  | anyPtr
  | aligned
  | nonnullAligned
deriving DecidableEq, Repr

/-- Evaluation of the zero-size precondition `pre₀` of contract `K` at alignment `a`
and address `p`. -/
def ZContract.holds : ZContract → Nat → Int → Bool
  | .anyPtr, _, _ => true
  | .aligned, a, p => Toy.ZstAssume.aligned a p
  | .nonnullAligned, a, p => p != 0 && Toy.ZstAssume.aligned a p

/-- Machine state: integer locals and a byte-granular dereferenceability map
(`deref p = true` means the byte at address `p` may be accessed). -/
structure State where
  locals : Var → Int
  deref : Int → Bool

/-- Update one local. -/
def State.set (s : State) (x : Var) (v : Int) : State :=
  { s with locals := fun y => if y = x then v else s.locals y }

/-- Integer expressions over locals. -/
inductive Expr where
  | const (v : Int)
  | var (x : Var)
  | add (a b : Expr)
deriving DecidableEq, Repr

/-- Expression evaluation (unbounded `Int` arithmetic, no wrapping). -/
def Expr.eval (s : State) : Expr → Int
  | .const v => v
  | .var x => s.locals x
  | .add a b => a.eval s + b.eval s

/-- Conditions usable in `assume`. -/
inductive Cond where
  | eq (x : Var) (v : Int)
  | ne (x : Var) (v : Int)
deriving DecidableEq, Repr

/-- Condition evaluation. -/
def Cond.eval (s : State) : Cond → Bool
  | .eq x v => s.locals x == v
  | .ne x v => s.locals x != v

/-- Statements.
* `emit e` — appends the value of `e` to the trace (no other statement is observable);
* `assume c` — UB if `c` is false, otherwise a no-op. This is the UB-on-false
  compiler assumption (in the style of an `assume` intrinsic of a compiler IR). In
  weakest-precondition calculi it behaves like an aborting `assert c`
  (`wp = c ∧ Q`), not like a miraculous verification-condition `assume c`
  (`wp = c → Q`);
* `assign x e` — `x := e`;
* `read p τ` / `write p τ` — an access of `τ.size` bytes at address `p` with alignment
  `τ.align` (the value is not modelled, so the two have the same semantics; no
  value-validity requirement exists, so uninhabited types are not represented);
* `copy src dst τ n` — a copy of `n` elements of type `τ`, i.e. `τ.size * n` bytes.
  The count `n` is a literal natural number, not a run-time expression; overlap of the
  two regions is not checked. -/
inductive Stmt where
  | emit (e : Expr)
  | assume (c : Cond)
  | assign (x : Var) (e : Expr)
  | read (p : Expr) (τ : Ty)
  | write (p : Expr) (τ : Ty)
  | copy (src dst : Expr) (τ : Ty) (n : Nat)
deriving DecidableEq, Repr

/-- Block terminators. `switch x arms ow` jumps to the label of the *first* arm whose
value equals `x`, or to `ow` if there is none. `unreachable` is UB when reached. -/
inductive Term where
  | goto (b : Label)
  | switch (x : Var) (arms : List (Int × Label)) (ow : Label)
  | unreachable
  | halt
deriving DecidableEq, Repr

/-- A basic block. -/
structure Block where
  stmts : List Stmt
  term : Term
deriving DecidableEq, Repr

/-- The block with no statements and an `unreachable` terminator. -/
def Block.unreach : Block := ⟨[], .unreachable⟩

/-- A program is a list of blocks; label `l` names the `l`-th block and execution
starts at label `0`. -/
abbrev Prog := List Block

/-- The block at label `l`. Degenerate edge: a label outside the list denotes
`Block.unreach`, so jumping there is UB. -/
def Prog.blk (P : Prog) (l : Label) : Block := P.getD l Block.unreach

/-- All of the `k` bytes `p, p+1, …, p+k-1` are dereferenceable. -/
def bytesDeref (d : Int → Bool) (p : Int) : Nat → Bool
  | 0 => true
  | k + 1 => d (p + k) && bytesDeref d p k

/-- The UB precondition of an access of `bytes` bytes at address `p` with alignment
`a`. Zero-byte accesses are governed by the zero-size contract `K`; accesses of at
least one byte by the fixed nonzero-size contract: non-null, aligned and every byte
dereferenceable. -/
def accessOK (K : ZContract) (d : Int → Bool) (a : Nat) (p : Int) (bytes : Nat) : Bool :=
  if bytes = 0 then K.holds a p else p != 0 && aligned a p && bytesDeref d p bytes

/-- The UB precondition of a statement in a state: `false` exactly when executing it
is UB. `emit` and `assign` never are. -/
def Stmt.pre (K : ZContract) (s : State) : Stmt → Bool
  | .emit _ => true
  | .assign _ _ => true
  | .assume c => c.eval s
  | .read p τ => accessOK K s.deref τ.align (p.eval s) τ.size
  | .write p τ => accessOK K s.deref τ.align (p.eval s) τ.size
  | .copy src dst τ n =>
      accessOK K s.deref τ.align (src.eval s) (τ.size * n) &&
        accessOK K s.deref τ.align (dst.eval s) (τ.size * n)

/-- `IsZeroSizeAccess s`: `s` is a `read` or `write` of a type of size `0`, or a `copy`
of `τ.size * n = 0` bytes (a zero-sized element type or a zero count). -/
def IsZeroSizeAccess : Stmt → Prop
  | .read _ τ => τ.size = 0
  | .write _ τ => τ.size = 0
  | .copy _ _ τ n => τ.size * n = 0
  | _ => False

instance : DecidablePred IsZeroSizeAccess := fun s => by
  cases s <;> unfold IsZeroSizeAccess <;> infer_instance

/-- The zero-size precondition `pre₀` of an access statement: the contract check on
its pointer (both pointers for `copy`). For statements that are not accesses it is
`true`. -/
def Stmt.zeroPre (K : ZContract) (s : State) : Stmt → Bool
  | .read p τ => K.holds τ.align (p.eval s)
  | .write p τ => K.holds τ.align (p.eval s)
  | .copy src dst τ _ => K.holds τ.align (src.eval s) && K.holds τ.align (dst.eval s)
  | _ => true

/-- The accessed type of an access statement. -/
def Stmt.accessTy? : Stmt → Option Ty
  | .read _ τ => some τ
  | .write _ τ => some τ
  | .copy _ _ τ _ => some τ
  | _ => none

end Toy.ZstAssume
