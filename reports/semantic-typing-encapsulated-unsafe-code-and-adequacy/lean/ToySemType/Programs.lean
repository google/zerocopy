import ToySemType.Syntax

/-!
# Concrete programs used in examples, witnesses, and counterexamples

Notation in doc comments uses only the package's own constructors:
`ifz c t e` runs `t` when `c` is `0` and `e` otherwise, so
`ifz (lt n size) t e` runs `t` when `n < size` is false and `e` when it is true.
-/

namespace Toy.SemType

open Expr

/-- The encapsulated library: a *bounds-checked raw read*
`λ n. ifz (lt n size) 0 (read (cast n))`, i.e. "if `n < size` then
`read (cast n)` else `0`" (note the branch order of `ifz`).
It uses the unsafe primitive `cast`, guarded by a dynamic check that the
address is allocated. It reads the global heap at address `n`: it takes no
container argument (a global `peek`, not a container-scoped `get`). -/
def checkedRead : Expr :=
  .lam (.ifz (.lt (.var 0) .size) (.num 0) (.read (.cast (.var 0))))

/-- The body of `checkedRead` instantiated at the argument `num n`. -/
def checkedBody (n : Nat) : Expr :=
  .ifz (.lt (.num n) .size) (.num 0) (.read (.cast (.num n)))

/-- The same library without the guard: `λ n. read (cast n)`. -/
def uncheckedRead : Expr := .lam (.read (.cast (.var 0)))

/-- An unsafe closed use of the primitive: `read (cast 7)`. -/
def forgedRead : Expr := .read (.cast (.num 7))

/-- Safe dereference `λ r. read r`. -/
def derefArg : Expr := .lam (.read (.var 0))

/-- `λ _. cast 7`: returns a forged reference. -/
def castSeven : Expr := .lam (.cast (.num 7))

/-- Inner continuation of `probeCellZero` (closed, ignores its argument):
`λ _. ifz (read (cast 0)) (read (cast 99)) 0`, i.e. "if cell 0 holds `0`
then `read (cast 99)` else `0`". -/
def probeBody : Expr :=
  .lam (.ifz (.read (.cast (.num 0))) (.read (.cast (.num 99))) (.num 0))

/-- `λ r. probeBody (write r 1)`: writes `1` through `r`, then reads address 0
through a forged reference and performs an unsafe read of address 99 if that
cell holds `0`. It is safe whenever `r = loc 0` (in any heap), but not for
other references when cell 0 holds `0`. -/
def probeCellZero : Expr := .lam (.app probeBody (.write (.var 0) (.num 1)))

/-- A closed non-value library that inspects the heap size:
`ifz (lt size 2) (λ _. 0) probeCellZero`, i.e. "if `size < 2` then
`probeCellZero` else `λ _. 0`". -/
def sizeGuardedProbe : Expr :=
  .ifz (.lt .size (.num 2)) (.lam (.num 0)) probeCellZero

/-- Client (free variable `0` is the library): `x 7`. -/
def callWith7 : Expr := .app (.var 0) (.num 7)

/-- Client: `read (f 0)`. -/
def readResultOf0 : Expr := .read (.app (.var 0) (.num 0))

/-- Client: `f (alloc 0)`: allocates a fresh cell and passes it to the library. -/
def callOnFreshCell : Expr := .app (.var 0) (.alloc (.num 0))

/-- Ill-typed client: `read (cast x)`. -/
def readCastVar : Expr := .read (.cast (.var 0))

/-- Ill-typed client: `read (cast (f 0))`: uses the library's result as an address. -/
def castResultClient : Expr := .read (.cast (.app (.var 0) (.num 0)))

/-- Client that is not syntactically typable but uses the library only through
`checkedRead`: `checkedRead (f 0)`. -/
def checkedClient : Expr := .app checkedRead (.app (.var 0) (.num 0))

/-- A well-typed closed program: `(λ r. read r) (alloc 5)`. -/
def allocThenRead : Expr := .app derefArg (.alloc (.num 5))

/-- A well-typed closed program returning a closure that captures a fresh
reference: `(λ r. λ _. read r) (alloc 5)`. -/
def captureRef : Expr := .app (.lam (.lam (.read (.var 1)))) (.alloc (.num 5))

/-- The runtime closure produced by `captureRef` from the empty heap:
`λ _. read (loc 0)`. -/
def capturedClosure : Expr := .lam (.read (.loc 0))

/-- A stateful library whose safety rests on an invariant about a stored cell:
`(λ c. λ n. ifz (lt n (read c)) 0 (read (cast n))) (alloc 0)`. It allocates a
private cell holding the bound `0` and guards the raw read with that stored
bound instead of with `size`. -/
def cellBoundRead : Expr :=
  .app (.lam (.lam (.ifz (.lt (.var 0) (.read (.var 1))) (.num 0) (.read (.cast (.var 0))))))
    (.alloc (.num 0))

/-- A closed expression that is safe from the empty heap but not from larger
heaps: `ifz size 0 (read (cast 99))`. -/
def sizeZeroOrForged : Expr := .ifz .size (.num 0) (.read (.cast (.num 99)))

/-- An `int`-typed argument that allocates a cell before returning `0`:
`(λ _. 0) (alloc 0)`. -/
def zeroAfterAlloc : Expr := .app (.lam (.num 0)) (.alloc (.num 0))

/-- The diverging term `(λ x. x x) (λ x. x x)` (closed, `cast`-free, untypable). -/
def omegaExpr : Expr :=
  .app (.lam (.app (.var 0) (.var 0))) (.lam (.app (.var 0) (.var 0)))

end Toy.SemType
