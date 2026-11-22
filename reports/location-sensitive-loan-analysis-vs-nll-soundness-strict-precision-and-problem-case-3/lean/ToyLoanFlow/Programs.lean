import ToyLoanFlow.Analyses

/-!
# Concrete programs

Locals are written `x`, `y` (plain data), `r`, `s`, `c` (references to data) and `pp`
(a reference to a reference), each program fixing its own numbering in its doc comment.
-/

namespace Toy.LoanFlow

/-- Problem case #3 (conditional return of a loan, otherwise a fresh mutable loan of the same
place), as in a get-or-insert on a map. Locals: `0 = x` (data; stands for `*map`),
`1 = r : &mut D`, `2 = s : &mut D`.

    0: r := &mut x        -> 1
    1: (branch)           -> 2, 3
    2: return r
    3: write x            -> 4      (the insertion)
    4: s := &mut x        -> 5
    5: return s
-/
def pc3 : Prog 6 3 where
  entry := 0
  succ := fun q => match q.val with
    | 0 => [1] | 1 => [2, 3] | 3 => [4] | 4 => [5] | _ => []
  stmt := fun q => match q.val with
    | 0 => .borrow .mut 1 0
    | 2 => .ret 1
    | 3 => .access .wr 0
    | 4 => .borrow .mut 2 0
    | 5 => .ret 2
    | _ => .nop
  ty := fun v => match v.val with
    | 0 => [] | _ => [.mut]

/-- Loop variant of problem case #3: a mutable borrow of the plain-data local `x` (standing for
`*map`), taken inside a loop, is returned conditionally; otherwise `x` is written and the loop
repeats. Each iteration borrows `x` directly; there is no reference through which a reborrow
could be taken. Locals: `0 = x` (data), `1 = r : &mut D`.

    0: r := &mut x        -> 1
    1: (branch)           -> 2, 3
    2: return r
    3: write x            -> 0
-/
def pc3Loop : Prog 4 2 where
  entry := 0
  succ := fun q => match q.val with
    | 0 => [1] | 1 => [2, 3] | 3 => [0] | _ => []
  stmt := fun q => match q.val with
    | 0 => .borrow .mut 1 0
    | 2 => .ret 1
    | 3 => .access .wr 0
    | _ => .nop
  ty := fun v => match v.val with
    | 0 => [] | _ => [.mut]

/-- Reassignment of the reference that holds a loan. Locals: `0 = x`, `1 = y` (data),
`2 = r : &mut D`.

    0: r := &mut x        -> 1
    1: write *r           -> 2
    2: r := &mut y        -> 3
    3: write x            -> 4
    4: write *r
-/
def pReassign : Prog 5 3 where
  entry := 0
  succ := fun q => match q.val with
    | 0 => [1] | 1 => [2] | 2 => [3] | 3 => [4] | _ => []
  stmt := fun q => match q.val with
    | 0 => .borrow .mut 2 0
    | 1 => .deref .wr 2
    | 2 => .borrow .mut 2 1
    | 3 => .access .wr 0
    | _ => .deref .wr 2
  ty := fun v => match v.val with
    | 2 => [.mut] | _ => []

/-- A copy of a mutable reference followed by a write to the place and a use of the original.
Locals: `0 = x` (data), `1 = r : &mut D`, `2 = s : &mut D`.

    0: r := &mut x        -> 1
    1: s := r             -> 2
    2: write x            -> 3
    3: write *r
-/
def pCopyThenUse : Prog 4 3 where
  entry := 0
  succ := fun q => match q.val with
    | 0 => [1] | 1 => [2] | 2 => [3] | _ => []
  stmt := fun q => match q.val with
    | 0 => .borrow .mut 1 0
    | 1 => .copy 2 1
    | 2 => .access .wr 0
    | _ => .deref .wr 1
  ty := fun v => match v.val with
    | 0 => [] | _ => [.mut]

/-- A shorter loan written through `&mut &D` into a longer-lived reference. Locals:
`0 = x`, `1 = y` (data), `2 = c : &D`, `3 = pp : &mut &D`, `4 = s : &D`.

    0: c := &x            -> 1
    1: pp := &mut c       -> 2
    2: s := &y            -> 3
    3: *pp := s           -> 4
    4: write y            -> 5
    5: read *c
-/
def pVariance : Prog 6 5 where
  entry := 0
  succ := fun q => match q.val with
    | 0 => [1] | 1 => [2] | 2 => [3] | 3 => [4] | 4 => [5] | _ => []
  stmt := fun q => match q.val with
    | 0 => .borrow .shr 2 0
    | 1 => .borrow .mut 3 2
    | 2 => .borrow .shr 4 1
    | 3 => .store 3 4
    | 4 => .access .wr 1
    | _ => .deref .rd 2
  ty := fun v => match v.val with
    | 2 => [.shr] | 3 => [.mut, .shr] | 4 => [.shr] | _ => []

/-- An ill-typed program: the loan is received by a local declared as plain data, which has no
origin. Locals: `0 = x` (data), `1 = r` (declared data).

    0: r := &mut x        -> 1
    1: write x            -> 2
    2: write *r
-/
def pUntypedHolder : Prog 3 2 where
  entry := 0
  succ := fun q => match q.val with
    | 0 => [1] | 1 => [2] | _ => []
  stmt := fun q => match q.val with
    | 0 => .borrow .mut 1 0
    | 1 => .access .wr 0
    | _ => .deref .wr 1
  ty := fun _ => []

/-- An ill-typed program: a reference is stored, through a `&mut` to a local declared as plain
data, into that local, which is then dereferenced. Locals: `0 = y` (data), `1 = c` (declared
data), `2 = pp : &mut D`, `3 = s : &D`.

    0: s := &y            -> 1
    1: pp := &mut c       -> 2
    2: *pp := s           -> 3
    3: write y            -> 4
    4: read *c
-/
def pUntypedStore : Prog 5 4 where
  entry := 0
  succ := fun q => match q.val with
    | 0 => [1] | 1 => [2] | 2 => [3] | 3 => [4] | _ => []
  stmt := fun q => match q.val with
    | 0 => .borrow .shr 3 0
    | 1 => .borrow .mut 2 1
    | 2 => .store 2 3
    | 3 => .access .wr 0
    | _ => .deref .rd 1
  ty := fun v => match v.val with
    | 2 => [.mut] | 3 => [.shr] | _ => []

/-- Problem case #3 without the return: the first loan is used at node `2` instead of being
returned. Locals: `0 = x` (data), `1 = r : &mut D`, `2 = s : &mut D`.

    0: r := &mut x        -> 1
    1: (branch)           -> 2, 3
    2: read *r
    3: write x            -> 4
    4: s := &mut x        -> 5
    5: read *s
-/
def pc3NoReturn : Prog 6 3 where
  entry := 0
  succ := fun q => match q.val with
    | 0 => [1] | 1 => [2, 3] | 3 => [4] | 4 => [5] | _ => []
  stmt := fun q => match q.val with
    | 0 => .borrow .mut 1 0
    | 2 => .deref .rd 1
    | 3 => .access .wr 0
    | 4 => .borrow .mut 2 0
    | 5 => .deref .rd 2
    | _ => .nop
  ty := fun v => match v.val with
    | 0 => [] | _ => [.mut]

/-- The shared-reference counterpart of `pCopyThenUse`. Locals: `0 = x` (data),
`1 = r : &D`, `2 = s : &D`.

    0: r := &x            -> 1
    1: s := r             -> 2
    2: write x            -> 3
    3: read *r
-/
def pCopyThenUseShr : Prog 4 3 where
  entry := 0
  succ := fun q => match q.val with
    | 0 => [1] | 1 => [2] | 2 => [3] | _ => []
  stmt := fun q => match q.val with
    | 0 => .borrow .shr 1 0
    | 1 => .copy 2 1
    | 2 => .access .wr 0
    | _ => .deref .rd 1
  ty := fun v => match v.val with
    | 0 => [] | _ => [.shr]

/-- A safe program that stores through `&mut &D`, so that the generated constraints are not
empty. Locals: `0 = x`, `1 = y` (data), `2 = c : &D`, `3 = pp : &mut &D`, `4 = s : &D`.

    0: c := &x            -> 1
    1: pp := &mut c       -> 2
    2: s := &y            -> 3
    3: *pp := s           -> 4
    4: read *c            -> 5
    5: write y
-/
def pStoreSafe : Prog 6 5 where
  entry := 0
  succ := fun q => match q.val with
    | 0 => [1] | 1 => [2] | 2 => [3] | 3 => [4] | 4 => [5] | _ => []
  stmt := fun q => match q.val with
    | 0 => .borrow .shr 2 0
    | 1 => .borrow .mut 3 2
    | 2 => .borrow .shr 4 1
    | 3 => .store 3 4
    | 4 => .deref .rd 2
    | _ => .access .wr 1
  ty := fun v => match v.val with
    | 2 => [.shr] | 3 => [.mut, .shr] | 4 => [.shr] | _ => []

/-- `pUntypedHolder` placed in nodes `1`–`3`, unreachable from the entry node `0` (a `nop` with
no successor). Locals: `0 = x` (data), `1 = r` (declared data).

    0: (nop)
    1: r := &mut x        -> 2
    2: write x            -> 3
    3: write *r
-/
def pUnreachUntyped : Prog 4 2 where
  entry := 0
  succ := fun q => match q.val with
    | 1 => [2] | 2 => [3] | _ => []
  stmt := fun q => match q.val with
    | 1 => .borrow .mut 1 0
    | 2 => .access .wr 0
    | 3 => .deref .wr 1
    | _ => .nop
  ty := fun _ => []

end Toy.LoanFlow
