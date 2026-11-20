import ToyProphecy.Prophecy
import ToyProphecy.Discipline

/-!
# Named programs and callees used throughout the package
-/

namespace Toy.Prophecy

open Expr Op Stmt

/-- A store with every local equal to `0`. -/
def zeroStore : Store := fun _ => 0

/-- The store with local `x` holding `x` (as an integer). -/
def idStore : Store := fun x => (x : Int)

/-- `r0 = &mut x0; *r0 = 5; end r0; x1 = x0` -/
def writeThenRead : Prog :=
  [op (borrow 0 0), op (write 0 (lit 5)), op (endBorrow 0), op (assign 1 (var 0))]

/-- Nested reborrows: `r0 = &mut x0; r1 = &mut *r0; *r1 = *r1 + 1; r2 = &mut *r1;
*r2 = *r2 + 10; end r2; end r1; *r0 = *r0 + 100; end r0`. -/
def nestedReborrows : Prog :=
  [op (borrow 0 0), op (reborrow 1 0), op (write 1 (add (deref 1) (lit 1))),
   op (reborrow 2 1), op (write 2 (add (deref 2) (lit 10))), op (endBorrow 2),
   op (endBorrow 1), op (write 0 (add (deref 0) (lit 100))), op (endBorrow 0)]

/-- Callee `fn inc(p: &mut i32) -> &mut i32 { *p = *p + 1; p }`. -/
def incCallee : Callee := { body := [write 0 (add (deref 0) (lit 1))], ret := 0 }

/-- Callee `fn deep(p: &mut i32) -> &mut i32 { let q = &mut *p; *q = *q + 2; end q;
*p = *p + 3; let s = &mut *p; let t = &mut *s; t }` (returns a reborrow two levels
below the parameter). -/
def deepCallee : Callee :=
  { body := [reborrow 1 0, write 1 (add (deref 1) (lit 2)), endBorrow 1,
             write 0 (add (deref 0) (lit 3)), reborrow 2 0, reborrow 3 2], ret := 3 }

/-- A caller of `deepCallee`: `r0 = &mut x0; r1 = deep(&mut *r0); *r1 = *r1 + 10;
end r1; x1 = *r0; end r0`. -/
def callDeep : Prog :=
  [op (borrow 0 0), call 1 deepCallee 0, op (write 1 (add (deref 1) (lit 10))),
   op (endBorrow 1), op (assign 1 (deref 0)), op (endBorrow 0)]

/-- The run-time selection example: `r0 = if x2 ≠ 0 { &mut x0 } else { &mut x1 };
*r0 = *r0 + 1; end r0`. -/
def selIncr : Prog :=
  [op (borrowSel 0 (var 2) 0 1), op (write 0 (add (deref 0) (lit 1))), op (endBorrow 0)]

end Toy.Prophecy
