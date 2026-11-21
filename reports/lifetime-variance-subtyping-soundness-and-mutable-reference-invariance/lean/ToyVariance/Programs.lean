import ToyVariance.Basic
import ToyVariance.Alg
import ToyVariance.Lang

/-!
# Concrete witness programs

The programs in the first sections are the witnesses for the forcedness results: each is
accepted by the checker under a modified table (with `subAlg` as the oracle, which is sound for
the generated relation by `subGen_of_subAlg`), and its execution reaches `Res.dangling` (the
theorems in `Results` state which). The last section holds programs used by the remaining
results; their properties are stated where they are used.
-/

namespace Toy.Variance

/-- A short-lived region, ended by `endRegion 0`. -/
abbrev sh : Lft := .till 0

/-- `&'static nat`. -/
abbrev rs : Ty := .ref .static .nat

/-- `&'sh nat`. -/
abbrev rsh : Ty := .ref sh .nat

/-- Common prelude: variable `2 : &'static nat` (location 0, region `static`) and
variable `5 : &'sh nat` (location 1, region `till 0`); variable `4 : &'sh mut nat`. -/
def prelude : List Stmt :=
  [.nat 0 5, .alloc 1 .static 0, .share 2 1, .nat 3 7, .alloc 4 sh 3, .share 5 4]

/-- Acceptance with the `subAlg` oracle gives typing for the generated relation. -/
theorem typed_of_checks {tbl : Table} {ax : Ty → Ty → Prop} {P : List Stmt} (fuel : Nat)
    (h : Checks (subAlg tbl true) fuel P = true) : Typed (SubGen tbl ax) P :=
  ⟨subAlg tbl true,
    fun S T hs => SubGen.lift (Table.le_refl tbl) (fun _ _ h => h.elim) (subGen_of_subAlg tbl S T true hs),
    fuel, h⟩

/-- A typed program that gets stuck refutes soundness. -/
theorem not_sound_of_stuck {R : Ty → Ty → Prop} {P : List Stmt} (ht : Typed R P) (fuel : Nat)
    (hs : (exec fuel St.init Env.empty P).isStuck = true) : ¬ Sound R := by
  intro hR
  have := hR P ht fuel
  rw [hs] at this
  exact Bool.noConfusion this

theorem isStuck_of_isDangling {r : Res} (h : r.isDangling = true) : r.isStuck = true := by
  cases r <;> simp_all [Res.isDangling, Res.isStuck]

/-! ## `&mut T` covariant in `T` -/

/-- `r : &'static mut &'static nat`; `r2 : &'sh mut &'sh nat := r` (needs covariance of
`&mut` in `T`); `*r2 = s` with `s : &'sh nat`; end `'sh`; read `**r`. -/
def progRefMutCo : List Stmt :=
  prelude ++
  [.alloc 10 .static 2,
   .copy 11 10 (.refMut sh rsh),
   .write 11 5,
   .endRegion 0,
   .read 12 10,
   .read 13 12]

/-- `r : &'static mut &'sh nat` holding `s`; `r2 : &'static mut &'static nat := r` (needs
contravariance of `&mut` in `T`); end `'sh`; read `**r2`. -/
def progRefMutContra : List Stmt :=
  prelude ++
  [.alloc 10 .static 5,
   .copy 11 10 (.refMut .static rs),
   .endRegion 0,
   .read 12 11,
   .read 13 12]

/-! ## `Cell<T>` covariant or contravariant in `T` -/

/-- `c : &'static Cell<&'static nat>`; `c2 : &'static Cell<&'sh nat> := c` (needs covariant
`Cell`); `c2.set(s)`; end `'sh`; read `*c.get()`. -/
def progCellCo : List Stmt :=
  prelude ++
  [.newCell 10 .static 2,
   .copy 11 10 (.ref .static (.cell rsh)),
   .cellSet 11 5,
   .endRegion 0,
   .cellGet 12 10,
   .read 13 12]

/-- `c : &'static Cell<&'sh nat>` holding `s`; `c2 : &'static Cell<&'static nat> := c`
(needs contravariant `Cell`); end `'sh`; read `*c2.get()`. -/
def progCellContra : List Stmt :=
  prelude ++
  [.newCell 10 .static 5,
   .copy 11 10 (.ref .static (.cell rs)),
   .endRegion 0,
   .cellGet 12 11,
   .read 13 12]

/-! ## `fn` covariant in its argument, contravariant in its result -/

/-- `f : fn(&'static nat) -> &'static nat` is the identity; `g : fn(&'sh nat) -> &'static nat
:= f` (needs a covariant argument); `y := g(s)`; end `'sh`; read `*y`. -/
def progFnArgCo : List Stmt :=
  prelude ++
  [.lam 10 rs rs 2 [.copy 2 0 rs],
   .copy 11 10 (.fn rsh rs),
   .call 12 11 5,
   .endRegion 0,
   .read 13 12]

/-- `f : fn(&'sh nat) -> &'sh nat` is the identity; `g : fn(&'sh nat) -> &'static nat := f`
(needs a contravariant result); `y := g(s)`; end `'sh`; read `*y`. -/
def progFnResContra : List Stmt :=
  prelude ++
  [.lam 10 rsh rsh 2 [.copy 2 0 rsh],
   .copy 11 10 (.fn rsh rs),
   .call 12 11 5,
   .endRegion 0,
   .read 13 12]

/-! ## Lifetime positions and covariant data positions made contravariant -/

/-- `&'sh nat ≤ &'static nat` (contravariant lifetime of `&`); end `'sh`; read. -/
def progRefLftContra : List Stmt :=
  prelude ++
  [.copy 10 5 (.ref .static .nat),
   .endRegion 0,
   .read 11 10]

/-- `&'static &'sh nat ≤ &'static &'static nat` (contravariant `&` in `T`). -/
def progRefTyContra : List Stmt :=
  prelude ++
  [.alloc 10 .static 5,
   .share 11 10,
   .copy 12 11 (.ref .static rs),
   .endRegion 0,
   .read 13 12,
   .read 14 13]

/-- `&'sh mut nat ≤ &'static mut nat` (contravariant lifetime of `&mut`). -/
def progRefMutLftContra : List Stmt :=
  prelude ++
  [.copy 10 4 (.refMut .static .nat),
   .endRegion 0,
   .read 11 10]

/-- `(&'sh nat, ()) ≤ (&'static nat, ())` (contravariant left tuple component). -/
def progProdLContra : List Stmt :=
  prelude ++
  [.unit 9,
   .pair 10 5 9,
   .copy 11 10 (.prod rs .unit),
   .endRegion 0,
   .fst 12 11,
   .read 13 12]

/-- `((), &'sh nat) ≤ ((), &'static nat)` (contravariant right tuple component). -/
def progProdRContra : List Stmt :=
  prelude ++
  [.unit 9,
   .pair 10 9 5,
   .copy 11 10 (.prod .unit rs),
   .endRegion 0,
   .snd 12 11,
   .read 13 12]

/-! ## Programs for the remaining results -/

/-- `&'static nat ≤ &'sh nat` used through the extra generator of `SemSub`. -/
def progR1Sem : List Stmt :=
  prelude ++ [.copy 6 2 rsh]

/-- `(&'static nat, ()) ≤ (&'sh nat, ())` through the body rule for `(T, ())`. -/
def progBodyCov : List Stmt :=
  prelude ++ [.unit 9, .pair 10 2 9, .copy 11 10 (.prod rsh .unit)]

/-- `PhantomData<&'sh nat> ≤ PhantomData<&'static nat>`, then end `'sh`. -/
def progPhantomBi : List Stmt :=
  [.phantom 0 rsh, .copy 1 0 (.phantom rs), .endRegion 0]

/-- Like `progRefMutCo`, with the alias at `&'static mut &'sh nat`. -/
def progRefMutCoStatic : List Stmt :=
  prelude ++
  [.alloc 10 .static 2,
   .copy 11 10 (.refMut .static rsh),
   .write 11 5,
   .endRegion 0,
   .read 12 10,
   .read 13 12]

/-- A higher-order witness: a thunk returning a function that stashes its `&'static nat`
argument in a `'static` cell is re-typed as returning a function accepting `&'sh nat`. -/
def progStructFnUnitContra : List Stmt :=
  prelude ++
  [.newCell 10 .static 2,
   .lam 11 rs .unit 10 [.cellSet 1 0, .unit 2],
   .lam 12 .unit (.fn rs .unit) 11 [.copy 2 1 (.fn rs .unit)],
   .copy 13 12 (.fn .unit (.fn rsh .unit)),
   .unit 14,
   .call 15 13 14,
   .call 16 15 5,
   .endRegion 0,
   .cellGet 17 10,
   .read 18 17]

/-- A function expecting `fn(nat) -> ()` re-typed as expecting `fn(&'static nat) -> ()` and
called with a function that reads its argument: the read meets a number (`Res.wrong`). -/
def progFnFnBiWrong : List Stmt :=
  [.unit 0,
   .lam 1 (.fn .nat .unit) .unit 0 [.nat 3 99, .call 4 0 3, .unit 2],
   .copy 2 1 (.fn (.fn rs .unit) .unit),
   .lam 3 rs .unit 0 [.read 4 0, .unit 2],
   .call 4 2 3]

end Toy.Variance
