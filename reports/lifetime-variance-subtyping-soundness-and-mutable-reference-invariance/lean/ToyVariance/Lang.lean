import ToyVariance.Basic

/-!
# A small imperative fragment: syntax, operational semantics, type checker, soundness

Values live in local variables and in a heap of region-tagged locations. Reading or writing a
location whose region is dead is the dangling-access stuck state.
-/

namespace Toy.Variance

/-- Statements. Variables are numbered. Inside a function body, variable `0` is the argument,
variable `1` the captured value, and the result is read from variable `2` at the end. -/
inductive Stmt where
  /-- `x := n` -/
  | nat (x n : Nat)
  /-- `x := ()` -/
  | unit (x : Nat)
  /-- `x := y`, ascribed type `T` (the only place subtyping is used). -/
  | copy (x y : Nat) (T : Ty)
  /-- `x := &'l mut <new location in region l holding y>`. -/
  | alloc (x : Nat) (l : Lft) (y : Nat)
  /-- `x := &*y` (shared reborrow of a mutable reference; same location). -/
  | share (x y : Nat)
  /-- `x := &'l <new Cell in region l holding y>`. -/
  | newCell (x : Nat) (l : Lft) (y : Nat)
  /-- `x := *y` -/
  | read (x y : Nat)
  /-- `*y := z` -/
  | write (y z : Nat)
  /-- `x := c.get()` -/
  | cellGet (x c : Nat)
  /-- `c.set(z)` -/
  | cellSet (c z : Nat)
  /-- `x := (y, z)` -/
  | pair (x y z : Nat)
  /-- `x := y.0` -/
  | fst (x y : Nat)
  /-- `x := y.1` -/
  | snd (x y : Nat)
  /-- `x := PhantomData::<T>` -/
  | phantom (x : Nat) (T : Ty)
  /-- `x := <function of type fn(T) -> U capturing c, with the given body>`. -/
  | lam (x : Nat) (T U : Ty) (c : Nat) (body : List Stmt)
  /-- `x := f(y)` -/
  | call (x f y : Nat)
  /-- End region `till n` (advance the clock to `n + 1`). -/
  | endRegion (n : Nat)
  /-- Stop the program safely (a panic/abort). -/
  | abort

/-- Runtime values. A closure carries its body and its captured value. -/
inductive Val where
  | unit
  | nat (n : Nat)
  | ptr (loc : Nat)
  | pair (a b : Val)
  | clo (body : List Stmt) (cap : Val)

/-- Local variables. -/
abbrev Env := Nat → Option Val

def Env.empty : Env := fun _ => none

def Env.set (e : Env) (x : Nat) (v : Val) : Env := fun k => if k = x then some v else e k

/-- The initial frame of a function call. -/
def Env.frame (arg cap : Val) : Env := (Env.empty.set 0 arg).set 1 cap

/-- Global state: the clock and the heap of `(region, contents)` locations. -/
structure St where
  time : Nat
  heap : List (Lft × Val)

def St.init : St := ⟨0, []⟩

/-- Outcomes of running a statement list. -/
inductive Res where
  | done (st : St) (env : Env)
  /-- Safe stop (`abort`). -/
  | halted
  /-- Read or write of a location whose region is dead. -/
  | dangling
  /-- Any other stuck state (unbound variable, wrong shape of value, …). -/
  | wrong
  | outOfFuel

def Res.isDangling : Res → Bool
  | .dangling => true
  | _ => false

/-- Stuck = `dangling` or `wrong`. -/
def Res.isStuck : Res → Bool
  | .dangling => true
  | .wrong => true
  | _ => false

/-- Fuel-bounded big-step execution (every statement and every call costs one unit). -/
def exec : Nat → St → Env → List Stmt → Res
  | 0, _, _, _ => .outOfFuel
  | _ + 1, st, env, [] => .done st env
  | f + 1, st, env, s :: rest =>
    match s with
    | .nat x n => exec f st (env.set x (.nat n)) rest
    | .unit x => exec f st (env.set x .unit) rest
    | .copy x y _ =>
      match env y with
      | some v => exec f st (env.set x v) rest
      | none => .wrong
    | .alloc x l y =>
      match env y with
      | some v =>
        if l.live st.time then
          exec f { st with heap := st.heap ++ [(l, v)] } (env.set x (.ptr st.heap.length)) rest
        else .wrong
      | none => .wrong
    | .share x y =>
      match env y with
      | some v => exec f st (env.set x v) rest
      | none => .wrong
    | .newCell x l y =>
      match env y with
      | some v =>
        if l.live st.time then
          exec f { st with heap := st.heap ++ [(l, v)] } (env.set x (.ptr st.heap.length)) rest
        else .wrong
      | none => .wrong
    | .read x y =>
      match env y with
      | some (.ptr p) =>
        match st.heap[p]? with
        | some (r, v) => if r.live st.time then exec f st (env.set x v) rest else .dangling
        | none => .wrong
      | _ => .wrong
    | .write y z =>
      match env y, env z with
      | some (.ptr p), some v =>
        match st.heap[p]? with
        | some (r, _) =>
          if r.live st.time then exec f { st with heap := st.heap.set p (r, v) } env rest
          else .dangling
        | none => .wrong
      | _, _ => .wrong
    | .cellGet x c =>
      match env c with
      | some (.ptr p) =>
        match st.heap[p]? with
        | some (r, v) => if r.live st.time then exec f st (env.set x v) rest else .dangling
        | none => .wrong
      | _ => .wrong
    | .cellSet c z =>
      match env c, env z with
      | some (.ptr p), some v =>
        match st.heap[p]? with
        | some (r, _) =>
          if r.live st.time then exec f { st with heap := st.heap.set p (r, v) } env rest
          else .dangling
        | none => .wrong
      | _, _ => .wrong
    | .pair x y z =>
      match env y, env z with
      | some a, some b => exec f st (env.set x (.pair a b)) rest
      | _, _ => .wrong
    | .fst x y =>
      match env y with
      | some (.pair a _) => exec f st (env.set x a) rest
      | _ => .wrong
    | .snd x y =>
      match env y with
      | some (.pair _ b) => exec f st (env.set x b) rest
      | _ => .wrong
    | .phantom x _ => exec f st (env.set x .unit) rest
    | .lam x _ _ c body =>
      match env c with
      | some cv => exec f st (env.set x (.clo body cv)) rest
      | none => .wrong
    | .call x g y =>
      match env g, env y with
      | some (.clo body cap), some a =>
        match exec f st (Env.frame a cap) body with
        | .done st' env' =>
          match env' 2 with
          | some r => exec f st' (env.set x r) rest
          | none => .wrong
        | .halted => .halted
        | .dangling => .dangling
        | .wrong => .wrong
        | .outOfFuel => .outOfFuel
      | _, _ => .wrong
    | .endRegion n =>
      if st.time ≤ n then exec f { st with time := n + 1 } env rest else .wrong
    | .abort => .halted

/-! ## Type checker -/

/-- Typing contexts. -/
abbrev Ctx := Nat → Option Ty

def Ctx.empty : Ctx := fun _ => none

def Ctx.set (Γ : Ctx) (x : Nat) (T : Ty) : Ctx := fun k => if k = x then some T else Γ k

/-- The initial context of a function body. -/
def Ctx.frame (T C : Ty) : Ctx := (Ctx.empty.set 0 T).set 1 C

/-- Checking mode: the static clock at top level, or "inside a function body". Inside a body
no lifetime is checked for liveness (a body may be run at any later time; it only touches
regions through its argument and its `'static` capture), regions cannot be ended, and new
locations can only be allocated in `static`. -/
structure Mode where
  time : Nat
  inBody : Bool

/-- Lifetimes usable in the current mode. -/
def Mode.lv (m : Mode) (l : Lft) : Bool := m.inBody || l.live m.time

/-- Look up a variable; its type must only mention usable lifetimes. -/
def Mode.get (m : Mode) (Γ : Ctx) (y : Nat) : Option Ty :=
  match Γ y with
  | some T => if T.liveIn m.lv then some T else none
  | none => none

/-- Fuel-bounded flow-sensitive type checker, parameterised by a Boolean subtyping oracle
`sub` used only by `copy`. Result: `none` = rejected; `some none` = accepted, control does not
reach the end (`abort`); `some (some Γ)` = accepted with final context `Γ`. -/
def chk : Nat → (Ty → Ty → Bool) → Mode → Ctx → List Stmt → Option (Option Ctx)
  | 0, _, _, _, _ => none
  | _ + 1, _, _, Γ, [] => some (some Γ)
  | f + 1, sub, m, Γ, s :: rest =>
    match s with
    | .nat x _ => chk f sub m (Γ.set x .nat) rest
    | .unit x => chk f sub m (Γ.set x .unit) rest
    | .copy x y T =>
      match m.get Γ y with
      | some S =>
        if T.closed && T.liveIn m.lv && sub S T then chk f sub m (Γ.set x T) rest else none
      | none => none
    | .alloc x l y =>
      match m.get Γ y with
      | some T =>
        if m.lv l && (!m.inBody || l == .static) then chk f sub m (Γ.set x (.refMut l T)) rest
        else none
      | none => none
    | .share x y =>
      match m.get Γ y with
      | some (.refMut l T) => chk f sub m (Γ.set x (.ref l T)) rest
      | _ => none
    | .newCell x l y =>
      match m.get Γ y with
      | some T =>
        if m.lv l && (!m.inBody || l == .static) then chk f sub m (Γ.set x (.ref l (.cell T))) rest
        else none
      | none => none
    | .read x y =>
      match m.get Γ y with
      | some (.ref _ T) => chk f sub m (Γ.set x T) rest
      | some (.refMut _ T) => chk f sub m (Γ.set x T) rest
      | _ => none
    | .write y z =>
      match m.get Γ y, m.get Γ z with
      | some (.refMut _ T), some Z => if Z == T then chk f sub m Γ rest else none
      | _, _ => none
    | .cellGet x c =>
      match m.get Γ c with
      | some (.ref _ (.cell T)) => chk f sub m (Γ.set x T) rest
      | _ => none
    | .cellSet c z =>
      match m.get Γ c, m.get Γ z with
      | some (.ref _ (.cell T)), some Z => if Z == T then chk f sub m Γ rest else none
      | _, _ => none
    | .pair x y z =>
      match m.get Γ y, m.get Γ z with
      | some A, some B => chk f sub m (Γ.set x (.prod A B)) rest
      | _, _ => none
    | .fst x y =>
      match m.get Γ y with
      | some (.prod A _) => chk f sub m (Γ.set x A) rest
      | _ => none
    | .snd x y =>
      match m.get Γ y with
      | some (.prod _ B) => chk f sub m (Γ.set x B) rest
      | _ => none
    | .phantom x T =>
      if T.closed && T.liveIn m.lv then chk f sub m (Γ.set x (.phantom T)) rest else none
    | .lam x T U c body =>
      match m.get Γ c with
      | some C =>
        if C.allStatic && T.closed && U.closed && T.liveIn m.lv && U.liveIn m.lv then
          match chk f sub ⟨m.time, true⟩ (Ctx.frame T C) body with
          | some none => chk f sub m (Γ.set x (.fn T U)) rest
          | some (some Γb) => if Γb 2 == some U then chk f sub m (Γ.set x (.fn T U)) rest else none
          | none => none
        else none
      | none => none
    | .call x g y =>
      match m.get Γ g, m.get Γ y with
      | some (.fn T U), some A => if A == T then chk f sub m (Γ.set x U) rest else none
      | _, _ => none
    | .endRegion n =>
      if !m.inBody && decide (m.time ≤ n) then chk f sub ⟨n + 1, false⟩ Γ rest else none
    | .abort => some none

/-- A closed top-level program is accepted with oracle `sub` and checker fuel `fuel`. -/
def Checks (sub : Ty → Ty → Bool) (fuel : Nat) (P : List Stmt) : Bool :=
  (chk fuel sub ⟨0, false⟩ Ctx.empty P).isSome

/-- `P` is well typed when `copy` may use the subtyping relation `R`: some Boolean oracle
contained in `R` makes the checker accept `P`. -/
def Typed (R : Ty → Ty → Prop) (P : List Stmt) : Prop :=
  ∃ sub : Ty → Ty → Bool, (∀ S T, sub S T = true → R S T) ∧ ∃ fuel, Checks sub fuel P = true

/-- `P` never reaches a stuck state (dangling access or other), for any fuel. -/
def Safe (P : List Stmt) : Prop :=
  ∀ fuel, (exec fuel St.init Env.empty P).isStuck = false

/-- A subtyping relation is sound when every program typed with it is safe. -/
def Sound (R : Ty → Ty → Prop) : Prop := ∀ P, Typed R P → Safe P

/-- Semantic (contextual) subtyping: adding `S ≤ T` as an extra generator to the subtyping
generated by `rustTable` (so it can be used under every type constructor, in every program)
keeps the type system sound. -/
def SemSub (S T : Ty) : Prop := Sound (SubGen rustTable (fun A B => A = S ∧ B = T))

/-- The relation `R` admits a dangling access: some program typed with `R` reaches the
dangling-access stuck state (`Res.dangling`) for some fuel. This is stronger than `¬ Sound R`,
which is also witnessed by programs that reach `Res.wrong`. -/
def AdmitsDanglingAccess (R : Ty → Ty → Prop) : Prop :=
  ∃ P, Typed R P ∧ ∃ fuel, (exec fuel St.init Env.empty P).isDangling = true

end Toy.Variance
