import Toy.StoreLaws.Lemmas

/-!
# Store laws: concrete models

Lawful and "lawful but weird" models of the `get`/`put` signature.  Each model
is meant to capture a recognizable behavior of a real storage device or
instrumented store; the law profiles of the models are proved in
`Toy.StoreLaws.Profiles`.

| model | intended reading |
| :--- | :--- |
| `intended` | an ordinary memory cell (defined in `Defs`) |
| `valueOnly` | an ordinary cell observed only through returned values |
| `unitModel` | the one-point model: nothing is observed |
| `writeLog` | an ordinary cell whose observer also sees a log of every write |
| `changeLog` | an ordinary cell whose observer sees a log of value-changing writes |
| `writesIgnored` | a read-only device: writes are silently dropped |
| `dirtyBit` | a cell with a hidden "modified" flag set by every write |
| `readToClear` | a destructive read: reading resets the cell to `d` |
| `faultingCounter` | a device that counts reads and faults on every write |
| `readCounter` | an ordinary cell whose observer sees how many reads happened |
| `inertHidden` | an ordinary cell next to a hidden component that programs never touch |
| `coupledHidden` | an ordinary cell next to a hidden bit that flips whenever a write changes the cell |
| `fstViaModel` | an artificial model used to test observational satisfaction through `Prod.fst` |
-/

namespace Toy.StoreLaws

/-- An ordinary cell observed only through returned values: the final cell
content is forgotten.  Carrier `S → V`. -/
def valueOnly (S V : Type) : Model S (S → V) where
  get k := fun s => k s s
  put t x := fun _ => x t

/-- Valuation for `valueOnly`: return `v` whatever the cell holds. -/
def valueOnlyRet {S V : Type} (v : V) : S → V := fun _ => v

/-- The one-point model: every program denotes `()`. -/
def unitModel (S : Type) : Model S Unit where
  get _ := ()
  put _ _ := ()

/-- An ordinary cell whose observer also sees the list of all values written,
in program order (`put t` prepends `t` to the log of the rest of the
computation).  Carrier `S → V × S × List S`. -/
def writeLog (S V : Type) : Model S (S → V × S × List S) where
  get k := fun s => k s s
  put t x := fun _ => ((x t).1, (x t).2.1, t :: (x t).2.2)

/-- Valuation for `writeLog` and `changeLog`: return `v`, log nothing. -/
def logRet {S V : Type} (v : V) : S → V × S × List S := fun s => (v, s, [])

/-- The observation of a logging model that forgets the log. -/
def dropLog {S V : Type} (x : S → V × S × List S) : S → V × S :=
  fun s => ((x s).1, (x s).2.1)

/-- An ordinary cell whose observer sees the list of writes that changed the
cell's content (a write of the value already held is not logged). -/
def changeLog (S V : Type) [DecidableEq S] : Model S (S → V × S × List S) where
  get k := fun s => k s s
  put t x := fun s₀ => ((x t).1, (x t).2.1, if t = s₀ then (x t).2.2 else t :: (x t).2.2)

/-- A read-only device: `put` is a no-op. -/
def writesIgnored (S V : Type) : Model S (S → V × S) where
  get k := fun s => k s s
  put _ x := x

/-- A cell with a hidden "modified" flag: every write sets the flag, reads
ignore it.  Carrier `S × Bool → V × (S × Bool)`. -/
def dirtyBit (S V : Type) : Model S (S × Bool → V × (S × Bool)) where
  get k := fun st => k st.1 st
  put t x := fun _ => x (t, true)

/-- Valuation for `dirtyBit` and `inertHidden`: return `v`, leave the state. -/
def pairRet {S H V : Type} (v : V) : S × H → V × (S × H) := fun st => (v, st)

/-- A destructive read: reading returns the cell content and resets the cell
to the default `d`. -/
def readToClear (S V : Type) (d : S) : Model S (S → V × S) where
  get k := fun s => k s d
  put t x := fun _ => x t

/-- A device that counts reads and faults (`none`) on every write.
Carrier `S → Option (V × S × Nat)`. -/
def faultingCounter (S V : Type) : Model S (S → Option (V × S × Nat)) where
  get k := fun s => (k s s).map (fun r => (r.1, r.2.1, r.2.2 + 1))
  put _ _ := fun _ => none

/-- Valuation for `faultingCounter`: return `v`, zero reads. -/
def faultingRet {S V : Type} (v : V) : S → Option (V × S × Nat) := fun s => some (v, s, 0)

/-- An ordinary cell whose observer sees the number of reads performed. -/
def readCounter (S V : Type) : Model S (S → V × S × Nat) where
  get k := fun s => ((k s s).1, (k s s).2.1, (k s s).2.2 + 1)
  put t x := fun _ => x t

/-- Valuation for `readCounter`: return `v`, zero reads. -/
def counterRet {S V : Type} (v : V) : S → V × S × Nat := fun s => (v, s, 0)

/-- An ordinary cell (first component) next to a hidden component `H` that no
operation reads or writes; the observer of the carrier sees both.
Carrier `S × H → V × (S × H)`. -/
def inertHidden (S H V : Type) : Model S (S × H → V × (S × H)) where
  get k := fun st => k st.1 st
  put t x := fun st => x (t, st.2)

/-- A valuation for `inertHidden S Bool V` whose returns flip the hidden bit: it
models leaves that carry a further effect on the hidden component. -/
def pairFlipRet {S V : Type} (v : V) : S × Bool → V × (S × Bool) :=
  fun st => (v, (st.1, !st.2))

/-- An ordinary Boolean cell next to a hidden bit that `put t` flips exactly
when `t` differs from the current cell content (so `cell xor hidden` is
invariant).  Carrier `Bool × Bool → V × (Bool × Bool)`. -/
def coupledHidden (V : Type) : Model Bool (Bool × Bool → V × (Bool × Bool)) where
  get k := fun st => k st.1 st
  put t x := fun st => x (t, xor (xor st.1 t) st.2)

/-- An artificial model on a Boolean cell with carrier `(Bool → Bool) × (Bool → Bool)`,
used with the non-injective observation `Prod.fst` to show that observational
satisfaction (`GetPutVia`, `PutGetVia`) does not inherit the entailments of
strict satisfaction. -/
def fstViaModel : Model Bool ((Bool → Bool) × (Bool → Bool)) where
  get k := (fun s => (k s).2 (!s), fun s => (k s).2 s)
  put t x := (fun _ => x.2 t, fun s => x.1 (!s))

end Toy.StoreLaws
