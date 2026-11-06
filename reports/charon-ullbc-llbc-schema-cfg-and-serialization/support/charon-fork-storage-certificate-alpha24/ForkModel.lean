import Lean
set_option linter.unusedSimpArgs false
namespace CharonFork
abbrev Byte := Fin 256
inductive Value where
 | boolean (b : Bool)
 | byte (b : Byte)
 deriving DecidableEq, Repr
structure State where
 values : Nat → Option Value
 live : Nat → Bool
 events : List String
def setValue (s : State) (n : Nat) (v : Option Value) : State :=
 { s with values := fun i => if i = n then v else s.values i }
def setLive (s : State) (n : Nat) (b : Bool) : State :=
 { s with live := fun i => if i = n then b else s.live i }
def log (s : State) (e : String) : State := { s with events := s.events ++ [e] }
inductive Op where
 | live (n : Nat)
 | dead (n : Nat)
 | copy (dst src : Nat)
 | nop
 deriving DecidableEq, Repr
def execOp (o : Op) (s : State) : Option State :=
 match o with
 | .live n => some (log (setValue (setLive s n true) n none) s!"live:{n}")
 | .dead n => some (log (setValue (setLive s n false) n none) s!"dead:{n}")
 | .copy d n => if s.live n && s.live d then
     match s.values n with
     | some v => some (log (setValue s d (some v)) s!"copy:{n}:{d}")
     | none => none
   else none
 | .nop => some s
def runOps : List Op → State → Option State
 | [], s => some s
 | o :: os, s => (execOp o s).bind (runOps os)
def branchMove (n : Nat) (s : State) : Option (Bool × State) :=
 if s.live n then
  match s.values n with
  | some (.boolean b) => some (b, log (setValue s n none) s!"move-bool:{n}:{b}")
  | _ => none
 else none
def finish (s : State) : Option State :=
 if s.live 0 then
  match s.values 0 with
  | some (.byte _) => some (log s "return:0")
  | _ => none
 else none
inductive Term where
 | branch (condition yes no : Nat)
 | jump (target : Nat)
 | ret
 deriving DecidableEq, Repr
structure Block where
 ops : List Op
 term : Term
 deriving DecidableEq, Repr
def runCFG (blocks : List Block) : Nat → Nat → State → Option State
 | 0, _, _ => none
 | fuel + 1, pc, s => do
   let block ← blocks[pc]?
   let s ← runOps block.ops s
   match block.term with
   | .ret => finish s
   | .jump target => runCFG blocks fuel target s
   | .branch n yes no =>
     let (b, s) ← branchMove n s
     runCFG blocks fuel (if b then yes else no) s
structure Fork where
 pre : List Op
 condition : Nat
 yes : List Op
 no : List Op
 post : List Op
 deriving DecidableEq, Repr
def graph (p : Fork) : List Block :=
 [⟨p.pre, .branch p.condition 1 2⟩,
  ⟨p.yes, .jump 3⟩, ⟨p.no, .jump 3⟩, ⟨p.post, .ret⟩]
def runStructured (p : Fork) (s : State) : Option State := do
 let s ← runOps p.pre s
 let (b, s) ← branchMove p.condition s
 let s ← runOps (if b then p.yes else p.no) s
 let s ← runOps p.post s
 finish s
theorem graph_fork (p : Fork) (fuel : Nat) (s : State) :
 runCFG (graph p) (fuel + 3) 0 s = runStructured p s := by
 simp only [runCFG, graph, List.getElem?_cons_zero, Option.bind_some,
   List.getElem?_cons_succ, Nat.add_assoc]
 unfold runStructured
 cases hp : runOps p.pre s with
 | none => simp [hp]
 | some s' =>
   cases hc : branchMove p.condition s' with
   | none => simp [hp, hc]
   | some pair =>
     rcases pair with ⟨b, s''⟩
     cases b <;> simp [hp, hc, runCFG, graph]
def raw : Fork := ⟨[.live 4, .copy 4 1], 4, [.copy 0 2], [.copy 0 3], [.dead 4]⟩
def built : Fork := { raw with yes := [.copy 0 2, .nop], no := [.copy 0 3, .nop] }
def final : Fork := raw
theorem built_final (s : State) : runStructured built s = runStructured final s := by
 have h (b : Bool) (t : State) :
   runOps (if b then [.copy 0 2, .nop] else [.copy 0 3, .nop]) t =
   runOps (if b then [.copy 0 2] else [.copy 0 3]) t := by
  cases b <;> simp [runOps, execOp]
 simp only [runStructured, built, final, raw, h]
theorem actual_before_after (fuel : Nat) (s : State) :
 runCFG (graph raw) (fuel + 3) 0 s = runStructured final s := graph_fork raw fuel s
theorem actual_before_built (fuel : Nat) (s : State) :
 runCFG (graph raw) (fuel + 3) 0 s = runStructured built s := by
 rw [graph_fork, built_final]; rfl
def entry (b : Bool) (x y : Byte) (oldReturn : Option Value)
 (oldTemp : Option Value) (tempLive : Bool) (frame : Nat → Option Value)
 (frameLive : Nat → Bool) : State :=
 ⟨fun n => if n = 0 then oldReturn else if n = 1 then some (.boolean b)
   else if n = 2 then some (.byte x) else if n = 3 then some (.byte y)
   else if n = 4 then oldTemp else frame n,
  fun n => if n < 4 then true else if n = 4 then tempLive else frameLive n, []⟩
def noDead : Fork := { final with post := [] }
def wrongBranch : Fork := { final with yes := [.copy 0 3] }
def oldBranch : Fork := { final with condition := 1 }
def sample : State := entry true 1 2 none (some (.boolean false)) true (fun _ => none) (fun _ => false)
def observation (o : Option State) : Option (Option Value × Bool × Option Value × List String) :=
 o.map fun s => (s.values 0, s.live 4, s.values 4, s.events)
example : observation (runStructured noDead sample) ≠ observation (runStructured final sample) := by decide
example : observation (runStructured wrongBranch sample) ≠ observation (runStructured final sample) := by decide
example : observation (runStructured oldBranch sample) ≠ observation (runStructured final sample) := by decide
#print axioms graph_fork
#print axioms built_final
#print axioms actual_before_after
#eval observation (runStructured final sample)
#eval observation (runStructured noDead sample)
#eval observation (runStructured wrongBranch sample)
#eval observation (runStructured oldBranch sample)
end CharonFork
