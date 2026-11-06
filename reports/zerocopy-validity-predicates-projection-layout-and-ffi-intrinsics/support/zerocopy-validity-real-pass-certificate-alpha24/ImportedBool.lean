import CapturedProofs
open Aeneas Aeneas.Std Result
set_option linter.unusedSimpArgs false
namespace ImportedBool
inductive Value where
 | byte (x : U8)
 | boolean (b : Bool)
structure State where
 locals : Nat → Option Value
 live : Nat → Bool
 events : List String
inductive Op where
 | storageLive (n : Nat)
 | copy (dst src : Nat)
 | lessMove (dst src : Nat) (literal : U8)
 | storageDead (n : Nat)
def setValue (s : State) (n : Nat) (v : Option Value) : State :=
 {s with locals := fun k => if k = n then v else s.locals k}
def setLive (s : State) (n : Nat) (b : Bool) : State :=
 {s with live := fun k => if k = n then b else s.live k}
def record (s : State) (event : String) := {s with events := s.events ++ [event]}
def exec : Op → State → Option State
 | .storageLive n, s => some (record (setValue (setLive s n true) n none) "live")
 | .storageDead n, s => some (record (setValue (setLive s n false) n none) "dead")
 | .copy dst src, s => if s.live dst && s.live src then do
    let v ← s.locals src
    pure (record (setValue s dst (some v)) "copy")
   else none
 | .lessMove dst src literal, s => if s.live dst && s.live src then do
    match ← s.locals src with
    | .byte x => pure (record (setValue (setValue s src none) dst (some (.boolean (decide (x < literal))))) "lt-move")
    | _ => none
   else none
def run : List Op → State → Option State
 | [], s => some s
 | op::ops, s => (exec op s).bind (run ops)
def rawOps : List Op := [.storageLive 2, .copy 2 1, .lessMove 0 2 (2#u8), .storageDead 2]
def structuredOps : List Op := [.storageLive 2, .copy 2 1, .lessMove 0 2 (2#u8), .storageDead 2]
theorem captured_raw_final (s : State) : run rawOps s = run structuredOps s := rfl
def entry (byte : U8) (oldReturn oldTemp : Option Value) (tempLive : Bool)
 (frame : Nat → Option Value) (frameLive : Nat → Bool) (events : List String) : State :=
 ⟨fun k => if k=0 then oldReturn else if k=1 then some (.byte byte) else if k=2 then oldTemp else frame k,
 fun k => if k<2 then true else if k=2 then tempLive else frameLive k, events⟩
def result (s : State) : Option Bool := do
 if s.live 0 then match ← s.locals 0 with
  | .boolean b => pure b
  | _ => none
 else none
theorem imported_emitted (byte : U8) (oldReturn oldTemp : Option Value) (tempLive : Bool)
 (frame : Nat → Option Value) (frameLive : Nat → Bool) (events : List String) :
 ((run rawOps (entry byte oldReturn oldTemp tempLive frame frameLive events)).bind result).map Result.ok =
 some (zerocopy_probe.util.validity.bool_encoding byte) := by
 simp [run, rawOps, exec, entry, setValue, setLive, record, result, zerocopy_probe.util.validity.bool_encoding]
theorem raw_domain (byte : U8) (oldReturn oldTemp : Option Value) (tempLive : Bool)
 (frame : Nat → Option Value) (frameLive : Nat → Bool) (events : List String) :
 ((run rawOps (entry byte oldReturn oldTemp tempLive frame frameLive events)).bind result).map Result.ok =
 some (ok (decide (byte.val=0 ∨ byte.val=1))) := by
 rw [imported_emitted, ZerocopyCapture.bool_all]
#print axioms captured_raw_final
#print axioms imported_emitted
#print axioms raw_domain
theorem frame_preserved (byte : U8) (oldReturn oldTemp : Option Value) (tempLive : Bool)
 (frame : Nat → Option Value) (frameLive : Nat → Bool) (events : List String)
 (out : State) (h : run rawOps (entry byte oldReturn oldTemp tempLive frame frameLive events) = some out)
 (j : Nat) (h0 : j≠0) (h1 : j≠1) (h2 : j≠2) :
 out.locals j = frame j ∧ out.live j = frameLive j := by
 simp [run, rawOps, exec, entry, setValue, setLive, record] at h
 cases h
 have hnot : ¬ j < 2 := by omega
 simp [setValue, setLive, entry, record, h0, h1, h2, hnot]
 omega
#print axioms frame_preserved
end ImportedBool
