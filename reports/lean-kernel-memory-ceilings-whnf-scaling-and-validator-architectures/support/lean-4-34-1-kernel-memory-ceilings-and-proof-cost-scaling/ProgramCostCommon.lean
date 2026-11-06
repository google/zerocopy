import AnnealResearch.ProofCostFrames

/-!
Common definitions for the program-specific matched proof-cost pilot.
Fixed protocol: 72558d95d3afe9155c3003e1b113fe9859824306cfc23bfae1051233f974b8f9.

These are literal finite named-stage Plan bodies over the unchanged raw kernel.
Source generation was an authoring aid only: no runtime repetition constructor,
new evaluator, proof suite, success extraction or safety theorem occurs here.
Normal completion is Config.completed; no numeric return is modeled. All roots
start in actual empty memory, with both public Bool inputs in the claim domain.
The parent owns compilation and independent review.
-/
namespace AnnealResearch.ProgramCostCommon

open Execution MemoryExecution MiniRustReference

def zeroByte : Byte := .init 0 none
def oneByte : Byte := .init 1 none
def sevenByte : Byte := .init 7 none
def nineByte : Byte := .init 9 none

def oneBytes : List Byte := [oneByte]
def sevenBytes : List Byte := [sevenByte]
def nineBytes : List Byte := [nineByte]

def signalByte (q : Bool) : Byte := if q then oneByte else zeroByte
def signalBytes (q : Bool) : List Byte := [signalByte q]

/-- All actual allocation records, including any ID beyond next, must be dead. -/
def NoLive (memory : State) : Prop :=
  ∀ id allocation, memory.allocations id = some allocation → allocation.live = false

def initial (body : Bool → Plan) (q : Bool) : Config State :=
  .running MiniRustReference.empty (body q) []

def CompletionNoLive (start : Config State) : Prop :=
  ∀ memory trace, Reach SourceStep start (.completed memory trace) → NoLive memory

/-- The same all-choice finite-prefix and conditional-completion proposition
will be the endpoint of both routes. This is a proposition, not its proof. -/
def Claim (body : Bool → Plan) (q : Bool) : Prop :=
  NoUB SourceStep Bad (initial body q) ∧ CompletionNoLive (initial body q)

/- 8 distinct call sites. Definitions run backwards so each successor
is already declared; execution starts at base8_s001. -/

def base8_s008 (pA : Ptr) : Plan :=
  .call (.free pA .heap 1 1) fun reply =>
    match reply with
    | .unit => .done
    | _ => .done

def base8_s007 (pA : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base8_s008 pA
    | _ => .done

def base8_s006 (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.free pB .heap 1 1) fun reply =>
    match reply with
    | .unit => base8_s007 pA
    | _ => .done

def base8_s005 (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base8_s006 pA pB
    | _ => .done

def base8_s004 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base8_s005 pA pB
    | _ => .done

def base8_s003 (q : Bool) (pA : Ptr) : Plan :=
  .call (.allocate .heap 1 1) fun reply =>
    match reply with
    | .pointer pB => base8_s004 q pA pB
    | _ => .done

def base8_s002 (q : Bool) (pA : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => base8_s003 q pA
    | _ => .done

def base8_s001 (q : Bool) : Plan :=
  .call (.allocate .heap 1 1) fun reply =>
    match reply with
    | .pointer pA => base8_s002 q pA
    | _ => .done

def base8 (q : Bool) : Plan := base8_s001 q

/- 32 distinct call sites. Definitions run backwards so each successor
is already declared; execution starts at base32_s001. -/

def base32_s032 (pA : Ptr) : Plan :=
  .call (.free pA .heap 1 1) fun reply =>
    match reply with
    | .unit => .done
    | _ => .done

def base32_s031 (pA : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base32_s032 pA
    | _ => .done

def base32_s030 (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.free pB .heap 1 1) fun reply =>
    match reply with
    | .unit => base32_s031 pA
    | _ => .done

def base32_s029 (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base32_s030 pA pB
    | _ => .done

def base32_s028 (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base32_s029 pA pB
    | _ => .done

def base32_s027 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base32_s028 pA pB
    | _ => .done

def base32_s026 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (nineBytes) 1) fun reply =>
    match reply with
    | .unit => base32_s027 q pA pB
    | _ => .done

def base32_s025 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base32_s026 q pA pB
    | _ => .done

def base32_s024 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base32_s025 q pA pB
    | _ => .done

def base32_s023 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base32_s024 q pA pB
    | _ => .done

def base32_s022 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => base32_s023 q pA pB
    | _ => .done

def base32_s021 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base32_s022 q pA pB
    | _ => .done

def base32_s020 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base32_s021 q pA pB
    | _ => .done

def base32_s019 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base32_s020 q pA pB
    | _ => .done

def base32_s018 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (nineBytes) 1) fun reply =>
    match reply with
    | .unit => base32_s019 q pA pB
    | _ => .done

def base32_s017 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base32_s018 q pA pB
    | _ => .done

def base32_s016 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base32_s017 q pA pB
    | _ => .done

def base32_s015 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base32_s016 q pA pB
    | _ => .done

def base32_s014 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => base32_s015 q pA pB
    | _ => .done

def base32_s013 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base32_s014 q pA pB
    | _ => .done

def base32_s012 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base32_s013 q pA pB
    | _ => .done

def base32_s011 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base32_s012 q pA pB
    | _ => .done

def base32_s010 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (nineBytes) 1) fun reply =>
    match reply with
    | .unit => base32_s011 q pA pB
    | _ => .done

def base32_s009 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base32_s010 q pA pB
    | _ => .done

def base32_s008 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base32_s009 q pA pB
    | _ => .done

def base32_s007 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base32_s008 q pA pB
    | _ => .done

def base32_s006 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => base32_s007 q pA pB
    | _ => .done

def base32_s005 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base32_s006 q pA pB
    | _ => .done

def base32_s004 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base32_s005 q pA pB
    | _ => .done

def base32_s003 (q : Bool) (pA : Ptr) : Plan :=
  .call (.allocate .heap 1 1) fun reply =>
    match reply with
    | .pointer pB => base32_s004 q pA pB
    | _ => .done

def base32_s002 (q : Bool) (pA : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => base32_s003 q pA
    | _ => .done

def base32_s001 (q : Bool) : Plan :=
  .call (.allocate .heap 1 1) fun reply =>
    match reply with
    | .pointer pA => base32_s002 q pA
    | _ => .done

def base32 (q : Bool) : Plan := base32_s001 q

/- 128 distinct call sites. Definitions run backwards so each successor
is already declared; execution starts at base128_s001. -/

def base128_s128 (pA : Ptr) : Plan :=
  .call (.free pA .heap 1 1) fun reply =>
    match reply with
    | .unit => .done
    | _ => .done

def base128_s127 (pA : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s128 pA
    | _ => .done

def base128_s126 (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.free pB .heap 1 1) fun reply =>
    match reply with
    | .unit => base128_s127 pA
    | _ => .done

def base128_s125 (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s126 pA pB
    | _ => .done

def base128_s124 (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s125 pA pB
    | _ => .done

def base128_s123 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s124 pA pB
    | _ => .done

def base128_s122 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (nineBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s123 q pA pB
    | _ => .done

def base128_s121 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s122 q pA pB
    | _ => .done

def base128_s120 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s121 q pA pB
    | _ => .done

def base128_s119 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s120 q pA pB
    | _ => .done

def base128_s118 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s119 q pA pB
    | _ => .done

def base128_s117 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s118 q pA pB
    | _ => .done

def base128_s116 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s117 q pA pB
    | _ => .done

def base128_s115 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s116 q pA pB
    | _ => .done

def base128_s114 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (nineBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s115 q pA pB
    | _ => .done

def base128_s113 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s114 q pA pB
    | _ => .done

def base128_s112 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s113 q pA pB
    | _ => .done

def base128_s111 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s112 q pA pB
    | _ => .done

def base128_s110 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s111 q pA pB
    | _ => .done

def base128_s109 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s110 q pA pB
    | _ => .done

def base128_s108 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s109 q pA pB
    | _ => .done

def base128_s107 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s108 q pA pB
    | _ => .done

def base128_s106 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (nineBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s107 q pA pB
    | _ => .done

def base128_s105 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s106 q pA pB
    | _ => .done

def base128_s104 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s105 q pA pB
    | _ => .done

def base128_s103 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s104 q pA pB
    | _ => .done

def base128_s102 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s103 q pA pB
    | _ => .done

def base128_s101 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s102 q pA pB
    | _ => .done

def base128_s100 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s101 q pA pB
    | _ => .done

def base128_s099 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s100 q pA pB
    | _ => .done

def base128_s098 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (nineBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s099 q pA pB
    | _ => .done

def base128_s097 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s098 q pA pB
    | _ => .done

def base128_s096 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s097 q pA pB
    | _ => .done

def base128_s095 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s096 q pA pB
    | _ => .done

def base128_s094 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s095 q pA pB
    | _ => .done

def base128_s093 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s094 q pA pB
    | _ => .done

def base128_s092 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s093 q pA pB
    | _ => .done

def base128_s091 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s092 q pA pB
    | _ => .done

def base128_s090 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (nineBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s091 q pA pB
    | _ => .done

def base128_s089 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s090 q pA pB
    | _ => .done

def base128_s088 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s089 q pA pB
    | _ => .done

def base128_s087 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s088 q pA pB
    | _ => .done

def base128_s086 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s087 q pA pB
    | _ => .done

def base128_s085 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s086 q pA pB
    | _ => .done

def base128_s084 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s085 q pA pB
    | _ => .done

def base128_s083 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s084 q pA pB
    | _ => .done

def base128_s082 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (nineBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s083 q pA pB
    | _ => .done

def base128_s081 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s082 q pA pB
    | _ => .done

def base128_s080 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s081 q pA pB
    | _ => .done

def base128_s079 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s080 q pA pB
    | _ => .done

def base128_s078 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s079 q pA pB
    | _ => .done

def base128_s077 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s078 q pA pB
    | _ => .done

def base128_s076 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s077 q pA pB
    | _ => .done

def base128_s075 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s076 q pA pB
    | _ => .done

def base128_s074 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (nineBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s075 q pA pB
    | _ => .done

def base128_s073 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s074 q pA pB
    | _ => .done

def base128_s072 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s073 q pA pB
    | _ => .done

def base128_s071 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s072 q pA pB
    | _ => .done

def base128_s070 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s071 q pA pB
    | _ => .done

def base128_s069 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s070 q pA pB
    | _ => .done

def base128_s068 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s069 q pA pB
    | _ => .done

def base128_s067 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s068 q pA pB
    | _ => .done

def base128_s066 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (nineBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s067 q pA pB
    | _ => .done

def base128_s065 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s066 q pA pB
    | _ => .done

def base128_s064 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s065 q pA pB
    | _ => .done

def base128_s063 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s064 q pA pB
    | _ => .done

def base128_s062 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s063 q pA pB
    | _ => .done

def base128_s061 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s062 q pA pB
    | _ => .done

def base128_s060 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s061 q pA pB
    | _ => .done

def base128_s059 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s060 q pA pB
    | _ => .done

def base128_s058 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (nineBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s059 q pA pB
    | _ => .done

def base128_s057 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s058 q pA pB
    | _ => .done

def base128_s056 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s057 q pA pB
    | _ => .done

def base128_s055 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s056 q pA pB
    | _ => .done

def base128_s054 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s055 q pA pB
    | _ => .done

def base128_s053 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s054 q pA pB
    | _ => .done

def base128_s052 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s053 q pA pB
    | _ => .done

def base128_s051 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s052 q pA pB
    | _ => .done

def base128_s050 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (nineBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s051 q pA pB
    | _ => .done

def base128_s049 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s050 q pA pB
    | _ => .done

def base128_s048 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s049 q pA pB
    | _ => .done

def base128_s047 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s048 q pA pB
    | _ => .done

def base128_s046 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s047 q pA pB
    | _ => .done

def base128_s045 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s046 q pA pB
    | _ => .done

def base128_s044 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s045 q pA pB
    | _ => .done

def base128_s043 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s044 q pA pB
    | _ => .done

def base128_s042 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (nineBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s043 q pA pB
    | _ => .done

def base128_s041 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s042 q pA pB
    | _ => .done

def base128_s040 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s041 q pA pB
    | _ => .done

def base128_s039 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s040 q pA pB
    | _ => .done

def base128_s038 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s039 q pA pB
    | _ => .done

def base128_s037 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s038 q pA pB
    | _ => .done

def base128_s036 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s037 q pA pB
    | _ => .done

def base128_s035 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s036 q pA pB
    | _ => .done

def base128_s034 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (nineBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s035 q pA pB
    | _ => .done

def base128_s033 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s034 q pA pB
    | _ => .done

def base128_s032 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s033 q pA pB
    | _ => .done

def base128_s031 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s032 q pA pB
    | _ => .done

def base128_s030 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s031 q pA pB
    | _ => .done

def base128_s029 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s030 q pA pB
    | _ => .done

def base128_s028 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s029 q pA pB
    | _ => .done

def base128_s027 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s028 q pA pB
    | _ => .done

def base128_s026 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (nineBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s027 q pA pB
    | _ => .done

def base128_s025 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s026 q pA pB
    | _ => .done

def base128_s024 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s025 q pA pB
    | _ => .done

def base128_s023 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s024 q pA pB
    | _ => .done

def base128_s022 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s023 q pA pB
    | _ => .done

def base128_s021 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s022 q pA pB
    | _ => .done

def base128_s020 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s021 q pA pB
    | _ => .done

def base128_s019 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s020 q pA pB
    | _ => .done

def base128_s018 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (nineBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s019 q pA pB
    | _ => .done

def base128_s017 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s018 q pA pB
    | _ => .done

def base128_s016 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s017 q pA pB
    | _ => .done

def base128_s015 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s016 q pA pB
    | _ => .done

def base128_s014 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s015 q pA pB
    | _ => .done

def base128_s013 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s014 q pA pB
    | _ => .done

def base128_s012 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s013 q pA pB
    | _ => .done

def base128_s011 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s012 q pA pB
    | _ => .done

def base128_s010 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (nineBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s011 q pA pB
    | _ => .done

def base128_s009 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s010 q pA pB
    | _ => .done

def base128_s008 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s009 q pA pB
    | _ => .done

def base128_s007 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s008 q pA pB
    | _ => .done

def base128_s006 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s007 q pA pB
    | _ => .done

def base128_s005 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => base128_s006 q pA pB
    | _ => .done

def base128_s004 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => base128_s005 q pA pB
    | _ => .done

def base128_s003 (q : Bool) (pA : Ptr) : Plan :=
  .call (.allocate .heap 1 1) fun reply =>
    match reply with
    | .pointer pB => base128_s004 q pA pB
    | _ => .done

def base128_s002 (q : Bool) (pA : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => base128_s003 q pA
    | _ => .done

def base128_s001 (q : Bool) : Plan :=
  .call (.allocate .heap 1 1) fun reply =>
    match reply with
    | .pointer pA => base128_s002 q pA
    | _ => .done

def base128 (q : Bool) : Plan := base128_s001 q

/- Distinct early cleanup, reached only by the actual bytes reply test below. -/

def early32_freeA (pA : Ptr) : Plan :=
  .call (.free pA .heap 1 1) fun reply =>
    match reply with
    | .unit => .done
    | _ => .done

def early32_freeB (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.free pB .heap 1 1) fun reply =>
    match reply with
    | .unit => early32_freeA pA
    | _ => .done

def early32_s016 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes bytes =>
        if bytes = oneBytes then early32_freeB pA pB
        else base32_s017 q pA pB
    | _ => .done

def early32_s015 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => early32_s016 q pA pB
    | _ => .done

def early32_s014 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => early32_s015 q pA pB
    | _ => .done

def early32_s013 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => early32_s014 q pA pB
    | _ => .done

def early32_s012 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => early32_s013 q pA pB
    | _ => .done

def early32_s011 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => early32_s012 q pA pB
    | _ => .done

def early32_s010 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (nineBytes) 1) fun reply =>
    match reply with
    | .unit => early32_s011 q pA pB
    | _ => .done

def early32_s009 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => early32_s010 q pA pB
    | _ => .done

def early32_s008 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => early32_s009 q pA pB
    | _ => .done

def early32_s007 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => early32_s008 q pA pB
    | _ => .done

def early32_s006 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => early32_s007 q pA pB
    | _ => .done

def early32_s005 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => early32_s006 q pA pB
    | _ => .done

def early32_s004 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => early32_s005 q pA pB
    | _ => .done

def early32_s003 (q : Bool) (pA : Ptr) : Plan :=
  .call (.allocate .heap 1 1) fun reply =>
    match reply with
    | .pointer pB => early32_s004 q pA pB
    | _ => .done

def early32_s002 (q : Bool) (pA : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => early32_s003 q pA
    | _ => .done

def early32_s001 (q : Bool) : Plan :=
  .call (.allocate .heap 1 1) fun reply =>
    match reply with
    | .pointer pA => early32_s002 q pA
    | _ => .done

def early32 (q : Bool) : Plan := early32_s001 q

/- The leak variant omits B's free only on the same actual-load early arm. -/

def leaky32_freeA (pA : Ptr) : Plan :=
  .call (.free pA .heap 1 1) fun reply =>
    match reply with
    | .unit => .done
    | _ => .done

def leaky32_s016 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes bytes =>
        if bytes = oneBytes then leaky32_freeA pA
        else base32_s017 q pA pB
    | _ => .done

def leaky32_s015 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => leaky32_s016 q pA pB
    | _ => .done

def leaky32_s014 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => leaky32_s015 q pA pB
    | _ => .done

def leaky32_s013 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => leaky32_s014 q pA pB
    | _ => .done

def leaky32_s012 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => leaky32_s013 q pA pB
    | _ => .done

def leaky32_s011 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => leaky32_s012 q pA pB
    | _ => .done

def leaky32_s010 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (nineBytes) 1) fun reply =>
    match reply with
    | .unit => leaky32_s011 q pA pB
    | _ => .done

def leaky32_s009 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => leaky32_s010 q pA pB
    | _ => .done

def leaky32_s008 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pB 1 1) fun reply =>
    match reply with
    | .bytes _ => leaky32_s009 q pA pB
    | _ => .done

def leaky32_s007 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => leaky32_s008 q pA pB
    | _ => .done

def leaky32_s006 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => leaky32_s007 q pA pB
    | _ => .done

def leaky32_s005 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => leaky32_s006 q pA pB
    | _ => .done

def leaky32_s004 (q : Bool) (pA : Ptr) (pB : Ptr) : Plan :=
  .call (.store pB (signalBytes q) 1) fun reply =>
    match reply with
    | .unit => leaky32_s005 q pA pB
    | _ => .done

def leaky32_s003 (q : Bool) (pA : Ptr) : Plan :=
  .call (.allocate .heap 1 1) fun reply =>
    match reply with
    | .pointer pB => leaky32_s004 q pA pB
    | _ => .done

def leaky32_s002 (q : Bool) (pA : Ptr) : Plan :=
  .call (.store pA (sevenBytes) 1) fun reply =>
    match reply with
    | .unit => leaky32_s003 q pA
    | _ => .done

def leaky32_s001 (q : Bool) : Plan :=
  .call (.allocate .heap 1 1) fun reply =>
    match reply with
    | .pointer pA => leaky32_s002 q pA
    | _ => .done

def leaky32 (q : Bool) : Plan := leaky32_s001 q

/- Choice discriminator: retain the actual first allocation and branch on
its numeric address. The ordinary arm starts after, not before, that allocation. -/

def staleChoice8_load (pA : Ptr) : Plan :=
  .call (.load pA 1 1) fun reply =>
    match reply with
    | .bytes _ => .spin
    | _ => .done

def staleChoice8_free (pA : Ptr) : Plan :=
  .call (.free pA .heap 1 1) fun reply =>
    match reply with
    | .unit => staleChoice8_load pA
    | _ => .done

def staleChoice8 (q : Bool) : Plan :=
  .call (.allocate .heap 1 1) fun reply =>
    match reply with
    | .pointer pA =>
        if pA.addr = 2 then staleChoice8_free pA
        else base8_s002 q pA
    | _ => .done

/-- Exact aliases for later route endpoints; no theorem is supplied. -/
def Base8Claim (q : Bool) : Prop := Claim base8 q
def Base32Claim (q : Bool) : Prop := Claim base32 q
def Base128Claim (q : Bool) : Prop := Claim base128 q
def Early32Claim (q : Bool) : Prop := Claim early32 q

def StaleChoice8Claim (q : Bool) : Prop := Claim staleChoice8 q
def Leaky32Claim (q : Bool) : Prop := Claim leaky32 q

end AnnealResearch.ProgramCostCommon
