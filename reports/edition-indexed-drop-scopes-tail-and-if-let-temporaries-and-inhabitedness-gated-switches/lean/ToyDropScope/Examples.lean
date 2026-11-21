import ToyDropScope.Semantics
import ToyDropScope.Switch

/-!
Positive and negative examples for every definition of the package, all fully proved.
-/

namespace Toy.DropScope

/-! ## Named example programs -/

/-- `{ let x = unit_with_dtor(0); temp_with_dtor(1) }`: a block with one local whose destructor
emits `dtor 0` and a tail expression that creates a temporary whose destructor emits `dtor 1`. -/
def tailProg : Expr := .block (.letS 0 [.dtor 0] .unit (.tail (.temp [.dtor 1] [])))

/-- `if let P = temp_with_dtor(0) { } else { out(1) }` with the pattern not matching. -/
def ifLetElseProg : Expr := .ifLet false (.temp [.dtor 0] []) .unit (.out 1)

/-- The `RefCell` tail-borrow shape: `{ let c = ..; c.borrow().len() }`. The local `c`
(name `0`) has a destructor without events; the tail creates a temporary that borrows `c` and
whose destructor emits `dtor 1`. -/
def refCellTailProg : Expr := .block (.letS 0 [] .unit (.tail (.temp [.dtor 1] [0])))

/-- A temporary in a `let` initializer, temporaries in `if let` branches and an `if let` whose
scrutinee creates no temporary: no temporary escapes a tail expression or an `if let`
scrutinee. -/
def stmtTempsProg : Expr :=
  .block (.letS 0 [.dtor 0] (.temp [.dtor 1] [])
    (.exprS (.ifLet false .unit (.temp [.dtor 2] []) (.seq (.temp [.dtor 3] []) (.out 0)))
      (.tail (.out 1))))

/-- A block with one local and one tail temporary whose destructors emit no events. -/
def silentTailProg : Expr := .block (.letS 0 [] .unit (.tail (.temp [] [])))

/-- The `RefCell` tail-borrow shape with a tail temporary whose destructor emits no events. -/
def silentRefCellTailProg : Expr := .block (.letS 0 [] .unit (.tail (.temp [] [0])))

/-- A block without locals whose tail expression creates a temporary with destructor event
`dtor 0`. -/
def topLevelTailTempProg : Expr := .block (.tail (.temp [.dtor 0] []))

/-- `if let P = temp_with_dtor(0) { }` with the pattern matching and an empty `else` block. -/
def bareIfLetThenProg : Expr := .ifLet true (.temp [.dtor 0] []) .unit .unit

/-- An `if let` whose pattern does not match and whose `else` block emits `out 1`; its scrutinee
is a `match` whose own scrutinee creates a temporary with destructor event `dtor 0`. The program
contains no block. -/
def matchInIfLetScrutProg : Expr :=
  .ifLet false (.matchE true (.temp [.dtor 0] []) .unit .unit) .unit (.out 1)

/-- A block without locals whose tail creates a temporary with destructor event `dtor 0`, followed
in the same expression by the output `out 1`. -/
def siblingTailProg : Expr := .seq (.block (.tail (.temp [.dtor 0] []))) (.out 1)

/-- Shadowing: an outer local named `0`, then an expression statement whose inner block declares
another local named `0` and whose tail creates a temporary that borrows the name `0`. -/
def shadowedBorrowProg : Expr :=
  .block (.letS 0 [] .unit
    (.exprS (.block (.letS 0 [] .unit (.tail (.temp [.dtor 1] [0])))) (.tail .unit)))

/-! ## `Edition.rules` -/

/-- Positive example: 2024 enables both narrowing rules. -/
theorem edition_rules_e2024 : Edition.e2024.rules = ⟨true, true⟩ := rfl

/-- Negative example: 2021 enables neither narrowing rule, so its settings differ from 2024's. -/
theorem edition_rules_e2021_ne_e2024 : Edition.e2021.rules ≠ Edition.e2024.rules := by decide

/-! ## `eval` / `run` / `trace` -/

/-- Positive example (2024 tail rule): the tail temporary is dropped before the block's local. -/
theorem trace_tailProg_e2024 : trace Edition.e2024.rules tailProg = [.dtor 1, .dtor 0] := by decide

/-- Positive example (2021 tail rule): the tail temporary is dropped after the block's local. -/
theorem trace_tailProg_e2021 : trace Edition.e2021.rules tailProg = [.dtor 0, .dtor 1] := by decide

/-- Negative example: under the 2024 rules the tail temporary is not dropped after the local. -/
theorem trace_tailProg_e2024_ne_local_first :
    trace Edition.e2024.rules tailProg ≠ [.dtor 0, .dtor 1] := by decide

/-- Positive example (statement scope): a temporary created in a `let` initializer is dropped at
the end of that statement, before the next statement's events, in both editions. -/
theorem trace_letInitTemp_both :
    trace Edition.e2021.rules (.block (.letS 0 [] (.temp [.dtor 1] []) (.tail (.out 0))))
      = [.dtor 1, .out 0] ∧
    trace Edition.e2024.rules (.block (.letS 0 [] (.temp [.dtor 1] []) (.tail (.out 0))))
      = [.dtor 1, .out 0] := by decide

/-- Positive example (2024 `if let` rule, else branch): the scrutinee temporary is dropped before
the `else` block runs. -/
theorem trace_ifLetElseProg_e2024 :
    trace Edition.e2024.rules ifLetElseProg = [.dtor 0, .out 1] := by decide

/-- Positive example (2024 `if let` rule, then branch): the scrutinee temporary is dropped after
the consequent. -/
theorem trace_ifLetThen_e2024 :
    trace Edition.e2024.rules (.ifLet true (.temp [.dtor 0] []) (.out 1) .unit)
      = [.out 1, .dtor 0] := by decide

/-- Negative example: under the 2021 rules the scrutinee temporary is not dropped before the
`else` block. -/
theorem trace_ifLetElseProg_e2021_ne_scrutinee_first :
    trace Edition.e2021.rules ifLetElseProg ≠ [.dtor 0, .out 1] := by decide

/-- Positive example (temporaries drop in reverse creation order). -/
theorem trace_two_temps_reverse :
    trace Edition.e2021.rules (.seq (.temp [.dtor 0] []) (.temp [.dtor 1] [])) = [.dtor 1, .dtor 0] :=
  by decide

/-! ## `Act.isDropTemp` / `mkTemps` / `dropTemps` -/

/-- Positive example (`Act.isDropTemp`): a temporary drop. -/
theorem isDropTemp_dropTemp : (Act.dropTemp [] [] [.dtor 0]).isDropTemp = true := rfl

/-- Negative example (`Act.isDropTemp`): a local drop is not a temporary drop. -/
theorem not_isDropTemp_dropLocal : (Act.dropLocal [] 0 [.dtor 0]).isDropTemp = false := rfl

/-- Positive example (`mkTemps`, `dropTemps`): `tailProg` creates and drops one temporary, with the
same tag and borrow list. -/
theorem mkTemps_dropTemps_tailProg :
    mkTemps (run Edition.e2021.rules tailProg) = [([0, 1, 0], [])] ∧
    dropTemps (run Edition.e2021.rules tailProg) = [([0, 1, 0], [])] := by decide

/-- Negative example (`mkTemps`, `dropTemps`): a creation is not a drop and a drop is not a
creation. -/
theorem dropTemps_mkTemp_mkTemps_dropTemp :
    dropTemps [.mkTemp [] []] = [] ∧ mkTemps [.dropTemp [] [] []] = [] := ⟨rfl, rfl⟩

/-! ## `borrowOK` / `accepts` -/

/-- Positive example: the `RefCell` tail-borrow shape is accepted under the 2024 rules. -/
theorem accepts_refCellTailProg_e2024 : accepts Edition.e2024.rules refCellTailProg = true := by
  decide

/-- Negative example: the same program is rejected under the 2021 rules (the temporary is dropped
after the local it borrows). -/
theorem accepts_refCellTailProg_e2021 : accepts Edition.e2021.rules refCellTailProg = false := by
  decide

/-- Negative example: a temporary borrowing a local that is not in scope is rejected. -/
theorem accepts_unboundBorrow : accepts Edition.e2024.rules (.temp [] [5]) = false := by decide

/-- Limitation example (`borrowOK`): with shadowing, the 2021 rules drop the inner local `0`
before the temporary that borrows the name `0`, yet the check accepts, because the outer local's
name is still live. -/
theorem borrowOK_shadowing_limitation :
    run Edition.e2021.rules shadowedBorrowProg =
      [.mkLocal [0] 0, .mkLocal [0, 0, 1, 0] 0, .mkTemp [0, 1, 0, 0, 1, 0] [0],
       .dropLocal [0, 0, 1, 0] 0 [], .dropTemp [0, 1, 0, 0, 1, 0] [0] [.dtor 1],
       .dropLocal [0] 0 []] ∧
    accepts Edition.e2021.rules shadowedBorrowProg = true := by decide

/-! ## `BehIncl` -/

/-- Positive example: behaviour inclusion is reflexive. -/
theorem behIncl_refl (R : Rules) : BehIncl R R := fun _ _ h => h

/-- Negative example: `tailProg` is accepted under both editions with different traces, so 2021
behaviour is not included in 2024 behaviour. -/
theorem not_behIncl_e2021_e2024_at_tailProg :
    beh Edition.e2021.rules tailProg = some [.dtor 0, .dtor 1] ∧
    beh Edition.e2024.rules tailProg = some [.dtor 1, .dtor 0] := by decide

/-! ## `toMatch` -/

/-- Positive example: an `if let` becomes a `match` with the same scrutinee and arms. -/
theorem toMatch_ifLetElseProg :
    toMatch ifLetElseProg = .matchE false (.temp [.dtor 0] []) .unit (.out 1) := rfl

/-- Negative example: `toMatch` changes a program containing an `if let`. -/
theorem toMatch_ifLetElseProg_ne : toMatch ifLetElseProg ≠ ifLetElseProg := by
  simp [toMatch, ifLetElseProg]

/-! ## `noEscape` -/

/-- Positive example: a temporary in a `let` initializer inside a block does not escape the block. -/
theorem noEscape_letInit : noEscape (.block (.letS 0 [] (.temp [] []) (.tail .unit))) = true := by
  decide

/-- Positive example: temporaries inside `match` arms do not escape the `match`. -/
theorem noEscape_matchArms : noEscape (.matchE true .unit (.temp [] []) (.temp [] [])) = true := by
  decide

/-- Negative example: a bare temporary escapes. -/
theorem noEscape_temp : noEscape (.temp [] []) = false := by decide

/-- Negative example: an `if let` scrutinee temporary counts as escaping (as under the 2021 rules). -/
theorem noEscape_ifLetScrut : noEscape (.ifLet true (.temp [] []) .unit .unit) = false := by decide

/-! ## `NoTailEscapingTemps` / `NoIfLetEscapingTemps` -/

/-- Positive example: in `stmtTempsProg` no temporary escapes a tail expression. -/
theorem noTailEscapingTemps_stmtTempsProg : NoTailEscapingTemps stmtTempsProg := by decide

/-- Negative example: `tailProg`'s tail expression creates a temporary. -/
theorem not_noTailEscapingTemps_tailProg : ¬ NoTailEscapingTemps tailProg := by decide

/-- Negative example: a temporary created in the tail of a block that is itself a tail
expression escapes both tail expressions. -/
theorem not_noTailEscapingTemps_nested :
    ¬ NoTailEscapingTemps (.block (.tail (.block (.tail (.temp [] []))))) := by decide

/-- Positive example: in `stmtTempsProg` no temporary escapes an `if let` scrutinee. -/
theorem noIfLetEscapingTemps_stmtTempsProg : NoIfLetEscapingTemps stmtTempsProg := by decide

/-- Negative example: `ifLetElseProg`'s scrutinee creates a temporary. -/
theorem not_noIfLetEscapingTemps_ifLetElseProg : ¬ NoIfLetEscapingTemps ifLetElseProg := by decide

/-! ## `Before` / `Flipped` / `Commute` -/

/-- The four actions of `tailProg` (syntax positions are reversed paths). -/
def tailProgLocalDrop : Act := .dropLocal [0] 0 [.dtor 0]
/-- The temporary drop of `tailProg`. -/
def tailProgTempDrop : Act := .dropTemp [0, 1, 0] [] [.dtor 1]

/-- The executed actions of `tailProg` under each edition. -/
theorem run_tailProg :
    run Edition.e2021.rules tailProg =
      [.mkLocal [0] 0, .mkTemp [0, 1, 0] [], tailProgLocalDrop, tailProgTempDrop] ∧
    run Edition.e2024.rules tailProg =
      [.mkLocal [0] 0, .mkTemp [0, 1, 0] [], tailProgTempDrop, tailProgLocalDrop] := by
  decide

/-- Positive example: in `tailProg` the local drop and the temporary drop are flipped. -/
theorem flipped_tailProg : Flipped tailProg tailProgLocalDrop tailProgTempDrop := by
  obtain ⟨h21, h24⟩ := run_tailProg
  refine ⟨⟨2, 3, by decide, ?_, ?_⟩, ⟨2, 3, by decide, ?_, ?_⟩⟩ <;> simp [h21, h24]

/-- Negative example: the local's binding and its drop are not flipped. -/
theorem not_flipped_tailProg_mkLocal :
    ¬ Flipped tailProg (.mkLocal [0] 0) tailProgLocalDrop := by
  obtain ⟨h21, h24⟩ := run_tailProg
  rintro ⟨_, i, j, hij, hi, hj⟩
  rw [h24] at hi hj
  have hi' : i = 3 := by
    match i, hi with
    | 0, h => simp [tailProgLocalDrop, tailProgTempDrop] at h
    | 1, h => simp [tailProgLocalDrop, tailProgTempDrop] at h
    | 2, h => simp [tailProgLocalDrop, tailProgTempDrop] at h
    | 3, _ => rfl
    | k + 4, h => simp at h
  have hj' : j = 0 := by
    match j, hj with
    | 0, _ => rfl
    | 1, h => simp at h
    | 2, h => simp [tailProgTempDrop] at h
    | 3, h => simp [tailProgLocalDrop] at h
    | k + 4, h => simp at h
  omega

/-- Positive example: two actions emitting the same single event commute. -/
theorem commute_same_event :
    Commute (.dropLocal [] 0 [.dtor 0]) (.dropTemp [1] [] [.dtor 0]) := rfl

/-- Negative example: the drops of `tailProg` do not commute. -/
theorem not_commute_tailProg : ¬ Commute tailProgLocalDrop tailProgTempDrop := by decide

/-! ## Switch model -/

/-- The three-variant switch from the documentation comment of the unreachable-enum-branching
pass: `match c { Less => 1, Equal => 2, _ => 3 }`, with tags `Less = 0`, `Equal = 1`,
`Greater = 2`. -/
def orderingSwitch : Switch := ⟨[(0, .goto 1), (1, .goto 2)], .goto 3⟩

/-- Positive example (`Switch.target`): an explicit arm is selected. -/
theorem target_orderingSwitch_0 : orderingSwitch.target 0 = .goto 1 := rfl

/-- Negative example (`Switch.target`): a value without explicit arm does not select an explicit
arm's target. -/
theorem target_orderingSwitch_2 : orderingSwitch.target 2 = .goto 3 := rfl

/-- Positive example (`exec`): a defined read continues to the selected target. -/
theorem exec_ok : exec (fun _ => false) (fun _ => true) orderingSwitch 1 = .ret 2 := rfl

/-- Negative example (`exec`): a read that is undefined behaviour yields `ub` whatever the target. -/
theorem exec_readUB : exec (fun _ => true) (fun _ => true) orderingSwitch 1 = .ub := rfl

/-- Positive example (`runArm`): using the payload of a tag with a payload continues. -/
theorem runArm_usePayload_ok : runArm (fun _ => true) 0 (.usePayload 7) = .ret 7 := rfl

/-- Negative example (`runArm`): using the payload of a tag without payload is `ub`. -/
theorem runArm_usePayload_bad : runArm (fun _ => false) 0 (.usePayload 7) = .ub := rfl

/-- Positive example (`Refines`): anything refines `ub`. -/
theorem refines_ub (o : Outcome) : Refines o .ub := Or.inl rfl

/-- Negative example (`Refines`): `ub` does not refine a normal outcome. -/
theorem not_refines_ub_ret : ¬ Refines .ub (.ret 0) := by simp [Refines]

/-- Positive example (`Refines`): equal normal outcomes refine each other. -/
theorem refines_ret_eq : Refines (.ret 3) (.ret 3) := Or.inr rfl

/-- Negative example (`Refines`): distinct normal outcomes do not refine each other. -/
theorem not_refines_ret_ne : ¬ Refines (.ret 0) (.ret 1) := by simp [Refines]

/-- Positive example (`allowedTag`): a tag below `n` satisfying `A`. -/
theorem allowedTag_pos : allowedTag 3 (fun _ => true) 2 = true := rfl

/-- Negative examples (`allowedTag`): a tag not below `n`, and a tag below `n` failing `A`. -/
theorem allowedTag_neg :
    allowedTag 3 (fun _ => true) 3 = false ∧ allowedTag 3 (fun t => t != 1) 1 = false := by decide

/-- Positive example (`remainingAllowed`): in `orderingSwitch` the allowed tag `2` has no explicit
arm. -/
theorem remainingAllowed_orderingSwitch : remainingAllowed 3 (fun _ => true) orderingSwitch = [2] := by
  decide

/-- Negative example (`remainingAllowed`): when every allowed tag has an explicit arm, nothing
remains. -/
theorem remainingAllowed_all_covered :
    remainingAllowed 3 (fun _ => true) ⟨[(0, .goto 0), (1, .goto 1), (2, .goto 2)], .goto 3⟩ = [] := by
  decide

/-- Positive example (`lastVariantTakesWildcard`, zero-remaining branch): every allowed tag of
`[true, false, true]` has an explicit arm, so the wildcard becomes `unreachable` and no arm is
added. -/
theorem lastVariantTakesWildcard_no_remaining :
    lastVariantTakesWildcard 3 (Enum.inhabitedTag [true, false, true])
        ⟨[(0, .goto 0), (2, .goto 2)], .goto 1⟩ =
      ⟨[(0, .goto 0), (2, .goto 2)], .unreachable⟩ := by decide

/-- Positive example (`lastVariantTakesWildcard`): the documented transformation of the pass:
the one inhabited variant without an explicit arm (`Greater`) takes the wildcard target and the
wildcard becomes `unreachable`. -/
theorem lastVariantTakesWildcard_orderingSwitch :
    lastVariantTakesWildcard 3 (fun _ => true) orderingSwitch =
      ⟨[(0, .goto 1), (1, .goto 2), (2, .goto 3)], .unreachable⟩ := by decide

/-- Negative example (`lastVariantTakesWildcard`): with two allowed tags lacking explicit arms the
switch is unchanged. -/
theorem lastVariantTakesWildcard_two_remaining :
    lastVariantTakesWildcard 3 (fun _ => true) ⟨[(0, .goto 1)], .goto 3⟩ = ⟨[(0, .goto 1)], .goto 3⟩ :=
  by decide

/-- Positive example (`pruneArms`): an arm on a tag outside the allowed set becomes `unreachable`. -/
theorem pruneArms_example :
    pruneArms 2 (fun t => t == 0) ⟨[(0, .goto 0), (1, .goto 1)], .goto 2⟩ =
      ⟨[(0, .goto 0), (1, .unreachable)], .goto 2⟩ := by decide

/-- Negative example (`pruneArms`): an arm on an allowed tag is kept. -/
theorem pruneArms_keeps_allowed :
    pruneArms 2 (fun _ => true) ⟨[(0, .goto 0), (1, .goto 1)], .goto 2⟩ =
      ⟨[(0, .goto 0), (1, .goto 1)], .goto 2⟩ := by decide

/-- Positive example (`readUB`): under `rejectUninhabited`, reading the tag of an uninhabited
variant is undefined behaviour. -/
theorem readUB_rejectUninhabited :
    readUB ⟨.rejectUninhabited, .rejectInvalid⟩ [true, false] 1 = true := by decide

/-- Negative example (`readUB`): under `permissive`, the same read is defined. -/
theorem readUB_permissive : readUB ⟨.permissive, .rejectInvalid⟩ [true, false] 1 = false := by
  decide

/-- Negative example (`readUB`): reading an inhabited variant's tag is defined under every
semantics. -/
theorem readUB_inhabited (D : DiscrSem) : readUB D [true, false] 0 = false := by
  cases D with | mk u i => cases u <;> cases i <;> decide

/-- Positive example (`readUB`, invalid tags): under `rejectInvalid` an invalid tag read is
undefined behaviour; under `passThrough` it is defined. -/
theorem readUB_invalid :
    readUB ⟨.permissive, .rejectInvalid⟩ [true] 1 = true ∧
    readUB ⟨.rejectUninhabited, .passThrough⟩ [true] 1 = false := by decide

/-- Degenerate edge (`readUB`, empty enum): every tag of the empty enum takes the invalid-tag
branch, so the uninhabited-tag choice is irrelevant. -/
theorem readUB_emptyEnum :
    readUB ⟨.rejectUninhabited, .passThrough⟩ [] 0 = false ∧
    readUB ⟨.permissive, .rejectInvalid⟩ [] 0 = true := by decide

/-- The toy niche encoding used by the examples: variant `0` is untagged (it holds the niche),
variants `1..2` are niche-encoded starting at stored value `2`. -/
def exampleNiche : NicheEnc := ⟨0, 1, 2, 2⟩

/-- Positive example (`NicheEnc.decode`): stored value `2` decodes to variant `1` and stored
value `3` to variant `2`. -/
theorem decode_exampleNiche : exampleNiche.decode 2 = 1 ∧ exampleNiche.decode 3 = 2 := by decide

/-- Negative example (`NicheEnc.decode`): stored values below the niche start decode to the
untagged variant, and so do values past the niche range. -/
theorem decode_exampleNiche_untagged :
    exampleNiche.decode 0 = 0 ∧ exampleNiche.decode 1 = 0 ∧ exampleNiche.decode 4 = 0 := by decide

/-- Degenerate edge (`NicheEnc.decode`): with an empty niche range (`nicheHi < nicheLo`) every
stored value decodes to the untagged variant. -/
theorem decode_of_nicheHi_lt_nicheLo (N : NicheEnc) (h : N.nicheHi < N.nicheLo) (v : Nat) :
    N.decode v = N.untagged := by
  unfold NicheEnc.decode
  split
  · omega
  · rfl

end Toy.DropScope
