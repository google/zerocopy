From iris.proofmode Require Export proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls gen_log_rel.
From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import tkmap_view.
From simuliris.tree_borrows Require Export defs.
From simuliris.tree_borrows Require Export steps_wf.
From simuliris.tree_borrows Require Import steps_progress.

Section disabled_tag.


  Context (C : gset call_id).

  Inductive pseudo_disabled (tr : tree item) (tg : tag) (l : Z) : permission → (option protector) → Prop :=
    | pseudo_disabled_disabled prot :
        (* a Disabled it also pseudo-disabled *)
        pseudo_disabled _ _ _ Disabled prot
    | pseudo_disabled_cousin_active tg_cous it_cous lp prot :
        rel_dec tr tg tg_cous = Foreign Cousin ->
        tree_lookup tr tg_cous it_cous ->
        protector_is_active it_cous.(iprot) C ->
        (item_lookup it_cous l) = mkPerm PermInit Active ->
        (* This is not allowed, since it actually survives foreign writes. *)
        lp ≠ ReservedIM -> lp ≠ Cell ->
        pseudo_disabled _ _ _ lp prot
    .

  (* this implicitly requires (by state_wf) that it's not (protected and initialized) *)
  (* it also implies (via state_wf) that all children are not (protected and initialized) *)
  Inductive is_disabled (tr : tree item) (tg : tag) (l : Z) : lazy_permission → option protector → Prop :=
    | disabled_init prot : 
        is_disabled _ _ _ (mkPerm PermInit Disabled) prot
    | disabled_pseudo lp prot :
        pseudo_disabled tr tg l lp prot →
        is_disabled _ _ _ (mkPerm PermLazy lp) prot.

  Inductive disabled_in_practice (tr : tree item) (tg : tag) (witness : tag) (l : Z)
    : Prop :=
    | disabled_parent it_witness inclusive :
      (* Doesn't have to be immediate, just any parent is Disabled *)
      rel_dec tr tg witness = Child inclusive ->
      tree_lookup tr witness it_witness ->
      is_disabled tr witness l (item_lookup it_witness l) (iprot it_witness) ->
      disabled_in_practice tr tg witness l
    .

  Definition disabled_tag_at (tr: tree item) (tg : tag) (l : Z) := ∃ witness, disabled_in_practice tr tg witness l.

  Definition disabled_tag (trs : trees) nxtp (tg : tag) (l : loc) := tg < nxtp ∧ (match trs !! l.1 with Some tr => disabled_tag_at tr tg l.2 ∨ ¬ tree_contains tg tr | None => True end).

  Definition active_child tr tg l :=
    ∃ it ii, tree_lookup tr (itag it) it ∧ rel_dec tr (itag it) tg = Child (Strict ii) ∧ item_lookup it l = mkPerm PermInit Active ∧ protector_is_active (iprot it) C.

End disabled_tag.