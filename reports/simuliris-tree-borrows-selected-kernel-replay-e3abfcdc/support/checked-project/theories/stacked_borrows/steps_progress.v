(** This file has been adapted from the Stacked Borrows development, available at 
  https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From simuliris.stacked_borrows Require Export steps_wf.
From Equations Require Import Equations.

(* TODO: do we need non-empty condition? ie (tsize T) > 0? *)
Lemma alloc_base_step P σ T :
  let l := (fresh_block σ.(shp), 0) in
  let t := σ.(snp) in
  let σ' := mkState (init_mem l (tsize T) σ.(shp))
                    (init_stacks σ.(sst) l (tsize T) (Tagged t)) σ.(scs) (S t) σ.(snc) in
  base_step P (Alloc T) σ (Place l (Tagged t) T) σ' [].
Proof. by econstructor; econstructor. Qed.

Lemma find_granting_is_Some stk kind bor
  (BOR: ∃ it, it ∈ stk ∧ it.(tg) = bor ∧ it.(perm) ≠ Disabled ∧
              (kind = AccessWrite → it.(perm) ≠ SharedReadOnly)) :
  is_Some (find_granting stk kind bor).
Proof.
  destruct BOR as [it [IN [Eq [ND KD]]]].
  destruct (list_find_elem_of (matched_grant kind bor) stk it IN)
    as [it1 Eq1].
  - split; [|done]. destruct it.(perm), kind; try done. naive_solver.
  - rewrite /find_granting Eq1. by eexists.
Qed.

Lemma dealloc1_progress stk bor cids
  (PR: Forall (λ it, ¬ is_active_protector cids it) stk)
  (BOR: ∃ it, it ∈ stk ∧ it.(tg) = bor ∧
        it.(perm) ≠ Disabled ∧ it.(perm) ≠ SharedReadOnly) :
  is_Some (dealloc1 stk bor cids).
Proof.
  rewrite /dealloc1.
  destruct (find_granting_is_Some stk AccessWrite bor) as [? Eq]; [naive_solver|].
  rewrite Eq /find_top_active_protector list_find_None_inv;
    [by eexists|done].
Qed.

Lemma for_each_is_Some α l (n: nat) b f :
  (∀ m : Z, 0 ≤ m ∧ m < n → l +ₗ m ∈ dom α) →
  (∀ (m: nat) stk, (m < n)%nat → α !! (l +ₗ m) = Some stk → is_Some (f stk)) →
  is_Some (for_each α l n b f).
Proof.
  revert α. induction n as [|n IHn]; intros α IN Hf; [by eexists|]. simpl.
  assert (is_Some (α !! (l +ₗ n))) as [stk Eq].
  { apply (elem_of_dom (D:=gset loc)), IN. by lia. }
  rewrite Eq /=. destruct (Hf n stk) as [stk' Eq']; [lia|done|].
  rewrite Eq' /=. destruct b; apply IHn.
  - intros. apply elem_of_dom. rewrite lookup_delete_ne.
    + apply (elem_of_dom (D:=gset loc)), IN. lia.
    + move => /shift_loc_inj. lia.
  - intros ???. rewrite lookup_delete_ne.
    + apply Hf. lia.
    + move => /shift_loc_inj. lia.
  - intros. apply elem_of_dom. rewrite lookup_insert_ne.
    + apply (elem_of_dom (D:=gset loc)), IN. lia.
    + move => /shift_loc_inj. lia.
  - intros ???. rewrite lookup_insert_ne.
    + apply Hf. lia.
    + move => /shift_loc_inj. lia.
Qed.

Definition item_inactive_protector cids (it: item) :=
  match it.(protector) with Some c => ¬ is_active cids c | _ => True end.

Lemma memory_deallocated_progress α cids l bor (n: nat) :
  (∀ m : Z, 0 ≤ m ∧ m < n → l +ₗ m ∈ dom α) →
  (∀ (m: nat) stk, (m < n)%nat → α !! (l +ₗ m) = Some stk →
      (∃ it, it ∈ stk ∧ it.(tg) = bor ∧
        it.(perm) ≠ Disabled ∧ it.(perm) ≠ SharedReadOnly) ∧
      ∀ it, it ∈ stk → item_inactive_protector cids it) →
  is_Some (memory_deallocated α cids l bor n).
Proof.
  intros IN IT. apply for_each_is_Some; [done|].
  intros m stk Lt Eq. destruct (IT _ _ Lt Eq) as [In PR].
  destruct (dealloc1_progress stk bor cids) as [? Eq1];
    [|done|rewrite Eq1; by eexists].
  apply Forall_forall. move => it /PR.
  rewrite /item_inactive_protector /is_active_protector /is_active.
  case protector; naive_solver.
Qed.

Lemma dealloc_base_step' P (σ: state) l bor T α (WF: state_wf σ) :
  (∀ m : Z, is_Some (σ.(shp) !! (l +ₗ m)) ↔ 0 ≤ m ∧ m < tsize T) →
  memory_deallocated σ.(sst) σ.(scs) l bor (tsize T) = Some α →
  let σ' := mkState (free_mem l (tsize T) σ.(shp)) α σ.(scs) σ.(snp) σ.(snc) in
  base_step P (Free (Place l bor T)) σ #[☠] σ' [].
Proof.
  intros DOM MD. econstructor; econstructor; eauto.
Qed.

Lemma dealloc_base_step P (σ: state) T l bor
  (WF: state_wf σ)
  (BLK: ∀ m : Z, l +ₗ m ∈ dom σ.(shp) ↔ 0 ≤ m ∧ m < tsize T)
  (BOR: ∀ (n: nat) stk, (n < tsize T)%nat →
    σ.(sst) !! (l +ₗ n) = Some stk →
    (∃ it, it ∈ stk ∧ it.(tg) = bor ∧
      it.(perm) ≠ Disabled ∧ it.(perm) ≠ SharedReadOnly) ∧
      ∀ it, it ∈ stk → item_inactive_protector σ.(scs) it) :
  ∃ σ',
  base_step P (Free (Place l bor T)) σ #[☠] σ' [].
Proof.
  destruct (memory_deallocated_progress σ.(sst) σ.(scs) l bor (tsize T))
    as [α' Eq']; [|done|].
  - intros. rewrite -(state_wf_dom _ WF). by apply BLK.
  - eexists. econstructor; econstructor; [|done].
    intros. by rewrite -(elem_of_dom (D:= gset loc) σ.(shp)).
Qed.

Lemma read_mem_is_Some' l n h :
  (∀ m, (m < n)%nat → l +ₗ m ∈ dom h) ↔
  is_Some (read_mem l n h).
Proof.
  eapply (read_mem_elim
            (λ l n h ov,
              (∀ m : nat, (m < n)%nat → l +ₗ m ∈ dom h) ↔ is_Some ov)
            (λ _ _ h l n oacc gov, is_Some oacc →
              ((∀ m : nat, (m < n)%nat → l +ₗ m ∈ dom h) ↔
               is_Some gov))).
  - naive_solver.
  - intros. split; first naive_solver. by intros; lia.
  - intros l1 n1 h2 l2 n2 oacc IH [acc Eqacc]. rewrite Eqacc /=.
    split.
    + intros BLK.
      assert (is_Some (h2 !! l2)) as [v2 Eq2].
      { apply (elem_of_dom (D:=gset loc)). rewrite -(shift_loc_0_nat l2).
        apply BLK. lia. }
      rewrite Eq2 /=. apply IH; [by eexists|].
      intros m Lt. rewrite shift_loc_assoc -(Nat2Z.inj_add 1). apply BLK. lia.
    + intros [v Eq]. destruct (h2 !! l2) as [v2|] eqn:Eq2; [|done].
      simpl in Eq.
      specialize (IH acc v2 (ltac:(by eexists))).
      intros m Lt. destruct m as [|m].
      { rewrite shift_loc_0_nat. apply (elem_of_dom_2 _ _ _ Eq2). }
      rewrite (_: l2 +ₗ S m = l2 +ₗ 1 +ₗ m); last first.
      { by rewrite shift_loc_assoc -(Nat2Z.inj_add 1). }
      apply IH; [|lia]. by eexists.
Qed.

Lemma read_mem_is_Some l n h
  (BLK: ∀ m, (m < n)%nat → l +ₗ m ∈ dom h) :
  is_Some (read_mem l n h).
Proof. by apply read_mem_is_Some'. Qed.

Lemma read_mem_values l n h v :
  read_mem l n h = Some v →
  length v = n ∧
  (∀ i, (i < n)%nat → h !! (l +ₗ i) = v !! i).
Proof.
  eapply (read_mem_elim
            (λ l n h ovl, ∀ vl, ovl = Some vl →
              length vl = n ∧
              (∀ i, (i < n)%nat → h !! (l +ₗ i) = vl !! i))
            (λ _ _ h l n oacc ovl, ∀ acc vl,
              oacc = Some acc → ovl = Some vl →
              (∀ i, (i < length acc)%nat → h !! (l +ₗ (i - length acc)) = acc !! i) →
              length vl = (length acc + n)%nat ∧
              (∀ i, (i < length acc)%nat → h !! (l +ₗ (i - length acc)) = vl !! i) ∧
              (∀ i, (i < n)%nat → h !! (l +ₗ i) = vl !! (length acc + i)%nat))).
  - intros ??? IH vl1 Eq.
    destruct (IH [] vl1) as [IH1 IH2]; [done..|simpl;intros;lia|].
    split; [done|]. intros i.
     rewrite -{2}(Nat.add_0_l i) -(length_nil (A:=scalar)). by apply IH2.
  - clear. intros _ _ ????????. simplify_eq/=.
    (* We use [simplify_eq/=] to work around https://github.com/mattam82/Coq-Equations/issues/449. *)
    split; [lia|]. split; [done|intros; lia].
  - clear. move => l0 n0 h l n oacc IH acc vl -> /=.
    case lookup as [v|] eqn:Eq; [|done].
    move => /= Eqvl ACC.
    destruct (IH acc v (acc ++ [v]) vl eq_refl Eqvl) as [IH0 [IH1 IH2]];
      last split; last split.
    { intros i. rewrite length_app /=. intros Lt.
      rewrite (_: l +ₗ 1 +ₗ (i - (length acc + 1)%nat) = l +ₗ (i - length acc));
        last first. { rewrite shift_loc_assoc. f_equal. lia. }
      case (decide (i = length acc)) => ?; [subst i|].
      - by rewrite Z.sub_diag shift_loc_0 list_lookup_middle.
      - have ?: (i < length acc)%nat by lia.
        rewrite ACC; [|done]. by rewrite lookup_app_l. }
    { rewrite IH0 length_app /=. lia. }
    { intros i Lt. rewrite -IH1; [|rewrite length_app /=; lia].
      f_equal. rewrite shift_loc_assoc. f_equal. rewrite length_app /=. lia. }
    intros [|i] Lt.
    + rewrite Nat.add_0_r -IH1; [|rewrite length_app /=; lia].
      rewrite length_app /= shift_loc_assoc. do 2 f_equal. lia.
    + rewrite (_: (l +ₗ S i) =  (l +ₗ 1 +ₗ i));
        [|rewrite shift_loc_assoc; f_equal; lia].
      rewrite IH2; [|lia]. f_equal. rewrite length_app /=. lia.
Qed.

Lemma read_mem_values' l n h v :
  length v = n →
  (∀ i, (i < n)%nat → h !! (l +ₗ i) = v !! i) →
  read_mem l n h = Some v.
Proof.
  intros <- Hs.
  destruct (read_mem_is_Some l (length v) h) as (v' & Hv').
  { intros m Hm. apply elem_of_dom. rewrite Hs; last done.
    apply lookup_lt_is_Some_2. done.
  }
  enough (v' = v) as -> by done.
  apply read_mem_values in Hv' as [Hlen Hv'].
  eapply list_eq_same_length; [reflexivity | lia | ].
  intros i sc sc' Hi.
  rewrite -Hs; last lia. rewrite -Hv'; last lia. intros -> [= ->]. done.
Qed.

Lemma replace_check'_is_Some cids acc stk :
  (∀ it, it ∈ stk → it.(perm) = Unique → item_inactive_protector cids it) →
  is_Some (replace_check' cids acc stk).
Proof.
  revert acc. induction stk as [|si stk IH]; intros acc PR; simpl; [by eexists|].
  case decide => EqU; last by (apply IH; set_solver).
  rewrite (Is_true_eq_true (check_protector cids si)); first by (apply IH; set_solver).
  have IN: si ∈ si :: stk by set_solver. apply PR in IN; [|done].
  move : IN. rewrite /check_protector /item_inactive_protector.
  case si.(protector) => [? /negb_prop_intro|//]. by case is_active.
Qed.

Lemma replace_check_is_Some cids stk :
  (∀ it, it ∈ stk → it.(perm) = Unique → item_inactive_protector cids it) →
  is_Some (replace_check cids stk).
Proof. move => /replace_check'_is_Some IS. by apply IS. Qed.

Lemma find_first_write_incompatible_is_Some stk pm:
  pm ≠ Disabled → pm ≠ SharedReadOnly →
  is_Some (find_first_write_incompatible stk pm).
Proof.
  intros. rewrite /find_first_write_incompatible.
  destruct pm; [by eexists| |done..].
  case list_find as [[]|]; by eexists.
Qed.

Lemma find_first_write_incompatible_length stk pm idx :
  find_first_write_incompatible stk pm = Some idx → (idx ≤ length stk)%nat.
Proof.
  rewrite /find_first_write_incompatible.
  destruct pm; [by intros; simplify_eq/=| |done..].
  case list_find as [[]|]; intros; simplify_eq/=; lia.
Qed.

Lemma remove_check_is_Some cids stk idx :
  (idx ≤ length stk)%nat →
  (∀ i it, (i < idx)%nat → stk !! i = Some it → item_inactive_protector cids it) →
  is_Some (remove_check cids stk idx).
Proof.
  revert idx. induction stk as [|si stk IH]; simpl; intros idx Le PR.
  { apply Nat.le_0_r in Le. subst idx. by eexists. }
  destruct idx as [|idx]; [by eexists|].
  have IA: item_inactive_protector cids si by (apply (PR O); [lia|done]).
  rewrite (Is_true_eq_true (check_protector cids si)).
  - apply IH; [lia|]. intros i ??. apply (PR (S i)). lia.
  - move : IA. rewrite /check_protector /item_inactive_protector.
    case si.(protector) => [? /negb_prop_intro|//]. by case is_active.
Qed.

Lemma grants_read_all pm: pm ≠ Disabled → grants pm AccessRead.
Proof. by case pm. Qed.
Lemma grants_write_all pm:
  pm ≠ Disabled → pm ≠ SharedReadOnly → grants pm AccessWrite.
Proof. by case pm. Qed.

Definition access1_read_pre cids (stk: stack) (bor: tag) :=
  ∃ (i: nat) it, stk !! i = Some it ∧ it.(tg) = bor ∧ it.(perm) ≠ Disabled ∧
  ∀ (j: nat) jt, (j < i)%nat → stk !! j = Some jt →
    (jt.(perm) = Disabled ∨ jt.(tg) ≠ bor) ∧
    match jt.(perm) with
    | Unique => item_inactive_protector cids jt
    | _ => True
    end.

Definition access1_write_pre cids (stk: stack) (bor: tag) :=
  ∃ (i: nat) it, stk !! i = Some it ∧ it.(perm) ≠ Disabled ∧
  it.(perm) ≠ SharedReadOnly ∧ it.(tg) = bor ∧
  ∀ (j: nat) jt, (j < i)%nat → stk !! j = Some jt →
    (jt.(perm) = Disabled ∨ jt.(perm) = SharedReadOnly ∨ jt.(tg) ≠ bor) ∧
    match find_first_write_incompatible (take i stk) it.(perm) with
    | Some idx =>
        if decide (j < idx)%nat then
        (* Note: if a Disabled item is already in the stack, then its protector
          must have been inactive since its insertion, so this condition is
          unneccessary. *)
          item_inactive_protector cids jt
        else True
    | _ => True
    end.

Definition is_write (access: access_kind) : bool :=
  match access with AccessWrite => true | _ => false end.
Definition access1_pre
  cids (stk: stack) (access: access_kind) (bor: tag) :=
  ∃ (i: nat) it, stk !! i = Some it ∧ it.(perm) ≠ Disabled ∧
  (is_write access → it.(perm) ≠ SharedReadOnly) ∧ it.(tg) = bor ∧
  ∀ (j: nat) jt, (j < i)%nat → stk !! j = Some jt →
    (jt.(perm) = Disabled ∨
     (if is_write access then jt.(perm) = SharedReadOnly ∨ jt.(tg) ≠ bor
      else jt.(tg) ≠ bor)) ∧
    if is_write access then
      match find_first_write_incompatible (take i stk) it.(perm) with
      | Some idx =>
          if decide (j < idx)%nat then
          (* Note: if a Disabled item is already in the stack, then its protector
            must have been inactive since its insertion, so this condition is
            unneccessary. *)
            item_inactive_protector cids jt
          else True
      | _ => True
      end
    else
      match jt.(perm) with
      | Unique => item_inactive_protector cids jt
      | _ => True
      end.

Lemma access1_is_Some cids stk kind bor
  (BOR: access1_pre cids stk kind bor) :
  is_Some (access1 stk kind bor cids).
Proof.
  destruct BOR as (i & it & Eqi & ND & IW & Eqit & Lti).
  rewrite /access1 /find_granting.
  rewrite (_: list_find (matched_grant kind bor) stk = Some (i, it)); last first.
  { apply list_find_Some_not_earlier. split; last split; [done|..].
    - split; [|done].
      destruct kind; [by apply grants_read_all|by apply grants_write_all, IW].
    - intros ?? Lt Eq GR. destruct (Lti _ _ Lt Eq) as [[Eq1|NEq1] NEq2].
      { move : GR. rewrite /matched_grant Eq1 /=. naive_solver. }
      destruct kind; [by apply NEq1, GR|]. destruct NEq1 as [OR|OR].
      + move : GR. rewrite /matched_grant OR /=. naive_solver.
      + by apply OR, GR. } simpl.
  have ?: (i ≤ length stk)%nat. { by eapply Nat.lt_le_incl, lookup_lt_Some. }
  destruct kind.
  - destruct (replace_check_is_Some cids (take i stk)) as [? Eq2];
      [|rewrite Eq2 /=; by eexists].
    intros jt [j Eqj]%list_elem_of_lookup_1 IU.
    have ?: (j < i)%nat.
    { rewrite -(length_take_le stk i); [|done]. by eapply lookup_lt_Some. }
    destruct (Lti j jt) as [Eq1 PR]; [done|..].
    + symmetry. by rewrite -Eqj lookup_take_lt.
    + move : PR. by rewrite /= IU.
  - destruct (find_first_write_incompatible_is_Some (take i stk) it.(perm))
      as [idx Eqx]; [done|by apply IW|]. rewrite Eqx /=.
    destruct (remove_check_is_Some cids (take i stk) idx) as [stk' Eq'];
      [..|rewrite Eq'; by eexists].
    + move : Eqx. apply find_first_write_incompatible_length.
    + intros j jt Lt Eqj.
      have ?: (j < i)%nat.
      { rewrite -(length_take_le stk i); [|done]. by eapply lookup_lt_Some. }
      destruct (Lti j jt) as [Eq1 PR]; [done|..].
      * symmetry. by rewrite -Eqj lookup_take_lt.
      * move : PR. by rewrite /= Eqx decide_True.
Qed.

Lemma access1_read_is_Some cids stk bor
  (BOR: access1_read_pre cids stk bor) :
  is_Some (access1 stk AccessRead bor cids).
Proof.
  destruct BOR as (i & it & Eqi & Eqit & ND &  Lti).
  apply access1_is_Some. exists i, it. do 4 (split; [done|]).
  intros j jt Lt Eq. by destruct (Lti _ _ Lt Eq).
Qed.

Lemma memory_read_is_Some α cids l bor (n: nat) :
  (∀ m, (m < n)%nat → l +ₗ m ∈ dom α) →
  (∀ (m: nat) stk, (m < n)%nat →
    α !! (l +ₗ m) = Some stk → access1_read_pre cids stk bor) →
  is_Some (memory_read α cids l bor n).
Proof.
  intros IN STK. apply for_each_is_Some.
  - intros m []. rewrite -(Z2Nat.id m); [|done]. apply IN.
    rewrite -(Nat2Z.id n) -Z2Nat.inj_lt; [done..|lia].
  - intros m stk Lt Eq.
    specialize (STK _ _ Lt Eq).
    destruct (access1_read_is_Some _ _ _ STK) as [? Eq2]. rewrite Eq2. by eexists.
Qed.

Lemma copy_base_step' P (σ: state) l bor T v α (WF: state_wf σ) :
  read_mem l (tsize T) σ.(shp) = Some v →
  memory_read σ.(sst) σ.(scs) l bor (tsize T) = Some α →
  let σ' := mkState σ.(shp) α σ.(scs) σ.(snp) σ.(snc) in
  base_step P (Copy (Place l bor T)) σ (Val v) σ' [].
Proof.
  intros RM. econstructor; econstructor; eauto.
  (*move => l1 [t1|//] /list_elem_of_lookup [i Eqi].*)
  (*apply (state_wf_mem_tag _ WF (l +ₗ i) l1).*)
  (*destruct (read_mem_values _ _ _ _ RM) as [Eq1 Eq2].*)
  (*rewrite Eq2; [done|]. rewrite -Eq1. by eapply lookup_lt_Some.*)
Qed.

Lemma copy_base_step P (σ: state) l bor T
  (WF: state_wf σ)
  (BLK: ∀ n, (n < tsize T)%nat → l +ₗ n ∈ dom σ.(shp))
  (BOR: ∀ m stk, (m < tsize T)%nat → σ.(sst) !! (l +ₗ m) = Some stk →
        access1_read_pre σ.(scs) stk bor) :
  ∃ v α,
  read_mem l (tsize T) σ.(shp) = Some v ∧
  memory_read σ.(sst) σ.(scs) l bor (tsize T) = Some α ∧
  let σ' := mkState σ.(shp) α σ.(scs) σ.(snp) σ.(snc) in
  base_step P (Copy (Place l bor T)) σ (Val v) σ' [].
Proof.
  destruct (read_mem_is_Some _ _ _ BLK) as [v RM].
  destruct (memory_read_is_Some σ.(sst) σ.(scs) l bor (tsize T));[|done|].
  { move => ? /BLK. by rewrite (state_wf_dom _ WF). }
  do 2 eexists. do 2 (split; [done|]). intros σ'.
  eapply copy_base_step'; eauto.
Qed.

Lemma failed_copy_base_step' P (σ: state) l bor T (WF: state_wf σ) :
  memory_read σ.(sst) σ.(scs) l bor (tsize T) = None →
  base_step P (Copy (Place l bor T)) σ (Val $ replicate (tsize T) ScPoison) σ [].
Proof.
  intros RM. destruct σ; simpl in *. econstructor; [eapply FailedCopyBS | ]. econstructor; eauto.
Qed.

Lemma access1_write_is_Some cids stk bor
  (BOR: access1_write_pre cids stk bor) :
  is_Some (access1 stk AccessWrite bor cids).
Proof.
  destruct BOR as (i & it & Eqi & ND & Neqi & Eqit & Lti).
  apply access1_is_Some. exists i, it. do 4 (split; [done|]).
  intros j jt Lt Eq. by destruct (Lti _ _ Lt Eq).
Qed.

Lemma memory_written_is_Some α cids l bor (n: nat) :
  (∀ m, (m < n)%nat → l +ₗ m ∈ dom α) →
  (∀ (m: nat) stk, (m < n)%nat →
    α !! (l +ₗ m) = Some stk → access1_write_pre cids stk bor) →
  is_Some (memory_written α cids l bor n).
Proof.
  intros IN STK. apply for_each_is_Some.
  - intros m []. rewrite -(Z2Nat.id m); [|done]. apply IN.
    rewrite -(Nat2Z.id n) -Z2Nat.inj_lt; [done..|lia].
  - intros m stk Lt Eq.
    specialize (STK _ _ Lt Eq).
    destruct (access1_write_is_Some _ _ _ STK) as [? Eq2]. rewrite Eq2. by eexists.
Qed.

Lemma write_base_step' P (σ: state) l bor T v α
  (LEN: length v = tsize T)
  (*(LOCVAL: v <<t σ.(snp))*)
  (BLK: ∀ n, (n < tsize T)%nat → l +ₗ n ∈ dom σ.(shp))
  (BOR: memory_written σ.(sst) σ.(scs) l bor (tsize T) = Some α) :
  let σ' := mkState (write_mem l v σ.(shp)) α σ.(scs) σ.(snp) σ.(snc) in
  base_step P (Write (Place l bor T) (Val v)) σ #[☠] σ' [].
Proof. intros. econstructor 2; econstructor; eauto; by rewrite LEN. Qed.

Lemma write_base_step P (σ: state) l bor T v
  (WF: state_wf σ)
  (LEN: length v = tsize T)
  (*(LOCVAL: v <<t σ.(snp))*)
  (BLK: ∀ n, (n < tsize T)%nat → l +ₗ n ∈ dom σ.(shp))
  (STK: ∀ m stk, (m < tsize T)%nat → σ.(sst) !! (l +ₗ m) = Some stk →
        access1_write_pre σ.(scs) stk bor) :
  ∃ α,
  memory_written σ.(sst) σ.(scs) l bor (tsize T) = Some α ∧
  let σ' := mkState (write_mem l v σ.(shp)) α σ.(scs) σ.(snp) σ.(snc) in
  base_step P (Write (Place l bor T) (Val v)) σ #[☠] σ' [].
Proof.
  destruct (memory_written_is_Some σ.(sst) σ.(scs) l bor (tsize T)); [|done|].
  { move => ? /BLK. by rewrite (state_wf_dom _ WF). }
  eexists. split; [done|]. by eapply write_base_step'.
Qed.

Lemma call_base_step P σ name e r fn :
  P !! name = Some fn →
  to_result e = Some r →
  base_step P (Call #[ScFnPtr name] e) σ (apply_func fn r) σ [].
Proof. by econstructor; econstructor. Qed.

Lemma init_call_base_step P σ :
  let c := σ.(snc) in
  let σ' := mkState σ.(shp) σ.(sst) ({[σ.(snc)]} ∪ σ.(scs)) σ.(snp) (S σ.(snc)) in
  base_step P InitCall σ (#[ScCallId (σ.(snc))]) σ' [].
Proof. by econstructor; econstructor. Qed.

Lemma end_call_base_step P (σ: state) c :
  c ∈ σ.(scs) →
  let σ' := mkState σ.(shp) σ.(sst) (σ.(scs) ∖ {[c]}) σ.(snp) σ.(snc) in
  base_step P (EndCall #[ScCallId c]) σ #[☠] σ' [].
Proof. intros. by econstructor; econstructor. Qed.

Lemma unsafe_action_is_Some_weak {A} (GI: A → nat → Prop)
  (f: A → _ → nat → _ → _) a l last cur_dist n
  (HF: ∀ a i j b, (last ≤ i ≤ j ∧ j ≤ last + cur_dist + n)%nat → GI a i →
          ∃ a', f a (l +ₗ i) (Z.to_nat (j - i)) b = Some a' ∧ GI a' j) :
  GI a last → ∃ a' last' cur_dist',
  unsafe_action f a l last cur_dist n = Some (a', (last', cur_dist')) ∧ GI a' last'.
Proof.
  intros HI. rewrite /unsafe_action.
  destruct (HF a last (last + cur_dist)%nat true) as [a' Eq1]; [lia|done|].
  move : Eq1.
  rewrite (_: Z.to_nat (Z.of_nat (last + cur_dist) - Z.of_nat last) = cur_dist);
    last by rewrite Nat2Z.inj_add Z.add_simpl_l Nat2Z.id.
  move => [-> HI'] /=.
  destruct (HF a' (last + cur_dist)%nat (last + cur_dist + n)%nat false)
    as [? [Eq2 HI2]]; [lia|done|].
  move : Eq2.
  rewrite (_: Z.to_nat (Z.of_nat (last + cur_dist + n) -
                Z.of_nat (last + cur_dist)) = n);
    last by rewrite Nat2Z.inj_add Z.add_simpl_l Nat2Z.id.
  move => -> /=. by do 3 eexists.
Qed.


Lemma visit_freeze_sensitive'_is_Some {A} (GI: A → nat → Prop)
  l (f: A → _ → nat → _ → _) a (last cur_dist: nat) T
  (HF: ∀ a i j b, (last ≤ i ≤ j ∧ j ≤ last + cur_dist + tsize T)%nat → GI a i →
          ∃ a', f a (l +ₗ i) (Z.to_nat (j - i)) b = Some a' ∧ GI a' j) :
  GI a last → ∃ a' last' cur_dist',
  visit_freeze_sensitive' l f a last cur_dist T = Some (a', (last', cur_dist')) ∧
  GI a' last'.
Proof.
  revert HF.
  apply (visit_freeze_sensitive'_elim
    (* general goal P *)
    (λ l f a last cur_dist T oalc,
      (∀ a i j b,(last ≤ i ≤ j ∧ j ≤ last + cur_dist + tsize T)%nat → GI a i →
          ∃ a', f a (l +ₗ i) (Z.to_nat (j - i)) b = Some a' ∧ GI a' j) →
      GI a last → ∃ a' last' cur', oalc = Some (a', (last', cur')) ∧ GI a' last')
    (λ l f _ _ _ _ a last cur_dist Ts oalc,
      (∀ a i j b, (last ≤ i ≤ j ∧ j ≤ last + cur_dist + tsize (Product Ts))%nat →
          GI a i → ∃ a', f a (l +ₗ i) (Z.to_nat (j - i)) b = Some a' ∧ GI a' j) →
      GI a last → ∃ a' last' cur', oalc = Some (a', (last', cur')) ∧ GI a' last')).
  - naive_solver.
  - naive_solver.
  - clear. intros ?????? HF. by apply unsafe_action_is_Some_weak.
  - clear. intros l f a last cur_dist T HF.
    case is_freeze; [by do 3 eexists|]. by apply unsafe_action_is_Some_weak.
  - clear. intros l f a last cur_dist Ts IH Hf HI.
    case is_freeze; [intros; simplify_eq/=; exists a, last; by eexists|by apply IH].
  - clear. intros l f a last cur_dist T HF.
    case is_freeze; [by do 3 eexists|]. by apply unsafe_action_is_Some_weak.
  - naive_solver.
  - clear.
    intros l f a last cur_dist Ts a1 last1 cur_dist1 T1 Ts1 IH1 IH2 HF HI.
    destruct IH2 as (a2 & last2 & cur_dist2 & Eq1 & HI2); [..|done|].
    { intros ???? [? Le]. apply HF. split; [done|]. clear -Le.
      rewrite tsize_product_cons. by lia. }
    destruct (visit_freeze_sensitive'_offsets _ _ _ _ _ _ _ _ _ Eq1)
      as [LeO EqO].
    rewrite Eq1 /=. apply (IH1 (a2, (last2,cur_dist2))); [..|done].
    intros a' i j b. cbn -[tsize]. intros Lej. apply HF.
    clear -LeO EqO Lej. destruct Lej as [[Le2 Lei] Lej].
    split; [lia|]. move : Lej. rewrite EqO tsize_product_cons. lia.
Qed.

Lemma visit_freeze_sensitive_is_Some' {A} (GI: A → nat → Prop)
  l (f: A → _ → nat → _ → _) a T
  (HF: ∀ a i j b, (i ≤ j ∧ j ≤ tsize T)%nat → GI a i →
          ∃ a', f a (l +ₗ i) (Z.to_nat (j - i)) b = Some a' ∧ GI a' j) :
  GI a O → ∃ a', visit_freeze_sensitive l T f a = Some a' ∧ GI a' (tsize T).
Proof.
  intros HI. rewrite /visit_freeze_sensitive.
  destruct (visit_freeze_sensitive'_is_Some GI l f a O O T)
    as (a1 & l1 & c1 & Eq1 & HI1); [|done|].
  { rewrite 2!Nat.add_0_l. intros ???? [[??]?]. by apply HF. }
  rewrite Eq1 -(Nat.add_sub c1 l1) -(Nat2Z.id (c1 + l1 - l1))
          Nat2Z.inj_sub; [|lia].
  move : Eq1. intros [? Eq]%visit_freeze_sensitive'_offsets.
  destruct (HF a1 l1 (c1 + l1)%nat true) as (a2 & Eq2 & HI2); [|done|].
  { split; [lia|]. move : Eq. rewrite 2!Nat.add_0_l. lia. }
  exists a2. split; [done|].
  move : Eq. by rewrite 2!Nat.add_0_l Nat.add_comm => [<-].
Qed.

Lemma visit_freeze_sensitive_is_Some'_2 {A} (GI: A → nat → Prop)
  l (f: A → _ → nat → _ → _) a T
  (HF: ∀ a i j b, (i ≤ j ∧ j ≤ tsize T)%nat → GI a i →
          ∃ a', f a (l +ₗ i) (Z.to_nat (j - i)) b = Some a' ∧ GI a' j) :
  GI a O → is_Some (visit_freeze_sensitive l T f a).
Proof.
  intros HI. destruct (visit_freeze_sensitive_is_Some' GI l f a T)
    as [a' [Eq _]]; [done..|by eexists].
Qed.

Lemma visit_freeze_sensitive_is_Some {A}
  l (f: A → _ → nat → _ → _) a T
  (HF: ∀ a i j b, (i ≤ j ∧ j ≤ tsize T)%nat →
          is_Some (f a (l +ₗ i) (Z.to_nat (j - i)) b)) :
  is_Some (visit_freeze_sensitive l T f a).
Proof.
  destruct (visit_freeze_sensitive_is_Some' (λ _ _, True) l f a T)
    as [a' [Eq _]]; [|done..|by eexists].
  intros a1 i j b Le _. destruct (HF a1 i j b Le). by eexists.
Qed.

Lemma access1_find_granting_agree stk kind bor cids i1 i2 pm1 stk2:
  find_granting stk kind bor = Some (i1, pm1) →
  access1 stk kind bor cids = Some (i2, stk2) →
  i1 = i2.
Proof.
  intros FI. rewrite /access1 FI /=.
  destruct kind.
  - case replace_check => [? /= ?|//]. by simplify_eq/=.
  - case find_first_write_incompatible => [? /=|//].
    case remove_check => [? /= ?|//]. by simplify_eq/=.
Qed.

Lemma find_granting_write stk bor i pi:
  find_granting stk AccessWrite bor = Some (i, pi) →
  pi ≠ Disabled ∧ pi ≠ SharedReadOnly.
Proof.
  move => /fmap_Some [[??] /= [IS ?]]. simplify_eq/=.
  apply list_find_Some in IS as (? & [IS ?] & ?).
  move : IS. rewrite /grants. case perm; naive_solver.
Qed.

(* The precondition `access1_pre` is too strong for the SharedReadWrite case:
  we only need a granting item for that case, we don't need the access check. *)
Lemma grant_is_Some stk old new cids :
  let access :=
    if grants new.(perm) AccessWrite then AccessWrite else AccessRead in
  access1_pre cids stk access old →
  is_Some (grant stk old new cids).
Proof.
  intros access ACC. rewrite /grant.
  destruct (find_granting_is_Some stk access old) as [[i pi] Eqi].
  { destruct ACC as (i & it & Eqi & ND & NEq & Eqt & Lt).
    exists it. split; [by eapply list_elem_of_lookup_2|].
    do 2 (split; [done|]). intros Eqa. apply NEq. by rewrite Eqa. }
  rewrite Eqi. cbn -[item_insert_dedup].
  destruct (access1_is_Some _ _ _ _ ACC) as [[i' stk'] Eq].
  rewrite Eq. cbn -[item_insert_dedup].
  destruct new.(perm); try by eexists.
  apply find_granting_write in Eqi as [].
  destruct (find_first_write_incompatible_is_Some (take i stk) pi) as [? Eq2];
    [done..|rewrite Eq2; by eexists].
Qed.

Lemma reborrowN_is_Some α cids l n old new pm protector
  (BLK: ∀ m, (m < n)%nat → l +ₗ m ∈ dom α):
  let access := if grants pm AccessWrite then AccessWrite else AccessRead in
  (∀ (m: nat) stk, (m < n)%nat → α !! (l +ₗ m) = Some stk →
    access1_pre cids stk access old) →
  is_Some (reborrowN α cids l n old new pm protector).
Proof.
  intros access STK.
  rewrite /reborrowN. apply for_each_is_Some.
  - intros m []. rewrite -(Z2Nat.id m); [|done]. apply BLK.
    rewrite -(Nat2Z.id n) -Z2Nat.inj_lt; [done..|lia].
  - intros m stk Lt Eq. apply grant_is_Some. by apply (STK _ _ Lt Eq).
Qed.

Lemma reborrowN_lookup (α1 α2 : stacks) cids l n old new pm protector
  (EQB : reborrowN α1 cids l n old new pm protector = Some α2) :
  (∀ m, (n ≤ m)%nat → α2 !! (l +ₗ m) = α1 !! (l +ₗ m)) ∧
  (∀ m stk, (m < n)%nat → α1 !! (l +ₗ m) = Some stk →
    ∃ stk', α2 !! (l +ₗ m) = Some stk' ∧
    let item := mkItem pm new protector in
    grant stk old item cids = Some stk') ∧
  (∀ m stk', (m < n)%nat → α2 !! (l +ₗ m) = Some stk' →
    ∃ stk, α1 !! (l +ₗ m) = Some stk ∧
    let item := mkItem pm new protector in
    grant stk old item cids = Some stk').
Proof.
  destruct (for_each_lookup _ _ _ _ _ EQB) as [HL1 [HL2 HL3]]. split; last split.
  - intros m Ge. apply HL3. intros i Lt Eq%shift_loc_inj. subst. lia.
  - by apply HL1.
  - by apply HL2.
Qed.

Lemma visit_freeze_sensitive'_is_freeze {A}
  l (f: A → _ → nat → _ → _) a (last cur_dist: nat) T :
  is_freeze T →
  visit_freeze_sensitive' l f a last cur_dist T
    = Some (a, (last, (cur_dist + tsize T)%nat)).
Proof.
  apply (visit_freeze_sensitive'_elim
    (* general goal P *)
    (λ l f a last cur_dist T oalc,
      is_freeze T → oalc = Some (a, (last, (cur_dist + tsize T)%nat)))
    (λ l f _ _ _ _ a last cur_dist Ts oalc,
      is_freeze (Product Ts) →
      oalc = Some (a, (last, (cur_dist + tsize (Product Ts))%nat)))).
  - done.
  - clear. intros ??????? _. by rewrite /= Nat.add_1_r.
  - done.
  - clear. intros ??????. by move => /Is_true_eq_true ->.
  - clear. intros ?????? _. by move => /Is_true_eq_true ->.
  - clear. intros ??????. by move => /Is_true_eq_true ->.
  - clear. intros _ _ _ _ _ _ ??? _. by rewrite /= Nat.add_0_r.
  - clear. intros l f a last cur_dist Ts a' l1 c1 T Ts' IH1 IH2 FRZ.
    rewrite IH2; first rewrite /= (IH1 (a', (l1, c1 + tsize T)%nat)).
    + simpl. do 3 f_equal. change (tsize T) with (0 + tsize T)%nat.
      rewrite -(foldl_fmap_shift_init _ (λ n, n + tsize T)%nat);
        [by lia|intros ?? _; by lia].
    + by eapply is_freeze_cons_product_inv.
    + by eapply is_freeze_cons_product_inv.
Qed.

Lemma visit_freeze_sensitive_is_freeze {A}
  l (f: A → _ → nat → _ → _) a T :
  is_freeze T → visit_freeze_sensitive l T f a = f a l (tsize T) true.
Proof.
  intros FRZ. rewrite /visit_freeze_sensitive visit_freeze_sensitive'_is_freeze;
    [by rewrite shift_loc_0_nat Nat.add_0_l|done].
Qed.

Lemma reborrow_is_freeze_is_Some α cids l old T kind new prot
  (BLK: ∀ m, (m < tsize T)%nat → l +ₗ m ∈ dom α)
  (FRZ: is_freeze T)
  (STK: ∀ m stk, (m < tsize T)%nat → α !! (l +ₗ m) = Some stk →
    let access := match kind with
                  | SharedRef | RawRef false => AccessRead
                  | _ => AccessWrite
                  end in access1_pre cids stk access old) :
  is_Some (reborrow α cids l old T kind new prot).
Proof.
  rewrite /reborrow. destruct kind as [[]| |[]].
  - by apply reborrowN_is_Some.
  - by apply reborrowN_is_Some.
  - rewrite visit_freeze_sensitive_is_freeze //. by apply reborrowN_is_Some.
  - by apply reborrowN_is_Some.
  - rewrite visit_freeze_sensitive_is_freeze //. by apply reborrowN_is_Some.
Qed.

Lemma reborrow_is_freeze_lookup α cids l old T kind new prot α'
  (FRZ: is_freeze T) :
  reborrow α cids l old T kind new prot = Some α' →
  ∀ m stk', (m < tsize T)%nat → α' !! (l +ₗ m) = Some stk' →
  ∃ stk, α !! (l +ₗ m) = Some stk ∧
  let pm := match kind with
                        | SharedRef | RawRef false => SharedReadOnly
                        | UniqueRef false => Unique
                        | UniqueRef true | RawRef true => SharedReadWrite
                        end in
  let item := mkItem pm new prot in
  grant stk old item cids = Some stk'.
Proof.
  rewrite /reborrow. destruct kind as [[]| |[]]; intros EQB m stk' Lt Eq'.
  - apply reborrowN_lookup in EQB as [_ [_ HL]]. by apply HL.
  - apply reborrowN_lookup in EQB as [_ [_ HL]]. by apply HL.
  - move : EQB. rewrite visit_freeze_sensitive_is_freeze; [|done].
    move => /reborrowN_lookup [_ [_ HL]]. by apply HL.
  - apply reborrowN_lookup in EQB as [_ [_ HL]]. by apply HL.
  - move : EQB. rewrite visit_freeze_sensitive_is_freeze; [|done].
    move => /reborrowN_lookup [_ [_ HL]]. by apply HL.
Qed.


Lemma retag_ref_is_freeze_is_Some α cids nxtp l old T kind prot
  (BLK: ∀ n, (n < tsize T)%nat → l +ₗ n ∈ dom α)
  (FRZ: is_freeze T)
  (STK: ∀ m stk, (m < tsize T)%nat → α !! (l +ₗ m) = Some stk →
    let access := match kind with
                  | SharedRef | RawRef false => AccessRead
                  | _ => AccessWrite
                  end in access1_pre cids stk access old) :
  is_Some (retag_ref α cids nxtp l old T kind prot).
Proof.
  rewrite /retag_ref. destruct (tsize T) as [|sT] eqn:Eqs; [by eexists|].
  set new := match kind with
             | RawRef _ => Untagged
             | _ => Tagged nxtp
             end.
  destruct (reborrow_is_freeze_is_Some α cids l old T kind new prot)
    as [α1 Eq1]; [by rewrite Eqs|..|done| |].
  { intros m stk Lt. apply STK. by rewrite -Eqs. }
  rewrite Eq1 /=. by eexists.
Qed.

Definition valid_protector rkind (cids: call_id_set) c :=
  match rkind with | FnEntry => c ∈ cids | _ => True end.
Definition pointer_kind_access pk :=
  match pk with
  | RefPtr Mutable | RawPtr Mutable | BoxPtr => AccessWrite
  | _ => AccessRead
  end.
Definition valid_block (α: stacks) cids (l: loc) (tg: tag) pk T :=
  is_freeze T ∧
  (∀ m, (m < tsize T)%nat → l +ₗ m ∈ dom α ∧ ∃ stk,
    α !! (l +ₗ m) = Some stk ∧ access1_pre cids stk (pointer_kind_access pk) tg).

Lemma retag_is_freeze_is_Some α nxtp cids c l otg kind pk T
  (LOC: valid_block α cids l otg pk T) :
  is_Some (retag α nxtp cids c l otg kind pk T).
Proof.
  destruct LOC as (FRZ & EQD).
  destruct pk as [[]|mut|]; simpl.
  - destruct (retag_ref_is_freeze_is_Some α cids nxtp l otg T
                (UniqueRef (is_two_phase kind)) (adding_protector kind c))
      as [bac Eq]; [by apply EQD|done..| |by eexists].
    simpl. clear -EQD. intros m stk Lt Eq.
    destruct (EQD _ Lt) as [_ [stk' [Eq' ?]]]. by simplify_eq/=.
  - destruct (retag_ref_is_freeze_is_Some α cids nxtp l otg T SharedRef
                      (adding_protector kind c))
      as [bac Eq]; [by apply EQD|done..| |by eexists].
    simpl. clear -EQD. intros m stk Lt Eq.
    destruct (EQD _ Lt) as [_ [stk' [Eq' ?]]]. by simplify_eq/=.
  - destruct kind; [by eexists..| |by eexists].
    destruct (retag_ref_is_freeze_is_Some α cids nxtp l otg T
              (RawRef (bool_decide (mut = Mutable))) None)
      as [bac Eq]; [by apply EQD|done..| |by eexists].
    simpl. clear -EQD. intros m stk Lt Eq.
    destruct (EQD _ Lt) as [_ [stk' [Eq' ?]]]. simplify_eq/=. by destruct mut.
  - destruct (retag_ref_is_freeze_is_Some α cids nxtp l otg T
                          (UniqueRef false) None)
      as [bac Eq]; [by apply EQD|done..| |by eexists].
    simpl. clear -EQD. intros m stk Lt Eq.
    destruct (EQD _ Lt) as [_ [stk' [Eq' ?]]]. by simplify_eq/=.
Qed.


Lemma retag_base_step' P σ l otg ntg pk T kind c' α' nxtp':
  c' ∈ σ.(scs) →
  retag σ.(sst) σ.(snp) σ.(scs) c' l otg kind pk T =
    Some (ntg, α', nxtp') →
  let σ' := mkState σ.(shp) α' σ.(scs) nxtp' σ.(snc) in
  base_step P (Retag #[ScPtr l otg] #[ScCallId c'] pk T kind) σ #[ScPtr l ntg] σ' [].
Proof.
  econstructor. { econstructor; eauto. } simpl.
  econstructor; eauto.
Qed.

Lemma retag_base_step P σ l c otg pk T kind
  (BAR: c ∈ σ.(scs))
  (LOC: valid_block σ.(sst) σ.(scs) l otg pk T)
  (WF: state_wf σ) :
  ∃ ntg α' nxtp',
  retag σ.(sst) σ.(snp) σ.(scs) c l otg kind pk T =
    Some (ntg, α', nxtp') ∧
  let σ' := mkState σ.(shp) α' σ.(scs) nxtp' σ.(snc) in
  base_step P (Retag #[ScPtr l otg] #[ScCallId c] pk T kind) σ #[ScPtr l ntg] σ' [].
Proof.
  destruct σ as [h α cids nxtp nxtc]; simpl in *.
  destruct (retag_is_freeze_is_Some α nxtp cids c l otg kind pk T)
    as [[[h' α'] nxtp'] Eq]; [done|].
  exists h', α' , nxtp'. split; [done|].
  eapply retag_base_step'; eauto.
Qed.

(* Lemma syscall_base_step σ id :
  base_step (SysCall id) σ [SysCallEvt id] #☠ σ [].
Proof.
  have EE: ∃ σ', base_step (SysCall id) σ [SysCallEvt id] #☠ σ' [] ∧ σ' = σ.
  { eexists. split. econstructor; econstructor. by destruct σ. }
  destruct EE as [? [? ?]]. by subst.
Qed. *)
