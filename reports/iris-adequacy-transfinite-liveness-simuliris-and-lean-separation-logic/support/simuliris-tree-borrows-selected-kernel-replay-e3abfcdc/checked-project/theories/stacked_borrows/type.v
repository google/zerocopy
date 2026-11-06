(** This file has been adapted from the Stacked Borrows development, available at 
  https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From Stdlib Require Import Program ssreflect.
From stdpp Require Export list countable.
From simuliris.stacked_borrows Require Export helpers.



Inductive mutability := Mutable | Immutable.
Inductive ref_kind :=
  | UniqueRef (two_phase: bool) (* `&mut` and `Box` *)
  | SharedRef (* `&`, with or without interior mutability *)
  | RawRef (mutable: bool) (* `*mut`/`*const`, raw pointers *)
  .
Inductive pointer_kind :=
  RefPtr (mut: mutability) | RawPtr (mut: mutability) | BoxPtr.

(* We never induct on this type since it uses [list.]
So disable schemes since we do not need them, but generating them causes warnings. *)
#[schemes=none]
Inductive type :=
  | FixedSize (sz: nat)
  | Reference (kind: pointer_kind) (T: type)
  | Unsafe (T: type)
  | Union (Ts: list type)
  | Product (Ts: list type)
  | Sum (Ts: list type)
  .
Declare Scope lrust_type.
Delimit Scope lrust_type with T.
Bind Scope lrust_type with type.


(** Types that don't contain UnsafeCells. *)
Fixpoint is_freeze (T: type) : bool :=
  match T with
  | FixedSize _ | Reference _ _ => true
  | Unsafe _ => false
  | Union Ts | Product Ts | Sum Ts => forallb is_freeze Ts
  end.

Lemma is_freeze_cons_product_inv T Ts:
  is_freeze (Product (T :: Ts)) →
  is_freeze T ∧ is_freeze (Product Ts).
Proof. by rewrite /= andb_True. Qed.

Lemma is_freeze_cons_sum_inv T Ts:
  is_freeze (Sum (T :: Ts)) →
  is_freeze T ∧ is_freeze (Sum Ts).
Proof. by rewrite /= andb_True. Qed.

(** Physical size of types *)
Fixpoint list_nat_max (ns: list nat) (d: nat) :=
  match ns with
  | [] => d
  | n :: ns => n `max` ((list_nat_max ns) d)
  end.

Lemma list_nat_max_spec ns :
  ns = [] ∧ list_nat_max ns O = O ∨
  list_nat_max ns O ∈ ns ∧ ∀ (i: nat), i ∈ ns → (i ≤ list_nat_max ns O)%nat.
Proof.
  induction ns as [|i ns IHi]; simpl; [rewrite elem_of_nil; naive_solver|].
  right. destruct IHi as [[]|[In MAX]].
  - subst. rewrite /= Nat.max_0_r list_elem_of_singleton.
    setoid_rewrite list_elem_of_singleton. naive_solver.
  - split.
    + apply Nat.max_case; [by left|by right].
    + move => i' /elem_of_cons [->|In']; first by apply Nat.le_max_l.
      etrans; first by apply MAX. apply Nat.le_max_r.
Qed.

Fixpoint tsize (T: type) : nat :=
  match T with
  | FixedSize sz => sz
  | Reference _ _ => 1%nat     (* We do not go beyond pointers *)
  | Unsafe T => tsize T
  | Union Ts => list_nat_max (tsize <$> Ts) O
  | Product Ts => foldl (λ sz T, sz + tsize T)%nat O Ts
  | Sum Ts => 1 + list_nat_max (tsize <$> Ts) O
  end.

Lemma tsize_product_cons T Ts :
  (tsize (Product (T :: Ts)) = tsize T + tsize (Product Ts))%nat.
Proof.
  rewrite /= -{1}(Nat.add_0_r (tsize T)). remember O as n eqn:Heqn. clear Heqn.
  revert n. induction Ts as [|Tc Ts IH]; intros n; [done|].
  by rewrite /= -Nat.add_assoc IH.
Qed.

Lemma tsize_subtype_of_product T Ts :
  T ∈ Ts → (tsize T ≤ tsize (Product Ts))%nat.
Proof.
  induction Ts as [|Tc Ts IH]; [by intros ?%not_elem_of_nil|].
  rewrite tsize_product_cons. move => /elem_of_cons [->|/IH]; lia.
Qed.

Lemma tsize_subtype_of_sum T Ts :
  T ∈ Ts → (S (tsize T) ≤ tsize (Sum Ts))%nat.
Proof.
  induction Ts as [|Tc Ts IH]; [by intros ?%not_elem_of_nil|].
  move => /elem_of_cons [->/=|/IH]; [lia|cbn; lia].
Qed.

Lemma tsize_sum_cons_le T Ts :
  tsize (Sum Ts) ≤ tsize (Sum (T :: Ts)).
Proof. cbn. lia. Qed.

(** Tree size of types *)
Fixpoint tnode_size (T: type) : nat :=
  match T with
  | FixedSize sz => 1%nat
  | Reference _ T => 1 + tnode_size T
  | Unsafe T => 1 + tnode_size T
  | Union Ts | Product Ts | Sum Ts =>
    1 + foldl (λ sz T, sz + 1 + (tnode_size T)) O Ts
  end.

Lemma foldl_inner_init_le {A} (fL: nat → nat) (fR: A → nat) (la: list A)
  (Le: ∀ n, n ≤ fL n) :
  ∀ n, n ≤ foldl (λ sz a, fL sz + fR a)%nat n la.
Proof.
  induction la as [|a0 la IH]; [done|]. move => n /=.
  etrans; [|eapply IH]. etrans; [apply Le|]. lia.
Qed.

Lemma tnode_size_elem_of T Ts (IN: T ∈ Ts):
  ∀ n, (tnode_size T < 1 + foldl (λ sz T, sz + 1 + (tnode_size T)) n Ts)%nat.
Proof.
  induction Ts as [|Tc Ts IH]; intros n;
    [exfalso; move : IN ; apply not_elem_of_nil|].
  move : IN => /elem_of_cons [->|/IH Lt].
  - rewrite Nat.add_comm -(Nat.add_0_r (tnode_size Tc)).
    apply Nat.add_le_lt_mono; [|lia]. simpl.
    etrans; [|apply foldl_inner_init_le]; intros; lia.
  - apply Lt.
Qed.

Lemma tnode_size_elem_of_union T Ts :
  T ∈ Ts → (tnode_size T < tnode_size (Union Ts))%nat.
Proof. intros ?. by apply tnode_size_elem_of. Qed.
Lemma tnode_size_elem_of_product T Ts :
  T ∈ Ts → (tnode_size T < tnode_size (Product Ts))%nat.
Proof. intros ?. by apply tnode_size_elem_of. Qed.
Lemma tnode_size_elem_of_sum T Ts :
  T ∈ Ts → (tnode_size T < tnode_size (Sum Ts))%nat.
Proof. intros ?. by apply tnode_size_elem_of. Qed.

Section type_general_ind.
Variable (P : type → Prop)
         (F1: ∀ sz, P (FixedSize sz))
         (F2: ∀ kind T, P T → P (Reference kind T))
         (F3: ∀ T, P T → P (Unsafe T))
         (F4: ∀ Ts, (∀ T, T ∈ Ts → P T) → P (Union Ts))
         (F5: ∀ Ts, (∀ T, T ∈ Ts → P T) → P (Product Ts))
         (F6: ∀ Ts, (∀ T, T ∈ Ts → P T) → P (Sum Ts)).
Program Fixpoint type_elim
         (T: type) {measure (tnode_size T)} : P T :=
    match T with
    | FixedSize sz => F1 sz
    | Reference kind T => F2 kind T (type_elim T)
    | Unsafe T => F3 T (type_elim T)
    | Union Ts => F4 Ts (λ T (IN: T ∈ Ts), type_elim T)
    | Product Ts => F5 Ts (λ T (IN: T ∈ Ts), type_elim T)
    | Sum Ts => F6 Ts (λ T (IN: T ∈ Ts), type_elim T)
    end.
Next Obligation. move=> ? _ ?? <- /=. lia. Qed.
Next Obligation. move=> ? _ ? <- /=. lia. Qed.
Next Obligation. naive_solver eauto using tnode_size_elem_of_union. Qed.
Next Obligation. naive_solver eauto using tnode_size_elem_of_product. Qed.
Next Obligation. naive_solver eauto using tnode_size_elem_of_sum. Qed.
Next Obligation. apply well_founded_ltof. Qed.
End type_general_ind.

(** Decidability *)

Global Instance type_inhabited : Inhabited type := populate (FixedSize 0).

Global Instance mutability_eq_dec : EqDecision mutability.
Proof. solve_decision. Defined.
Global Instance mutability_countable : Countable mutability.
Proof.
  refine (inj_countable'
    (λ m, match m with Mutable => 0 | Immutable => 1 end)
    (λ x, match x with 0 => Mutable | _ => Immutable end) _); by intros [].
Qed.

Global Instance pointer_kind_eq_dec : EqDecision pointer_kind.
Proof. solve_decision. Defined.
Global Instance pointer_kind_countable : Countable pointer_kind.
Proof.
  refine (inj_countable
          (λ k, match k with
              | RefPtr mut => inl $ inl mut
              | RawPtr mut => inl $ inr mut
              | BoxPtr => inr ()
              end)
          (λ s, match s with
              | inl (inl mut) => Some $ RefPtr mut
              | inl (inr mut) => Some $ RawPtr mut
              | inr _ => Some BoxPtr
              end) _); by intros [].
Qed.

Fixpoint type_beq (T T': type) : bool :=
  let fix type_list_beq Ts Ts' :=
    match Ts, Ts' with
    | [], [] => true
    | T::Ts, T'::Ts' => type_beq T T' && type_list_beq Ts Ts'
    | _, _ => false
    end
  in
  match T, T' with
  | FixedSize n, FixedSize n' => bool_decide (n = n')
  | Reference k T, Reference k' T' => bool_decide (k = k') && type_beq T T'
  | Unsafe T, Unsafe T' => type_beq T T'
  | Union Ts, Union Ts' | Product Ts, Product Ts' | Sum Ts, Sum Ts' =>
      type_list_beq Ts Ts'
  | _, _ => false
  end.
Lemma type_beq_correct (T1 T2 : type) : type_beq T1 T2 ↔ T1 = T2.
Proof.
  revert T1 T2; fix FIX 1; intros T1 T2;
    destruct T1 as [| | |Ts1|Ts1|Ts1],
             T2 as [| | |Ts2|Ts2|Ts2];
    simpl; try done;
    rewrite ?andb_True ?bool_decide_spec ?FIX;
    try (split; intro; [destruct_and?|split_and?]; congruence).
  - match goal with |- context [?F Ts1 Ts2] => assert (F Ts1 Ts2 ↔ Ts1 = Ts2) end.
    { revert Ts2. induction Ts1 as [|Ts1h Ts1q]; intros Ts2; destruct Ts2; try done.
      specialize (FIX Ts1h). naive_solver. }
    clear FIX. naive_solver.
  - match goal with |- context [?F Ts1 Ts2] => assert (F Ts1 Ts2 ↔ Ts1 = Ts2) end.
    { revert Ts2. induction Ts1 as [|Ts1h Ts1q]; intros Ts2; destruct Ts2; try done.
      specialize (FIX Ts1h). naive_solver. }
    clear FIX. naive_solver.
  - match goal with |- context [?F Ts1 Ts2] => assert (F Ts1 Ts2 ↔ Ts1 = Ts2) end.
    { revert Ts2. induction Ts1 as [|Ts1h Ts1q]; intros Ts2; destruct Ts2; try done.
      specialize (FIX Ts1h). naive_solver. }
    clear FIX. naive_solver.
Qed.
Global Instance type_eq_dec : EqDecision type.
Proof.
  refine (λ T1 T2, cast_if (decide (type_beq T1 T2))); by rewrite -type_beq_correct.
Defined.
Global Instance type_countable : Countable type.
Proof.
  refine (inj_countable'
    (fix go T := match T with
     | FixedSize sz => GenNode 0 [GenLeaf $ inl sz]
     | Reference kind T => GenNode 1 [GenLeaf $ inr kind; go T]
     | Unsafe T => GenNode 2 [go T]
     | Union Ts => GenNode 3 (go <$> Ts)
     | Product Ts => GenNode 4 (go <$> Ts)
     | Sum Ts => GenNode 5 (go <$> Ts)
     end)
    (fix go s := match s with
     | GenNode 0 [GenLeaf (inl sz)] => FixedSize sz
     | GenNode 1 [GenLeaf (inr kind); T] => Reference kind (go T)
     | GenNode 2 [T] => Unsafe (go T)
     | GenNode 3 Ts => Union (go <$> Ts)
     | GenNode 4 Ts => Product (go <$> Ts)
     | GenNode 5 Ts => Sum (go <$> Ts)
     | _ => FixedSize 0
     end) _).
  fix FIX 1. intros [| | |Ts|Ts|Ts]; csimpl; f_equal=>//; revert Ts; clear -FIX.
  - fix FIX_INNER 1. intros []; [done|]. by f_equal/=.
  - fix FIX_INNER 1. intros []; [done|]. by f_equal/=.
  - fix FIX_INNER 1. intros []; [done|]. by f_equal/=.
Qed.

(** Finding sum types *)
Fixpoint sub_sum_types' (T : type) (cur: nat) : list (nat * type) :=
  match T with
  | Unsafe T => sub_sum_types' T cur
  | Union Ts => foldl (λ ns T, ns ++ sub_sum_types' T cur) [] Ts
  | Sum Ts =>
      [(cur, Sum Ts)] ++ foldl (λ ns T, ns ++ sub_sum_types' T (cur + 1)) [] Ts
  | Product Ts =>
      (foldl (λ sns T, ((sns.1 + tsize T)%nat, sns.2 ++ sub_sum_types' T sns.1))
             (cur, []) Ts).2
  | _ => []
  end.

Definition sub_sum_types T := sub_sum_types' T O.

Lemma sub_sum_types_O_elem_of Ts : (O, Sum Ts) ∈ sub_sum_types (Sum Ts).
Proof. by left. Qed.

Lemma foldl_inner_app_fmap {A B} (f: B → list A) (g: A → A) la0 lb :
  g <$> (foldl (λ la b, la ++ f b) la0 lb)
  = foldl (λ la b, la ++ (g <$> f b)) (g <$> la0) lb.
Proof.
  revert la0. induction lb as [|b lb IH]; move => la0; [done|].
  by rewrite /= IH fmap_app.
Qed.

Lemma sub_sum_type'_shift T n m:
  sub_sum_types' T (n + m) = (λ nT, ((nT.1 + m)%nat, nT.2)) <$> sub_sum_types' T n.
Proof.
  revert n.
  apply (type_elim (λ T, ∀ n, sub_sum_types' T _ = _ <$> sub_sum_types' T _)).
  - done.
  - done.
  - done.
  - intros ? IH n. simpl.
    rewrite (foldl_fun_ext
              (λ ns T0, ns ++ sub_sum_types' T0 (n + m))
              (λ ns T0, ns ++
                ((λ nT, ((nT.1 + m)%nat, nT.2)) <$> sub_sum_types' T0 n))).
    + by rewrite foldl_inner_app_fmap.
    + by move => ?? /IH ->.
  - intros ? IH n. simpl.
    set g : nat * list (nat * type) → nat * list (nat * type) :=
      λ sns, ((λ n, n + m)%nat sns.1, (λ nT, ((nT.1 + m)%nat, nT.2)) <$> sns.2).
    change ((n + m)%nat, []) with (g (n, [])).
    rewrite -foldl_fmap_shift_init //.
    move => ?? /IH IH1. rewrite /g /=. f_equal; [lia|by rewrite fmap_app IH1].
  - intros ? IH n. cbn.
    rewrite (foldl_fun_ext
              (λ ns T0, ns ++ sub_sum_types' T0 (n + m + 1))
              (λ ns T0, ns ++
                ((λ nT, ((nT.1 + m)%nat, nT.2)) <$> sub_sum_types' T0 (n + 1)))).
    + by rewrite foldl_inner_app_fmap.
    + move => ?? /IH IH1. rewrite (_: (n + m + 1) = (n + 1) + m)%nat; last lia.
      by rewrite IH1.
Qed.

Lemma foldl_inner_app_elem_of {A B} (f: B → list A) la0 lb :
  ∀ a, a ∈ foldl (λ la b, la ++ f b) la0 lb → a ∈ la0 ∨ ∃ b, b ∈ lb ∧ a ∈ f b.
Proof.
  revert la0. induction lb as [|b lb IH]; move => la0 a; [by left|].
  move => /IH [/elem_of_app[|]|[b' [? ?]]]; [by left|right..].
  - exists b. split; [by left|done].
  - exists b'. split; [by right|done].
Qed.

Lemma foldl_inner_app_not_nil {A B} (f: B → list A) lb :
  foldl (λ la b, la ++ f b) [] lb ≠ [] → ∃ b, b ∈ lb ∧ f b ≠ [].
Proof.
  destruct (foldl (λ la b, la ++ f b) [] lb) as [|a la] eqn:Eq; [done|].
  move => _.
  destruct (foldl_inner_app_elem_of f [] lb a) as [IN|[b [? ?%elem_of_not_nil]]].
  - rewrite Eq. by left.
  - exfalso. move : IN. by apply not_elem_of_nil.
  - by exists b.
Qed.

Lemma foldl_inner_app_elem_of_2 {A B C}
  (fL: C → B → C) (fR: B → C → list A) c0 la0 lb :
  ∀ a, a ∈ (foldl (λ cla b, (fL cla.1 b, cla.2 ++ fR b cla.1)) (c0, la0) lb).2 →
  a ∈ la0 ∨ ∃ b c, b ∈ lb ∧ a ∈ fR b c.
Proof.
  revert c0 la0. induction lb as [|b lb IH]; move => c0 la0 a; [by left|].
  move => /IH [/elem_of_app[|]|[b' [c' [? ?]]]]; [by left|right..].
  - exists b, c0. split; [by left|done].
  - exists b', c'. split; [by right|done].
Qed.

Lemma foldl_inner_app_not_nil_2 {A B C}
  (fL: C → B → C) (fR: B → C → list A) c lb :
  (foldl (λ cla b, (fL cla.1 b, cla.2 ++ fR b cla.1)) (c, []) lb).2 ≠ [] →
  ∃ b c, b ∈ lb ∧ fR b c ≠ [].
Proof.
  destruct ((foldl (λ cla b, (fL cla.1 b, cla.2 ++ fR b cla.1)) (c, []) lb).2)
    as [|a la] eqn:Eq; [done|]. move => _.
  destruct (foldl_inner_app_elem_of_2 fL fR c [] lb a)
    as [IN|[b [c' [? ?%elem_of_not_nil]]]].
  - rewrite Eq. by left.
  - exfalso. move : IN. by apply not_elem_of_nil.
  - by exists b, c'.
Qed.

Lemma sub_sum_types_ne T :
  sub_sum_types T ≠ [] →
  match T with
  | Unsafe T => sub_sum_types T ≠ []
  | Union Ts | Product Ts => ∃ Tc, Tc ∈ Ts ∧ sub_sum_types Tc ≠ []
  | Sum Ts => True
  | _ => False
  end.
Proof.
  destruct T; [done..| | |done].
  - by rewrite /sub_sum_types /= => /foldl_inner_app_not_nil.
  - rewrite /sub_sum_types /= =>
            /(foldl_inner_app_not_nil_2
                (λ n T0, (n + tsize T0))%nat (sub_sum_types')) [Tc [c [?]]].
    rewrite -(Nat.add_0_l c) sub_sum_type'_shift => NE.
    exists Tc. split; [done|] => NIL. apply NE. by rewrite NIL.
Qed.

Lemma foldl_inner_app_elem_of_init_2 {A B C}
  (fL: C → B → C) (fR: B → C → list A) c0 la0 lb :
  ∀ a, a ∈ la0 →
  a ∈ (foldl (λ cla b, (fL cla.1 b, cla.2 ++ fR b cla.1)) (c0, la0) lb).2.
Proof.
  revert c0 la0. induction lb as [|b lb IH]; move => c0 la0 a INa /=; [done|].
  apply IH. rewrite elem_of_app. by left.
Qed.

Lemma sub_sum_types_product_first T Tc Ts n :
  (n, T) ∈ sub_sum_types Tc → (n, T) ∈ sub_sum_types (Product (Tc :: Ts)).
Proof.
  rewrite /sub_sum_types /=.
  by apply (foldl_inner_app_elem_of_init_2
              (λ n T0, (n + tsize T0))%nat (sub_sum_types')).
Qed.

Fact sub_sum_types_foldl n m (la lb: list (nat * type)) (Ts: list type) :
  let lR :=
    (foldl (λ sns T0, (sns.1 + tsize T0, sns.2 ++ sub_sum_types' T0 sns.1))
             (n, lb) Ts) in
  (foldl (λ sns T0, (sns.1 + tsize T0, sns.2 ++ sub_sum_types' T0 sns.1))
        (n + m, la ++ ((λ nT, (nT.1 + m, nT.2)) <$> lb)) Ts)
  = (lR.1 + m, la ++ ((λ nT, (nT.1 + m, nT.2)) <$> lR.2)).
Proof.
  revert n lb. induction Ts as [|T Ts IH]; intros n lb; [done|].
  revert IH. simpl. intros IH.
  rewrite sub_sum_type'_shift -app_assoc -fmap_app.
  rewrite (_: n + m + tsize T = (n + tsize T) + m)%nat; last lia.
  by rewrite (IH (n + tsize T)).
Qed.

Lemma sub_sum_types_product_further T Tc Ts n :
  (n, T) ∈ sub_sum_types (Product Ts) →
  (tsize Tc + n, T) ∈ sub_sum_types (Product (Tc :: Ts)).
Proof.
  rewrite /sub_sum_types /= => IN.
  rewrite -(app_nil_r (sub_sum_types' Tc 0)) -{2}(Nat.add_0_l (tsize Tc))
          (_: [] = (λ nT: nat * type, (nT.1 + (tsize Tc), nT.2)) <$> []) //.
  rewrite sub_sum_types_foldl /= elem_of_app.
  right. simpl. apply list_elem_of_fmap.
  exists (n, T). by rewrite Nat.add_comm /=.
Qed.

Lemma foldl_inner_app_elem_of_init {A B}
  (f: list A → B → list A) la0 lb :
  ∀ a, a ∈ la0 → a ∈ (foldl (λ a b, a ++ f a b)) la0 lb.
Proof.
  revert la0. induction lb as [|b lb IH]; move => la0 a INa /=; [done|].
  apply IH. rewrite elem_of_app. by left.
Qed.

Lemma sub_sum_types_sum_first T Tc Ts n :
  (n, T) ∈ sub_sum_types Tc → (S n, T) ∈ sub_sum_types (Sum (Tc :: Ts)).
Proof.
  rewrite /sub_sum_types /= => IN. right.
  apply foldl_inner_app_elem_of_init.
  rewrite -(Nat.add_0_l 1) sub_sum_type'_shift -Nat.add_1_r list_elem_of_fmap.
  by exists (n, T).
Qed.

Lemma foldl_inner_init_lt {A} (fL: nat → nat) (fR: A → nat) (la: list A)
  (MONO: ∀ n m, n < m → fL n < fL m) :
  ∀ n m, n < m →
  foldl (λ sz a, fL sz + fR a)%nat n la < foldl (λ sz a, fL sz + fR a)%nat m la.
Proof.
  induction la as [|a0 la IH]; [done|]. move => n m Lt /=.
  by apply IH, Nat.add_lt_mono_r, MONO.
Qed.

Lemma tnode_size_product_cons_lt Tc Ts :
  tnode_size (Product Ts) < tnode_size (Product (Tc :: Ts)).
Proof. cbn. rewrite -Nat.succ_lt_mono. apply foldl_inner_init_lt; [intros|]; lia. Qed.

Lemma tnode_size_sum_cons_lt Tc Ts :
  tnode_size (Sum Ts) < tnode_size (Sum (Tc :: Ts)).
Proof. cbn. rewrite -Nat.succ_lt_mono. apply foldl_inner_init_lt; [intros|]; lia. Qed.

Lemma sub_sum_types'_le n m Tc T: (n, Tc) ∈ sub_sum_types' T m → m ≤ n.
Proof.
  rewrite -{1}(Nat.add_0_l m) sub_sum_type'_shift list_elem_of_fmap =>
          [[[??] [? ?]]]. simplify_eq. simpl. lia.
Qed.

Lemma sub_sum_types_sum_eq Ts1 Ts2 :
  (0, Sum Ts1) ∈ sub_sum_types (Sum Ts2) → Ts1 = Ts2.
Proof.
  rewrite /sub_sum_types /= elem_of_cons => [[?|]]; [by simplify_eq|].
  intros [?%not_elem_of_nil|[? [? IN%sub_sum_types'_le]]]%foldl_inner_app_elem_of;
    [done|lia].
Qed.

Lemma sub_sum_types_elem_of n T Ts:
  (n, T) ∈ sub_sum_types (Sum Ts) →
  (n = 0 ∧ T = Sum Ts) ∨ (0 < n ∧ ∃ Tc, Tc ∈ Ts ∧ (n - 1, T) ∈ sub_sum_types Tc).
Proof.
  rewrite {1}/sub_sum_types /= elem_of_cons => [[?|]]; [simplify_eq; by left|].
  intros [?%not_elem_of_nil|[Tc [IN1 IN2]]]%foldl_inner_app_elem_of; [done|right].
  move : IN2. rewrite -(Nat.add_0_l 1) sub_sum_type'_shift list_elem_of_fmap.
  move => [[n1 T'] [Eq IN2]]. simplify_eq. simpl. split; [lia|].
  exists Tc. split; [done|]. by rewrite Nat.add_sub.
Qed.

Lemma foldl_inner_app_elem_of_inv {A B} (f: B → list A) la0 lb :
  ∀ a, a ∈ foldl (λ la b, la ++ f b) la0 lb ↔ a ∈ la0 ∨ ∃ b, b ∈ lb ∧ a ∈ f b.
Proof.
  revert la0. induction lb as [|b lb IH]; move => la0 a.
  { simpl. setoid_rewrite elem_of_nil. naive_solver. }
  rewrite /= IH elem_of_app. setoid_rewrite elem_of_cons. naive_solver.
Qed.

Lemma sub_sum_types_elem_of_2 n T Ts:
  (n, T) ∈ sub_sum_types (Sum Ts) ↔
  (n = 0 ∧ T = Sum Ts) ∨ (0 < n ∧ ∃ Tc, Tc ∈ Ts ∧ (n - 1, T) ∈ sub_sum_types Tc).
Proof.
  split; first by apply sub_sum_types_elem_of.
  rewrite {1}/sub_sum_types /=. intros [IN|IN].
  - destruct IN. subst. by left.
  - cbn. right. rewrite foldl_inner_app_elem_of_inv. right.
    destruct IN as [Gt0 [Tc [IN1 IN2]]]. exists Tc. split; [done|].
    rewrite -(Nat.add_0_l 1) sub_sum_type'_shift list_elem_of_fmap.
    exists (n - 1, T). split; [|done]. simpl. f_equal. lia.
Qed.

Lemma sub_sum_types_sum_further Tn Tc Ts n :
  0 < n →
  (n, Sum Tn) ∈ sub_sum_types (Sum Ts) →
  (n, Sum Tn) ∈ sub_sum_types (Sum (Tc :: Ts)).
Proof.
  intros Gt0. rewrite 2!sub_sum_types_elem_of_2.
  intros [[? _]|(_ & Tc' & IN1 & IN2)]; [subst; by lia|]. right.
  split; [done|]. exists Tc'. split; [by right|done].
Qed.

(** Finding ref types *)
Fixpoint sub_ref_types' (T : type) (cur: nat) : list (nat * type) :=
  match T with
  | Reference pk Tref => [(cur, Reference pk Tref)]
  | Unsafe T => sub_ref_types' T cur
  | Union Ts => foldl (λ ns T, ns ++ sub_ref_types' T cur) [] Ts
  | Sum Ts => foldl (λ ns T, ns ++ sub_ref_types' T (cur + 1)) [] Ts
  | Product Ts =>
      (foldl (λ sns T, ((sns.1 + tsize T)%nat, sns.2 ++ sub_ref_types' T sns.1))
             (cur, []) Ts).2
  | _ => []
  end.

Definition sub_ref_types T := sub_ref_types' T O.

Lemma sub_ref_types_O_elem_of pk T :
  (O, Reference pk T) ∈ sub_ref_types (Reference pk T).
Proof. by left. Qed.

Lemma sub_ref_type'_shift T n m:
  sub_ref_types' T (n + m) = (λ nT, ((nT.1 + m)%nat, nT.2)) <$> sub_ref_types' T n.
Proof.
  revert n.
  apply (type_elim (λ T, ∀ n, sub_ref_types' T _ = _ <$> sub_ref_types' T _)).
  - done.
  - done.
  - done.
  - intros ? IH n. simpl.
    rewrite (foldl_fun_ext
              (λ ns T0, ns ++ sub_ref_types' T0 (n + m))
              (λ ns T0, ns ++
                ((λ nT, ((nT.1 + m)%nat, nT.2)) <$> sub_ref_types' T0 n))).
    + by rewrite foldl_inner_app_fmap.
    + by move => ?? /IH ->.
  - intros ? IH n. simpl.
    set g : nat * list (nat * type) → nat * list (nat * type) :=
      λ sns, ((λ n, n + m)%nat sns.1, (λ nT, ((nT.1 + m)%nat, nT.2)) <$> sns.2).
    change ((n + m)%nat, []) with (g (n, [])).
    rewrite -foldl_fmap_shift_init //.
    move => ?? /IH IH1. rewrite /g /=. f_equal; [lia|by rewrite fmap_app IH1].
  - intros ? IH n. cbn.
    rewrite (foldl_fun_ext
              (λ ns T0, ns ++ sub_ref_types' T0 (n + m + 1))
              (λ ns T0, ns ++
                ((λ nT, ((nT.1 + m)%nat, nT.2)) <$> sub_ref_types' T0 (n + 1)))).
    + by rewrite foldl_inner_app_fmap.
    + move => ?? /IH IH1. rewrite (_: (n + m + 1) = (n + 1) + m)%nat; last lia.
      by rewrite IH1.
Qed.

Lemma sub_ref_types_product_first T Ts n :
  n ∈ sub_ref_types T → n ∈ sub_ref_types (Product (T :: Ts)).
Proof.
  rewrite /sub_ref_types /=.
  by apply (foldl_inner_app_elem_of_init_2
              (λ n T0, (n + tsize T0))%nat (sub_ref_types'  )).
Qed.

Fact sub_ref_types_foldl n m (la lb: list (nat * type)) (Ts: list type) :
  let lR :=
    (foldl (λ sns T0, (sns.1 + tsize T0, sns.2 ++ sub_ref_types' T0 sns.1))
             (n, lb) Ts) in
  (foldl (λ sns T0, (sns.1 + tsize T0, sns.2 ++ sub_ref_types' T0 sns.1))
        (n + m, la ++ ((λ nT, (nT.1 + m, nT.2)) <$> lb)) Ts)
  = (lR.1 + m, la ++ ((λ nT, (nT.1 + m, nT.2)) <$> lR.2)).
Proof.
  revert n lb. induction Ts as [|T Ts IH]; intros n lb; [done|].
  revert IH. simpl. intros IH.
  rewrite sub_ref_type'_shift -app_assoc -fmap_app.
  rewrite (_: n + m + tsize T = (n + tsize T) + m)%nat; last lia.
  by rewrite (IH (n + tsize T)).
Qed.

Lemma sub_ref_types_product_further T Ts Tr pk n :
  (n, Reference pk Tr) ∈ sub_ref_types (Product Ts) →
  (tsize T + n, Reference pk Tr)%nat ∈ sub_ref_types (Product (T :: Ts)).
Proof.
  rewrite /sub_ref_types /= => IN .
  rewrite -(app_nil_r (sub_ref_types' T 0)) -{2}(Nat.add_0_l (tsize T))
          (_: [] = (λ nT: nat * type, (nT.1 + (tsize T), nT.2)) <$> []) //.
  rewrite sub_ref_types_foldl /= elem_of_app.
  right. simpl. apply list_elem_of_fmap.
  exists (n, Reference pk Tr). by rewrite Nat.add_comm /=.
Qed.

Lemma sub_ref_types_sum_first T Tc Ts n :
  (n, T) ∈ sub_ref_types Tc → (S n, T) ∈ sub_ref_types (Sum (Tc :: Ts)).
Proof.
  rewrite /sub_ref_types /= => IN.
  apply foldl_inner_app_elem_of_init.
  rewrite -(Nat.add_0_l 1) sub_ref_type'_shift -Nat.add_1_r list_elem_of_fmap.
  by exists (n, T).
Qed.

Lemma sub_ref_types_sum_further T Tc Ts n :
  (n, T) ∈ sub_ref_types (Sum Ts) → (n, T) ∈ sub_ref_types (Sum (Tc :: Ts)).
Proof.
  rewrite /sub_ref_types /= 2!foldl_inner_app_elem_of_inv.
  intros [?%not_elem_of_nil|]; [done|by right].
Qed.
