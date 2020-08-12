(*** Formal Construction of a Set Theory in Coq ***)
(** based on the thesis by Jonas Kaiser, November 23, 2012 **)
(** Coq coding by choukh, April 2020 **)

Require Export ZFC.ZFC1.

(*** ZFC集合论2：集合建构式，任意交，二元交，有序对，笛卡尔积 ***)

(** 集合建构式 **)
Definition Sep : set → (set → Prop) → set := λ X P,
  ε (inhabits ∅) (λ Z, ∀ x, x ∈ Z ↔ x ∈ X ∧ P x).
Notation "{ x ∊ X | P }" := (Sep X (λ x, P x)).

(* 用ε算子，从替代公理和空集公理导出Zermelo分类公理 *)
Theorem sep_correct : ∀ X P x, x ∈ {x ∊ X | P} ↔ x ∈ X ∧ P x.
Proof.
  intros X P. unfold Sep. apply ε_spec.
  destruct (classic (∃x ∈ X, P x)).
  - destruct H as [x0 [H1 H2]].
    set (F_spec := λ x y, (P x ∧ x = y) ∨ (~ P x ∧ x0 = y)).
    set (F := λ x, ε (inhabits ∅) (F_spec x)).
    assert (F_tauto: ∀ x, F_spec x (F x)). {
      intros. unfold F. apply ε_spec.
      unfold F_spec. destruct (classic (P x)).
      - exists x. left. auto.
      - exists x0. right. auto.
    }
    assert (A: ∀ x,   P x → x  = F x) by firstorder.
    assert (B: ∀ x, ~ P x → x0 = F x) by firstorder.
    exists {F | x ∊ X}. split; intros.
    + apply ReplE in H... destruct H as [x' [H3 H4]].
      destruct (classic (P x')).
      * apply A in H as H5. rewrite H4 in H5.
        rewrite <- H5. auto.
      * apply B in H as H5. rewrite H4 in H5.
        rewrite <- H5. auto.
    + apply ReplAx... destruct H as [H3 H4].
      apply A in H4. exists x. split; auto.
  - exists ∅. firstorder using EmptyE.
Qed.

Lemma SepI : ∀ X (P : set → Prop), ∀x ∈ X, P x → x ∈ {x ∊ X | P}.
Proof. intros X P x Hx HP. apply sep_correct. auto. Qed.

Lemma SepE1 : ∀ X P, ∀x ∈ {x ∊ X | P}, x ∈ X.
Proof. intros X P x Hx. apply sep_correct in Hx. firstorder. Qed.

Lemma SepE2 : ∀ X P, ∀x ∈ {x ∊ X | P}, P x.
Proof. intros X P x Hx. apply sep_correct in Hx. firstorder. Qed.

Lemma SepE : ∀ X P, ∀x ∈ {x ∊ X | P}, x ∈ X ∧ P x.
Proof. intros X P x Hx. apply sep_correct in Hx. apply Hx. Qed.

Lemma sep_sub : ∀ X P, {x ∊ X | P} ⊆ X.
Proof. unfold Sub. exact SepE1. Qed.

Lemma sep_power : ∀ X P, {x ∊ X | P} ∈ 𝒫 X.
Proof. intros. apply PowerAx. apply sep_sub. Qed.

Lemma sep_0 : ∀ P, {x ∊ ∅ | P} = ∅.
Proof. intros. apply sub_0_iff_0. apply sep_sub. Qed.

Lemma sep_0_inv : ∀ X P, {x ∊ X | P} = ∅ -> ∀x ∈ X, ¬P x.
Proof.
  intros X P H x Hx HP.
  cut (x ∈ ∅). intros. exfalso0.
  rewrite <- H. apply SepI; auto.
Qed.

Lemma sep_sing : ∀ x P,
  ( P x ∧ {x ∊ ⎨x⎬ | P} = ⎨x⎬) ∨
  (¬P x ∧ {x ∊ ⎨x⎬ | P} = ∅).
Proof with auto.
  intros. pose proof (sep_sub ⎨x⎬ P).
  apply sub_sing in H. destruct H.
  - rewrite H. right. split...
    eapply sep_0_inv. apply H. apply SingI.
  - rewrite H. left. split...
    apply (SepE2 ⎨x⎬). rewrite H. apply SingI.
Qed.

(** 任意交 **)
Definition Inter : set -> set :=
  λ Y, {x ∊ ⋃Y | (λ x, ∀y ∈ Y, x ∈ y)}.
Notation "⋂ X" := (Inter X) (at level 9, right associativity).

Lemma InterI : ∀ x Y, ⦿ Y → (∀y ∈ Y, x ∈ y) → x ∈ ⋂Y.
Proof.
  intros x Y H H0.
  destruct H as [y H]. apply SepI.
  - eapply UnionI. apply H. apply H0. apply H.
  - apply H0.
Qed.

Lemma InterE : ∀ Y, ∀x ∈ ⋂Y, ⦿Y ∧ ∀y ∈ Y, x ∈ y.
Proof.
  intros Y x Hx. apply SepE in Hx as [H1 H2].
  apply UnionE1 in H1. split; auto.
Qed.

Fact inter_0 : ⋂ ∅ = ∅.
Proof.
  unfold Inter. rewrite union_0_0. rewrite sep_0. reflexivity.
Qed.

(** 二元交 **)
Definition BInter : set → set → set := λ X Y, ⋂{X, Y}.
Notation "X ∩ Y" := (BInter X Y) (at level 49).

Lemma BInterI : ∀ x X Y, x ∈ X → x ∈ Y → x ∈ X ∩ Y.
Proof.
  intros. apply InterI.
  - exists X. apply PairI1.
  - intros y Hy. apply PairE in Hy. destruct Hy.
    + subst. apply H.
    + subst. apply H0.
Qed.

Lemma BInterE : ∀ X Y, ∀x ∈ X ∩ Y, x ∈ X ∧ x ∈ Y.
Proof.
  intros H Y x Hx. apply InterE in Hx as [_ Hx]. split.
  - apply Hx. apply PairI1.
  - apply Hx. apply PairI2.
Qed.

Example inter_self_0 : ∀ a, a ∩ a = ∅ → a = ∅.
Proof.
  intros. apply EmptyI. intros x H1.
  pose proof ((EmptyE H) x).
  apply H0. apply BInterI; apply H1.
Qed.

Example inter_eq_0_e : ∀ a b, ⦿a → a ∩ b = ∅ → a ≠ b.
Proof.
  unfold not. intros. subst.
  apply inter_self_0 in H0.
  destruct H as [x H]. subst. exfalso0.
Qed.

(** 有序对 **)
Definition OPair : set → set → set := λ x y, {⎨x⎬, {x, y}}.
Notation "< x , y , .. , z >" :=
  ( OPair .. ( OPair x y ) .. z ) (z at level 69).

Definition π1 : set → set := λ p, ⋃ ⋂ p.
Definition π2 : set → set := λ p,
  ⋃ {x ∊ ⋃p | λ x, x ∈ ⋂p → ⋃p = ⋂p}.

Lemma op_union : ∀ x y, ⋃<x, y> = {x, y}.
Proof.
  intros. apply ExtAx. intros a. split; intros.
  - apply UnionAx in H.
    destruct H as [A [H1 H2]].
    apply PairE in H1. destruct H1.
    + rewrite H in H2. apply SingE in H2.
      subst. apply PairI1.
    + rewrite H in H2. apply H2.
  - unfold OPair. apply PairE in H. destruct H.
    + subst. apply BUnionI1. apply SingI.
    + subst. apply BUnionI2. apply PairI2.
Qed.

Lemma op_inter : ∀ x y, ⋂<x, y> = ⎨x⎬.
Proof.
  intros. apply ExtAx. intros a. split; intros.
  - apply InterE in H as [_ H].
    apply H. apply PairI1.
  - apply SingE in H. subst. apply InterI.
    + exists ⎨x⎬. apply PairI1.
    + intros z Hz. apply PairE in Hz. destruct Hz.
      * subst. apply SingI.
      * subst. apply PairI1.
Qed.

Lemma π1_correct : ∀ x y, π1 <x, y> = x.
Proof.
  unfold π1. intros. rewrite op_inter.
  rewrite union_sing_x_x. reflexivity. 
Qed.

Lemma pair_eq_pair_i : ∀ a b c d, {a, b} = {c, d} ->
  (a = c ∧ b = d) ∨ (a = d ∧ b = c).
Proof.
  intros.
  assert (a ∈ {c, d}). rewrite <- H. apply PairI1.
  assert (b ∈ {c, d}). rewrite <- H. apply PairI2.
  assert (c ∈ {a, b}). rewrite H. apply PairI1.
  assert (d ∈ {a, b}). rewrite H. apply PairI2.
  apply PairE in H0. apply PairE in H1.
  apply PairE in H2. apply PairE in H3.
  destruct H0, H1, H2, H3; auto.
Qed.

Lemma sing_eq_pair_i : ∀ a b c, ⎨a⎬ = {b, c} → a = b ∧ a = c.
Proof. intros. apply pair_eq_pair_i in H. firstorder. Qed.

Lemma pair_eq_sing_i : ∀ a b c, {b, c} = ⎨a⎬ → a = b ∧ a = c.
Proof.
  intros. apply eq_sym in H.
  apply sing_eq_pair_i. apply H.
Qed.

Lemma sing_eq_sing_i : ∀ a b, ⎨a⎬ = ⎨b⎬ → a = b.
Proof. intros. apply sing_eq_pair_i in H. firstorder. Qed.

Lemma π2_correct : ∀ x y, π2 <x, y> = y.
Proof.
  unfold π2. intros.
  rewrite op_union in *.
  rewrite op_inter in *.
  apply ExtAx. intros a. split; intros.
  - apply UnionAx in H... destruct H as [A [H1 H2]].
    apply SepE in H1 as [H3 H4].
    apply PairE in H3. destruct H3.
    + subst. pose proof (H4 (SingI x)).
      apply pair_eq_sing_i in H as [_ H].
      subst. apply H2.
    + subst. apply H2.
  - eapply UnionI; [|apply H].
    apply SepI. apply PairI2.
    intros. apply SingE in H0. subst. reflexivity.
Qed.

Lemma op_correct : ∀ a b c d, <a, b> = <c, d> ↔ a = c ∧ b = d.
Proof.
  split; intros.
  - pose proof (π1_correct a b).
    rewrite H in H0. rewrite π1_correct in H0.
    pose proof (π2_correct a b).
    rewrite H in H1. rewrite π2_correct in H1. auto.
  - destruct H. subst. reflexivity.
Qed.

Definition is_pair : set -> Prop := λ p, ∃ x y, p = <x, y>.

Lemma op_η : ∀ p, is_pair p ↔ p = <π1 p, π2 p>.
Proof.
  split; intros.
  - destruct H as [a [b H]]. rewrite H.
    rewrite π1_correct. rewrite π2_correct. reflexivity.
  - exists (π1 p), (π2 p). apply H.
Qed.

(** 笛卡儿积 **)
Definition CProd : set → set → set := λ A B,
  ⋃ {λ a, {λ b, <a, b> | x∊B} | x∊A}.
Notation "A × B" := (CProd A B) (at level 40).

Lemma CProdI : ∀ A B, ∀a ∈ A, ∀b ∈ B, <a, b> ∈ A × B.
Proof.
  intros A B a Ha b Hb. eapply UnionI.
  - apply ReplI. apply Ha.
  - apply ReplI. apply Hb.
Qed.

Lemma CProdE1 : ∀ p A B, p ∈ A × B → π1 p ∈ A ∧ π2 p ∈ B.
Proof.
  intros. apply UnionAx in H. destruct H as [x [H1 H2]].
  apply ReplE in H1. destruct H1 as [a [H3 H4]].
  subst x. apply ReplE in H2. destruct H2 as [b [H1 H2]].
  symmetry in H2. split.
  - rewrite H2. rewrite π1_correct. apply H3.
  - rewrite H2. rewrite π2_correct. apply H1.
Qed.

Lemma CProdE2 : ∀ p A B, p ∈ A × B → is_pair p.
Proof.
  intros. apply UnionAx in H. destruct H as [x [H1 H2]].
  apply ReplE in H1. destruct H1 as [a [H3 H4]].
  subst x. apply ReplE in H2. destruct H2 as [b [H1 H2]].
  exists a, b. auto.
Qed.

Lemma CProd_correct : ∀ p A B, p ∈ A × B ↔ ∃a ∈ A, ∃b ∈ B, p = <a, b>.
Proof.
  split; intros.
  - apply CProdE1 in H as H0. destruct H0 as [H1 H2].
    apply CProdE2 in H. destruct H as [a [b H]].
    rewrite H in *. rewrite π1_correct in H1.
    rewrite π2_correct in H2. firstorder.
  - destruct H as [a [H1 H2]]. destruct H2 as [b [H2 H3]].
    subst. apply CProdI. apply H1. apply H2.
Qed.

Example cprod_0_x : ∀ B, ∅ × B = ∅.
Proof. unfold CProd. intros. rewrite funion_0. reflexivity. Qed.

Example cprod_x_0 : ∀ A, A × ∅ = ∅.
Proof.
  intros. apply sub_0_iff_0. intros x H.
  apply CProdE1 in H. destruct H as [_ H]. exfalso0.
Qed.
