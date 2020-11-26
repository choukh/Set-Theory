(*** Formal Construction of a Set Theory in Coq ***)
(** based on the thesis by Jonas Kaiser, November 23, 2012 **)
(** Coq coding by choukh, April 2020 **)

Require Export ZFC.ZFC1.

(*** ZFC集合论2：集合建构式，任意交，二元交，有序对，笛卡尔积 ***)

(** 集合建构式 **)
Definition Sep : set → (set → Prop) → set := λ A P,
  let F := (λ x, match (ixm (P x)) with
    | inl _ => ⎨x⎬
    | inr _ => ∅
  end) in ⋃{F | x ∊ A}.
Notation "{ x ∊ A | P }" := (Sep A (λ x, P x)).

(* 从替代公理和空集公理导出Zermelo分类公理 *)
Theorem sep_correct : ∀ A P x, x ∈ {x ∊ A | P} ↔ x ∈ A ∧ P x.
Proof with auto.
  split.
  - intros Hx. apply UnionAx in Hx as [y [Hy Hx]].
    apply ReplAx in Hy as [a [Ha Heq]]. subst y.
    destruct (ixm (P a)).
    + apply SingE in Hx. subst x...
    + exfalso0.
  - intros [Hx HP]. apply UnionAx. exists ⎨x⎬. split...
    apply ReplAx. exists x. split...
    destruct (ixm (P x))... exfalso...
Qed.

Lemma SepI : ∀ A (P : set → Prop), ∀x ∈ A, P x → x ∈ {x ∊ A | P}.
Proof. intros A P x Hx HP. apply sep_correct. auto. Qed.

Lemma SepE1 : ∀ A P, ∀x ∈ {x ∊ A | P}, x ∈ A.
Proof. intros A P x Hx. apply sep_correct in Hx. firstorder. Qed.

Lemma SepE2 : ∀ A P, ∀x ∈ {x ∊ A | P}, P x.
Proof. intros A P x Hx. apply sep_correct in Hx. firstorder. Qed.

Lemma SepE : ∀ A P, ∀x ∈ {x ∊ A | P}, x ∈ A ∧ P x.
Proof. intros A P x Hx. apply sep_correct in Hx. apply Hx. Qed.

Lemma sep_sub : ∀ A P, {x ∊ A | P} ⊆ A.
Proof. unfold Sub. exact SepE1. Qed.

Lemma sep_power : ∀ A P, {x ∊ A | P} ∈ 𝒫 A.
Proof. intros. apply PowerAx. apply sep_sub. Qed.

Lemma sep_0 : ∀ P, {x ∊ ∅ | P} = ∅.
Proof. intros. apply sub_empty. apply sep_sub. Qed.

Lemma sep_0_inv : ∀ A P, {x ∊ A | P} = ∅ -> ∀x ∈ A, ¬P x.
Proof.
  intros A P H x Hx HP.
  cut (x ∈ ∅). intros. exfalso0.
  rewrite <- H. apply SepI; auto.
Qed.

Lemma sep_sing : ∀ x P,
  ( P x ∧ {x ∊ ⎨x⎬ | P} = ⎨x⎬) ∨
  (¬P x ∧ {x ∊ ⎨x⎬ | P} = ∅).
Proof with auto.
  intros. pose proof (sep_sub ⎨x⎬ P).
  apply subset_of_single in H. destruct H.
  - rewrite H. right. split...
    eapply sep_0_inv. apply H... apply SingI.
  - rewrite H. left. split...
    apply (SepE2 ⎨x⎬). rewrite H...
Qed.

Theorem no_set_of_all_set : ¬ ∃ A, ∀ x, x ∈ A.
Proof.
  intros [A Ha].
  set {x ∊ A | λ x, x ∉ x} as B.
  destruct (classic (B ∈ B)) as [Hb|Hb].
  - apply SepE in Hb as H. destruct H as [_ H].
    apply H. apply Hb.
  - apply Hb. apply SepI. apply Ha. apply Hb.
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
  apply UnionAx in H1 as [y [Hy _]].
  split. exists y. apply Hy. apply H2.
Qed.

Fact inter_0 : ⋂ ∅ = ∅.
Proof.
  unfold Inter. rewrite union_empty. rewrite sep_0. reflexivity.
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

(* 不交 *)
Definition disjoint : set → set → Prop := λ X Y, X ∩ Y = ∅.

Lemma disjointI : ∀ A B, (¬ ∃ x, x ∈ A ∧ x ∈ B) → disjoint A B.
Proof.
  intros. apply EmptyI. intros x Hx. apply H.
  exists x. apply BInterE in Hx. apply Hx.
Qed.

Lemma disjointE : ∀ A B x, disjoint A B → x ∈ A → x ∈ B → ⊥.
Proof.
  intros * H Ha Hb. eapply EmptyE in H.
  apply H. apply BInterI; eauto.
Qed.

(* 非空集合的二元并具有单射性 *)
Lemma disjoint_bunion_injective : ∀ A B C,
  disjoint A C → disjoint B C →
  A ∪ C = B ∪ C → A = B.
Proof with auto.
  intros * Hdja Hdjb Heq.
  apply ExtAx. split; intros Hx.
  - assert (Hx': x ∈ A ∪ C) by (apply BUnionI1; auto).
    rewrite Heq in Hx'. apply BUnionE in Hx' as []...
    exfalso. apply (disjointE A C x)...
  - assert (Hx': x ∈ B ∪ C) by (apply BUnionI1; auto).
    rewrite <- Heq in Hx'. apply BUnionE in Hx' as []...
    exfalso. apply (disjointE B C x)...
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
  rewrite union_single. reflexivity. 
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

Lemma op_iff : ∀ a b c d, <a, b> = <c, d> ↔ a = c ∧ b = d.
Proof.
  split; intros.
  - pose proof (π1_correct a b).
    rewrite H in H0. rewrite π1_correct in H0.
    pose proof (π2_correct a b).
    rewrite H in H1. rewrite π2_correct in H1. auto.
  - destruct H. subst. reflexivity.
Qed.

Definition is_pair : set -> Prop := λ p, ∃ x y, p = <x, y>.

Lemma OPairI : ∀ x y, is_pair <x, y>.
Proof.
  intros. exists x, y. reflexivity.
Qed.

Hint Immediate OPairI : core.
Hint Rewrite π1_correct π2_correct : zfc_hint.
Ltac zfcrewrite := autorewrite with zfc_hint in *; try congruence.

Lemma op_η : ∀ p, is_pair p ↔ p = <π1 p, π2 p>.
Proof.
  split; intros.
  - destruct H as [a [b H]]. rewrite H. zfcrewrite.
  - rewrite H. auto.
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
  apply ReplAx in H1 as [a [H3 H4]]. subst x.
  apply ReplAx in H2 as [b [H1 H2]].
  symmetry in H2. split.
  - rewrite H2. rewrite π1_correct. apply H3.
  - rewrite H2. rewrite π2_correct. apply H1.
Qed.

Lemma CProdE2 : ∀ p A B, p ∈ A × B → is_pair p.
Proof.
  intros. apply UnionAx in H. destruct H as [x [H1 H2]].
  apply ReplAx in H1 as [a [H3 H4]]. subst x.
  apply ReplAx in H2 as [b [H1 H2]].
  exists a, b. auto.
Qed.

Lemma cprod_iff : ∀ p A B, p ∈ A × B ↔ ∃a ∈ A, ∃b ∈ B, p = <a, b>.
Proof.
  split; intros.
  - apply CProdE1 in H as H0. destruct H0 as [H1 H2].
    apply CProdE2 in H. destruct H as [a [b H]].
    rewrite H in *. rewrite π1_correct in H1.
    rewrite π2_correct in H2. firstorder.
  - destruct H as [a [H1 H2]]. destruct H2 as [b [H2 H3]].
    subst. apply CProdI. apply H1. apply H2.
Qed.

Fact cprod_0_x : ∀ B, ∅ × B = ∅.
Proof. unfold CProd. intros. rewrite funion_0. reflexivity. Qed.

Fact cprod_x_0 : ∀ A, A × ∅ = ∅.
Proof.
  intros. apply sub_empty. intros x H.
  apply CProdE1 in H. destruct H as [_ H]. exfalso0.
Qed.

Fact cprod_single_single : ∀ x, ⎨x⎬ × ⎨x⎬ = ⎨<x, x>⎬.
Proof with auto.
  intros. apply ExtAx. split; intros Hx.
  - apply cprod_iff in Hx as [a [Ha [b [Hb Hx]]]].
    apply SingE in Ha. apply SingE in Hb. subst...
  - apply SingE in Hx. subst. apply CProdI...
Qed.
