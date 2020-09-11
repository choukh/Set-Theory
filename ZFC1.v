(*** Formal Construction of a Set Theory in Coq ***)
(** based on the thesis by Jonas Kaiser, November 23, 2012 **)
(** Coq coding by choukh, April 2020 **)

Require Export ZFC.ZFC0.

(*** ZFC集合论1：配对，单集，二元并，集族的并 ***)

Definition Doubleton : set := 𝒫 𝒫 ∅.

Lemma DoubletonI1 : ∅ ∈ Doubleton.
Proof. apply PowerAx. intros x Hx. exfalso0. Qed.

Lemma DoubletonI2 : 𝒫 ∅ ∈ Doubleton.
Proof.
  apply PowerAx. intros x Hx.
  apply only_empty_in_power_empty in Hx.
  subst. apply empty_in_all_power.
Qed.

Definition PairRepl : set → set → set → set := λ a b x,
  match (ixm (∅ ∈ x)) with
  | inl _ => b
  | inr _ => a
  end.

(** 配对 **)
Definition Pair : set → set → set := λ x y,
  {PairRepl x y | w ∊ Doubleton}.
Notation "{ x , y }" := (Pair x y).

Lemma PairI1 : ∀ x y, x ∈ {x, y}.
Proof.
  intros. apply ReplAx. exists ∅. split.
  - apply DoubletonI1.
  - unfold PairRepl. destruct (ixm (∅ ∈ ∅)).
    + exfalso0.
    + reflexivity.
Qed.

Lemma PairI2 : ∀ x y, y ∈ {x, y}.
Proof.
  intros. apply ReplAx. exists (𝒫 ∅). split.
  - apply DoubletonI2.
  - unfold PairRepl. destruct (ixm (∅ ∈ 𝒫 ∅)).
    + reflexivity.
    + exfalso. apply n. apply empty_in_all_power. 
Qed.

Lemma PairE : ∀ x y, ∀w ∈ {x, y}, w = x ∨ w = y.
Proof.
  intros x y w Hw. apply ReplAx in Hw as [z [_ Heq]].
  unfold PairRepl in Heq. destruct (ixm (∅ ∈ z)).
  - subst. right. reflexivity.
  - subst. left. reflexivity.
Qed.

(* 配对是顺序无关的 *)
Theorem pair_ordering_agnostic : ∀ a b, {a, b} = {b, a}.
Proof.
  intros. apply ExtAx.
  split; intros.
  - apply PairE in H.
    destruct H as [H1|H2].
    + subst x. apply PairI2.
    + subst x. apply PairI1.
  - apply PairE in H.
    destruct H as [H1|H2].
    + subst x. apply PairI2.
    + subst x. apply PairI1.
Qed.

(** 单集 **)
Definition Singleton : set → set := λ x, {x, x}.
Notation "⎨ x ⎬" := (Singleton x).

Lemma SingI : ∀ x, x ∈ ⎨x⎬.
Proof. unfold Singleton. intros. apply PairI1. Qed.
Hint Immediate SingI : core.

Lemma SingE : ∀ x y, x ∈ ⎨y⎬ → x = y.
Proof.
  intros. apply PairE in H.
  destruct H; apply H.
Qed.

Lemma SingNI : ∀ A B, A ≠ B → A ∉ ⎨B⎬.
Proof.
  intros * Hnq H. apply Hnq. apply SingE in H. apply H.
Qed.

Lemma SingNE : ∀ A B, A ∉ ⎨B⎬ → A ≠ B.
Proof.
  intros * H Heq. apply H. subst A. apply SingI.
Qed.

Declare Scope ZFC1_scope.
Delimit Scope ZFC1_scope with zfc1.
Open Scope ZFC1_scope.

(* 壹 *)
Definition One := ⎨∅⎬.
Notation "1" := One : ZFC1_scope.

Lemma OneI1 : ∅ ∈ 1.
Proof. apply SingI. Qed.

Lemma OneI2 : ∀ A, A = ∅ → A ∈ 1.

Proof. intros. subst. apply OneI1. Qed.
Lemma OneE : ∀ A, A ∈ 1 → A = ∅.
Proof. intros. apply SingE. apply H. Qed.

Example empty_neq_one : ∅ ≠ 1.
Proof.
  intros H. eapply ExtAx in H.
  destruct H as [_ H].
  pose proof (H OneI1).
  eapply EmptyAx. apply H0.
Qed.

(* 贰 *)
Definition Two := {∅, 1}.
Notation "2" := Two : ZFC1_scope.

Lemma TwoI1 : ∅ ∈ 2.
Proof. apply PairI1. Qed.

Lemma TwoI2 : 1 ∈ 2.
Proof. apply PairI2. Qed.

Lemma TwoI3 : ∀ A, A = ∅ ∨ A = 1 → A ∈ 2.
Proof.
  intros A [H1|H2].
  - subst. apply TwoI1.
  - subst. apply TwoI2.
  
  Qed.
Lemma TwoE : ∀ A, A ∈ 2 → A = ∅ ∨ A = 1.
Proof. intros. apply PairE. apply H. Qed.

(* 更多引理 *)

Lemma in_impl_sing_sub : ∀ X, ∀x ∈ X, ⎨x⎬ ⊆ X.
Proof.
  intros X x Hx y Hy.
  apply SingE in Hy. subst. apply Hx.
Qed.

Lemma sing_char : ∀ X, ∀ x ∈ X, (∀ y ∈ X, x = y) → X = ⎨x⎬.
Proof.
  intros X x Hx H.
  apply ExtAx. split; intros.
  - apply H in H0. subst. apply SingI.
  - apply SingE in H0. subst. apply Hx.
Qed.

Lemma sub_sing : ∀ x A, A ⊆ ⎨x⎬ → A = ∅ ∨ A = ⎨x⎬.
Proof.
  intros. destruct (empty_or_inh A).
  - left. apply H0.
  - right. destruct H0 as [a Ha].
    unfold Sub in H...
    apply sing_char...
    + apply H in Ha as Hs. apply SingE in Hs.
      subst. apply Ha.
    + intros b Hb.
      apply H in Hb. apply SingE in Hb. auto.
Qed.

Lemma sub_1 : ∀ A, A ⊆ 1 -> A = ∅ ∨ A = 1.
Proof. apply sub_sing. Qed.

Lemma empty_1_2_0 : ∀ O I, O ∈ I → I ∈ 2 → O = ∅.
Proof.
  intros. apply EmptyI. unfold not. intros.
  apply TwoE in H0.
  destruct H0.
  - subst. eapply EmptyAx. apply H.
  - subst. apply OneE in H.
    subst. eapply EmptyAx. apply H1.
Qed.

Lemma in_2_inh_1 : ∀S ∈ 2, ⦿ S → S = 1.
Proof.
  intros S HS Hi.
  apply TwoE in HS. destruct HS.
  - subst. destruct Hi. exfalso0.
  - apply H.
Qed.

Example union_sing_x_x : ∀ X, ⋃ ⎨X⎬ = X.
Proof.
  intros. apply ExtAx. split; intros.
  - apply UnionAx in H as [a [H1 H2]].
    apply SingE in H1. subst. apply H2.
  - eapply UnionI. apply SingI. apply H.
Qed.

Example union_1_0 : ⋃ 1 = ∅.
Proof. exact (union_sing_x_x ∅). Qed.

Example in_2_impl_union_0 : ∀ X, X ∈ 2 → ⋃ X = ∅.
Proof.
  intros. apply TwoE in H. destruct H.
  - subst. apply union_0_0.
  - subst. apply union_1_0.
Qed.

Example union_2_1 : ⋃ 2 = 1.
Proof.
  apply ExtAx. split; intro.
  - apply UnionAx in H as [a [H1 H2]].
    apply TwoE in H1 as [].
    + rewrite H in H2. exfalso0.
    + subst. apply H2.
  - eapply UnionI. apply TwoI2. apply H.
Qed.

Example power_0_1 : 𝒫 ∅ = 1.
Proof.
  apply ExtAx. split; intros.
  - apply PowerAx in H. apply OneI2.
    apply sub_0_iff_0. apply H.
  - apply PowerAx. apply OneE in H.
    subst. apply sub_0_iff_0. reflexivity.
Qed.

Example power_1_2 : 𝒫 1 = 2.
Proof.
  apply ExtAx. split; intros.
  - apply PowerAx in H.
    apply TwoI3. apply sub_1. apply H.
  - apply PowerAx. apply TwoE in H. destruct H; subst.
    + intros x H. exfalso0.
    + apply sub_refl.
Qed.

(** 二元并 **)
Definition BUnion : set → set → set := λ X Y, ⋃{X, Y}.
Notation "X ∪ Y" := (BUnion X Y) (at level 50).

Lemma BUnionI1 : ∀ w X Y, w∈X → w ∈ X∪Y.
Proof.
  intros. apply UnionI with X.
  - apply PairI1.
  - apply H.
Qed.

Lemma BUnionI2 : ∀ w X Y, w∈Y → w ∈ X∪Y.
Proof.
  intros. apply UnionI with Y.
  - apply PairI2.
  - apply H.
Qed.

Lemma BUnionE : ∀ w X Y, w ∈ X∪Y → w∈X ∨ w∈Y.
Proof.
  intros. apply UnionAx in H.
  destruct H as [z [H1 H2]].
  apply PairE in H1.
  destruct H1 ; subst; auto.
Qed.

(** 集族的并 **)

Lemma FUnionI : ∀ X F, ∀x ∈ X, ∀y ∈ F x, y ∈ ⋃{F|x ∊ X}.
Proof.
  intros X F x Hx y Hy. eapply UnionI.
  - apply ReplI. apply Hx.
  - apply Hy.
Qed.

Lemma FUnionE : ∀ X F, ∀y ∈ ⋃{F|x ∊ X}, ∃x ∈ X, y ∈ F x.
Proof.
  intros X F y Hy.
  apply UnionAx in Hy as [x [H1 H2]].
  apply ReplAx in H1 as [z [H3 H4]].
  exists z. split. apply H3. subst. apply H2.
Qed. 

Example funion_0 : ∀ F, ⋃{F|x ∊ ∅} = ∅.
Proof. intros. rewrite repl_empty. apply union_0_0. Qed.

Example funion_1 : ∀ X F,
  (∀x ∈ X, F x ∈ 2) → (∃x ∈ X, F x = 1) → ⋃{F|x ∊ X} = 1.
Proof.
  intros. assert (∀ x ∈ ⋃{F | x ∊ X}, x = ∅). {
    intros x Hx. apply FUnionE in Hx as [y [H1 H2]].
    apply H in H1.
    eapply empty_1_2_0. apply H2. apply H1.
  }
  apply ExtAx. split; intros.
  - apply H1 in H2. subst. apply OneI1.
  - apply UnionAx. exists 1. split.
    + apply ReplAx in H0. apply H0. 
    + apply H2.
Qed.

Example funion_const : ∀ X F C,
  ⦿ X → (∀x ∈ X, F x = C) → ⋃{F|x ∊ X} = C.
Proof.
  intros. apply ExtAx. split; intros.
  - apply FUnionE in H1. destruct H1 as [y [H1 H2]].
    apply H0 in H1. subst. auto.
  - destruct H as [y H]. eapply FUnionI.
    apply H. apply H0 in H. subst. auto.
Qed.

Example funion_const_0 : ∀ X F, 
  (∀x ∈ X, F x = ∅) → ⋃{F|x ∊ X} = ∅.
Proof.
  intros. destruct (empty_or_inh X).
  - subst. apply funion_0.
  - exact (funion_const X F ∅ H0 H).
Qed.

Example funion_2 : ∀ X F, 
  (∀x ∈ X, F x ∈ 2) → ⋃{F|x ∊ X} ∈ 2.
Proof.
  intros. destruct (classic (∃x ∈ X, F x = 1)).
  - pose proof (funion_1 X F H H0) as H1.
    rewrite H1. apply TwoI2.
  - assert (∀x ∈ X, F x = ∅). {
      intros x Hx. apply H in Hx as H2.
      apply TwoE in H2. destruct H2; firstorder. 
    }
    pose proof (funion_const_0 X F H1).
    rewrite H2. apply TwoI1.
Qed.

Close Scope ZFC1_scope.
