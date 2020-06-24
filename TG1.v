(*** Formal Construction of a Set Theory in Coq ***)
(** based on the thesis by Jonas Kaiser, November 23, 2012 **)
(** Coq coding by choukh, April 2020 **)

Require Export ZFC.TG0.

(*** TG集合论扩展1：单集，壹，贰 ***)

(** 单集 **)
Definition Sing : set → set := λ x, {x, x}.
Notation "⎨ x ⎬" := (Sing x).

Lemma SingI : ∀ x, x ∈ ⎨x⎬.
Proof. unfold Sing. intros. apply PairI1. Qed.

Lemma SingE : ∀ x y, x ∈ ⎨y⎬ → x = y.
Proof.
  intros. apply PairE in H.
  destruct H; apply H.
Qed.

Lemma GUSing : ∀ N X, X ∈ 𝒰(N) → Sing X ∈ 𝒰(N).
Proof.
  intros. unfold Sing.
  apply GUPair; apply H.
Qed.

Declare Scope one_two_scope.
Open Scope one_two_scope.

(** 壹 **)
Definition One := ⎨∅⎬.
Notation "1" := One : one_two_scope.

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
Notation "2" := Two : one_two_scope.

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

(** 各种引理 **)

Lemma in_impl_sing_sub : ∀ X, ∀x ∈ X, ⎨x⎬ ⊆ X.
Proof.
  unfold Sub. introq.
  apply SingE in H0. subst. apply H.
Qed.

Lemma sub_0_iff_0 : ∀ A, A ⊆ ∅ ↔ A = ∅.
Proof.
  split; intros.
  - apply EmptyI. unfold not. intros.
    apply H in H0. eapply EmptyAx. apply H0.
  - subst. intros x H. apply H.
Qed.

Lemma empty_or_inh : ∀ A, A = ∅ ∨ ⦿A.
Proof.
  intros. destruct (classic (A = ∅)).
  - left. apply H.
  - right. apply EmptyNE. apply H.  
Qed.

Lemma sing_char : ∀ X, ∀ x ∈ X, (∀ y ∈ X, x = y) → X = ⎨x⎬.
Proof.
  unfoldq. intros X x Hx H.
  apply ExtAx. split; intros.
  - apply H in H0. subst. apply SingI.
  - apply SingE in H0. subst. apply Hx.
Qed.

Lemma sub_sing : ∀ x A, A ⊆ ⎨x⎬ → A = ∅ ∨ A = ⎨x⎬.
Proof with unfoldq.
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
  introq.
  apply TwoE in H. destruct H.
  - apply EmptyNI in H0. subst.
    exfalso. apply H0. reflexivity.
  - apply H.
Qed.

(** 各种练习 **)

Example union_0_0 : ⋃∅ = ∅.
Proof.
  apply ExtAx. split.
  - intros. apply UnionE1 in H.
    destruct H as [a H]. exfalso0.
  - intros. exfalso0.
Qed.

Example union_sing_x_x : ∀ X, ⋃ ⎨X⎬ = X.
Proof.
  intros. apply ExtAx. split; intros.
  - apply UnionAx in H. unfoldq.
    destruct H as [a [H1 H2]].
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
  - apply UnionAx in H. unfoldq.
    destruct H as [a [H1 H2]].
    apply TwoE in H1.
    destruct H1.
    + rewrite H in H2. exfalso0.
    + subst. apply H2.
  - eapply UnionI. apply TwoI2. apply H.
Qed.

Example power_0_1 : 𝒫(∅) = 1.
Proof.
  apply ExtAx. split; intros.
  - apply PowerAx in H. apply OneI2.
    apply sub_0_iff_0. apply H.
  - apply PowerAx. apply OneE in H.
    subst. apply sub_0_iff_0. reflexivity.
Qed.

Example power_1_2 : 𝒫(1) = 2.
Proof.
  apply ExtAx. split; intros.
  - apply PowerAx in H.
    apply TwoI3. apply sub_1. apply H.
  - apply PowerAx. apply TwoE in H. destruct H; subst.
    + intros x H. exfalso0.
    + apply sub_refl.
Qed.

Lemma repl0I : ∀ F, {F | x ∊ ∅} = ∅.
Proof.
  intros. apply EmptyI.
  intros x H. apply ReplE in H. unfoldq.
  destruct H as [y [H _]]. exfalso0.
Qed.

Lemma repl0E : ∀ F X, {F | x ∊ X} = ∅ → X = ∅.
Proof.
  intros. apply sub_0_iff_0. intros x Hx.
  eapply ReplI in Hx. rewrite H in Hx. exfalso0.
Qed.
