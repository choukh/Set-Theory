(** Coq coding by choukh, Jan 2021 **)

Require Import ZFC.Axiom.ZFC2.

(* Epsilon-induction *)
(* https://en.wikipedia.org/wiki/Epsilon-induction *)

(**=== Epsilon归纳原理 ===**)
(* 对于集合的任意性质P，如果可以通过证明"集合A的所有成员都具有性质P"来证明A具有性质P，
  那么所有集合都具有性质P。 *)
Axiom ε_ind : ∀ P : set → Prop,
  (∀ A, (∀a ∈ A, P a) → P A) → ∀ A, P A.

Lemma not_all_not_iff_ex : ∀ P : set → Prop, ¬ (∀ A, ¬ P A) ↔ (∃ A, P A).
Proof. split. exact (not_all_not_ex _ P). firstorder. Qed.

Lemma not_all_iff_ex_not : ∀ P : set → Prop, ¬ (∀ A, P A) ↔ (∃ A, ¬ P A).
Proof. split. exact (not_all_ex_not _ P). firstorder. Qed.

(** ∈归纳原理蕴含正则公理模式 **)
Theorem reg_schema : ∀ P,
  (∃ A, P A) → ∃ A, P A ∧ ¬∃x ∈ A, P x.
Proof.
  intros P.
  pose proof (ε_ind (λ x, ¬ P x)). simpl in H.
  remember (∀ A, (∀x ∈ A, ¬ P x) → ¬ P A) as R.
  remember (∀ A, ¬ P A) as S.
  assert (∀ P Q: Prop, (P → Q) → (¬ Q → ¬ P)) by auto.
  pose proof (H0 R S H). subst. clear H H0.  
  rewrite not_all_not_iff_ex in H1.
  rewrite not_all_iff_ex_not in H1.
  intros. apply H1 in H. destruct H as [A H].
  exists A. clear H1.
  assert (∀ A B : Prop, ¬ (A → ¬ B) ↔ ¬¬B ∧ ¬¬A) by firstorder.
  rewrite H0 in H. clear H0. destruct H.
  apply NNPP in H. apply NNPP in H0. firstorder.
Qed.

(* 由正则公理模式导出原始正则公理：
  所有非空集合X中至少有一个成员x，它与X的交集为空集。*)
Theorem regularity : ∀ A, A ≠ ∅ → ∃a ∈ A, a ∩ A = ∅.
Proof.
  intros A Hne. apply EmptyNE in Hne.
  pose proof (reg_schema (λ x, x ∈ A)).
  simpl in H. apply H in Hne.
  destruct Hne as [x [H1 H2]].
  exists x. split. apply H1.
  apply EmptyI. intros y H3.
  apply H2. apply BInterE in H3.
  exists y. apply H3.
Qed.

(* 不存在以自身为元素的集合 *)
Theorem not_self_contained : ¬ ∃ x, x ∈ x.
Proof.
  intros H.
  pose proof (reg_schema (λ x, x ∈ x)).
  simpl in H0. apply H0 in H.
  destruct H as [x [H1 H2]].
  apply H2. exists x. split; auto.
Qed.

(* 没有循环单链 *)
Lemma well_founded_1 : ∀ X, X ∉ X.
Proof.
  intros X. pose proof (ε_ind (λ X, X ∉ X)). simpl in H.
  apply H. intros. intros Ht. apply H0 in Ht as Hf. auto.
Qed.

(* 没有循环双链 *)
Lemma well_founded_2 : ∀ X Y, X ∈ Y → Y ∉ X.
Proof.
  intros X Y H. pose proof (ε_ind (λ X, ∀ Y, X ∈ Y → Y ∉ X)).
  apply H0; [|apply H]. clear X Y H H0.
  intros X H Y H1 H2.
  pose proof (H Y H2 X H2). auto.
Qed.

(* 没有循环三链 *)
Lemma well_founded_3 : ∀ X Y Z, X ∈ Y → Y ∈ Z → Z ∉ X.
Proof.
  intros X Y Z H. pose proof (ε_ind (λ X, ∀ Y Z, X ∈ Y → Y ∈ Z → Z ∉ X)).
  apply H0; [|apply H]. clear X Y Z H H0.
  intros X H Y Z H1 H2 H3.
  pose proof (H Z H3 X Y H3 H1). auto.
Qed.
