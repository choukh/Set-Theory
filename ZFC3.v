(*** Formal Construction of a Set Theory in Coq ***)
(** based on the thesis by Jonas Kaiser, November 23, 2012 **)
(** Coq coding by choukh, April 2020 **)

Require Export ZFC.ZFC2.
Require Import Setoid.

(*** ZFC集合论3：无穷公理，选择公理，正则公理 ***)

(* 后续运算 *)
Definition Suc : set → set := λ a, a ∪ ⎨a⎬.
Notation "a ⁺" := (Suc a) (at level 8).

(* 归纳集 *)
Definition inductive : set → Prop := λ A,
  ∅ ∈ A ∧ ∀a ∈ A, a⁺ ∈ A.

(**=== 公理6: 无穷公理 ===**)
Parameter 𝐈 : set. 
Axiom InfAx : inductive 𝐈.

(** 希尔伯特ε算子等效于选择公理 **)

(* 选择函数 *)
Definition cho : set → set := λ s, ε (inhabits ∅) (λ x, x ∈ s).

(* “答案确实是在题目选项里选的” *)
Lemma chosen_contained : ∀ s, ⦿s → cho s ∈ s.
Proof. intros s. exact (ε_spec (inhabits ∅) (λ x, x ∈ s)). Qed.

(* “答案集包含在问题集的并集里” *)
Theorem chosen_included : ∀ S, (∀s ∈ S, ⦿s) → {cho | s ∊ S} ⊆ ⋃S.
Proof.
  intros S H x Hx.
  apply ReplE in Hx as [s [H1 H2]].
  eapply UnionI. apply H1.
  apply H in H1. subst.
  apply chosen_contained. apply H1.
Qed.

(* “单选题” *)
Theorem one_chosen : ∀ S, (∀s ∈ S, ⦿s) →
  (∀ s t ∈ S, s ≠ t → s ∩ t = ∅) →
  ∀s ∈ S, ∃ x, s ∩ {cho | s ∊ S} = ⎨x⎬.
Proof.
  intros S Hi Hdj s Hs.
  exists (cho s).
  apply sub_asym.
  - intros x Hx. apply BInterE in Hx as [Hx1 Hx2].
    cut (x = cho s).
    + intros. subst. apply SingI.
    + apply ReplE in Hx2.
      destruct Hx2 as [t [Ht Hteq]].
      destruct (classic (s = t)).
      * subst. reflexivity.
      * pose proof (Hdj s Hs t Ht H).
        pose proof ((EmptyE H0) x).
        exfalso. apply H1. apply BInterI. apply Hx1.
        pose proof (chosen_contained t (Hi t Ht)).
        rewrite Hteq in H2. apply H2.
  - apply in_impl_sing_sub. apply BInterI.
    + apply chosen_contained. apply Hi. apply Hs.
    + apply ReplI. apply Hs.
Qed.

(* 更多经典逻辑引理 *)
(* Library Coq.Logic.Classical_Pred_Type *)

Lemma double_negation : ∀ P : Prop, ¬¬P ↔ P.
Proof.
  split; intros.
  - destruct (classic P) as [HP | HF]; firstorder.
  - destruct (classic (¬P)) as [HF | HFF]; firstorder.
Qed.

Lemma not_all_not_ex : ∀ P : set → Prop, ¬ (∀ X, ¬ P X) ↔ (∃ X, P X).
Proof.
  split; intros.
  - destruct (classic (∃ X, P X)); firstorder.
  - firstorder.
Qed.

Lemma not_all_ex_not : ∀ P : set → Prop, ¬ (∀ X, P X) ↔ (∃ X, ¬ P X).
Proof.
  intros. pose proof (not_all_not_ex (λ x, ¬ P x)).
  simpl in H. rewrite <- H. clear H.
  split; intros.
  - intros H1. apply H. intros. specialize H1 with X.
    rewrite double_negation in H1. apply H1.
  - firstorder.
Qed.

(**=== 公理7: ∈归纳原理 ===**)
(* 对于集合的任意性质P，如果可以通过证明"集合A的所有成员都具有性质P"来证明A具有性质P，
  那么所有集合都具有性质P。 *)
Axiom ε_ind : ∀ P : set → Prop,
  (∀ A, (∀a ∈ A, P a) → P A) → ∀ A, P A.

(** ∈归纳原理等效于正则公理模式 **)
Theorem reg_schema : ∀ P,
  (∃ X, P X) → ∃ X, P X ∧ ¬∃x ∈ X, P x.
Proof.
  intros P. pose proof (ε_ind (λ x, ¬ P x)). simpl in H.
  remember (∀ X, (∀x ∈ X, ¬ P x) → ¬ P X) as A.
  remember (∀ X, ¬ P X) as B.
  assert (∀ P Q: Prop, (P → Q) → (¬ Q → ¬ P)) by auto.
  pose proof (H0 A B H). subst. clear H H0.
  rewrite not_all_not_ex in H1.
  rewrite not_all_ex_not in H1.
  intros. apply H1 in H. destruct H as [X H].
  exists X. clear H1.
  assert (∀ A B : Prop, ¬ (A → ¬ B) ↔ ¬¬B ∧ ¬¬A) by firstorder.
  rewrite H0 in H. clear H0.
  repeat rewrite double_negation in H. firstorder.
Qed.

(* 由正则公理模式导出原始正则公理：
  所有非空集合X中至少有一个成员x，它与X的交集为空集。*)
Theorem regularity : ∀ X, ⦿ X → ∃x ∈ X, x ∩ X = ∅.
Proof.
  intros.
  pose proof (reg_schema (λ x, x ∈ X)).
  simpl in H0. apply H0 in H.
  destruct H as [x [H1 H2]].
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
