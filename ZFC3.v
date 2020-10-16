(*** Formal Construction of a Set Theory in Coq ***)
(** based on the thesis by Jonas Kaiser, November 23, 2012 **)
(** Coq coding by choukh, April 2020 **)

Require Export ZFC.ZFC2.

(*** ZFC集合论3：无穷公理，选择公理，正则公理 ***)

(* 后续运算 *)
Definition Suc : set → set := λ a, a ∪ ⎨a⎬.
Notation "a ⁺" := (Suc a) (at level 8).

Lemma suc_has_n : ∀ n, n ∈ n⁺.
Proof. intros. apply BUnionI2. apply SingI. Qed.

Lemma suc_inc_n : ∀ n, n ⊆ n⁺.
Proof. intros n x Hx. apply BUnionI1. apply Hx. Qed.

Lemma suc_neq_0 : ∀ n, n⁺ ≠ ∅.
Proof.
  intros n H. eapply EmptyE in H. apply H. apply suc_has_n.
Qed.

(* 归纳集 *)
Definition inductive : set → Prop := λ A,
  ∅ ∈ A ∧ ∀a ∈ A, a⁺ ∈ A.

(**=== 公理6: 无穷公理 ===**)
Parameter 𝐈 : set. 
Axiom InfAx : inductive 𝐈.

(** 希尔伯特epsilon算子等效于选择公理 **)

(* 选择函数 *)
Definition Choice : set → set := λ s, epsilon (inhabits ∅) (λ x, x ∈ s).

(* “答案确实是在题目选项里选的” *)
Lemma chosen_contained : ∀ s, ⦿s → Choice s ∈ s.
Proof. intros s. exact (epsilon_spec (inhabits ∅) (λ x, x ∈ s)). Qed.

(* “答案集包含在问题集的并集里” *)
Theorem chosen_included : ∀ S, (∀s ∈ S, ⦿s) → {Choice | s ∊ S} ⊆ ⋃S.
Proof.
  intros S H x Hx.
  apply ReplAx in Hx as [s [H1 H2]].
  eapply UnionI. apply H1.
  apply H in H1. subst.
  apply chosen_contained. apply H1.
Qed.

(* “单选题” *)
Theorem one_chosen : ∀ S, (∀s ∈ S, ⦿s) →
  (∀ s t ∈ S, s ≠ t → disjoint s t) →
  ∀s ∈ S, ∃ x, s ∩ {Choice | s ∊ S} = ⎨x⎬.
Proof with eauto.
  intros S Hi Hdj s Hs.
  exists (Choice s). apply sub_asym.
  - intros x Hx. apply BInterE in Hx as [Hx1 Hx2].
    cut (x = Choice s).
    + intros. subst...
    + apply ReplAx in Hx2 as [t [Ht Hteq]].
      destruct (classic (s = t)) as [|Hnq].
      * congruence.
      * pose proof (chosen_contained t (Hi t Ht)) as Hx2.
        rewrite Hteq in Hx2. apply Hdj in Hnq...
        exfalso. eapply disjointE...
  - apply single_of_member_is_subset. apply BInterI.
    + apply chosen_contained. apply Hi...
    + apply ReplI...
Qed.

(* 更多经典逻辑引理 *)
Lemma not_all_not_iff_ex : ∀ P : set → Prop, ¬ (∀ X, ¬ P X) ↔ (∃ X, P X).
Proof. split. exact (not_all_not_ex _ P). firstorder. Qed.

Lemma not_all_iff_ex_not : ∀ P : set → Prop, ¬ (∀ X, P X) ↔ (∃ X, ¬ P X).
Proof. split. exact (not_all_ex_not _ P). firstorder. Qed.

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
  rewrite not_all_not_iff_ex in H1.
  rewrite not_all_iff_ex_not in H1.
  intros. apply H1 in H. destruct H as [X H].
  exists X. clear H1.
  assert (∀ A B : Prop, ¬ (A → ¬ B) ↔ ¬¬B ∧ ¬¬A) by firstorder.
  rewrite H0 in H. clear H0. destruct H.
  apply NNPP in H. apply NNPP in H0. firstorder.
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
