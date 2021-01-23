(*** Formal Construction of a Set Theory in Coq ***)
(** based on the thesis by Jonas Kaiser, November 23, 2012 **)
(** Coq coding by choukh, April 2020 **)

Require Export ZFC.ZFC2.

(*** ZFC集合论3：无穷公理，选择公理，正则公理 ***)

Declare Scope ZFC_scope.
Open Scope ZFC_scope.
Delimit Scope ZFC_scope with zfc.

(* 后续运算 *)
Definition Suc : set → set := λ a, a ∪ ⎨a⎬.
Notation "a ⁺" := (Suc a) (at level 8) : ZFC_scope.

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

(**=== 公理7: 选择公理 ===**)
(* 由希尔伯特epsilon算子导出选择公理 *)

(* 希尔伯特epsilon算子相当于类（class）上的选择函数（全局选择公理）*)
Definition ClassChoice := λ P, epsilon (inhabits ∅) P.
Definition class_choice_spec := λ P, epsilon_spec (inhabits ∅) P.

(* 把epsilon的能力限制在集合上（选择公理）*)
Definition SetChoice := λ S, ClassChoice (λ x, x ∈ S).
Definition set_choice_spec := λ S, class_choice_spec (λ x, x ∈ S).

(* “答案确实是在题目选项里选的” *)
Lemma chosen_contained : ∀ s, ⦿ s → SetChoice s ∈ s.
Proof. intros s. apply set_choice_spec. Qed.

(* “答案集包含在问题集的并集里” *)
Theorem chosen_included : ∀ S, (∀s ∈ S, ⦿s) → {SetChoice | s ∊ S} ⊆ ⋃S.
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
  ∀s ∈ S, ∃ x, s ∩ {SetChoice | s ∊ S} = ⎨x⎬.
Proof with eauto.
  intros S Hi Hdj s Hs.
  exists (SetChoice s). apply sub_antisym.
  - intros x Hx. apply BInterE in Hx as [Hx1 Hx2].
    cut (x = SetChoice s).
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

(**=== 公理8: 正则公理 ===**)
(* We will postpone its declaration until really necessary *)
(* For more detail please see EST7_6 *)
Definition Regularity := ∀ A, A ≠ ∅ → ∃a ∈ A, a ∩ A = ∅.
