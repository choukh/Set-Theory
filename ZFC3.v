(*** Formal Construction of a Set Theory in Coq ***)
(** adapted from the thesis by Jonas Kaiser, November 23, 2012 **)
(** Coq coding by choukh, April 2020 **)

Require Export ZFC.ZFC2.

(*** ZFC集合论3：无穷公理，选择公理，正则公理 ***)

(* 后续运算 *)
Definition Suc := λ a, a ∪ ⎨a⎬.
Notation "a ⁺" := (Suc a) (at level 6, format "a ⁺") : set_scope.

Lemma suc_has_n : ∀ n, n ∈ n⁺.
Proof. intros. apply BUnionI2. apply SingI. Qed.
Global Hint Immediate suc_has_n : core.

Lemma suc_inc_n : ∀ n, n ⊆ n⁺.
Proof. intros n x Hx. apply BUnionI1. apply Hx. Qed.

Lemma suc_neq_0 : ∀ n, n⁺ ≠ ∅.
Proof.
  intros n H. eapply EmptyE in H. apply H. apply suc_has_n.
Qed.
Global Hint Immediate suc_neq_0 : core.

(* 归纳集 *)
Definition inductive := λ A, ∅ ∈ A ∧ ∀a ∈ A, a⁺ ∈ A.

(**=== 公理6: 无穷公理 ===**)
Parameter 𝐈 : set. 
Axiom InfAx : inductive 𝐈.

(**=== 公理7: 选择公理 ===**)
(* See lib/Choice.v *)

(**=== 公理8: 正则公理 ===**)
(* We will postpone its declaration until really necessary *)
(* For more detail please see EST7_6 *)
Definition Regularity := ∀ A, A ≠ ∅ → ∃a ∈ A, a ∩ A = ∅.
