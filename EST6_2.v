(** Based on "Elements of Set Theory" Chapter 1 Part 2 **)
(** Coq coding by choukh, Aug 2020 **)

Require Export ZFC.EST6_1.

(*** EST第六章2：基数算术 ***)

(* TODO: We will remove this primitive notion after Chapter 7 *)
Parameter card : set → set.
Notation "| A |" := (card A) (at level 40) : ZFC_scope.
Axiom CardAx1 : ∀ A B, |A| = |B| ↔ A ≈ B.
Axiom CardAx2 : ∀ A, finite A → |A| = fin_card A.

Definition is_card : set → Prop := λ κ, ∃ K, κ = |K|.

(* 集合的基数为零当且仅当它是空集 *)
Lemma card_empty : ∀ A, |A| = ∅ ↔ A = ∅.
Proof with nauto.
  split; intros.
  - rewrite <- eqnum_empty, <- CardAx1,
      (CardAx2 ∅), (fin_card_n ∅)...
  - subst A. rewrite CardAx2, fin_card_n...
Qed.

(* 集合的基数不为零当且仅当集合非空 *)
Lemma set_nonzero_card_nonzero : ∀ A, ⦿ A ↔ ⦿ |A|.
Proof with nauto.
  split; intros [a Ha].
  - apply EmptyNE. intro.
    rewrite card_empty in H. subst. exfalso0.
  - apply EmptyNE. intro. subst A.
    rewrite CardAx2, fin_card_n in Ha... exfalso0.
Qed.

(* 任意集合都可以在任意非零基数的集合里 *)
Lemma any_set_in_set_of_any_nonzero_card : ∀ a κ,
  is_card κ → ⦿ κ → ∃ A, |A| = κ ∧ a ∈ A.
Proof with auto; try congruence.
  intros * [K Hκ] Hi. subst κ.
  apply set_nonzero_card_nonzero in Hi as [k Hk].
  destruct (classic (a ∈ K)) as [|Ha]. exists K. split...
  pose proof (bijection_exists_between_set_and_element_replaced
    K k a Hk Ha) as [f Hf].
  exists {ReplaceElement k a | x ∊ K}. split.
  - apply CardAx1. apply eqnum_symm. exists f...
  - apply ReplAx. exists k. split...
    unfold ReplaceElement. destruct (ixm (k = k))...
Qed.
