(** Based on "Elements of Set Theory" Chapter 8 Part 3 **)
(** Coq coding by choukh, Mar 2021 **)

Require Export ZFC.EST8_2.
Require Import ZFC.lib.LoStruct.
Require Import ZFC.lib.ScottsTrick.
Import ScottsTrick.ForAnyType.

(*** EST第八章3：序类型 ***)

Definition it := λ S, scott (λ S, <A S, R S>) isomorphic S.

Fact it_nonempty : ∀ S, it S ≠ ∅.
Proof.
  intros. apply scott_nonempty. apply iso_equiv.
Qed.

Theorem it_correct : ∀ S T, it S = it T ↔ S ≅ T.
Proof.
  intros. apply scott_correct.
  intros U V Heq. apply op_iff in Heq as [].
  apply eq_intro; auto. apply iso_equiv.
Qed.


