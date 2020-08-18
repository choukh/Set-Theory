(** Based on "Elements of Set Theory" Chapter 1 Part 2 **)
(** Coq coding by choukh, Aug 2020 **)

Require Export ZFC.EST6_1.

(*** EST第六章2：基数算术 ***)

(* TODO: We will remove this primitive notion after Chapter 7 *)
Parameter card : set → set.
Axiom CardAx1 : ∀ A B, card A = card B ↔ A ≈ B.
Axiom CardAx2 : ∀ A, finite A → card A = fin_card A.


