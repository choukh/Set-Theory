(** Based on "Elements of Set Theory" Chapter 6 Part 5 **)
(** Coq coding by choukh, Oct 2020 **)

Require Export ZFC.EX6_2.

(*** EST第六章5：可数集 ***)

(* 可数集 *)
Definition countable : set → Prop := λ A, A ≼ ω.

(* 集合是可数集当且仅当其基数小于等于阿列夫零 *)
Lemma countable_iff_leq_aleph0 : ∀ A, countable A ↔ |A| ≤ ℵ₀.
Proof. split; apply cardLeq_iff; auto. Qed.

(* 集合是可数集当且仅当它是有限集或与ω等势 *)
Lemma countable_iff_finite_or_eqnum_ω :
  ∀ A, countable A ↔ finite A ∨ A ≈ ω.
Proof with auto.
  split.
  - intros Hdm. destruct (classic (finite A))... right.
    apply infinite_set_dominated_by_ω_eqnum_ω...
  - intros [[n [Hn [f [Hi [Hd Hr]]]]]|[f Hf]].
    + exists f. split... split... rewrite Hr.
      apply trans_sub... apply ω_trans.
    + exists f. apply bijection_is_injection...
Qed.
