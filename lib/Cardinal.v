(** Coq coding by choukh, Nov 2020 **)

Require Export ZFC.EX6_3.
Require Import ZFC.lib.OrdFacts.

(* == implicit AC == *)
(* 基数是序数 *)
Lemma card_is_ord : ∀ 𝜅, is_card 𝜅 → is_ord 𝜅.
Proof.
  intros 𝜅 [k Hk]. subst. apply card_is_initial_ord.
Qed.
Hint Immediate card_is_ord : core.

(* == implicit AC == *)
(* 基数集是良序集 *)
Lemma cards_woset : ∀ 𝛫, (∀𝜅 ∈ 𝛫, is_card 𝜅) →
  woset 𝛫 (MemberRel 𝛫).
Proof.
  intros K HK. apply ords_woset.
  intros 𝜅 H𝜅. apply card_is_ord. apply HK. apply H𝜅.
Qed.

(* == implicit AC == *)
Lemma card_epsilon_to_cardLt : ∀ 𝜅 𝜆, is_card 𝜅 → is_card 𝜆 →
  𝜅 ∈ 𝜆 → 𝜅 <𝐜 𝜆.
Proof with auto.
  intros 𝜅 𝜆 H𝜅 H𝜆 Hlt.
  apply ord_lt_iff_psub in Hlt as [Hsub Hnq]...
  apply dominate_sub in Hsub. repeat split...
Qed.

(* == implicit AC == *)
Lemma cardLt_to_card_epsilon : ∀ 𝜅 𝜆,
  𝜅 <𝐜 𝜆 → 𝜅 ∈ 𝜆.
Proof with auto.
  intros 𝜅 𝜆 [[H𝜅 [H𝜆 Hdom]] Hnq].
  destruct (classic (𝜅 ∈ 𝜆))... exfalso. apply Hnq.
  rewrite (card_of_card 𝜅), (card_of_card 𝜆)... apply CardAx1.
  apply ord_leq_iff_not_gt in H...
  apply ord_leq_iff_sub in H...
  apply dominate_sub in H. apply Schröeder_Bernstein...
Qed.

(* == implicit AC == *)
(* 基数的序与序数的序等价 *)
Fact cardLt_iff_card_epsilon : ∀ 𝜅 𝜆,
  𝜅 <𝐜 𝜆 ↔ is_card 𝜅 ∧ is_card 𝜆 ∧ 𝜅 ∈ 𝜆.
Proof with auto.
  split.
  - intros Hlt. split. apply Hlt. split. apply Hlt.
    apply cardLt_to_card_epsilon...
  - intros [H𝜅 [H𝜆 Hlt]]. apply card_epsilon_to_cardLt...
Qed.

Module AlternativeProofAboutCardConnectivity.

Check EST6_4.card_connected.

(* == implicit AC == *)
(* 基数具有连通性 *)
Fact card_connected : ∀ 𝜅 𝜆,
  is_card 𝜅 → is_card 𝜆 → 𝜅 ≠ 𝜆 → 𝜅 <𝐜 𝜆 ∨ 𝜆 <𝐜 𝜅.
Proof.
  intros 𝜅 𝜆 H𝜅 H𝜆 Hnq.
  apply ord_connected in Hnq as [];
  auto; [left|right]; apply cardLt_iff_card_epsilon; auto.
Qed.

End AlternativeProofAboutCardConnectivity.

(* == implicit AC == *)
(* 无限基数是极限序数 *)
Lemma infcard_is_limit : ∀ 𝜅, infcard 𝜅 → is_limit 𝜅.
Proof.
  intros 𝜅 [Hcd Hinf].
  apply initial_inford_is_limit; [|split; auto].
  destruct Hcd as [k Hk]. rewrite Hk.
  apply card_is_initial_ord.
Qed.
