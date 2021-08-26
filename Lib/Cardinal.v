(** Coq coding by choukh, Nov 2020 **)

Require Export ZFC.Theory.EX6_3.
Require Import ZFC.Lib.OrdFacts.
Require Import ZFC.Lib.WosetMin.
Import WosetMin.FullVer.

(***
  基数的序与序数的序等价，
  无限基数是极限基数，
  后继基数，
  每个序数都有比它大的基数，
  不存在包括所有基数的集合
***)

(* == implicit AC == *)
(* 基数是序数 *)
Lemma card_is_ord : 𝐂𝐃 ⫃ 𝐎𝐍.
Proof.
  intros 𝜅 [k Hk]. subst. apply card_is_initord.
Qed.
Global Hint Resolve card_is_ord : core.

(* == implicit AC == *)
(* 无限基数是序数 *)
Lemma infcard_is_ord : 𝐂𝐃ⁱⁿᶠ ⫃ 𝐎𝐍.
Proof. intros 𝜅 [H _]. auto. Qed.
Global Hint Immediate infcard_is_ord : core.

(* == implicit AC == *)
(* 基数集是良序集 *)
Lemma cards_woset : ∀ 𝛫, 𝛫 ⪽ 𝐂𝐃 → woset 𝛫 (MemberRel 𝛫).
Proof.
  intros K HK. apply ords_woset.
  intros 𝜅 H𝜅. apply card_is_ord. apply HK. apply H𝜅.
Qed.

(* == implicit AC == *)
Lemma ord_lt_to_cardLt : ∀ 𝜅 𝜆 ⋵ 𝐂𝐃, 𝜅 ∈ 𝜆 → 𝜅 <𝐜 𝜆.
Proof with auto.
  intros 𝜅 H𝜅 𝜆 H𝜆 Hlt.
  apply ord_lt_iff_psub in Hlt as [Hsub Hnq]...
  apply dominate_sub in Hsub. repeat split...
Qed.

(* == implicit AC == *)
Lemma cardLt_to_ord_lt : ∀ 𝜅 𝜆,
  𝜅 <𝐜 𝜆 → 𝜅 ∈ 𝜆.
Proof with auto.
  intros 𝜅 𝜆 [[H𝜅 [H𝜆 Hdom]] Hnq].
  contra. apply Hnq.
  rewrite (card_of_card 𝜅), (card_of_card 𝜆)... apply CardAx1.
  apply ord_leq_iff_not_gt in H...
  apply ord_leq_iff_sub in H...
  apply dominate_sub in H. apply Schröeder_Bernstein...
Qed.

(* == implicit AC == *)
(* 基数的序与序数的序等价 *)
Fact cardLt_iff_ord_lt : ∀ 𝜅 𝜆,
  𝜅 <𝐜 𝜆 ↔ 𝜅 ⋵ 𝐂𝐃 ∧ 𝜆 ⋵ 𝐂𝐃 ∧ 𝜅 ∈ 𝜆.
Proof with auto.
  split.
  - intros Hlt. split. apply Hlt. split. apply Hlt.
    apply cardLt_to_ord_lt...
  - intros [H𝜅 [H𝜆 Hlt]]. apply ord_lt_to_cardLt...
Qed.

Module AlternativeProofAboutCardConnectivity.

Check EST6_4.card_connected.

(* == implicit AC == *)
(* 基数具有连通性 *)
Fact card_connected : ∀ 𝜅 𝜆 ⋵ 𝐂𝐃, 𝜅 ≠ 𝜆 → 𝜅 <𝐜 𝜆 ∨ 𝜆 <𝐜 𝜅.
Proof.
  intros 𝜅 H𝜅 𝜆 H𝜆 Hnq.
  apply ord_connected in Hnq as [];
  auto; [left|right]; apply cardLt_iff_ord_lt; auto.
Qed.

End AlternativeProofAboutCardConnectivity.

(* == implicit AC == *)
Lemma ord_leq_to_cardLeq : ∀ 𝜅 𝜆 ⋵ 𝐂𝐃, 𝜅 ⋸ 𝜆 → 𝜅 ≤ 𝜆.
Proof with auto.
  intros 𝜅 H𝜅 𝜆 H𝜆 Hlt.
  rewrite (card_of_card 𝜅), (card_of_card 𝜆)...
  apply cardLeq_iff. apply dominate_sub.
  apply ord_leq_iff_sub...
Qed.

(* == implicit AC == *)
Lemma cardLeq_to_ord_leq : ∀ 𝜅 𝜆, 𝜅 ≤ 𝜆 → 𝜅 ⋸ 𝜆.
Proof with auto.
  intros.
  apply cardLeq_iff_lt_or_eq in H as [|[_ [_ H]]]...
  left. apply cardLt_to_ord_lt...
Qed.

(* == implicit AC == *)
(* 基数的序与序数的序等价 *)
Fact cardLeq_iff_ord_leq : ∀ 𝜅 𝜆,
  𝜅 ≤ 𝜆 ↔ 𝜅 ⋵ 𝐂𝐃 ∧ 𝜆 ⋵ 𝐂𝐃 ∧ 𝜅 ⋸ 𝜆.
Proof with auto.
  split.
  - intros Hlt. split. apply Hlt. split. apply Hlt.
    apply cardLeq_to_ord_leq...
  - intros [H𝜅 [H𝜆 Hlt]]. apply ord_leq_to_cardLeq...
Qed.

(* == implicit AC == *)
(* 无限基数是极限序数 *)
Lemma infcard_is_limit : 𝐂𝐃ⁱⁿᶠ ⫃ 𝐎𝐍ˡⁱᵐ.
Proof.
  intros 𝜅 [Hcd Hinf].
  apply initial_inford_is_limit; [|split; auto].
  destruct Hcd as [k Hk]. rewrite Hk.
  apply card_is_initord.
Qed.

(* 后继基数 *)
Notation "A ₊" := (HartogsNumber A) (at level 8, format "A ₊") : set_scope.

(* 后继基数是基数 *)
Lemma card_suc_is_card : ∀ A, A₊ ⋵ 𝐂𝐃.
Proof with eauto.
  intros.
  pose proof (hartog_spec_intro A) as [HoA [Hndom Hleast]].
  exists A₊. apply card_iff_initord. split...
  intros β Hβ. intros Hqn.
  assert (Hoβ: β ⋵ 𝐎𝐍). eapply ord_is_ords...
  assert (¬ β ≼ A). {
    intros H. apply Hndom.
    apply (dominate_rewrite_l _ β)... symmetry...
  }
  apply Hleast in H... eapply ord_not_leq_gt; revgoals...
Qed.
Global Hint Immediate card_suc_is_card : core.

(* 后继基数是序数 *)
Corollary card_suc_is_ord : ∀ A, A₊ ⋵ 𝐎𝐍.
Proof.
  intros. apply card_is_ord. apply card_suc_is_card.
Qed.
Global Hint Immediate card_suc_is_ord : core.

(* 集合的基数小于其后继 *)
Lemma card_suc_has_card : ∀ A, |A| ∈ A₊.
Proof with auto; try easy.
  intros. unfold card.
  set (Min A₊ (MemberRel A₊)) as min.
  set {ξ ∊ A₊ | ξ ≈ A} as B.
  pose proof (hartog_spec_intro A) as [Hα [Hndom Hleast]].
  pose proof (min_correct A₊ (MemberRel A₊) B) as [Hm Hmin]... {
    apply ords_woset. intros b Hb. eapply ord_is_ords.
    apply hartog_spec_intro. apply Hb.
  } {
    exists (|A|). apply SepI...
    apply ord_lt_iff_not_sub...
    intros H. apply dominate_sub in H...
    apply (dominate_rewrite_r A) in H...
    rewrite <- CardAx0... rewrite <- CardAx0...
  } {
    intros x Hx. apply SepE1 in Hx...
  }
  apply SepE1 in Hm...
Qed.

(* 后继基数是大于该基数的最小基数 *)
Lemma card_suc_correct : ∀ A, ∀𝜅 ⋵ 𝐂𝐃, |A| ∈ 𝜅 → A₊ ⋸ 𝜅.
Proof with eauto.
  intros A 𝜅 Hcd HA𝜅.
  pose proof (hartog_spec_intro A) as [Ho [Hndom Hleast]].
  apply ord_lt_to_cardLt in HA𝜅...
  apply Hleast. apply card_is_ord...
  intros H𝜅A. apply cardLeq_iff in H𝜅A.
  rewrite <- card_of_card in H𝜅A...
  eapply cardLeq_to_not_gt...
Qed.

(* ex7_23 集合的哈特格斯数是该集合基数的后继基数 *)
Theorem hartogs_is_card_suc : ∀ A,
  (* i   *) A₊ ⋵ 𝐂𝐃 ∧
  (* ii  *) |A| ∈ A₊ ∧
  (* iii *) ∀𝜅 ⋵ 𝐂𝐃, |A| ∈ 𝜅 → A₊ ⋸ 𝜅.
Proof.
  intros. repeat split.
  - apply card_suc_is_card.
  - apply card_suc_has_card.
  - apply card_suc_correct.
Qed.

(* ex7_24 每个序数都有比它大的基数 *)
Theorem all_ord_ex_larger_card : ∀α ⋵ 𝐎𝐍, ∃𝜅 ⋵ 𝐂𝐃, α ∈ 𝜅.
Proof with auto.
  intros α Hα. exists α₊. split.
  apply card_suc_is_card.
  pose proof (card_suc_has_card α) as Hlt.
  apply ord_lt_to_cardLt in Hlt...
  rewrite (card_of_card α₊) in Hlt...
  apply cardLt_iff in Hlt as [Hdom Hnqn].
  apply ord_lt_iff_not_sub...
  intros H. apply dominate_sub in H.
  apply Hnqn. apply Schröeder_Bernstein...
Qed.

(* 不存在一个集合包括所有基数 *)
Corollary no_set_of_all_card : ¬ ∃ A, ∀𝜅 ⋵ 𝐂𝐃, 𝜅 ∈ A.
Proof with auto.
  intros [A H]. apply Burali_Forti.
  exists (⋃ A). intros α Hoα. apply UnionAx.
  apply all_ord_ex_larger_card in Hoα as [𝜅 [Hcd Hα]].
  exists 𝜅. split...
Qed.

(* 不存在一个集合包括所有无限基数 *)
Corollary no_set_of_all_infcard : ¬ ∃ A, ∀𝜅 ⋵ 𝐂𝐃ⁱⁿᶠ, 𝜅 ∈ A.
Proof with eauto.
  intros [A H]. apply Burali_Forti.
  exists (⋃ A). intros α Hoα. apply UnionAx.
  apply all_ord_ex_larger_card in Hoα as [𝜅 [H𝜅 Hα]].
  assert (Hcs: 𝜅 + ℵ₀ ⋵ 𝐂𝐃)...
  assert (Hos: (𝜅 + ℵ₀) ⋵ 𝐎𝐍)...
  apply all_ord_ex_larger_card in Hos as [𝜆 [H𝜆 Hlt]].
  exists 𝜆. split. apply H. split...
  - apply (parent_set_of_infinite_is_infinite (𝜅 + ℵ₀)).
    apply ord_leq_iff_sub... apply cardAdd_infinite_iff...
  - eapply ord_trans...
    cut (𝜅 <𝐜 𝜆). apply cardLt_iff_ord_lt.
    eapply cardLeq_lt_tran; revgoals.
    apply cardLt_iff_ord_lt... apply cardAdd_enlarge...
Qed.
