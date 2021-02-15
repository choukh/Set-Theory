(** Coq coding by choukh, Jan 2021 **)

Require Import ZFC.EST7_4.
Require Import ZFC.EST6_2.
Require Import ZFC.lib.FuncFacts.

(* 有限序数 *)
Definition finord := λ α, is_ord α ∧ finite α.

(* 无限序数 *)
Definition inford := λ α, is_ord α ∧ infinite α.

(* 自然数集的非空有限子集有极大元 *)
Lemma finite_ords_is_bounded : ∀ A, ⦿ A → is_ords A →
  finite A → ∃ α, sub_maximum α A.
Proof with auto; try congruence.
  intros A Hne Hords [n [Hn Hqn]].
  generalize dependent A.
  set {n ∊ ω | λ n, ∀ A, ⦿ A → is_ords A → A ≈ n → ∃ α, sub_maximum α A} as N.
  ω_induction N Hn; intros A Hne Hords Hqn. {
    apply eqnum_empty in Hqn. apply EmptyNI in Hne. exfalso...
  }
  clear N Hn n. destruct Hne as [α Hα].
  destruct (classic (sub_maximum α A)). exists α...
  apply not_and_or in H as []. exfalso...
  apply set_not_all_ex_not in H as [β [Hβ Hαβ]].
  apply Hords in Hα as Hoα. apply Hords in Hβ as Hoβ.
  apply ord_lt_iff_not_sub in Hαβ...
  apply split_one_element in Hα as HeqA. rewrite HeqA in Hqn.
  apply finite_set_remove_one_element in Hqn...
  specialize IH with (A - ⎨α⎬) as [μ [Hμ Hmax]]...
  { exists β. apply SepI... apply SingNI...
    intros Heq. apply (ord_irrefl α)...
  } {
    intros x Hx. apply SepE1 in Hx. apply Hords...
  }
  apply SepE1 in Hμ... apply Hords in Hμ as Hoμ.
  destruct (classic (β ⊆ μ)) as [Hβμ|Hμβ].
  - exists μ. split... intros γ Hγ.
    destruct (classic (γ = α)).
    + rewrite H. apply ord_lt_iff_psub... apply Hβμ...
    + apply Hmax. apply SepI... apply SingNI...
  - exists β. split... intros γ Hγ.
    apply ord_lt_iff_not_sub in Hμβ...
    destruct (classic (γ = α)).
    + rewrite H. apply ord_lt_iff_psub...
    + eapply sub_tran.
      * apply Hmax. apply SepI... apply SingNI...
      * apply ord_lt_iff_psub...
Qed.

(* 非零极限序数是无限序数 *)
Lemma limit_is_inford : ∀ α, α ≠ ∅ → is_limit α → inford α.
Proof with eauto; try congruence.
  intros α Hne Hlim. split. apply Hlim. intros Hfin.
  apply limit_ord_no_maximum in Hlim as Hbnd.
  apply Hbnd. apply finite_ords_is_bounded...
  apply EmptyNE... apply ord_is_ords. apply Hlim.
Qed.

(* 非零有限序数是后继序数 *)
Lemma nonzero_finord_is_suc : ∀ α, α ≠ ∅ → finord α → is_suc α.
Proof with auto.
  intros α Hne [Hord Hfin].
  apply ord_is_suc_or_limit in Hord as []...
  apply limit_is_inford in H as [_ Hinf]... exfalso...
Qed.

(* 任意序数与自身的单集不交 *)
Lemma ord_disjoint : ∀ α, is_ord α → disjoint α ⎨α⎬.
Proof.
  intros n Hn. apply disjointI. intros [x [H1 H2]].
  apply SingE in H2. subst. eapply ord_irrefl; eauto.
Qed.

(* 自然数等价于有限序数 *)
Lemma nat_iff_finord : ∀ n, n ∈ ω ↔ finord n.
Proof with neauto.
  split. {
    intros Hn. split.
    apply nat_is_ord... apply nat_finite...
  }
  intros [Hord [k [Hk Hqn]]].
  generalize dependent n.
  set {k ∊ ω | λ k, ∀ n, is_ord n → n ≈ k → n ∈ ω} as N.
  ω_induction N Hk; intros n Hn Hqn.
  - apply eqnum_empty in Hqn. subst...
  - apply ord_is_suc_or_limit in Hn as [Hsuc|Hlim].
    + destruct Hsuc as [p [Hp Heq]]. subst n.
      apply ω_inductive. apply IH...
      eapply eqnum_sets_removing_one_element_still_eqnum...
      apply ord_disjoint...
      apply nat_disjoint...
    + destruct (classic (n = ∅)). subst...
      exfalso. apply limit_is_inford in Hlim as [_ Hinf]...
      apply Hinf. exists (m⁺). split... apply ω_inductive...
Qed.

(* ω是无限序数 *)
Lemma ω_is_inford : inford ω.
Proof. split. apply ω_is_ord. apply ω_infinite. Qed.

(* 大于等于ω的序数是无限序数 *)
Lemma ord_geq_ω_infinite : ∀ α, is_ord α → ω ⋸ α → inford α.
Proof with eauto.
  intros α Hα Hle.
  apply ord_leq_iff_sub in Hle... split...
  eapply parent_set_of_infinite_is_infinite...
  apply ω_infinite.
Qed.

(* 无限序数大于等于ω *)
Lemma inford_geq_ω : ∀ α, inford α → ω ⋸ α.
Proof with auto.
  intros α [Hα Hinf]. apply ord_leq_iff_not_gt...
  intros Hlt. apply Hinf. apply nat_finite...
Qed.

(* 序数大于等于ω当且仅当该序数是无限序数 *)
Lemma ord_geq_ω_iff_inford : ∀ α, is_ord α ∧ ω ⋸ α ↔ inford α.
Proof with auto.
  split.
  - intros [Hα Hle]. apply ord_geq_ω_infinite...
  - intros Hinf. split. apply Hinf. apply inford_geq_ω...
Qed.

(* 无限序数与自身的后继等势 *)
Lemma inford_eqnum_its_suc : ∀ α, inford α → α⁺ ≈ α.
Proof with neauto; try congruence.
  intros α Hinf.
  apply inford_geq_ω in Hinf as Hgeω.
  destruct Hinf as [Hα Hinf].
  set (Func α⁺ α (λ x, match (ixm (x = α)) with
    | inl _ => ∅
    | inr _ => match (ixm (x ∈ ω)) with
      | inl _ => x⁺
      | inr _ => x
  end end)) as f.
  exists f. apply meta_bijective.
  - intros x Hx. destruct (ixm (x = α)).
    + apply ord_nq_0_gt_0... apply EmptyNI.
      apply infinite_set_nonempty...
    + apply BUnionE in Hx as []; [|apply SingE in H]...
      destruct (ixm (x ∈ ω))... destruct Hgeω as [Hlt|Heq].
      * apply (ord_trans α Hα _ ω)... eapply ω_inductive...
      * rewrite <- Heq. apply ω_inductive...
  - intros x1 H1 x2 H2 Heq.
    destruct (ixm (x1 = α)); destruct (ixm (x2 = α))...
    + exfalso. destruct (ixm (x2 ∈ ω)).
      * eapply suc_neq_0...
      * apply n0. subst x2...
    + exfalso. destruct (ixm (x1 ∈ ω)).
      * eapply suc_neq_0...
      * apply n0. subst x1...
    + destruct (ixm (x1 ∈ ω)); destruct (ixm (x2 ∈ ω))...
      * apply suc_injective...
      * exfalso. apply n1. rewrite <- Heq. apply ω_inductive...
      * exfalso. apply n1. rewrite Heq. apply ω_inductive...
  - intros y Hy.
    destruct (classic (y = ∅)). {
      exists α. split... destruct (ixm (α = α))...
    }
    destruct (classic (y ∈ ω)).
    + ω_destruct y... exists n'. split.
      eapply ord_trans... apply ord_lt_suc_iff_sub...
      apply ord_leq_iff_sub...
      destruct (ixm (n' = α)).
      * subst. exfalso. apply ord_leq_iff_not_gt in Hgeω...
      * destruct (ixm (n' ∈ ω))...
    + exists y. split. apply BUnionI1...
      destruct (ixm (y = α)).
      * exfalso. eapply ord_irrefl...
      * destruct (ixm (y ∈ ω))...
Qed.

(* 无限序数的前驱（如果存在）是无限序数 *)
Lemma pred_of_inford_infinite : ∀ α β, inford α → α = β⁺ → inford β.
Proof with eauto.
  intros α β [Hα Hinf] Heq.
  assert (Hβ: is_ord β). {
    eapply ord_is_ords... rewrite Heq. apply suc_has_n.
  }
  split... apply (remove_one_member_from_infinite β) in Hinf.
  replace β with (α - ⎨β⎬)... rewrite Heq. unfold Suc.
  apply add_one_member_then_remove. apply ord_irrefl...
Qed.

(* 初始无限序数是极限序数 *)
Fact initial_inford_is_limit : ∀ α,
  initial_ord α → inford α → is_limit α.
Proof with eauto.
  intros α [Hα Hinit] Hinf.
  destruct (ord_is_suc_or_limit α)... exfalso.
  destruct H as [β [Hβ Heq]].
  apply (Hinit β); rewrite Heq.
  - apply suc_has_n.
  - apply inford_eqnum_its_suc.
    eapply pred_of_inford_infinite...
Qed.
