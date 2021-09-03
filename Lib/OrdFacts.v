(** Coq coding by choukh, Jan 2021 **)

Require Import ZFC.Elements.EST7_4.
Require Import ZFC.Elements.EST6_2.
Require Import ZFC.Lib.FuncFacts.

(* 有限序数 *)
Definition finord := λ α, α ⋵ 𝐎𝐍 ∧ finite α.
Notation 𝐎𝐍ᶠⁱⁿ := finord.

(* 无限序数 *)
Definition inford := λ α, α ⋵ 𝐎𝐍 ∧ infinite α.
Notation 𝐎𝐍ⁱⁿᶠ := inford.

(* 自然数集的非空有限子集有极大元 *)
Lemma finite_ords_is_bounded : ∀ A, ⦿ A → A ⪽ 𝐎𝐍 →
  finite A → ∃ α, sub_maximum α A.
Proof with auto; try congruence.
  intros A Hne Hords [n [Hn Hqn]].
  generalize dependent A.
  ω_induction n; intros A Hne Hords Hqn. {
    apply eqnum_empty in Hqn. apply EmptyNI in Hne. exfalso...
  }
  clear Hn n. destruct Hne as [α Hα].
  destruct (classic (sub_maximum α A)). exists α...
  apply not_and_or in H as []. exfalso...
  apply set_not_all_ex_not in H as [β [Hβ Hαβ]].
  apply Hords in Hα as Hoα. apply Hords in Hβ as Hoβ.
  apply ord_lt_iff_not_sub in Hαβ...
  apply split_one_element in Hα as HeqA. rewrite HeqA in Hqn.
  apply finite_set_remove_one_member in Hqn...
  specialize IH with (A - {α,}) as [μ [Hμ Hmax]]...
  { exists β. apply SepI... apply SingNI...
    intros Heq. apply (ord_irrefl α)...
  } {
    intros x Hx. apply SepE1 in Hx. apply Hords...
  }
  apply SepE1 in Hμ... apply Hords in Hμ as Hoμ.
  destruct (classic (β ⊆ μ)) as [Hβμ|Hμβ].
  - exists μ. split... intros γ Hγ.
    destruct (classic (γ = α)).
    + rewrite H. apply ord_lt_iff_psub...
    + apply Hmax. apply SepI... apply SingNI...
  - exists β. split... intros γ Hγ.
    apply ord_lt_iff_not_sub in Hμβ...
    destruct (classic (γ = α)).
    + rewrite H. apply ord_lt_iff_psub...
    + eapply sub_trans.
      * apply Hmax. apply SepI... apply SingNI...
      * apply ord_lt_iff_psub...
Qed.

(* 非零极限序数是无限序数 *)
Lemma limord_is_inford : ∀α ⋵ 𝐎𝐍ˡⁱᵐ, α ≠ ∅ → α ⋵ 𝐎𝐍ⁱⁿᶠ.
Proof with eauto; try congruence.
  intros α Hlim Hne. split. apply Hlim. intros Hfin.
  apply limord_no_maximum in Hlim as Hbnd.
  apply Hbnd. apply finite_ords_is_bounded...
  apply EmptyNE... apply ord_is_ords. apply Hlim.
Qed.

(* 非零有限序数是后继序数 *)
Lemma nonzero_finord_is_suc : ∀α ⋵ 𝐎𝐍ᶠⁱⁿ, α ≠ ∅ → α ⋵ 𝐎𝐍ˢᵘᶜ.
Proof with auto.
  intros α [Hord Hfin] Hne.
  apply sucord_or_limord in Hord as []...
  apply limord_is_inford in H as [_ Hinf]... exfalso...
Qed.

(* 任意序数与自身的单集不交 *)
Lemma ord_disjoint : ∀α ⋵ 𝐎𝐍, disjoint α {α,}.
Proof.
  intros n Hn. apply disjointI. intros [x [H1 H2]].
  apply SingE in H2. subst. eapply ord_irrefl; eauto.
Qed.

(* 自然数等价于有限序数 *)
Lemma nat_iff_finord : ∀ n, n ∈ ω ↔ n ⋵ 𝐎𝐍ᶠⁱⁿ.
Proof with neauto.
  split. {
    intros Hn. split... apply nat_finite...
  }
  intros [Hord [k [Hk Hqn]]].
  generalize dependent n.
  ω_induction k; intros n Hn Hqn.
  - apply eqnum_empty in Hqn. subst...
  - apply sucord_or_limord in Hn as [Hsuc|Hlim].
    + destruct Hsuc as [p [Hp Heq]]. subst n.
      apply ω_inductive. apply IH...
      eapply eqnum_sets_removing_one_element_still_eqnum...
      apply ord_disjoint...
      apply nat_disjoint...
    + destruct (classic (n = ∅)). subst...
      exfalso. apply limord_is_inford in Hlim as [_ Hinf]...
      apply Hinf. exists (m⁺). split... apply ω_inductive...
Qed.

(* ω是无限序数 *)
Lemma ω_is_inford : ω ⋵ 𝐎𝐍ⁱⁿᶠ.
Proof. split. apply ω_is_ord. apply ω_infinite. Qed.

(* 大于等于ω的序数是无限序数 *)
Lemma ord_geq_ω_infinite : ∀α ⋵ 𝐎𝐍, ω ⋸ α → α ⋵ 𝐎𝐍ⁱⁿᶠ.
Proof with eauto.
  intros α Hα Hle.
  apply ord_le_iff_sub in Hle... split...
  eapply parent_set_of_infinite_is_infinite...
  apply ω_infinite.
Qed.

(* 无限序数大于等于ω *)
Lemma inford_geq_ω : ∀α ⋵ 𝐎𝐍ⁱⁿᶠ, ω ⋸ α.
Proof with auto.
  intros α [Hα Hinf]. apply ord_le_iff_not_gt...
  intros Hlt. apply Hinf. apply nat_finite...
Qed.

(* 序数大于等于ω当且仅当该序数是无限序数 *)
Lemma ord_geq_ω_iff_inford : ∀ α, α ⋵ 𝐎𝐍 ∧ ω ⋸ α ↔ α ⋵ 𝐎𝐍ⁱⁿᶠ.
Proof with auto.
  split.
  - intros [Hα Hle]. apply ord_geq_ω_infinite...
  - intros Hinf. split. apply Hinf. apply inford_geq_ω...
Qed.

(* 无限序数与自身的后继等势 *)
Lemma inford_eqnum_its_suc : ∀α ⋵ 𝐎𝐍ⁱⁿᶠ, α⁺ ≈ α.
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
  exists f. apply meta_bijection.
  - intros x Hx. destruct (ixm (x = α)).
    + apply ord_neq_0_gt_0... apply EmptyNI.
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
      apply ord_le_iff_sub...
      destruct (ixm (n' = α)).
      * subst. exfalso. apply ord_le_iff_not_gt in Hgeω...
      * destruct (ixm (n' ∈ ω))...
    + exists y. split. apply BUnionI1...
      destruct (ixm (y = α)).
      * exfalso. eapply ord_irrefl...
      * destruct (ixm (y ∈ ω))...
Qed.

(* 无限序数的前驱（如果存在）是无限序数 *)
Lemma pred_of_inford_infinite : ∀α ⋵ 𝐎𝐍ⁱⁿᶠ, ∀ β, α = β⁺ → β ⋵ 𝐎𝐍ⁱⁿᶠ.
Proof with eauto.
  intros α [Hα Hinf] β Heq.
  assert (Hβ: β ⋵ 𝐎𝐍). {
    eapply ord_is_ords... rewrite Heq. apply suc_has_n.
  }
  split... apply (remove_one_member_from_infinite β) in Hinf.
  replace β with (α - {β,})... rewrite Heq. unfold Suc.
  apply add_one_member_then_remove. apply ord_irrefl...
Qed.

(* 初始无限序数是极限序数 *)
Fact initial_inford_is_limit : ∀α ⋵ 𝐎𝐍ⁱⁿⁱᵗ, α ⋵ 𝐎𝐍ⁱⁿᶠ → α ⋵ 𝐎𝐍ˡⁱᵐ.
Proof with eauto.
  intros α [Hα Hinit] Hinf.
  destruct (sucord_or_limord α)... exfalso.
  destruct H as [β [Hβ Heq]].
  apply (Hinit β); rewrite Heq.
  - apply suc_has_n.
  - apply inford_eqnum_its_suc.
    eapply pred_of_inford_infinite...
Qed.
