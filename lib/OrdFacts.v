(** Coq coding by choukh, Jan 2021 **)

Require Import ZFC.EST7_4.
Require Import ZFC.EST6_2.

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
Lemma disjoint_ord_single : ∀ α, is_ord α → disjoint α ⎨α⎬.
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
      apply disjoint_ord_single...
      apply disjoint_nat_single...
    + destruct (classic (n = ∅)). subst...
      exfalso. apply limit_is_inford in Hlim as [_ Hinf]...
      apply Hinf. exists (m⁺). split... apply ω_inductive...
Qed.

Lemma ω_is_inford : inford ω.
Proof. split. apply ω_is_ord. apply ω_infinite. Qed.

(* TODO: infinite cardinal is limit ordinal *)
