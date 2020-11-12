(** Solutions to "Elements of Set Theory" Chapter 6 Part 3 **)
(** Coq coding by choukh, Oct 2020 **)

Require Export ZFC.EST6_6.
Require Import ZFC.EST6_4_EXTEND_2.
Require Import ZFC.lib.IndexedFamilyUnion.

(* ex6_26 see EST6_5 Theorem cardLeq_union_cardMul *)
(* ex6_28 see https://math.stackexchange.com/questions/201410/open-measurable-sets-containing-all-rational-numbers *)
(* ex6_29 see https://math.stackexchange.com/questions/2876327/show-that-a-certain-set-of-positive-real-numbers-must-be-finite-or-countable *)
(* ex6_30 see EST6_5 Fact sq_dominated_by_ω_arrow *)
(* ex6_31 see EST6_6 Theorem cardMul_infinite_self *)

(* 有限子集集 *)
Definition FiniteSubSets : set → set := λ A,
  {B ∊ 𝒫 A | finite}.
Notation "'𝗙𝗶𝗻'" := (FiniteSubSets) (at level 9).

(* n元子集集 *)
Definition FinCardSubSets : set → set → set := λ A n,
  {B ∊ 𝒫 A | λ B, B ≈ n}.
Notation "'𝗙𝗶𝗻𝗰'" := (FinCardSubSets) (at level 9).

(* 有限子集与n元子集的相互转化 *)
Lemma finCardSubSets_iff_finiteSubSets : 
  ∀ A B, ∀n ∈ ω, B ∈ 𝗙𝗶𝗻𝗰 A n ↔ B ∈ 𝗙𝗶𝗻 A ∧ B ≈ n.
Proof with auto.
  intros A B n Hn. unfold FinCardSubSets. split; intros.
  - apply SepE in H as [H1 H2]. split...
    apply SepI... exists n. split...
  - destruct H as [H1 H2]. apply SepE in H1 as [HB Hfin].
    apply SepI...
Qed.

(* 零元子集只有空集 *)
Fact finCardSubSet_0 : ∀ A, 𝗙𝗶𝗻𝗰 A 0 = ⎨∅⎬.
Proof with nauto.
  intros. apply ExtAx. split; intros Hx.
  - apply SepE in Hx as [_ Hx].
    rewrite eqnum_empty in Hx. subst...
  - apply SingE in Hx. subst. apply SepI...
    apply empty_in_all_power.
Qed.

(* 有限子集集的基数等于所有n元子集集的基数的累加 *)
Lemma card_of_finCardSubSets : ∀ A, |𝗙𝗶𝗻 A| = ∑ᵢ (𝗙𝗶𝗻𝗰 A).
Proof with neauto.
  intros. assert (Hw: ∀B ∈ 𝗙𝗶𝗻 A, |B| ∈ ω). {
    intros B HB. apply nat_iff_fincard. split...
    rewrite <- set_finite_iff_card_finite...
    apply SepE in HB as []...
  }
  apply CardAx1.
  set (λ B, <B, |B|>) as F.
  set (Func (𝗙𝗶𝗻 A) (⋃ᵢ λ i, 𝗙𝗶𝗻𝗰 A i × ⎨i⎬) F) as f.
  exists f. apply meta_bijective.
  + intros B HB. assert (HBw: |B| ∈ ω) by (apply Hw; auto).
    eapply IFUnionI... apply CProdI...
    apply finCardSubSets_iff_finiteSubSets...
    split... apply CardAx0.
  + intros x1 H1 x2 H2 Heq. apply op_iff in Heq as []...
  + intros p Hp. apply IFUnionE in Hp as [n [Hn Hp]].
    apply cprod_iff in Hp as [B [HB [m [Hm Hp]]]]. subst p.
    apply finCardSubSets_iff_finiteSubSets in HB as [HB Hqn]...
    apply SingE in Hm; subst. exists B. split...
    rewrite <- CardAx1, <- (card_of_nat n) in Hqn...
    rewrite <- Hqn...
Qed.

(* ==需要选择公理== *)
(* n元子集集的基数不大于原集合基数的n次幂 *)
Lemma cardLeq_finCardSubSets_pow_n : AC_III' →
  ∀ A, ∀n ∈ ω, |𝗙𝗶𝗻𝗰 A n| ≤ |A| ^ n.
Proof with auto.
  intros AC3' A n Hn.
  rewrite (card_of_nat n) at 2...
  rewrite cardExp. apply cardLeq_iff.
  set (λ B, {f ∊ n ⟶ B | λ f, f: n ⟹ B}) as G.
  set {G | B ∊ 𝗙𝗶𝗻𝗰 A n} as 𝒢.
  pose proof (AC3' 𝒢) as [F [HfF [HdF HrF]]]. {
    intros F HF. apply ReplAx in HF as [B [HB HF]]. subst F.
    apply finCardSubSets_iff_finiteSubSets in HB as [_ Hqn]...
    symmetry in Hqn. destruct Hqn as [f Hf].
    exists f. apply SepI. apply ArrowI.
    apply bijection_is_func...
    apply bijection_is_surjection...
  }
  assert (HFap: ∀B ∈ 𝗙𝗶𝗻𝗰 A n, F[G B] ∈ G B). {
    intros B HB. apply HrF. apply ReplAx. exists B. split...
  }
  assert (Hg: ∀B ∈ 𝗙𝗶𝗻𝗰 A n, F[G B]: n ⟹ B). {
    intros B HB. apply HFap in HB as Hf. apply SepE in Hf as []...
  }
  assert (Hsub: ∀B ∈ 𝗙𝗶𝗻𝗰 A n, B ⊆ A). {
    intros B HB.
    apply finCardSubSets_iff_finiteSubSets in HB as [HB _]...
    apply SepE in HB as [HB _]. apply PowerAx...
  }
  set (Func (𝗙𝗶𝗻𝗰 A n) (n ⟶ A) (λ B, F[G B])) as h.
  exists h. apply meta_injective.
  - intros B HB. apply ArrowI.
    destruct (Hg B) as [Hfg [Hdg Hrg]]...
    split... split... rewrite Hrg. apply Hsub...
  - intros B1 H1 B2 H2 Heq.
    destruct (Hg B1) as [_ [_ Hr1]]...
    destruct (Hg B2) as [_ [_ Hr2]]... congruence.
Qed.

(* ==需要选择公理== *)
(* 同一无限基数的可数无限累加与自身相等 *)
Lemma cardInfSum_self : AC_VI → ∀ 𝜅, infcard 𝜅 → ∑ᵢ (λ _, 𝜅) = 𝜅.
Proof with nauto.
  intros AC6 𝜅 [Hcd Hinf].
  rewrite cardInfSum_of_same_card, cardMul_comm...
  rewrite (cardMul_absorption AC6 𝜅 ℵ₀)...
  - apply aleph0_is_the_least_infinite_card...
    apply AC_VI_to_III... split...
  - intros Heq. apply (fin_card_neq_aleph0 0)...
    rewrite Heq, <- card_of_nat...
Qed.

(* ==需要选择公理== *)
(* ex6_32: 无限集与其有限子集集等势 *)
Theorem infinite_set_eqnum_finite_subsets : AC_VI →
  ∀ A, infinite A → A ≈ 𝗙𝗶𝗻 A.
Proof with neauto.
  intros AC6 A Hinf.
  assert (AC3': AC_III'). { apply AC_VI_to_III'... }
  apply set_infinite_iff_card_infinite in Hinf.
  apply Schröeder_Bernstein.
  - set (Func A (𝗙𝗶𝗻 A) (λ a, ⎨a⎬)) as f.
    exists f. apply meta_injective.
    + intros a Ha. apply SepI... apply PowerAx.
      apply single_of_member_is_subset...
    + intros x1 H1 x2 H2 Heq. apply single_injective...
  - (* |𝗙𝗶𝗻 A| = ∑ᵢ(𝗙𝗶𝗻ᵢ A) ≤ ∑ᵢ|A| = ℵ₀⋅|A| = |A| *)
    apply cardLeq_iff. rewrite card_of_finCardSubSets.
    rewrite <- cardInfSum_self; [|auto|split]...
    apply cardInfSum_preserve_leq... intros i Hi.
    rewrite <- (card_of_card (|A|))...
    (* |(𝗙𝗶𝗻ᵢ A)[n]| ≤ |A| *)
    eapply cardLeq_tran. apply cardLeq_finCardSubSets_pow_n...
    apply cardExp_infinite_leq... split...
Qed.

(* ==需要选择公理== *)
(* 有限序列集的基数不大于原集合基数的有限次幂的累加 *)
Lemma cardLeq_sq_infSum_pow_n : AC_III' → ∀ A,
  |𝗦𝗾 A| ≤ ∑ᵢ (λ i, |A| ^ i).
Proof with nauto.
  intros AC3' *.
  assert (Heq: ∑ᵢ (λ i, |A| ^ i) = ∑ᵢ (λ i, i ⟶ A)). {
    apply cardInfSum_well_defined...
    intros i Hi. rewrite <- card_of_card...
    rewrite (card_of_nat i) at 1... apply cardExp.
  }
  rewrite Heq, cardInfSum_of_disjoint.
  - apply cardLeq_iff. apply dominate_sub.
    apply sq_sub_ifunion_arrow.
  - intros i Hi j Hj Hnq. apply disjointI. intros [x [H1 H2]].
    apply SepE in H1 as [_ [_ [H1 _]]].
    apply SepE in H2 as [_ [_ [H2 _]]]. congruence.
Qed.

(* ==需要选择公理== *)
(* ex6_33: 无限集的有限序列集与自身等势 *)
Theorem infinite_set_eqnum_sq : AC_VI → ∀ A, infinite A → A ≈ 𝗦𝗾 A.
Proof with nauto.
  intros AC6 A Hinf.
  assert (AC3': AC_III'). { apply AC_VI_to_III'... }
  apply set_infinite_iff_card_infinite in Hinf.
  apply Schröeder_Bernstein. apply dominated_by_sq.
  (* |𝗦𝗾 A| ≤ ∑ᵢ|A|^n ≤ ∑ᵢ|A| = ℵ₀⋅|A| = |A| *)
  apply cardLeq_iff. eapply cardLeq_tran. {
    apply cardLeq_sq_infSum_pow_n...
  }
  rewrite <- cardInfSum_self; [|auto|split]...
  apply cardInfSum_preserve_leq... intros i Hi.
  rewrite <- card_of_card, <- (card_of_card (|A|))...
  apply cardExp_infinite_leq... split...
Qed.
