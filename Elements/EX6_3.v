(** Solutions to "Elements of Set Theory" Chapter 6 **)
(** Coq coding by choukh, Oct 2020 **)

Require Import ZFC.Lib.IndexedFamilyUnion.
Require Import ZFC.Lib.ChoiceFacts.
Require Export ZFC.Elements.EST6_6.

(* ex6_26 see EST6_5 Theorem cardLe_union_cardMul *)
(* ex6_28 see https://math.stackexchange.com/questions/201410/open-measurable-sets-containing-all-rational-numbers *)
(* ex6_29 see https://math.stackexchange.com/questions/2876327/show-that-a-certain-set-of-positive-real-numbers-must-be-finite-or-countable *)
(* ex6_30 see EST6_5 Fact sq_dominated_by_ω_arrow *)
(* ex6_31 see EST6_6 Theorem cardMul_infcard_self *)

(** ex6_32 **)

(* 有限子集集 *)
Definition FiniteSubSets : set → set := λ A,
  {B ∊ 𝒫 A | finite B}.
Notation 𝗙𝗶𝗻 := FiniteSubSets.

(* n元子集集 *)
Definition FinCardSubSets : set → set → set := λ A n,
  {B ∊ 𝒫 A | B ≈ n}.
Notation 𝗙𝗶𝗻𝗰 := FinCardSubSets.

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
Fact finCardSubSet_0 : ∀ A, 𝗙𝗶𝗻𝗰 A 0 = {∅,}.
Proof with nauto.
  intros. ext Hx.
  - apply SepE in Hx as [_ Hx].
    rewrite eqnum_empty in Hx. subst...
  - apply SingE in Hx. subst. apply SepI.
    apply empty_in_all_power. easy.
Qed.

(* 有限子集集的基数等于所有n元子集集的基数的累加 *)
Lemma card_of_finCardSubSets : ∀ A, |𝗙𝗶𝗻 A| = ∑ᵢ (𝗙𝗶𝗻𝗰 A).
Proof with neauto.
  intros. assert (Hw: ∀B ∈ 𝗙𝗶𝗻 A, |B| ∈ ω). {
    intros B HB. apply nat_iff_fincard. split...
    rewrite <- set_finite_iff_card_finite...
    apply SepE2 in HB...
  }
  apply CardAx1.
  set (λ B, <B, |B|>) as F.
  set (Func (𝗙𝗶𝗻 A) (⋃ᵢ λ i, 𝗙𝗶𝗻𝗰 A i × {i,}) F) as f.
  exists f. apply meta_bijection.
  + intros B HB. assert (HBw: |B| ∈ ω) by (apply Hw; auto).
    eapply IFUnionI... apply CPrdI...
    apply finCardSubSets_iff_finiteSubSets...
    split... apply CardAx0.
  + intros x1 H1 x2 H2 Heq. apply op_iff in Heq as []...
  + intros p Hp. apply IFUnionE in Hp as [n [Hn Hp]].
    apply CPrdE1 in Hp as [B [HB [m [Hm Hp]]]]. subst p.
    apply finCardSubSets_iff_finiteSubSets in HB as [HB Hqn]...
    apply SingE in Hm; subst. exists B. split...
    rewrite <- CardAx1, <- (card_of_nat n) in Hqn...
    rewrite <- Hqn...
Qed.

(* ==需要选择公理== *)
(* n元子集集的基数不大于原集合基数的n次幂 *)
Lemma cardLe_finCardSubSets_pow_n : AC_III' →
  ∀ A, ∀n ∈ ω, |𝗙𝗶𝗻𝗰 A n| ≤ |A| ^ n.
Proof with auto.
  intros AC3' A n Hn.
  rewrite (card_of_nat n) at 2...
  rewrite cardExp. apply cardLe_iff.
  set (λ B, {f ∊ n ⟶ B | f: n ⟹ B}) as G.
  set {G B | B ∊ 𝗙𝗶𝗻𝗰 A n} as 𝒢.
  pose proof (AC3' 𝒢) as [F [HfF [HdF HrF]]]. {
    intros F HF. apply ReplAx in HF as [B [HB HF]]. subst F.
    apply finCardSubSets_iff_finiteSubSets in HB as [_ Hqn]...
    symmetry in Hqn. destruct Hqn as [f Hf].
    exists f. apply SepI. apply arrowI.
    apply bijection_is_func...
    apply bijection_is_surjection...
  }
  assert (HFap: ∀B ∈ 𝗙𝗶𝗻𝗰 A n, F[G B] ∈ G B). {
    intros B HB. apply HrF. apply ReplAx. exists B. split...
  }
  assert (Hg: ∀B ∈ 𝗙𝗶𝗻𝗰 A n, F[G B]: n ⟹ B). {
    intros B HB. apply HFap in HB as Hf. apply SepE2 in Hf...
  }
  assert (Hsub: ∀B ∈ 𝗙𝗶𝗻𝗰 A n, B ⊆ A). {
    intros B HB.
    apply finCardSubSets_iff_finiteSubSets in HB as [HB _]...
    apply SepE in HB as [HB _]. apply PowerAx...
  }
  set (Func (𝗙𝗶𝗻𝗰 A n) (n ⟶ A) (λ B, F[G B])) as h.
  exists h. apply meta_injection.
  - intros B HB. apply arrowI.
    destruct (Hg B) as [Hfg [Hdg Hrg]]...
    split... split... rewrite Hrg. apply Hsub...
  - intros B1 H1 B2 H2 Heq.
    destruct (Hg B1) as [_ [_ Hr1]]...
    destruct (Hg B2) as [_ [_ Hr2]]... congruence.
Qed.

(* ==需要选择公理== *)
(* 同一无限基数的可数无限累加与自身相等 *)
Lemma cardInfSum_self : AC_VI → ∀𝜅 ⋵ 𝐂𝐃ⁱⁿᶠ, ∑ᵢ (λ _, 𝜅) = 𝜅.
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
  - set (Func A (𝗙𝗶𝗻 A) (λ a, {a,})) as f.
    exists f. apply meta_injection.
    + intros a Ha. apply SepI... apply PowerAx.
      apply single_of_member_is_subset...
    + intros x1 H1 x2 H2 Heq. apply single_eq_single...
  - (* |𝗙𝗶𝗻 A| = ∑ᵢ(𝗙𝗶𝗻ᵢ A) ≤ ∑ᵢ|A| = ℵ₀⋅|A| = |A| *)
    apply cardLe_iff. rewrite card_of_finCardSubSets.
    rewrite <- (cardInfSum_self AC6 (|A|)); [|split]...
    apply cardInfSum_preserve_le... intros i Hi.
    rewrite <- (card_of_card (|A|))...
    (* |(𝗙𝗶𝗻ᵢ A)[n]| ≤ |A| *)
    eapply cardLe_trans. apply cardLe_finCardSubSets_pow_n...
    apply cardExp_infcard_le... split...
Qed.

(* ==需要选择公理== *)
(* 有限序列集的基数不大于原集合基数的有限次幂的累加 *)
Lemma cardLe_sq_infSum_pow_n : AC_III' → ∀ A,
  |𝗦𝗾 A| ≤ ∑ᵢ (λ i, |A| ^ i).
Proof with nauto.
  intros AC3' *.
  assert (Heq: ∑ᵢ (λ i, |A| ^ i) = ∑ᵢ (λ i, i ⟶ A)). {
    apply cardInfSum_well_defined...
    intros i Hi. rewrite <- card_of_card...
    rewrite (card_of_nat i) at 1... apply cardExp.
  }
  rewrite Heq, cardInfSum_of_disjoint.
  - apply cardLe_iff. apply dominate_sub.
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
  apply cardLe_iff. eapply cardLe_trans. {
    apply cardLe_sq_infSum_pow_n...
  }
  rewrite <- (cardInfSum_self AC6 (|A|)) at 1; [|split]...
  apply cardInfSum_preserve_le... intros i Hi.
  rewrite <- card_of_card, <- (card_of_card (|A|))...
  apply cardExp_infcard_le... split...
Qed.

(* ==需要选择公理== *)
(* ex6_34: 无限基数的幂等于2的幂 *)
Theorem cardExp_infcard_infcard : AC_VI →
  ∀ 𝜅, ∀𝜆 ⋵ 𝐂𝐃ⁱⁿᶠ, 2 ≤ 𝜅 → 𝜅 ≤ 𝜆 →
  𝜅 ^ 𝜆 = 2 ^ 𝜆.
Proof with nauto.
  intros AC6 𝜅 𝜆 Hicl Hle1 Hle2.
  apply cardLe_antisym.
  - (* 𝜅 ^ 𝜆 ≤ 𝜆 ^ 𝜆 ≤ 2 ^ 𝜆 *)
    eapply cardLe_trans.
    + apply cardExp_preserve_base_le... apply Hle2.
    + apply eq_cardLe... apply cardExp_infcard_self...
  - apply cardExp_preserve_base_le...
Qed.

(* ex6_35
  { {∏ {x ∊ P | x ≤ p} | p ∊ P} | P ∊ 𝒫 PrimeSet} ?
*)

(** ex6_36 **)

Lemma cardGeq_2_impl_suc_suc : ∀n ∈ ω, 2 ≤ n → ∃m ∈ ω, n = m⁺⁺.
Proof with nauto.
  intros n Hn H2.
  apply fin_cardLe_iff_le in H2...
  apply lt_iff_suc_le in H2; [|apply ω_inductive|]...
  ω_destruct n. exfalso0.
  ω_destruct n. apply BUnionE in H2 as []. exfalso0.
  apply SingE in H. exfalso. apply (suc_neq_0 0)...
  exists n. split...
Qed.

Lemma card_neq_0_and_1 : ∀𝜅 ⋵ 𝐂𝐃, 𝜅 ≠ 0 → 𝜅 ≠ 1 → 2 ≤ 𝜅.
Proof with nauto.
  intros 𝜅 Hcd H0 H1.
  destruct (classic (finite 𝜅)).
  - assert (Hk: 𝜅 ∈ ω). { apply nat_iff_fincard. split... }
    apply fin_cardLe_iff_le... apply le_iff_sub...
    contra.
    apply lt_iff_not_sub in H2...
    rewrite two in H2. apply PairE in H2 as []...
    rewrite one in H1...
  - apply cardLt_infcard_n... split...
Qed.

(* 洗牌集：每个元素都不与自身对应的全排列 *)
Definition Shuffle : set → set := λ A,
  {f ∊ Permutation A | ∀a ∈ A, f[a] ≠ a}.

Lemma shuffle_iff : ∀ A f,
  f ∈ Shuffle A ↔ f: A ⟺ A ∧ ∀a ∈ A, f[a] ≠ a.
Proof with auto.
  split; intros.
  - apply SepE in H as [Hf Hnq].
    apply permutation_iff in Hf. split...
  - destruct H as []. apply SepI... apply permutation_iff...
Qed.

(* 任意基数大于等于2的有限集合，存在其洗牌 *)
Lemma finite_shuffle_exists : ∀ A,
  finite A → 2 ≤ |A| → ⦿ Shuffle A.
Proof with neauto; try congruence.
  intros A [n [Hn Hqn]] H2.
  apply CardAx1 in Hqn as Heq.
  rewrite <- (card_of_nat n) in Heq...
  rewrite Heq in H2. clear Heq.
  apply cardGeq_2_impl_suc_suc in H2 as [m [Hm Heqn]]... subst n.
  assert (Hmp: m⁺ ∈ ω) by (apply ω_inductive; auto).
  assert (Hmpp: m⁺⁺ ∈ ω) by (apply ω_inductive; auto).
  assert (H0: 0 ∈ m⁺⁺). { apply suc_has_0... }
  destruct Hqn as [f Hf].
  apply inv_bijection in Hf as Hf'.
  apply bijection_is_func in Hf as [Hmapf [Hinjf Hrf]].
  apply bijection_is_func in Hf' as [Hmapf' [Hinjf' Hrf']].
  assert (H := Hmapf). destruct H as [_ [Hdf _]].
  assert (H := Hmapf'). destruct H as [_ [Hdf' _]].
  assert (Hap: ∀x ∈ A, f[x] ∈ m⁺⁺). {
    intros x Hx. eapply ap_ran...
  }
  assert (Hapw: ∀x ∈ A, f[x] ∈ ω). {
    intros x Hx. apply (ω_trans _ (m⁺⁺))...
  }
  assert (Happ: ∀x ∈ A, f[x] ≠ m⁺ → f[x]⁺ ∈ m⁺⁺). {
    intros x Hx Hnq. apply Hap in Hx as H.
    apply (suc_preserve_lt (f[x]))...
    apply BUnionE in H as []... apply SingE in H...
  }
  set (Func A A (λ x,
    match (ixm (f[x] = m⁺)) with
      | inl _ => f⁻¹[0]
      | inr _ => f⁻¹[f[x]⁺]
    end
  )) as g.
  assert (Hg: g: A ⟺ A). {
    apply meta_bijection.
    - intros x Hx. destruct (ixm (f[x] = m⁺)); eapply ap_ran...
    - intros x1 H1 x2 H2 Heq.
      destruct (ixm (f[x1] = m⁺)) as [Hfx1|Hfx1];
      destruct (ixm (f[x2] = m⁺)) as [Hfx2|Hfx2].
      + apply (injectiveE f)...
      + exfalso. apply injectiveE in Heq... eapply suc_neq_0...
        rewrite Hdf'. apply Happ...
      + exfalso. apply injectiveE in Heq... eapply suc_neq_0...
        rewrite Hdf'. apply Happ...
      + apply injectiveE in Heq... apply suc_injective in Heq...
        apply injectiveE in Heq...
        rewrite Hdf'. apply Happ...
        rewrite Hdf'. apply Happ...
    - intros y Hy. set (f[y]) as n. assert (Hnw: n ∈ ω)...
      ω_destruct n.
      + exists (f⁻¹[m⁺]). split. eapply ap_ran...
        destruct (ixm (f[(f⁻¹)[m⁺]] = m⁺)).
        * rewrite pred, <- H, inv_dom_reduction...
        * rewrite inv_ran_reduction in n... rewrite Hrf...
      + assert (Hn'm: n ∈ m⁺⁺). {
          apply BUnionI1. apply suc_preserve_lt...
          rewrite <- Heq. eapply ap_ran...
        }
        exists (f⁻¹[n]). split. eapply ap_ran...
        destruct (ixm (f[(f⁻¹)[n]] = m⁺)).
        * exfalso. rewrite inv_ran_reduction in e...
          apply Hap in Hy. rewrite <- e, <- Heq in Hy.
          apply (nat_irrefl (f[y]))...
        * rewrite inv_ran_reduction, <- Heq, inv_dom_reduction...
  }
  exists g. apply SepI.
  - apply permutation_iff...
  - intros a Ha Heq. unfold g in Heq.
    rewrite meta_func_ap in Heq; [|apply bijection_is_func|]...
    destruct (ixm (f[a] = m⁺)).
    + rewrite <- Heq, inv_ran_reduction in e... eapply suc_neq_0...
    + assert (f[f⁻¹[f[a]⁺]] = f[a]) by congruence.
      rewrite inv_ran_reduction in H...
      * apply (nat_neq_suc (f[a]))...
      * rewrite Hrf. apply Happ...
Qed.

(* ==需要选择公理== *)
(* 任意无限集，存在其洗牌 *)
Lemma infinite_shuffle_exists : AC_VI → ∀ A,
  infinite A → ⦿ Shuffle A.
Proof with eauto; try congruence.
  intros AC6 A Hinf.
  apply set_infinite_iff_card_infinite in Hinf.
  assert (Hinfc: |A| ⋵ 𝐂𝐃ⁱⁿᶠ) by (split; auto).
  pose proof (cardAdd_infcard_self AC6 (|A|) Hinfc). simpl in H.
  rewrite cardAdd in H. apply CardAx1 in H as [f Hf].
  apply inv_bijection in Hf as Hf'.
  apply bijection_is_func in Hf as [Hf [Hif Hrf]].
  apply bijection_is_func in Hf' as [Hf' [Hif' Hrf']].
  assert (H := Hf). destruct H as [Hff [Hdf _]].
  assert (H := Hf'). destruct H as [Hff' [Hdf' _]].
  set (Func A A (λ a, match (ixm (π2 f⁻¹[a] = 0)) with
    | inl _ => f[<π1 f⁻¹[a], 1>]
    | inr _ => f[<π1 f⁻¹[a], 0>]
  end)) as g.
  assert (Hf'Ap: ∀x ∈ A, f⁻¹[x] ∈ A × { 0 ,} ∪ A × { 1 ,}). {
    intros x Hx. rewrite <- Hdf' in Hx. eapply ap_ran...
  }
  assert (Hπ1: ∀x ∈ A, π1 f⁻¹[x] ∈ A). {
    intros x Hx. apply Hf'Ap in Hx.
    apply BUnionE in Hx as [];
    apply CPrdE1 in H as [a [Ha [b [_ H]]]];
    rewrite H; zfc_simple.
  }
  assert (Hpair: ∀x ∈ A, is_pair f⁻¹[x]). {
    intros x Hx. apply Hf'Ap in Hx.
    apply BUnionE in Hx as []; apply cprd_is_pairs in H...
  }
  assert (Hπ2: ∀x ∈ A, π2 f⁻¹[x] ≠ 0 → π2 f⁻¹[x] = 1). {
    intros x Hx H0. rewrite <- Hdf' in Hx.
    apply func_correct in Hx... apply ranI in Hx.
    rewrite Hrf' in Hx. apply BUnionE in Hx as [].
    - apply CPrdE1 in H as [a [Ha [b [Hb H]]]].
      apply SingE in Hb. rewrite H in H0. zfc_simple.
    - apply CPrdE1 in H as [a [Ha [b [Hb H]]]].
      apply SingE in Hb. rewrite H. zfc_simple.
  }
  assert (Hg: g: A ⟺ A). {
    apply meta_bijection.
    - intros x Hx.
      destruct (ixm (π2 f⁻¹[x] = 0)); eapply ap_ran...
      + apply BUnionI2. apply CPrdI...
      + apply BUnionI1. apply CPrdI...
    - intros x1 H1 x2 H2 Heq.
      assert (H10: <π1 f⁻¹[x1], 0> ∈ dom f). {
        rewrite Hdf. apply BUnionI1. apply CPrdI...
      }
      assert (H11: <π1 f⁻¹[x1], 1> ∈ dom f). {
        rewrite Hdf. apply BUnionI2. apply CPrdI...
      }
      assert (H20: <π1 f⁻¹[x2], 0> ∈ dom f). {
        rewrite Hdf. apply BUnionI1. apply CPrdI...
      }
      assert (H21: <π1 f⁻¹[x2], 1> ∈ dom f). {
        rewrite Hdf. apply BUnionI2. apply CPrdI...
      }
      apply Hpair in H1 as Hp1. apply op_η in Hp1.
      apply Hpair in H2 as Hp2. apply op_η in Hp2.
      destruct (ixm (π2 f⁻¹[x1] = 0));
      destruct (ixm (π2 f⁻¹[x2] = 0));
      apply injectiveE in Heq; auto;
      apply op_iff in Heq as [Heq1 Heq2]...
      + assert (<π1 f⁻¹[x1], π2 f⁻¹[x1]> = <π1 f⁻¹[x2], π2 f⁻¹[x2]>)...
        rewrite <- Hp1, <- Hp2 in H. apply injectiveE in H...
      + exfalso. eapply suc_neq_0...
      + exfalso. eapply suc_neq_0...
      + apply Hπ2 in n... apply Hπ2 in n0...
        assert (<π1 f⁻¹[x1], π2 f⁻¹[x1]> = <π1 f⁻¹[x2], π2 f⁻¹[x2]>)...
        rewrite <- Hp1, <- Hp2 in H. apply injectiveE in H...
    - intros y Hy.
      rewrite <- Hdf' in Hy.
      apply func_correct in Hy...
      apply ranI in Hy as Hx. apply domI in Hy.
      rewrite Hrf' in Hx.
      apply BUnionE in Hx as [];
      apply CPrdE1 in H as [a [Ha [b [Hb H]]]];
      apply SingE in Hb; subst b. {
        exists (f[<a, 1>]). split.
        - eapply ap_ran... apply BUnionI2. apply CPrdI...
        - assert (Hp: <a, 1> ∈ dom f). {
            rewrite Hdf. apply BUnionI2. apply CPrdI...
          }
          destruct (ixm (π2 f⁻¹[f[<a, 1>]] = 0)).
          + rewrite inv_dom_reduction in e...
            zfc_simple. exfalso. eapply suc_neq_0...
          + rewrite inv_dom_reduction... zfc_simple.
            rewrite <- H, inv_ran_reduction...
      } {
        exists (f[<a, 0>]). split.
        - eapply ap_ran... apply BUnionI1. apply CPrdI...
        - assert (Hp: <a, 0> ∈ dom f). {
            rewrite Hdf. apply BUnionI1. apply CPrdI...
          }
          destruct (ixm (π2 f⁻¹[f[<a, 0>]] = 0)).
          + rewrite inv_dom_reduction... zfc_simple.
            rewrite <- H, inv_ran_reduction...
          + rewrite inv_dom_reduction in n... zfc_simple.
      }
  }
  exists g. apply shuffle_iff. split...
  intros a Ha Hap. unfold g in Hap.
  rewrite meta_func_ap in Hap; [|apply bijection_is_func|]...
  destruct (ixm (π2 f⁻¹[a] = 0)).
  - assert (f⁻¹[a] = f⁻¹[f[<π1 f⁻¹[a], 1>]])...
    rewrite inv_dom_reduction in H...
    + rewrite H in e. zfc_simple. eapply suc_neq_0...
    + rewrite Hdf. apply BUnionI2. apply CPrdI...
  - assert (f⁻¹[a] = f⁻¹[f[<π1 f⁻¹[a], 0>]])...
    rewrite inv_dom_reduction in H...
    + rewrite H in n. zfc_simple.
    + rewrite Hdf. apply BUnionI1. apply CPrdI...
Qed.

(* ==需要选择公理== *)
(* 任意基数大于等于2的集合，存在其洗牌 *)
Lemma shuffle_exists : AC_VI → ∀ A, 2 ≤ |A| → ⦿ Shuffle A.
Proof with auto.
  intros AC3 A H2.
  destruct (classic (finite A)).
  - apply finite_shuffle_exists...
  - apply infinite_shuffle_exists...
Qed.

(* ==需要选择公理== *)
(* 无限基数的阶乘大于等于自身 *)
Lemma cardLe_infcard_factorial : AC_VI →
  ∀𝜅 ⋵ 𝐂𝐃ⁱⁿᶠ, 𝜅 ≤ 𝜅!.
Proof with neauto; try congruence.
  intros AC6 𝜅 [Hcd Hinf].
  assert (AC3': AC_III'). { apply AC_VI_to_III'... }
  rewrite card_of_card at 1... clear Hcd.
  apply cardLe_iff. rename 𝜅 into A.
  set {Shuffle (A - {a,}) | a ∊ A} as 𝒮.
  pose proof (AC3' 𝒮) as [F [HfF [HdF HrF]]]. {
    intros S HS. apply ReplAx in HS as [B [HB HS]]. subst S.
    apply shuffle_exists... apply cardLt_infcard_n...
    split... rewrite <- set_infinite_iff_card_infinite.
    apply remove_one_member_from_infinite...
  }
  set (λ a, F[Shuffle (A - {a,})]) as F'.
  set (λ a, F' a ∪ Ident {a,}) as G.
  set (Func A (Permutation A) G) as g.
  assert (HS: ∀a ∈ A, Shuffle (A - {a,}) ∈ 𝒮). {
    intros a Ha. apply ReplAx. exists a. split...
  }
  assert (Hdj: ∀a ∈ A, (A - {a,}) ∩ {a,} = ∅). {
    intros a Ha. ext Hx; [exfalso|exfalso0].
    apply BInterE in Hx as [H1 H2]. apply SepE2 in H1...
  }
  assert (HF'a: ∀a ∈ A,
    (F' a : A - {a,} ⟺ A - {a,}) ∧
    ∀x ∈ A - {a,}, (F' a)[x] ≠ x
  ). {
    intros a Ha. apply HS in Ha.
    apply HrF in Ha. apply shuffle_iff...
  }
  assert (HGa: ∀a ∈ A, G a: A ⟺ A). {
    intros a Ha.
    rewrite <- (remove_one_member_then_return A a) at 1 2...
    apply bunion_bijection.
    - apply HF'a...
    - apply ident_bijection.
    - intros x Hx. rewrite Hdj in Hx... exfalso0.
    - intros y Hy. rewrite Hdj in Hy... exfalso0.
  }
  assert (Huap: ∀a ∈ A,
    (∀x ∈ A - {a,}, (G a)[x] = (F' a)[x]) ∧
    ∀x ∈ {a,}, (G a)[x] = (Ident {a,})[x]
  ). {
    intros a Ha. eapply bunion_func_ap.
    - apply bijection_is_func. apply HF'a...
    - apply bijection_is_func. apply ident_bijection.
    - intros x Hx. rewrite Hdj in Hx... exfalso0.
    - intros y Hy. rewrite Hdj in Hy... exfalso0.
  }
  assert (Heq1: ∀ a ∈ A, (G a)[a] = a). {
    intros a Ha. rewrite <- (ident_ap {a,} a) at 3...
    apply Huap in Ha as [_ Heq]. rewrite Heq...
  }
  assert (Heq2: ∀ a x ∈ A, (G a)[x] = x → a = x). {
    intros a Ha x Hx Hap.
    contra.
    assert (x ∈ A - {a,}). { apply SepI... apply SingNI... }
    pose proof (Huap a Ha) as [Heq _].
    rewrite Heq in Hap... eapply (HF'a a Ha)...
  }
  exists g. apply meta_injection.
  - intros a Ha. apply permutation_iff. apply HGa...
  - intros x1 H1 x2 H2 Heq.
    assert ((G x1)[x2] = (G x2)[x2])... rewrite Heq1 in H...
Qed.

(* ==需要选择公理== *)
(* 无限基数的阶乘是无限基数 *)
Lemma cardFactorial_infinite : AC_VI →
  ∀𝜅 ⋵ 𝐂𝐃ⁱⁿᶠ, infinite (𝜅!).
Proof with eauto.
  intros AC6 𝜅 Hinf.
  assert (AC3: AC_III). { apply AC_VI_to_III... }
  pose proof (aleph0_is_the_least_infinite_card AC3 _ Hinf)...
  apply cardGeq_aleph0_infinite. unfold CardFactorial...
  eapply cardLe_trans; revgoals... apply cardLe_infcard_factorial...
Qed.

(* ==需要选择公理== *)
(* ex6_36: 无限基数的阶乘等于2的幂 *)
Theorem cardFactorial_infcard_eq_2_pow : AC_VI →
  ∀𝜅 ⋵ 𝐂𝐃ⁱⁿᶠ, 𝜅! = 2 ^ 𝜅.
Proof with neauto; try congruence.
  intros AC6 𝜅 [Hcd Hinf].
  assert (AC3: AC_III). { apply AC_VI_to_III... }
  assert (AC3': AC_III'). { apply AC_III_iff_III'... }
  eapply cardLe_antisym. {
    eapply cardLe_trans.
    - apply cardLe_iff. apply dominate_sub.
      intros x Hx. apply SepE in Hx as [Hx _]. apply Hx.
    - rewrite <- cardExp, <- card_of_card...
      apply eq_cardLe... apply cardExp_infcard_self... split...
  }
  rewrite <- (cardAdd_absorption AC6 (𝜅!) 𝜅); revgoals. {
    apply cardLe_infcard_factorial... split...
  } {
    apply cardFactorial_infinite... split...
  }
  unfold CardFactorial.
  rewrite (card_of_card 𝜅) at 3...
  rewrite cardAdd. apply cardLe_iff. rename 𝜅 into A.
  set {B ∊ 𝒫 A | 2 ≤ (|B|)} as ℬ.
  set {Shuffle B | B ∊ ℬ} as 𝒮.
  pose proof (AC3' 𝒮) as [F [HfF [HdF HrF]]]. {
    intros S HS. apply ReplAx in HS as [B [HB HS]]. subst S.
    apply SepE in HB as [_ H2]. apply shuffle_exists...
  }
  set (λ f, {a ∊ A | f[a] = 0}) as O.
  set (λ f, {a ∊ A | f[a] = 1}) as I.
  set (λ X, F[Shuffle X]) as shuffle.
  set (λ f, shuffle (O f) ∪ Ident (I f)) as G.
  set (λ f, match (ixm (|O f| = 0)) with
    | inl _ => <Ident A, 0>
    | inr _ => match (ixm (|O f| = 1)) with
      | inl _ => <⋃(O f), 1>
      | inr _ => <G f, 0>
    end
  end) as G'.
  set (Func (A ⟶ 2) (Permutation A × {0,} ∪ A × {1,}) G') as g.
  assert (HOf: ∀f ∈ A ⟶ 2, O f ∈ 𝒫 A). {
    intros f Hf. apply PowerAx. intros x Hx.
    apply SepE1 in Hx...
  }
  assert (HSf: ∀f ∈ A ⟶ 2, 2 ≤ |O f| → Shuffle (O f) ∈ 𝒮). {
    intros f Hf H2. apply ReplAx. exists (O f). split... apply SepI...
  }
  assert (Hsf: ∀f ∈ A ⟶ 2, 2 ≤ |O f| → shuffle (O f) : O f ⟺ O f ∧
    ∀a ∈ O f, (shuffle (O f))[a] ≠ a). {
    intros f Hf Hle. pose proof (HSf f Hf Hle).
    apply HrF in H. apply SepE in H as [H1 H2]. split...
    apply permutation_iff...
  }
  assert (Hdj: ∀f ∈ A ⟶ 2, O f ∩ I f = ∅). {
    intros f Hf. ext Hx; [exfalso|exfalso0].
    apply BInterE in Hx as [H1 H2].
    apply SepE in H1 as [_ H1].
    apply SepE in H2 as [_ H2].
    rewrite H1 in H2. eapply suc_neq_0...
  }
  assert (Hfx: ∀f ∈ A ⟶ 2, ∀x ∈ A, f[x] = 0 ∨ f[x] = 1). {
    intros f Hf x Hx.
    apply arrow_iff in Hf as [_ [_ Hrf]].
    apply Hrf in Hx. rewrite two in Hx.
    apply PairE in Hx. rewrite one...
  }
  assert (HeqA: ∀f ∈ A ⟶ 2, A = O f ∪ I f). {
    intros f Hf. ext Hx.
    - pose proof (Hfx f Hf x Hx) as [].
      + apply BUnionI1. apply SepI...
      + apply BUnionI2. apply SepI...
    - apply BUnionE in Hx as []; apply SepE1 in H...
  }
  assert (HGf: ∀f ∈ A ⟶ 2, 2 ≤ |O f| → G f: A ⟺ A). {
    intros f Hf Hle. erewrite HeqA...
    apply bunion_bijection.
    - apply Hsf...
    - apply ident_bijection.
    - intros x Hx. rewrite Hdj in Hx... exfalso0.
    - intros x Hx. rewrite Hdj in Hx... exfalso0.
  }
  assert (HGfx: ∀f ∈ A ⟶ 2, 2 ≤ |O f| →
    (∀x ∈ O f, (G f)[x] = (shuffle (O f))[x]) ∧
    (∀x ∈ I f, (G f)[x] = (Ident (I f))[x])
  ). {
    intros f Hf Hle.
    eapply bunion_func_ap...
    - apply bijection_is_func. apply Hsf...
    - apply bijection_is_func. apply ident_bijection.
    - intros x Hx. rewrite Hdj in Hx... exfalso0.
    - intros x Hx. rewrite Hdj in Hx... exfalso0.
  }
  assert (Hnq0: ∀f ∈ A ⟶ 2, |O f| = 0 → ∀x ∈ A, f[x] ≠ 0). {
    intros f Hf H x Hx H0. rewrite card_eq_0 in H.
    eapply EmptyE. apply H. apply SepI...
  }
  assert (Hnqx: ∀f ∈ A ⟶ 2, 2 ≤ |O f| → ∀x ∈ O f, (G f)[x] ≠ x). {
    intros f Hf Hle x Hx.
    pose proof (HGfx f Hf Hle) as [Heq _].
    rewrite Heq... apply Hsf...
  }
  assert (Heqx: ∀f ∈ A ⟶ 2, 2 ≤ |O f| → ∀x ∈ I f, (G f)[x] = x). {
    intros f Hf Hle x Hx.
    pose proof (HGfx f Hf Hle) as [_ Heq].
    rewrite Heq... apply ident_ap...
  }
  exists g. apply meta_injection.
  - intros f Hf. unfold G'.
    destruct (ixm (|O f| = 0)). {
      apply BUnionI1. apply CPrdI...
      apply permutation_iff. apply ident_bijection.
    }
    destruct (ixm (|O f| = 1)). {
      apply BUnionI2. apply CPrdI...
      apply card_eq_1 in e as [a Heq].
      rewrite Heq, union_single.
      assert (Ha: a ∈ O f) by (rewrite Heq; auto).
      apply SepE1 in Ha...
    }
    apply BUnionI1. apply CPrdI...
    apply permutation_iff... apply HGf...
    apply card_neq_0_and_1...
  - intros f1 H1 f2 H2 Heq. unfold G' in Heq.
    destruct (ixm (|O f1| = 0)) as [H10|H10];
    destruct (ixm (|O f2| = 0)) as [H20|H20].
    + apply arrow_iff in H1 as H. destruct H as [Hf1 [Hd1 _]].
      apply arrow_iff in H2 as H. destruct H as [Hf2 [Hd2 _]].
      eapply func_ext_intro... intros x Hx. rewrite Hd1 in Hx.
      pose proof (Hnq0 f1 H1 H10 x Hx).
      pose proof (Hnq0 f2 H2 H20 x Hx).
      pose proof (Hfx f1 H1 x Hx) as [];
      pose proof (Hfx f2 H2 x Hx) as []...
    + destruct (ixm (|O f2| = 1)) as [H21|H21].
      * apply op_iff in Heq as [_ H]. exfalso. eapply suc_neq_0...
      * exfalso.
        apply op_iff in Heq as [Heq _].
        assert (Hle: 2 ≤ |O f2|). { apply card_neq_0_and_1... }
        apply card_neq_0 in H20 as [a Ha].
        apply Hnqx in Ha as Hnq... apply Hnq. rewrite <- Heq.
        apply ident_ap. apply SepE1 in Ha...
    + destruct (ixm (|O f1| = 1)) as [H11|H11].
      * apply op_iff in Heq as [_ H]. exfalso. eapply suc_neq_0...
      * exfalso.
        apply op_iff in Heq as [Heq _].
        assert (Hle: 2 ≤ |O f1|) by (apply card_neq_0_and_1; auto).
        apply card_neq_0 in H10 as [a Ha].
        apply Hnqx in Ha as Hnq... apply Hnq. rewrite Heq.
        apply ident_ap. apply SepE1 in Ha...
    + destruct (ixm (|O f1| = 1)) as [H11|H11];
      destruct (ixm (|O f2| = 1)) as [H21|H21].
      * apply op_iff in Heq as [H _].
        apply card_eq_1 in H11 as [a Heqa].
        apply card_eq_1 in H21 as [b Heqb].
        rewrite Heqa, Heqb, union_single, union_single in H.
        assert (Heq: O f1 = O f2)...
        clear H10 H20 a Heqa b Heqb H.
        apply arrow_iff in H1 as H. destruct H as [Hf1 [Hd1 Hr1]].
        apply arrow_iff in H2 as H. destruct H as [Hf2 [Hd2 Hr2]].
        apply func_ext_intro... intros x Hx. rewrite Hd1 in Hx...
        pose proof (Hfx f1 H1 x Hx) as [Hf10|Hf11];
        pose proof (Hfx f2 H2 x Hx) as [Hf20|Hf21]... {
          assert (x ∈ O f1). { apply SepI... }
          rewrite Heq in H. apply SepE in H as [_ Hf20].
          exfalso. rewrite Hf20 in Hf21. eapply suc_neq_0...
        } {
          assert (x ∈ O f2). { apply SepI... }
          rewrite <- Heq in H. apply SepE in H as [_ Hf10].
          exfalso. rewrite Hf10 in Hf11. eapply suc_neq_0...
        }
      * apply op_iff in Heq as [_ H]. exfalso. eapply suc_neq_0...
      * apply op_iff in Heq as [_ H]. exfalso. eapply suc_neq_0...
      * apply op_iff in Heq as [H _].
        apply arrow_iff in H1 as H'. destruct H' as [Hf1 [Hd1 Hr1]].
        apply arrow_iff in H2 as H'. destruct H' as [Hf2 [Hd2 Hr2]].
        apply func_ext_intro...
        intros x Hx. rewrite Hd1 in Hx...
        assert (Hle1: 2 ≤ |O f1|) by (apply card_neq_0_and_1; auto).
        assert (Hle2: 2 ≤ |O f2|) by (apply card_neq_0_and_1; auto).
        assert (Heq: (G f1)[x] = (G f2)[x]) by congruence.
        pose proof (Hfx f1 H1 x Hx) as [Hf10|Hf11];
        pose proof (Hfx f2 H2 x Hx) as [Hf20|Hf21]... {
          assert (Hx0: x ∈ O f1) by (apply SepI; auto).
          assert (Hx1: x ∈ I f2) by (apply SepI; auto).
          apply Hnqx in Hx0... apply Heqx in Hx1...
        } {
          assert (Hx0: x ∈ O f2) by (apply SepI; auto).
          assert (Hx1: x ∈ I f1) by (apply SepI; auto).
          apply Hnqx in Hx0... apply Heqx in Hx1...
        }
Qed.

(** cardFactorial misc **)

(* 0的阶乘等于1 *)
Fact cardFactorial_0 : 0! = 1.
Proof with nauto; try easy.
  rewrite (card_of_nat 1)... apply CardAx1.
  replace (Embed 1) with (Permutation 0)...
  ext Hx.
  - apply SepE in Hx as [Hx _]. apply SepE in Hx as [Hx _].
    rewrite cprd_0_r, power_empty, <- one in Hx...
  - rewrite one in Hx. apply SingE in Hx. subst x.
    apply permutation_iff. apply empty_bijection.
Qed.

(* 1的阶乘等于1 *)
Fact cardFactorial_1 : 1! = 1.
Proof with nauto; try easy.
  rewrite <- (card_of_single {<∅, ∅>,}) at 2. apply CardAx1.
  replace {{<∅, ∅>,},} with (Permutation 1)...
  ext Hx.
  - apply SepE in Hx as [Hx [_ [Hd _]]]. apply SepE in Hx as [Hx _].
    rewrite one in Hx. unfold One in Hx.
    rewrite cprd_single_single, power_single in Hx.
    apply PairE in Hx as []; subst...
    assert (0 ∈ 1). { apply suc_has_0... }
    rewrite <- Hd in H. apply domE in H as [y Hp]. exfalso0.
  - assert (Hf: {<∅, ∅>,}: {∅,} ⟺ {∅,}) by apply single_pair_bijection.
    rewrite one. apply SingE in Hx; subst. apply permutation_iff...
Qed.

(* 基数阶乘保持序关系 *)
Lemma cardFactorial_preserve_le : ∀ A B, |A| ≤ |B| → A! ≤ B!.
Proof with eauto; try congruence.
  intros. apply cardLe_iff.
  apply cardLe_iff in H as [g [Hig [Hdg Hrg]]].
  set (λ f, g ∘ f ∘ g⁻¹) as ℱ.
  assert (Hgbi: g: A ⟺ ran g) by (split; auto).
  assert (Hcom: ∀ f, f: A ⟺ A → g ∘ f ∘ g⁻¹: ran g ⟺ ran g). {
    intros f Hf. eapply bijection_transform...
  }
  set (λ f, ℱ f ∪ Ident (B - ran g)) as ℱ'.
  set (Func (Permutation A) (Permutation B) ℱ') as F.
  exists F. apply meta_injection. {
    intros f Hf. unfold ℱ', ℱ.
    apply permutation_iff.
    apply permutation_iff in Hf.
    apply Hcom in Hf as [Hic [Hdc Hrc]].
    split; [|split].
    - apply bunion_injective...
      apply ident_injective. split.
      + intros x Hx. exfalso.
        apply BInterE in Hx as [H1 H2]. rewrite Hdc in H1.
        rewrite dom_ident in H2. apply SepE in H2 as [_ Hx]...
      + intros y Hy. exfalso.
        apply BInterE in Hy as [H1 H2]. rewrite Hrc in H1.
        rewrite ran_ident in H2. apply SepE in H2 as [_ Hy]...
    - ext Hx.
      + apply domE in Hx as [y Hp].
        apply BUnionE in Hp as []; apply domI in H.
        * apply Hrg...
        * rewrite dom_ident in H. apply SepE1 in H...
      + destruct (classic (x ∈ ran g)).
        * eapply domI. apply BUnionI1.
          apply func_correct... destruct Hic... 
        * eapply domI. apply BUnionI2.
          apply identI. apply SepI...
    - ext y Hy.
      + apply ranE in Hy as [x Hp].
        apply BUnionE in Hp as []; apply ranI in H.
        * apply Hrg...
        * rewrite ran_ident in H. apply SepE1 in H...
      + destruct (classic (y ∈ ran g)).
        * rewrite <- Hrc in H. apply ranE in H as [x Hp].
          eapply ranI. apply BUnionI1...
        * eapply ranI. apply BUnionI2.
          apply identI. apply SepI...
  } {
    intros f1 Hf1 f2 Hf2 Heq.
    apply disjoint_bunion_injective in Heq; revgoals. {
      apply disjointI. intros [x [H1 H2]]. unfold ℱ in H1.
      apply permutation_iff in Hf2.
      apply Hcom in Hf2 as [[Hcf _] [Hdc Hrc]].
      apply func_pair in H1 as Heqx... rewrite Heqx in H1, H2.
      apply domI in H1. rewrite Hdc in H1.
      apply domI in H2. rewrite dom_ident in H2.
      apply SepE2 in H2...
    } {
      apply disjointI. intros [x [H1 H2]]. unfold ℱ in H1.
      apply permutation_iff in Hf1.
      apply Hcom in Hf1 as [[Hcf _] [Hdc Hrc]].
      apply func_pair in H1 as Heqx... rewrite Heqx in H1, H2.
      apply domI in H1. rewrite Hdc in H1.
      apply domI in H2. rewrite dom_ident in H2.
      apply SepE2 in H2...
    }
    apply permutation_iff in Hf1 as [[[Hrel1 _] _] [Hdf1 Hrf1]].
    apply permutation_iff in Hf2 as [[[Hrel2 _] _] [Hdf2 Hrf2]].
    assert (H1: (ℱ f1) ∘ g  = (ℱ f2) ∘ g) by congruence.
    unfold ℱ in H1. rewrite
      compo_assoc, compo_inv_dom_ident, Hdg, <- Hdf1,
      compo_assoc, right_compo_ident, restr_to_dom,
      compo_assoc, compo_inv_dom_ident, Hdg, <- Hdf2,
      compo_assoc, right_compo_ident, restr_to_dom in H1...
    assert (H2: g⁻¹ ∘ (g ∘ f1) = g⁻¹ ∘ (g ∘ f2)) by congruence.
    rewrite
      <- compo_assoc, compo_inv_dom_ident, Hdg, <- Hdf1,
      left_compo_ident', Hdf1, <- Hrf1,
      <- inv_dom, restr_to_dom, inv_inv,
      <- compo_assoc, compo_inv_dom_ident, Hdg, <- Hdf2,
      left_compo_ident', Hdf2, <- Hrf2,
      <- inv_dom, restr_to_dom, inv_inv in H2...
  }
Qed.
