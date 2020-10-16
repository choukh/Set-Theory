(** Based on "Elements of Set Theory" Chapter 6 Part 4 EX 1 **)
(** Coq coding by choukh, Sep 2020 **)

Require Export ZFC.EST6_4.

(*** EST第六章4扩展1：选择公理的系统考察：图基引理，豪斯多夫极大原理 ***)

(* 有限特征条件：集合满足条件当且仅当该集合的每个有限子集都满足条件 *)
Definition finite_character_property : (set → Prop) → Prop := λ P,
  ∀ B, P B ↔ ∀ C, finite C → C ⊆ B → P C.

(* 有限特征集：集合是其成员当且仅当该集合的每个有限子集都是其成员 *)
Definition finite_character_set : set → Prop := λ 𝒜,
  finite_character_property (λ x, x ∈ 𝒜).
Notation "'𝗙𝗖' 𝒜" := (finite_character_set 𝒜) (at level 70).

(* 选择公理等效表述7：图基引理（第二极大原理） *)
(* 具有有限特征的非空集合必有子集关系下的极大元 *)
Definition AC_VII : Prop := ∀ 𝒜, ⦿ 𝒜 →
  𝗙𝗖 𝒜 → ∃ M, max_member M 𝒜.

(* 链集：集合的所有全序子集所组成的集合 *)
Definition Chains : set → set := λ A, {ℬ ∊ 𝒫 A | is_chain}.

(* 极大链：链集的极大元 *)
Definition max_chain : set → set → Prop := λ ℳ 𝒜,
  max_member ℳ (Chains 𝒜).

(* 选择公理等效表述8：豪斯多夫极大原理 *)
(* 对于偏序集中任意全序子集(链)，都存在极大全序子集(极大链)包含它 *)
Definition AC_VIII : Prop := ∀ 𝒜 ℬ, ℬ ⊆ 𝒜 → is_chain ℬ →
  ∃ ℳ, max_chain ℳ 𝒜 ∧ ℬ ⊆ ℳ.

(* 选择公理等效表述8'：极大原理 *)
(* 偏序集有极大元，如果对于该偏序集中的任意链，
  都存在该偏序集中的一个成员，包含链中的所有成员 *)
Definition AC_VIII' : Prop := ∀ 𝒜,
  (∀ ℬ, ℬ ⊆ 𝒜 → is_chain ℬ → ∃N ∈ 𝒜, ∀B ∈ ℬ, B ⊆ N) →
  ∃ M, max_member M 𝒜.

(* 空集是链 *)
Lemma emptyset_is_chain : is_chain ∅.
Proof. intros x Hx. exfalso0. Qed.

(* 链的子集仍是链 *)
Lemma sub_of_chain_is_chain : ∀ ℬ 𝒞, is_chain ℬ → 𝒞 ⊆ ℬ → is_chain 𝒞.
Proof.
  intros * Hchn Hsub C HC D HD. apply Hchn; apply Hsub; auto.
Qed.

(* 非空有限链必有极大元 *)
Lemma finite_chain_has_max : ∀ ℬ, ⦿ ℬ →
  finite ℬ → is_chain ℬ → ∃ M, max_member M ℬ.
Proof with eauto; try congruence.
  intros ℬ Hne [n [Hn Hqn]]. generalize dependent ℬ.
  set {n ∊ ω | λ n, ∀ ℬ,
    ⦿ ℬ → ℬ ≈ n → is_chain ℬ → ∃ M, max_member M ℬ } as N.
  ω_induction N Hn; intros ℬ Hne Hqn Hchn. {
    exfalso. apply EmptyNI in Hne. apply eqnum_empty in Hqn...
  }
  destruct Hne as [B HB].
  apply split_one_element in HB as Heq.
  destruct (classic (ℬ - ⎨B⎬ = ∅)) as [|Hne]. {
    exists B. split... intros x Hx.
    apply sub_iff_no_comp in H. apply H in Hx. apply SingE in Hx...
  }
  pose proof (IH (ℬ - ⎨B⎬)) as [M [HM Hmax]].
  - apply EmptyNE...
  - apply finite_set_remove_one_element...
  - eapply sub_of_chain_is_chain...
  - assert (HM': M ∈ ℬ). { apply SepE in HM as []... }
    pose proof (Hchn B HB M HM') as [].
    + exists M. split... intros x Hx.
      destruct (classic (x = B)).
      * subst x. destruct (classic (M ⊆ B))... right. apply sub_asym...
      * apply Hmax. apply SepI... apply SingNI...
    + exists B. split... intros x Hx.
      destruct (classic (x = B))...
      destruct (Hmax x). { apply SepI... apply SingNI... }
      * left. intros Hsub. apply H1. eapply sub_tran...
      * left. subst x. intros Hsub. apply H0. apply sub_asym...
Qed.

(* AC cycle
    6 → 7 → 8 → 8' → 6
*)

Theorem AC_VI_to_AC_VII : AC_VI → AC_VII.
Proof with eauto.
  unfold AC_VI, AC_VII.
  intros Zorn 𝒜 [A HA] Hfc. apply Zorn.
  intros ℬ Hchn Hs1. apply Hfc.
  intros C Hfin Hs2. destruct (classic (C = ∅)). {
    eapply Hfc in HA. apply HA. apply Hfin.
    subst C. apply empty_sub_all.
  }
  cut (∃B ∈ ℬ, C ⊆ B). {
    intros [B [HB Hs3]]. apply Hs1 in HB.
    apply Hfc with B C in HB...
  }
  set {p ∊ C × ℬ | λ p, π1 p ∈ π2 p} as R.
  pose proof (AC_VI_to_I Zorn) as AC1.
  pose proof (AC1 R) as [F [HfF [HsF Hd]]]. { apply sep_cp_is_rel. }
  assert (HdF: dom F = C). {
    rewrite Hd. apply ExtAx. split; intros Hx.
    - apply domE in Hx as [y Hp]. apply SepE in Hp as [Hp _].
      apply CProdE1 in Hp as [Hx _]. zfcrewrite.
    - apply Hs2 in Hx as Hxb.
      apply UnionAx in Hxb as [B [HB Hxb]].
      eapply domI. apply SepI. apply CProdI... zfcrewrite.
  }
  assert (Hsub: ran F ⊆ ℬ). {
    intros y Hy. apply ranE in Hy as [x Hp].
    apply HsF in Hp. apply SepE in Hp as [Hp _].
    apply CProdE1 in Hp as [_ Hy]. zfcrewrite.
  }
  pose proof (finite_chain_has_max (ran F)) as [M [HM Hmax]].
  - apply EmptyNE in H as [c Hc].
    exists (F[c]). eapply ap_ran... split...
  - eapply dominated_by_finite_is_finite.
    apply domain_dominate_range... rewrite HdF...
  - intros D HD E HE. apply Hchn; apply Hsub...
  - exists M. split. apply Hsub...
    intros x Hx. rewrite <- HdF in Hx. apply domE in Hx as [B Hp].
    apply ranI in Hp as Hr. apply func_ap in Hp as Hap... subst B.
    apply HsF in Hp. apply SepE in Hp as [_ Hx]. zfcrewrite.
    destruct (Hmax (F[x])); auto; [|subst M]...
    apply Hsub in Hr. apply Hsub in HM.
    pose proof (Hchn M HM (F[x]) Hr) as [].
    exfalso... apply H1...
Qed.

(* 通过二元并从有限特征集构造具有有限特征的子集 *)
Lemma construct_fc_subset_by_bunion : ∀ 𝒜, 𝗙𝗖 𝒜 →
  ∀A ∈ 𝒜, 𝗙𝗖 {B ∊ 𝒜 | λ B, A ∪ B ∈ 𝒜}.
Proof with eauto.
  intros 𝒜 Hfc A HA. split.
  - intros HB C HfC HsC.
    apply SepE in HB as [HB Hu]. apply SepI.
    + eapply Hfc in HB...
    + apply Hfc. intros D HfD HsD.
      eapply Hfc in Hu... eapply sub_tran. apply HsD.
      rewrite bunion_comm, (bunion_comm A). apply sub_mono_bunion...
  - intros H. apply SepI.
    + apply Hfc. intros C HfC HsC.
      pose proof (H C HfC HsC) as HC. apply SepE in HC as []...
    + apply Hfc. intros C HfC HsC.
      set (B ∩ C) as D.
      assert (HD: D ∈ {B ∊ 𝒜 | λ B, A ∪ B ∈ 𝒜}). {
        apply H. apply (subset_of_finite_is_finite _ C)...
        intros x Hx. apply BInterE in Hx as []...
        intros x Hx. apply BInterE in Hx as []...
      }
      apply SepE in HD as [_ Hu].
      eapply Hfc in Hu... unfold D.
      rewrite bunion_binter_distr. intros x Hx.
      apply BInterI. apply HsC... apply BUnionI2...
Qed.

(* ==需要选择公理== *)
(* 对于有限特征集的任意成员都存在极大元包含它 *)
Lemma for_all_in_fc_set_ex_max_contains_it : AC_VII → ∀ 𝒜, 𝗙𝗖 𝒜 →
  ∀A ∈ 𝒜, ∃ M, max_member M 𝒜 ∧ A ⊆ M.
Proof with eauto; try congruence.
  intros AC7 𝒜 Hfc A HA.
  set {B ∊ 𝒜 | λ B, A ∪ B ∈ 𝒜} as 𝒜'.
  pose proof (AC7 𝒜') as [M [HM Hmax]].
  - exists A. apply SepI... rewrite bunion_self...
  - apply construct_fc_subset_by_bunion...
  - exists M. assert (Hu: A ∪ M ∈ 𝒜'). {
      apply SepE in HM as [_ Hu]. apply SepI...
      rewrite bunion_assoc, bunion_self...
    }
    assert (Hsub: A ⊆ M). {
      apply Hmax in Hu as [].
      - exfalso. apply H. intros x Hx. apply BUnionI2...
      - rewrite H. intros x Hx. apply BUnionI1...
    }
    split... split. apply SepE in HM as []...
    intros K HK. destruct (classic (M ⊆ K))... right.
    cut (K ∈ 𝒜'). { intros HK'. apply Hmax in HK' as []... }
    apply SepI... replace (A ∪ K) with K...
    apply ExtAx. split; intros Hx.
    * apply BUnionI2...
    * apply BUnionE in Hx as []... apply H. apply Hsub...
Qed.

(* 集合的链集具有有限特征 *)
Lemma set_of_all_chains_in_set_is_fc_set : ∀ A, 𝗙𝗖 (Chains A).
Proof with eauto.
  split.
  - intros HB C _ HsC.
    apply SepE in HB as [HsB Hchn]. apply PowerAx in HsB.
    apply SepI. apply PowerAx. eapply sub_tran...
    eapply sub_of_chain_is_chain...
  - intros H. apply SepI.
    + apply PowerAx. intros x Hx.
      assert (Hs: ⎨x⎬ ∈ Chains A). {
        apply H... intros s Hs. apply SingE in Hs. subst...
      }
      apply SepE in Hs as [Hs _]. apply PowerAx in Hs. apply Hs...
    + intros a Ha b Hb.
      destruct (classic (a = b)). { left. subst... }
      assert (Hp: {a, b} ∈ Chains A). {
        apply H. apply pair_finite...
        intros x Hx. apply PairE in Hx as []; subst...
      }
      apply SepE in Hp as [_ Hchn].
      apply Hchn. apply PairI1. apply PairI2.
Qed.

Theorem AC_VII_to_AC_VIII : AC_VII → AC_VIII.
Proof with auto.
  unfold AC_VIII.
  intros Tukey * Hsub Hchn.
  apply for_all_in_fc_set_ex_max_contains_it.
  apply Tukey. apply set_of_all_chains_in_set_is_fc_set.
  apply SepI... apply PowerAx...
Qed.

Theorem AC_VIII_to_AC_VIII' : AC_VIII → AC_VIII'.
Proof with auto.
  unfold AC_VIII, AC_VIII'.
  intros Hausdorff 𝒜 H.
  pose proof (Hausdorff 𝒜 ∅) as [ℳ [[HM Hmax] _]].
  { apply empty_sub_all. }
  { apply emptyset_is_chain. }
  apply SepE in HM as [HM Hchn]. apply PowerAx in HM.
  specialize H with ℳ as [N [HN Hmax']]...
  exists N. split... intros K HK.
  destruct (classic (N ⊆ K)) as [Hsub|]... right.
  apply sub_asym... apply Hmax'...
  replace ℳ with (ℳ ∪ ⎨K⎬). apply BUnionI2...
  cut (ℳ ∪ ⎨K⎬ ∈ Chains 𝒜). {
    intros Hu. apply Hmax in Hu as [Hm|]... exfalso.
    apply Hm. intros x Hx. apply BUnionI1...
  }
  apply SepI.
  - apply PowerAx. intros x Hx.
    apply BUnionE in Hx as [Hx|Hx]. apply HM...
    apply SingE in Hx. subst x...
  - intros C HC D HD.
    apply BUnionE in HC as [HC|HC]; apply BUnionE in HD as [HD|HD].
    + apply Hchn...
    + apply SingE in HD. subst D. left.
      eapply sub_tran. apply Hmax'... apply Hsub.
    + apply SingE in HC. subst C. right.
      eapply sub_tran. apply Hmax'... apply Hsub.
    + apply SingE in HC. apply SingE in HD. subst C D. left...
Qed.

Theorem AC_VIII'_to_AC_VI : AC_VIII' → AC_VI.
Proof with auto.
  unfold AC_VIII', AC_VI.
  intros MP A Hbnd.
  apply MP. intros B Hsub Hchn.
  pose proof (Hbnd _ Hchn Hsub) as Hu.
  exists (⋃ B). split... intros b Hb. apply ex2_3...
Qed.
