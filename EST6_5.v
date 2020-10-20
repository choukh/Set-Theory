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

(* 空集是可数集 *)
Lemma empty_countable : countable ∅.
Proof.
  apply countable_iff_finite_or_eqnum_ω.
  left. apply empty_finite.
Qed.

(* 可数集的子集仍是可数集 *)
Lemma subset_of_countable : ∀ A B,
  B ⊆ A → countable A → countable B.
Proof with auto.
  intros * Hsub [f [Hi [Hd Hr]]].
  exists (f ↾ B). split. apply restr_injective...
  split. apply restr_dom. destruct Hi... rewrite Hd...
  eapply sub_tran. apply restr_ran_included. apply Hr.
Qed.

(* 任意非空集合是可数集当且仅当它被ω满射 *)
Lemma countable_iff_mapped_onto_by_ω :
  ∀ A, ⦿ A → (∃ F, F: ω ⟹ A) ↔ countable A.
Proof. exact dominated_by_ω_iff_mapped_onto_by_ω. Qed.

(* ==需要选择公理== *)
(* 可数多个可数集的并是可数集 *)
Theorem countable_union_of_coutable_set : AC_II →
  ∀ 𝒜, countable 𝒜 → (∀A ∈ 𝒜, countable A) → countable (⋃ 𝒜).
Proof with eauto; try congruence.
  intros AC2 𝒜 Hcnt HcntA.
  set {A ∊ 𝒜 | λ A, ⦿ A} as 𝒜'.
  assert (Hsub: 𝒜' ⊆ 𝒜). {
    intros x Hx. apply SepE in Hx as []...
  }
  assert (Hequ: ⋃ 𝒜 = ⋃ 𝒜'). {
    apply ExtAx. split; intros Hx.
    - apply UnionAx in Hx as [A [HA Hx]].
      destruct (classic (A = ∅)). subst A. exfalso0.
      apply EmptyNE in H. apply UnionAx.
      exists A. split... apply SepI...
    - apply UnionAx in Hx as [A [HA Hx]]. apply UnionAx.
      exists A. split... apply SepE in HA as []...
  }
  apply (subset_of_countable _ 𝒜') in Hcnt...
  rewrite Hequ. clear Hequ.
  destruct (classic (𝒜' = ∅)) as [Heq|Hne]. {
    rewrite Heq, union_empty. apply empty_countable.
  }
  apply EmptyNE in Hne.
  apply countable_iff_mapped_onto_by_ω. {
    destruct Hne as [A HA]. apply SepE in HA as [HA [a Ha]].
    exists a. apply UnionAx. exists A. split...
    apply SepI... exists a...
  }
  apply countable_iff_mapped_onto_by_ω in Hcnt as [g Hg]...
  assert (Hgm: ∀m ∈ ω, g[m] ∈ 𝒜'). {
    intros m Hm. eapply ap_ran... apply surjection_is_func...
  }
  set (Func ω 𝒫 (ω ⟶ ⋃ 𝒜') (λ m,
    {f ∊ ω ⟶ ⋃ 𝒜' | λ f, f: ω ⟹ g[m]}
  )) as h.
  assert (Hh: h: ω ⇒ 𝒫 (ω ⟶ ⋃ 𝒜')). {
    apply meta_maps_into. intros m Hm. apply PowerAx.
    intros x Hx. apply SepE in Hx as []...
  }
  assert (Hneh: ∀m ∈ ω, ⦿ h[m]). {
    intros m Hm. apply Hgm in Hm as Hgma.
    apply SepE in Hgma as [Hgma Hnegm]. apply HcntA in Hgma.
    apply countable_iff_mapped_onto_by_ω in Hgma as [f Hf]...
    exists f. unfold h. rewrite meta_func_ap... apply SepI...
    destruct Hf as [Hf [Hd Hr]].
    apply arrow_iff. split... split... intros x Hx.
    apply UnionAx. exists (g[m]). split.
    apply SepI... apply Hsub. apply Hgm...
    rewrite <- Hr. eapply ranI. apply func_correct...
  }
  apply AC2 in Hneh as [F HF]. apply SepE in HF as [_ HFi].
  assert (HFm: ∀m ∈ ω, F[m]: ω ⟹ g[m]). {
    intros m Hm. apply HFi in Hm as HFm. unfold h in HFm.
    rewrite meta_func_ap in HFm... apply SepE in HFm as []...
  }
  set (Func (ω × ω) ⋃ 𝒜' (λ p, F[π2 p][π1 p])) as f.
  assert (Hf: f: ω × ω ⟹ ⋃ 𝒜'). {
    apply meta_surjective.
    - intros p Hp.
      apply cprod_iff in Hp as [a [Ha [b [Hb Hp]]]].
      subst p. zfcrewrite. apply UnionAx.
      exists (g[b]). split. apply Hgm... apply (ap_ran ω)...
      apply surjection_is_func. apply HFm...
    - intros y Hy. apply UnionAx in Hy as [A [HA Hy]].
      destruct Hg as [Hfg [Hdg Hrg]]. rewrite <- Hrg in HA.
      apply ranE in HA as [b Hgb]. apply domI in Hgb as Hb.
      apply func_ap in Hgb... rewrite Hdg in Hb.
      pose proof (HFm b Hb) as [HfF [HdF HrF]].
      rewrite <- Hgb, <- HrF in Hy. apply ranE in Hy as [a HFb].
      apply domI in HFb as Ha. apply func_ap in HFb...
      exists <a, b>. split. apply CProdI... zfcrewrite.
  }
  destruct Hf as [Hff [Hdf Hrf]].
  destruct ω_eqnum_ω_cp_ω as [p [[Hfp _] [Hdp Hrp]]].
  exists (f ∘ p). split. apply compo_func... split.
  - rewrite compo_dom... apply ExtAx. split; intros Hx.
    + apply SepE in Hx as [Hx _]...
    + apply SepI... rewrite Hdf, <- Hrp.
      eapply ranI. apply func_correct...
  - apply ExtAx. intros y. split; intros Hy.
    + apply ranE in Hy as [w Hp].
      apply compoE in Hp as [x [_ Hp]].
      rewrite <- Hrf. eapply ranI...
    + rewrite <- Hrf in Hy. apply ranE in Hy as [x Hpf].
      apply domI in Hpf as Hx. rewrite Hdf, <- Hrp in Hx.
      apply ranE in Hx as [w Hpp]. eapply ranI. eapply compoI...
Qed.
