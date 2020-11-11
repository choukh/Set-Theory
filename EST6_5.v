(** Based on "Elements of Set Theory" Chapter 6 Part 5 **)
(** Coq coding by choukh, Oct 2020 **)

Require Export ZFC.EX6_2.
Require Import ZFC.lib.NaturalSubsetMin.

(*** EST第六章5：可数集，可数多个可数集的并是可数集 ***)

(* 可数集 *)
Definition countable : set → Prop := λ A, A ≼ ω.
(* 不可数集 *)
Definition uncountable : set → Prop := λ A, ¬countable A.

(* 集合是可数集当且仅当它是有限集或可数无限集 *)
Lemma countable_iff :
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

(* 集合是不可数集当且仅当它是无限集且不与ω等势 *)
Lemma uncountable_iff :
  ∀ A, uncountable A ↔ infinite A ∧ A ≉ ω.
Proof.
  intros. unfold uncountable, infinite.
  rewrite countable_iff. tauto.
Qed.

(* 集合是可数集当且仅当其基数小于等于阿列夫零 *)
Lemma countable_iff_cardLeq_aleph0 : ∀ A, countable A ↔ |A| ≤ ℵ₀.
Proof. split; apply cardLeq_iff; auto. Qed.

(* 空集是可数集 *)
Lemma empty_countable : countable ∅.
Proof.
  apply countable_iff.
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

(* 集合是可数集如果它被ω满射 *)
Lemma countable_if_mapped_onto_by_ω :
  ∀ A F, F: ω ⟹ A → countable A.
Proof. exact dominated_by_ω_if_mapped_onto_by_ω. Qed.

(* 非空集合是可数集蕴含它被ω满射 *)
Lemma countable_impl_mapped_onto_by_ω :
  ∀ A, ⦿ A → countable A → ∃ F, F: ω ⟹ A.
Proof. exact dominated_by_ω_impl_mapped_onto_by_ω. Qed.

(* 非空集合是可数集当且仅当它被ω满射 *)
Fact countable_iff_mapped_onto_by_ω :
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
  apply countable_impl_mapped_onto_by_ω in Hcnt as [g Hg]...
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
  apply AC2 in Hneh as [F HF]. apply SepE in HF as [_ HF].
  assert (HFm: ∀m ∈ ω, F[m]: ω ⟹ g[m]). {
    intros m Hm. apply HF in Hm as HFm. unfold h in HFm.
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
  destruct ω_eqnum_ω_cp_ω as [i Hi].
  apply (countable_if_mapped_onto_by_ω _ (f ∘ i)).
  eapply compo_surjection... apply bijection_is_surjection...
Qed.

(* ==可以不用选择公理== (用算术基本定理直接建立双射) *)
Fact union_of_all_n_arrow_ω_countable :
  countable ⋃{λ n, n ⟶ ω | n ∊ ω}.
Proof with neauto.
  apply countable_union_of_coutable_set.
  - apply ac2.
  - apply countable_iff. right.
    symmetry. apply eqnum_repl.
    intros n Hn m Hm Heq.
    set (Func n ω (λ x, x)) as f.
    assert (Hf: f ∈ n ⟶ ω). {
      apply SepI. apply PowerAx.
      intros p Hp. apply SepE in Hp as []...
      apply meta_maps_into. intros x Hx. eapply ω_trans...
    }
    apply arrow_iff in Hf as Hfn. destruct Hfn as [_ [Hdn _]].
    rewrite Heq in Hf. apply arrow_iff in Hf as [_ [Hdm _]].
    congruence.
  - intros A HA. apply ReplAx in HA as [n [Hn Hqn]]. subst A.
    apply countable_iff.
    destruct (classic (n = 0)).
    + left. subst n. rewrite arrow_from_empty. apply nat_finite...
    + right. eapply eqnum_tran.
      * apply cardExp_well_defined. apply CardAx0. reflexivity.
      * apply CardAx1. rewrite <- cardExp_aleph0_n at 2... reflexivity.
Qed.

(* 自然数序列 *)
Definition Sq : set → set := λ A,
  {f ∊ 𝒫 (ω × A) | λ f, ∃n ∈ ω, f: n ⇒ A}.

Fact sq_ω_eqnum_ω : Sq ω ≈ ω.
Proof with neauto; try congruence.
  apply Schröeder_Bernstein.
  - eapply dominate_tran; [|apply union_of_all_n_arrow_ω_countable].
    apply dominate_sub. intros f Hf.
    apply SepE in Hf as [_ [n [Hn Hf]]].
    apply UnionAx. exists (n ⟶ ω). split.
    + apply ReplAx. exists n. split...
    + destruct Hf as [Hf [Hd Hr]].
      apply arrow_iff. split... split...
      intros x Hx. apply Hr. eapply ranI. apply func_correct...
  - set (Func ω (Sq ω) (λ x, Func 1 ω (λ _, x))) as f.
    exists f. apply meta_injective.
    + intros x Hx. apply SepI.
      * apply PowerAx. intros p Hp. apply SepE in Hp as [Hp _].
        apply cprod_iff in Hp as [a [Ha [b [Hb Hp]]]].
        subst p. apply CProdI... eapply ω_trans...
      * exists 1. split... apply meta_maps_into. intros _ _...
    + intros x1 Hx1 x2 Hx2 Heq.
      assert (<∅, x1> ∈ Func 1 ω (λ _, x1)). {
        apply SepI. apply CProdI... apply suc_has_0... zfcrewrite.
      }
      rewrite Heq in H. apply SepE in H as [_ H]. zfcrewrite.
Qed.

Fact sq_countable : ∀ A, countable A → countable (Sq A).
Proof with eauto; try congruence.
  intros A [g Hg].
  eapply dominate_tran; revgoals. {
    apply eqnum_dominate. rewrite <- sq_ω_eqnum_ω...
  }
  set (Func (Sq A) (Sq ω) (λ f,
    Func (dom f) ω (λ n, g[f[n]])
  )) as F.
  exists F. apply meta_injective.
  - intros f Hf. apply SepE in Hf as [_ [n [Hn Hf]]].
    assert (Hf' := Hf). destruct Hf' as [_ [Hdf _]].
    apply SepI.
    + apply PowerAx. intros p Hp. apply SepE in Hp as [Hp _].
      apply cprod_iff in Hp as [a [Ha [b [Hb Hp]]]].
      subst p. apply CProdI... eapply ω_trans...
    + exists n. split... rewrite Hdf.
      apply meta_maps_into. intros x Hx. eapply ap_ran.
      apply injection_is_func... eapply ap_ran...
  - intros f1 H1 f2 H2 Heq.
    apply SepE in H1 as [_ [n1 [Hn1 [Hf1 [Hdf1 Hrf1]]]]].
    apply SepE in H2 as [_ [n2 [Hn2 [Hf2 [Hdf2 Hrf2]]]]].
    assert (Hf1x: ∀x ∈ dom f1, f1[x] ∈ A). {
      intros x Hx. eapply ap_ran... split...
    }
    assert (Hf2x: ∀x ∈ dom f2, f2[x] ∈ A). {
      intros x Hx. eapply ap_ran... split...
    }
    assert (H1: ∀x ∈ dom f1, g[f1[x]] ∈ ω). {
      intros x Hx. eapply ap_ran.
      apply injection_is_func... apply Hf1x...
    }
    assert (H2: ∀x ∈ dom f2, g[f2[x]] ∈ ω). {
      intros x Hx. eapply ap_ran.
      apply injection_is_func... apply Hf2x...
    }
    apply func_ext_elim in Heq as [Heq1 Heq2]; [|apply func_is_func..].
    rewrite meta_dom, meta_dom in Heq1...
    rewrite meta_dom in Heq2...
    apply func_ext_intro...
    intros x Hx. apply Heq2 in Hx as Heq.
    rewrite meta_func_ap, meta_func_ap in Heq; revgoals...
    apply meta_maps_into... apply meta_maps_into...
    destruct Hg as [Hi [Hd Hr]].
    eapply injectiveE; eauto; rewrite Hd.
    apply Hf1x... apply Hf2x...
Qed.

(* “定理：可数多个可数集的并是可数集“的推广 *)
Theorem cardLeq_union : AC_I →
  ∀ 𝒜 𝜅, is_card 𝜅 → (∀A ∈ 𝒜, |A| ≤ 𝜅) → |⋃ 𝒜| ≤ |𝒜| ⋅ 𝜅.
Proof with auto; try congruence.
  intros AC1 * [K HK] Hle.
  set {A ∊ 𝒜 | λ A, ⦿ A} as 𝒜'.
  assert (Hle': |𝒜'| ≤ |𝒜|). {
    apply cardLeq_sub. intros x Hx. apply SepE in Hx as []...
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
  rewrite HK, Hequ in *. clear HK 𝜅 Hequ.
  eapply cardLeq_tran; revgoals.
  apply cardMul_preserve_leq. apply Hle'.
  apply cardLeq_iff.
  eapply dominate_rewrite_l. {
    apply cardMul_well_defined. apply CardAx0. apply CardAx0.
  }
  set (Func 𝒜' 𝒫 (K ⟶ ⋃ 𝒜') (λ A,
    {f ∊ K ⟶ ⋃ 𝒜' | λ f, f: K ⟹ A}
  )) as h.
  assert (Hh: h: 𝒜' ⇒ 𝒫 (K ⟶ ⋃ 𝒜')). {
    apply meta_maps_into. intros m Hm. apply PowerAx.
    intros x Hx. apply SepE in Hx as []...
  }
  assert (Hneh: ∀A ∈ 𝒜', ⦿ h[A]). {
    intros A HA. assert (HA' := HA).
    apply SepE in HA as [HA HneA].
    apply Hle in HA. apply cardLeq_iff in HA.
    apply dominated_impl_mapped_onto in HA as [f Hf]...
    exists f. unfold h. rewrite meta_func_ap... apply SepI...
    destruct Hf as [Hf [Hd Hr]].
    apply arrow_iff. split... split... intros x Hx.
    apply UnionAx. exists A. split...
    rewrite <- Hr. eapply ranI. apply func_correct...
  }
  pose proof (AC_I_to_II AC1) as AC2.
  apply AC2 in Hneh as [F HF]. apply SepE in HF as [_ HF].
  assert (HFA: ∀A ∈ 𝒜', F[A]: K ⟹ A). {
    intros A HA. apply HF in HA as HFA. unfold h in HFA.
    rewrite meta_func_ap in HFA... apply SepE in HFA as []...
  }
  set (Func (𝒜' × K) ⋃ 𝒜' (λ p, F[π1 p][π2 p])) as f.
  assert (Hf: f: 𝒜' × K ⟹ ⋃ 𝒜'). {
    apply meta_surjective.
    - intros p Hp.
      apply cprod_iff in Hp as [A [HA [k [Hk Hp]]]].
      subst p. zfcrewrite. apply UnionAx.
      exists A. split... apply (ap_ran K)...
      apply surjection_is_func. apply HFA...
    - intros a Ha. apply UnionAx in Ha as [A [HA Ha]].
      pose proof (HFA A HA) as [HfF [HdF HrF]].
      rewrite <- HrF in Ha. apply ranE in Ha as [k HFAk].
      apply domI in HFAk as Ha. apply func_ap in HFAk...
      exists <A, k>. split. apply CProdI... zfcrewrite.
  }
  eapply domain_of_surjection_dominate_range... apply Hf.
Qed.

Fact sq_dominated_by_ω_arrow : ∀ A, 2 ≤ |A| → Sq A ≼ ω ⟶ A.
Proof with neauto; try congruence.
  intros A Hle.
  eapply dominate_rewrite_l. {
    apply cardExp_well_defined; symmetry; apply CardAx0.
  }
  cut (|Sq A| ≤ |A| ^ ℵ₀). { apply cardLeq_iff. }
  rewrite <- cardMul_aleph0_expAleph0...
  apply cardLeq_iff.
  eapply dominate_rewrite_l. {
    apply cardMul_well_defined. apply CardAx0.
    eapply eqnum_tran; revgoals. apply CardAx0.
    apply cardExp_well_defined; apply CardAx0.
  }
  assert (Hne: ⦿ A). {
    apply EmptyNE. intros H. apply card_empty_iff in H.
    rewrite H in Hle. apply fin_cardLeq_iff_leq in Hle...
    apply leq_iff_sub in Hle... apply sub_empty in Hle.
    eapply (lt_irrefl 2)... rewrite Hle at 1.
    apply suc_has_0. apply ω_inductive...
  }
  destruct Hne as [a Ha].
  set (λ f, Func ω A (λ x,
    match (ixm (x ∈ dom f)) with
      | inl _ => f[x]
      | inr _ => a
    end
  )) as G.
  set (Func (Sq A) (ω ⟶ A) (λ f, G f)) as g.
  set (Func (Sq A) (ω × (ω ⟶ A)) (λ f, <dom f, g[f]>)) as F.
  assert (HGp: ∀f ∈ Sq A, G f ∈ 𝒫 (ω × A)). {
    intros f Hf. apply PowerAx. intros p Hp.
    apply SepE in Hp as []...
  }
  assert (HG: ∀f ∈ Sq A, G f : ω ⇒ A). {
    intros f Hf.
    apply SepE in Hf as [_ [n [Hn [Hf [Hd Hr]]]]].
    apply meta_maps_into.
    intros x Hx. destruct (ixm (x ∈ dom f))...
    eapply ap_ran... split...
  }
  assert (Hg: g: Sq A ⇒ (ω ⟶ A)). {
    apply meta_maps_into. intros f Hf.
    apply SepI. apply HGp... apply HG...
  }
  exists F. apply meta_injective.
  - intros f Hf. apply CProdI.
    apply SepE in Hf as [_ [n [Hn [_ [Hd _]]]]]...
    apply SepI; unfold g; rewrite meta_func_ap...
    apply HGp... apply HG...
  - intros f1 H1 f2 H2 Heq.
    apply op_iff in Heq as [Heqd Heqg].
    unfold g in Heqg.
    do 2 rewrite meta_func_ap in Heqg...
    assert (H1' := H1). assert (H2' := H2).
    apply SepE in H1' as [_ [n [Hn [Hf1 [Hd _]]]]].
    apply SepE in H2' as [_ [_ [_ [Hf2 _]]]].
    apply func_ext... split... intros x Hx.
    assert (Hxw: x ∈ ω). { eapply ω_trans... }
    assert (Heq: (G f1)[x] = (G f2)[x]) by congruence.
    unfold G in Heq.
    do 2 rewrite meta_func_ap in Heq; auto; [|apply HG..]...
    rewrite <- Heqd in Heq. destruct (ixm (x ∈ dom f1))...
Qed.
