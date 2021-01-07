(** Coq coding by choukh, Oct 2020 **)

Require Import ZFC.EX6_1.
Require Import ZFC.lib.Dominate.
Require Import ZFC.lib.WosetMin.
Import WosetMin.SimpleVer.

(** Facts about finite / infinite subset of ω **)

(* 自然数集的非空有限子集有极大元 *)
Lemma finite_subset_of_ω_is_bounded : ∀ N, ⦿ N → N ⊆ ω →
  finite N → ∃ m, sub_maximum m N.
Proof with auto; try congruence.
  intros N Hne Hsub [n [Hn Hqn]].
  generalize dependent N.
  set {n ∊ ω | λ n, ∀ N, ⦿ N → N ⊆ ω → N ≈ n → ∃ m, sub_maximum m N} as M.
  ω_induction M Hn; intros N Hne Hsub Hcd. {
    apply eqnum_empty in Hcd. apply EmptyNI in Hne. exfalso...
  }
  clear M Hn n. destruct Hne as [k Hk].
  destruct (classic (sub_maximum k N)). exists k...
  apply not_and_or in H as []. exfalso...
  apply set_not_all_ex_not in H as [p [Hp Hkp]].
  apply Hsub in Hk as Hkw. apply Hsub in Hp as Hpw.
  apply lt_iff_not_sub in Hkp...
  apply split_one_element in Hk as HeqN. rewrite HeqN in Hcd.
  apply finite_set_remove_one_element in Hcd...
  specialize IH with (N - ⎨k⎬) as [q [Hq Hmax]]...
  { exists p. apply SepI... apply SingNI...
    intros Heq. apply (nat_irrefl k)...
  } {
    eapply sub_tran...
  }
  apply SepE in Hq as [Hq _]... apply Hsub in Hq as Hqw.
  destruct (classic (p ⊆ q)) as [Hpq|Hqp].
  - exists q. split... intros n Hn.
    destruct (classic (n = k)).
    + rewrite H. apply lt_iff_psub... apply Hpq...
    + apply Hmax. apply SepI... apply SingNI...
  - exists p. split... intros n Hn.
    apply lt_iff_not_sub in Hqp...
    destruct (classic (n = k)).
    + rewrite H. apply lt_iff_psub...
    + eapply sub_tran.
      * apply Hmax. apply SepI... apply SingNI...
      * apply lt_iff_psub...
Qed.

(* 自然数集的没有极大元的非空子集是无限集 *)
Corollary unbound_subset_of_ω_is_infinite : ∀ N, ⦿ N → N ⊆ ω →
  nat_archimedean N → infinite N.
Proof with eauto.
  intros N Hne Hsub Harc Hfin.
  eapply nat_archimedean_iff_no_maximum...
  apply finite_subset_of_ω_is_bounded...
Qed.

(* 自然数集的有极大元的子集是非空有限集 *)
Lemma bounded_subset_of_ω_is_finite : ∀ N, N ⊆ ω →
  (∃ m, sub_maximum m N) → ⦿ N ∧ finite N.
Proof with nauto.
  intros N Hsub [n [Hn Hmax]]. split. exists n...
  apply Hsub in Hn as Hnw. generalize dependent N.
  set {n ∊ ω | λ n, ∀ N, N ⊆ ω → n ∈ N → (∀ k ∈ N, k ⊆ n) → finite N} as M.
  ω_induction M Hnw; intros N Hsub Hn Hmax.
  - exists 1. split... cut (N = ⎨∅⎬). {
      intros H. rewrite H. apply eqnum_single_one.
    }
    apply ExtAx. split; intros Hx.
    + apply Hmax in Hx. apply sub_empty in Hx. subst x...
    + apply SingE in Hx. subst x...
  - pose proof (nat_neq_suc m Hm) as Hnq.
    assert (Hstar: ∀k ∈ N, k ∉ ⎨m⁺⎬ → k ⊆ m). {
      intros k Hk Hk'. apply Hsub in Hk as Hkw. apply SingNE in Hk'.
      destruct (classic (k ⊆ m)) as [|Hmk]... exfalso.
      apply lt_iff_not_sub in Hmk; [|auto|apply Hsub]...
      apply lt_iff_suc_leq in Hmk...
      apply leq_iff_sub in Hmk; [|apply ω_inductive|]...
      apply Hk'. apply sub_antisym... apply Hmax...
    }
    destruct (classic (m ∈ N)) as [HmN|HmN].
    + replace N with (N - ⎨m⁺⎬ ∪ ⎨m⁺⎬).
      apply bunion_finite... apply IH.
      * eapply sub_tran...
      * apply SepI... apply SingNI...
      * intros k Hk. apply SepE in Hk as [Hk Hk']. apply Hstar...
      * apply remove_one_member_then_return...
    + replace N with (N ∪ ⎨m⎬ - ⎨m⁺⎬ - ⎨m⎬ ∪ ⎨m⁺⎬).
      apply bunion_finite... apply comp_finite. apply IH.
      * eapply sub_tran... eapply sub_tran...
        intros x Hx. apply BUnionE in Hx as [].
        apply Hsub... apply SingE in H. subst...
      * apply SepI. apply BUnionI2... apply SingNI...
      * intros k Hk. apply SepE in Hk as [Hk Hk'].
        apply BUnionE in Hk as [Hk|Hk]. apply Hstar...
        apply SingE in Hk; subst...
      * rewrite union_comp.
        replace (⎨m⎬ - ⎨m⁺⎬) with ⎨m⎬. {
          rewrite add_one_member_then_remove.
          - rewrite remove_one_member_then_return...
          - intros H. apply SepE1 in H...
        }
        apply ExtAx. split; intros Hx.
        apply SepI... apply SingE in Hx; subst. apply SingNI...
        apply SepE1 in Hx...
Qed.

(* 自然数集的无限子集没有极大元 *)
Corollary infinite_subset_of_ω_is_unbound : ∀ N, N ⊆ ω →
  infinite N → (⦿ N ∧ nat_archimedean N).
Proof with auto.
  intros N Hsub Hinf.
  apply infinite_set_nonempty in Hinf as Hne. split...
  apply nat_archimedean_iff_no_maximum...
  intros Hmax. apply Hinf.
  apply bounded_subset_of_ω_is_finite...
Qed.

(* 自然数集的子集是非空有限集当且仅当其有极大元 *)
Theorem subset_of_ω_is_finite_iff_bounded : ∀ N, N ⊆ ω →
  (⦿ N ∧ finite N) ↔ ∃ m, sub_maximum m N.
Proof with auto.
  intros N Hsub. split.
  - intros [Hne Hfin].
    apply finite_subset_of_ω_is_bounded...
  - apply bounded_subset_of_ω_is_finite...
Qed.

(* 自然数集的子集是无限集当且仅当其非空且没有极大元 *)
Theorem subset_of_ω_is_infinite_iff_unbound : ∀ N, N ⊆ ω →
  infinite N ↔ (⦿ N ∧ nat_archimedean N).
Proof with auto.
  intros N Hsub. split.
  - apply infinite_subset_of_ω_is_unbound...
  - intros []. apply unbound_subset_of_ω_is_infinite...
Qed.

(** Facts about sets dominated by ω **)

(* ω的任意无限子集与ω等势 *)
Theorem infinite_subset_of_ω_eqnum_ω : ∀ N,
  N ⊆ ω → infinite N → N ≈ ω.
Proof with neauto; try congruence.
  intros N Hsub Hinf.
  apply Schröeder_Bernstein. apply dominate_sub...
  apply infinite_subset_of_ω_is_unbound in Hinf as [Hne Harc]...
  destruct (ω_well_ordered N) as [n0 [Hn0 Hle]]...
  apply Hsub in Hn0 as Hn0w.
  assert (Hsubn: ∀n ∈ ω, {x ∊ N | λ x, n ∈ x} ⊆ N). {
    intros n Hn x Hx. apply SepE1 in Hx...
  }
  set (Func N N (Next N Lt)) as F.
  assert (HF: F: N ⇔ N). {
    apply meta_injective.
    - intros n Hn. apply Hsub in Hn as Hnw. apply (Hsubn n Hnw).
      pose proof (Harc n Hnw) as [m [Hm Hnm]].
      apply ω_next... exists m. split...
    - intros n1 H1 n2 H2.
      apply ω_next_injective; auto; apply Harc; apply Hsub...
  }
  assert (Hn0': n0 ∈ N - ran F). {
    destruct HF as [[Hf _] [Hd Hr]].
    apply SepI... intros H.
    apply ranE in H as [x Hp]. apply domI in Hp as Hx.
    rewrite Hd in Hx. apply Hsub in Hx as Hxw.
    apply func_ap in Hp... unfold F in Hp.
    rewrite meta_func_ap in Hp; [|split|]...
    pose proof (Hle x Hx) as Hn0x. apply leq_iff_sub in Hn0x...
    apply ω_next in Hx as [Hx _]... { apply Harc... }
    rewrite Hp in Hx. apply SepE in Hx as [_ Hx].
    apply Hn0x in Hx. apply (nat_irrefl x)...
  }
  pose proof (injective_recursion _ _ _ HF Hn0') as [f [Hf _]].
  exists f...
Qed.

(* 被ω支配的无限集与ω等势 *)
Corollary infinite_set_dominated_by_ω_eqnum_ω : ∀ A,
  A ≼ ω → infinite A → A ≈ ω.
Proof with auto.
  intros A [f [Hf [Hd Hr]]] Hinf.
  assert (A ≈ ran f). { exists f. split... }
  rewrite H. apply infinite_subset_of_ω_eqnum_ω...
  intros Hfin. apply Hinf.
  apply (dominated_by_finite_is_finite _ (ran f))...
  exists f. split...
Qed.

(* 集合被ω支配如果它被ω满射 *)
Lemma dominated_by_ω_if_mapped_onto_by_ω :
  ∀ B F, F: ω ⟹ B → B ≼ ω.
Proof with auto; try congruence.
  intros B f [Hf [Hd Hr]].
  set (λ b, {n ∊ ω | λ n, f[n] = b}) as 𝒩.
  set (Func B ω (λ x, (Min Lt)[𝒩 x])) as g.
  exists g. apply meta_injective.
  + intros x Hx. eapply ap_ran.
    apply ω_min_maps_into. apply SepI.
    * apply PowerAx. intros n Hn. apply SepE1 in Hn...
    * rewrite <- Hr in Hx. apply ranE in Hx as [n Hp].
      apply domI in Hp as Hn. apply func_ap in Hp...
      apply SingNI. apply EmptyNI. exists n. apply SepI...
  + intros b1 Hb1 b2 Hb2 Heq.
    assert (Hsub: ∀ b, 𝒩 b ⊆ ω). {
      intros b0 x Hx. apply SepE1 in Hx...
    }
    specialize (ω_min (𝒩 b1)) as [H1 _]... {
      rewrite <- Hr in Hb1. apply ranE in Hb1 as [n1 H1].
      apply domI in H1 as Hn1. apply func_ap in H1...
      exists n1. apply SepI...
    }
    specialize (ω_min (𝒩 b2)) as [H2 _]... {
      rewrite <- Hr in Hb2. apply ranE in Hb2 as [n2 H2].
      apply domI in H2 as Hn2. apply func_ap in H2...
      exists n2. apply SepI...
    }
    apply SepE in H1 as [_ H1].
    apply SepE in H2 as [_ H2]. congruence.
Qed.

(* 非空集合被ω支配蕴含它被ω满射 *)
Lemma dominated_by_ω_impl_mapped_onto_by_ω :
  ∀ B, ⦿ B → B ≼ ω → ∃ F, F: ω ⟹ B.
Proof with auto; try congruence.
  intros B [b Hb] Hdm.
  destruct (classic (finite B)).
  - destruct H as [n [Hn [f Hf]]].
    set (Func ω B (λ x, match (ixm (x ∈ n)) with
      | inl _ => f⁻¹[x]
      | inr _ => b
    end)) as g.
    exists g. apply meta_surjective.
    + intros x Hx. destruct (ixm (x ∈ n))... apply (ap_ran n)...
      apply bijection_is_func. apply inv_bijection...
    + intros y Hy. destruct Hf as [[Hf Hs] [Hd Hr]].
      rewrite <- Hd in Hy. apply domE in Hy as [x Hp].
      apply ranI in Hp as Hx. rewrite Hr in Hx.
      exists x. split. apply (ω_trans _ n)...
      destruct (ixm (x ∈ n))... apply func_ap.
      apply inv_func_iff_sr... rewrite <- inv_op...
  - apply infinite_set_dominated_by_ω_eqnum_ω in H as [f Hf]...
    exists (f⁻¹). apply bijection_is_surjection. apply inv_bijection...
Qed.

(* 非空集合被ω支配当且仅当它被ω满射 *)
Fact dominated_by_ω_iff_mapped_onto_by_ω :
  ∀ B, ⦿ B → (∃ F, F: ω ⟹ B) ↔ B ≼ ω.
Proof with eauto.
  intros B Hne. split.
  - intros [f Hf]. eapply dominated_by_ω_if_mapped_onto_by_ω...
  - apply dominated_by_ω_impl_mapped_onto_by_ω...
Qed.
