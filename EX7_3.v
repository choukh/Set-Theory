(** Solutions to "Elements of Set Theory" Chapter 7 Part 3 **)
(** Coq coding by choukh, Dec 2020 **)

Require ZFC.lib.Real.
Require ZFC.lib.ScottsTrick.
Require Import ZFC.EST7_6.

(* ex7_26 see EST7_6 Fact ord_grounded rank_of_ord *)

(** ex7_27 戴德金实数集的秩 **)
Section RankOfReal.
Import Real.
Hint Resolve rank_is_ord : core.
Hint Resolve ord_suc_is_ord : core.

(* 整数集是良基集 *)
Lemma int_grounded : grounded ℤ.
Proof with eauto.
  apply grounded_intro. intros a Ha.
  apply ReplAx in Ha as [p [_ Ha]]. subst a.
  apply grounded_intro. intros q Hq.
  apply SepE2 in Hq. apply SepE1 in Hq.
  apply CProdE2 in Hq as [_ Hq]. clear p.
  apply CProdE1 in Hq as [m [Hm [n [Hn Hq]]]]. subst q.
  apply grounded_intro. intros p Hp.
  apply PairE in Hp as []; subst p.
  - apply grounded_intro. intros x Hx.
    apply SingE in Hx; subst.
    eapply member_grounded... apply ord_grounded...
  - apply grounded_intro. intros x Hx.
    apply PairE in Hx as []; subst;
    eapply member_grounded; eauto; apply ord_grounded...
Qed.
Hint Resolve int_grounded : core.

(* 有理数集是良基集 *)
Lemma rat_grounded : grounded ℚ.
Proof with eauto.
  apply grounded_intro. intros r Hr.
  apply ReplAx in Hr as [p [_ Hr]]. subst r.
  apply grounded_intro. intros q Hq.
  apply SepE2 in Hq. apply SepE1 in Hq.
  apply CProdE2 in Hq as [_ Hq]. clear p.
  apply CProdE1 in Hq as [a [Ha [b [Hb Hq]]]]. subst q.
  apply grounded_intro. intros p Hp.
  apply PairE in Hp as []; subst p.
  - apply grounded_intro. intros x Hx.
    apply SingE in Hx; subst.
    eapply member_grounded...
  - apply grounded_intro. intros x Hx.
    apply PairE in Hx as []; subst;
    eapply member_grounded... apply SepE1 in Hb...
Qed.
Hint Resolve rat_grounded : core.

(* 戴德金实数集是良基集 *)
Lemma real_grounded : grounded ℝ.
Proof with eauto.
  apply grounded_intro. intros x Hx.
  apply SepE1 in Hx. apply PowerAx in Hx.
  apply grounded_intro. intros q Hq. apply Hx in Hq.
  eapply member_grounded...
Qed.
Hint Resolve real_grounded : core.

(* 整数的秩 *)
Lemma rank_of_int : ∀a ∈ ℤ, rank a = ω.
Proof with neauto.
  intros a Ha.
  rewrite rank_recurrence; [|apply (member_grounded ℤ)]...
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply ExtAx. split; intros Hx.
  - apply FUnionE in Hx as [a [Ha Hx]].
    apply SepE2 in Ha. apply SepE1 in Ha.
    apply CProdE2 in Ha as [_ Ha].
    apply CProdE1 in Ha as [p [Hp [q [Hq Ha]]]].
    subst a. rewrite rank_of_op in Hx.
    eapply ord_trans... repeat apply ω_inductive.
    rewrite rank_of_ord, rank_of_ord.
    + destruct (nat_comparability p Hp q Hq)...
      * rewrite bunion_of_nats_eq_l...
      * rewrite bunion_of_nats_eq_r...
    + eapply ord_is_ords...
    + eapply ord_is_ords...
    + apply (member_grounded ω)... apply ord_grounded...
    + apply (member_grounded ω)... apply ord_grounded...
  - eapply FUnionI. {
      apply (eqvcI _ _ <(m + x)%n, (x + n)%n>).
      apply planeEquivI... apply add_ran... apply add_ran...
      unfold IntEq. rewrite <- add_assoc...
    }
    assert (H1: (m + x)%n ∈ ω). apply add_ran...
    assert (H2: (x + n)%n ∈ ω). apply add_ran...
    rewrite rank_of_op, rank_of_ord, rank_of_ord.
    + destruct (nat_comparability (m + x)%n H1 (x + n)%n H2)...
      * rewrite bunion_of_nats_eq_l...
        apply BUnionI1. apply BUnionI1.
        destruct (leq_add_enlarge x Hx n Hn).
        apply BUnionI1... apply BUnionI2. rewrite H0 at 1...
      * rewrite bunion_of_nats_eq_r...
        apply BUnionI1. apply BUnionI1. rewrite add_comm...
        destruct (leq_add_enlarge x Hx m Hm).
        apply BUnionI1... apply BUnionI2. rewrite H0 at 1...
    + eapply ord_is_ords...
    + eapply ord_is_ords...
    + apply (member_grounded ω)... apply ord_grounded...
    + apply (member_grounded ω)... apply ord_grounded...
Qed.

(* 整数集的秩 *)
Lemma rank_of_Int : rank ℤ = ω⁺.
Proof with nauto.
  rewrite rank_recurrence...
  apply ExtAx. split; intros Hx.
  - apply FUnionE in Hx as [a [Ha Hx]].
    apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
    rewrite rank_of_int in Hx... apply pQuotI...
  - apply (FUnionI _ _ ([<0, 0>]~%pz))...
    rewrite rank_of_int...
Qed.

(* 有理数的秩 *)
Lemma rank_of_rat : ∀r ∈ ℚ, rank r = ω⁺⁺⁺.
Proof with neauto.
  intros r Hr.
  rewrite rank_recurrence; [|apply (member_grounded ℚ)]...
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  apply ExtAx. split; intros Hx.
  - apply FUnionE in Hx as [r [Hr Hx]].
    apply SepE2 in Hr. apply SepE1 in Hr.
    apply CProdE2 in Hr as [_ Hr].
    apply CProdE1 in Hr as [c [Hc [d [Hd Hr]]]].
    subst r. apply SepE1 in Hd.
    rewrite rank_of_op, rank_of_int, rank_of_int,
      bunion_of_ords_eq_l in Hx...
    apply (member_grounded ℤ)... apply (member_grounded ℤ)...
  - eapply FUnionI.
    + apply (eqvcI _ _ <a, b>).
      apply planeEquivI... reflexivity.
    + apply SepE1 in Hb.
      rewrite rank_of_op, rank_of_int, rank_of_int,
        bunion_of_ords_eq_l...
      apply (member_grounded ℤ)... apply (member_grounded ℤ)...
Qed.

(* 有理数集的秩 *)
Lemma rank_of_rats : rank ℚ = ω⁺⁺⁺⁺.
Proof with nauto.
  rewrite rank_recurrence...
  apply ExtAx. split; intros Hx.
  - apply FUnionE in Hx as [r [Hr Hx]].
    apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
    rewrite rank_of_rat in Hx... apply pQuotI...
  - apply (FUnionI _ _ ([<Int 0, Int 1>]~%pq))...
    rewrite rank_of_rat...
Qed.

(* 戴德金实数的秩 *)
Lemma rank_of_real : ∀x ∈ ℝ, rank x = ω⁺⁺⁺⁺.
Proof with eauto.
  intros x Hx.
  rewrite <- (subset_same_rank ℚ)... apply rank_of_rats.
  intros r Hr s Hs. rewrite rank_of_rat, rank_of_rat...
  apply SepE1 in Hx... apply realE0 in Hx as [q [_ Hq]].
  apply EmptyNI. exists q...
Qed.

(* ex7_27 戴德金实数集的秩 *)
Fact rank_of_Real : rank ℝ = ω⁺⁺⁺⁺⁺.
Proof with nauto.
  rewrite <- (rank_of_real (Real 0))...
  apply member_rank_up...
  intros x Hx y Hy. rewrite rank_of_real, rank_of_real...
Qed.

End RankOfReal.

(* 假设正则公理，那么第α层宇宙就是由那些秩小于α的集合所组成的集合 *)
Example ex7_28 : Regularity → ∀ α β, is_ord α → is_ord β →
  α ⋸ β → V α = {X ∊ V β | λ X, rank X ∈ α}.
Proof with eauto.
  intros Reg α β Hoα Hoβ Hle.
  destruct Hle; apply ExtAx; split; intros Hx.
  - apply SepI... eapply V_sub... rewrite <- rank_of_V...
    apply rank_of_member... apply V_grounded...
  - apply SepE2 in Hx. rewrite V_hierarchy...
    eapply FUnionI... apply PowerAx. apply grounded_in_rank.
    apply all_grounded_iff_regularity...
  - subst. apply SepI... rewrite <- rank_of_V...
    apply rank_of_member... apply V_grounded...
  - subst. apply SepE1 in Hx...
Qed.

(* ex7_29 see EST7_6 Fact ord_grounded rank_of_ord *)
(* ex7_30 see EST7_6 Lemma rank_of_pair rank_of_power rank_of_union *)

(* ex_7_31 不依赖选择公理而依赖正则公理的基数定义 *)
Module Kard.
Import ScottsTrick.ForSet.

Definition kard := λ A, scott equinumerous A.

Fact kard_nonempty : ∀ A, kard A ≠ ∅.
Proof.
  intros. apply scott_nonempty. apply eqnum_equiv.
Qed.

Lemma kard_intro : ∀ A B, B ≈ A →
  (∀ C, B ≈ C → rank B ⋸ rank C) → B ∈ kard A.
Proof.
  intros A B. apply scott_intro. apply eqnum_equiv.
Qed.

Lemma kard_elim : ∀ A, ∀B ∈ kard A, B ≈ A ∧
  ∀ C, B ≈ C → rank B ⋸ rank C.
Proof.
  intros A B HB. apply scott_elim. apply HB. apply eqnum_equiv.
Qed.

Fact kard_spec : ∀ A B,
  (B ≈ A ∧ ∀ C, B ≈ C → rank B ⋸ rank C) ↔ B ∈ kard A.
Proof.
  intros A B. apply scott_spec. apply eqnum_equiv.
Qed.

Theorem kard_correct : ∀ A B, kard A = kard B ↔ A ≈ B.
Proof.
  intros A B. apply scott_correct. apply eqnum_equiv.
Qed.

End Kard.

(* ex_7_32 同构类型 *)
Module IsomorphismType.
Import ScottsTrick.ForAnyType.
Import OrderedStruct.

Definition it := λ S, scott (λ S, <A S, R S>) isomorphic S.

Fact it_nonempty : ∀ S, it S ≠ ∅.
Proof.
  intros. apply scott_nonempty. apply iso_equiv.
Qed.

Theorem it_correct : ∀ S T, it S = it T ↔ S ≅ T.
Proof.
  intros. apply scott_correct.
  intros U V Heq. apply op_iff in Heq as [].
  apply eq_intro; auto. apply iso_equiv.
Qed.

End IsomorphismType.

Example ex7_33 : ∀ D B, grounded D → trans D →
  (∀a ∈ D, a ⊆ B → a ∈ B) → D ⊆ B.
Proof with eauto.
  intros * Hgnd Htr HB.
  destruct (classic (D ⊆ B)) as [|Hnsub]... exfalso.
  assert (Hne: ⦿ (D - B)). {
    apply EmptyNE. intros H0.
    apply sub_iff_no_comp in H0...
  }
  set {rank | x ∊ D - B} as Ω.
  destruct (ords_woset Ω) as [_ Hmin]. {
    intros x Hx. apply ReplAx in Hx as [d [Hd Heq]].
    subst x. apply rank_is_ord...
    eapply member_grounded... apply SepE1 in Hd...
  }
  pose proof (Hmin Ω) as [μ [Hμ Hle]]... {
    destruct Hne as [d Hd].
    exists (rank d). eapply ReplI...
  }
  apply ReplAx in Hμ as [m [Hm Heqμ]]. subst μ.
  apply SepE in Hm as [Hm Hm']. apply Hm'.
  apply HB... intros x Hxm.
  destruct (classic (x ∈ B)) as [|Hx']... exfalso.
  assert (HxD: x ∈ D)...
  assert (Hx: x ∈ D - B). apply SepI...
  assert (rank x ∈ Ω). eapply ReplI...
  assert (Hgm: grounded m). eapply member_grounded...
  assert (Hgx: grounded x). eapply member_grounded...
  apply rank_of_member in Hxm...
  apply Hle in H as [].
  - apply binRelE3 in H. eapply ord_not_lt_gt; revgoals...
  - rewrite H in Hxm. eapply ord_irrefl; revgoals...
Qed.

Section RegularWorld.
Import RegularityConsequences.

Example ex7_34 : ∀ x y u v, {x, {x, y}} = {u, {u, v}} →
  x = u ∧ y = v.
Proof with eauto; try congruence.
  intros.
  assert (Hx: x ∈ {u, {u, v}}). {
    rewrite <- H. apply PairI1.
  }
  assert (Hp: {x, y} ∈ {u, {u, v}}). {
    rewrite <- H. apply PairI2.
  }
  apply PairE in Hx as [].
  - subst u. split... apply PairE in Hp as [].
    + exfalso. eapply pair_regularity...
    + apply pair_iff in H0 as [[]|[]]...
  - apply PairE in Hp as [].
    + exfalso. apply (no_descending_chain_2 x {x, y}).
      apply PairI1. rewrite H1, H0. apply PairI1.
    + apply pair_iff in H1 as [[]|[]]...
      subst. exfalso. rewrite pair_ordering_agnostic in H1.
      eapply pair_regularity...
Qed.

(* ex7_35 对于任意集合，后继都是单射 *)
Theorem suc_injective : ∀ a b, a⁺ = b⁺ → a = b.
Proof with auto.
  intros.
  assert (Ha: a ∈ b⁺). rewrite <- H. apply suc_has_n.
  assert (Hb: b ∈ a⁺). rewrite H. apply suc_has_n.
  apply BUnionE in Ha as [].
  - apply BUnionE in Hb as [].
    + exfalso. apply (no_descending_chain_2 a b)...
    + apply SingE in H1...
  - apply SingE in H0...
Qed.

(* ex7_36 see Fact transitive_closure_persist_rank *)

(* ex7_37 连通传递集等价于序数 *)
Theorem connected_trans_iff_ord : ∀ α,
  is_ord α ↔ connected (MemberRel α) α ∧ trans α.
Proof with eauto.
  split. {
    intros Ho. split.
    - apply lo_connected. apply ord_woset...
    - apply ord_trans...
  }
  intros [Hcnt Htr].
  apply transitive_set_well_ordered_by_epsilon_is_ord...
  split. apply loset_iff_connected_poset. repeat split...
  - apply memberRel_is_binRel.
  - eapply binRel_is_rel. apply memberRel_is_binRel.
  - intros x y z Hxy Hyz.
    apply binRelE2 in Hxy as [Hx [Hy Hxy]].
    apply binRelE2 in Hyz as [_  [Hz Hyz]].
    apply binRelI...
    destruct (classic (x = z)). {
      subst. exfalso. eapply no_descending_chain_2...
    }
    apply Hcnt in H as []; auto; apply binRelE3 in H...
    exfalso. eapply no_descending_chain_3...
  - intros x H. apply binRelE3 in H.
    exfalso. eapply no_descending_chain_1...
  - intros B Hne Hsub.
    apply EmptyNI in Hne.
    pose proof (ex_epsilon_minimal B Hne) as [m [Hm Hmin]].
    exists m. split... intros x Hx.
    apply Hsub in Hx as Hxα.
    apply Hsub in Hm as Hmα.
    apply Hmin in Hx as H. destruct H; [|right]...
    destruct (classic (x = m)) as [|Hnq]; [right|left]...
    apply Hcnt in Hnq as []... exfalso.
    apply H. eapply binRelE3...
Qed.

(* ex7_38 see EST7_4 Theorem ord_is_suc_or_limit *)

(* ex7_39 传递集的传递集等价于序数 *)
Theorem trans_of_trans_iff_ord : ∀ α,
  is_ord α ↔ trans α ∧ ∀ξ ∈ α, trans ξ.
Proof with eauto.
  split. {
    intros Ho. repeat split.
    - apply ord_trans...
    - intros ξ Hξ. apply ord_trans. eapply ord_is_ords...
  }
  intros [Htr1 Htr2].
  apply connected_trans_iff_ord. split...
  intros a Ha b Hb Hnqab.
  destruct (classic (a ∈ b)) as [|Hab]; [left|right]; apply binRelI...
  destruct (classic (b ∈ a)) as [|Hba]... exfalso.
  set {x ∊ α | λ x, ∃y ∈ α, x ≠ y ∧ x ∉ y ∧ y ∉ x} as A.
  pose proof (ex_epsilon_minimal A) as [m [Hm HminA]]. {
    apply EmptyNI. exists a.
    apply SepI... exists b. split...
  }
  apply SepE in Hm as H.
  destruct H as [Hmα [y [Hy [Hnqmy [Hmy Hym]]]]].
  set {x ∊ α | λ x, x ≠ m ∧ x ∉ m ∧ m ∉ x} as B.
  pose proof (ex_epsilon_minimal B) as [n [Hn HminB]]. {
    apply EmptyNI. exists y. apply SepI...
  }
  apply SepE in Hn as H.
  destruct H as [Hnα [Hnqnm [Hnm Hmn]]].
  apply Hnqnm. apply ExtAx. split; intros Hx.
  - destruct (classic (x ∈ m)) as [|Hxm]... exfalso.
    assert (HxB: x ∈ B). {
      apply SepI. eapply Htr1...
      repeat split... intros H. subst...
      intros Hmx. apply Hmn. eapply Htr2...
    }
    apply HminB in HxB as H. destruct H.
    apply H... subst. eapply no_descending_chain_1...
  - destruct (classic (x ∈ n)) as [|Hxn]... exfalso.
    assert (HxA: x ∈ A). {
      apply SepI. eapply Htr1... exists n. split...
      repeat split... intros H. subst...
      intros Hnx. apply Hnm. eapply Htr2...
    }
    apply HminA in HxA as H. destruct H.
    apply H... subst. eapply no_descending_chain_1...
Qed.

End RegularWorld.

Section TC.
Import TransitiveClosureDef.

Local Lemma fn_grounded :
  ∀ A, grounded A → ∀n ∈ ω, grounded (F A)[n].
Proof with auto.
  intros A Hgnd n Hn.
  set {n ∊ ω | λ n, grounded (F A)[n]} as N.
  ω_induction N Hn. rewrite f_0...
  rewrite f_n... apply union_grounded.
  apply pair_grounded... apply union_grounded...
Qed.
Hint Resolve fn_grounded : core.

Local Lemma rank_of_fn :
  ∀ A, grounded A → ∀n ∈ ω, rank (F A)[n] = rank A.
Proof with eauto; try congruence.
  intros A Hgnd n Hn.
  set {n ∊ ω | λ n, rank (F A)[n] = rank A} as N.
  ω_induction N Hn. rewrite f_0...
  assert (H1: grounded (F A)[m]). apply fn_grounded...
  assert (H2: grounded ⋃(F A)[m]). apply union_grounded...
  assert (H3: grounded (A ∪ ⋃(F A)[m])). {
    apply union_grounded... apply pair_grounded...
  }
  apply ExtAx. split; intros Hx.
  - rewrite f_n, rank_recurrence in Hx...
    apply FUnionE in Hx as [y [Hy Hx]].
    apply BUnionE in Hy as [].
    + rewrite rank_recurrence... eapply FUnionI...
    + apply rank_of_member in H...
      pose proof (rank_of_union (F A)[m] H1) as Hsub.
      apply ord_leq_iff_sub in Hsub...
      apply Hsub in H. rewrite IH in H.
      apply BUnionE in Hx as [].
      eapply ord_trans... apply SingE in H0...
  - rewrite rank_recurrence in Hx...
    apply FUnionE in Hx as [y [Hy Hx]].
    rewrite f_n, rank_recurrence...
    eapply FUnionI... apply BUnionI1...
Qed.

Lemma transitive_closure_grounded :
  ∀ A, grounded A → grounded (𝗧𝗖 A).
Proof with eauto.
  intros A Hgnd. apply grounded_intro.
  intros x Hx. apply UnionAx in Hx as [y [Hy Hx]].
  pose proof (f_spec A) as [Hf [Hd Hr]].
  apply ranE in Hy as [n Hp].
  apply domI in Hp as Hn. rewrite Hd in Hn.
  apply func_ap in Hp... subst y.
  eapply member_grounded; revgoals... apply fn_grounded...
Qed.
Hint Resolve transitive_closure_grounded : core.

(* ex7_36 任意集合与其传递闭包等秩 *)
Fact transitive_closure_persist_rank :
  ∀ S, grounded S → rank (𝗧𝗖 S) = rank S.
Proof with eauto; try congruence.
  intros S Hgnd.
  apply ExtAx. split; intros Hx.
  - rewrite rank_recurrence in Hx...
    apply FUnionE in Hx as [s [Hs Hx]].
    apply UnionAx in Hs as [y [Hy Hs]].
    pose proof (f_spec S) as [Hf [Hd Hr]].
    apply ranE in Hy as [n Hp].
    apply domI in Hp as Hn. rewrite Hd in Hn.
    apply func_ap in Hp... subst y.
    apply rank_of_member in Hs; [|apply fn_grounded]...
    rewrite rank_of_fn in Hs...
    apply BUnionE in Hx as [].
    eapply ord_trans; revgoals... apply SingE in H...
  - rewrite rank_recurrence in *...
    apply FUnionE in Hx as [s [Hs Hx]].
    eapply FUnionI... apply tc_contains...
Qed.

End TC.
