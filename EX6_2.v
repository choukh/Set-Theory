(** Solutions to "Elements of Set Theory" Chapter 6 Part 2 **)
(** Coq coding by choukh, Sep 2020 **)

Require Export ZFC.EST6_4.

(* 所有集合的支配集不能构成一个集合 *)
Example ex6_15 : ¬∃ 𝒜, ∀ B, ∃A ∈ 𝒜, B ≼ A.
Proof with eauto.
  intros [𝒜 H].
  specialize H with (𝒫 ⋃𝒜) as [A [H1 H2]].
  apply union_dominate in H1.
  assert (𝒫 ⋃𝒜 ≼ ⋃𝒜) by (eapply dominate_tran; eauto).
  apply cardLeq_iff in H. rewrite card_of_power in H.
  destruct (cardLt_power (|⋃𝒜|)) as [H3 H4]...
  apply H4. eapply cardLeq_asym...
Qed.

Example ex6_16_1 : ∀ A, A ≼ A ⟶ 2.
Proof with neauto; try congruence.
  intros.
  set (λ x y : set, match (ixm (x = y)) with
    | inl _ => Embed 0
    | inr _ => Embed 1
  end) as ℱ.
  set (Func A (A ⟶ 2) (λ x, Func A 2 (ℱ x))) as F.
  assert (HF: ∀x ∈ A, Func A 2 (ℱ x): A ⇒ 2). {
    intros x Hx. apply meta_maps_into. intros y Hy.
    unfold ℱ. destruct (ixm (x = y))...
    apply suc_has_0; apply ω_inductive... apply suc_has_n.
  }
  exists F. apply meta_injective.
  - intros x Hx. apply SepI.
    + apply PowerAx. intros f Hf. apply SepE in Hf as []...
    + apply HF...
  - intros x1 H1 x2 H2 Heq.
    assert ((Func A 2 (ℱ x1))[x1] = (Func A 2 (ℱ x2))[x1]) by congruence.
    rewrite meta_func_ap, meta_func_ap in H...
    unfold ℱ in H. destruct (ixm (x1 = x1))...
    destruct (ixm (x2 = x1))... exfalso. eapply suc_neq_0...
    apply HF... apply HF...
Qed.

Example ex6_16_2 : ∀ A, A ≉ A ⟶ 2.
Proof with neauto; try congruence.
  intros A [F [[Hf Hs] [Hd Hr]]].
  set (Func A 2 (λ x, match (ixm (F[x][x] = 0)) with
    | inl _ => 1
    | inr _ => 0
  end)) as g.
  assert (Hgf: g: A ⇒ 2). {
    apply meta_maps_into. intros x Hx.
    destruct (ixm (F[x][x] = 0)). apply suc_has_n.
    apply suc_has_0; apply ω_inductive...
  }
  assert (Hg: g ∈ A ⟶ 2). {
    apply SepI... apply PowerAx.
    intros p Hp. apply SepE in Hp as []...
  }
  rewrite <- Hr in Hg. apply ranE in Hg as [x Hp].
  apply domI in Hp as Hx. apply func_ap in Hp...
  assert (F[x][x] = g[x]) by congruence.
  unfold g in H. rewrite meta_func_ap in H...
  destruct (ixm (F[x][x] = 0))...
  rewrite e in H. eapply suc_neq_0...
Qed.

Example ex6_17_a : Embed 0 <𝐜 ℵ₀ ∧ 0 + ℵ₀ = ℵ₀ + ℵ₀.
Proof with nauto.
  split. apply cardLt_nat_aleph0...
  rewrite cardAdd_comm, cardAdd_ident, cardAdd_aleph0_aleph0...
Qed.

Example ex6_17_b : Embed 1 <𝐜 2 ^ ℵ₀ ∧ 1 ⋅ 2 ^ ℵ₀ = 2 ^ ℵ₀ ⋅ 2 ^ ℵ₀.
Proof with nauto.
  split. eapply cardLeq_lt_tran.
  apply cardLt_nat_aleph0... apply cardLt_power...
  rewrite cardMul_comm, cardMul_ident, cardMul_2aleph0_2aleph0...
Qed.

Example ex6_17_c : Embed 1 <𝐜 Embed 2 ∧ 1 ^ 0 = 2 ^ 0.
Proof with nauto.
  split. apply fin_cardLt_iff_lt... apply suc_has_n...
  rewrite cardExp_0_r, cardExp_0_r...
Qed.

Example ex6_17_d : Embed 1 <𝐜 Embed 2 ∧ 0 ^ 1 = 0 ^ 2.
Proof with nauto.
  split. apply fin_cardLt_iff_lt... apply suc_has_n...
  rewrite cardExp_0_l, cardExp_0_l...
  apply suc_neq_0. apply suc_neq_0.
Qed.

(* ex6_18: see EST6_4 Theorem AC_III_iff_AC_III' *)

(* ==未使用选择公理== *)
(* 有限个非空集合的笛卡尔积非空 *)
Example ex6_19 : ∀ I X, finite I → (∀i ∈ I, ⦿ X[i]) → ⦿ InfCProd I X.
Proof with eauto; try congruence.
  intros * [n [Hn Hqn]]. generalize dependent I.
  set {n ∊ ω | λ n, ∀ I, I ≈ n → (∀i ∈ I, ⦿ X[i]) → ⦿ InfCProd I X} as N.
  ω_induction N Hn; intros I Hqn HneX.
  - apply eqnum_empty in Hqn. rewrite Hqn.
    exists ∅. apply SepI.
    + apply SepI. apply empty_in_all_power.
      apply injection_is_func. apply empty_injective.
    + intros i Hi. exfalso0.
  - apply set_eqnum_suc_inhabited in Hqn as HneI...
    destruct HneI as [j Hj]. apply split_one_element in Hj as HeqI.
    rewrite HeqI in Hqn. apply fin_set_remove_one_element in Hqn...
    specialize IH with (I - ⎨j⎬) as [f Hf]... {
      intros i Hi. apply HneX. apply SepE in Hi as []...
    }
    apply SepE in Hf as [Hf Hfi].
    apply arrow_iff in Hf as [Hf [Hd Hr]].
    pose proof (HneX _ Hj) as [xⱼ Hxj].
    assert (Hf': is_function (f ∪ ⎨<j, xⱼ>⎬)). {
      apply bunion_func... apply single_pair_is_func.
      intros x Hx. exfalso. apply BInterE in Hx as [H1 H2].
      rewrite dom_of_single_pair in H2.
      rewrite Hd in H1. apply SepE in H1 as []...
    }
    assert (Hstar: ∀i ∈ I, (f ∪ ⎨<j, xⱼ>⎬)[i] ∈ X[i]). {
      intros i Hi. destruct (classic (i = j)).
      * subst. replace ((f ∪ ⎨<j, xⱼ>⎬)[j]) with xⱼ...
        symmetry. apply func_ap... apply BUnionI2...
      * assert (Hi': i ∈ I - ⎨j⎬). { apply SepI... apply SingNI... }
        replace ((f ∪ ⎨<j, xⱼ>⎬)[i]) with (f[i])... apply Hfi...
        symmetry. apply func_ap... apply BUnionI1. apply func_correct...
    }
    exists (f ∪ ⎨<j, xⱼ>⎬). apply SepI.
    apply arrow_iff. split; [|split]...
    + apply ExtAx. split; intros Hx.
      * apply domE in Hx as [y Hp]. apply BUnionE in Hp as [].
        apply domI in H. rewrite Hd in H. apply SepE in H as []...
        apply SingE in H. apply op_iff in H as []; subst...
      * destruct (classic (x = j)).
        subst. eapply domI. apply BUnionI2...
        eapply domI. apply BUnionI1. apply func_correct...
        rewrite Hd. apply SepI... apply SingNI...
    + intros i Hi. apply UnionAx. exists (X[i]). split.
      apply ReplAx. exists i. split... apply Hstar...
    + exact Hstar.
Qed.

Example ex6_20 : ∀ A R, ⦿ A →
  (∀y ∈ A, ∃x ∈ A, <x, y> ∈ R) →
  ∃ f, f: ω ⇒ A ∧ ∀n ∈ ω, <f[n⁺], f[n]> ∈ R.
Proof with eauto.
  intros * [a Ha] Hpr.
  set {p ∊ R | λ p, π1 p ∈ A ∧ π2 p ∈ A} as R'.
  pose proof (inv_rel R') as Hrel'.
  apply ac1 in Hrel' as [F [HfF [HsF HdF]]].
  assert (HF: F: A ⇒ A). {
    split; [|split]...
    - rewrite HdF. rewrite inv_dom.
      apply ExtAx. intros y. split; intros Hy.
      + apply ranE in Hy as [x Hp].
        apply SepE in Hp as [_ [_ Hy]]. zfcrewrite.
      + pose proof (Hpr _ Hy) as [x [Hx Hp]].
        eapply ranI. apply SepI. apply Hp. zfcrewrite...
    - intros y Hy. apply ranE in Hy as [x Hp].
      apply HsF in Hp. apply inv_op in Hp.
      apply SepE in Hp as [_ [Hx _]]. zfcrewrite.
  }
  pose proof (ω_recursion_0 _ _ _ HF Ha) as [f [Hf [Hf0 Heq]]].
  exists f. split... intros n Hn. rewrite Heq...
  assert (HsR: R' ⊆ R). { intros p Hp. apply SepE in Hp as []... }
  apply HsR. rewrite inv_op. apply HsF. apply func_correct...
  destruct HF as [_ [Hd _]]. rewrite Hd. eapply ap_ran...
Qed.

(* ex6_21: see EST6_4_EX Theorem AC_VI_to_AC_VII *)
