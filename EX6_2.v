(** Solutions to "Elements of Set Theory" Chapter 6 Part 2 **)
(** Coq coding by choukh, Oct 2020 **)

Require Export ZFC.EST6_4.
Require Import ZFC.lib.NatIsomorphism.
Require Import ZFC.lib.IndexedFamilyUnion.
Require Import ZFC.lib.WosetMin.
Require Import ZFC.lib.Choice.
Import WosetMin.SimpleVer.

(* 所有集合的支配集不能构成一个集合 *)
Example ex6_15 : ¬∃ 𝒜, ∀ B, ∃A ∈ 𝒜, B ≼ A.
Proof with eauto.
  intros [𝒜 H].
  specialize H with (𝒫 ⋃𝒜) as [A [H1 H2]].
  apply union_dominate in H1.
  assert (𝒫 ⋃𝒜 ≼ ⋃𝒜) by (eapply dominate_tran; eauto).
  apply cardLeq_iff in H. rewrite card_of_power in H.
  destruct (cardLt_power (|⋃𝒜|)) as [H3 H4]...
  apply H4. eapply cardLeq_antisym...
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
    + apply PowerAx. intros f Hf. apply SepE1 in Hf...
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
    intros p Hp. apply SepE1 in Hp...
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
  split. apply cardLt_aleph0_if_finite...
  rewrite cardAdd_comm, cardAdd_ident, cardAdd_aleph0_aleph0...
Qed.

Example ex6_17_b : Embed 1 <𝐜 2 ^ ℵ₀ ∧ 1 ⋅ 2 ^ ℵ₀ = 2 ^ ℵ₀ ⋅ 2 ^ ℵ₀.
Proof with nauto.
  split. eapply cardLeq_lt_tran.
  apply cardLt_aleph0_if_finite... apply cardLt_power...
  rewrite cardMul_comm, cardMul_ident, cardMul_expAleph0_expAleph0...
Qed.

Example ex6_17_c : Embed 1 <𝐜 Embed 2 ∧ 1 ^ 0 = 2 ^ 0.
Proof with nauto.
  split. apply fin_cardLt_iff_lt... apply suc_has_n...
  rewrite cardExp_0_r, cardExp_0_r...
Qed.

Example ex6_17_d : Embed 1 <𝐜 Embed 2 ∧ 0 ^ 1 = 0 ^ 2.
Proof with nauto.
  split. apply fin_cardLt_iff_lt... apply suc_has_n...
  rewrite cardExp_0_l, cardExp_0_l... apply suc_neq_0.
Qed.

(* ex6_18: see lib/Choice Theorem AC_III_iff_III' *)

(* ==不需要选择公理== *)
(* 有限个非空集合的笛卡尔积非空 *)
Example ex6_19 : ∀ I ℱ, finite I → (∀i ∈ I, ⦿ ℱ i) → ⦿ InfCProd I ℱ.
Proof with eauto; try congruence.
  intros * [n [Hn Hqn]]. generalize dependent I.
  set {n ∊ ω | λ n, ∀ I, I ≈ n → (∀i ∈ I, ⦿ ℱ i) → ⦿ InfCProd I ℱ} as N.
  ω_induction N Hn; intros I Hqn HneX.
  - apply eqnum_empty in Hqn. rewrite Hqn.
    exists ∅. apply SepI.
    + apply SepI. apply empty_in_all_power.
      apply injection_is_func. apply empty_injective.
    + intros i Hi. exfalso0.
  - apply set_eqnum_suc_nonempty in Hqn as HneI...
    destruct HneI as [j Hj]. apply split_one_element in Hj as HeqI.
    rewrite HeqI in Hqn. apply finite_set_remove_one_element in Hqn...
    specialize IH with (I - ⎨j⎬) as [f Hf]... {
      intros i Hi. apply HneX. apply SepE1 in Hi...
    }
    apply SepE in Hf as [Hf Hfi].
    apply arrow_iff in Hf as [Hf [Hd Hr]].
    pose proof (HneX _ Hj) as [xⱼ Hxj].
    assert (Hf': is_function (f ∪ ⎨<j, xⱼ>⎬)). {
      apply bunion_is_func... apply single_pair_is_func.
      apply EmptyI. intros x Hx. apply BInterE in Hx as [H1 H2].
      rewrite dom_of_single_pair in H2.
      rewrite Hd in H1. apply SepE2 in H1...
    }
    assert (Hstar: ∀i ∈ I, (f ∪ ⎨<j, xⱼ>⎬)[i] ∈ ℱ i). {
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
        apply domI in H. rewrite Hd in H. apply SepE1 in H...
        apply SingE in H. apply op_iff in H as []; subst...
      * destruct (classic (x = j)).
        subst. eapply domI. apply BUnionI2...
        eapply domI. apply BUnionI1. apply func_correct...
        rewrite Hd. apply SepI... apply SingNI...
    + intros i Hi. apply UnionAx. exists (ℱ i). split.
      apply ReplAx. exists i. split... apply Hstar...
    + exact Hstar.
Qed.

(* ex6_20 see EST7_2 Lemma non_woset_ex_descending_chain *)
(* ex6_21 see lib/Choice Theorem AC_VI_to_AC_VII *)
(* ex6_22 see lib/Choice Theorem AC_I_iff_I' *)

Example ex6_23 : ∀ A F g h,
  is_function g → dom g = ω →
  (∀n ∈ ω, g[n] = F[A - h[n]]) → h[∅] = ∅ →
  (∀n ∈ ω, h[n⁺] = h[n] ∪ ⎨F[A - h[n]]⎬) →
  ∀n ∈ ω, g⟦n⟧ = h[n].
Proof with eauto; try congruence.
  intros * Hfg Hdg Hrg Hh0 Hhn n Hn.
  set {n ∊ ω | λ n, g⟦n⟧ = h[n]} as N.
  ω_induction N Hn.
  - apply ExtAx. split; intros Hx.
    + apply imgE in Hx as [k [Hk _]]. exfalso0.
    + rewrite Hh0 in Hx. exfalso0.
  - apply ExtAx. split; intros Hx.
    + apply imgE in Hx as [k [Hk Hp]]. rewrite Hhn...
      apply BUnionE in Hk as [].
      * apply BUnionI1. rewrite <- IH. eapply imgI...
      * apply BUnionI2. apply SingE in H. subst k.
        apply func_ap in Hp... subst x. rewrite <- Hrg...
    + rewrite Hhn in Hx... apply BUnionE in Hx as [].
      * rewrite <- IH in H. apply imgE in H as [k [Hk Hp]].
        eapply imgI. apply BUnionI1... apply Hp.
      * apply SingE in H. subst x. rewrite <- Hrg...
        eapply imgI. apply BUnionI2... apply func_correct...
Qed.

(* ex6_24 see EST6_4 CardInfSum CardInfProd *)

(** ex6_25 **)

(* 增长序列 *)
Definition incr_seq : (nat → set) → Prop := λ Q,
  ∀ n, Q n ⊆ Q (S n).

(* 若增长序列的元素下标有小于等于关系那么元素有包含关系 *)
Lemma incr_seq_index_leq_impl_sub : ∀ Q, incr_seq Q →
  ∀ n m, n <= m → Q n ⊆ Q m.
Proof with auto.
  intros Q Hinc n m Hle.
  induction m.
  - apply Le.le_n_0_eq in Hle. subst...
  - apply PeanoNat.Nat.le_succ_r in Hle as []; [|subst]...
    eapply sub_tran. apply IHm... apply Hinc.
Qed.

(* ==需要选择公理== *)
Example ex6_25 : AC_III → ∀ Q A, incr_seq Q → A ⊆ ⋃ᵢ Q →
  (∀ B, infinite B → B ⊆ A → ∃ n, infinite (B ∩ Q n)) →
  ∃ n, A ⊆ Q n.
Proof with neauto; try congruence.
  intros AC3 * Hinc Hsuba Hinf.
  apply not_all_not_ex. intros Han.
  assert (Hnea: ∀ n, ⦿ (A - Q n)). {
    intros. apply EmptyNE. intros H.
    apply sub_iff_no_comp in H. eapply Han...
  }
  clear Han.
  pose proof (AC3 A) as [F [_ [_ Hch]]].
  set (λ n, F[A - Q n]) as g.
  set {λ n, g n | n ∊ ω} as B.
  assert (Hneb: ⦿ B). {
    exists (F[A - Q 0]). apply ReplAx.
    exists ∅. split... rewrite <- zero, embed_proj_id...
  }
  assert (Hgn1: ∀ n, g n ∈ A - Q n). { intros. apply Hch... }
  assert (Hgn2: ∀ n, ∃ m, g n ∈ Q m). {
    intros. specialize Hgn1 with n.
    apply SepE in Hgn1 as [Hgn _]. apply Hsuba in Hgn.
    apply nat_IFUnionE in Hgn as [m Hgm]. exists m...
  }
  assert (Hgn3: ∀ n, g n ∈ B). {
    intros. apply ReplAx. exists (Embed n). split.
    apply embed_ran. rewrite embed_proj_id...
  }
  assert (Hgn4: ∀ n, g n ∉ Q n). {
    intros. specialize Hgn1 with n.
    apply SepE2 in Hgn1...
  }
  specialize Hinf with B as [n Hinf].
  - intros Hfin.
    set (λ x, {n ∊ ω | λ n, x ∈ Q n}) as 𝒩.
    set (λ x, (Min Lt)[𝒩 x]) as f.
    assert (Hmin: ∀b ∈ B, ε_minimum (f b) (𝒩 b)). {
      intros b Hb. apply ω_min.
      apply ReplAx in Hb as [n [Hn Heqb]]. subst b.
      specialize Hgn2 with n as [m Hgn].
      - exists (Embed m). apply SepI.
        apply embed_ran. rewrite embed_proj_id...
      - intros x Hx. apply SepE1 in Hx...
    }
    apply (repl_finite f) in Hfin.
    apply finite_subset_of_ω_is_bounded in Hfin as [m [Hm Hmax]]; revgoals. {
      intros x Hx. apply ReplAx in Hx as [b [Hb Hfb]]. subst x.
      apply Hmin in Hb as [Hfb _]. apply SepE1 in Hfb...
    } {
      destruct Hneb as [b Hb]. exists (f b).
      apply ReplAx. exists b. split...
    }
    cut (B ⊆ Q m). {
      intros Hsub. apply (Hgn4 m). apply Hsub...
    }
    apply ReplAx in Hm as [b [Hb Heqm]].
    apply Hmin in Hb as [Hfb _]. apply SepE in Hfb as [Hfb _].
    assert (Hsub: B ⊆ ⋃{λ n, Q n | n ∊ m ⁺}). {
      intros x Hx. assert (Hx' := Hx).
      apply Hmin in Hx' as [Hfx Hsub].
      apply SepE in Hfx as [Hfx Hxq].
      apply UnionAx. exists (Q (f x)). split...
      apply ReplAx. exists (f x). split...
      apply lt_suc_iff_sub... apply Hmax.
      apply ReplAx. exists x. split...
    }
    eapply sub_tran. apply Hsub.
    intros x Hx. apply UnionAx in Hx as [q [Hq Hx]].
    apply ReplAx in Hq as [n [Hn Hq]]. subst q.
    assert (Hnw: n ∈ ω). {
      eapply ω_trans... apply ω_inductive...
    }
    apply BUnionE in Hn as [].
    + apply (incr_seq_index_leq_impl_sub Q Hinc n)...
      apply le_isomorphic. repeat rewrite proj_embed_id...
      apply lt_iff_psub...
    + apply SingE in H...
  - intros x Hx. apply ReplAx in Hx as [n [Hn Hx]]. subst x.
    assert (Hsub: A - Q n ⊆ A) by auto. apply Hsub...
  - set {m ∊ ω | λ m, g m ∈ Q n} as M.
    set {λ m, g m | m ∊ M} as C.
    assert (Hsubm: M ⊆ ω). {
      intros x Hx. apply SepE1 in Hx...
    }
    assert (Heq: B ∩ Q n = C). {
      apply ExtAx. split; intros Hx.
      - apply BInterE in Hx as [H1 H2].
        apply ReplAx in H1 as [m [Hm Hgm]]. subst x.
        apply ReplAx. exists m. split... apply SepI...
      - apply ReplAx in Hx as [m [Hm Hgm]]. subst x.
        apply SepE in Hm as [_ Hgm]. apply BInterI...
    }
    assert (HinfM: infinite M). {
      intros Hfin. apply Hinf. rewrite Heq.
      apply (dominated_by_finite_is_finite _ M)...
      set (Func M C (λ x, g x)) as f.
      apply (domain_of_surjection_dominate_range ac1 _ _ f).
      apply meta_surjective.
      - intros x Hx. apply ReplAx. exists x. split...
      - intros y Hy. apply ReplAx in Hy as [x [Hx Heqy]].
        exists x. split...
    }
    pose proof (infinite_subset_of_ω_is_unbound M) as [_ Harc]...
    pose proof (embed_ran n) as Hnw.
    apply Harc in Hnw as [m [Hm Hnm]].
    apply SepE in Hm as [Hm Hgm].
    apply lt_iff_psub in Hnm as [Hnm _]...
    rewrite <- (proj_embed_id m) in Hnm...
    apply le_isomorphic in Hnm.
    apply (incr_seq_index_leq_impl_sub Q Hinc) in Hnm.
    apply Hnm in Hgm. specialize Hgn1 with m.
    apply SepE2 in Hgn1...
Qed.
