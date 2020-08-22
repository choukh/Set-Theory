(** Based on "Elements of Set Theory" Chapter 1 Part 1 **)
(** Coq coding by choukh, Aug 2020 **)

Require Export ZFC.lib.Natural.
Require Export ZFC.lib.FuncFacts.

(*** EST第六章1：等势，康托定理，鸽笼原理，有限基数 ***)

(** 等势 **)
Definition equinumerous : set → set → Prop := λ A B,
  ∃ F, F: A ⟺ B.
Notation "A ≈ B" := ( equinumerous A B) (at level 70).
Notation "A ≉ B" := (¬equinumerous A B) (at level 70).

(* 任意集合的幂集与该集合到双元集的所有函数的集合等势 *)
Example power_eqnum_func_to_2 : ∀ A, 𝒫 A ≈ A ⟶ 2.
Proof with neauto.
  intros.
  set (λ B, Relation A 2 (λ x y,
    y = match (ixm (x ∈ B)) with
      | inl _ => 1
      | inr _ => 0
    end
  )) as ℱ.
  set (Relation (𝒫 A) (A ⟶ 2) (λ B y, y = ℱ B)) as G.
  assert (H1_2: 1 ∈ 2) by apply suc_has_n.
  assert (H0_2: 0 ∈ 2) by (apply suc_has_0; apply ω_inductive; nauto).
  assert (Hff: ∀ B, is_function (ℱ B)). {
    intros. repeat split.
    - apply rel_is_rel.
    - apply domE in H...
    - intros y1 y2 H1 H2.
      apply SepE2 in H1. apply SepE2 in H2. zfcrewrite.
  }
  assert (Hfs: ∀ B, ℱ B ∈ A ⟶ 2). {
    intros. apply Arrow_correct. split... split.
    - apply ExtAx. intros x. split; intros Hx.
      + apply domE in Hx as [y Hp]. apply SepE1 in Hp.
        apply CProdE1 in Hp as []. zfcrewrite.
      + destruct (classic (x ∈ B)).
        * eapply domI. apply SepI.
          { apply CProdI. apply Hx. apply H1_2. }
          { zfcrewrite. destruct (ixm (x ∈ B))... exfalso... }
        * eapply domI. apply SepI.
          { apply CProdI. apply Hx. apply H0_2. }
          { zfcrewrite. destruct (ixm (x ∈ B))... exfalso... }
    - intros x Hx. destruct (classic (x ∈ B)).
      + cut ((ℱ B)[x] = 1). congruence.
        apply func_ap... apply SepI. apply CProdI...
        zfcrewrite. destruct (ixm (x ∈ B))... exfalso...
      + cut ((ℱ B)[x] = 0). congruence.
        apply func_ap... apply SepI. apply CProdI...
        zfcrewrite. destruct (ixm (x ∈ B))... exfalso...
  }
  assert (Hchr: ∀y ∈ A ⟶ 2, ∃ B, B ⊆ A ∧ y = ℱ B). {
    intros y Hy. set {x ∊ A | λ x, y[x] = 1} as B.
    exists B. split. apply sep_sub.
    apply SepE in Hy as [Hy [Hfy [Hdy Hry]]]. apply PowerAx in Hy.
    apply ExtAx. intros x. split; intros Hxy.
    - apply Hy in Hxy as Hxp. apply SepI...
      apply CProd_correct in Hxp as [a [Ha [b [Hb Hx]]]].
      subst x. zfcrewrite. destruct (ixm (a ∈ B)) as [H|H].
      + apply SepE2 in H as Hap. rewrite <- Hap.
        symmetry. apply func_ap...
      + rewrite two in Hb. apply TwoE in Hb as []...
        exfalso. subst b. rewrite <- one in Hxy.
        apply H. apply SepI... apply func_ap...
    - apply SepE in Hxy as [Hx Heq].
      apply CProd_correct in Hx as [a [Ha [b [Hb Hx]]]].
      subst x. zfcrewrite. rewrite <- Hdy in Ha.
      destruct (ixm (a ∈ B)) as [H|H]; subst b.
      + apply SepE in H as [].
        rewrite <- H0. apply func_correct...
      + apply func_correct in Ha as Hap...
        apply ranI in Hap. apply Hry in Hap.
        rewrite two in Hap. apply TwoE in Hap as []...
        * rewrite pred, <- H0. apply func_correct...
        * exfalso. apply H. apply SepI.
          rewrite <- Hdy... rewrite one...
  }
  exists G. repeat split.
  - apply rel_is_rel. - apply domE in H...
  - intros y1 y2 H1 H2.
    apply SepE in H1 as [Hp H1]. apply SepE2 in H2.
    apply CProdE1 in Hp as []. zfcrewrite.
  - apply ranE in H...
  - intros B1 B2 H1 H2.
    apply SepE in H1 as [H11 H12].
    apply SepE in H2 as [H21 H22].
    apply CProdE1 in H11 as [H11 _].
    apply CProdE1 in H21 as [H21 _]. zfcrewrite. subst.
    apply PowerAx in H11. apply PowerAx in H21.
    apply ExtAx. intros a. split; intros Hab.
    + apply H11 in Hab as Haa.
      assert (Hp: <a, 1> ∈ ℱ B1). {
        apply SepI. apply CProdI... zfcrewrite.
        destruct (ixm (a ∈ B1))... exfalso...
      }
      rewrite H22 in Hp. apply SepE2 in Hp. zfcrewrite.
      destruct (ixm (a ∈ B2))... exfalso. eapply suc_neq_0...
    + apply H21 in Hab as Haa.
      assert (Hp: <a, 1> ∈ ℱ B2). {
        apply SepI. apply CProdI... zfcrewrite.
        destruct (ixm (a ∈ B2))... exfalso...
      }
      rewrite <- H22 in Hp. apply SepE2 in Hp. zfcrewrite.
      destruct (ixm (a ∈ B1))... exfalso. eapply suc_neq_0...
  - apply ExtAx. intros x. split; intros Hx.
    + apply domE in Hx as [y Hp]. apply SepE1 in Hp.
      apply CProdE1 in Hp as []. zfcrewrite.
    + eapply domI. apply SepI. apply CProdI... zfcrewrite...
  - apply ExtAx. intros y. split; intros Hy.
    + apply ranE in Hy as [x Hp]. apply SepE1 in Hp.
      apply CProdE1 in Hp as []. zfcrewrite.
    + assert (Hy' := Hy). apply Hchr in Hy' as [B [Hsub Heq]].
      eapply ranI. apply SepI. apply CProdI...
      apply PowerAx. apply Hsub. zfcrewrite.
Qed.

(* 等势有自反性 *)
Lemma eqnum_refl : ∀ A, A ≈ A.
Proof.
  intros. exists (Ident A).
  apply ident_bijective.
Qed.
Hint Immediate eqnum_refl : core.

(* 等势有对称性 *)
Lemma eqnum_symm : ∀ A B, A ≈ B → B ≈ A.
Proof.
  intros * [f H]. exists (f⁻¹).
  apply inv_bijection. auto.
Qed.

(* 等势有传递性 *)
Lemma eqnum_tran : ∀ A B C, A ≈ B → B ≈ C → A ≈ C.
Proof.
  intros * [f Hf] [g Hg]. exists (g ∘ f).
  eapply compo_bijection; eauto.
Qed.

(* 集合与空集等势当且仅当它是空集 *)
Lemma eqnum_empty : ∀ A, A ≈ ∅ ↔ A = ∅.
Proof with auto.
  split. intros [f Hf]. apply bijection_empty in Hf...
  intros. subst A...
Qed.

(* 康托定理：任意集合都不与自身的幂集等势 *)
Theorem Cantor's : ∀ A, A ≉ 𝒫 A.
Proof with auto.
  intros A [f [[Hf _] [Hd Hr]]].
  set {x ∊ A | λ x, x ∉ f[x]} as B.
  assert (Hsub: B ⊆ A) by apply sep_sub.
  apply PowerAx in Hsub as HB. rewrite <- Hr in HB.
  apply ranE in HB as [x Hap]. apply domI in Hap as Hx.
  rewrite Hd in Hx. apply func_ap in Hap...
  destruct (classic (x ∈ B)).
  - apply SepE2 in H. apply H. rewrite Hap. apply SepI...
  - apply H. apply SepI... rewrite Hap...
Qed.

(* 鸽笼原理引理：任意自然数到自身的单射是满射 *)
Lemma injection_between_same_nat_surjective :
  ∀n ∈ ω, ∀ f, f: n ⇔ n → ran f = n.
Proof with neauto; try congruence.
  intros n Hn.
  set {n ∊ ω | λ n, ∀ f, f: n ⇔ n → ran f = n} as N.
  ω_induction N Hn. {
    intros f [_ [_ Hr]]. apply sub_asym...
    intros x Hx. exfalso0.
  }
  rename m into k.
  assert (Hstar: ∀ f, f: k⁺ ⇔ k⁺ → (∀p ∈ k, f[p] ∈ k) → ran f = k⁺). {
    intros f [[Hf Hs] [Hd Hr]] H.
    assert (Hr': ran (f ↾ k) = k). {
      apply IH. split. apply restr_injective... split...
      split... apply restr_dom... rewrite Hd...
      intros y Hy. apply ranE in Hy as [x Hp].
      apply restrE2 in Hp as [Hp Hx]...
      apply func_ap in Hp... subst. apply H...
    }
    assert (Hkd: k ∈ dom f) by (rewrite Hd; nauto).
    assert (Hfk: f[k] = k). {
      apply domE in Hkd as [y Hp]. apply ranI in Hp as Hy.
      apply Hr in Hy. apply BUnionE in Hy as [Hy|Hy].
      - exfalso. rewrite <- Hr' in Hy.
        apply ranE in Hy as [x Hp'].
        apply restrE2 in Hp' as [Hp' Hx]...
        eapply singrE in Hp... subst.
        eapply lt_not_refl; revgoals...
      - apply SingE in Hy; subst. apply func_ap...
    }
    apply sub_asym... intros p Hp.
    rewrite (ran_split_by_restr _ _ _ Hd).
    apply BUnionE in Hp as [].
    + apply BUnionI1. rewrite Hr'...
    + apply BUnionI2. rewrite ran_of_restr_to_single...
  }
  clear Hn N n IH. intros f Hf.
  destruct (classic (∀p ∈ k, f[p] ∈ k)). { apply Hstar... }
  rewrite set_not_all_ex_not in H. destruct H as [p [Hp Hout]].
  assert (Hpw: p ∈ ω) by (eapply ω_trans; eauto).
  assert (Hpd: p ∈ k⁺) by (apply BUnionI1; nauto).
  assert (Hkd: k ∈ k⁺) by nauto.
  pose proof (injection_swap_value f k⁺ k⁺ p Hpd k Hkd Hf) as [Hf' Hreq].
  remember (FuncSwapValue f p k) as f'.
  rewrite <- Hreq. apply Hstar... clear Hstar Hreq.
  destruct Hf as [[Hf Hs] [Hd Hr]].
  assert (Hfp: f[p] = k). {
    cut (f[p] ∈ k⁺). intros.
    - apply BUnionE in H as [|Hfp]. exfalso... apply SingE in Hfp...
    - apply Hr. eapply ranI. apply func_correct...
  }
  assert (Hfk: f[k] ∈ k). {
    rewrite <- Hd in Hkd. apply func_correct in Hkd as Hpr...
    apply ranI in Hpr as Hyr. apply Hr in Hyr.
    apply BUnionE in Hyr as [|Hyr]... apply SingE in Hyr.
    exfalso. cut (k = p). intros. rewrite H in Hp.
    eapply lt_not_refl; revgoals... eapply func_injective... split...
  }
  destruct Hf' as [[Hf' _] [Hd' _]]. intros x Hx.
  destruct (classic (x = p)) as [Hxp|Hxp]; [|
  destruct (classic (x = k)) as [Hxk|Hxk]].
  - subst x. rewrite <- Hd' in Hpd.
    apply domE in Hpd as [y Hpr]. apply func_ap in Hpr as Hap...
    rewrite Heqf' in Hpr. apply SepE in Hpr as [_ Hpr]. zfcrewrite.
    destruct (ixm (p = p))...
  - subst x. exfalso. eapply lt_not_refl; revgoals...
  - assert (Hxd: x ∈ dom f) by (rewrite Hd; apply BUnionI1; auto).
    assert (Hxd': x ∈ dom f') by (rewrite Hd'; apply BUnionI1; auto).
    apply domE in Hxd' as [y Hpr]. apply func_ap in Hpr as Hap...
    rewrite Heqf' in Hpr. apply SepE in Hpr as [_ Hpr]. zfcrewrite.
    destruct (ixm (x = p))... destruct (ixm (x = k))...
    subst y. rewrite Hap. clear Hap n n0 Hx Hxk.
    apply domE in Hxd as [y Hpr].
    apply domI in Hpr as Hxd. apply ranI in Hpr as Hy.
    apply func_ap in Hpr... subst y. apply Hr in Hy.
    apply BUnionE in Hy as []... apply SingE in H.
    exfalso. apply Hxp. eapply func_injective... split...
Qed.

(* 任意自然数到自身的满射是单射 *)
Lemma surjection_between_same_nat_injective :
  ∀n ∈ ω, ∀ f, f: n ⟹ n → injective f.
Proof with auto.
  intros n Hn f Hf.
  assert (Hf' := Hf). destruct Hf' as [Hff [Hdf Hrf]].
  apply right_inv_of_surjection_injective in Hf as [g [Hg Hid]].
  apply injection_between_same_nat_surjective in Hg as Hrg...
  destruct Hg as [[Hfg Hsg] [Hdg _]].
  assert (Heq: (f ∘ g) ∘ g⁻¹ = Ident n ∘ g⁻¹) by congruence.
  rewrite compo_assoc, compo_inv_ran_ident,
    right_compo_ident, Hrg, <- Hdf, restr_to_dom,
    left_compo_ident, Hdf, <- Hdg, restr_to_dom in Heq... 
  assert (Hgb: g: n ⟺ n) by (split; split ; auto).
  apply inv_bijection in Hgb. rewrite <- Heq in Hgb.
  destruct Hgb... destruct Hfg... destruct Hff...
Qed.

(* 鸽笼原理：任意自然数都不与自身的真子集等势 *)
Theorem pigeonhole : ∀ k, ∀n ∈ ω, k ⊂ n → n ≉ k.
Proof with eauto.
  intros k n Hn [Hsub Hnq] [f [[Hf Hs] [Hd Hr]]].
  apply Hnq. rewrite <- Hr. eapply injection_between_same_nat_surjective...
  split; split... rewrite Hr...
Qed.

(* 有限集与无限集的定义 *)
Definition finite : set → Prop := λ A, ∃n ∈ ω, A ≈ n.
Definition infinite : set → Prop := λ A, ¬finite A.

(* 空集是有限集 *)
Fact empty_finite : finite ∅.
Proof. exists ∅. split; nauto. Qed.
Hint Resolve empty_finite : core.

(* 自然数是有限集 *)
Fact nat_finite : ∀n ∈ ω, finite n.
Proof.
  intros n Hn. exists n. split. apply Hn. apply eqnum_refl.
Qed.

(* 鸽笼原理推论：任意集合都不与自身的真子集等势 *)
Corollary no_fin_eqnum_proper_sub : ∀ A B, finite A → B ⊂ A → A ≉ B.
Proof with eauto.
  intros * [n [Hn [g Hg]]] Hsub [f Hf].
  assert (Hf': f: A ⇔ A). {
    destruct Hf as [Hf [Hd Hr]]. destruct Hsub as [Hsub _].
    split... split... rewrite <- Hr in Hsub...
  }
  pose proof (injection_transform f g A n Hf' Hg) as [Hih [Hdh Hrh]].
  remember (g ∘ f ∘ g⁻¹) as h.
  assert (Hrh': ran h ⊂ n). {
    destruct Hf as [_ [_ Hrf]].
    destruct Hg as [Hig [Hdg Hrg]].
    assert (Hig' := Hig). destruct Hig' as [Hg Hsg].
    apply comp_inhabited in Hsub as [a Ha].
    apply CompE in Ha as [Ha Ha'].
    apply properSubI... exists (g[a]). split.
    - rewrite <- Hrg. eapply ranI.
      apply func_correct... rewrite Hdg...
    - intros Hga. apply ranE in Hga as [x Hp]. rewrite Heqh in Hp.
      apply compoE in Hp as [y [_ Hp]].
      apply compoE in Hp as [z [H1 H2]].
      apply domI in H2 as Hzd. apply func_ap in H2...
      apply func_injective in H2; auto; [|rewrite Hdg]...
      clear Hzd. subst z. apply ranI in H1. rewrite Hrf in H1... 
  }
  apply (pigeonhole (ran h) n)... exists h. split...
Qed.

(* 与自身的真子集等势的集合是无限集 *)
Corollary infiniteI : ∀ A B, B ⊂ A → A ≈ B → infinite A.
Proof.
  intros A B Hsub Heqn Hfin.
  eapply no_fin_eqnum_proper_sub; eauto.
Qed.

(* ω是无限集 *)
Corollary ω_infinite : infinite ω.
Proof with nauto.
  set (ω - ⎨0⎬) as B.
  assert (H0: 0 ∉ B). {
    intros H. apply SepE in H as [_ H]. apply H...
  }
  assert (Hsub: B ⊂ ω). {
    apply properSubI...
    intros n Hn. apply CompE in Hn as []...
    exists 0. split...
  }
  eapply infiniteI. apply Hsub.
  destruct σ_func as [Hf [Hd _]].
  exists σ. split; split...
  - split. apply ranE in H...
    intros x1 x2 H1 H2.
    apply ReplAx in H1 as [m [Hm H1]].
    apply ReplAx in H2 as [n [Hn H2]].
    apply op_correct in H1 as [];
    apply op_correct in H2 as []; subst.
    apply suc_injective in H4...
  - apply ExtAx. intros y. split; intros Hy.
    + apply ranE in Hy as [x Hp].
      apply domI in Hp as Hx. rewrite Hd in Hx.
      apply func_ap in Hp... subst y. rewrite σ_ap...
      apply CompI. apply ω_inductive... apply SingNI...
    + apply CompE in Hy as [Hy Hy']. apply SingNE in Hy'.
      ω_destruct y. exfalso... subst y.
      eapply ranI. apply ReplAx. exists n'. split...
Qed.

(* 有限集与唯一自然数等势 *)
Corollary finite_eqnum_unique_nat : ∀ A, finite A →
  ∃! n, n ∈ ω ∧ A ≈ n.
Proof with eauto.
  intros A Hfin. split...
  intros m n [Hm H1] [Hn H2].
  assert (H3: m ≈ n). {
    eapply eqnum_tran. apply eqnum_symm. apply H1. apply H2.
  }
  destruct (classic (m = n))... exfalso.
  apply lt_connected in H as []...
  - apply lt_iff_sub in H...
    apply (no_fin_eqnum_proper_sub n m)... apply nat_finite...
    apply eqnum_symm...
  - apply lt_iff_sub in H...
    apply (no_fin_eqnum_proper_sub m n)... apply nat_finite...
Qed.

(* 等势的自然数相等 *)
Corollary nat_eqnum_eq : ∀ m n ∈ ω, m ≈ n → m = n.
Proof with auto.
  intros m Hm n Hn Hqn.
  destruct (classic (m = n))... exfalso.
  apply lt_connected in H as []...
  - apply lt_iff_sub in H...
    apply (no_fin_eqnum_proper_sub n m)... apply nat_finite...
    apply eqnum_symm...
  - apply lt_iff_sub in H...
    apply (no_fin_eqnum_proper_sub m n)... apply nat_finite...
Qed.

(* 有限基数 *)
Definition fin_card : set → set := λ A, ⋃{n ∊ ω | λ n, A ≈ n}.

(* 有限基数定义为与有限集自身等势的自然数 *)
Lemma fin_card_correct : ∀ A, finite A →
  ∃n ∈ ω, fin_card A = n ∧ A ≈ n.
Proof with auto.
  intros A Hfin. assert (Hfin' := Hfin).
  destruct Hfin' as [n [Hn H1]]. exists n. repeat split...
  apply ExtAx. split; intros Hx.
  - apply UnionAx in Hx as [m [Hm Hx]].
    apply SepE in Hm as [Hm H2].
    pose proof (finite_eqnum_unique_nat A) as [_ Hu]...
    cut (m = n). congruence. apply Hu; split...
  - apply UnionAx. exists n. split... apply SepI...
Qed.

(* 有限集与其基数等势 *)
Lemma fin_set_eqnum_its_card : ∀ A, finite A → A ≈ fin_card A.
Proof.
  intros A Hfin.
  apply fin_card_correct in Hfin as [n [_ [Hc Hqn]]].
  congruence.
Qed.

(* 有限集等势当且仅当它们的基数相等 *)
Lemma fin_sets_eqnum_iff_cards_eq : ∀ A B, finite A → finite B → 
  fin_card A = fin_card B ↔ A ≈ B.
Proof with auto.
  intros A B H1 H2.
  apply fin_card_correct in H1 as [m [Hm [H11 H12]]].
  apply fin_card_correct in H2 as [n [Hn [H21 H22]]].
  split; intros.
  - eapply eqnum_tran. apply H12.
    apply eqnum_symm. congruence.
  - cut (m ≈ n). intros Hqn.
    + apply nat_eqnum_eq in Hqn... congruence.
    + eapply eqnum_tran. apply eqnum_symm. apply H12.
      eapply eqnum_tran. apply H. apply H22.
Qed.

(* 自然数的基数与该自然数相等 *)
Lemma fin_card_n : ∀n ∈ ω, fin_card n = n.
Proof with auto.
  intros n Hn.
  apply ExtAx. split; intros Hx.
  - apply UnionAx in Hx as [m [Hm Hx]].
    apply SepE in Hm as [Hm Hqn].
    apply nat_eqnum_eq in Hqn... congruence.
  - apply UnionAx. exists n. split... apply SepI...
Qed.

(* 自然数的子集是有限集 *)
Lemma sub_of_nat_is_finite : ∀n ∈ ω, ∀ C,
  C ⊂ n → ∃m ∈ ω, m ∈ n ∧ C ≈ m.
Proof with neauto.
  intros n Hn.
  set {n ∊ ω | λ n, ∀ C, C ⊂ n → ∃m ∈ ω, m ∈ n ∧ C ≈ m} as N.
  ω_induction N Hn; intros C [Hsub Hnq].
  - exfalso. apply Hnq. apply EmptyI.
    intros x Hx. apply Hsub in Hx. exfalso0.
  - rename m into k. rename Hm into Hk.
    (* C = {0, 1 ... k-1} | k *)
    destruct (classic (C = k)) as [|Hnq']. {
      exists k. split... split. apply suc_has_n. subst...
    }
    destruct (classic (k ∈ C)) as [Hkc|Hkc]; revgoals.
    + (* C = {0, 1 ... k-2} | k-1, k *)
      assert (Hps: C ⊂ k). {
        split... intros x Hx. apply Hsub in Hx as Hxk.
        apply BUnionE in Hxk as []... exfalso.
        apply SingE in H. subst...
      }
      apply IH in Hps as [m [Hmw [Hmk Hqn]]].
      exists m. split... split... apply BUnionI1...
    + (* C = {0, 1 ... k-2, k} | k-1 *)
      assert (HC: C = (C ∩ k) ∪ ⎨k⎬). {
        apply ExtAx. split; intros Hx.
        - destruct (classic (x = k)).
          + apply BUnionI2. subst...
          + apply BUnionI1. apply BInterI...
            apply Hsub in Hx. apply BUnionE in Hx as [|Hx]...
            exfalso. apply SingE in Hx...
        - apply BUnionE in Hx as [Hx|Hx].
          + apply BInterE in Hx as []...
          + apply SingE in Hx. subst...
      }
      assert (Hps: C ∩ k ⊂ k). {
        split. intros x Hx. apply BInterE in Hx as []...
        intros H. rewrite binter_comm, <- ch2_17_1_4 in H.
        apply Hnq. apply ExtAx. split; intros Hx.
        - apply Hsub in Hx...
        - apply BUnionE in Hx as []. apply H in H0...
          apply SingE in H0. subst...
      }
      apply IH in Hps as [m [Hmw [Hmk [f Hf]]]].
      exists (m⁺). split. apply ω_inductive... split.
      apply lt_both_side_suc in Hmk...
      exists (f ∪ ⎨<k, m>⎬). rewrite HC.
      apply bijection_add_point...
      * apply disjointI. intros [x [H1 H2]]. apply SingE in H2.
        subst x. apply BInterE in H1 as [_ H].
        eapply lt_not_refl; revgoals...
      * apply disjointI. intros [x [H1 H2]]. apply SingE in H2.
        subst m. eapply lt_not_refl; revgoals...
Qed.

(* 单射的定义域与该单射的像等势 *)
Lemma dom_of_injection_eqnum_img :
  ∀ F A, injective F → A ⊆ dom F → A ≈ F⟦A⟧.
Proof with eauto.
  intros F A Hi Hsub. exists (F ↾ A).
  split... apply restr_injective...
  split. apply restr_dom... destruct Hi... reflexivity.
Qed.

(* 有限集的子集是有限集 *)
Corollary sub_of_finite_is_finite : ∀ A B,
  A ⊆ B → finite B → finite A.
Proof with neauto.
  intros A B H1 [n [Hn [f [Hi [Hd Hr]]]]].
  rewrite <- Hd in H1. apply dom_of_injection_eqnum_img in H1...
  pose proof (img_included f A) as H2. rewrite Hr in H2.
  destruct (classic (f⟦A⟧ = n)) as [Heq|Hnq].
  - exists n. split... rewrite <- Heq...
  - assert (Hps: f⟦A⟧ ⊂ n) by (split; auto).
    apply sub_of_nat_is_finite in Hps as [m [Hm [Hmn Hqn]]]...
    exists m. split... eapply eqnum_tran...
Qed.
