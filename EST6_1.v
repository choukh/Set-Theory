(** Based on "Elements of Set Theory" Chapter 1 Part 1 **)
(** Coq coding by choukh, Aug 2020 **)

Require Export ZFC.EST5_7.

Close Scope Real_scope.
Open Scope ZFC_scope.

(*** EST第六章1：等势 ***)

(* 集合的经典逻辑引理 *)

Lemma set_not_all_not_ex : ∀ X P, ¬(∀x ∈ X, ¬P x) ↔ (∃x ∈ X, P x).
Proof.
  split; intros.
  - destruct (classic (∃x ∈ X, P x)); firstorder.
  - firstorder.
Qed.

Lemma set_not_all_ex_not : ∀ X P, ¬(∀x ∈ X, P x) ↔ (∃x ∈ X, ¬P x).
Proof.
  intros. pose proof (set_not_all_not_ex X (λ x, ¬P x)).
  simpl in H. rewrite <- H. clear H.
  split; intros.
  - intros H1. apply H. intros x Hx. apply H1 in Hx.
    rewrite double_negation in Hx. apply Hx.
  - firstorder.
Qed.

(** 等势 **)
Definition equinumerous : set → set → Prop := λ A B,
  ∃ F, F: A ⟺ B.
Notation "A ≈ B" := ( equinumerous A B) (at level 99).
Notation "A ≉ B" := (¬equinumerous A B) (at level 99).

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

Lemma eqnum_refl : ∀ A, A ≈ A.
Proof.
  intros. exists (Ident A).
  apply ident_bijective.
Qed.

Lemma eqnum_symm : ∀ A B, A ≈ B → B ≈ A.
Proof.
  intros * [f H]. exists (f⁻¹).
  apply inv_bijection. auto.
Qed.

Lemma eqnum_tran : ∀ A B C, A ≈ B → B ≈ C → A ≈ C.
Proof.
  intros * [f Hf] [g Hg]. exists (g ∘ f).
  eapply compo_bijection; eauto.
Qed.

(* 康托定理 *)
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

Lemma restr_on_single : ∀ F a, is_function F →
  a ∈ dom F → ran (F ↾ ⎨a⎬) = ⎨F[a]⎬.
Proof with auto.
  intros * Hf Ha. apply ExtAx. intros y. split; intros Hy.
  - apply ranE in Hy as [x Hp].
    apply restrE in Hp as [b [c [Hb [Hp Heq]]]].
    apply op_correct in Heq as []; subst.
    apply SingE in Hb; subst.
    apply func_ap in Hp... subst. apply SingI.
  - apply SingE in Hy; subst. eapply ranI.
    apply restrI. apply SingI. apply func_correct...
Qed.

Lemma restr_ran_bunion : ∀ F A B, dom F = A ∪ B →
  ran F = ran (F ↾ A) ∪ ran (F ↾ B).
Proof with eauto.
  intros. apply ExtAx. intros y. split; intros Hy.
  - apply ranE in Hy as [x Hp]. apply domI in Hp as Hd.
    rewrite H in Hd. apply BUnionE in Hd as [].
    + apply BUnionI1. eapply ranI. apply restrI...
    + apply BUnionI2. eapply ranI. apply restrI...
  - apply BUnionE in Hy as [Hy|Hy].
    + apply ranE in Hy as [x Hp].
      apply restrE in Hp as [b [c [Hb [Hp Heq]]]].
      apply op_correct in Heq as []; subst. eapply ranI...
    + apply ranE in Hy as [x Hp].
      apply restrE in Hp as [b [c [Hb [Hp Heq]]]].
      apply op_correct in Heq as []; subst. eapply ranI...
Qed.

(* 鸽笼原理 *)
Lemma pigeonhole_0 : ∀n ∈ ω, ∀ f, f: n ⇔ n → ran f = n.
Proof with neauto; try congruence.
  intros n Hn.
  set {n ∊ ω | λ n, ∀ f, f: n ⇔ n → ran f = n} as T.
  ω_induction T Hn. {
    intros f [_ [_ Hr]]. apply sub_asym...
    intros x Hx. exfalso0.
  }
  rename m into k.
  assert (Hstar: ∀ f, f: k⁺ ⇔ k⁺ → (∀p ∈ k, f[p] ∈ k) → ran f = k⁺). {
    intros f [[Hf Hs] [Hd Hr]] H.
    assert (Hres: f ↾ k: k ⇔ k⁺). {
      split. apply restr_injective... split... split.
      - apply restr_dom... rewrite Hd...
      - eapply sub_tran. apply restr_ran_included. apply Hr.
    }
    assert (Hr': ran (f ↾ k) = k). {
      destruct Hres as [Hri [Hrd Hrr]]. apply IH.
      split. apply restr_injective... split... split...
      intros y Hy. apply ranE in Hy as [x Hp].
      apply restrE in Hp as [a [b [Ha [Hp Heq]]]].
      apply op_correct in Heq as []; subst.
      apply func_ap in Hp... subst. apply H...
    }
    assert (Hkd: k ∈ dom f) by (rewrite Hd; nauto).
    assert (Hfk: f[k] = k). {
      apply domE in Hkd as [y Hp]. apply ranI in Hp as Hy.
      apply Hr in Hy. apply BUnionE in Hy as [Hy|Hy].
      - rewrite <- Hr' in Hy. apply ranE in Hy as [x Hp'].
        apply restrE in Hp' as [a [b [Ha [Hp' Heq]]]].
        apply op_correct in Heq as []; subst.
        exfalso. eapply singrE in Hp... subst.
        eapply lt_not_refl; revgoals...
      - apply SingE in Hy; subst. apply func_ap...
    }
    apply sub_asym... intros p Hp.
    rewrite (restr_ran_bunion _ _ _ Hd).
    apply BUnionE in Hp as [].
    + apply BUnionI1. rewrite Hr'...
    + apply BUnionI2. rewrite restr_on_single, Hfk...
  }
  clear Hn T n IH. intros f Hf.
  destruct (classic (∀p ∈ k, f[p] ∈ k)). { apply Hstar... }
  rewrite set_not_all_ex_not in H. destruct H as [p [Hp Hout]].
  assert (Hpw: p ∈ ω) by (eapply ω_trans; eauto).
  destruct Hf as [[Hf Hs] [Hd Hr]].
  assert (Hfp: f[p] ∈ k⁺). {
    apply Hr. eapply ranI. apply func_correct...
    rewrite Hd. apply BUnionI1...
  }
  apply BUnionE in Hfp as [|Hfp]. exfalso... apply SingE in Hfp.
  assert (Hkd: k ∈ dom f) by (rewrite Hd; nauto).
  assert (Hpd: p ∈ dom f) by (rewrite Hd; apply BUnionI1; nauto).
  assert (Hfk: f[k] ∈ k). {
    assert (Hkd' := Hkd).
    apply domE in Hkd' as [y Hpr]. apply ranI in Hpr as Hfk.
    apply func_ap in Hpr... subst y. apply Hr in Hfk.
    apply BUnionE in Hfk as [|Hfk]... apply SingE in Hfk.
    exfalso. cut (k = p). intros. rewrite H in Hp.
    eapply lt_not_refl; revgoals...
    eapply func_injective... split...
  }
  set (Relation (dom f) (ran f) (λ x y,
    y = match (ixm (x = p)) with
    | inl _ => f[k]
    | inr _ =>
      match (ixm (x = k)) with
      | inl _ => f[p]
      | inr _ => f[x]
      end
    end
  )) as f'.
  assert (Hf': is_function f'). {
    repeat split. apply rel_is_rel. apply domE in H...
    intros y1 y2 H1 H2.
    apply SepE in H1 as [_ H1].
    apply SepE in H2 as [_ H2]. zfcrewrite.
  }
  assert (Hdeq: dom f' = dom f). {
    apply ExtAx. intros x. split; intros Hx.
    - apply domE in Hx as [Hy Hpr].
      apply SepE in Hpr as [Hpr _].
      apply CProdE1 in Hpr as [Hx _]. zfcrewrite.
    - destruct (classic (x = p)) as [Hxp|Hxp]; [|
      destruct (classic (x = k)) as [Hxk|Hxk]].
      + apply domE in Hkd as [y Hpr].
        apply ranI in Hpr as Hy. apply func_ap in Hpr...
        eapply domI. apply SepI. apply CProdI; auto.
        apply Hy. zfcrewrite.
        destruct (ixm (x = p)) as [H1|H1]...
      + apply domE in Hpd as [y Hpr].
        apply ranI in Hpr as Hy. apply func_ap in Hpr...
        eapply domI. apply SepI. apply CProdI; auto.
        apply Hy. zfcrewrite.
        destruct (ixm (x = p)) as [H1|H1]...
        destruct (ixm (x = k)) as [H2|H2]...
      + assert (Hx' := Hx). apply domE in Hx as [y Hpr].
        apply ranI in Hpr as Hy. apply func_ap in Hpr...
        eapply domI. apply SepI. apply CProdI... zfcrewrite.
        destruct (ixm (x = p)) as [H1|H1]...
        destruct (ixm (x = k)) as [H2|H2]...
  }
  assert (Hreq: ran f' = ran f). {
    apply ExtAx. intros y. split; intros Hy.
    - apply ranE in Hy as [x Hpr].
      apply SepE in Hpr as [Hpr _].
      apply CProdE1 in Hpr as [_ Hy]. zfcrewrite.
    - assert (Hy' := Hy). apply ranE in Hy' as [x Hpr].
      apply domI in Hpr as Hx. apply func_ap in Hpr...
      destruct (classic (x = p)) as [Hxp|Hxp]; [|
      destruct (classic (x = k)) as [Hxk|Hxk]]; eapply ranI.
      + apply SepI. apply CProdI; auto. rewrite Hd.
        apply suc_has_n. zfcrewrite.
        destruct (ixm (k = p)) as [H1|H1]...
        destruct (ixm (k = k)) as [H2|H2]...
      + apply SepI. apply CProdI; auto. rewrite Hd.
        apply BUnionI1. apply Hp. zfcrewrite.
        destruct (ixm (p = p)) as [H1|H1]...
      + apply SepI. apply CProdI; auto. rewrite Hd.
        rewrite <- Hd... zfcrewrite.
        destruct (ixm (x = p)) as [H1|H1]...
        destruct (ixm (x = k)) as [H2|H2]...
  }
  rewrite <- Hreq. apply Hstar. clear Hstar. split; split...
  - split. apply ranE in H...
    intros x1 x2 H1 H2.
    apply SepE in H1 as [H11 H12]. apply CProdE1 in H11 as [].
    apply SepE in H2 as [H21 H22]. apply CProdE1 in H21 as []. zfcrewrite.
    destruct (ixm (x1 = p)); destruct (ixm (x2 = p));
    destruct (ixm (x1 = k)); destruct (ixm (x2 = k))...
    + exfalso. apply n1. eapply func_injective... split...
    + exfalso. apply n0. eapply func_injective... split...
    + exfalso. apply n0. eapply func_injective... split...
    + exfalso. apply n. eapply func_injective... split...
    + eapply func_injective... split...
  - rewrite Hreq...
  - intros x Hx.
    destruct (classic (x = p)) as [Hxp|Hxp]; [|
    destruct (classic (x = k)) as [Hxk|Hxk]].
    + subst x. rewrite <- Hdeq in Hpd.
      apply domE in Hpd as [y Hpr]. apply func_ap in Hpr as Hap...
      apply SepE in Hpr as [_ Hpr]. zfcrewrite.
      destruct (ixm (p = p))...
    + subst x. exfalso. eapply lt_not_refl...
    + assert (Hxd: x ∈ dom f) by (rewrite Hd; apply BUnionI1; auto).
      assert (Hxd': x ∈ dom f') by (rewrite Hdeq; auto).
      apply domE in Hxd' as [y Hpr]. apply func_ap in Hpr as Hap...
      apply SepE in Hpr as [_ Hpr]. zfcrewrite.
      destruct (ixm (x = p))... destruct (ixm (x = k))...
      subst y. rewrite Hap. clear Hap n n0 Hx Hxk Hreq Hdeq.
      assert (Hxd' := Hxd).
      apply domE in Hxd' as [y Hpr]. apply ranI in Hpr as Hy.
      apply func_ap in Hpr... subst y. apply Hr in Hy.
      apply BUnionE in Hy as []... apply SingE in H.
      exfalso. apply Hxp. eapply func_injective... split...
Qed.

Theorem pigeonhole : ∀ k n ∈ ω, k ⊂ n → n ≉ k.
Proof with eauto.
  intros k Hk n Hn [Hsub Hnq] [f [[Hf Hs] [Hd Hr]]].
  apply Hnq. rewrite <- Hr. eapply pigeonhole_0...
  split; split... rewrite Hr...
Qed.





















(* Definition finite : set → Prop := λ A, ∃n ∈ ω, A ≈ n. *)
