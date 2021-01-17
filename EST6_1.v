(** Based on "Elements of Set Theory" Chapter 6 Part 1 **)
(** Coq coding by choukh, Aug 2020 **)

Require Export Setoid.
Require Export ZFC.lib.Natural.
Require Export ZFC.lib.FuncFacts.
Require Import ZFC.lib.WosetMin.
Import WosetMin.SimpleVer.

(*** EST第六章1：等势，康托定理，鸽笼原理，有限基数 ***)

(** 等势 **)
Definition equinumerous : set → set → Prop := λ A B,
  ∃ F, F: A ⟺ B.
Notation "A ≈ B" := ( equinumerous A B) (at level 70).
Notation "A ≉ B" := (¬equinumerous A B) (at level 70).

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

Add Relation set equinumerous
  reflexivity proved by eqnum_refl
  symmetry proved by eqnum_symm
  transitivity proved by eqnum_tran
  as eqnum_rel.

(* 集合与空集等势当且仅当它是空集 *)
Lemma eqnum_empty : ∀ A, A ≈ ∅ ↔ A = ∅.
Proof with auto.
  split. intros [f Hf]. apply bijection_to_empty in Hf...
  intros. subst A...
Qed.

(* 单集与壹等势 *)
Lemma eqnum_single_one : ∀ a, ⎨a⎬ ≈ 1.
Proof with auto.
  intros. set (Func ⎨a⎬ 1 (λ _, 0)) as F.
  exists F. apply meta_bijective.
  - intros _ _. apply suc_has_n.
  - intros x1 Hx1 x2 Hx2 Heq.
    apply SingE in Hx1. apply SingE in Hx2. subst...
  - intros y Hy. rewrite one in Hy. apply SingE in Hy.
    exists a. split...
Qed.

(* 配对与贰等势 *)
Lemma eqnum_pair_two : ∀ a b, a ≠ b → {a, b} ≈ 2.
Proof with eauto; try congruence.
  intros * Hnq. set (Func {a, b} 2 (λ x, match (ixm (x = a)) with
    | inl _ => 0
    | inr _ => 1
  end)) as F.
  assert (H1_2: 1 ∈ 2) by apply suc_has_n.
  assert (H0_2: 0 ∈ 2) by (apply suc_has_0; apply ω_inductive; nauto).
  exists F. apply meta_bijective.
  - intros x Hx. destruct (ixm (x = a))...
  - intros x1 Hx1 x2 Hx2 Heq.
    destruct (ixm (x1 = a)); destruct (ixm (x2 = a));
    apply PairE in Hx1 as []; apply PairE in Hx2 as []...
    exfalso; eapply suc_neq_0... exfalso; eapply suc_neq_0...
  - intros y Hy. rewrite two in Hy. apply PairE in Hy as [].
    exists a. split. apply PairI1. destruct (ixm (a = a))...
    exists b. split. apply PairI2. destruct (ixm (b = a))... rewrite one...
Qed.

(* 所有的单集等势 *)
Lemma eqnum_single : ∀ a b, ⎨a⎬ ≈ ⎨b⎬.
Proof. intros. repeat rewrite eqnum_single_one; auto. Qed.
Hint Immediate eqnum_single : core.

(* 集合与单集的笛卡尔积与原集合等势 *)
Lemma eqnum_cprod_single : ∀ A a, A ≈ A × ⎨a⎬.
Proof with auto.
  intros. set (Func A (A × ⎨ a ⎬) (λ x, <x, a>)) as F.
  exists F. apply meta_bijective.
  - intros x Hx. apply CProdI...
  - intros x1 Hx1 x2 Hx2 Heq.
    apply op_iff in Heq as []...
  - intros y Hy. apply CProdE1 in Hy as [b [Hb [c [Hc Heq]]]].
    apply SingE in Hc. subst. exists b. split...
Qed.

(* 笛卡尔积在等势意义下满足交换律 *)
Lemma eqnum_cprod_comm : ∀ A B, A × B ≈ B × A.
Proof with auto.
  intros. set (Func (A × B) (B × A) (λ x, <π2 x, π1 x>)) as F.
  exists F. apply meta_bijective.
  - intros x Hx.
    apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]].
    subst. zfcrewrite. apply CProdI...
  - intros x1 Hx1 x2 Hx2 Heq.
    apply CProdE1 in Hx1 as [a [Ha [b [Hb Hx1]]]].
    apply CProdE1 in Hx2 as [c [Hc [d [Hd Hx2]]]].
    subst. zfcrewrite.
    apply op_iff in Heq as []. congruence.
  - intros y Hy.
    apply CProdE1 in Hy as [a [Ha [c [Hc Hy]]]].
    exists <c, a>. split. apply CProdI... zfcrewrite.
Qed.

(* 笛卡尔积在等势意义下满足结合律 *)
Lemma eqnum_cprod_assoc : ∀ A B C, (A × B) × C ≈ A × (B × C).
Proof with auto.
  intros.
  set (Func ((A × B) × C) (A × (B × C)) (λ x,
    <π1 (π1 x), <π2 (π1 x), π2 x>>
  )) as F.
  exists F. apply meta_bijective.
  - intros x Hx.
    apply CProdE1 in Hx as [d [Hd [c [Hc H1]]]].
    apply CProdE1 in Hd as [a [Ha [b [Hb H2]]]].
    subst. zfcrewrite. apply CProdI... apply CProdI...
  - intros x1 Hx1 x2 Hx2 Heq.
    apply CProdE1 in Hx1 as [d1 [Hd1 [c1 [Hc1 H11]]]].
    apply CProdE1 in Hd1 as [a1 [Ha1 [b1 [Hb1 H12]]]].
    apply CProdE1 in Hx2 as [d2 [Hd2 [c2 [Hc2 H21]]]].
    apply CProdE1 in Hd2 as [a2 [Ha2 [b2 [Hb2 H22]]]].
    apply op_iff in Heq as [H1 H2].
    apply op_iff in H2 as [H2 H3]. subst. zfcrewrite.
  - intros y Hy.
    apply CProdE1 in Hy as [a [Ha [d [Hd H1]]]].
    apply CProdE1 in Hd as [b [Hb [c [Hc H2]]]].
    exists <a, b, c>. split. apply CProdI... apply CProdI... zfcrewrite.
Qed.

(* 任意集合的幂集与该集合到贰的所有函数的集合等势 *)
Lemma power_eqnum_func_to_2 : ∀ A, 𝒫 A ≈ A ⟶ 2.
Proof with neauto.
  intros.
  set (λ B, Func A 2 (λ x,
    match (ixm (x ∈ B)) with
      | inl _ => 1
      | inr _ => 0
    end
  )) as ℱ.
  set (Func (𝒫 A) (A ⟶ 2) (λ B, ℱ B)) as G.
  assert (H1_2: 1 ∈ 2) by apply suc_has_n.
  assert (H0_2: 0 ∈ 2) by (apply suc_has_0; apply ω_inductive; nauto).
  exists G. apply meta_bijective.
  - intros B HB. apply arrow_iff. split...
    apply func_is_func. split.
    + apply ExtAx. intros x. split; intros Hx.
      * apply domE in Hx as [y Hp]. apply SepE1 in Hp.
        apply CProdE2 in Hp as []...
      * destruct (classic (x ∈ B)). {
          eapply domI. apply SepI.
          - apply CProdI. apply Hx. apply H1_2.
          - zfcrewrite. destruct (ixm (x ∈ B))... exfalso...
        } {
          eapply domI. apply SepI.
          - apply CProdI. apply Hx. apply H0_2.
          - zfcrewrite. destruct (ixm (x ∈ B))... exfalso...
        }
    + intros x Hx. destruct (classic (x ∈ B)).
      * cut ((ℱ B)[x] = 1). congruence.
        apply func_ap... apply func_is_func.
        apply SepI. apply CProdI... zfcrewrite.
        destruct (ixm (x ∈ B))... exfalso...
      * cut ((ℱ B)[x] = 0). congruence.
        apply func_ap... apply func_is_func.
        apply SepI. apply CProdI... zfcrewrite.
        destruct (ixm (x ∈ B))... exfalso...
  - intros B1 H1 B2 H2 Heq.
    apply PowerAx in H1. apply PowerAx in H2.
    apply ExtAx. intros a. split; intros Hab.
    + assert (Hp: <a, 1> ∈ ℱ B1). {
        apply SepI. apply CProdI... apply H1... zfcrewrite.
        destruct (ixm (a ∈ B1))... exfalso...
      }
      rewrite Heq in Hp. apply SepE2 in Hp. zfcrewrite.
      destruct (ixm (a ∈ B2))... exfalso. eapply suc_neq_0...
    + assert (Hp: <a, 1> ∈ ℱ B2). {
        apply SepI. apply CProdI... apply H2... zfcrewrite.
        destruct (ixm (a ∈ B2))... exfalso...
      }
      rewrite <- Heq in Hp. apply SepE2 in Hp. zfcrewrite.
      destruct (ixm (a ∈ B1))... exfalso. eapply suc_neq_0...
  - intros y Hy. set {x ∊ A | λ x, y[x] = 1} as B.
    exists B. split. apply PowerAx. apply sep_sub.
    apply SepE in Hy as [Hy [Hfy [Hdy Hry]]]. apply PowerAx in Hy.
    apply ExtAx. intros x. split; intros Hxy.
    + apply SepE in Hxy as [Hx Heq].
      apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]].
      subst x. zfcrewrite. rewrite <- Hdy in Ha.
      destruct (ixm (a ∈ B)) as [H|H]; subst b.
      * apply SepE in H as [].
        rewrite <- H0. apply func_correct...
      * apply func_correct in Ha as Hap...
        apply ranI in Hap. apply Hry in Hap.
        rewrite two in Hap. apply TwoE in Hap as []... {
          rewrite pred, <- H0. apply func_correct...
        } {
          exfalso. apply H. apply SepI.
          rewrite <- Hdy... rewrite one...
        }
    + apply Hy in Hxy as Hxp. apply SepI...
      apply CProdE1 in Hxp as [a [Ha [b [Hb Hx]]]].
      subst x. zfcrewrite. destruct (ixm (a ∈ B)) as [H|H].
      * apply SepE2 in H as Hap. rewrite <- Hap.
        symmetry. apply func_ap...
      * rewrite two in Hb. apply TwoE in Hb as []...
        exfalso. subst b. rewrite <- one in Hxy.
        apply H. apply SepI... apply func_ap...
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
    intros f [_ [_ Hr]]. apply sub_antisym...
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
        eapply nat_irrefl...
      - apply SingE in Hy; subst. apply func_ap...
    }
    apply sub_antisym... intros p Hp.
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
  assert (Hfp: f[p] = k). {
    cut (f[p] ∈ k⁺). intros.
    - apply BUnionE in H as [|Hfp]. exfalso... apply SingE in Hfp...
    - eapply ap_ran... apply injection_is_func...
  }
  destruct Hf as [[Hf Hs] [Hd Hr]].
  assert (Hfk: f[k] ∈ k). {
    rewrite <- Hd in Hkd. apply func_correct in Hkd as Hpr...
    apply ranI in Hpr as Hyr. apply Hr in Hyr.
    apply BUnionE in Hyr as [|Hyr]... apply SingE in Hyr.
    exfalso. cut (k = p). intros. rewrite H in Hp.
    eapply nat_irrefl... eapply injectiveE... split...
  }
  destruct Hf' as [[Hf' _] [Hd' _]]. intros x Hx.
  destruct (classic (x = p)) as [Hxp|Hxp]; [|
  destruct (classic (x = k)) as [Hxk|Hxk]].
  - subst x. rewrite <- Hd' in Hpd.
    apply domE in Hpd as [y Hpr]. apply func_ap in Hpr as Hap...
    rewrite Heqf' in Hpr. apply SepE in Hpr as [_ Hpr]. zfcrewrite.
    destruct (ixm (p = p))...
  - subst x. exfalso. eapply nat_irrefl...
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
    exfalso. apply Hxp. eapply injectiveE... split...
Qed.

(* 任意自然数到自身的满射是单射 *)
Lemma surjection_between_same_nat_injective :
  ∀n ∈ ω, ∀ f, f: n ⟹ n → injective f.
Proof with eauto; try congruence.
  intros n Hn f [Hf [Hd Hr]].
  set (λ y, {n ∊ ω | λ n, f[n] = y}) as 𝒩.
  set (Func n n (λ y, (Min Lt)[𝒩 y])) as g.
  assert (Hg: g: n ⇒ n). {
    apply meta_maps_into.
    intros y Hy. rewrite <- Hr in Hy.
    apply ranE in Hy as [x Hp]. apply domI in Hp as Hx.
    rewrite Hd in Hx. apply func_ap in Hp...
    assert (Hxw: x ∈ ω). { eapply ω_trans... }
    assert (Hxn: x ∈ 𝒩 y). { apply SepI... }
    specialize (ω_min (𝒩 y)) as [Hm Hle].
    + exists x...
    + intros w Hw. apply SepE1 in Hw...
    + apply SepE in Hm as [Hm _].
      apply Hle in Hxn as [].
      * apply (nat_trans n Hn _ x)...
      * subst...
  }
  assert (Hfgy: ∀y ∈ n, f[g[y]] = y). {
    intros y Hy. unfold g.
    rewrite meta_func_ap...
    specialize (ω_min (𝒩 y)) as [H _]...
    - rewrite <- Hr in Hy. apply ranE in Hy as [x Hp].
      apply domI in Hp as Hx. apply func_ap in Hp...
      exists x. apply SepI... eapply ω_trans...
    - intros x Hx. apply SepE1 in Hx...
    - apply SepE2 in H...
  }
  assert (Hig: g: n ⇔ n). {
    destruct Hg as [Hfg [Hdg Hrg]]. split... split...
    intros y Hy. split. apply ranE in Hy...
    intros y1 y2 H1 H2.
    apply domI in H1 as Hy1. apply func_ap in H1...
    apply domI in H2 as Hy2. apply func_ap in H2...
    assert (f[g[y1]] = f[g[y2]])...
    rewrite Hfgy, Hfgy in H...
  }
  apply injection_between_same_nat_surjective in Hig as Hrg...
  destruct Hg as [Hfg [Hdg _]].
  split... intros y Hy. split. apply ranE in Hy...
  intros x1 x2 H1 H2.
  apply domI in H1 as Hx1. rewrite Hd, <- Hrg in Hx1.
  apply domI in H2 as Hx2. rewrite Hd, <- Hrg in Hx2.
  apply ranE in Hx1 as [y1 Hg1]. apply domI in Hg1 as Hy1.
  apply ranE in Hx2 as [y2 Hg2]. apply domI in Hg2 as Hy2.
  apply func_ap in H1... apply func_ap in Hg1...
  apply func_ap in H2... apply func_ap in Hg2...
  assert (f[g[y1]] = f[g[y2]])...
  rewrite Hfgy, Hfgy in H...
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

(* 单集是有限集 *)
Fact single_finite : ∀ a, finite ⎨a⎬.
Proof. exists 1. split. nauto. apply eqnum_single_one. Qed.
Hint Resolve single_finite : core.

(* 配对是有限集 *)
Fact pair_finite : ∀ a b, a ≠ b → finite {a, b}.
Proof. exists 2. split. nauto. apply eqnum_pair_two. apply H. Qed.

(* 自然数是有限集 *)
Fact nat_finite : ∀n ∈ ω, finite n.
Proof.
  intros n Hn. exists n. split. apply Hn. reflexivity.
Qed.

(* 无限集非空 *)
Fact infinite_set_nonempty : ∀ A, infinite A → ⦿ A.
Proof.
  intros A Hinf. apply EmptyNE.
  intros H. apply Hinf. subst. auto.
Qed.

(* 集合有限当且仅当其存在有限集与其等势 *)
Lemma set_finite_iff_eqnum_finite_set : ∀ A,
  finite A ↔ ∃ B, A ≈ B ∧ finite B.
Proof with auto.
  split. intros [n [Hn Hqn]]. exists n. split... apply nat_finite...
  intros [B [H1 [n [Hn H2]]]]. exists n. split... rewrite <- H2...
Qed.

(* 鸽笼原理推论：任意有限集都不与自身的真子集等势 *)
Corollary no_fin_set_eqnum_its_proper_subset : ∀ A B,
  finite A → B ⊂ A → A ≉ B.
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
    apply comp_nonempty in Hsub as [a Ha].
    apply CompE in Ha as [Ha Ha'].
    apply properSub_intro... exists (g[a]). split.
    - rewrite <- Hrg. eapply ranI.
      apply func_correct... rewrite Hdg...
    - intros Hga. apply ranE in Hga as [x Hp]. rewrite Heqh in Hp.
      apply compoE in Hp as [y [_ Hp]].
      apply compoE in Hp as [z [H1 H2]].
      apply domI in H2 as Hzd. apply func_ap in H2...
      apply injectiveE in H2; auto; [|rewrite Hdg]...
      clear Hzd. subst z. apply ranI in H1. rewrite Hrf in H1... 
  }
  apply (pigeonhole (ran h) n)... exists h. split...
Qed.

(* 与自身的真子集等势的集合是无限集 *)
Corollary infinite_if_eqnum_proper_sub : ∀ A B,
  B ⊂ A → A ≈ B → infinite A.
Proof.
  intros A B Hsub Heqn Hfin.
  eapply no_fin_set_eqnum_its_proper_subset; eauto.
Qed.

(* ω是无限集 *)
Corollary ω_infinite : infinite ω.
Proof with nauto.
  set (ω - ⎨0⎬) as B.
  assert (H0: 0 ∉ B). {
    intros H. apply SepE in H as [_ H]. apply H...
  }
  assert (Hsub: B ⊂ ω). {
    apply properSub_intro...
    intros n Hn. apply CompE in Hn as []...
    exists 0. split...
  }
  eapply infinite_if_eqnum_proper_sub. apply Hsub.
  destruct σ_maps_into as [Hf [Hd _]].
  exists σ. split; split...
  - split. apply ranE in H...
    intros x1 x2 H1 H2.
    apply ReplAx in H1 as [m [Hm H1]].
    apply ReplAx in H2 as [n [Hn H2]].
    apply op_iff in H1 as [];
    apply op_iff in H2 as []; subst.
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
Corollary fin_set_eqnum_unique_nat : ∀ A, finite A →
  ∃! n, n ∈ ω ∧ A ≈ n.
Proof with eauto.
  intros A Hfin. split...
  intros m n [Hm H1] [Hn H2].
  destruct (classic (m = n))... exfalso.
  rewrite H1 in H2.
  apply nat_connected in H as []...
  - apply lt_iff_psub in H... apply (no_fin_set_eqnum_its_proper_subset n m)...
    apply nat_finite... symmetry...
  - apply lt_iff_psub in H...
    apply (no_fin_set_eqnum_its_proper_subset m n)... apply nat_finite...
Qed.

(* 等势的自然数相等 *)
Corollary nat_eqnum_eq : ∀ m n ∈ ω, m ≈ n → m = n.
Proof with auto.
  intros m Hm n Hn Hqn.
  destruct (classic (m = n))... exfalso.
  apply nat_connected in H as []...
  - apply lt_iff_psub in H... apply (no_fin_set_eqnum_its_proper_subset n m)...
    apply nat_finite... symmetry...
  - apply lt_iff_psub in H...
    apply (no_fin_set_eqnum_its_proper_subset m n)... apply nat_finite...
Qed.

(* 有限基数 *)
Definition FinCard : set → set := λ A, ⋃{n ∊ ω | λ n, A ≈ n}.

(* 有限基数定义为与有限集自身等势的自然数 *)
Lemma fin_card_correct : ∀ A, finite A →
  ∃n ∈ ω, FinCard A = n ∧ A ≈ n.
Proof with auto.
  intros A Hfin. assert (Hfin' := Hfin).
  destruct Hfin' as [n [Hn H1]]. exists n. repeat split...
  apply ExtAx. split; intros Hx.
  - apply UnionAx in Hx as [m [Hm Hx]].
    apply SepE in Hm as [Hm H2].
    pose proof (fin_set_eqnum_unique_nat A) as [_ Hu]...
    cut (m = n). congruence. apply Hu; split...
  - apply UnionAx. exists n. split... apply SepI...
Qed.

(* 有限集与其基数等势 *)
Lemma fin_set_eqnum_its_card : ∀ A, finite A → A ≈ FinCard A.
Proof.
  intros A Hfin.
  apply fin_card_correct in Hfin as [n [_ [Hc Hqn]]].
  congruence.
Qed.

(* 两个有限集等势当且仅当它们的基数相等 *)
Lemma fin_sets_eqnum_iff_cards_eq : ∀ A B, finite A → finite B → 
  FinCard A = FinCard B ↔ A ≈ B.
Proof with auto.
  intros A B H1 H2.
  apply fin_card_correct in H1 as [m [Hm [H11 H12]]].
  apply fin_card_correct in H2 as [n [Hn [H21 H22]]].
  split; intros.
  - rewrite H12. symmetry. congruence.
  - cut (m ≈ n). intros Hqn.
    + apply nat_eqnum_eq in Hqn... congruence.
    + rewrite <- H12, <- H22...
Qed.

(* 自然数的基数与该自然数相等 *)
Lemma fin_card_n : ∀n ∈ ω, FinCard n = n.
Proof with auto.
  intros n Hn.
  apply ExtAx. split; intros Hx.
  - apply UnionAx in Hx as [m [Hm Hx]].
    apply SepE in Hm as [Hm Hqn].
    apply nat_eqnum_eq in Hqn... congruence.
  - apply UnionAx. exists n. split... apply SepI...
Qed.

(* 自然数的子集是有限集 *)
Lemma subset_of_ω_is_finite : ∀n ∈ ω, ∀ C,
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
        intros H. rewrite binter_comm, <- ex2_17_1_4 in H.
        apply Hnq. apply ExtAx. split; intros Hx.
        - apply Hsub in Hx...
        - apply BUnionE in Hx as []. apply H in H0...
          apply SingE in H0. subst...
      }
      apply IH in Hps as [m [Hmw [Hmk [f Hf]]]].
      exists (m⁺). split. apply ω_inductive... split.
      apply suc_preserve_lt in Hmk...
      exists (f ∪ ⎨<k, m>⎬). rewrite HC.
      apply bijection_add_point...
      * apply disjointI. intros [x [H1 H2]]. apply SingE in H2.
        subst x. apply BInterE in H1 as [_ H].
        eapply nat_irrefl; revgoals...
      * apply disjointI. intros [x [H1 H2]]. apply SingE in H2.
        subst m. eapply nat_irrefl...
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
Corollary subset_of_finite_is_finite : ∀ A B,
  A ⊆ B → finite B → finite A.
Proof with neauto.
  intros A B H1 [n [Hn [f [Hi [Hd Hr]]]]].
  rewrite <- Hd in H1. apply dom_of_injection_eqnum_img in H1...
  pose proof (img_included f A) as H2. rewrite Hr in H2.
  destruct (classic (f⟦A⟧ = n)) as [Heq|Hnq].
  - exists n. split... rewrite <- Heq...
  - assert (Hps: f⟦A⟧ ⊂ n) by (split; auto).
    apply subset_of_ω_is_finite in Hps as [m [Hm [Hmn Hqn]]]...
    exists m. split... rewrite H1...
Qed.

(* 无限集的父集是无限集 *)
Corollary parent_set_of_infinite_is_infinite : ∀ A B,
  A ⊆ B → infinite A → infinite B.
Proof.
  intros * Hsub Hinf Hfin. apply Hinf.
  eapply subset_of_finite_is_finite; eauto.
Qed.

Lemma cprod_disjoint_l : ∀ A B C D,
  disjoint A C → disjoint (A × B) (C × D).
Proof.
  intros * Hdj. apply disjointI. intros [x [H1 H2]].
  apply CProdE1 in H1 as [a [Ha [b [Hb Hx]]]]. subst x.
  apply CProdE2 in H2 as [Ha' _].
  eapply disjointE; eauto.
Qed.

Lemma cprod_disjoint_r : ∀ A B C D,
  disjoint B D → disjoint (A × B) (C × D).
Proof.
  intros * Hdj. apply disjointI. intros [x [H1 H2]].
  apply CProdE1 in H1 as [a [Ha [b [Hb Hx]]]]. subst x.
  apply CProdE2 in H2 as [_ Hb'].
  eapply disjointE; eauto.
Qed.

(* 不交化：通过笛卡尔积构造出分别与原集合等势但不交的两个集合 *)
Lemma cprod_disjointify : ∀ A B m n,
  m ≠ n → disjoint (A × ⎨m⎬) (B × ⎨n⎬).
Proof.
  intros. apply cprod_disjoint_r.
  apply disjointI. intros [x [H1 H2]].
  apply SingE in H1. apply SingE in H2. congruence.
Qed.

Corollary disjointify_0_1 : ∀ A B, disjoint (A × ⎨0⎬) (B × ⎨1⎬).
Proof.
  intros. apply cprod_disjointify. intro. eapply suc_neq_0. eauto.
Qed.

(* 任意自然数与自身的单集不交 *)
Lemma nat_disjoint : ∀n ∈ ω, disjoint n ⎨n⎬.
Proof.
  intros n Hn. apply disjointI. intros [x [H1 H2]].
  apply SingE in H2. subst. eapply nat_irrefl; eauto.
Qed.

(* 等势的集合分别除去一个元素仍然等势 *)
Lemma eqnum_sets_removing_one_element_still_eqnum :
  ∀ A B a b, A ∪ ⎨a⎬ ≈ B ∪ ⎨b⎬ →
  disjoint A ⎨a⎬ → disjoint B ⎨b⎬ → A ≈ B.
Proof with eauto; try congruence.
  intros * [f Hf] Hdja Hdjb. assert (Hf' := Hf).
  destruct Hf' as [Hi [Hd Hr]].
  set (FuncSwapValue f a f⁻¹[b]) as g.
  assert (Ha: a ∈ A ∪ ⎨a⎬) by (apply BUnionI2; auto).
  assert (Hbr: b ∈ ran f). { rewrite Hr. apply BUnionI2... }
  assert (Hb: f⁻¹[b] ∈ A ∪ ⎨a⎬). {
    destruct Hi as [Hff Hs].
    rewrite <- Hd, <- inv_ran. eapply ap_ran. split...
    apply inv_func_iff_sr... rewrite inv_dom...
  }
  apply (bijection_swap_value _ _ _ _ Ha _ Hb) in Hf as Hg.
  assert (Hga: g[a] = b). {
    apply func_ap... destruct Hg as [[Hg _] _]...
    apply SepI. apply CProdI... zfcrewrite.
    destruct (ixm (a = a))... rewrite inv_ran_reduction... 
  }
  clear Hf Hi Hd Hr Ha Hbr Hb.
  destruct Hg as [Hi [Hd Hr]]. assert (Hi' := Hi).
  destruct Hi as [Hg Hs].
  exists (g ↾ A). split; [|split].
  - apply restr_injective...
  - apply restr_dom... intros x Hx. subst g.
    rewrite Hd. apply BUnionI1...
  - apply ExtAx. intros y. split; intros Hy.
    + apply ranE in Hy as [x Hp].
      apply restrE2 in Hp as [Hp Hx].
      apply ranI in Hp as Hy. subst g. rewrite Hr in Hy.
      apply BUnionE in Hy as []...
      apply SingE in H. subst y. apply func_ap in Hp...
      rewrite <- Hp in Hga. cut (a = x).
      * intros H. subst x. exfalso. eapply disjointE.
        apply Hdja. apply Hx. apply SingI.
      * eapply injectiveE...
        rewrite Hd. apply BUnionI2...
        rewrite Hd. apply BUnionI1...
    + assert (y ∈ ran g). { subst g. rewrite Hr. apply BUnionI1... }
      apply ranE in H as [x Hp]. apply domI in Hp as Hx.
      subst g. rewrite Hd in Hx. apply BUnionE in Hx as [].
      * eapply ranI. apply restrI...
      * apply SingE in H. subst x. apply func_ap in Hp...
        rewrite <- Hp, Hga in Hy. exfalso. eapply disjointE.
        apply Hdjb. apply Hy. apply SingI.
Qed.

(* 从有限集中取出一个元素则基数减1 *)
Corollary finite_set_remove_one_element : ∀ A a, ∀n ∈ ω,
  (A - ⎨a⎬) ∪ ⎨a⎬ ≈ n⁺ → A - ⎨a⎬ ≈ n.
Proof with eauto.
  intros * n Hn Hqn.
  eapply eqnum_sets_removing_one_element_still_eqnum...
  apply disjointI. intros [x [H1 H2]]. apply SepE2 in H1...
  apply nat_disjoint...
Qed.
