(** Based on "Elements of Set Theory" Chapter 6 Part 4 EX 2 **)
(** Coq coding by choukh, Sep 2020 **)

Require Export ZFC.EST6_4.

(*** EST第六章4扩展2：基数的无限累加和，基数的无限累乘积 ***)

(* 基数的无限累加和 *)
Definition CardInfSum : set → set → set := λ I X,
  |⋃{λ i, X[i] × ⎨i⎬ | i ∊ I}|.
Notation "∑" := (CardInfSum) : Card_scope.

(* 基数的无限累乘积 *)
Definition CardInfProd : set → set → set := λ I X,
  |InfCProd I X|.
Notation "∏" := (CardInfProd) : Card_scope.

(* 函数不交化：给定任意函数和单集，可以构造一个新的函数，使得
  (1) 新函数的定义域是原函数的定义域与给定单集的笛卡尔积 且
  (2) 新函数的值域是原函数的值域与给定单集的笛卡尔积 *)
Definition FuncDisjointify : set → set → set := λ i F,
  Func (dom F × ⎨i⎬) (ran F × ⎨i⎬) (λ x, <F[π1 x], i>).

Lemma bijection_disjointify : ∀ F i, injective F →
  (FuncDisjointify i F): dom F × ⎨i⎬ ⟺ ran F × ⎨i⎬.
Proof with eauto; try congruence.
  intros. apply meta_bijective.
  - intros x Hx. apply CProdI... eapply ap_ran.
    split. destruct H... split... apply CProdE1 in Hx as [H1 _]...
  - intros p1 Hp1 p2 Hp2 Heq.
    apply cprod_iff in Hp1 as [a [Ha [b [Hb H1]]]].
    apply cprod_iff in Hp2 as [c [Hc [d [Hd H2]]]].
    apply SingE in Hb. apply SingE in Hd. subst. zfcrewrite.
    apply op_iff in Heq as [Heq _]. apply op_iff.
    split... eapply injectiveE...
  - intros y Hy. destruct H as [Hf _].
    apply cprod_iff in Hy as [a [Ha [b [Hb Hy]]]].
    apply ranE in Ha as [x Hp].
    apply domI in Hp as Hx. apply func_ap in Hp as Hap...
    exists <x, b>. split. apply CProdI... subst y. zfcrewrite.
    apply op_iff. apply SingE in Hb. split...
Qed.

(* 不交化后的函数相等则原函数相等 *)
Lemma funcDisjointify_injective : ∀ i f g,
  is_function f → is_function g →
  FuncDisjointify i f = FuncDisjointify i g → f = g.
Proof with eauto.
  cut (∀ i f g, is_function f → is_function g →
      FuncDisjointify i f = FuncDisjointify i g → f ⊆ g). {
    intros H * Hf Hg Heq. apply sub_asym; eapply H...
  }
  intros * Hf Hg Heq p Hpf.
  apply func_pair in Hpf as Heqp... rewrite Heqp in Hpf.
  apply domI in Hpf as Hdf. apply ranI in Hpf as Hrf.
  assert (<<π1 p, i>, <π2 p, i>> ∈ FuncDisjointify i f). {
    apply SepI. apply CProdI; apply CProdI... zfcrewrite.
    apply op_iff. split... symmetry. apply func_ap...
  }
  rewrite Heq in H. apply SepE in H as [Hpg Hap].
  apply CProdE1 in Hpg as [Hdg Hrg].
  apply CProdE1 in Hdg as [Hdg _].
  apply CProdE1 in Hrg as [Hrg _]. zfcrewrite.
  apply op_iff in Hap as [Hap _]. symmetry in Hap.
  rewrite Heqp. apply func_point...
Qed.

(* ==需要选择公理== *)
(* 基数的无限累加和良定义 *)
Theorem cardInfSum_well_defined : AC_III' → ∀ I A B,
  (∀i ∈ I, |A[i]| = |B[i]|) → ∑ I A = ∑ I B.
Proof with eauto; try congruence.
  intros AC3' * Heqcd. unfold AC_III' in AC3'.
  set (λ i, {f ∊ A[i] ⟶ B[i] | λ f, f: A[i] ⟺ B[i]}) as F_.
  set (λ i, {FuncDisjointify i | f ∊ F_ i}) as F'_.
  set {F'_ | i ∊ I} as ℱ.
  specialize AC3' with ℱ as [g [Hfg [Hdg Hrg]]]. {
    intros x Hx. apply ReplAx in Hx as [i [Hi HFi]]. subst x.
    apply Heqcd in Hi. apply CardAx1 in Hi as [f Hf].
    exists (FuncDisjointify i f). apply ReplAx.
    exists f. split... apply SepI... apply ArrowI.
    apply bijection_is_func...
  }
  set {λ F, g[F] | F ∊ ℱ} as G.
  assert (HpUG: ∀p ∈ ⋃G, ∃i ∈ I, p ∈ g[F'_ i]). {
    intros p Hp. apply UnionAx in Hp as [f [Hf Hp]].
    apply ReplAx in Hf as [F [HF Heqf]].
    apply ReplAx in HF as [i [Hi HeqF]].
    subst F f. exists i. split...
  }
  assert (HgF: ∀i ∈ I, ∃ f, f: A[i] ⟺ B[i] ∧ g[F'_ i] = FuncDisjointify i f). {
    intros i Hi.
    assert (HFi: F'_ i ∈ ℱ). { apply ReplAx. exists i. split... }
    apply Hrg in HFi. apply ReplAx in HFi as [f [Hf Heq]].
    apply SepE in Hf as [_ Hf]. exists f. split...
  }
  apply CardAx1. exists (⋃ G). split; split.
  - repeat split.
    + intros p Hp. apply HpUG in Hp as [i [Hi Hp]].
      apply HgF in Hi as [f [Hf Heq]]. rewrite Heq in Hp.
      apply SepE in Hp as [Hp _]. apply CProdE2 in Hp...
    + apply domE in H...
    + intros y1 y2 H1 H2.
      apply HpUG in H1 as [i1 [Hi1 Hp1]].
      apply HpUG in H2 as [i2 [Hi2 Hp2]].
      apply HgF in Hi1 as [f1 [Hf1 Heq1]]. rewrite Heq1 in Hp1.
      apply HgF in Hi2 as [f2 [Hf2 Heq2]]. rewrite Heq2 in Hp2.
      apply SepE in Hp1 as [Hp1 H1]. apply CProdE1 in Hp1 as [Hx1 _].
      apply SepE in Hp2 as [Hp2 H2]. apply CProdE1 in Hp2 as [Hx2 _].
      zfcrewrite. destruct (classic (i1 = i2)). {
        cut (f1 = f2). { intros Heqf. subst. apply op_iff... }
        apply (funcDisjointify_injective i1)...
        destruct Hf1 as [[]]... destruct Hf2 as [[]]...
      }
      exfalso. eapply disjointE; revgoals.
      apply Hx1. apply Hx2. apply disjoint_cprod...
  - intros y Hy. split. apply ranE in Hy...
    intros x1 x2 H1 H2.
    apply HpUG in H1 as [i1 [Hi1 Hp1]].
    apply HpUG in H2 as [i2 [Hi2 Hp2]].
    apply HgF in Hi1 as [f1 [Hf1 Heq1]]. rewrite Heq1 in Hp1.
    apply HgF in Hi2 as [f2 [Hf2 Heq2]]. rewrite Heq2 in Hp2.
    apply SepE in Hp1 as [Hp1 H1]. apply CProdE1 in Hp1 as [Hx1 Hy1].
    apply SepE in Hp2 as [Hp2 H2]. apply CProdE1 in Hp2 as [Hx2 Hy2].
    apply cprod_iff in Hx1 as [a [Ha [b [Hb Hx1]]]].
    apply cprod_iff in Hx2 as [c [Hc [d [Hd Hx2]]]].
    apply SingE in Hb. apply SingE in Hd. zfcrewrite. subst x1 x2.
    zfcrewrite. destruct (classic (i1 = i2)). {
      cut (f1 = f2). {
        intros Heqf. subst. apply op_iff in H2 as [Hap Hi].
        apply op_iff. split... eapply injectiveE... destruct Hf2...
      }
      apply (funcDisjointify_injective i1)...
      destruct Hf1 as [[]]... destruct Hf2 as [[]]...
    }
    exfalso. eapply disjointE; revgoals.
    apply Hy1. apply Hy2. apply disjoint_cprod...
  - apply ExtAx. split; intros Hx.
    + apply domE in Hx as [y Hp].
      apply HpUG in Hp as [i [Hi Hp]].
      apply UnionAx. exists (A[i] × ⎨i⎬). split...
      apply ReplAx. exists i. split...
      apply HgF in Hi as [f [Hf Heq]]. rewrite Heq in Hp.
      apply SepE in Hp as [Hp _]. apply CProdE1 in Hp as [Hx _].
      zfcrewrite. destruct Hf as [_ [Hdf _]]...
    + apply UnionAx in Hx as [X [HX Hx]].
      apply ReplAx in HX as [i [Hi Heq]]. subst X.
      apply cprod_iff in Hx as [a [Ha [b [Hb Heq]]]].
      apply SingE in Hb. subst.
      cut (<<a, i>, g[F'_ i][<a, i>]> ∈ ⋃G). { eapply domI... }
      apply UnionAx. exists (g[F'_ i]). split.
      apply ReplAx. exists (F'_ i). split...
      apply ReplAx. exists i. split...
      apply HgF in Hi as [f [Hf Heq]]. rewrite Heq.
      destruct Hf as [Hif [Hdf _]].
      pose proof (bijection_disjointify f i) as [[Hfd _] [Hdd _]]...
      apply func_correct... rewrite Hdd. apply CProdI...
  - apply ExtAx. intros y. split; intros Hy.
    + apply ranE in Hy as [x Hp].
      apply HpUG in Hp as [i [Hi Hp]].
      apply UnionAx. exists (B[i] × ⎨i⎬). split...
      apply ReplAx. exists i. split...
      apply HgF in Hi as [f [Hf Heq]]. rewrite Heq in Hp.
      apply SepE in Hp as [Hp _]. apply CProdE1 in Hp as [_ Hy].
      zfcrewrite. destruct Hf as [_ [_ Hrf]]...
    + apply UnionAx in Hy as [Y [HY Hy]].
      apply ReplAx in HY as [i [Hi Heq]]. subst Y.
      apply cprod_iff in Hy as [a [Ha [b [Hb Heq]]]].
      apply SingE in Hb. subst.
      cut (<g[F'_ i]⁻¹[<a, i>], <a, i>> ∈ ⋃G). { eapply ranI... }
      apply UnionAx. exists (g[F'_ i]). split.
      apply ReplAx. exists (F'_ i). split...
      apply ReplAx. exists i. split...
      apply HgF in Hi as [f [Hf Heq]]. rewrite Heq.
      destruct Hf as [Hif [_ Hrf]].
      pose proof (bijection_disjointify f i) as [[Hfd Hsd] [_ Hrd]]...
      rewrite inv_op. apply func_correct. apply inv_func_iff_sr...
      rewrite inv_dom. rewrite Hrd. apply CProdI...
Qed.

(* ==需要选择公理== *)
(* 基数的无限累乘积良定义 *)
Theorem cardInfProd_well_defined : AC_III' → ∀ I A B,
  (∀i ∈ I, |A[i]| = |B[i]|) → ∏ I A = ∏ I B.
Proof with eauto; try congruence.
  intros AC3' * Heqcd. unfold AC_III' in AC3'.
  set (λ i, {f ∊ A[i] ⟶ B[i] | λ f, f: A[i] ⟺ B[i]}) as F_.
  set {F_ | i ∊ I} as ℱ.
  specialize AC3' with ℱ as [g [Hfg [Hdg Hrg]]]. {
    intros x Hx. apply ReplAx in Hx as [i [Hi HFi]]. subst x.
    apply Heqcd in Hi. apply CardAx1 in Hi as [f Hf].
    exists f. apply SepI... apply ArrowI. apply bijection_is_func...
  }
  set (⋃{ap B | i ∊ I}) as ℬ.
  set (⋃{ap A | i ∊ I}) as 𝒜.
  set (λ x, Func I ℬ (λ i, g[F_ i][x[i]])) as G.
  set (λ y, Func I 𝒜 (λ i, g[F_ i]⁻¹[y[i]])) as G'.
  assert (HFi: ∀i ∈ I, F_ i ∈ ℱ). {
    intros i Hi. apply ReplAx. exists i. split...
  }
  assert (HgF: ∀i ∈ I, g[F_ i]: A[i] ⟺ B[i]). {
    intros i Hi. apply HFi in Hi.
    apply Hrg in Hi. apply SepE in Hi as [_ HgF]...
  }
  assert (HgFx: ∀i ∈ I, ∀x ∈ InfCProd I A, g[F_ i][x[i]] ∈ B[i]). {
    intros i Hi x Hx. eapply ap_ran. apply bijection_is_func...
    apply HgF... eapply InfCProdE...
  }
  assert (HgFy: ∀i ∈ I, ∀y ∈ InfCProd I B, g[F_ i]⁻¹[y[i]] ∈ A[i]). {
    intros i Hi x Hx. eapply ap_ran. apply bijection_is_func...
    apply inv_bijection. apply HgF... eapply InfCProdE...
  }
  assert (HBi: ∀i ∈ I, B[i] ⊆ ℬ). {
    intros i Hi b Hb. apply UnionAx. exists (B[i]). split...
    apply ReplAx. exists i. split...
  }
  assert (HgFx': ∀i ∈ I, ∀x ∈ InfCProd I A, g[F_ i][x[i]] ∈ ℬ). {
    intros i Hi x Hx. eapply HBi... apply HgFx...
  }
  assert (HG: ∀x ∈ InfCProd I A, G x: I ⇒ ℬ). {
    intros x Hx. apply meta_maps_into. intros i Hi.
    eapply HBi... apply HgFx...
  }
  assert (HAi: ∀i ∈ I, A[i] ⊆ 𝒜). {
    intros i Hi a Ha. apply UnionAx. exists (A[i]). split...
    apply ReplAx. exists i. split...
  }
  assert (HgFy': ∀i ∈ I, ∀y ∈ InfCProd I B, g[F_ i]⁻¹[y[i]] ∈ 𝒜). {
    intros i Hi x Hx. eapply HAi... apply HgFy...
  }
  assert (HG': ∀y ∈ InfCProd I B, G' y: I ⇒ 𝒜). {
    intros y Hy. apply meta_maps_into. intros i Hi.
    eapply HAi... apply HgFy...
  }
  set (Func (InfCProd I A) (InfCProd I B) G) as h.
  apply CardAx1. exists h. apply meta_bijective.
  - intros x Hx. apply SepI.
    + apply ArrowI. apply HG...
    + intros i Hi. unfold G. rewrite meta_func_ap...
      apply HgFx... apply HG...
  - intros x1 Hx1 x2 Hx2 Heq.
    assert (∀i ∈ I, g[F_ i][x1[i]] = g[F_ i][x2[i]]). {
      intros i Hi. eapply func_sv. apply HG... rewrite <- Heq.
      - apply SepI. apply CProdI... apply HgFx'... zfcrewrite.
      - apply SepI. apply CProdI... apply HgFx'... zfcrewrite.
    }
    apply InfCProdE in Hx1 as [Hx1 Hxi1].
    apply InfCProdE in Hx2 as [Hx2 Hxi2].
    destruct Hx1 as [Hf1 [Hd1 Hr1]].
    destruct Hx2 as [Hf2 [Hd2 Hr2]].
    apply func_ext... intros i Hi. rewrite Hd1 in Hi.
    pose proof (HgF _ Hi) as [Hinj [Hd _]].
    eapply injectiveE...
    + rewrite Hd. apply Hxi1...
    + rewrite Hd. apply Hxi2...
    + apply H...
  - intros y Hy. assert (Hx: G' y ∈ InfCProd I A). {
      apply InfCProdI. apply HG'...
      intros i Hi. unfold G'. rewrite meta_func_ap...
      apply HgFy... apply HG'...
    }
    assert (Heqd: dom (G (G' y)) = I). {
      apply ExtAx. intros i. split; intros Hi.
      - apply domE in Hi as [f Hp].
        apply SepE in Hp as [Hp _].
        apply CProdE1 in Hp as [Hi _]. zfcrewrite.
      - eapply domI. apply SepI. apply CProdI...
        apply HgFx'... zfcrewrite.
    }
    exists (G' y). split... apply func_ext...
    + apply meta_maps_into. intros i Hi. apply HgFx'...
    + apply InfCProdE in Hy as [[]]...
    + apply InfCProdE in Hy as [[_ [Hd _]]]...
    + intros i Hi. rewrite Heqd in Hi. unfold G, G'.
      pose proof (HgF _ Hi) as [Hinj [Hd Hr]].
      rewrite meta_func_ap... rewrite meta_func_ap...
      rewrite inv_ran_reduction...
      * rewrite Hr. eapply InfCProdE...
      * apply meta_maps_into. intros j Hj. apply HgFy'...
      * apply meta_maps_into. intros j Hj. apply HgFx'...
Qed.
