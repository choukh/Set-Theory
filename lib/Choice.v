(** Based on "Elements of Set Theory" Chapter 7 Part 5 **)
(** Coq coding by choukh, Jan 2021 **)

Require Import ZFC.lib.Dominate.

(*** AC 1 ~ 6 ***)

(* 选择公理的等效表述1：单值化原则：存在函数包含于给定关系 *)
Definition AC_I := ∀ R, is_rel R →
  ∃ F, is_function F ∧ F ⊆ R ∧ dom F = dom R.

(* 选择公理等效表述1'：存在从并集到原集合的函数使得参数是值的成员 *)
Definition AC_I' := ∀ A,
  ∃ F, F: ⋃A ⇒ A ∧ ∀x ∈ dom F, x ∈ F[x].

(* 选择公理等效表述2：任意多个非空集合的笛卡尔积非空 *)
Definition AC_II :=
  ∀ I ℱ, (∀i ∈ I, ⦿ ℱ i) → ⦿ InfCProd I ℱ.

(* 选择公理等效表述3：非空子集所组成的集合上存在选择函数 *)
Definition AC_III := ∀ A,
  ∃ F, is_function F ∧ dom F = {x ∊ 𝒫 A | nonempty} ∧ 
  ∀ B, ⦿ B → B ⊆ A → F[B] ∈ B.

(* 选择公理等效表述3'：非空集合所组成的集合上存在选择函数 *)
Definition AC_III' := ∀ 𝒜, (∀A ∈ 𝒜, ⦿ A) →
  ∃ F, is_function F ∧ dom F = 𝒜 ∧ ∀A ∈ 𝒜, F[A] ∈ A.

(* 选择公理等效表述4：策梅洛公设 (Zermelo’s Postulate) *)
Definition AC_IV := ∀ 𝒜,
  (* a 子集非空 *) (∀A ∈ 𝒜, ⦿ A) →
  (* b 子集不交 *) (∀ A B ∈ 𝒜, A ≠ B → disjoint A B) →
  ∃ C, ∀A ∈ 𝒜, ∃ x, A ∩ C = ⎨x⎬.

(* 选择公理等效表述5：势具有可比较性 *)
Definition AC_V := ∀ A B, A ≼ B ∨ B ≼ A.

(* 链：子集关系下的全序集 *)
Definition is_chain := λ ℬ, ∀ C D ∈ ℬ, C ⊆ D ∨ D ⊆ C.

(* Zorn's Lemma (set theory form) *)
(* 选择公理等效表述6：佐恩引理（第一极大原理） *)
(* 若偏序集中任意全序子集(链)均有上界，则该偏序集存在极大元 *)
Definition AC_VI := ∀ 𝒜,
  (∀ ℬ, is_chain ℬ → ℬ ⊆ 𝒜 → ⋃ℬ ∈ 𝒜) → ∃ M, sub_maximal M 𝒜.

(* AC cycle
    (1 ↔ 1') → 2 → 4 → (3 ↔ 3') → 1
    6 → [1, 5]
    continue at EST7_5: [3, 5] → WO → 6
*)

Theorem AC_I_to_II : AC_I → AC_II.
Proof with eauto.
  unfold AC_I, AC_II. intros * AC1 I ℱ Hxi.
  set (I × ⋃{ℱ | i ∊ I}) as P.
  set {p ∊ P | λ p, π2 p ∈ ℱ (π1 p)} as R.
  specialize AC1 with R as [f [Hf [Hsub Hdeq]]]. {
    apply sep_cp_is_rel.
  }
  assert (Hdeq2: dom f = I). {
    rewrite Hdeq. apply ExtAx. intros i. split; intros Hi.
    - apply domE in Hi as [y Hp]. apply SepE in Hp as [Hp _].
      apply CProdE2 in Hp as [Hi _]...
    - apply Hxi in Hi as Hx. destruct Hx.
      eapply domI. apply SepI. apply CProdI...
      eapply FUnionI... zfcrewrite.
  }
  exists f. apply InfCProdI.
  - split... split... intros y Hy.
    apply ranE in Hy as [i Hp].
    apply Hsub in Hp. apply SepE in Hp as [Hp _].
    apply CProdE2 in Hp as [_ Hy]...
  - intros i Hi. rewrite <- Hdeq2 in Hi.
    apply func_correct in Hi... apply Hsub in Hi.
    apply SepE in Hi as [_ Hy]. zfcrewrite.
Qed.

Theorem AC_I_iff_I' : AC_I ↔ AC_I'.
Proof with eauto; try congruence.
  unfold AC_I, AC_I'. split.
  - intros AC1 A.
    set {p ∊ ⋃A × A | λ p, π1 p ∈ π2 p} as R.
    specialize AC1 with R as [f [Hf [Hsub Hdeq]]]. {
      apply sep_cp_is_rel.
    }
    assert (Hd: dom f = ⋃ A). {
      rewrite Hdeq. apply ExtAx. split; intros Hx.
      - apply domE in Hx as [y Hp].
        apply SepE in Hp as [Hp _].
        apply CProdE2 in Hp as [Hx _]...
      - assert (Hu := Hx). apply UnionAx in Hx as [a [Ha Hx]].
        eapply domI. apply SepI. apply CProdI... zfcrewrite.
    }
    exists f. split; [split; [|split]|]...
    + intros y Hy. apply ranE in Hy as [x Hp].
      apply Hsub in Hp. apply SepE in Hp as [Hp _].
      apply CProdE2 in Hp as [_ Hy]...
    + intros x Hx. apply domE in Hx as [y Hp].
      apply func_ap in Hp as Hap... rewrite Hap.
      apply Hsub in Hp. apply SepE in Hp as [_ H]. zfcrewrite.
  - intros AC1' R Hrel.
    specialize AC1' with R as [f [[Hf [Hd Hr]] Hin]].
    assert (Hdf: ∀x ∈ dom R, ⎨x⎬ ∈ dom f). {
      intros x Hx. rewrite Hd. apply UnionAx.
      eapply domE in Hx as [y Hp].
      exists <x, y>. split... apply PairI1.
    }
    assert (Hrf: ∀x ∈ dom R, ∃ a b, <a, b> ∈ R ∧ f[⎨x⎬] = <a, b>). {
      intros x Hx. apply Hdf in Hx.
      apply domE in Hx as [y Hp]. apply ranI in Hp as Hy.
      apply func_ap in Hp... subst y. apply Hr in Hy.
      apply rel_pair in Hy as Heqy...
      exists (π1 f[⎨x⎬]), (π2 f[⎨x⎬]). split...
    }
    set (Func (dom R) (ran R) (λ x, π2 f[⎨x⎬])) as g.
    assert (Hg: is_function g). {
      apply meta_maps_into. intros x Hx.
      apply Hrf in Hx as [a [b [Hp Hfx]]].
      rewrite Hfx. zfcrewrite. eapply ranI...
    }
    exists g. split; [|split]...
    + intros p Hp. apply SepE in Hp as [Hp Heq].
      apply CProdE1 in Hp as [x [Hx [y [_ Hp]]]].
      subst p. zfcrewrite. subst y.
      apply Hdf in Hx as Hsx. apply Hin in Hsx.
      apply Hrf in Hx as [a [b [Hp Hfx]]].
      rewrite Hfx in *. zfcrewrite.
      apply PairE in Hsx as [].
      * apply single_injective in H...
      * apply single_eq_pair in H as [H1 H2]...
    + apply ExtAx. split; intros Hx.
      * apply domE in Hx as [y Hp]. apply SepE in Hp as [Hp _].
        apply CProdE2 in Hp as [Hx _]...
      * assert (Hx' := Hx). apply Hrf in Hx' as [a [b [Hp Hfx]]].
        apply ranI in Hp. eapply domI. apply SepI. apply CProdI...
        zfcrewrite. rewrite Hfx. zfcrewrite.
Qed.

Theorem AC_II_to_IV : AC_II → AC_IV.
Proof with eauto.
  unfold AC_II, AC_IV. intros AC2 𝒜 Hi Hdj.
  destruct (AC2 𝒜 (λ x, x)) as [f Hf]. {
    intros A HA. apply Hi...
  }
  apply SepE in Hf as [Hf Hin].
  apply arrow_iff in Hf as [Hf [Hd _]].
  exists (ran f). intros A HA. exists (f[A]). apply sub_antisym.
  - intros y Hy. apply BInterE in Hy as [H1 H2].
    apply ranE in H2 as [x Hp]. apply domI in Hp as Hx.
    rewrite Hd in Hx. apply Hin in Hx as Hfx.
    apply func_ap in Hp... subst y. 
    destruct (classic (A = x)). subst x...
    exfalso. apply Hdj in H... eapply disjointE...
  - apply single_of_member_is_subset. apply BInterI.
    + apply Hin...
    + eapply ap_ran... split...
Qed.

Theorem AC_IV_to_III : AC_IV → AC_III.
Proof with eauto.
  unfold AC_IV, AC_III. intros AC4 A.
  set {x ∊ 𝒫 A | nonempty} as A'.
  set {λ B, ⎨B⎬ × B | B ∊ A'} as 𝒜.
  destruct AC4 with 𝒜 as [C Hsg]. {
    intros x Hx. apply ReplAx in Hx as [B [HB Hx]].
    apply SepE in HB as [_ [b Hb]]. subst x.
    exists <B, b>. apply CProdI...
  } {
    intros x Hx y Hy Hnq.
    apply ReplAx in Hx as [B [_ Hx]].
    apply ReplAx in Hy as [C [_ Hy]].
    apply disjointI. intros [p [H1 H2]]. apply Hnq. subst.
    apply CProdE1 in H1 as [a [Ha [b [Hb H1]]]].
    apply CProdE1 in H2 as [c [Hc [d [Hd H2]]]]. subst.
    apply SingE in Ha. apply SingE in Hc.
    apply op_iff in H2 as []. congruence.
  }
  assert (Hstar: ∀x ∈ ⋃ 𝒜, ∃ B, B ∈ A' ∧ x ∈ ⎨B⎬ × B). {
    intros x Hx. apply UnionAx in Hx as [p [Hp Hx]].
    apply ReplAx in Hp as [B [HB Hp]]. subst. exists B. split...
  }
  assert (Hcp: ∀B ∈ A', ⎨B⎬ × B ∈ 𝒜). {
    intros B HB. apply ReplAx. exists B. split...
  }
  set (C ∩ ⋃𝒜) as F.
  assert (Hf: is_function F). {
    repeat split.
    - intros x Hx. apply BInterE in Hx as [_ Hx].
      apply Hstar in Hx as [B [_ Hp]].
      apply CProdE1 in Hp as [a [Ha [b [Hb Hp]]]].
      apply SingE in Ha. subst...
    - apply domE in H...
    - intros y1 y2 H1 H2.
      apply BInterE in H1 as [Hc1 H1].
      apply BInterE in H2 as [Hc2 H2].
      apply Hstar in H1 as [B1 [_ H1]].
      apply Hstar in H2 as [B2 [HB2 H2]].
      apply CProdE1 in H1 as [a [Ha [b [Hb H1]]]].
      apply CProdE1 in H2 as [c [Hc [d [Hd H2]]]].
      apply SingE in Ha. apply SingE in Hc.
      apply op_iff in H1 as []. apply op_iff in H2 as []. subst.
      apply Hcp in HB2 as H0.
      assert (H1: <B2, b> ∈ ⎨B2⎬ × B2 ∩ C).
        { apply BInterI... apply CProdI... }
      assert (H2: <B2, d> ∈ ⎨B2⎬ × B2 ∩ C).
        { apply BInterI... apply CProdI... }
      apply Hsg in H0 as [x Hx]. rewrite Hx in H1, H2.
      apply SingE in H1. apply SingE in H2. subst.
      apply op_iff in H2 as []...
  }
  exists F. split... split.
  - apply ExtAx. split; intros Hx.
    + apply domE in Hx as [y Hp].
      apply BInterE in Hp as [_ Hp].
      apply Hstar in Hp as [B [HB Hp]].
      apply CProdE2 in Hp as [Hx _].
      apply SingE in Hx. subst...
    + assert (H: ⎨x⎬ × x ∈ 𝒜). { apply ReplAx. exists x. split... }
      pose proof (Hsg _ H) as [p Heq].
      assert (Hp: p ∈ ⎨x⎬ × x ∩ C). { rewrite Heq... }
      apply BInterE in Hp as [H1 H2]. assert (H1' := H1).
      apply CProdE1 in H1 as [a [Ha [b [Hb H1]]]].
      apply SingE in Ha. subst. eapply domI. apply BInterI...
      apply UnionAx. exists (⎨x⎬ × x). split...
  - intros B Hi Hsub.
    assert (HB: B ∈ A'). { apply SepI... apply PowerAx... }
    apply Hcp in HB. pose proof (Hsg _ HB) as [p Heq].
    assert (Hp: p ∈ ⎨B⎬ × B ∩ C). { rewrite Heq... }
    apply BInterE in Hp as [H1 H2].
    apply CProdE1 in H1 as [a [Ha [b [Hb H1]]]].
    apply SingE in Ha. subst. cut (F[B] = b). congruence.
    apply func_ap... apply BInterI... apply UnionAx.
    exists (⎨B⎬ × B). split... apply CProdI...
Qed.

Theorem AC_III_iff_III' : AC_III ↔ AC_III'.
Proof with eauto.
  unfold AC_III, AC_III'. split.
  - intros AC3 𝒜 Hne.
    specialize AC3 with (⋃ 𝒜) as [f [Hf [Hd Hr]]].
    assert (Hsub: 𝒜 ⊆ dom f). {
      intros x Hx. rewrite Hd. apply SepI. apply ex2_6_b... apply Hne...
    }
    exists (f ↾ 𝒜). split; [|split].
    + apply restr_func...
    + apply ExtAx. split; intros Hx.
      * apply domE in Hx as [y Hp]. apply restrE2 in Hp as []...
      * eapply domI. apply restrI... apply func_correct... apply Hsub...
    + intros A HA. rewrite (restr_ap f (dom f))...
      apply Hr. apply Hne... apply ex2_3...
  - intros AC3' A.
    specialize AC3' with {x ∊ 𝒫 A | nonempty} as [f [Hf [Hd Hr]]]. {
      intros x Hx. apply SepE2 in Hx...
    }
    exists f. split; [|split]...
    intros x Hne Hsub. apply Hr. apply SepI... apply PowerAx...
Qed.

Theorem AC_III_to_I : AC_III → AC_I.
Proof with auto.
  unfold AC_III, AC_I. intros AC3 R Hrel.
  specialize AC3 with (ran R) as [G [Hgf [Hgd Hgr]]].
  set (λ x, {y ∊ ran R | λ y, <x, y> ∈ R}) as ℬ.
  set (Func (dom R) (ran R) (λ x, G[ℬ x])) as F.
  assert (Hstar: ∀x ∈ dom R, <x, G[ℬ x]> ∈ R). {
    intros x Hx. cut (G[ℬ x] ∈ ℬ x).
    intros H. apply SepE2 in H...
    apply domE in Hx as [y Hp].
    apply ranI in Hp as Hr. apply Hgr. exists y.
    apply SepI... intros z Hz. apply SepE1 in Hz...
  }
  assert (Hf: F: dom R ⇒ ran R). {
    apply meta_maps_into. intros x Hx.
    eapply ranI. apply Hstar...
  }
  destruct Hf as [Hff [Hfd _]].
  exists F. split; [|split]...
  intros p Hp. apply SepE in Hp as [H1 H2].
  apply CProdE1 in H1 as [a [Ha [b [Hb Hp]]]].
  subst. zfcrewrite. subst. apply Hstar...
Qed.

Theorem AC_VI_to_I : AC_VI → AC_I.
Proof with eauto.
  unfold AC_VI, AC_I. intros Zorn R Hrel.
  set {f ∊ 𝒫 R | λ f, is_function f} as 𝒜.
  specialize Zorn with 𝒜 as [M [HM Hmax]]. {
    intros ℬ Hchn Hsub.
    assert (Hu: ⋃ ℬ ∈ 𝒫 R). {
      apply PowerAx. intros x Hx.
      apply UnionAx in Hx as [B [HB Hx]].
      apply Hsub in HB. apply SepE in HB as [HB _].
      apply PowerAx in HB. apply HB...
    }
    apply SepI... repeat split.
    - intros x Hx. apply Hrel. apply PowerAx in Hu. apply Hu...
    - apply domE in H...
    - intros y1 y2 H1 H2.
      apply UnionAx in H1 as [g [Hg H1]].
      apply UnionAx in H2 as [h [Hh H2]].
      pose proof (Hchn _ Hg _ Hh) as [Hgh|Hhg].
      + apply Hsub in Hh. apply SepE in Hh as [_ Hh].
        apply Hgh in H1. eapply func_sv...
      + apply Hsub in Hg. apply SepE in Hg as [_ Hg].
        apply Hhg in H2. eapply func_sv...
  }
  exists M. apply SepE in HM as [Hsub Hf].
  apply PowerAx in Hsub. split; [|split]...
  destruct (classic (dom M = dom R)) as [|Hnq]... exfalso.
  assert (Hps: dom M ⊂ dom R). {
    split... intros x Hx. apply domE in Hx as [y Hp].
    eapply domI. apply Hsub...
  }
  apply comp_nonempty in Hps as [a Ha].
  apply SepE in Ha as [Ha Hb]. apply domE in Ha as [b Hab].
  set (M ∪ ⎨<a, b>⎬) as M'. cut (M' ∈ 𝒜). {
    intros HM'. apply Hmax in HM' as [].
    - apply H. intros x Hx. apply BUnionI1...
    - apply Hb. rewrite H. eapply domI. apply BUnionI2...
  }
  apply SepI.
  - apply PowerAx. intros p Hp. apply BUnionE in Hp as [].
    apply Hsub... apply SingE in H. subst...
  - apply bunion_is_func... apply single_pair_is_func.
    intros x Hx. apply BInterE in Hx as [H1 H2].
    apply domE in H1 as [y1 H1].
    rewrite dom_of_single_pair in H2. apply SingE in H2.
    subst. exfalso. apply Hb. eapply domI...
Qed.

Theorem AC_VI_to_V : AC_VI → AC_V.
Proof with eauto; try congruence.
  unfold AC_VI, AC_V. intros Zorn A B.
  set {f ∊ 𝒫 (A × B) | λ f, injective f} as 𝒜.
  specialize Zorn with 𝒜 as [M [HM Hmax]]. {
    intros ℬ Hchn Hsub.
    assert (Hu: ⋃ ℬ ∈ 𝒫 (A × B)). {
      apply PowerAx. intros x Hx.
      apply UnionAx in Hx as [C [HC Hx]].
      apply Hsub in HC. apply SepE in HC as [HC _].
      apply PowerAx in HC. apply HC...
    }
    apply SepI... apply PowerAx in Hu. split; [split|].
    - intros x Hx. apply Hu in Hx. apply cprod_is_pairs in Hx...
    - split. apply domE in H...
      intros y1 y2 H1 H2.
      apply UnionAx in H1 as [g [Hg H1]].
      apply UnionAx in H2 as [h [Hh H2]].
      pose proof (Hchn _ Hg _ Hh) as [Hgh|Hhg].
      + apply Hsub in Hh. apply SepE in Hh as [_ [Hh _]].
        apply Hgh in H1. eapply func_sv...
      + apply Hsub in Hg. apply SepE in Hg as [_ [Hg _]].
        apply Hhg in H2. eapply func_sv...
    - intros y Hy. split. apply ranE in Hy...
      intros x1 x2 H1 H2.
      apply UnionAx in H1 as [g [Hg H1]].
      apply UnionAx in H2 as [h [Hh H2]].
      pose proof (Hchn _ Hg _ Hh) as [Hgh|Hhg].
      + apply Hsub in Hh. apply SepE in Hh as [_ Hh].
        apply Hgh in H1. eapply injectiveE...
        eapply domI... eapply domI... destruct Hh as [Hh _].
        apply func_ap in H1... apply func_ap in H2...
      + apply Hsub in Hg. apply SepE in Hg as [_ Hg].
        apply Hhg in H2. eapply injectiveE...
        eapply domI... eapply domI... destruct Hg as [Hg _].
        apply func_ap in H1... apply func_ap in H2...
  }
  apply SepE in HM as [Hsub Hinj]. apply PowerAx in Hsub.
  destruct (classic (dom M = A ∨ ran M = B)). {
    destruct H; [left; exists M|right; exists (M⁻¹)].
    - split... split... intros y Hy. apply ranE in Hy as [x Hp].
      apply Hsub in Hp. apply CProdE2 in Hp as []...
    - split. apply inv_injective... split.
      rewrite inv_dom... rewrite inv_ran.
      intros x Hx. apply domE in Hx as [y Hp].
      apply Hsub in Hp. apply CProdE2 in Hp as []...
  }
  exfalso. apply not_or_and in H as [Hnq1 Hnq2].
  assert (Hps1: dom M ⊂ A). {
    split... intros x Hx. apply domE in Hx as [y Hp].
    apply Hsub in Hp. apply CProdE2 in Hp as []...
  }
  assert (Hps2: ran M ⊂ B). {
    split... intros y Hy. apply ranE in Hy as [x Hp].
    apply Hsub in Hp. apply CProdE2 in Hp as []...
  }
  apply comp_nonempty in Hps1 as [a Ha].
  apply comp_nonempty in Hps2 as [b Hb].
  apply SepE in Ha as [Ha Ha'].
  apply SepE in Hb as [Hb Hb'].
  set ((M ∪ ⎨<a, b>⎬)) as M'. cut (M' ∈ 𝒜). {
    intros HM'. apply Hmax in HM' as [].
    - apply H. intros x Hx. apply BUnionI1...
    - apply Ha'. rewrite H. eapply domI. apply BUnionI2...
  }
  assert (Hinj' := Hinj). destruct Hinj' as [Hf Hs].
  apply SepI; [|split].
  - apply PowerAx. intros p Hp. apply BUnionE in Hp as [].
    apply Hsub... apply SingE in H. subst. apply CProdI...
  - apply bunion_is_func... apply single_pair_is_func.
    intros x Hx. apply BInterE in Hx as [H1 H2].
    apply domE in H1 as [y1 H1].
    rewrite dom_of_single_pair in H2. apply SingE in H2.
    subst. exfalso. apply Ha'. eapply domI...
  - intros y Hy. split. apply ranE in Hy...
    intros x1 x2 H1 H2.
    apply BUnionE in H1 as [H1|H1]; apply BUnionE in H2 as [H2|H2].
    + eapply injectiveE... eapply domI... eapply domI...
      apply func_ap in H1... apply func_ap in H2...
    + exfalso. apply SingE in H2. apply op_iff in H2 as []; subst.
      apply Hb'. eapply ranI...
    + exfalso. apply SingE in H1. apply op_iff in H1 as []; subst.
      apply Hb'. eapply ranI...
    + apply SingE in H1. apply op_iff in H1 as []; subst.
      apply SingE in H2. apply op_iff in H2 as []; subst...
Qed.

Theorem AC_VI_to_III : AC_VI → AC_III.
Proof.
  intros. apply AC_IV_to_III. apply AC_II_to_IV.
  apply AC_I_to_II. apply AC_VI_to_I. apply H.
Qed.

Theorem AC_VI_to_III' : AC_VI → AC_III'.
Proof.
  intros. apply AC_III_iff_III'. apply AC_VI_to_III. apply H.
Qed.

Theorem ac1 : AC_I.
Proof. exact EST3_2.ac1. Qed.

Theorem ac2 : AC_II.
Proof. apply AC_I_to_II. apply ac1. Qed.

Theorem ac4 : AC_IV.
Proof. apply AC_II_to_IV. apply ac2. Qed.

Theorem ac3 : AC_III.
Proof. apply AC_IV_to_III. apply ac4. Qed.

Theorem ac3' : AC_III'.
Proof. apply AC_III_iff_III'. apply ac3. Qed.

(* ==需要选择公理== *)
(* 满射的定义域支配值域 *)
Lemma domain_of_surjection_dominate_range : AC_I →
  ∀ A B F, F: A ⟹ B → B ≼ A.
Proof with auto.
  intros AC1 * H.
  apply right_inv_of_surjection_injective in H as [G [H _]]...
  exists G. apply H.
Qed.

(* ==需要选择公理== *)
(* 函数的定义域支配值域 *)
Lemma domain_dominate_range : AC_I → ∀ F, is_function F → ran F ≼ dom F.
Proof with eauto.
  intros AC1 F HF.
  eapply domain_of_surjection_dominate_range... split; [|split]...
Qed.

(* ==需要选择公理== *)
(* 任意非空集合B被集合A支配如果B被A满射 *)
Lemma dominated_impl_mapped_onto : AC_I →
  ∀ A B, ⦿ B → B ≼ A → ∃ F, F: A ⟹ B.
Proof with auto.
  intros AC1 * Hne [G HG].
  apply injection_is_func in HG as [HG Hi].
  apply (left_inv G B A HG Hne) in Hi as [F [HF Hid]].
  exists F. apply right_inv... exists G. split...
Qed.

(* ==需要选择公理== *)
(* 任意非空集合B被集合A支配当且仅当B被A满射 *)
Fact dominated_iff_mapped_onto : AC_I →
  ∀ A B, ⦿ B → (∃ F, F: A ⟹ B) ↔ B ≼ A.
Proof with eauto.
  split; intros [F HF].
  - eapply domain_of_surjection_dominate_range...
  - apply dominated_impl_mapped_onto... exists F...
Qed.

(*** AC 6 ~ 8 ***)

(* 有限特征条件：集合满足条件当且仅当该集合的每个有限子集都满足条件 *)
Definition finite_character_property : (set → Prop) → Prop := λ P,
  ∀ B, P B ↔ ∀ C, finite C → C ⊆ B → P C.

(* 有限特征集：集合是其成员当且仅当该集合的每个有限子集都是其成员 *)
Definition finite_character_set := λ 𝒜,
  finite_character_property (λ x, x ∈ 𝒜).
Notation 𝗙𝗖 := finite_character_set.

(* 选择公理等效表述7：图基引理（第二极大原理） *)
(* 具有有限特征的非空集合必有子集关系下的极大元 *)
Definition AC_VII := ∀ 𝒜, ⦿ 𝒜 →
  𝗙𝗖 𝒜 → ∃ M, sub_maximal M 𝒜.

(* 链集：集合的所有全序子集所组成的集合 *)
Definition Chains := λ A, {B ∊ 𝒫 A | is_chain}.

(* 极大链：链集的极大元 *)
Definition max_chain := λ ℳ 𝒜, sub_maximal ℳ (Chains 𝒜).

(* 选择公理等效表述8：豪斯多夫极大原理 *)
(* 对于偏序集中任意全序子集(链)，都存在极大全序子集(极大链)包含它 *)
Definition AC_VIII := ∀ 𝒜 ℬ, ℬ ⊆ 𝒜 → is_chain ℬ →
  ∃ ℳ, max_chain ℳ 𝒜 ∧ ℬ ⊆ ℳ.

(* 选择公理等效表述8'：极大原理 *)
(* 偏序集有极大元，如果对于该偏序集中的任意链，
  都存在该偏序集中的一个成员，包含链中的所有成员 *)
Definition AC_VIII' := ∀ 𝒜,
  (∀ ℬ, ℬ ⊆ 𝒜 → is_chain ℬ → ∃N ∈ 𝒜, ∀B ∈ ℬ, B ⊆ N) →
  ∃ M, sub_maximal M 𝒜.

(* 空集是链 *)
Lemma emptyset_is_chain : is_chain ∅.
Proof. intros x Hx. exfalso0. Qed.

(* 链的子集仍是链 *)
Lemma sub_of_chain_is_chain : ∀ ℬ 𝒞, is_chain ℬ → 𝒞 ⊆ ℬ → is_chain 𝒞.
Proof.
  intros * Hchn Hsub C HC D HD. apply Hchn; apply Hsub; auto.
Qed.

(* 非空有限链必有极大元 *)
Lemma finite_chain_has_max : ∀ ℬ, ⦿ ℬ →
  finite ℬ → is_chain ℬ → ∃ M, sub_maximal M ℬ.
Proof with eauto; try congruence.
  intros ℬ Hne [n [Hn Hqn]]. generalize dependent ℬ.
  set {n ∊ ω | λ n, ∀ ℬ,
    ⦿ ℬ → ℬ ≈ n → is_chain ℬ → ∃ M, sub_maximal M ℬ } as N.
  ω_induction N Hn; intros ℬ Hne Hqn Hchn. {
    exfalso. apply EmptyNI in Hne. apply eqnum_empty in Hqn...
  }
  destruct Hne as [B HB].
  apply split_one_element in HB as Heq.
  destruct (classic (ℬ - ⎨B⎬ = ∅)) as [|Hne]. {
    exists B. split... intros x Hx.
    apply sub_iff_no_comp in H. apply H in Hx. apply SingE in Hx...
  }
  pose proof (IH (ℬ - ⎨B⎬)) as [M [HM Hmax]].
  - apply EmptyNE...
  - apply finite_set_remove_one_element...
  - eapply sub_of_chain_is_chain...
  - assert (HM': M ∈ ℬ). { apply SepE1 in HM... }
    pose proof (Hchn B HB M HM') as [].
    + exists M. split... intros x Hx.
      destruct (classic (x = B)).
      * subst x. destruct (classic (M ⊆ B))... right. apply sub_antisym...
      * apply Hmax. apply SepI... apply SingNI...
    + exists B. split... intros x Hx.
      destruct (classic (x = B))...
      destruct (Hmax x). { apply SepI... apply SingNI... }
      * left. intros Hsub. apply H1. eapply sub_tran...
      * left. subst x. intros Hsub. apply H0. apply sub_antisym...
Qed.

(* AC cycle
    6 → 7 → 8 → 8' → 6
*)

Theorem AC_VI_to_AC_VII : AC_VI → AC_VII.
Proof with eauto.
  unfold AC_VI, AC_VII.
  intros Zorn 𝒜 [A HA] Hfc. apply Zorn.
  intros ℬ Hchn Hs1. apply Hfc.
  intros C Hfin Hs2. destruct (classic (C = ∅)). {
    eapply Hfc in HA. apply HA. apply Hfin.
    subst C. apply empty_sub_all.
  }
  cut (∃B ∈ ℬ, C ⊆ B). {
    intros [B [HB Hs3]]. apply Hs1 in HB.
    apply Hfc with B C in HB...
  }
  set {p ∊ C × ℬ | λ p, π1 p ∈ π2 p} as R.
  pose proof (AC_VI_to_I Zorn) as AC1.
  pose proof (AC1 R) as [F [HfF [HsF Hd]]]. { apply sep_cp_is_rel. }
  assert (HdF: dom F = C). {
    rewrite Hd. apply ExtAx. split; intros Hx.
    - apply domE in Hx as [y Hp]. apply SepE in Hp as [Hp _].
      apply CProdE2 in Hp as [Hx _]...
    - apply Hs2 in Hx as Hxb.
      apply UnionAx in Hxb as [B [HB Hxb]].
      eapply domI. apply SepI. apply CProdI... zfcrewrite.
  }
  assert (Hsub: ran F ⊆ ℬ). {
    intros y Hy. apply ranE in Hy as [x Hp].
    apply HsF in Hp. apply SepE in Hp as [Hp _].
    apply CProdE2 in Hp as [_ Hy]...
  }
  pose proof (finite_chain_has_max (ran F)) as [M [HM Hmax]].
  - apply EmptyNE in H as [c Hc].
    exists (F[c]). eapply ap_ran... split...
  - eapply dominated_by_finite_is_finite.
    apply domain_dominate_range... rewrite HdF...
  - intros D HD E HE. apply Hchn; apply Hsub...
  - exists M. split. apply Hsub...
    intros x Hx. rewrite <- HdF in Hx. apply domE in Hx as [B Hp].
    apply ranI in Hp as Hr. apply func_ap in Hp as Hap... subst B.
    apply HsF in Hp. apply SepE in Hp as [_ Hx]. zfcrewrite.
    destruct (Hmax (F[x])); auto; [|subst M]...
    apply Hsub in Hr. apply Hsub in HM.
    pose proof (Hchn M HM (F[x]) Hr) as [].
    exfalso... apply H1...
Qed.

(* 通过二元并从有限特征集构造具有有限特征的子集 *)
Lemma construct_fc_subset_by_bunion : ∀ 𝒜, 𝗙𝗖 𝒜 →
  ∀A ∈ 𝒜, 𝗙𝗖 {B ∊ 𝒜 | λ B, A ∪ B ∈ 𝒜}.
Proof with eauto.
  intros 𝒜 Hfc A HA. split.
  - intros HB C HfC HsC.
    apply SepE in HB as [HB Hu]. apply SepI.
    + eapply Hfc in HB...
    + apply Hfc. intros D HfD HsD.
      eapply Hfc in Hu... eapply sub_tran. apply HsD.
      rewrite bunion_comm, (bunion_comm A). apply sub_mono_bunion...
  - intros H. apply SepI.
    + apply Hfc. intros C HfC HsC.
      pose proof (H C HfC HsC) as HC. apply SepE1 in HC...
    + apply Hfc. intros C HfC HsC.
      set (B ∩ C) as D.
      assert (HD: D ∈ {B ∊ 𝒜 | λ B, A ∪ B ∈ 𝒜}). {
        apply H. apply (subset_of_finite_is_finite _ C)...
        intros x Hx. apply BInterE in Hx as []...
        intros x Hx. apply BInterE in Hx as []...
      }
      apply SepE in HD as [_ Hu].
      eapply Hfc in Hu... unfold D.
      rewrite bunion_binter_distr. intros x Hx.
      apply BInterI. apply HsC... apply BUnionI2...
Qed.

(* ==需要选择公理== *)
(* 对于有限特征集的任意成员都存在极大元包含它 *)
Lemma for_all_in_fc_set_ex_max_contains_it : AC_VII → ∀ 𝒜, 𝗙𝗖 𝒜 →
  ∀A ∈ 𝒜, ∃ M, sub_maximal M 𝒜 ∧ A ⊆ M.
Proof with eauto; try congruence.
  intros AC7 𝒜 Hfc A HA.
  set {B ∊ 𝒜 | λ B, A ∪ B ∈ 𝒜} as 𝒜'.
  pose proof (AC7 𝒜') as [M [HM Hmax]].
  - exists A. apply SepI... rewrite bunion_self...
  - apply construct_fc_subset_by_bunion...
  - exists M. assert (Hu: A ∪ M ∈ 𝒜'). {
      apply SepE in HM as [_ Hu]. apply SepI...
      rewrite bunion_assoc, bunion_self...
    }
    assert (Hsub: A ⊆ M). {
      apply Hmax in Hu as [].
      - exfalso. apply H. intros x Hx. apply BUnionI2...
      - rewrite H. intros x Hx. apply BUnionI1...
    }
    split... split. apply SepE1 in HM...
    intros K HK. destruct (classic (M ⊆ K))... right.
    cut (K ∈ 𝒜'). { intros HK'. apply Hmax in HK' as []... }
    apply SepI... replace (A ∪ K) with K...
    apply ExtAx. split; intros Hx.
    * apply BUnionI2...
    * apply BUnionE in Hx as []... apply H. apply Hsub...
Qed.

(* 集合的链集具有有限特征 *)
Lemma set_of_all_chains_in_set_is_fc_set : ∀ A, 𝗙𝗖 (Chains A).
Proof with eauto.
  split.
  - intros HB C _ HsC.
    apply SepE in HB as [HsB Hchn]. apply PowerAx in HsB.
    apply SepI. apply PowerAx. eapply sub_tran...
    eapply sub_of_chain_is_chain...
  - intros H. apply SepI.
    + apply PowerAx. intros x Hx.
      assert (Hs: ⎨x⎬ ∈ Chains A). {
        apply H... intros s Hs. apply SingE in Hs. subst...
      }
      apply SepE in Hs as [Hs _]. apply PowerAx in Hs. apply Hs...
    + intros a Ha b Hb.
      destruct (classic (a = b)). { left. subst... }
      assert (Hp: {a, b} ∈ Chains A). {
        apply H. apply pair_finite...
        intros x Hx. apply PairE in Hx as []; subst...
      }
      apply SepE in Hp as [_ Hchn].
      apply Hchn. apply PairI1. apply PairI2.
Qed.

Theorem AC_VII_to_AC_VIII : AC_VII → AC_VIII.
Proof with auto.
  unfold AC_VIII.
  intros Tukey * Hsub Hchn.
  apply for_all_in_fc_set_ex_max_contains_it.
  apply Tukey. apply set_of_all_chains_in_set_is_fc_set.
  apply SepI... apply PowerAx...
Qed.

Theorem AC_VIII_to_AC_VIII' : AC_VIII → AC_VIII'.
Proof with auto.
  unfold AC_VIII, AC_VIII'.
  intros Hausdorff 𝒜 H.
  pose proof (Hausdorff 𝒜 ∅) as [ℳ [[HM Hmax] _]].
  { apply empty_sub_all. }
  { apply emptyset_is_chain. }
  apply SepE in HM as [HM Hchn]. apply PowerAx in HM.
  specialize H with ℳ as [N [HN Hmax']]...
  exists N. split... intros K HK.
  destruct (classic (N ⊆ K)) as [Hsub|]... right.
  apply sub_antisym... apply Hmax'...
  replace ℳ with (ℳ ∪ ⎨K⎬). apply BUnionI2...
  cut (ℳ ∪ ⎨K⎬ ∈ Chains 𝒜). {
    intros Hu. apply Hmax in Hu as [Hm|]... exfalso.
    apply Hm. intros x Hx. apply BUnionI1...
  }
  apply SepI.
  - apply PowerAx. intros x Hx.
    apply BUnionE in Hx as [Hx|Hx]. apply HM...
    apply SingE in Hx. subst x...
  - intros C HC D HD.
    apply BUnionE in HC as [HC|HC]; apply BUnionE in HD as [HD|HD].
    + apply Hchn...
    + apply SingE in HD. subst D. left.
      eapply sub_tran. apply Hmax'... apply Hsub.
    + apply SingE in HC. subst C. right.
      eapply sub_tran. apply Hmax'... apply Hsub.
    + apply SingE in HC. apply SingE in HD. subst C D. left...
Qed.

Theorem AC_VIII'_to_AC_VI : AC_VIII' → AC_VI.
Proof with auto.
  unfold AC_VIII', AC_VI.
  intros MP A Hbnd.
  apply MP. intros B Hsub Hchn.
  pose proof (Hbnd _ Hchn Hsub) as Hu.
  exists (⋃ B). split... intros b Hb. apply ex2_3...
Qed.
