(** Based on "Elements of Set Theory" Chapter 8 Part 4 **)
(** Coq coding by choukh, Mar 2021 **)

Require Export ZFC.EST8_3.
Require Import ZFC.lib.LoStruct.

(*** EST第八章4：序类型乘法，序类型算术定律 ***)

(* 反向字典序 *)
Definition LoMul_R := λ S T, BinRel (A S × A T) (λ p1 p2,
  (π2 p1 <ᵣ π2 p2) (R T) ∨
  (π1 p1 <ᵣ π1 p2) (R S) ∧ π2 p1 = π2 p2
).
Notation "S * T" := (LoMul_R S T) : LoStruct_scope.

Lemma loMul_is_binRel : ∀ S T, is_binRel (S * T) (A S × A T).
Proof.
  intros S T x Hx.
  apply binRelE1 in Hx as [a [Ha [b [Hb [Hx _]]]]].
  subst x. apply CProdI; auto.
Qed.

Lemma loMul_tranr : ∀ S T, tranr (S * T).
Proof with eauto.
  intros S T x y z Hxy Hyz.
  destruct (lo S) as [_ [HtrS _]].
  destruct (lo T) as [_ [HtrT _]].
  apply binRelE2 in Hxy as [Hx [Hy [Hxy|[Hxy H1]]]];
  apply binRelE2 in Hyz as [_  [Hz [Hyz|[Hyz H2]]]]; apply binRelI...
  - left. eapply HtrT...
  - left. congruence.
  - left. congruence.
  - right. split. eapply HtrS... congruence.
Qed.

Lemma loMul_irrefl : ∀ S T, irrefl (S * T).
Proof.
  intros S T x H.
  apply binRelE2 in H as [Hx [_ [H|[H _]]]];
  (eapply lo_irrefl; [apply lo|]); eauto.
Qed.

Lemma loMul_connected : ∀ S T, connected (S * T) (A S × A T).
Proof with auto.
  intros S T x Hx y Hy Hnq.
  apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]].
  apply CProdE1 in Hy as [c [Hc [d [Hd Hy]]]]. subst.
  destruct (classic (a = c)); destruct (classic (b = d)).
  - exfalso. apply Hnq. apply op_iff...
  - eapply (lo_connected _ _ (lo T)) in H0 as []; auto;
    [left|right]; (apply binRelI; [apply CProdI..|zfc_simple])...
  - eapply (lo_connected _ _ (lo S)) in H as []; auto;
    [left|right]; (apply binRelI; [apply CProdI..|zfc_simple])...
  - eapply (lo_connected _ _ (lo T)) in H0 as []; auto;
    [left|right]; (apply binRelI; [apply CProdI..|zfc_simple])...
Qed.

Theorem loMul_loset : ∀ S T, loset (A S × A T) (S * T).
Proof.
  intros S T.
  apply loset_iff_connected_poset. repeat split.
  - apply loMul_connected.
  - apply loMul_is_binRel.
  - eapply binRel_is_rel. apply loMul_is_binRel.
  - apply loMul_tranr.
  - apply loMul_irrefl.
Qed.

Definition LoMul := λ S T,
  constr (A S × A T) (S * T) (loMul_loset S T).
Notation "S ⋅ T" := (LoMul S T) : LoStruct_scope.

Lemma loMul_well_defined : ∀ S S' T T',
  S ≅ S' → T ≅ T' → S ⋅ T ≅ S' ⋅ T'.
Proof with eauto; try congruence.
  intros * [f [Hf Hopf]] [g [Hg Hopg]].
  apply bijection_is_func in Hf as [Hf [Hinjf Hrf]].
  apply bijection_is_func in Hg as [Hg [Hinjg Hrg]].
  assert (H := Hf). destruct H as [_ [Hdf _]].
  assert (H := Hg). destruct H as [_ [Hdg _]].
  set (Func (A S × A T) (A S' × A T') (λ x, <f[π1 x], g[π2 x]>)) as F.
  assert (Hbi: F: A S × A T ⟺ A S' × A T'). {
    apply meta_bijective.
    - intros x Hx. apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]].
      subst x. zfc_simple. apply CProdI; eapply ap_ran...
    - intros x1 H1 x2 H2 Heq.
      apply CProdE1 in H1 as [a [Ha [b [Hb H1]]]].
      apply CProdE1 in H2 as [c [Hc [d [Hd H2]]]].
      subst. zfc_simple. apply op_iff in Heq as [H1 H2].
      apply injectiveE in H1... apply injectiveE in H2...
    - intros y Hy.
      apply CProdE1 in Hy as [a [Ha [b [Hb Hy]]]].
      subst. zfc_simple.
      exists <f⁻¹[a], g⁻¹[b]>. split; zfc_simple.
      + apply CProdI; eapply ap_ran; eauto;
        apply bijection_is_func; apply inv_bijection;
        apply bijection_is_func...
      + rewrite inv_ran_reduction, inv_ran_reduction...
  }
  apply bijection_is_func in Hbi as HF. destruct HF as [HF _].
  exists F. split... unfold LoMul. simpl.
  intros x Hx y Hy. unfold F.
  rewrite meta_func_ap, meta_func_ap...
  apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]].
  apply CProdE1 in Hy as [c [Hc [d [Hd Hy]]]].
  subst. zfc_simple. split; intros Hxy.
  - apply binRelI; zfc_simple; [apply CProdI; eapply ap_ran; eauto..|].
    apply binRelE2 in Hxy as [_ [_ [Hlt|[Hlt Heq]]]]; zfc_simple.
    + left. apply Hopg...
    + right. split... apply Hopf...
  - apply binRelI; zfc_simple; [apply CProdI..|]...
    apply binRelE2 in Hxy as [_ [_ [Hlt|[Hlt Heq]]]]; zfc_simple.
    + left. apply Hopg...
    + right. split. apply Hopf... apply injectiveE in Heq...
Qed.

Import OrderType.

Definition OtMul :=
  λ ρ σ, ot (proj ρ ⋅ proj σ).
Notation "ρ ⋅ σ" := (OtMul ρ σ) : OrderType_scope.

Lemma otMul_eq_ot_of_loMul : ∀ S T, ot S ⋅ ot T = ot (S ⋅ T)%lo.
Proof.
  intros. apply ot_correct.
  apply loMul_well_defined; apply proj_ot_id.
Qed.

Theorem otMul_well_defined : ∀ S S' T T',
  S ≅ S' → T ≅ T' → ot S ⋅ ot T = ot S' ⋅ ot T'.
Proof.
  intros * HisoS HisoT. do 2 rewrite otMul_eq_ot_of_loMul.
  apply ot_correct. apply loMul_well_defined; auto.
Qed.

(** 序类型算术定律 **)

Open Scope LoStruct_scope.

Lemma loAdd_assoc : ∀ S T U, S + T + U ≅ S + (T + U).
Proof with auto; try congruence.
  intros. unfold LoAdd at 1 3. simpl. unfold LoDisj_A.
  set (A (S + T) × ⎨0⎬ ∪ A U × ⎨1⎬) as Dom.
  set (A S × ⎨0⎬ ∪ A (T + U) × ⎨1⎬) as Ran.
  set (Func Dom Ran (λ x, match (ixm (π2 x = 0)) with
    | inl _ => match (ixm (π2 (π1 x) = 0)) with
      | inl _ => <π1 (π1 x), 0>
      | inr _ => <<π1 (π1 x), 0>, 1> end
    | inr _ => <<π1 x, 1>, 1> end
  )) as F.
  pose proof contra_1_0 as H10.
  pose proof contra_0_1 as H01.
  assert (Hbi: F: Dom ⟺ Ran). {
    apply meta_bijective.
    - intros x Hx. 
      apply BUnionE in Hx as []; destruct (ixm (π2 x = 0));
      apply CProdE1 in H as [a [Ha [b [Hb Heq]]]];
      apply SingE in Hb; subst; zfc_simple.
      + apply BUnionE in Ha as []; destruct (ixm (π2 a = 0));
        apply CProdE1 in H as [c [Hc [d [Hd Heq]]]];
        apply SingE in Hd; subst; zfc_simple.
        * apply BUnionI1. apply CProdI...
        * apply BUnionI2. apply CProdI...
          apply BUnionI1. apply CProdI...
      + apply BUnionI2. apply CProdI...
        apply BUnionI2. apply CProdI...
    - intros x1 H1 x2 H2 Heq.
      destruct (ixm (π2 x1 = 0)) as [Hx1|Hx1];
      destruct (ixm (π2 x2 = 0)) as [Hx2|Hx2];
      destruct (ixm (π2 (π1 x1) = 0)) as [Hx11|Hx12];
      destruct (ixm (π2 (π1 x2) = 0)) as [Hx21|Hx22];
      apply op_iff in Heq as []; subst;
      apply BUnionE in H1 as [H1|H1];
      apply BUnionE in H2 as [H2|H2];
      apply CProdE1 in H1 as [a [Ha [b [Hb H1]]]];
      apply CProdE1 in H2 as [c [Hc [d [Hd H2]]]];
      apply SingE in Hb; apply SingE in Hd; subst; zfc_simple;
      try (apply op_iff in H as []; congruence);
      apply BUnionE in Ha as [Ha|Ha];
      apply BUnionE in Hc as [Hc|Hc];
      apply CProdE1 in Ha as [s [Hs [t [Ht Ha]]]];
      apply CProdE1 in Hc as [u [Hu [v [Hv Hc]]]];
      apply SingE in Ht; apply SingE in Hv; subst; zfc_simple;
      apply op_iff in H as []; subst...
    - intros y Hy. apply BUnionE in Hy as [];
      apply CProdE1 in H as [a [Ha [b [Hb Hy]]]];
      apply SingE in Hb; subst.
      + exists <<a, 0>, 0>. split.
        apply BUnionI1. apply CProdI...
        apply BUnionI1. apply CProdI... zfc_simple.
        destruct (ixm (Embed 0 = 0))...
      + apply BUnionE in Ha as [];
        apply CProdE1 in H as [c [Hc [d [Hd H]]]];
        apply SingE in Hd; subst; zfc_simple.
        * exists <<c, 1>, 0>. split.
          apply BUnionI1. apply CProdI...
          apply BUnionI2. apply CProdI... zfc_simple.
          destruct (ixm (Embed 0 = 0))...
          destruct (ixm (Embed 1 = 0))...
        * exists <c, 1>. split.
          apply BUnionI2. apply CProdI... zfc_simple.
          destruct (ixm (Embed 1 = 0))...
  }
  apply bijection_is_func in Hbi as HF. destruct HF as [HF _].
  exists F. split... unfold LoAdd. simpl.
  intros x Hx y Hy. unfold F.
  rewrite meta_func_ap, meta_func_ap...
  split; intros Hxy.
  - destruct (ixm (π2 x = 0));
    destruct (ixm (π2 y = 0));
    apply BUnionE in Hx as [Hx|Hx];
    apply BUnionE in Hy as [Hy|Hy];
    apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]];
    apply CProdE1 in Hy as [c [Hc [d [Hd Hy]]]];
    apply SingE in Hb; apply SingE in Hd; subst; zfc_simple;
    (apply BUnionE in Hxy as [Hxy|Hxy]; [
      apply BUnionE in Hxy as [Hxy|Hxy];
      apply ReplAx in Hxy as H; destruct H as [p [Hp H]]; 
      apply op_iff in H as [H1 H2];
      apply op_iff in H1 as [H1 H1'];
      apply op_iff in H2 as [H2 H2']; subst; zfc_simple
    |]).
    + apply BUnionE in Hp as [Hp|Hp].
      * apply BUnionE in Hp as [Hp|Hp];
        apply ReplAx in Hp as [q [Hq H]];
        apply BUnionE in Ha as [Ha|Ha];
        apply BUnionE in Hc as [Hc|Hc];
        apply CProdE1 in Ha as [s [Hs [t [Ht Ha]]]];
        apply CProdE1 in Hc as [u [Hu [v [Hv Hc]]]];
        apply SingE in Ht; apply SingE in Hv; subst; zfc_simple;
        apply op_iff in Ha as []; apply op_iff in Hc as []...
        -- destruct (ixm (Embed 0 = 0))...
           apply BUnionI1. apply BUnionI1.
           apply ReplAx. exists q; split...
        -- destruct (ixm (Embed 1 = 0))...
           apply BUnionI1. apply BUnionI2. apply ReplAx.
           exists <<π1 q, 0>, <π2 q, 0>>. split; zfc_simple.
           apply BUnionI1. apply BUnionI1.
           apply ReplAx. exists q; split...
      * apply CProdE1 in Hp as [s [Hs [t [Ht Hp]]]];
        apply CProdE1 in Hs as [u [Hu [v [Hv Hs]]]];
        apply CProdE1 in Ht as [x [Hx [y [Hy Ht]]]];
        apply SingE in Hv; apply SingE in Hy; subst; zfc_simple.
        destruct (ixm (Embed 0 = 0))...
        destruct (ixm (Embed 1 = 0))...
        apply BUnionI2. apply CProdI; apply CProdI...
        apply BUnionI1. apply CProdI...
    + apply CProdE1 in Hxy as [s [Hs [t [Ht Hxy]]]].
      apply op_iff in Hxy as [_ H]. subst.
      apply CProdE2 in Ht as [_ H]. apply SingE in H...
    + apply CProdE1 in Hxy as [s [Hs [t [Ht Hxy]]]].
      apply op_iff in Hxy as []; subst.
      apply CProdE2 in Hs as [Hs _].
      apply BUnionE in Hs as [];
      apply CProdE1 in H as [x [Hx [y [Hy H]]]];
      apply SingE in Hy; subst; zfc_simple.
      * destruct (ixm (Embed 0 = 0))...
        apply BUnionI2. apply CProdI; apply CProdI... apply BUnionI2...
      * destruct (ixm (Embed 1 = 0))...
        apply BUnionI1. apply BUnionI2. apply ReplAx.
        exists <<x, 0>, <c, 1>>. split; zfc_simple.
        apply BUnionI2. apply CProdI; apply CProdI...
    + apply CProdE1 in Hxy as [s [Hs [t [Ht Hxy]]]].
      apply op_iff in Hxy as [_ H]. subst.
      apply CProdE2 in Ht as [_ H]. apply SingE in H...
    + apply BUnionI1. apply BUnionI2. apply ReplAx.
      exists <<π1 p, 1>, <π2 p, 1>>. split; zfc_simple.
      apply BUnionI1. apply BUnionI2...
    + apply CProdE2 in Hxy as [H _].
      apply CProdE2 in H as [_ H]. apply SingE in H...
  - destruct (ixm (π2 x = 0));
    destruct (ixm (π2 y = 0));
    apply BUnionE in Hx as [Hx|Hx];
    apply BUnionE in Hy as [Hy|Hy];
    apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]];
    apply CProdE1 in Hy as [c [Hc [d [Hd Hy]]]];
    apply SingE in Hb; apply SingE in Hd; subst; zfc_simple;
    (apply BUnionE in Hxy as [Hxy|Hxy]; [
      apply BUnionE in Hxy as [Hxy|Hxy];
      apply ReplAx in Hxy as H; destruct H as [p [Hp H]]; 
      apply op_iff in H as [H1 H2];
      destruct (ixm (π2 a = 0));
      destruct (ixm (π2 c = 0));
      apply op_iff in H1 as [H1 H1'];
      apply op_iff in H2 as [H2 H2'];
      subst; zfc_simple
    |]);
    try (apply BUnionE in Ha as [Ha|Ha];
      apply CProdE1 in Ha as [s [Hs [t [Ht Ha]]]];
      apply SingE in Ht);
    try (apply BUnionE in Hc as [Hc|Hc];
      apply CProdE1 in Hc as [u [Hu [v [Hv Hc]]]];
      apply SingE in Hv);
    subst; zfc_simple;
    destruct (ixm (Embed 0 = 0));
    destruct (ixm (Embed 1 = 0))...
    + destruct (ixm (Embed 0 = 0))...
      apply BUnionI1. apply BUnionI1. apply ReplAx.
      exists <<s, 0>, <u, 0>>. split; zfc_simple.
      apply BUnionI1. apply BUnionI1...
    + apply BUnionE in Hp as [Hp|Hp].
      * apply BUnionE in Hp as [Hp|Hp];
        apply ReplAx in Hp as [q [Hq H]]; subst; zfc_simple;
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst;
        apply BUnionI1; apply BUnionI1; apply ReplAx;
        exists <<π1 q, 1>, <π2 q, 1>>; split; zfc_simple.
        apply BUnionI1. apply BUnionI2.
        apply ReplAx. exists q. split...
      * apply CProdE0 in Hp as [_ H]. apply CProdE0 in H as [_ H].
        rewrite H2 in H. zfc_simple. apply SingE in H...
    + apply CProdE1 in Hxy as [a [Ha [b [Hb H]]]].
      apply op_iff in H as [_ H]. subst.
      apply CProdE2 in Hb as [_ H]. apply SingE in H...
    + apply BUnionI1. apply BUnionI1. apply ReplAx.
      exists <<s, 0>, <u, 1>>. split; zfc_simple.
      apply BUnionI2. apply CProdI; apply CProdI...
    + apply CProdE1 in Hxy as [a [Ha [b [Hb H]]]].
      apply op_iff in H as [_ H]. subst.
      apply CProdE2 in Hb as [_ H]. apply SingE in H...
    + apply CProdE1 in Hxy as [a [Ha [b [Hb H]]]].
      apply op_iff in H as [H _]. subst.
      apply CProdE2 in Ha as [_ H]. apply SingE in H...
    + apply BUnionI2. apply CProdI. apply CProdI...
      apply BUnionI2. apply CProdI... apply CProdI...
    + apply BUnionI2. apply CProdI. apply CProdI...
      apply BUnionI2. apply CProdI... apply CProdI...
    + apply BUnionI2. apply CProdI. apply CProdI...
      apply BUnionI1. apply CProdI... apply CProdI...
    + apply BUnionI2. apply CProdI. apply CProdI...
      apply BUnionI2. apply CProdI... apply CProdI...
    + apply BUnionE in Hp as [Hp|Hp].
      * apply BUnionE in Hp as [Hp|Hp];
        apply ReplAx in Hp as [q [Hq H]]; subst; zfc_simple;
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst;
        apply BUnionI1; apply BUnionI1; apply ReplAx;
        exists <<π1 q, 1>, <π2 q, 1>>; split; zfc_simple.
      * apply CProdE0 in Hp as [_ H]. apply CProdE0 in H as [_ H].
        rewrite H2 in H. zfc_simple. apply SingE in H...
    + apply BUnionE in Hp as [Hp|Hp].
      * apply BUnionE in Hp as [Hp|Hp];
        apply ReplAx in Hp as [q [Hq H]]; subst; zfc_simple;
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst;
        apply BUnionI1; apply BUnionI1; apply ReplAx;
        exists <<π1 q, 1>, <π2 q, 1>>; split; zfc_simple.
      * apply CProdE0 in Hp as [_ H]. apply CProdE0 in H as [_ H].
        rewrite H2 in H. zfc_simple. apply SingE in H...
    + apply CProdE2 in Hxy as [H _].
      apply CProdE2 in H as [_ H]. apply SingE in H...
    + apply CProdE2 in Hxy as [H _].
      apply CProdE2 in H as [_ H]. apply SingE in H...
    + apply BUnionE in Hp as [Hp|Hp].
      * apply BUnionE in Hp as [Hp|Hp];
        apply ReplAx in Hp as [q [Hq H]]; subst; zfc_simple;
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst...
        apply BUnionI1. apply BUnionI2. apply ReplAx.
        exists q. split; zfc_simple.
      * apply CProdE0 in Hp as [H _]. rewrite H1 in H.
        apply CProdE0 in H as [_ H]. zfc_simple. apply SingE in H...
    + apply BUnionE in Hp as [Hp|Hp].
      * apply BUnionE in Hp as [Hp|Hp];
        apply ReplAx in Hp as [q [Hq H]]; subst; zfc_simple;
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst...
        apply BUnionI1. apply BUnionI2. apply ReplAx.
        exists q. split; zfc_simple.
      * apply CProdE0 in Hp as [H _]. rewrite H1 in H.
        apply CProdE0 in H as [_ H]. zfc_simple. apply SingE in H...
    + apply BUnionE in Hp as [Hp|Hp].
      * apply BUnionE in Hp as [Hp|Hp];
        apply ReplAx in Hp as [q [Hq H]]; subst; zfc_simple;
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst...
        apply BUnionI1. apply BUnionI2. apply ReplAx.
        exists q. split; zfc_simple.
      * apply CProdE0 in Hp as [H _]. rewrite H1 in H.
        apply CProdE0 in H as [_ H]. zfc_simple. apply SingE in H...
    + apply BUnionE in Hp as [Hp|Hp].
      * apply BUnionE in Hp as [Hp|Hp];
        apply ReplAx in Hp as [q [Hq H]]; subst; zfc_simple;
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst...
        apply BUnionI1. apply BUnionI2. apply ReplAx.
        exists q. split; zfc_simple.
      * apply CProdE0 in Hp as [H _]. rewrite H1 in H.
        apply CProdE0 in H as [_ H]. zfc_simple. apply SingE in H...
    + apply CProdE2 in Hxy as [H _].
      apply CProdE2 in H as [_ H]. apply SingE in H...
Qed.

Lemma loMul_assoc : ∀ S T U, S ⋅ T ⋅ U ≅ S ⋅ (T ⋅ U).
Proof with auto; try congruence.
  intros. unfold LoMul. simpl.
  set (A S × A T × A U) as Dom.
  set (A S × (A T × A U)) as Ran.
  set (Func Dom Ran (λ x, <π1 (π1 x), <π2 (π1 x), π2 x>>)) as F.
  assert (Hbi: F: Dom ⟺ Ran). {
    apply meta_bijective.
    - intros x Hx.
      apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]].
      apply CProdE1 in Ha as [c [Hc [d [Hd Ha]]]].
      subst. zfc_simple. apply CProdI... apply CProdI...
    - intros x1 H1 x2 H2 Heq.
      apply CProdE1 in H1 as [a [Ha [b [Hb H1]]]].
      apply CProdE1 in Ha as [c [Hc [d [Hd Ha]]]].
      apply CProdE1 in H2 as [s [Hs [t [Ht H2]]]].
      apply CProdE1 in Hs as [u [Hu [v [Hv Hs]]]].
      subst. zfc_simple.
      apply op_iff in Heq as [H1 H2].
      apply op_iff in H2 as [H2 H3]...
    - intros y Hy.
      apply CProdE1 in Hy as [a [Ha [b [Hb Hy]]]].
      apply CProdE1 in Hb as [c [Hc [d [Hd Hb]]]].
      exists <<a, c>, d>. split. apply CProdI... apply CProdI...
      subst. zfc_simple.
  }
  apply bijection_is_func in Hbi as HF. destruct HF as [HF _].
  exists F. split... unfold LoAdd. simpl.
  intros x Hx y Hy. unfold F.
  rewrite meta_func_ap, meta_func_ap...
  apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]].
  apply CProdE1 in Ha as [c [Hc [d [Hd Ha]]]].
  apply CProdE1 in Hy as [s [Hs [t [Ht Hy]]]].
  apply CProdE1 in Hs as [u [Hu [v [Hv Hs]]]].
  split; intros Hxy; apply binRelI; subst; zfc_simple;
  try (apply CProdI; auto; apply CProdI; auto).
  - apply binRelE1 in Hxy as [a [Ha [s [Hs [H [Hlt|[Hlt Heq]]]]]]];
    apply op_iff in H as []; subst; zfc_simple.
    + left. apply binRelI. apply CProdI... apply CProdI...
      left. zfc_simple.
    + apply binRelE1 in Hlt as [k [Hk [l [Hl [H' [Hlt|[Hlt Heq']]]]]]];
      apply op_iff in H' as []; subst; zfc_simple.
      * left. apply binRelI. apply CProdI... apply CProdI...
        right. zfc_simple...
      * right. split...
  - apply binRelE1 in Hxy as [a [Ha [s [Hs [H [Hlt|[Hlt Heq]]]]]]];
    apply op_iff in H as []; subst; zfc_simple.
    + apply binRelE1 in Hlt as [k [Hk [l [Hl [H' [Hlt|[Hlt Heq']]]]]]];
      apply op_iff in H' as []; subst; zfc_simple. left...
      right. split... apply binRelI. apply CProdI... apply CProdI...
      left. zfc_simple...
    + apply op_iff in Heq as []; subst.
      right. split... apply binRelI. apply CProdI... apply CProdI...
      right. zfc_simple...
Qed.

Lemma loMul_distr : ∀ S T U, S ⋅ (T + U) ≅ S ⋅ T + S ⋅ U.
Proof with auto; try congruence.
  intros. unfold LoMul. unfold LoAdd at 4. simpl.
  unfold LoDisj_A. simpl.
  set (A S × (A T × ⎨0⎬ ∪ A U × ⎨1⎬)) as Dom.
  set ((A S × A T) × ⎨0⎬ ∪ (A S × A U) × ⎨1⎬) as Ran.
  set (Func Dom Ran (λ x, match (ixm (π2 (π2 x) = 0)) with
    | inl _ => <π1 x, π1 (π2 x), 0>
    | inr _ => <π1 x, π1 (π2 x), 1> end
  )) as F.
  pose proof contra_0_1 as H01.
  pose proof contra_1_0 as H10.
  assert (Hbi: F: Dom ⟺ Ran). {
    apply meta_bijective.
    - intros x Hx.
      apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]].
      apply BUnionE in Hb as [];
      apply CProdE1 in H as [c [Hc [d [Hd H]]]];
      apply SingE in Hd; subst; zfc_simple.
      + destruct (ixm (Embed 0 = 0))...
        apply BUnionI1. apply CProdI... apply CProdI...
      + destruct (ixm (Embed 1 = 0))...
        apply BUnionI2. apply CProdI... apply CProdI...
    - intros x1 H1 x2 H2 Heq.
      apply CProdE1 in H1 as [a [Ha [b [Hb H1]]]].
      apply CProdE1 in H2 as [c [Hc [d [Hd H2]]]].
      apply BUnionE in Hb as [];
      apply CProdE1 in H as [s [Hs [t [Ht Hb]]]];
      apply BUnionE in Hd as [];
      apply CProdE1 in H as [u [Hu [v [Hv Hd]]]];
      apply SingE in Ht; apply SingE in Hv; subst; zfc_simple;
      destruct (ixm (Embed 0 = 0));
      destruct (ixm (Embed 1 = 0)); try congruence;
      apply op_iff in Heq as [H1 H2];
      apply op_iff in H1 as []...
    - intros y Hy. apply BUnionE in Hy as [];
      apply CProdE1 in H as [a [Ha [b [Hb H]]]];
      apply CProdE1 in Ha as [c [Hc [d [Hd Ha]]]];
      apply SingE in Hb; subst; zfc_simple.
      + exists <c, <d, 0>>. split; zfc_simple.
        apply CProdI... apply BUnionI1. apply CProdI...
        destruct (ixm (Embed 0 = 0))...
      + exists <c, <d, 1>>. split; zfc_simple.
        apply CProdI... apply BUnionI2. apply CProdI...
        destruct (ixm (Embed 1 = 0))...
  }
  apply bijection_is_func in Hbi as HF. destruct HF as [HF _].
  exists F. split... unfold LoAdd. simpl.
  intros x Hx y Hy. unfold F.
  rewrite meta_func_ap, meta_func_ap...
  split; intros Hxy;
  apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]];
  apply CProdE1 in Hy as [c [Hc [d [Hd Hy]]]];
  apply BUnionE in Hb as [];
  apply CProdE1 in H as [s [Hs [t [Ht Hb]]]];
  apply BUnionE in Hd as [];
  apply CProdE1 in H as [u [Hu [v [Hv Hd]]]];
  apply SingE in Ht; apply SingE in Hv; subst; zfc_simple;
  destruct (ixm (Embed 0 = 0));
  destruct (ixm (Embed 1 = 0))...
  - apply BUnionI1. apply BUnionI1. apply ReplAx.
    exists <<a, s>, <c, u>>. split; zfc_simple.
    apply binRelI. apply CProdI... apply CProdI...
    apply binRelE3 in Hxy as []; zfc_simple.
    + apply BUnionE in H as [].
      * apply BUnionE in H as []; apply ReplAx in H as [x [Hx H]];
        apply op_iff in H as [H1 H2];
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst... left.
        unfold relLt. rewrite <- (rel_pair (R T))...
        eapply binRel_is_rel. apply lo.
      * apply CProdE2 in H as [_ H].
        apply CProdE2 in H as [_ H]. apply SingE in H...
    + destruct H as [H1 H2]. apply op_iff in H2 as []; subst. right...
  - apply BUnionI2. apply CProdI; apply CProdI; auto; apply CProdI...
  - apply binRelE3 in Hxy as []; zfc_simple.
    + apply BUnionE in H as [].
      * apply BUnionE in H as []; apply ReplAx in H as [x [Hx H]];
        apply op_iff in H as [H1 H2];
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst...
      * apply CProdE2 in H as [_ H].
        apply CProdE2 in H as [_ H]. apply SingE in H...
    + destruct H as [H1 H2]. apply op_iff in H2 as []; subst...
  - apply BUnionI1. apply BUnionI2. apply ReplAx.
    exists <<a, s>, <c, u>>. split; zfc_simple.
    apply binRelI. apply CProdI... apply CProdI...
    apply binRelE3 in Hxy as []; zfc_simple.
    + apply BUnionE in H as [].
      * apply BUnionE in H as []; apply ReplAx in H as [x [Hx H]];
        apply op_iff in H as [H1 H2];
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst... left.
        unfold relLt. rewrite <- (rel_pair (R U))...
        eapply binRel_is_rel. apply lo.
      * apply CProdE2 in H as [H _].
        apply CProdE2 in H as [_ H]. apply SingE in H...
    + destruct H as [H1 H2]. apply op_iff in H2 as []; subst...
  - apply binRelI; zfc_simple.
    + apply CProdI... apply BUnionI1. apply CProdI...
    + apply CProdI... apply BUnionI1. apply CProdI...
    + apply BUnionE in Hxy as [].
      * apply BUnionE in H as []; apply ReplAx in H as [x [Hx H]];
        apply op_iff in H as [H1 H2];
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst...
        apply binRelE1 in Hx as [b [Hb [d [Hd [Hx [Hlt|[Hlt Heq]]]]]]];
        subst; zfc_simple; subst; zfc_simple.
        -- left. apply BUnionI1. apply BUnionI1. apply ReplAx.
           exists <s, u>. split; zfc_simple...
        -- right. split...
      * apply CProdE2 in H as [_ H].
        apply CProdE2 in H as [_ H]. apply SingE in H...
  - apply binRelI; zfc_simple.
    + apply CProdI... apply BUnionI1. apply CProdI...
    + apply CProdI... apply BUnionI2. apply CProdI...
    + left. apply BUnionI2. apply CProdI; apply CProdI...
  - apply binRelI; zfc_simple.
    + apply CProdI... apply BUnionI2. apply CProdI...
    + apply CProdI... apply BUnionI1. apply CProdI...
    + apply BUnionE in Hxy as [].
      * apply BUnionE in H as []; apply ReplAx in H as [x [Hx H]];
        apply op_iff in H as [H1 H2];
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst...
      * apply CProdE2 in H as [_ H].
        apply CProdE2 in H as [_ H]. apply SingE in H...
  - apply binRelI; zfc_simple.
    + apply CProdI... apply BUnionI2. apply CProdI...
    + apply CProdI... apply BUnionI2. apply CProdI...
    + apply BUnionE in Hxy as [].
      * apply BUnionE in H as []; apply ReplAx in H as [x [Hx H]];
        apply op_iff in H as [H1 H2];
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst...
        apply binRelE1 in Hx as [b [Hb [d [Hd [Hx [Hlt|[Hlt Heq]]]]]]];
        subst; zfc_simple; subst; zfc_simple.
        -- left. apply BUnionI1. apply BUnionI2. apply ReplAx.
           exists <s, u>. split; zfc_simple...
        -- right. split...
      * apply CProdE2 in H as [H _].
        apply CProdE2 in H as [_ H]. apply SingE in H...
Qed.

Import StructureCasting.

Lemma loAdd_ident : ∀ S, S + LOⁿ 0 ≅ S.
Proof with auto; try congruence.
  intros. unfold LoAdd. simpl.
  unfold LoDisj_A. simpl.
  set (A S × ⎨0⎬ ∪ 0 × ⎨1⎬) as Dom.
  set (Func Dom (A S) (λ x, match (ixm (π2 x = 0)) with
    | inl _ => π1 x
    | inr _ => ∅ end
  )) as F.
  pose proof contra_0_1 as H01.
  pose proof contra_1_0 as H10.
  assert (Hbi: F: Dom ⟺ A S). {
    apply meta_bijective.
    - intros x Hx.
      apply BUnionE in Hx as []; destruct (ixm (π2 x = 0));
      apply CProdE0 in H as []...
      apply SingE in H0... exfalso0. exfalso0.
    - intros x1 H1 x2 H2 Heq.
      destruct (ixm (π2 x1 = 0)) as [Hx1|Hx1];
      destruct (ixm (π2 x2 = 0)) as [Hx2|Hx2];
      apply BUnionE in H1 as [H1|H1];
      apply BUnionE in H2 as [H2|H2];
      apply CProdE1 in H1 as [a [Ha [b [Hb H1]]]];
      apply CProdE1 in H2 as [c [Hc [d [Hd H2]]]];
      apply SingE in Hb; apply SingE in Hd; subst; zfc_simple.
      exfalso0. exfalso0. exfalso0.
    - intros y Hy. exists <y, 0>. split.
      + apply BUnionI1. apply CProdI...
      + zfc_simple. destruct (ixm (Embed 0 = 0))...
  }
  apply bijection_is_func in Hbi as HF. destruct HF as [HF _].
  exists F. split; simpl...
  intros x Hx y Hy. unfold F.
  rewrite meta_func_ap, meta_func_ap...
  split; intros Hxy;
  destruct (ixm (π2 x = 0));
  destruct (ixm (π2 y = 0));
  apply BUnionE in Hx as [Hx|Hx];
  apply BUnionE in Hy as [Hy|Hy];
  apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]];
  apply CProdE1 in Hy as [c [Hc [d [Hd Hy]]]];
  apply SingE in Hb; apply SingE in Hd; subst; zfc_simple;
  [(apply BUnionE in Hxy as [Hxy|Hxy]; [
    apply BUnionE in Hxy as [Hxy|Hxy];
    apply ReplAx in Hxy as [p [Hp H]]; 
    apply op_iff in H as [H1 H2];
    apply op_iff in H1 as [H1 H1'];
    apply op_iff in H2 as [H2 H2']; subst; zfc_simple
  |])..| | | |]; try exfalso0.
  - unfold relLt. rewrite <- (rel_pair (R S))...
    eapply binRel_is_rel. apply lo.
  - apply CProdE2 in Hxy as [_ H].
    apply CProdE2 in H as [_ H]. apply SingE in H...
  - apply BUnionI1. apply BUnionI1. apply ReplAx.
    exists <a, c>. split; zfc_simple...
Qed.

Lemma loMul_ident : ∀ S, S ⋅ LOⁿ 1 ≅ S.
Proof with nauto; try congruence.
  intros. unfold LoMul. simpl.
  set (Func (A S × 1) (A S) π1) as F.
  assert (Hbi: F: A S × 1 ⟺ A S). {
    apply meta_bijective.
    - intros x Hx. apply CProdE0 in Hx as []...
    - intros x1 H1 x2 H2 Heq.
      apply CProdE1 in H1 as [a [Ha [b [Hb H1]]]].
      apply CProdE1 in H2 as [c [Hc [d [Hd H2]]]].
      rewrite one in Hb, Hd.
      apply SingE in Hb. apply SingE in Hd. subst. zfc_simple.
    - intros y Hy. exists <y, 0>. split; zfc_simple.
      apply CProdI... apply BUnionI2...
  }
  apply bijection_is_func in Hbi as HF. destruct HF as [HF _].
  exists F. split; simpl...
  intros x Hx y Hy. unfold F.
  rewrite meta_func_ap, meta_func_ap...
  apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]].
  apply CProdE1 in Hy as [c [Hc [d [Hd Hy]]]].
  rewrite one in Hb, Hd.
  apply SingE in Hb. apply SingE in Hd. subst. zfc_simple.
  split; intros Hxy.
  - apply binRelE3 in Hxy as [|[]]; zfc_simple.
    apply SepE2 in H. zfc_simple.
    exfalso. apply (nat_irrefl ∅)...
  - apply binRelI; zfc_simple.
    apply CProdI... apply BUnionI2...
    apply CProdI... apply BUnionI2...
    right. split...
Qed.

Lemma loMul_0 : ∀ S, S ⋅ LOⁿ 0 ≅ LOⁿ 0.
Proof with auto; try congruence.
  intros. unfold LoMul. simpl.
  exists ∅. split; simpl.
  rewrite cprod_0_r. apply empty_bijective.
  intros x Hx. apply CProdE0 in Hx as [_ H]. exfalso0.
Qed.

Open Scope OrderType_scope.

Theorem otAdd_assoc : ∀ ρ σ τ, is_ot ρ → is_ot σ → is_ot τ → 
  ρ + σ + τ = ρ + (σ + τ).
Proof with auto.
  intros * [S HS] [T HT] [U HU]. subst.
  do 4 rewrite otAdd_eq_ot_of_loAdd.
  apply ot_correct. apply loAdd_assoc.
Qed.

Theorem otMul_assoc : ∀ ρ σ τ, is_ot ρ → is_ot σ → is_ot τ → 
  ρ ⋅ σ ⋅ τ = ρ ⋅ (σ ⋅ τ).
Proof with auto.
  intros * [S HS] [T HT] [U HU]. subst.
  do 4 rewrite otMul_eq_ot_of_loMul.
  apply ot_correct. apply loMul_assoc.
Qed.

Theorem otMul_distr : ∀ ρ σ τ, is_ot ρ → is_ot σ → is_ot τ → 
  ρ ⋅ (σ + τ) = ρ ⋅ σ + ρ ⋅ τ.
Proof with auto.
  intros * [S HS] [T HT] [U HU]. subst.
  rewrite (otAdd_eq_ot_of_loAdd T U).
  rewrite (otMul_eq_ot_of_loMul S T).
  rewrite (otMul_eq_ot_of_loMul S U).
  rewrite otMul_eq_ot_of_loMul.
  rewrite otAdd_eq_ot_of_loAdd.
  apply ot_correct. apply loMul_distr.
Qed.

Theorem otAdd_ident : ∀ ρ, is_ot ρ → ρ + otⁿ 0 = ρ.
Proof with auto.
  intros ρ [S HS]. subst.
  unfold otⁿ. rewrite otAdd_eq_ot_of_loAdd.
  apply ot_correct. apply loAdd_ident.
Qed.

Theorem otMul_ident : ∀ ρ, is_ot ρ → ρ ⋅ otⁿ 1 = ρ.
Proof with auto.
  intros ρ [S HS]. subst.
  unfold otⁿ. rewrite otMul_eq_ot_of_loMul.
  apply ot_correct. apply loMul_ident.
Qed.

Theorem otMul_0 : ∀ ρ, is_ot ρ → ρ ⋅ otⁿ 0 = otⁿ 0.
Proof with auto.
  intros ρ [S HS]. subst.
  unfold otⁿ. rewrite otMul_eq_ot_of_loMul.
  apply ot_correct. apply loMul_0.
Qed.
