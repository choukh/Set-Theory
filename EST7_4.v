(** Based on "Elements of Set Theory" Chapter 7 Part 4 **)
(** Coq coding by choukh, Dec 2020 **)

Require Export ZFC.EST7_3.
Require Import ZFC.lib.FuncFacts.

(*** EST第七章4：序数的定义，序数的序 ***)

Module Export OrdinalNumber.

Section EpsilonImageWellDefined.
Import EpsilonImage.

Local Lemma eq_α : ∀ f A R B S, woset A R → woset B S →
  f: A ⟺ B → order_preserved_func A R f S →
  (∀x ∈ A, (E A R)[x] = (E B S)[f[x]]) → α A R = α B S.
Proof with eauto; try congruence.
  intros * Hwor Hwos Hf Hopf Heq.
  apply e_bijective in Hwor as [[Hf1 _] [Hd1 _]].
  apply e_bijective in Hwos as [[Hf2 _] [Hd2 _]].
  apply inv_bijection in Hf as Hf'.
  apply bijection_is_func in Hf as [Hf [Hif Hrf]].
  apply bijection_is_func in Hf' as [Hf' _].
  unfold α. rewrite ran_eq_repl_by_ap, ran_eq_repl_by_ap...
  apply ExtAx. intros y. split; intros Hy.
  - apply ReplAx in Hy as [x [Hx Hap]]. rewrite Heq in Hap...
    apply ReplAx. exists (f[x]). split... rewrite Hd2.
    eapply ap_ran...
  - apply ReplAx in Hy as [x [Hx Hap]].
    rewrite <- (inv_ran_reduction f Hif x), <- Heq in Hap...
    apply ReplAx. exists (f⁻¹[x]). split...
    rewrite Hd1. eapply ap_ran... eapply ap_ran...
Qed.

Import OrderedStruct.

(* 伊普西隆像良定义 *)
Theorem epsilon_image_well_defined :
  ∀ S T, wo S → wo T → S ≅ T ↔ α S = α T.
Proof with eauto; try congruence.
  intros S T Hwos Hwot. split; revgoals. {
    intros Heq.
    apply wo_iso_epsilon in Hwos.
    apply wo_iso_epsilon in Hwot.
    unfold Epsilon, α, ε, EpsilonImage.ε in Heq, Hwos, Hwot.
    rewrite Heq in Hwos. rewrite <- Hwot in Hwos...
  }
  intros [f [Hf Hopf]].
  eapply eq_α ... intros x Hx.
  set (EpsilonImage.E (A S) (R S)) as E₁.
  set (EpsilonImage.E (A T) (R T)) as E₂.
  set {x ∊ (A S) | λ x, E₁[x] = E₂[f[x]]} as B.
  replace (A S) with B in Hx.
  apply SepE2 in Hx... clear x Hx.
  eapply transfinite_induction...
  split. intros t Ht. apply SepE1 in Ht...
  intros t Ht Hsub. apply SepI...
  assert (Hft: f[t] ∈ A T). {
    eapply ap_ran... apply bijection_is_func...
  }
  unfold E₁, E₂. rewrite e_ap, e_ap... fold E₁ E₂.
  apply ExtAx. split; intros Hx.
  - apply ReplAx in Hx as [s [Hs Heq]]. subst x.
    apply ReplAx. exists (f[s]). split.
    + apply SepE in Hs as [Hs Hlt].
      eapply dom_binRel in Hs; [|apply Hwos].
      apply segI. apply Hopf...
    + apply Hsub in Hs. apply SepE2 in Hs...
  - apply inv_bijection in Hf as Hf'.
    apply bijection_is_func in Hf as [_ [Hi Hr]].
    apply bijection_is_func in Hf' as [Hf' _].
    apply ReplAx in Hx as [s [Hs Heq]]. subst x.
    apply SepE in Hs as [Hs Hlt].
    eapply dom_binRel in Hs; [|apply Hwot].
    apply ReplAx. exists (f⁻¹[s]). split.
    + apply segI. apply Hopf...
      * eapply ap_ran...
      * rewrite inv_ran_reduction...
    + rewrite <- (inv_ran_reduction f) in Hlt...
      apply Hopf in Hlt; [|eapply ap_ran|]...
      assert (f⁻¹[s] ∈ seg t (R S)). {
        apply SepI... eapply domI...
      }
      apply Hsub in H. apply SepE2 in H.
      rewrite inv_ran_reduction in H...
Qed.

End EpsilonImageWellDefined.

Import WOStruct.
Import WOStruct.Inheritance.

(* 序数 *)
Definition ord := λ S, α S.
Definition is_ord := λ α, ∃ S, α = ord S.

(* 序数良定义 *)
Lemma ord_well_defined : ∀ S T, S ≅ T → ord S = ord T.
Proof.
  intros. unfold ord, α.
  apply (epsilon_image_well_defined (parent S) (parent T)).
  apply parent_wo. apply parent_wo. apply H.
Qed.

Lemma ordI : ∀ S t, ∀s ∈ A S, (E S)[s] = t → t ∈ ord S.
Proof. exact α_intro. Qed.

Lemma ordE : ∀ S, ∀t ∈ ord S, ∃s ∈ A S, (E S)[s] = t.
Proof. exact α_elim. Qed.

(* 可以以成员关系良序排列的传递集是序数 *)
Theorem transtive_set_well_ordered_by_epsilon_is_ord :
  ∀ α, trans α → woset α (MemberRel α) → is_ord α.
Proof with eauto.
  intros α Htr Hwo.
  set (constr α (MemberRel α) Hwo) as S.
  cut (∀x ∈ α, (E S)[x] = x). {
    intros H. exists S.
    pose proof (EpsilonImage.e_bijective (A S) (R S)) as [[Hf _] [Hd _]]...
    apply ExtAx. split; intros Hx.
    - apply (ranI _ x). apply func_point...
      rewrite Hd. apply Hx. apply H...
    - apply ranE in Hx as [w Hp].
      apply domI in Hp as Hw. rewrite Hd in Hw.
      apply func_ap in Hp... rewrite H in Hp... subst... 
  }
  intros x Hx.
  set {x ∊ α | λ x, (E S)[x] = x} as B.
  replace α with B in Hx. apply SepE2 in Hx... clear Hx x.
  eapply transfinite_induction. apply (wo S). split.
  intros x Hx. apply SepE1 in Hx...
  intros t Ht Hsub. apply SepI...
  unfold E. rewrite EpsilonImage.e_ap...
  apply ExtAx. split; intros Hx.
  - apply ReplAx in Hx as [s [Hs H1]]. apply Hsub in Hs as Hsb.
    apply SepE in Hsb as [_ H2]. apply SepE in Hs as [_ H].
    unfold E in H2. rewrite <- H2, H1 in H.
    apply binRelE2 in H as [_ [_ H]]...
  - assert (x ∈ seg t (R S)). {
      apply segI. apply binRelI...
    }
    apply ReplAx. exists x. split...
    apply Hsub in H. apply SepE2 in H...
Qed.

(* 序数类是传递类 *)
Theorem ord_tranc : ∀ α, is_ord α → ∀x ∈ α, is_ord x.
Proof.
  intros α [S H] x Hx. subst.
  apply ordE in Hx as [t [Ht Heqx]]. subst x.
  set (Seg t S) as T. exists T.
  symmetry. apply seg_α. apply Ht.
Qed.

(* 序数是传递集 *)
Theorem ord_trans : ∀ α, is_ord α → trans α.
Proof.
  intros α [S H]. subst. apply α_trans.
Qed.

End OrdinalNumber.
