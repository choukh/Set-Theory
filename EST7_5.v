(** Based on "Elements of Set Theory" Chapter 7 Part 5 **)
(** Coq coding by choukh, Jan 2021 **)

Require Export ZFC.EST7_4.
Require Import ZFC.lib.Dominate.
Require Import ZFC.lib.Choice.

(*** EST第七章5：哈托格斯定理，良序定理 ***)

Import OrderedStruct.
Import WOStruct.
Import WOStruct.EpsilonImage.

(* 存在与给定序数等势且同构的结构 *)
Lemma exists_struct_eqnum_and_iso_to_given_ord :
  ∀ S B, ord S ≈ B → ∃ T, A T = B ∧ S ≅ T.
Proof with auto.
  intros S B Hqn.
  symmetry in Hqn. destruct Hqn as [f Hf].
  set (BinRel B (λ x y, f[x] ∈ f[y])) as R.
  set (OrderedStruct.constr B R (binRel_is_binRel _ _)) as T.
  (* order_embedding *)
  assert (Hoeb: ∀ x y ∈ B, (x <ᵣ y) R ↔ (f[x] <ᵣ f[y]) (ε S)). {
    intros x Hx y Hy. split; intros Hlt.
    - apply binRelE3 in Hlt.
      apply SepI; zfcrewrite.
      apply CProdI; eapply ap_ran; eauto; apply bijection_is_func...
    - apply binRelE3 in Hlt. apply binRelI...
  }
  assert (Hiso: (parent (Epsilon S) ≅ T)%os). {
    symmetry. exists f. split...
  }
  apply iso_wo in Hiso as Hwo; [|apply parent_wo].
  set (constr B R Hwo) as T'.
  exists T'. split... rewrite iso_epsilon. symmetry.
  exists f. split...
Qed.

(* 哈托格斯定理：对任意集合存在不被其支配的最小序数 *)
Theorem Hartogs' : ∀ A, ∃ α, is_ord α ∧ ¬ α ≼ A ∧
  ∀ β, is_ord β → ¬ β ≼ A → α ≤ β.
Proof with eauto; try congruence.
  intros B.
  set {w ∊ 𝒫 B × 𝒫 (B × B) | λ w, woset (π1 w) (π2 w)} as W.
  set (λ w α, ∃ S, α = ord S ∧ π1 w = A S ∧ π2 w = R S) as ϕ.
  set (ϕ_Repl ϕ W) as Ω.
  set {β ∊ Ω | λ β, β ≼ B} as α.
  assert (Hexu: ∀w ∈ W, ∃! y, ϕ w y). {
    intros w Hw. split.
    - apply SepE2 in Hw.
      set (WOStruct.constr (π1 w) (π2 w) Hw) as S.
      exists (ord S), S...
    - intros y1 y2 [S [HAS [HRS H1]]] [T [HAT [HRT H2]]].
      subst. f_equal. apply eq_intro...
  }
  assert (Hstar: ∀β ∈ α, β ≼ B ∧ (∃w ∈ W, ϕ w β)). {
    intros β Hβ. apply SepE in Hβ as [Hβ Hdom].
    apply ϕ_ReplAx in Hβ as []...
  }
  assert (Hords: is_ords α). {
    intros β Hβ. apply Hstar in Hβ as [_ [_ [_ [S [H _]]]]]. subst... 
  }
  assert (Hα: is_ord α). {
    apply transitive_set_of_ords_is_ord...
    intros γ β Hγ Hβ. apply SepI.
    - apply Hstar in Hβ as [_ [w [Hw [S [Heqβ [HA HR]]]]]].
      apply ϕ_ReplAx... rewrite Heqβ in Hγ.
      apply α_elim in Hγ as [t [Ht Hap]].
      exists <A (Seg t S), R (Seg t S)>. split.
      + apply SepI; zfcrewrite...
        apply SepE1 in Hw. apply CProdE0 in Hw as [H1 H2].
        rewrite HA in H1. apply PowerAx in H1.
        rewrite HR in H2. apply PowerAx in H2.
        apply CProdI; apply PowerAx.
        * intros x Hx. apply SepE1 in Hx. apply H1...
        * intros x Hx. apply SepE1 in Hx. apply H2...
      + rewrite <- seg_α in Hap...
        exists (Seg t S); zfcrewrite...
    - apply Hords in Hβ as Hoβ.
      apply ord_is_ords in Hγ as Hoγ...
      apply (dominate_tran γ β)... apply dominate_sub.
      apply ord_lt_iff_psub... apply Hstar...
  }
  exists α. repeat split...
  - intros Hdom. eapply ord_irrefl...
    apply SepI... apply ϕ_ReplAx...
    apply dominate_iff in Hdom as [C [Hsub Hqn]].
    destruct Hα as [S HS]. rewrite HS in Hqn.
    apply exists_struct_eqnum_and_iso_to_given_ord in Hqn.
    destruct Hqn as [T [Heq Hiso]]. subst C.
    exists <A T, R T>. split.
    + apply SepI; zfcrewrite... apply CProdI; apply PowerAx...
      destruct (wo T) as [[Hbr _] _].
      intros x Hx. apply Hbr in Hx.
      apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]]. subst x.
      apply CProdI; apply Hsub...
    + exists T; zfcrewrite. split...
      rewrite HS. apply ord_well_defined...
  - intros β Hβ Hneg. apply ord_leq_iff_neg_lt...
    intros Hβα. apply Hneg. apply SepE2 in Hβα...
Qed.

(* ==需要选择公理== *)
(* 良序定理：任意集合都存在良序 *)
Theorem well_ordering : AC_III → ∀ A, ∃ R, woset A R.
Proof with auto.
  intros AC3 A.
Admitted.
