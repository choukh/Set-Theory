(** Solutions to "Elements of Set Theory" Chapter 7 Part 3 **)
(** Coq coding by choukh, Dec 2020 **)

Require Export ZFC.EST7_4.
Require Import ZFC.lib.FuncFacts.

Import WOStruct.
Import WOStruct.EpsilonImage.
Hint Immediate ord_is_ord : core.

(* ex7_15_a 良序结构不与自身的任意前节同构 *)
Lemma wo_not_iso_seg : ∀ S, ∀t ∈ A S, S ≇ Seg t S.
Proof with eauto.
  intros S t Ht Hiso.
  apply ord_well_defined in Hiso.
  apply (ord_irrefl (ord S))...
  rewrite Hiso at 1. eapply ordI...
  symmetry. apply seg_α...
Qed.

(* ex7_15_b 良序结构的同构关系具有至多三歧性 *)
Theorem wo_iso_at_most_trich : ∀ S T,
  at_most_trich (∃t ∈ A S, Seg t S ≅ T) (S ≅ T) (∃t ∈ A T, S ≅ Seg t T).
Proof with eauto.
  repeat split.
  - intros [[t [Ht H1]] H2].
    eapply wo_not_iso_seg... rewrite H1...
  - intros [[t [Ht H1]] H2].
    eapply wo_not_iso_seg... rewrite <- H1. symmetry...
  - intros [[s [Hs H1]] [t [Ht H2]]].
    apply ord_well_defined in H1.
    apply ord_well_defined in H2.
    rewrite seg_α in H1, H2...
    apply ordI in H1... symmetry in H2.
    apply ordI in H2...
    apply (ord_irrefl (ord S))... eapply ord_trans...
Qed.

(* ex7_16_1 see EST7_4 Lemma ord_suc_preserve_lt *)
(* ex7_16_2 see EST7_4 Lemma ord_suc_injective *)

(* ex7_17 子结构的序数小于等于原结构的序数 *)
Theorem ord_of_sub_struct_leq : ∀ S T, S ⊑ T → ord S ≤ ord T.
Proof with eauto.
  intros * [Has Hrs].
  destruct (classic (ord S = ord T))...
  apply ord_connected in H as []... exfalso.
  apply ord_lt_elim in H as [t [Ht [f [Hf Hopf]]]].
  apply bijection_is_func in Hf as [Hf _].
  destruct (wo S) as [Hlo Hmin].
  set {x ∊ A S | λ x, (f[x] <ᵣ x) (R S)} as B.
  pose proof (Hmin B) as [m [Hm Hle]].
  - exists t. apply SepI...
    assert (Hft: f[t] ∈ A (Seg t S)). {
      eapply ap_ran... apply Has...
    }
    apply SepE2 in Hft...
  - intros x Hx. apply SepE1 in Hx...
  - apply SepE in Hm as [Hm Hlt]. apply Has in Hm.
    assert (Hsub: A (Seg t S) ⊆ A S). {
      intros x Hx. apply SepE1 in Hx...
    }
    assert (Hfm: f[m] ∈ A S). {
      apply Hsub. eapply ap_ran...
    }
    assert (Hfmb: f[m] ∈ B). {
      apply SepI... rewrite Hrs in Hlt. apply SepE1 in Hlt.
      apply Hopf in Hlt... apply SepE1 in Hlt... apply Has...
    }
    assert (H := Hlo). destruct H as [_ [Htr _]].
    apply Hle in Hfmb as []; eapply linearOrder_irrefl...
    rewrite H in Hlt at 2...
Qed.

(* ex7_18 see EST7_4 limit ordinal *)
