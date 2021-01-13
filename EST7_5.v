(** Based on "Elements of Set Theory" Chapter 7 Part 5 **)
(** Coq coding by choukh, Jan 2021 **)

Require Export ZFC.EST7_4.
Require Import ZFC.lib.Dominate.
Require Import ZFC.lib.Choice.
Require Import ZFC.lib.WosetMin.
Import WosetMin.FullVer.

(*** EST第七章5：哈托格斯数，良序定理，基数的定义，
  良序定理与选择公理、佐恩引理的互推 ***)

Section ImportStruct.

Import OrderedStruct.
Import WOStruct.
Import WOStruct.EpsilonImage.

(* 若集合与给定序数等势，那么可以用该集合构造与该序数同构的良序结构 *)
Lemma set_eqnum_ord_can_be_woset :
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
    apply set_eqnum_ord_can_be_woset in Hqn.
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

(* 哈托格斯数：不被给定集合支配的最小序数 *)
Definition hartog_spec := λ A α, is_ord α ∧ ¬ α ≼ A ∧
  ∀ β, is_ord β → ¬ β ≼ A → α ≤ β.

Definition HartogsNumber := λ A, epsilon (inhabits ∅) (hartog_spec A).

Lemma hartog_spec_intro : ∀ A, hartog_spec A (HartogsNumber A).
Proof.
  intros A. apply (epsilon_spec (inhabits ∅) (hartog_spec A)).
  apply Hartogs'.
Qed.

(* AC cycle
  [3, 5] → WO → 6
*)

(* 良序定理：任意集合都可以良序化 *)
Definition WO := ∀ A, ∃ R, woset A R.

(* ==需要选择公理== *)
Theorem well_ordering : AC_III → WO.
Proof with eauto; try congruence.
  intros AC3 B.
  pose proof (AC3 B) as [G [_ [_ HrG]]].
  set (Extraneous B) as e.
  set (λ f y, y = match (ixm (B - ran f = ∅)) with
    | inl _ => e
    | inr _ => G[B - ran f]
  end) as ϕ.
  specialize hartog_spec_intro with B as [Hα [Hndom _]].
  set (HartogsNumber B) as α. fold α in Hα, Hndom.
  assert (H := Hα). destruct H as [S HS].
  set (Epsilon S) as S'. assert (Heqα: α = A S')...
  pose proof (recrusion_spec_intro S' ϕ) as [HfF [HdF HrF]]. {
    unfold ϕ. intros f. split...
  }
  set (Recursion S' ϕ) as F. fold F in HfF, HdF, HrF.
  assert (Hap0: ∀β ∈ α, F[β] = match ixm (B - F⟦β⟧ = ∅) with
    | inl _ => e
    | inr _ => G[B - F⟦β⟧]
  end). {
    intros β Hβ. replace (F⟦β⟧) with (ran (F ↾ seg β (R S'))).
    apply HrF... replace (seg β (R S')) with β...
    symmetry. apply seg_of_ord... rewrite Heqα in Hβ...
  }
  assert (Hap1: ∀β ∈ α, B - F⟦β⟧ = ∅ → F[β] = e). {
    intros β Hβ H0. rewrite Hap0...
    destruct (ixm (B - F⟦β⟧ = ∅)) as []...
  }
  assert (Hap2: ∀β ∈ α, F[β] ≠ e → F[β] = G [B - F⟦β⟧]). {
    intros β Hβ He. rewrite Hap0...
    destruct (ixm (B - F⟦β⟧ = ∅)) as []...
    exfalso. apply He. apply Hap1...
  }
  assert (Hind0: ∀β ∈ α, F[β] ≠ e → G[B - F⟦β⟧] ∈ B - F⟦β⟧). {
    intros β Hβ He. apply HrG... apply EmptyNE.
    intros H0. apply He... apply Hap1...
  }
  assert (Hind1: ∀ β γ ∈ α, F[β] ≠ e → F[γ] ≠ e →
    γ ∈ β → G[B - F⟦γ⟧] ∈ F⟦β⟧
  ). {
    intros β Hβ γ Hγ H1 H2 Hlt. eapply ranI.
    apply restrI... eapply func_point... rewrite Hap2...
  }
  assert (Hstar: ∀ ξ, ξ ⊆ α → (∀x ∈ ξ, F[x] ≠ e) →
    single_rooted (F ↾ ξ) ∧ ran (F ↾ ξ) ⊆ B
  ). {
    intros ξ Hsub He. split.
    - intros y Hy. split. apply ranE in Hy...
      intros γ β H1 H2.
      apply restrE2 in H1 as [H1 Hγ]. apply Hsub in Hγ as Hγα.
      apply restrE2 in H2 as [H2 Hβ]. apply Hsub in Hβ as Hβα.
      apply func_ap in H1...
      apply func_ap in H2... subst y.
      rewrite Hap2, Hap2 in H2; auto; [|apply He..]...
      destruct (classic (γ = β))... exfalso.
      apply ord_connected in H as [Hlt|Hlt]; [| |eapply ord_is_ords..]...
      * pose proof (Hind0 β Hβα (He β Hβ)).
        apply SepE2 in H. apply H. rewrite H2.
        apply Hind1; [| |apply He..|]...
      * pose proof (Hind0 γ Hγα (He γ Hγ)).
        apply SepE2 in H. apply H. rewrite <- H2.
        apply Hind1; [| |apply He..|]...
    - intros y Hy. apply ranE in Hy as [β Hp].
      apply restrE2 in Hp as [Hp Hβδ].
      apply domI in Hp as Hβ. apply func_ap in Hp...
      subst y. rewrite Hap2; [| |apply He]...
      assert (B - F⟦β⟧ ⊆ B)...
      apply H. apply Hind0... apply He...
  }
  set {x ∊ α | λ x, F[x] = e} as E.
  pose proof (min_correct S' E) as [Hδ Hmin]. {
    destruct (classic (∀x ∈ α, F[x] ≠ e)) as [He|He].
    - exfalso. apply Hndom. exists F.
      assert (HeqF: F = F ↾ α). {
        rewrite Heqα, <- HdF, restr_to_dom... apply HfF.
      }
      split; split; auto; try congruence;
      rewrite HeqF; apply Hstar...
    - apply set_not_all_ex_not in He as [β [Hβ H]].
      exists β. apply SepI... apply NNPP...
  } {
    intros β Hβ. apply SepE1 in Hβ...
  }
  set ((Min S')[E]) as δ. fold δ in Hδ, Hmin.
  apply SepE in Hδ as [Hδ HFδ].
  apply ord_is_ords in Hδ as Hordδ...
  apply ord_lt_iff_psub in Hδ as H... destruct H as [Hsub _].
  assert (H := Hordδ). destruct H as [T HT].
  cut (ord T ≈ B). {
    intros H. apply set_eqnum_ord_can_be_woset
      in H as [T' [HT' _]].
    exists (R T'). rewrite <- HT'...
  }
  assert (He: ∀x ∈ δ, F[x] ≠ e). {
    intros x Hx He.
    assert (x ∈ E). {
      apply SepI... eapply (Ordinals.ord_trans)...
    }
    apply Hmin in H as [].
    - apply binRelE3 in H. eapply ord_not_lt_gt; revgoals...
      eapply ord_is_ords...
    - eapply ord_irrefl...
  }
  rewrite <- HT. exists (F ↾ δ). split; split.
  - apply restr_func...
  - apply Hstar...
  - rewrite Heqα, <- HdF in Hsub.
    apply restr_dom in Hsub...
  - apply sub_antisym. apply Hstar...
    rewrite Hap0 in HFδ...
    destruct (ixm (B - F ⟦δ⟧ = ∅)).
    apply sub_iff_no_comp...
    exfalso. apply (extraneous B).
    fold e. rewrite <- HFδ.
    assert (B - F⟦δ⟧ ⊆ B)... apply H.
    apply HrG... apply EmptyNE...
Qed.

(* 良序集与其序数等势 *)
Lemma woset_eqnum_ord : ∀ S, A S ≈ ord S.
Proof.
  intros. pose proof (iso_epsilon S) as [f [Hf _]].
  exists f. apply Hf.
Qed.

(* ==需要选择公理== *)
(* 任意集合都可以用序数计数 *)
Theorem numeration : AC_III → ∀ A, ∃ α, is_ord α ∧ α ≈ A.
Proof with auto.
  intros AC3 A. pose proof (well_ordering AC3 A) as [R Hwo].
  set (WOStruct.constr A R Hwo) as S.
  exists (ord S). split... rewrite <- woset_eqnum_ord...
Qed.

End ImportStruct.

(* 基数：与给定集合等势的最小序数 *)
Definition card := λ A,
  let α := HartogsNumber A in
  let min := Min α (MemberRel α) in
  min[{ξ ∊ α | λ ξ, ξ ≈ A}].

Notation "| A |" := (card A) (at level 40) : ZFC_scope.

(* ==需要选择公理== *)
Lemma card_well_defined : AC_III →
  ∀ A, |A| ≈ A ∧ is_ord (|A|) ∧
  ∀ β, is_ord β → β ≈ A → |A| ≤ β.
Proof with eauto.
  intros AC3 A.
  set (HartogsNumber A) as α.
  set {ξ ∊ α | λ ξ, ξ ≈ A} as B.
  set ((Min α (MemberRel α))[B]) as μ.
  pose proof (hartog_spec_intro A) as [Hα [Hndom Hle]].
  fold α in Hndom, Hle.
  assert (Hstar: ∀ ξ, is_ord ξ → ξ ≈ A → ξ ∈ α). {
    intros ξ Hξ Hqn. destruct (classic (ξ ∈ α))...
    exfalso. apply ord_leq_iff_neg_lt in H...
    apply ord_leq_iff_sub in H...
    apply dominate_sub in H.
    apply Hndom. eapply dominate_rewrite_r in H...
  }
  assert (Hwo: woset α (MemberRel α)). apply ord_woset...
  pose proof (min_correct α (MemberRel α) B Hwo) as [Hμ Hmin]. {
    pose proof (numeration AC3 A) as [ξ [Hξ Hqn]].
    exists ξ. apply SepI...
  } {
    intros ξ Hξ. apply SepE1 in Hξ...
  }
  fold μ in Hμ, Hmin. split; [|split].
  - apply SepE2 in Hμ...
  - apply SepE1 in Hμ. eapply ord_is_ords...
  - intros β Hβ Hqn. assert (β ∈ B). apply SepI...
    apply Hmin in H as []... apply binRelE3 in H...
Qed.

(* == implicit AC == *)
Theorem CardAx0 : ∀ A, A ≈ |A|.
Proof.
  intros. symmetry. apply card_well_defined. apply ac3.
Qed.

(* == implicit AC == *)
Theorem CardAx1 : ∀ A B, |A| = |B| ↔ A ≈ B.
Proof with eauto.
  split; intros H.
  - rewrite CardAx0, H, <- CardAx0...
  - pose proof (card_well_defined ac3 A) as [Hca [Hoa Hlea]].
    pose proof (card_well_defined ac3 B) as [Hcb [Hob Hleb]].
    rewrite H in Hca at 2. apply Hleb in Hca...
    rewrite <- H in Hcb at 2. apply Hlea in Hcb...
    destruct Hca; destruct Hcb...
    exfalso. eapply ord_not_lt_gt; revgoals...
Qed.

(* == implicit AC == *)
Theorem CardAx2 : ∀ A, finite A → |A| = FinCard A.
Proof with eauto.
  intros A Hfin.
  apply fin_card_correct in Hfin as [n [Hn [Hfin Hqn]]].
  rewrite Hfin. apply CardAx1 in Hqn. rewrite Hqn.
  pose proof (card_well_defined ac3 n) as [Hqnn [Hocn Hle]].
  assert (Hon: is_ord n). apply nat_is_ord...
  pose proof (Hle n) as []...
  exfalso. apply ord_lt_iff_psub in H...
  apply no_fin_set_eqnum_its_proper_subset in H.
  apply H. rewrite Hqnn... apply nat_finite...
Qed.
