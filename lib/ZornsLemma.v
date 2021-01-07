(** Coq coding by choukh, Jan 2021 **)

Require Import ZFC.EST7_4.
Require Import ZFC.lib.Cardinal.
Require Import ZFC.lib.OrdinalAsType.

(* set-theoretic form *)
Definition set_theoretic_Zorn := EST6_4.AC_VI.

(* general form *)
Definition general_Zorn := ∀ A R, poset A R →
  (∀ B, B ⊆ A → loset B (R ⥏ B) → ∃ u, upperBound u B A R) →
  ∃ m, maximal m A R.

(* nonempty form *)
Definition nonempty_Zorn := ∀ A R, ⦿ A → poset A R →
  (∀ B, ⦿ B → B ⊆ A → loset B (R ⥏ B) → ∃ u, upperBound u B A R) →
  ∃ m, maximal m A R.

(* 链是全序集 *)
Lemma chain_is_loset : ∀ A, is_chain A ↔ loset A (SubsetRel A).
Proof with eauto; try congruence.
  split.
  - intros Hchn. apply loset_iff_connected_poset.
    split; [|apply subsetRel_is_poset].
    intros a Ha b Hb Hnq.
    pose proof (Hchn a Ha b Hb) as []; [left|right]; apply binRelI...
  - intros Hlo x Hx y Hy.
    destruct (classic (x = y)) as [|Hnq]. left...
    eapply lo_connected in Hnq as H... destruct H.
    * apply binRelE2 in H as [_ [_ []]]...
    * apply binRelE2 in H as [_ [_ []]]...
Qed.

(* 集合的包含关系在子集上的限制等于子集的包含关系 *)
Lemma subRel_of_subselRel : ∀ A B, B ⊆ A →
  (SubsetRel A) ⥏ B = SubsetRel B.
Proof with auto.
  intros A B Hsub.
  apply ExtAx. split; intros Hx.
  - apply SepE in Hx as [Hx Hp].
    apply CProdE1 in Hp as [a [Ha [b [Hb Hp]]]]. subst x.
    apply binRelE2 in Hx as [_ [_ H]]. apply binRelI...
  - apply binRelE1 in Hx as [a [Ha [b [Hb [Hx H]]]]]. subst x.
    apply SepI. apply binRelI; [apply Hsub..|]... apply CProdI...
Qed.

(* 佐恩引理一般形式到集合论形式 *)
Lemma general_Zorn_to_set_theoretic :
  general_Zorn → set_theoretic_Zorn.
Proof with eauto; try congruence.
  intros AC6_0 A Hzn.
  pose proof (AC6_0 A (SubsetRel A)) as [m Hmax].
  - apply subsetRel_is_poset.
  - intros B Hsub Hlo. 
    assert (Hchn: is_chain B). {
      apply chain_is_loset.
      rewrite subRel_of_subselRel in Hlo...
    }
    exists (⋃ B). split. apply Hzn...
    intros y Hy. destruct (classic (y = ⋃ B)). right...
    left. apply binRelI. apply Hsub... apply Hzn...
    split... apply union_is_ub...
  - exists m... eapply sub_maximal_iff...
Qed.

(* 佐恩引理与其非空形式等价 *)
Lemma nonempty_Zorn_iff_general : general_Zorn ↔ nonempty_Zorn.
Proof with auto.
  split; intros Hzn.
  - intros A R [a Ha] Hpo Hub. apply Hzn...
    intros B Hsub Hlo. destruct (classic (B = ∅)).
    + exists a. split... intros y Hy. subst. exfalso0.
    + apply Hub... apply EmptyNE...
  - intros A R Hpo Hub. apply Hzn...
    specialize Hub with ∅ as [m [Hm _]].
    apply empty_sub_all. rewrite subRel_empty.
    apply empty_loset. exists m...
Qed.

Import OrdinalAsType.

(* ==需要选择公理== *)
(* 佐恩引理一般形式的证明 *)
Lemma Zorn's : AC_III' → general_Zorn.
Proof with eauto; try congruence.
  intros AC3' A R Hpo Hub.
  (* 反证法 *)
  destruct (classic (∃ m, maximal m A R)) as [|Harc]... exfalso.
  apply po_archimedean_iff_no_maximal in Harc...
  (* 子集的上界集 *)
  set (λ B, {x ∊ A | λ x, ∀b ∈ B, (b <ᵣ x) R}) as Upper.
  (* 全序子集族 *)
  set {B ∊ 𝒫 A | λ W, loset B (R ⥏ B)} as ℬ.
  (* 上界集族 *)
  set {Upper | B ∊ ℬ} as 𝒜.
  pose proof (AC3' 𝒜) as [F [HfF [HdF HrF]]]. {
    intros x Hx. apply ReplAx in Hx as [B [HB Hx]]. subst x.
    apply SepE in HB as [Hsub Hlo]. apply PowerAx in Hsub.
    specialize Hub with B as [u [Hu Hle]]...
    apply Harc in Hu as [v [Hv Hlt]].
    exists v. apply SepI... intros b Hb.
    apply Hle in Hb. eapply relLe_lt_tranr... apply Hpo.
  }
  (* 上界函数 *)
  set (Func ℬ A (λ B, F[Upper B])) as g.
  assert (HrF': ∀B ∈ ℬ, F[Upper B] ∈ Upper B). {
    intros B HB. apply HrF. apply ReplAx. exists B. split...
  }
  assert (Hg: g: ℬ ⇒ A). {
    apply meta_maps_into. intros B HB.
    apply HrF' in HB. apply SepE1 in HB...
  }
  (* f(B)是B的严格上界 *)
  assert (Hstrict: ∀B ∈ ℬ, strictUpperBound g[B] B A R). {
    intros B HB. split. eapply ap_ran...
    unfold g. rewrite meta_func_ap...
    apply HrF' in HB. apply SepE2 in HB. apply HB...
  }
  (* 构造a₀ *)
  set (g[∅]) as a₀.
  assert (Ha₀: a₀ ∈ A). {
    assert (H0: ∅ ∈ ℬ). {
      apply SepI. apply empty_in_all_power.
      rewrite subRel_empty. apply empty_loset.
    }
    assert (Hsub: Upper ∅ ⊆ A). {
      intros x Hx. apply SepE1 in Hx...
    }
    unfold a₀, g. rewrite meta_func_ap...
    apply Hsub. apply HrF. apply ReplAx. exists ∅. split...
  }
  (* TODO: wait for recursion on ordinals on ch8 *)
Admitted.

Module AlternativeProofWithoutRecursion.

(* ==需要选择公理== *)
(* 佐恩引理一般形式的证明 *)
Lemma Zorn's : AC_III' → general_Zorn.
Proof with eauto; try congruence.
  intros AC3' A R Hpo Hub.
  (* 反证法 *)
  destruct (classic (∃ m, maximal m A R)) as [|Harc]... exfalso.
  apply po_archimedean_iff_no_maximal in Harc...
  (* 子集的上界集 *)
  set (λ B, {x ∊ A | λ x, ∀b ∈ B, (b <ᵣ x) R}) as Upper.
  (* 全序子集族 *)
  set {B ∊ 𝒫 A | λ W, loset B (R ⥏ B)} as ℬ.
  (* 上界集族 *)
  set {Upper | B ∊ ℬ} as 𝒜.
  pose proof (AC3' 𝒜) as [F [HfF [HdF HrF]]]. {
    intros x Hx. apply ReplAx in Hx as [B [HB Hx]]. subst x.
    apply SepE in HB as [Hsub Hlo]. apply PowerAx in Hsub.
    specialize Hub with B as [u [Hu Hle]]...
    apply Harc in Hu as [v [Hv Hlt]].
    exists v. apply SepI... intros b Hb.
    apply Hle in Hb. eapply relLe_lt_tranr... apply Hpo.
  }
  (* 上界函数 *)
  set (Func ℬ A (λ B, F[Upper B])) as g.
  assert (HrF': ∀B ∈ ℬ, F[Upper B] ∈ Upper B). {
    intros B HB. apply HrF. apply ReplAx. exists B. split...
  }
  assert (Hg: g: ℬ ⇒ A). {
    apply meta_maps_into. intros B HB.
    apply HrF' in HB. apply SepE1 in HB...
  }
  (* f(B)是B的严格上界 *)
  assert (Hstrict: ∀B ∈ ℬ, strictUpperBound g[B] B A R). {
    intros B HB. split. eapply ap_ran...
    unfold g. rewrite meta_func_ap...
    apply HrF' in HB. apply SepE2 in HB. apply HB...
  }
  set (λ t B, {x ∊ B | λ x, (x <ᵣ t) R}) as seg.
  set (λ B, B ⊆ A ∧
    (* a *) woset B (R ⥏ B) ∧
    (* b *) ∀x ∈ B, x = g[seg x B]
  ) as conforming.
  (* comparability *)
  assert (Hcom: ∀ B C, B ≠ C → conforming B → conforming C →
    (∃t ∈ B, seg t B = C) ∨ ∃t ∈ C, seg t C = B
  ). {
    cut (∀ B C, ⦿ (B - C) → conforming B → conforming C →
      ∃t ∈ B, seg t B = C
    ). {
      intros H B C Hnq HcB HcC.
      destruct (classic (C ⊆ B)) as [Hcb|Hbc].
      - left. apply H... apply EmptyNE.
        intros H0. apply sub_iff_no_comp in H0...
        apply Hnq. eapply sub_antisym...
      - right. apply H... apply EmptyNE.
        intros H0. apply Hbc. apply sub_iff_no_comp...
    }
    intros B C Hne [HsB [HwB HgB]] [HsC [HwC HgC]].
    destruct HwB as [HloB HminB].
    destruct HwC as [HloC HminC].
    pose proof (HminB (B - C)) as [m [Hm Hmle]]...
    apply SepE in Hm as [Hm Hm'].
    exists m. split... apply sub_antisym.
    + intros x Hx. apply SepE in Hx as [Hx Hxm].
      destruct (classic (x ∈ C)) as [|Hx']... exfalso.
      assert (x ∈ B - C). apply SepI... apply Hmle in H.
      eapply (lo_irrefl _ B)... eapply relLt_le_tranr...
      apply HloB. apply SepI... apply CProdI...
    + destruct (classic (C ⊆ seg m B)) as [|Hnsub]... exfalso.
      pose proof (HminC (C - seg m B)) as [n [Hn Hnle]]... {
        apply EmptyNE. intros H. apply sub_iff_no_comp in H...
      }
      pose proof (HminB (B - seg n C)) as [k [Hk Hkle]]... {
        apply EmptyNE. intros H. apply sub_iff_no_comp in H.
        apply H in Hm. apply SepE1 in Hm...
      }
      assert (Heq: seg k B = seg n C). {
        apply ExtAx. split; intros Hx.
        - destruct (classic (x ∈ seg n C))... exfalso.
          apply SepE in Hx as [Hx Hxk].
          assert (Hx': x ∈ B - seg n C). apply SepI...
          apply Hkle in Hx'. eapply (lo_irrefl _ B)...
          eapply relLt_le_tranr... apply HloB.
          apply SepI... apply CProdI... apply SepE1 in Hk...
        - apply SepE in Hx as [Hx Hxn].
          assert (HxB: x ∈ B). {
            destruct (classic (x ∈ B))... exfalso.
            assert (Hx': x ∈ C - seg m B). {
              apply SepI... intros H'. apply H. apply SepE1 in H'...
            }
            apply Hnle in Hx'. eapply (lo_irrefl _ C)...
            eapply relLt_le_tranr... apply HloC.
            apply SepI... apply CProdI... apply SepE1 in Hn...
          }
          destruct (classic ((n <ᵣ k) R)).
          + apply SepI... eapply relLt_tranr... apply Hpo.
          + exfalso. apply SepE2 in Hk.
            apply Hk. apply SepI.
      }
      assert (Hkm: (k ≤ᵣ m) (R ⥏ B)). {
        apply Hkle. apply SepI...
        intros H. apply Hm'. apply SepE1 in H...
      }
  }

End AlternativeProofWithoutRecursion.
