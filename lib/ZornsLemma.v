(** Coq coding by choukh, Jan 2021 **)

Require Import ZFC.EST7_5.
Require Import ZFC.lib.Choice.
Require Import ZFC.lib.Cardinal.
Require Import ZFC.lib.OrdinalAsType.
Require Import ZFC.lib.WosetMin.
Import WosetMin.FullVer.

(* set-theoretic form *)
Definition set_theoretic_Zorn := Choice.AC_VI.

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
    * apply binRelE3 in H as []...
    * apply binRelE3 in H as []...
Qed.

(* 集合的包含关系在子集上的限制等于子集的包含关系 *)
Lemma subRel_of_subselRel : ∀ A B, B ⊆ A →
  (SubsetRel A) ⥏ B = SubsetRel B.
Proof with auto.
  intros A B Hsub.
  apply ExtAx. split; intros Hx.
  - apply SepE in Hx as [Hx Hp].
    apply CProdE1 in Hp as [a [Ha [b [Hb Hp]]]]. subst x.
    apply binRelE3 in Hx. apply binRelI...
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

(* AC cycle
  3' → (Zorn ↔ WO) → 6 (→ ... → 3')
*)

Import OrdinalAsType.

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
  set (Func ℬ A (λ B, F[Upper B])) as f.
  assert (HrF': ∀B ∈ ℬ, F[Upper B] ∈ Upper B). {
    intros B HB. apply HrF. apply ReplAx. exists B. split...
  }
  assert (Hf: f: ℬ ⇒ A). {
    apply meta_maps_into. intros B HB.
    apply HrF' in HB. apply SepE1 in HB...
  }
  (* f(B)是B的严格上界 *)
  assert (f_strict: ∀B ∈ ℬ, strictUpperBound f[B] B A R). {
    intros B HB. split. eapply ap_ran...
    unfold f. rewrite meta_func_ap...
    apply HrF' in HB. apply SepE2 in HB. apply HB...
  }
  (* 构造a₀ *)
  set (f[∅]) as a₀.
  assert (Ha₀: a₀ ∈ A). {
    assert (H0: ∅ ∈ ℬ). {
      apply SepI. apply empty_in_all_power.
      rewrite subRel_empty. apply empty_loset.
    }
    assert (Hsub: Upper ∅ ⊆ A). {
      intros x Hx. apply SepE1 in Hx...
    }
    unfold a₀, f. rewrite meta_func_ap...
    apply Hsub. apply HrF. apply ReplAx. exists ∅. split...
  }
  (* TODO: wait for recursion on ordinals on ch8 *)
Admitted.

Module AlternativeProofWithoutRecursion.

(* 佐恩引理一般形式的证明 *)
Lemma Zorn's : AC_III' → general_Zorn.
Proof with eauto; try congruence.
  intros AC3' A R Hpo Hub. assert (H := Hpo).
  destruct H as [_ [_ [Htr Hir]]].
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
    apply Hle in Hb. eapply relLe_lt_tranr...
  }
  (* 上界函数 *)
  set (Func ℬ A (λ B, F[Upper B])) as f.
  assert (HrF': ∀B ∈ ℬ, F[Upper B] ∈ Upper B). {
    intros B HB. apply HrF. apply ReplAx. exists B. split...
  }
  assert (Hf: f: ℬ ⇒ A). {
    apply meta_maps_into. intros B HB.
    apply HrF' in HB. apply SepE1 in HB...
  }
  (* f(B)是B的严格上界 *)
  assert (f_strict: ∀B ∈ ℬ, strictUpperBound f[B] B A R). {
    intros B HB. split. eapply ap_ran...
    unfold f. rewrite meta_func_ap...
    apply HrF' in HB. apply SepE2 in HB. apply HB...
  }
  set (λ t B, {x ∊ B | λ x, (x <ᵣ t) R}) as seg.
  set (λ B, ∀x ∈ B, x = f[seg x B]) as inductive.
  set (λ B, B ⊆ A ∧
    (* a *) woset B (R ⥏ B) ∧
    (* b *) inductive B
  ) as good.
  assert (comparability: ∀ B C,
    B ≠ C → good B → good C →
    (∃t ∈ B, seg t B = C) ∨ ∃t ∈ C, seg t C = B
  ). {
    cut (∀ B C, ⦿ (B - C) → good B → good C →
      ∃t ∈ B, seg t B = C
    ). {
      intros H B C Hnq HgB HgC.
      destruct (classic (C ⊆ B)) as [Hcb|Hbc].
      - left. apply H... apply EmptyNE.
        intros H0. apply sub_iff_no_comp in H0...
        apply Hnq. eapply sub_antisym...
      - right. apply H... apply EmptyNE.
        intros H0. apply Hbc. apply sub_iff_no_comp...
    }
    intros B C Hne [HsB [HwB HiB]] [HsC [HwC HiC]].
    destruct HwB as [HloB HminB].
    destruct HwC as [HloC HminC].
    pose proof (HminB (B - C)) as [b [Hb Hble]]...
    apply SepE in Hb as [Hb Hb'].
    exists b. split... apply sub_antisym.
    + intros x Hx. apply SepE in Hx as [Hx Hxb].
      destruct (classic (x ∈ C)) as [|Hx']... exfalso.
      assert (x ∈ B - C). apply SepI... apply Hble in H.
      eapply (lo_irrefl _ B)... eapply relLt_le_tranr...
      apply HloB. apply SepI... apply CProdI...
    + destruct (classic (C ⊆ seg b B)) as [|Hnsub]... exfalso.
      pose proof (HminC (C - seg b B)) as [c [Hc Hcle]]... {
        apply EmptyNE. intros H. apply sub_iff_no_comp in H...
      }
      pose proof (HminB (B - seg c C)) as [d [Hd Hdle]]... {
        apply EmptyNE. intros H. apply sub_iff_no_comp in H.
        apply H in Hb. apply SepE1 in Hb...
      }
      assert (Hdb: (d ≤ᵣ b) (R ⥏ B)). {
        apply Hdle. apply SepI...
        intros H. apply Hb'. apply SepE1 in H...
      }
      apply SepE in Hc as [Hc Hc'].
      apply SepE in Hd as [Hd Hd'].
      assert (Heq: d = c). {
        rewrite (HiB d), HiC... f_equal.
        apply ExtAx. split; intros Hx.
        - destruct (classic (x ∈ seg c C))... exfalso.
          apply SepE in Hx as [Hx Hxk].
          assert (Hx': x ∈ B - seg c C). apply SepI...
          apply Hdle in Hx'. eapply (lo_irrefl _ B)...
          eapply relLt_le_tranr... apply HloB.
          apply SepI... apply CProdI...
        - apply SepE in Hx as [Hx Hxc].
          destruct (classic (d = b)) as [|Hnq]. {
            subst d. destruct (classic (x ∈ seg b B))... exfalso.
            assert (Hx': x ∈ C - seg b B). apply SepI...
            apply Hcle in Hx'. eapply (lo_irrefl _ C)...
            eapply relLt_le_tranr... apply HloC.
            apply SepI... apply CProdI...
          }
          assert (HdC: d ∈ C). {
            destruct (classic (d ∈ C)) as [|HdC]... exfalso.
            assert (HdB: d ∈ B - C). apply SepI... 
            apply Hble in HdB as []; destruct Hdb...
            eapply (lo_irrefl _ B)... eapply relLt_tranr... apply HloB.
          }
          assert (HxB: x ∈ B). {
            destruct (classic (x ∈ B))... exfalso.
            assert (Hx': x ∈ C - seg b B). {
              apply SepI... intros H'. apply H. apply SepE1 in H'...
            }
            apply Hcle in Hx'. eapply (lo_irrefl _ C)...
            eapply relLt_le_tranr... apply HloC.
            apply SepI... apply CProdI...
          }
          apply SepI...
          destruct (classic (d = c)). subst...
          eapply lo_connected in H as []; eauto; apply SepE1 in H.
          + exfalso. apply Hd'. apply SepI...
          + eapply relLt_tranr...
      }
      destruct Hdb... apply SepE1 in H.
      apply Hc'. apply SepI... subst...
  }
  assert (good_or_not: ∀ B, good B →
    ∀x ∈ B, ∀y ∈ A, (y <ᵣ x) R → y ∈ B ∨ ¬∃C, good C ∧ y ∈ C
  ). {
    intros B HgB x Hx y Hy Hyx.
    destruct (classic (y ∈ B)) as [|Hy']...
    right. intros [C [HgC HyC]].
    destruct (classic (B = C)) as [|Hnq]...
    pose proof (comparability B C Hnq HgB HgC).
    destruct H as [[t [Ht Hseg]]|[t [Ht Hseg]]]; subst.
    - apply SepE1 in HyC...
    - apply Hy'. apply SepE2 in Hx.
      apply SepI... eapply relLt_tranr...
  }
  set {B ∊ 𝒫 A | good} as 𝒞.
  assert (Hsubu: ⋃ 𝒞 ⊆ A). {
    intros x Hx. apply UnionAx in Hx as [C [HC Hx]].
    apply SepE1 in HC. apply PowerAx in HC. apply HC...
  }
  assert (union_lo: loset ⋃ 𝒞 (R ⥏ ⋃ 𝒞)). {
    apply loset_iff_connected_poset.
    split; [|eapply subRel_poset]...
    intros x Hx y Hy Hnq.
    assert (H := Hx). apply UnionAx in H as [X [HX Hx']].
    assert (H := Hy). apply UnionAx in H as [Y [HY Hy']].
    apply SepE2 in HX. apply SepE2 in HY.
    destruct (classic (X = Y)) as [|HnQ]. {
      subst Y. apply (lo_connected (R ⥏ X) X) in Hnq...
      destruct Hnq; [left|right]; apply SepE1 in H;
      apply SepI; auto; apply CProdI... apply HX.
    }
    pose proof (comparability X Y HnQ HX HY).
    destruct H as [[t [Ht Hseg]]|[t [Ht Hseg]]].
    + subst Y. apply SepE1 in Hy'.
      apply (lo_connected (R ⥏ X) X) in Hnq...
      destruct Hnq; [left|right]; apply SepE1 in H;
      apply SepI; auto; apply CProdI... apply HX.
    + subst X. apply SepE1 in Hx'.
      apply (lo_connected (R ⥏ Y) Y) in Hnq...
      destruct Hnq; [left|right]; apply SepE1 in H;
      apply SepI; auto; apply CProdI... apply HY.
  }
  assert (union_wo: woset ⋃ 𝒞 (R ⥏ ⋃ 𝒞)). {
    split... intros B [b Hb] Hsub.
    apply Hsub in Hb as H.
    apply UnionAx in H as [C [HC HbC]].
    apply SepE2 in HC as HgC.
    set ((Min C (R ⥏ C))[B ∩ C]) as m.
    pose proof (min_correct C (R ⥏ C) (B ∩ C)) as [Hm Hmin].
    - apply HgC.
    - exists b. apply BInterI...
    - intros x Hx. apply BInterE in Hx as []...
    - exists m. fold m in Hm, Hmin.
      apply BInterE in Hm as [HmB HmC].
      assert (HmU: m ∈ ⋃ 𝒞). apply Hsub...
      split... intros x Hx.
      assert (HxU: x ∈ ⋃ 𝒞). apply Hsub...
      destruct (classic (x ∈ C)) as [HxC|HxC].
      + assert (x ∈ B ∩ C) by (apply BInterI; auto).
        apply Hmin in H as []; [left|right]...
        apply SepE1 in H. apply SepI... apply CProdI...
      + destruct (classic (m = x))...
        eapply lo_connected in H as [|Hxm]... left... right.
        exfalso. apply SepE1 in Hxm. apply Hsubu in HxU as HxA.
        pose proof (good_or_not C HgC m HmC x HxA Hxm) as []...
        apply H. apply UnionAx in HxU as [D [HD HxD]].
        exists D. split... apply SepE2 in HD...
  }
  assert (union_ind: inductive ⋃ 𝒞). {
    intros t Ht. apply UnionAx in Ht as [B [HB Ht]].
    apply SepE2 in HB as HgB. assert (H := HgB).
    destruct H as [_ [_ Hap]].
    apply Hap in Ht as Heqt. rewrite Heqt at 1. f_equal.
    apply ExtAx. split; intros Hx.
    - apply SepE in Hx as [Hx Hxt]. apply SepI...
      apply UnionAx. exists B. split...
    - apply SepE in Hx as [Hx Hxt]. apply SepI...
      apply Hsubu in Hx as HxA.
      pose proof (good_or_not B HgB t Ht x HxA Hxt) as []...
      exfalso. apply H. apply UnionAx in Hx as [C [HC HxC]].
      exists C. split... apply SepE2 in HC...
  }
  (* since ⋃ 𝒞 is woset and inductive,
  it is good but we don't need this fact,
  instead we prove suc of ⋃ 𝒞 is good *)
  assert (Hu: ⋃ 𝒞 ∈ ℬ). {
    apply SepI. apply PowerAx... apply union_lo.
  }
  set (⋃ 𝒞 ∪ ⎨f[⋃ 𝒞]⎬) as S.
  assert (Hsubs: S ⊆ A). {
    intros x Hx. apply BUnionE in Hx as []. apply Hsubu...
    apply SingE in H. subst. eapply ap_ran...
  }
  assert (suc_lo: loset S (R ⥏ S)). {
    apply loset_iff_connected_poset.
    split; [|eapply subRel_poset]...
    intros x Hx y Hy Hnq.
    assert (HxS := Hx). assert (HyS := Hy).
    apply BUnionE in Hx as [Hx|Hx];
    apply BUnionE in Hy as [Hy|Hy].
    - apply (lo_connected (R ⥏ ⋃ 𝒞) ⋃ 𝒞) in Hnq as []; auto; [left|right];
      apply SepE1 in H; apply SepI; auto; apply CProdI...
    - left. apply SingE in Hy. rewrite Hy.
      apply f_strict in Hx... apply SepI... apply CProdI...
    - right. apply SingE in Hx. rewrite Hx.
      apply f_strict in Hy... apply SepI... apply CProdI...
    - apply SingE in Hx; apply SingE in Hy...
  }
  assert (suc_wo: woset S (R ⥏ S)). {
    split... intros B [b Hb] Hsub.
    set (B ∩ ⋃ 𝒞) as C.
    assert (Hor: ∀x ∈ B, x ∈ C ∨ x ∈ B ∧ x = f[⋃ 𝒞]). {
      intros x Hx. apply Hsub in Hx as HxS.
      apply BUnionE in HxS as []; [left|right].
      apply BInterI... apply SingE in H...
    }
    destruct (classic (C = ∅)) as [H0|Hne].
    - apply Hor in Hb as [Hb|[Hb Heqb]].
      + exfalso. eapply EmptyE...
      + exists b. split... intros x Hx. cut (b = x). right...
        apply Hor in Hx as [Hx|[Hx Heqx]]...
        exfalso. eapply EmptyE...
    - destruct union_wo as [_ Hmin].
      pose proof (Hmin C) as [m [Hm Hle]].
      + apply EmptyNE in Hne...
      + intros x Hx. apply BInterE in Hx as []...
      + apply BInterE in Hm as [HmB HmU].
        exists m. split... intros x Hx.
        apply Hor in Hx as [Hx|[Hx Heqx]].
        * apply Hle in Hx as H.
          apply BInterE in Hx as [HxB _].
          destruct H; [left|right]...
          apply SepE1 in H. apply SepI...
          apply CProdI; apply Hsub...
        * left. subst x. apply SepI. apply f_strict...
          apply CProdI; apply Hsub...
  }
  assert (suc_good: good S). {
    split... split... intros t Ht.
    apply BUnionE in Ht as [Ht|Ht].
    - apply union_ind in Ht as Heqt.
      rewrite Heqt at 1. f_equal.
      apply ExtAx. split; intros Hx.
      + apply SepE in Hx as [Hx Hxt].
        apply SepI... apply BUnionI1...
      + apply SepE in Hx as [Hx Hxt].
        apply SepI... apply BUnionE in Hx as []...
        apply SingE in H. subst. rewrite Heqt in Hxt.
        exfalso. eapply relLt_irrefl...
        eapply relLt_tranr... apply f_strict...
    - apply SingE in Ht. rewrite Ht at 1. f_equal.
      apply ExtAx. split; intros Hx.
      + apply SepI. apply BUnionI1...
        rewrite Ht. apply f_strict...
      + apply SepE in Hx as [Hx Hxt].
        apply BUnionE in Hx as []... apply SingE in H.
        exfalso. subst. eapply relLt_irrefl...
  }
  assert (Hfu: f[⋃ 𝒞] ∈ ⋃ 𝒞). {
    apply UnionAx. exists S. split... apply SepI...
    apply PowerAx. apply Hsubs. apply BUnionI2...
  }
  apply f_strict in Hu as [_ Hlt]. apply Hlt in Hfu.
  eapply relLt_irrefl...
Qed.

End AlternativeProofWithoutRecursion.

Theorem WO_to_Zorn : WO → general_Zorn.
Admitted.
