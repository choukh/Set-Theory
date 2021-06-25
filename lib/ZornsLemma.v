(** Coq coding by choukh, Jan 2021 **)

Require Export ZFC.lib.Ordinal.
Require Import ZFC.lib.ChoiceFacts.
Require ZFC.lib.WosetMin.

(* set-theoretic form *)
Definition set_theoretic_Zorn := ChoiceFacts.AC_VI.

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
    split; [|apply subsetRel_poset].
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
  - apply subsetRel_poset.
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

Import RecursionOnOrdinals.

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
  set {B ∊ 𝒫 A | λ B, loset B (R ⥏ B)} as ℬ.
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
    intros B HB. apply HrF. apply ReplI...
  }
  assert (Hf: f: ℬ ⇒ A). {
    apply meta_function. intros B HB.
    apply HrF' in HB. apply SepE1 in HB...
  }
  (* f(B)是B的严格上界 *)
  assert (f_strict: ∀B ∈ ℬ, strictUpperBound f[B] B A R). {
    intros B HB. split. eapply ap_ran...
    unfold f. rewrite meta_func_ap...
    apply HrF' in HB. apply SepE2 in HB. apply HB...
  }
  set (Recursion (λ B, f[B])) as a.
  assert (HB: ∀α ⋵ 𝐎𝐍, {a | β ∊ α} ∈ ℬ). {
    eapply transfinite_induction_schema_on_ordinals.
    intros α Hoα IH.
    assert (Hsub: {a | β ∊ α} ⊆ A). {
      intros x Hx. apply ReplAx in Hx as [β [Hβ Hx]]. subst x.
      assert (Hoβ: β ⋵ 𝐎𝐍). eapply ord_is_ords...
      unfold a. rewrite recursion_spec... eapply ap_ran...
    }
    apply SepI. apply PowerAx...
    apply loset_iff_connected_poset.
    split; [|eapply subRel_poset]...
    intros x Hx y Hy Hnq.
    apply ReplAx in Hx as H. destruct H as [δ [Hδ Heqx]].
    apply ReplAx in Hy as H. destruct H as [ε [Hε Heqy]]. subst x y.
    assert (Hoδ: δ ⋵ 𝐎𝐍). eapply ord_is_ords...
    assert (Hoε: ε ⋵ 𝐎𝐍). eapply ord_is_ords; revgoals...
    destruct (classic (δ = ε)) as [|Hnq']...
    apply ord_connected in Hnq' as []; auto; [left|right];
    (apply SepI; [|apply CProdI; auto]); unfold a;
    [rewrite (recursion_spec _ ε)|rewrite (recursion_spec _ δ)]; auto;
    (apply f_strict; [apply IH|apply ReplI])...
  }
  assert (Hmono: ∀α ⋵ 𝐎𝐍, ∀β ∈ α, (a β <ᵣ a α) R). {
    intros α Hoα β Hlt.
    unfold a. rewrite (recursion_spec _ α)...
    apply f_strict. apply HB... apply ReplI...
  }
  set {x ∊ A | λ x, ∃α ⋵ 𝐎𝐍, x = a α} as A'.
  set (ϕ_Repl (λ x α, α ⋵ 𝐎𝐍 ∧ x = a α) A') as Ω.
  apply Burali_Forti. exists Ω.
  intros α Hoα. apply ϕ_ReplAx.
  - intros x Hx. rewrite <- unique_existence. split.
    + apply SepE2 in Hx as [ξ [Hξ Hx]]...
    + intros δ ε [Hoδ H1] [Hoε H2]. subst x.
      destruct (classic (δ = ε))... exfalso.
      apply ord_connected in H as []; auto;
      apply Hmono in H; auto; rewrite H2 in H;
      eapply relLt_irrefl; eauto; apply Hpo.
  - exists (a α). split... apply SepI...
    unfold a. rewrite recursion_spec... eapply ap_ran...
Qed.

Module AlternativeProofWithoutRecursion.
Import WosetMin.FullVer.

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
    intros B HB. apply HrF. apply ReplI...
  }
  assert (Hf: f: ℬ ⇒ A). {
    apply meta_function. intros B HB.
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

Section ImportWoStruct.
Import WoStruct.

Theorem WO_to_Zorn : WO → general_Zorn.
Proof with eauto; try congruence.
  intros WO. intros A Q Hpo Hub.
  pose proof (WO A) as [W Hwo].
  set (WoStruct.constr A W Hwo) as S.
  set (λ f, ∃a ∈ A, dom f = seg a (R S) ∧
    ∀b ∈ dom f, f[b] = 1 → (b <ᵣ a) Q) as P.
  set (λ f y, y = match (ixm (P f)) with
    | inl _ => Embed 1
    | inr _ => 0
  end) as γ.
  pose proof (recrusion_spec_intro S γ) as [Hff [Hdf Hrf]]. {
    intros f. unfold γ. rewrite <- unique_existence.
    destruct (ixm (P f)); split...
  }
  set (Recursion S γ) as f. fold f in Hff, Hdf, Hrf.
  set {a ∊ A | λ A, f[a] = 1} as C.
  assert (contra: Embed 0 ≠ 1). {
    intros H. apply (suc_neq_0 0)...
  }
  assert (Hsubd: ∀a ∈ A, seg a (R S) ⊆ WoStruct.A S). {
    intros a Ha x Hx. apply SepE1 in Hx.
    eapply dom_binRel in Hx... apply wo.
  }
  assert (Heqd: ∀a ∈ A, dom (f ↾ seg a (R S)) = seg a (R S)). {
    intros a Ha. apply restr_dom... rewrite Hdf...
  }
  assert (HC: ∀a ∈ A, a ∈ C ↔ ∀b ∈ C, (b <ᵣ a) (R S) → (b <ᵣ a) Q). {
    intros a HaA. split.
    - intros Ha b Hb Hlt.
      apply SepE in Ha as [_ Hfa].
      apply SepE in Hb as [Hb Hfb]. rewrite Hrf in Hfa...
      assert (Hb': b ∈ seg a (R S)). apply SepI... eapply domI...
      destruct (ixm (P (f ↾ seg a (R S))))...
      destruct p as [a' [Ha' [Heqa' Hsub]]].
      assert (Heq: a = a'). {
        rewrite Heqd in Heqa'... eapply seg_injective... apply wo.
      }
      rewrite Heq. apply Hsub.
      + eapply domI. apply restrI...
        eapply func_point... rewrite Hdf...
      + rewrite (restr_ap f (WoStruct.A S))...
    - intros Hinc. apply SepI... rewrite Hrf...
      destruct (ixm (P (f ↾ seg a (R S))))...
      exfalso. apply n. unfold P.
      exists a. repeat split...
      intros b Hb Hfb. rewrite Heqd in Hb...
      apply Hsubd in Hb as HbA...
      apply SepE2 in Hb as Hlt.
      apply Hinc... apply SepI...
      rewrite restr_ap in Hfb; revgoals...
  }
  assert (Hsub: C ⊆ A). {
    intros x Hx. apply SepE1 in Hx...
  }
  assert (Hlo: loset C (Q ⥏ C)). {
    apply loset_iff_connected_poset.
    split; [|eapply subRel_poset]...
    intros a Ha b Hb Hnq.
    apply SepE1 in Ha as HaA.
    apply SepE1 in Hb as HbA.
    eapply lo_connected in Hnq as [];
    [left|right|apply Hwo|auto..];
    (apply SepI; [apply HC|apply CProdI])...
  }
  pose proof (Hub C) as [u [Hu Hle]]...
  exists u. split... intros d Hd.
  destruct (classic ((u <ᵣ d) Q))... exfalso.
  assert (HdC: d ∈ C). {
    apply HC... intros b Hb Hbd. apply Hle in Hb.
    eapply relLe_lt_tranr... apply Hpo.
  }
  apply Hle in HdC. eapply relLt_irrefl. apply Hpo.
  eapply relLe_lt_tranr... apply Hpo.
Qed.

End ImportWoStruct.

Theorem Zorn_to_WO : general_Zorn → WO.
Proof with eauto; try congruence.
  intros Zorn X.
  set {w ∊ 𝒫 X × 𝒫 (X × X) | λ w, woset (π1 w) (π2 w)} as 𝓦.
  set (BinRel 𝓦 (λ u v,
    let A := π1 u in let B := π1 v in
    let RA := π2 u in let RB := π2 v in
    A ⊂ B ∧
    RA = RB ⥏ A ∧
    ∀a ∈ A, ∀b ∈ B - A, (a <ᵣ b) RB
  )) as 𝓡.
  pose proof (Zorn 𝓦 𝓡) as [𝓜 [H𝓜 Hmax]]. {
    (* poset 𝓦 𝓡 *)
    repeat split.
    - apply binRel_is_binRel.
    - apply rel_is_rel.
    - intros u v w Huv Hvw.
      apply binRelE2 in Huv as [Hu [_ [[H11 H11'] [H12 H13]]]].
      apply binRelE2 in Hvw as [_ [Hw [[H21 H21'] [H22 H23]]]].
      apply binRelI... repeat split.
      + eapply sub_tran...
      + intros Heq. rewrite Heq in H11.
        apply H21'. eapply sub_antisym...
      + apply ExtAx. split; intros Hx.
        * rewrite H12 in Hx. apply SepE in Hx as [H1 H2].
          rewrite H22 in H1. apply SepE1 in H1. apply SepI...
        * apply SepE in Hx as [H1 H2].
          rewrite H12. apply SepI...
          rewrite H22. apply SepI...
          apply CProdE1 in H2 as [a [Ha [b [Hb Hx]]]].
          subst x. apply CProdI; apply H11...
      + intros a Ha b Hb.
        destruct (classic (b ∈ π1 v)) as [Hb'|Hb'].
        * assert ((a <ᵣ b) (π2 v)). {
            apply H13... apply SepE in Hb as [H1 H2]. apply SepI...
          }
          rewrite H22 in H. apply SepE1 in H...
        * apply H23. apply H11...
          apply SepE in Hb as [H1 H2]. apply SepI...
    - intros w Hp. apply binRelE3 in Hp as [[] _]...
  } {
    (* chain 𝓒 has upper bound *)
    intros 𝓒 Hsub Hlo.
    set (⋃ {π1 | w ∊ 𝓒}) as U.
    set (BinRel U (λ s t, ∃ C RC, (s <ᵣ t) RC ∧ <C, RC> ∈ 𝓒)) as RU.
    assert (HU: <U, RU> ∈ 𝓦). {
      apply SepI; zfc_simple. {
        apply CProdI.
        - apply PowerAx. intros x Hx.
          apply UnionAx in Hx as [A [HA Hx]].
          apply ReplAx in HA as [p [Hp Heq]].
          apply Hsub in Hp. apply SepE1 in Hp.
          apply CProdE1 in Hp as [A' [HA [R [_ Hp]]]].
          subst p. zfc_simple. subst A'.
          apply PowerAx in HA. apply HA...
        - apply PowerAx. intros p Hp.
          apply binRelE1 in Hp as [a [Ha [b [Hb [Heq [C [RC [Hlt Hp]]]]]]]].
          subst p. apply Hsub in Hp. apply SepE1 in Hp.
          apply CProdE2 in Hp as [_ H].
          apply PowerAx in H. apply H...
      }
      (* woset U RU *)
      split; [apply loset_iff_connected_poset; split|].
      - (* connected RU U *)
        intros a Ha b Hb Hnq.
        assert (HaU := Ha). assert (HbU := Hb).
        apply UnionAx in Ha as [A [HA Ha]].
        apply UnionAx in Hb as [B [HB Hb]].
        apply ReplAx in HA as [p [HpC HA]].
        apply ReplAx in HB as [q [HqC HB]]. subst.
        destruct (classic (p = q)). {
          subst. apply Hsub in HpC.
          apply SepE in HpC as [Hp Hwo].
          apply CProdE1 in Hp as [A [_ [RA [_ Hp]]]].
          subst. zfc_simple.
          eapply lo_connected in Hnq as [];
          [left|right|apply Hwo|auto..]; apply binRelI...
        }
        eapply lo_connected in H as [];
        [| |apply Hlo|auto..]; apply SepE1 in H;
        apply binRelE2 in H as [Hp [Hq [HAB _]]];
        apply SepE in Hp as [Hp HwoA];
        apply SepE in Hq as [Hq HwoB];
        apply CProdE1 in Hp as [A [_ [RA [_ Hp]]]];
        apply CProdE1 in Hq as [B [_ [RB [_ Hq]]]];
        subst; zfc_simple; [apply HAB in Ha|apply HAB in Hb];
        (eapply lo_connected in Hnq as [];
        [left|right|apply HwoB|auto..]; apply binRelI)...
      - (* poset U RU *)
        repeat split.
        + apply binRel_is_binRel.
        + apply rel_is_rel.
        + intros u v w Huv Hvw.
          apply binRelE2 in Huv as [Hu [Hv [C [RC [Huv HC]]]]].
          apply binRelE2 in Hvw as [_ [Hw [D [RD [Hvw HD]]]]].
          destruct (classic (<C, RC> = <D, RD>)). {
            apply op_iff in H as []; subst.
            apply Hsub in HC. apply SepE2 in HC. zfc_simple.
            apply binRelI... exists D, RD. split...
            eapply relLt_tranr... apply HC.
          }
          eapply lo_connected in H as [];
          [| |apply Hlo|auto..]; apply SepE1 in H;
          apply binRelE2 in H as [Hp [Hq [_ [H _]]]];
          apply SepE in Hp as [Hp HwoA];
          apply SepE in Hq as [Hq HwoB];
          apply CProdE1 in Hp as [A [_ [RA [_ Hp]]]];
          apply CProdE1 in Hq as [B [_ [RB [_ Hq]]]];
          apply op_iff in Hp as [];
          apply op_iff in Hq as [];
          subst; zfc_simple; apply binRelI; auto;
          exists B, RB; split; auto; [
            rewrite H in Huv; apply SepE1 in Huv|
            rewrite H in Hvw; apply SepE1 in Hvw
          ]; eapply relLt_tranr; eauto; apply HwoB.
        + intros u Hp. apply binRelE3 in Hp as [C [RC [Hlt Hp]]].
          apply Hsub in Hp. apply SepE2 in Hp. zfc_simple.
          eapply lo_irrefl. apply Hp. apply Hlt.
      - (* has min *)
        intros A [a Ha] HAU.
        apply HAU in Ha as HaU.
        apply UnionAx in HaU as [C [HC HaC]].
        apply ReplAx in HC as [p [HpC HC]].
        apply Hsub in HpC as Hp.
        apply SepE in Hp as [Hp [_ Hmin]].
        apply CProdE1 in Hp as [C' [_ [RC [_ Hp]]]].
        subst p. zfc_simple. subst C'.
        pose proof (Hmin (A ∩ C)) as [m [Hm Hle]].
        + exists a. apply BInterI...
        + intros x Hx. apply BInterE in Hx as []...
        + apply BInterE in Hm as [HmA HmC].
          exists m. split... intros x HxA.
          destruct (classic (m = x)) as [|Hmx]. right... left.
          apply binRelI; [apply HAU..|]...
          destruct (classic (x ∈ C)) as [HxC|HxC']. {
            assert (x ∈ A ∩ C). apply BInterI...
            apply Hle in H as []...
          }
          apply HAU in HxA as Hx.
          apply UnionAx in Hx as [D [HD Hx]].
          apply ReplAx in HD as [q [HqC HD]].
          apply Hsub in HqC as Hq.
          apply SepE in Hq as [Hq Hwo].
          apply CProdE1 in Hq as [D' [_ [RD [_ Hq]]]].
          subst q. zfc_simple. subst D'.
          destruct (classic (<C, RC> = <D, RD>)) as [|Hnq]. {
            apply op_iff in H as []; subst...
          }
          eapply lo_connected in Hnq as [];
          [| |apply Hlo|auto..]; apply SepE1 in H;
          apply binRelE3 in H as [H1 [_ H3]]; zfc_simple.
          * exists D, RD. split... apply H3... apply SepI...
          * apply H1 in Hx...
    }
    (* show that <U, RU> is upper bound of 𝓒 *)
    exists (<U, RU>). split... intros p HpC.
    destruct (classic (p = <U, RU>)) as [|Hnq]. right... left.
    apply binRelI... apply Hsub in HpC as Hp.
    apply SepE in Hp as [Hp Hwo].
    apply CProdE1 in Hp as [A [_ [RA [_ Hp]]]].
    subst. zfc_simple.
    assert (HAU: A ⊆ U). {
      apply union_is_ub. apply ReplAx.
      exists <A, RA>. split... zfc_simple.
    }
    assert (HeqR: RA = RU ⥏ A). {
      destruct Hwo as [[Hbr _] _].
      apply ExtAx. intros p. split; intros Hp.
      - apply Hbr in Hp as H.
        apply CProdE1 in H as [a [Ha [b [Hb Heqp]]]].
        subst p. apply SepI.
        apply binRelI; [apply HAU..|]... apply CProdI...
      - apply SepE in Hp as [Hp Hpp].
        apply binRelE1 in Hp as [a [Ha [b [Hb [Hp [B [RB [Hlt HP]]]]]]]].
        subst p. apply CProdE2 in Hpp as [HaA HaB]. 
        destruct (classic (<A, RA> = <B, RB>)). {
          apply op_iff in H as []; subst...
        }
        eapply lo_connected in H as [];
        [| |apply Hlo|auto..]; apply SepE1 in H;
        apply binRelE3 in H as [_ [H2 _]]; zfc_simple.
        * rewrite H2. apply SepI... apply CProdI...
        * rewrite H2 in Hlt. apply SepE1 in Hlt...
    }
    repeat split...
    - intros Heq. apply Hnq. apply op_iff. split...
      rewrite HeqR, Heq.
      apply ExtAx. intros p. split; intros Hp.
      apply SepE1 in Hp... apply SepI... apply SepE1 in Hp...
    - intros a Ha b Hb. apply binRelI.
      apply HAU... apply SepE1 in Hb...
      apply SepE in Hb as [Hb Hb'].
      apply UnionAx in Hb as [B [HB Hb]].
      apply ReplAx in HB as [q [HqC HB]].
      apply Hsub in HqC as Hq.
      apply SepE in Hq as [Hq HwoB].
      apply CProdE1 in Hq as [B' [_ [RB [_ Hq]]]].
      subst q. zfc_simple. subst B'.
      destruct (classic (<A, RA> = <B, RB>)). {
        apply op_iff in H as []; subst...
      }
      eapply lo_connected in H as [];
      [| |apply Hlo|auto..]; apply SepE1 in H;
      apply binRelE3 in H as [H1 [_ H3]]; zfc_simple;
      exists B, RB; split...
      * apply H3... apply SepI...
      * apply H1 in Hb...
  }
  (* by contradiction show that M = X and RM is the desired well order *)
  apply SepE in H𝓜 as H. destruct H as [Hp Hwo].
  apply CProdE1 in Hp as [M [Hsub [RM [_ Hp]]]].
  subst. zfc_simple. apply PowerAx in Hsub.
  exists RM. replace X with M...
  destruct (classic (M = X)) as [|HMX]... exfalso.
  assert (Hpsub: M ⊂ X). split...
  apply comp_nonempty in Hpsub as [s Hs].
  apply SepE in Hs as [Hs Hs'].
  set (M ∪ ⎨s⎬) as M'.
  set (BinRel (M ∪ ⎨s⎬) (λ x y,
    match (ixm (x = s)) with
    | inl _ => False
    | inr _ =>
      match (ixm (y = s)) with
      | inl _ => True
      | inr _ => (x <ᵣ y) RM
  end end)) as RM'.
  assert (Hsub': M' ⊆ X). {
    intros x Hx. apply BUnionE in Hx as [].
    apply Hsub... apply SingE in H...
  }
  assert (HM': <M', RM'> ∈ 𝓦). {
    apply SepI; zfc_simple.
    apply CProdI; apply PowerAx...
    intros p Hp. apply SepE1 in Hp.
    apply CProdE1 in Hp as [a [Ha [b [Hb Hp]]]].
    subst. apply CProdI; apply Hsub'...
    (* woset M' RM' *)
    split; [apply loset_iff_connected_poset; split|].
    - (* connected RM' M' *)
      intros a Ha b Hb Hnq.
      apply BUnionE in Ha as [Ha|Ha];
      apply BUnionE in Hb as [Hb|Hb].
      + eapply lo_connected in Hnq as [];
        [left|right|apply Hwo|auto..];
        (apply binRelI; [apply BUnionI1; auto..|]);
        destruct (ixm (a = s)); try congruence;
        destruct (ixm (b = s))...
      + left. apply binRelI.
        apply BUnionI1... apply BUnionI2... apply SingE in Hb.
        destruct (ixm (b = s))...
        destruct (ixm (a = s))...
      + right. apply binRelI.
        apply BUnionI1... apply BUnionI2... apply SingE in Ha.
        destruct (ixm (b = s))...
        destruct (ixm (a = s))...
      + apply SingE in Ha; apply SingE in Hb...
    - (* poset M' RM' *)
      repeat split.
      + apply binRel_is_binRel.
      + apply rel_is_rel.
      + intros x y z Hxy Hyz.
        apply binRelE2 in Hxy as [Hx [Hy Hxy]].
        apply binRelE2 in Hyz as [_ [Hz Hyz]].
        apply binRelI...
        (apply BUnionE in Hx as [Hx|Hx]; [|apply SingE in Hx]);
        (apply BUnionE in Hy as [Hy|Hy]; [|apply SingE in Hy]);
        (apply BUnionE in Hz as [Hz|Hz]; [|apply SingE in Hz]);
        destruct (ixm (x = s));
        destruct (ixm (y = s));
        destruct (ixm (z = s))...
        * eapply relLt_tranr... apply Hwo.
        * exfalso...
      + intros x Hp. apply binRelE2 in Hp as [Hx [_ H]].
        apply BUnionE in Hx as [Hx|Hx].
        * destruct (ixm (x = s))...
          eapply lo_irrefl... apply Hwo.
        * apply SingE in Hx.
          destruct (ixm (x = s))...
    - (* has min *)
      intros A [a Ha] HAM'.
      destruct (classic (A - ⎨s⎬ = ∅)) as [|Hne]. {
        exists a. split... intros x Hx. right.
        replace A with ⎨a⎬ in Hx.
        apply SingE in Hx... clear x Hx.
        apply ExtAx. split; intros Hx.
        - apply SingE in Hx...
        - apply sub_iff_no_comp in H.
          apply H in Hx. apply SingE in Hx.
          apply H in Ha. apply SingE in Ha. subst...
      }
      destruct Hwo as [_ Hmin].
      pose proof (Hmin (A - ⎨s⎬)) as [m [Hm Hle]].
      + apply EmptyNE...
      + intros x Hx. apply SepE in Hx as [Hx Hx'].
        apply SingNE in Hx'. apply HAM' in Hx.
        apply BUnionE in Hx as []... apply SingE in H...
      + apply SepE in Hm as [Hm Hm']. apply SingNE in Hm'.
        exists m. split... intros x Hx.
        destruct (classic (m = x)) as [|Hnq]. right... left.
        apply binRelI; [apply HAM'..|]...
        destruct (ixm (m = s))...
        destruct (ixm (x = s))...
        assert (x ∈ A - ⎨s⎬). apply SepI... apply SingNI...
        apply Hle in H as []...
  }
  apply Hmax in HM' as H.
  destruct H; revgoals. {
    apply op_iff in H as [H _].
    apply Hs'. rewrite <- H. apply BUnionI2...
  }
  apply H. apply binRelI...
  repeat split; zfc_simple...
  - intros x Hx. apply BUnionI1...
  - intros Heq. apply Hs'. rewrite Heq. apply BUnionI2...
  - apply ExtAx. split; intros Hx.
    + destruct Hwo as [[Hbr _] _].
      apply Hbr in Hx as Hp. apply SepI...
      apply CProdE1 in Hp as [a [Ha [b [Hb Hp]]]].
      subst. apply binRelI; [apply BUnionI1..|]...
      destruct (ixm (a = s))...
      destruct (ixm (b = s))...
    + apply SepE in Hx as [H1 H2].
      apply binRelE1 in H1 as [a [_ [b [_ [Heq Hlt]]]]].
      subst. apply CProdE2 in H2 as [Ha Hb].
      destruct (ixm (a = s))...
      destruct (ixm (b = s))...
  - intros a Ha b Hb.
    apply SepE in Hb as [Hb Hb'].
    apply binRelI; [apply BUnionI1|..]...
    destruct (ixm (a = s))...
    destruct (ixm (b = s))...
    apply BUnionE in Hb as []...
    apply SingE in H0...
Qed.
