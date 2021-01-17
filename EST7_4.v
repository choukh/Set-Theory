(** Based on "Elements of Set Theory" Chapter 7 Part 4 **)
(** Coq coding by choukh, Dec 2020 **)

Require Export ZFC.EST7_3.
Require Import ZFC.lib.FuncFacts.

(*** EST第七章4：序数的定义，序数的序，布拉利-福尔蒂悖论，后继序数，极限序数 ***)

Module Export Ordinals.
Import WOStruct.

Section EpsilonImageWellDefined.
Import WOStruct.EpsilonImage.

Local Lemma eq_α : ∀ f S T, f:ₒₑ S ⟺ T →
  (∀x ∈ A S, (E S)[x] = (E T)[f[x]]) → α S = α T.
Proof with eauto; try congruence.
  intros * [Hf Hoe] Heq.
  destruct (e_bijective S) as [[Hf1 _] [Hd1 _]].
  destruct (e_bijective T) as [[Hf2 _] [Hd2 _]].
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
  ∀ S T, parent S ≅ parent T ↔ α S = α T.
Proof with eauto; try congruence.
  intros S T. split; revgoals. {
    intros Heq. rewrite wo_iso_epsilon, wo_iso_epsilon.
    unfold ε. rewrite Heq. reflexivity.
  }
  intros [f [Hf Hoe]].
  eapply eq_α. split... intros x Hx.
  set {x ∊ WOStruct.A S | λ x, (E S)[x] = (E T)[f[x]]} as B.
  replace (WOStruct.A S) with B in Hx.
  apply SepE2 in Hx... clear x Hx.
  eapply transfinite_induction...
  split. intros t Ht. apply SepE1 in Ht...
  intros t Ht Hsub. apply SepI...
  assert (Hft: f[t] ∈ WOStruct.A T). {
    eapply ap_ran... apply bijection_is_func...
  }
  rewrite e_ap, e_ap...
  apply ExtAx. split; intros Hx.
  - apply ReplAx in Hx as [s [Hs Heq]]. subst x.
    apply ReplAx. exists (f[s]). split.
    + apply SepE in Hs as [Hs Hlt].
      eapply dom_binRel in Hs; [|apply (WOStruct.wo S)].
      apply segI. apply Hoe...
    + apply Hsub in Hs. apply SepE2 in Hs...
  - apply inv_bijection in Hf as Hf'.
    apply bijection_is_func in Hf as [_ [Hi Hr]].
    apply bijection_is_func in Hf' as [Hf' _].
    apply ReplAx in Hx as [s [Hs Heq]]. subst x.
    apply SepE in Hs as [Hs Hlt].
    eapply dom_binRel in Hs; [|apply (WOStruct.wo T)].
    assert (Hsr: s ∈ ran f) by (rewrite Hr; apply Hs).
    apply ReplAx. exists (f⁻¹[s]). split.
    + apply segI. apply Hoe...
      * eapply ap_ran...
      * rewrite inv_ran_reduction... 
    + rewrite <- (inv_ran_reduction f) in Hlt...
      apply Hoe in Hlt; [|eapply ap_ran|]...
      assert (f⁻¹[s] ∈ seg t (WOStruct.R S)). {
        apply SepI... eapply domI...
      }
      apply Hsub in H. apply SepE2 in H.
      rewrite inv_ran_reduction in H...
Qed.

End EpsilonImageWellDefined.

Section OrdDef.
Import WOStruct.EpsilonImage.

(* 序数 *)
Definition ord := λ S, α S.
Definition is_ord := λ α, ∃ S, α = ord S.

Lemma ord_is_ord : ∀ S, is_ord (ord S).
Proof. intros. exists S. auto. Qed.

(* 序数良定义 *)
Lemma ord_well_defined : ∀ S T, S ≅ T ↔ ord S = ord T.
Proof with auto.
  split; intros.
  - unfold ord, α. apply epsilon_image_well_defined.
    rewrite <- parent_iso...
  - apply epsilon_image_well_defined in H. apply parent_iso...
Qed.

Lemma ordI : ∀ S t, ∀s ∈ A S, (E S)[s] = t → t ∈ ord S.
Proof. exact α_intro. Qed.

Lemma ordE : ∀ S, ∀t ∈ ord S, ∃s ∈ A S, (E S)[s] = t.
Proof. exact α_elim. Qed.

(* 由同构关系导出序数的序 *)
Lemma ord_lt_intro : ∀ S T, ∀t ∈ A T, S ≅ Seg t T → ord S ∈ ord T.
Proof with eauto.
  intros * t Ht Hiso. eapply ordI...
  apply ord_well_defined in Hiso. rewrite seg_α in Hiso...
Qed.

(* 由序数的序导出同构关系 *)
Lemma ord_lt_elim : ∀ S T, ord S ∈ ord T → ∃t ∈ A T, S ≅ Seg t T.
Proof with eauto.
  intros. apply ordE in H as [t [Ht H]]. exists t. split...
  apply ord_well_defined. rewrite seg_α...
Qed.

(* 序数的序数等于自身 *)
Lemma ord_of_ord : ∀ S, ord S = ord (Epsilon S).
Proof.
  intros. apply ord_well_defined. apply iso_epsilon.
Qed.

(* 空集的序数等于零 *)
Lemma ord_empty : ∀ S, A S = ∅ → ord S = ∅.
Proof.
  intros. apply e_empty in H.
  unfold ord, α. rewrite H. apply ran_of_empty.
Qed.

(* 序数是良序集 *)
Lemma ord_woset : ∀ α, is_ord α → woset α (MemberRel α).
Proof. intros α [S H]. subst. apply (wo (Epsilon S)). Qed.

(* 可以以成员关系良序排列的传递集是序数 *)
Theorem transitive_set_well_ordered_by_epsilon_is_ord :
  ∀ α, trans α → woset α (MemberRel α) → is_ord α.
Proof with eauto.
  intros α Htr Hwo.
  set (constr α (MemberRel α) Hwo) as S.
  cut (∀x ∈ α, (E S)[x] = x). {
    intros H. exists S.
    pose proof (e_bijective S) as [[Hf _] [Hd _]]...
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
  intros t Ht Hsub. apply SepI... rewrite e_ap...
  apply ExtAx. split; intros Hx.
  - apply ReplAx in Hx as [s [Hs H1]]. apply Hsub in Hs as Hsb.
    apply SepE in Hsb as [_ H2]. apply SepE in Hs as [_ H].
    rewrite <- H2, H1 in H.
    apply binRelE3 in H...
  - assert (x ∈ seg t (R S)). {
      apply segI. apply binRelI...
    }
    apply ReplAx. exists x. split...
    apply Hsub in H. apply SepE2 in H...
Qed.

(* 序数集 *)
Definition is_ords := λ S, ∀α ∈ S, is_ord α.

(* 序数里都是序数 *)
Theorem ord_is_ords : ∀ α, is_ord α → is_ords α.
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

(* 序数的序反自反 *)
Theorem ord_irrefl : ∀ α, is_ord α → α ∉ α.
Proof.
  intros α [S H]. subst. intros H.
  pose proof (ordE _ _ H) as [s [Hs Heq]].
  rewrite <- Heq in H. eapply e_irrefl; eauto.
Qed.

End OrdDef.

(* 序数的序满足三歧性 *)
Theorem ord_trich : ∀ α β, is_ord α → is_ord β →
  α ∈ β ∧ α ≠ β ∧ β ∉ α ∨
  α ∉ β ∧ α = β ∧ β ∉ α ∨
  α ∉ β ∧ α ≠ β ∧ β ∈ α.
Proof with eauto.
  intros α β Hα Hβ.
  assert (α ∈ β ∨ α = β ∨ β ∈ α). {
    destruct Hα as [S Heqα].
    destruct Hβ as [T Heqβ]. subst.
    destruct (wo_iso_at_least_trich S T) as [H|[[t [Ht H]]|[t [Ht H]]]].
    - right; left. apply ord_well_defined...
    - left. eapply ord_lt_intro...
    - right; right. eapply ord_lt_intro... symmetry...
  }
  destruct H as [Hab|[Hnq|Hba]].
  - left. split... split; intros H; subst;
    eapply ord_irrefl... eapply ord_trans...
  - right; left. repeat split; auto; intros H; subst;
    eapply ord_irrefl...
  - right; right. repeat split; auto; intros H; subst;
    eapply ord_irrefl... eapply ord_trans...
Qed.

(* 序数的序是连通的 *)
Corollary ord_connected : ∀ α β, is_ord α → is_ord β →
  α ≠ β → α ∈ β ∨ β ∈ α.
Proof.
  intros α β Hα Hβ Hnq.
  destruct (ord_trich α β) as [[H []]|[[H []]|[H []]]]; tauto.
Qed.

(* 序数的小于等于关系与子集关系等价 *)
Corollary ord_leq_iff_sub : ∀ α β, is_ord α → is_ord β → α ≤ β ↔ α ⊆ β.
Proof with eauto.
  intros α β Hα Hβ. split.
  - intros [].
    + intros x Hx. eapply ord_trans...
    + subst. apply sub_refl.
  - intros H. destruct (classic (α = β)). right...
    left. apply ord_connected in H0 as []...
    apply H in H0. exfalso. eapply ord_irrefl...
Qed.

(* 序数的任意前节也是序数 *)
Fact seg_of_ord : ∀ α, is_ord α → ∀β ∈ α, seg β (MemberRel α) = β.
Proof with eauto.
  intros α Hα β Hlt.
  apply ExtAx. split; intros Hx.
  - apply SepE2 in Hx. apply binRelE3 in Hx...
  - apply segI. apply binRelI... eapply ord_trans...
Qed.

(* 序数的非空集合一定有最小序数 *)
Theorem ords_has_minimum : ∀ A, is_ords A → ⦿ A → 
  ∃μ ∈ A, ∀α ∈ A, μ ≤ α.
Proof with eauto.
  intros A Hord [β Hβ].
  destruct (classic (β ∩ A = ∅)) as [H0|Hne].
  - exists β. split... intros α Hα.
    destruct (classic (α = β))...
    apply ord_connected in H as []; [| |apply Hord..]...
    eapply EmptyE in H0. exfalso. apply H0. apply BInterI...
  - set (β ∩ A) as B. fold B in Hne.
    apply EmptyNE in Hne... apply Hord in Hβ.
    set (constr β (MemberRel β) (ord_woset β Hβ)) as S.
    pose proof (min_correct S B) as [Hm Hmin]...
    + intros b Hb. apply BInterE in Hb as []...
    + set ((Min S)[B]) as μ. fold μ in Hm, Hmin.
      apply BInterE in Hm as [Hμβ Hμs]...
      exists μ. split... intros α Hαs.
      destruct (classic (α ∈ β)) as [Hαβ|Hαβ].
      * assert (α ∈ B) by (apply BInterI; auto).
        apply Hmin in H as []... apply binRelE3 in H...
      * apply Hord in Hαs.
        assert (β ≤ α). {
          destruct (ord_trich α β) as [[H []]|[[H []]|[H []]]];
          auto; tauto.
        }
        apply ord_leq_iff_sub in H... apply H in Hμβ...
Qed.

(* 序数集是良序集 *)
Theorem ords_woset : ∀ A, is_ords A → woset A (MemberRel A).
Proof with eauto.
  intros S Hord. repeat split.
  - apply memberRel_is_binRel.
  - intros α β γ Hαβ Hβγ.
    apply binRelE2 in Hαβ as [Hα [Hβ Hαβ]].
    apply binRelE2 in Hβγ as [_  [Hγ Hβγ]].
    apply binRelI... eapply ord_trans... apply Hord...
  - intros α Hα β Hβ.
    destruct (ord_trich α β) as [[H []]|[[H []]|[H []]]].
    apply Hord... apply Hord...
    + left. repeat split... apply binRelI...
      intros H2. apply H1. apply binRelE3 in H2...
    + right; left. repeat split...
      intros H2. apply H. apply binRelE3 in H2...
      intros H2. apply H1. apply binRelE3 in H2...
    + right; right. repeat split...
      intros H2. apply H. apply binRelE3 in H2...
      apply binRelI...
  - intros B Hne Hsub.
    pose proof (ords_has_minimum B) as [μ Hmin]...
      { intros α Hα. apply Hord. apply Hsub... }
    exists μ. eapply ε_minimum_iff...
Qed.

(* 由序数组成的传递集是序数 *)
Corollary transitive_set_of_ords_is_ord :
  ∀ A, is_ords A → trans A → is_ord A.
Proof with auto.
  intros A Hord Htr.
  apply transitive_set_well_ordered_by_epsilon_is_ord...
  apply ords_woset...
Qed.

(* 零是序数 *)
Corollary empty_is_ord : is_ord ∅.
Proof.
  apply transitive_set_of_ords_is_ord.
  intros x Hx. exfalso0. intros x y _ Hy. exfalso0.
Qed.
Hint Resolve empty_is_ord : core.

(* 序数的后继是序数 *)
Corollary ord_suc_is_ord : ∀ α, is_ord α → is_ord α⁺.
Proof with eauto.
  intros α Hord.
  apply transitive_set_of_ords_is_ord.
  - intros x Hx. apply BUnionE in Hx as [].
    + eapply ord_is_ords...
    + apply SingE in H. subst...
  - apply ex4_2. apply ord_trans...
Qed.

(* 序数集的并是序数 *)
Corollary union_of_ords_is_ord : ∀ A, is_ords A → is_ord (⋃ A).
Proof with eauto.
  intros A Hord.
  apply transitive_set_of_ords_is_ord.
  - intros x Hx. apply UnionAx in Hx as [y [Hy Hx]].
    apply Hord in Hy. eapply ord_is_ords...
  - apply trans_sub. intros δ Hδ.
    apply UnionAx in Hδ as [α [Hα Hδ]].
    eapply sub_tran; revgoals. apply union_is_ub...
    apply ord_leq_iff_sub... eapply ord_is_ords.
    apply Hord... apply Hδ. apply Hord...
Qed.

(* 序数上界 *)
Definition is_ub := λ μ A, is_ord μ ∧ ∀α ∈ A, α ≤ μ.

(* 序数/序数集上确界 *)
Definition sup := λ A, ⋃ A.
Definition is_sup : set → set → Prop :=
  λ μ A, is_ub μ A ∧ ∀ α, is_ub α A → μ ≤ α.

(* 序数集的并是其上确界 *)
Lemma sup_correct : ∀ A, is_ords A → is_sup (sup A) A.
Proof with auto.
  intros A Hord.
  apply union_of_ords_is_ord in Hord as Hu.
  repeat split...
  - intros α Hα. apply ord_leq_iff_sub...
    apply Hord... apply union_is_ub...
  - intros α [H1 H2]. apply ord_leq_iff_sub...
    apply union_is_sup. intros a Ha.
    apply ord_leq_iff_sub... apply Hord... apply H2...
Qed.

(* 序数的后继是大于该序数的最小序数 *)
Lemma ord_lt_iff_suc_leq : ∀ α β, is_ord α → is_ord β →
  α ∈ β → α⁺ ≤ β.
Proof with eauto.
  intros α β H1 H2 Hα. apply ord_leq_iff_sub...
  apply ord_suc_is_ord... intros x Hx.
  apply BUnionE in Hx as [].
  - eapply ord_trans...
  - apply SingE in H. subst...
Qed.

(* ω是序数 *)
Fact ω_is_ord : is_ord ω.
Proof.
  set (WOStruct.constr ω Lt Lt_wellOrder) as S.
  exists S. symmetry. apply α_ω.
Qed.

(* ω是序数集 *)
Fact ω_is_ords : is_ords ω.
Proof. apply ord_is_ords. apply ω_is_ord. Qed.

(* 自然数是序数 *)
Fact nat_is_ord : ∀n ∈ ω, is_ord n.
Proof. intros n Hn. apply ω_is_ords. apply Hn. Qed.

(* 有限序数的上确界是ω *)
Fact sup_of_ω_is_ω : is_sup ω ω.
Proof.
  replace ω with (⋃ ω) at 1.
  apply sup_correct. apply ω_is_ords.
  apply sub_antisym. apply trans_union_sub. apply ω_trans.
  intros n Hn. apply UnionAx. exists n⁺. split.
  apply ω_inductive. apply Hn. apply suc_has_n.
Qed.

(* 布拉利-福尔蒂悖论：不存在包含所有序数的集合 *)
Theorem Burali_Forti : ¬ ∃ A, ∀ α, is_ord α → α ∈ A.
Proof with eauto.
  intros [A HA].
  set {x ∊ A | λ x, is_ord x} as Ω.
  assert (HΩ: ∀ α, is_ord α ↔ α ∈ Ω). {
    split; intros H. apply SepI... apply SepE2 in H...
  }
  cut (is_ord Ω). {
    intros Hord. apply HΩ in Hord as Hrefl.
    eapply ord_irrefl...
  }
  apply transitive_set_well_ordered_by_epsilon_is_ord.
  - intros x y Hxy Hy. apply HΩ.
    eapply ord_is_ords. apply SepE2 in Hy... apply Hxy.
  - apply ords_woset. intros α Hα. apply SepE2 in Hα...
Qed.

(** more about order of ord parallel to nat in EST4_3 **)

(* 两个序数不能同时满足大于关系和小于关系 *)
Lemma ord_not_lt_gt : ∀ α β, is_ord α → is_ord β →
  α ∈ β → β ∈ α → ⊥.
Proof.
  intros α β Hα Hβ Hαβ Hβα. eapply ord_irrefl. apply Hα.
  eapply ord_trans; eauto.
Qed.

(* 两个序数不能同时满足等于关系和小于关系 *)
Lemma ord_not_lt_self : ∀ α β, is_ord α → is_ord β →
  α = β → α ∈ β → ⊥.
Proof.
  intros α β Hα Hβ Heq Hαβ. subst. eapply ord_irrefl; eauto.
Qed.

(* 两个序数不能同时满足小于等于关系和大于关系 *)
Lemma ord_not_leq_gt : ∀ α β, is_ord α → is_ord β →
  α ≤ β → β ∈ α → ⊥.
Proof with eauto.
  intros α β Hα Hβ Hle Hgt. destruct Hle.
  - eapply ord_not_lt_gt; revgoals...
  - eapply ord_not_lt_self; revgoals...
Qed.

(* 序数的小于等于关系与小于后继的转化 *)
Lemma ord_leq_iff_lt_suc : ∀ α β, is_ord α → is_ord β →
  α ≤ β ↔ α ∈ β⁺.
Proof with nauto.
  intros α β Hα Hβ. split.
  - intros []. apply BUnionI1... subst...
  - intros H. apply BUnionE in H as []. left...
    right. apply SingE in H...
Qed.

(* 序数后继保序 *)
Lemma ord_suc_preserve_lt : ∀ α β, is_ord α → is_ord β →
  α ∈ β ↔ α⁺ ∈ β⁺.
Proof with eauto.
  intros α β Hα Hβ. split; intros H.
  - destruct (classic (α⁺ = β)) as [|Hnq]. {
      apply BUnionI2. subst...
    }
    apply BUnionI1.
    assert (Hordα': is_ord α⁺) by (apply ord_suc_is_ord; auto).
    apply ord_connected in Hnq as [|Hβα]... exfalso.
    apply BUnionE in Hβα as [Hβα|Heq].
    + eapply ord_not_lt_gt;revgoals...
    + apply SingE in Heq. eapply ord_not_lt_self; revgoals...
  - apply ord_leq_iff_lt_suc in H as []...
    + eapply ord_trans; revgoals... apply suc_has_n.
    + rewrite <- H. apply suc_has_n.
    + apply ord_suc_is_ord...
Qed.

(* 序数后继是单射 *)
Lemma ord_suc_injective : ∀ α β, is_ord α → is_ord β →
  α⁺ = β⁺ → α = β.
Proof with auto.
  intros α β Hα Hβ Heq.
  assert (⋃α⁺ = ⋃β⁺) by congruence.
  apply ord_trans in Hα. apply ord_trans in Hβ.
  apply trans_union_suc in Hα.
  apply trans_union_suc in Hβ. congruence.
Qed.

(* 后继序数大于零 *)
Lemma ord_suc_has_0 : ∀ α, is_ord α → ∅ ∈ α⁺.
Proof with auto.
  intros α Hα. destruct (classic (∅ = α)).
  - apply BUnionI2. subst...
  - apply ord_connected in H as []...
    apply BUnionI1... exfalso0.
Qed.

(* 任意序数不等于其后继 *)
Lemma ord_neq_suc : ∀ α, is_ord α → α ≠ α⁺.
Proof.
  intros α Hα. pose proof (suc_has_n α). intros Heq.
  rewrite <- Heq in H at 1. apply (ord_irrefl α); auto.
Qed.

(* 不等于零的序数大于零 *)
Lemma ord_nq_0_gt_0 : ∀ α, is_ord α → α ≠ ∅ ↔ ∅ ∈ α.
Proof with auto.
  intros α Hα. split; intros.
  - apply ord_connected in H as []... exfalso0.
  - destruct (classic (α = ∅))... subst. exfalso0.
Qed.

(* 任意序数大于等于零 *)
Lemma ord_ge_0 : ∀ α, is_ord α → ∅ ≤ α.
Proof with auto.
  intros. apply ord_leq_iff_sub; auto.
  apply empty_sub_all.
Qed.

(* 序数的小于关系与真子集关系等价 *)
Lemma ord_lt_iff_psub : ∀ α β, is_ord α → is_ord β →
  α ∈ β ↔ α ⊂ β.
Proof with eauto.
  intros α β Hα Hβ. split.
  - intros Hlt. split. apply ord_leq_iff_sub...
    intros Heq. subst. eapply ord_irrefl...
  - intros [Hsub Hnq].
    apply ord_connected in Hnq as []...
    apply Hsub in H. exfalso. eapply ord_irrefl...
Qed.

Lemma ord_lt_iff_not_sub : ∀ α β, is_ord α → is_ord β →
  α ∈ β ↔ β ⊈ α.
Proof with auto.
  intros α β Hα Hβ. split; intros H.
  - intros Hsub. apply Hsub in H. apply (ord_irrefl α)...
  - destruct (classic (α = β)) as [Heq|Hnq].
    + exfalso. apply H. subst...
    + apply ord_connected in Hnq as [|Hlt]... exfalso.
      apply H. apply ord_lt_iff_psub...
Qed.

Lemma ord_lt_suc_iff_sub : ∀ α β, is_ord α → is_ord β →
  α ⊆ β ↔ α ∈ β⁺.
Proof.
  intros α β Hα Hβ. rewrite <- (ord_leq_iff_lt_suc α β Hα Hβ).
  symmetry. exact (ord_leq_iff_sub α β Hα Hβ).
Qed.

Lemma ord_leq_iff_not_gt : ∀ α β, is_ord α → is_ord β →
  α ≤ β ↔ β ∉ α.
Proof with eauto.
  intros α β Hα Hβ.
  rewrite (ord_leq_iff_sub α β Hα Hβ).
  split; intros H.
  - intros Hlt. apply ord_lt_iff_not_sub in Hlt...
  - destruct (classic (α ⊆ β))...
    exfalso. apply H. apply ord_lt_iff_not_sub...
Qed.

(* 序数不稠密 *)
Lemma ord_not_dense : ∀ α, is_ord α →
  ¬ ∃ β, is_ord β ∧ α ∈ β ∧ β ∈ α⁺.
Proof with eauto.
  intros α Hα [β [Hβ [Hαβ Hβα]]].
  apply BUnionE in Hβα as [Hlt|Heq].
  - eapply ord_not_lt_gt; revgoals...
  - apply SingE in Heq. eapply ord_not_lt_self; revgoals...
Qed.

(* 序数集最小元的两种定义等价 *)
Lemma ord_ε_minimum_iff_sub_minimum : ∀ α A, is_ords A →
  ε_minimum α A ↔ sub_minimum α A.
Proof with auto.
  split; intros [Hm Hmin]; split; auto; intros β Hβ;
  apply Hmin in Hβ as Hle; (apply ord_leq_iff_sub; [apply H..|])...
Qed.

(* 序数集最大元的两种定义等价 *)
Lemma ord_ε_maximum_iff_sub_maximum : ∀ α A, is_ords A →
  ε_maximum α A ↔ sub_maximum α A.
Proof with auto.
  split; intros [Hm Hmax]; split; auto; intros β Hβ;
  apply Hmax in Hβ as Hle; (apply ord_leq_iff_sub; [apply H..|])...
Qed.

(* 序数集的阿基米德性 *)
Definition ord_archimedean := λ A, ∀a ∈ A, ∃b ∈ A, a ∈ b.

(* 具有阿基米德性的序数集没有最大元 *)
Lemma ord_archimedean_impl_no_maximum : ∀ A, is_ords A →
  ord_archimedean A → ¬∃μ, sub_maximum μ A.
Proof with auto.
  intros A Hord Hnmax [μ [Hμ Hmax]].
  pose proof (Hnmax μ Hμ) as [β [Hβ Hβμ]]. apply Hmax in Hβ.
  apply Hβ in Hβμ. apply (ord_irrefl μ)... apply Hord in Hμ...
Qed.

(* 没有最大元的非空序数集具有阿基米德性 *)
Lemma ord_archimedean_if_no_maximum : ∀ A, ⦿ A → is_ords A →
  (¬∃μ, sub_maximum μ A) → ord_archimedean A.
Proof with eauto.
  intros A [γ Hγ] Hord Hnmax α Hα.
  eapply not_ex_all_not in Hnmax.
  apply not_and_or in Hnmax as []. exfalso...
  apply set_not_all_ex_not in H as [μ [Hμ Hαμ]].
  apply ord_lt_iff_not_sub in Hαμ; [|apply Hord..]...
  exists μ. split...
Qed.

(* 非空序数集具有阿基米德性当且仅当它没有最大元 *)
Theorem ord_archimedean_iff_no_maximum : ∀ A, ⦿ A → is_ords A →
  ord_archimedean A ↔ ¬∃μ, sub_maximum μ A.
Proof with auto.
  intros A Hne Hord. split; intros H.
  - apply ord_archimedean_impl_no_maximum...
  - apply ord_archimedean_if_no_maximum...
Qed.

(* 后继序数 *)
Definition is_suc := λ α, ∃ β, is_ord β ∧ α = β⁺.
(* 极限序数 *)
Definition is_limit := λ α, is_ord α ∧ α = sup α.

(* 后继序数的上确界是其前驱 *)
Lemma sup_of_suc : ∀ α, is_ord α → sup α⁺ = α.
Proof.
  intros. apply ord_trans in H. apply trans_union_suc in H.
  unfold sup. rewrite H. reflexivity.
Qed.

(* 后继序数包含上确界 *)
Lemma suc_contains_sup : ∀ α, is_suc α → sup α ∈ α.
Proof.
  intros α [β [Hβ Heqα]]. subst α.
  rewrite sup_of_suc. apply suc_has_n. apply Hβ.
Qed.

(* 后继序数的上确界是其最大元 *)
Lemma maximum_of_suc : ∀ α, is_suc α → ε_maximum (sup α) α.
Proof with auto.
  intros. split. apply suc_contains_sup...
  intros β Hβ. apply sup_correct...
  destruct H as [γ [Hγ Heq]]. rewrite Heq.
  apply ord_is_ords. apply ord_suc_is_ord...
Qed.

(* 极限序数不含上确界 *)
Lemma limit_ord_not_contains_sup : ∀ α, is_limit α → sup α ∉ α.
Proof with auto.
  intros α [Hα Heq] H. rewrite Heq in H at 2.
  apply (ord_irrefl (sup α))...
  apply union_of_ords_is_ord. apply ord_is_ords...
Qed.

(* 零是极限序数（也可以单独把零分为一类） *)
Lemma empty_is_limit : is_limit ∅.
Proof.
  split. apply empty_is_ord.
  unfold sup. rewrite union_empty. reflexivity.
Qed.

(* 极限序数具有阿基米德性 *)
Lemma limit_ord_archimedean : ∀ α, is_limit α → ord_archimedean α.
Proof.
  intros α [Hα Heq] β Hβ. rewrite Heq in Hβ.
  apply UnionAx in Hβ. apply Hβ.
Qed.

(* 极限序数无最大元 *)
Lemma limit_ord_no_maximum : ∀ α, is_limit α → ¬ ∃ μ, sub_maximum μ α.
Proof.
  intros. apply ord_archimedean_impl_no_maximum.
  apply ord_is_ords. apply H. apply limit_ord_archimedean. apply H.
Qed.

(* 序数是极限序数当且仅当它不是后继序数 *)
Lemma ord_is_limit_iff_not_suc : ∀ α, is_ord α →
  is_limit α ↔ ¬ is_suc α.
Proof with eauto.
  split.
  - intros [Hα H1] [β [Hβ H2]]. rewrite H2 in H1 at 2.
    rewrite sup_of_suc in H1... rewrite H1 in H2.
    eapply ord_neq_suc...
  - intros Hnsuc. destruct (classic (is_limit α)) as [|Hnlim]...
    exfalso. apply Hnsuc. clear Hnsuc.
    apply not_and_or in Hnlim as [|Hneq]. exfalso...
    assert (Hne: sup α ⊂ α). {
      split... apply union_is_sup.
      intros β Hβα. apply ord_leq_iff_sub...
      apply ord_is_ords in H. apply H...
    }
    apply comp_nonempty in Hne as [β Hβ].
    apply SepE in Hβ as [Hβ Hβ'].
    assert (Hordβ: is_ord β). {
      apply ord_is_ords in H. apply H...
    }
    assert (Hordβ': is_ord β⁺). {
      apply ord_suc_is_ord...
    }
    exists β. split...
    destruct (classic (α = β⁺)) as [|Hnq]...
    exfalso. apply ord_connected in Hnq as [H1|H2]...
    + apply (ord_not_dense β)...
    + apply Hβ'. apply UnionAx. exists (β⁺).
      split... apply suc_has_n.
Qed.

(* 序数是后继序数当且仅当它不是极限序数 *)
Corollary ord_is_suc_iff_not_limit : ∀ α, is_ord α →
  is_suc α ↔ ¬ is_limit α.
Proof.
  intros. pose proof (ord_is_limit_iff_not_suc α H). tauto.
Qed.

(* 序数要么是后继序数要么是极限序数 *)
Theorem ord_is_suc_or_limit : ∀ α, is_ord α →
  is_suc α ∨ is_limit α.
Proof with auto.
  intros. destruct (classic (is_suc α))...
  right. apply ord_is_limit_iff_not_suc...
Qed.

End Ordinals.
Hint Immediate ord_is_ord : core.
Hint Resolve empty_is_ord : core.
Hint Resolve ω_is_ord : core.
