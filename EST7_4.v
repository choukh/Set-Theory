(** Based on "Elements of Set Theory" Chapter 7 Part 4 **)
(** Coq coding by choukh, Dec 2020 **)

Require Export ZFC.EST7_3.
Require Import ZFC.lib.FuncFacts.
Require Import ZFC.lib.WosetMin.
Import WosetMin.FullVer.

(*** EST第七章4：序数的定义，序数的序，布拉利-福尔蒂悖论 ***)

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

Section OrdDef.
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

Theorem ord_irrefl : ∀ α, is_ord α → α ∉ α.
Proof.
  intros α [S H]. subst. intros H.
  pose proof (ordE _ _ H) as [s [Hs Heq]].
  rewrite <- Heq in H. eapply e_irrefl; eauto.
Qed.

Theorem ord_trich : ∀ α β, is_ord α → is_ord β →
  α ∈ β ∧ α ≠ β ∧ β ∉ α ∨
  α ∉ β ∧ α = β ∧ β ∉ α ∨
  α ∉ β ∧ α ≠ β ∧ β ∈ α.
Proof with eauto.
  intros α β Hα Hβ.
  cut (α ∈ β ∨ α = β ∨ β ∈ α). {
    intros [Hab|[Hnq|Hba]].
    - left. split... split; intros H; subst;
      eapply ord_irrefl... eapply ord_trans...
    - right; left. repeat split; auto; intros H; subst;
      eapply ord_irrefl...
    - right; right. repeat split; auto; intros H; subst;
      eapply ord_irrefl... eapply ord_trans...
  }
  destruct Hα as [S Heqα].
  destruct Hβ as [T Heqβ]. subst.
  destruct (wo_iso_trich S T) as [H|[[t [Ht H]]|[t [Ht H]]]].
  - right; left. apply ord_well_defined...
  - left. apply (ordI _ _ t)...
    rewrite (ord_well_defined _ (Seg t T)), <- seg_α...
  - right; right. apply (ordI _ _ t)...
    rewrite (ord_well_defined _ (Seg t S)), seg_α... symmetry...
Qed.

End OrdDef.

Corollary ord_connected : ∀ α β, is_ord α → is_ord β →
  α ≠ β → α ∈ β ∨ β ∈ α.
Proof.
  intros α β Hα Hβ Hnq.
  destruct (ord_trich α β) as [[H []]|[[H []]|[H []]]]; tauto.
Qed.

Corollary ordLeq_iff_sub : ∀ α β, is_ord α → is_ord β → α ≤ β ↔ α ⊆ β.
Proof with eauto.
  intros α β Hα Hβ. split.
  - intros [].
    + intros x Hx. eapply ord_trans...
    + subst. apply sub_refl.
  - intros H. destruct (classic (α = β)). right...
    left. apply ord_connected in H0 as []...
    apply H in H0. exfalso. eapply ord_irrefl...
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
    pose proof (min_correct β (MemberRel β) B) as [Hm Hmin]...
    + apply ord_woset. apply Hord...
    + apply EmptyNE in Hne...
    + intros b Hb. apply BInterE in Hb as []...
    + set ((Min β (MemberRel β))[B]) as μ. fold μ in Hm, Hmin.
      apply BInterE in Hm as [Hμβ Hμs]...
      exists μ. split... intros α Hαs.
      destruct (classic (α ∈ β)) as [Hαβ|Hαβ].
      * assert (α ∈ B) by (apply BInterI; auto).
        apply Hmin in H as []... apply binRelE2 in H as [_ [_ H]]...
      * apply Hord in Hαs. apply Hord in Hβ.
        assert (β ≤ α). {
          destruct (ord_trich α β) as [[H []]|[[H []]|[H []]]];
          auto; tauto.
        }
        apply ordLeq_iff_sub in H... apply H in Hμβ...
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
      intros H2. apply H1. apply binRelE2 in H2 as [_ [_ H2]]...
    + right; left. repeat split...
      intros H2. apply H. apply binRelE2 in H2 as [_ [_ H2]]...
      intros H2. apply H1. apply binRelE2 in H2 as [_ [_ H2]]...
    + right; right. repeat split...
      intros H2. apply H. apply binRelE2 in H2 as [_ [_ H2]]...
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

(* 序数的后继是序数 *)
Corollary suc_is_ord : ∀ α, is_ord α → is_ord α⁺.
Proof with eauto.
  intros α Hprd.
  apply transitive_set_of_ords_is_ord.
  - intros x Hx. apply BUnionE in Hx as [].
    + eapply ord_is_ords...
    + apply SingE in H. subst...
  - apply ex4_2. apply ord_trans...
Qed.

(* 并集是包含关系的上界 *)
Lemma union_is_ub : ∀A, ∀a ∈ A, a ⊆ ⋃A.
Proof. exact ex2_3. Qed.

(* 并集是包含关系的上确界 *)
Lemma union_is_sup: ∀ A B, (∀a ∈ A, a ⊆ B) → ⋃A ⊆ B.
Proof. exact ex2_5. Qed.

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
    apply ordLeq_iff_sub... eapply ord_is_ords...
    apply Hord... apply Hord...
Qed.

(* 序数上界 *)
Definition ordUb : set → set → Prop :=
  λ μ A, is_ord μ ∧ ∀α ∈ A, α ≤ μ.

(* 序数上确界 *)
Definition ordSup : set → set → Prop :=
  λ μ A, ordUb μ A ∧ ∀ α, ordUb α A → μ ≤ α.

(* 序数集的并是其上确界 *)
Fact sup_of_ords : ∀ A, is_ords A → ordSup (⋃ A) A.
Proof with auto.
  intros A Hord.
  apply union_of_ords_is_ord in Hord as Hu.
  repeat split...
  - intros α Hα. apply ordLeq_iff_sub...
    apply Hord... apply union_is_ub...
  - intros α [H1 H2]. apply ordLeq_iff_sub...
    apply union_is_sup. intros a Ha.
    apply ordLeq_iff_sub... apply Hord... apply H2...
Qed.

(* 序数的后继是大于该序数的最小序数 *)
Fact ord_suc_correct : ∀ α β, is_ord α → is_ord β → α ∈ β → α⁺ ≤ β.
Proof with eauto.
  intros α β H1 H2 Hα. apply ordLeq_iff_sub...
  apply suc_is_ord... intros x Hx.
  apply BUnionE in Hx as [].
  - eapply ord_trans...
  - apply SingE in H. subst...
Qed.

(* 布拉利-福尔蒂悖论 *)
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
    eapply ord_is_ords... apply SepE2 in Hy...
  - apply ords_woset. intros α Hα. apply SepE2 in Hα...
Qed.

End OrdinalNumber.
