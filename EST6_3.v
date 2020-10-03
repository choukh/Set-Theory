(** Based on "Elements of Set Theory" Chapter 6 Part 3 **)
(** Coq coding by choukh, Sep 2020 **)

Require Export ZFC.EX6_1.
Require Import ZFC.lib.IndexedFamilyUnion.

(*** EST第六章3：支配关系，施罗德-伯恩斯坦定理，基数的序，阿列夫零 ***)

(* 集合的支配关系 *)
Definition dominate : set → set → Prop := λ A B, ∃ f, f: A ⇔ B.
Notation "A ≼ B" := (dominate A B) (at level 70).
Notation "A ≺ B" := (A ≼ B ∧ A ≉ B) (at level 70).

(* 等势的集合相互支配 *)
Lemma eqnum_dominate : ∀ A B, A ≈ B → A ≼ B ∧ B ≼ A.
Proof with auto.
  intros * [f Hf]. split.
  exists f. apply bijection_is_surjective_injection...
  exists (f⁻¹). apply bijection_is_surjective_injection. apply inv_bijection...
Qed.

(* 支配关系是自反的 *)
Lemma dominate_refl : ∀ A, A ≼ A.
Proof.
  intros. exists (Ident A).
  apply bijection_is_surjective_injection. apply ident_bijective.
Qed.
Hint Immediate dominate_refl : core.

(* 支配关系是传递的 *)
Lemma dominate_tran : ∀ A B C, A ≼ B → B ≼ C → A ≼ C.
Proof.
  intros * [f Hf] [g Hg].
  exists (g ∘ f). eapply compo_injection; eauto.
Qed.

(* 可以证明支配关系也是反对称的 *)

(* 施罗德-伯恩斯坦定理 *)
Theorem Schröeder_Bernstein : ∀ A B, A ≼ B → B ≼ A → A ≈ B.
Proof with eauto; try congruence.
  intros * [f [Hif [Hdf Hrf]]] [g [Hig [Hdg Hrg]]].
  set (A - ran g) as C₀.
  set (λ x, g⟦f⟦x⟧⟧) as F.
  set (λ n, iter n F C₀) as Cᵢ. set (⋃ᵢ Cᵢ) as C.
  set (λ n, f⟦Cᵢ n⟧) as Dᵢ. set (⋃ᵢ Dᵢ) as D.
  set (Func A B (λ x, match (ixm (x ∈ C)) with
    | inl _ => f[x]
    | inr _ => g⁻¹[x]
  end)) as h.
  assert (Hif' := Hif). destruct Hif' as [Hff Hsf].
  assert (Hig' := Hig). destruct Hig' as [Hfg Hsg].
  assert (HeqC0: Cᵢ 0 = C₀) by reflexivity.
  assert (HeqCn: ∀ n, Cᵢ (S n) = g⟦Dᵢ n⟧). { intros. unfold Dᵢ... }
  assert (HsubC: C₀ ⊆ C). {
    intros x Hx. eapply IFUnionI. rewrite HeqC0...
  }
  assert (HsubA: C ⊆ A). {
    intros x Hx. apply IFUnionE in Hx as [m Hm].
    destruct m. rewrite HeqC0 in Hm. apply SepE in Hm as []...
    rewrite HeqCn in Hm. apply img_included in Hm. apply Hrg...
  }
  assert (Hxrg:∀x ∈ A, x ∉ C → x ∈ ran g). {
    intros x Hx H. destruct (classic (x ∈ ran g))...
    exfalso. apply H. apply HsubC. apply SepI...
  }
  assert (Hdc: ∀ n, ∀x ∈ ran g, (g⁻¹)[x] ∈ Dᵢ n → x ∈ C). {
    intros n x Hx H. eapply IFUnionI. rewrite HeqCn.
    eapply imgI. apply H. rewrite inv_op. apply func_correct.
    apply inv_func_iff_sr... rewrite inv_dom...
  }
  exists h. apply meta_bijective.
  - intros x Hx. destruct (ixm (x ∈ C)).
    + eapply ap_ran. split... apply Hx.
    + rewrite <- Hdg, <- inv_ran. eapply ap_ran. split...
      apply inv_func_iff_sr... rewrite inv_dom. apply Hxrg...
  - intros x1 Hx1 x2 Hx2 Heq.
    destruct (ixm (x1 ∈ C)) as [H1|H1];
    destruct (ixm (x2 ∈ C)) as [H2|H2].
    + apply (injectiveE f)...
    + apply IFUnionE in H1 as [m Hcm].
      exfalso. apply H2. eapply Hdc. apply Hxrg...
      rewrite <- Heq. eapply imgI. apply Hcm. apply func_correct...
    + apply IFUnionE in H2 as [m Hcm].
      exfalso. apply H1. eapply Hdc. apply Hxrg...
      rewrite Heq. eapply imgI. apply Hcm. apply func_correct...
    + apply (injectiveE g⁻¹)... apply inv_injective...
      rewrite inv_dom. apply Hxrg...
      rewrite inv_dom. apply Hxrg...
  - intros y Hy. destruct (classic (y ∈ D)). {
      apply IFUnionE in H as [m H].
      apply imgE in H as [x [Hx Hpf]].
      apply IFUnionI in Hx. apply func_ap in Hpf...
      exists x. split. apply HsubA...
      destruct (ixm (x ∈ C))... exfalso... 
    }
    exists (g[y]). split. eapply ap_ran... split...
    destruct (ixm (g[y] ∈ C)) as [Hgy|Hgy];
      [exfalso|rewrite inv_dom_reduction]...
    apply IFUnionE in Hgy as [m Hgy]. destruct m.
    + rewrite HeqC0 in Hgy. apply SepE in Hgy as [_ Hgy].
      apply Hgy. eapply ap_ran... split...
    + rewrite HeqCn in Hgy. apply imgE in Hgy as [x [Hx Hp]].
      apply domI in Hp as Hxdg. apply func_ap in Hp...
      apply injectiveE in Hp... subst x. apply H. eapply IFUnionI...
Qed.

(* 子集被支配 *)
Lemma dominate_sub : ∀ A B, A ⊆ B → A ≼ B.
Proof with auto.
  intros. exists (Ident A).
  pose proof (ident_bijective A) as [Hi [Hd Hr]].
  split; [|split]... rewrite Hr...
Qed.

(* 集合的并支配其元素 *)
Lemma union_dominate : ∀ a A, a ∈ A → a ≼ ⋃A.
Proof. intros. apply dominate_sub. apply ex2_3. apply H. Qed.

(* 若一个集合分别是两个等势的集合的子集和母集，则这三个集合等势 *)
Corollary sub_squeeze_to_eqnum : ∀ A B C,
  A ⊆ B → B ⊆ C → A ≈ C → A ≈ B ∧ B ≈ C.
Proof.
  intros * H1 H2 Hqn.
  apply dominate_sub in H1.
  apply dominate_sub in H2.
  apply eqnum_dominate in Hqn as [H3 H4].
  split; apply Schröeder_Bernstein; auto;
  eapply dominate_tran; eauto.
Qed.

(* B支配A当且仅当存在B的子集与A等势 *)
Lemma dominate_iff : ∀ A B, A ≼ B ↔ (∃ C, C ⊆ B ∧ A ≈ C).
Proof with auto.
  intros. split.
  - intros [f [Hi [Hd Hr]]]. exists (dom f⁻¹). split.
    + intros x Hx. rewrite inv_dom in Hx. apply Hr...
    + exists f. split; [|split]... rewrite inv_dom...
  - intros [C [Hsub [f [Hi [Hd Hr]]]]]. exists f.
    split; [|split]... rewrite Hr...
Qed.

(* 任意自然数被ω支配 *)
Lemma ω_dominate : ∀n ∈ ω, n ≼ ω.
Proof with auto.
  intros n Hn. apply dominate_sub.
  apply trans_sub... apply ω_trans.
Qed.

(* 被有限集支配的集合是有限集 *)
Lemma dominated_by_finite_is_finite : ∀ A B,
  A ≼ B → finite B → finite A.
Proof with auto.
  intros A B [f [Hf [Hd Hr]]] Hfin.
  apply set_finite_iff_eqnum_finite_set.
  exists (dom (f⁻¹)). split.
  - symmetry. exists (f⁻¹). split; [|split]...
    apply inv_injective... rewrite inv_ran...
  - apply (sub_of_finite_is_finite _ B)...
    intros y Hy. rewrite inv_dom in Hy. apply Hr...
Qed.

(* 基数的序关系 *)
Definition CardLeq : set → set → Prop := λ 𝜅 𝜆,
  is_card 𝜅 ∧ is_card 𝜆 ∧ 𝜅 ≼ 𝜆.
Notation "𝜅 ≤ 𝜆" := (CardLeq 𝜅 𝜆) : Card_scope.

(* 两个集合的基数有序关系当且仅当这两个集合有支配关系 *)
Lemma cardLeq_iff : ∀ A B, |A| ≤ |B| ↔ A ≼ B.
Proof with eauto; try congruence.
  intros. split.
  - intros [_ [_ Hdm]].
    apply dominate_iff in Hdm as [C [Hsub H1]].
    rewrite <- CardAx0 in H1.
    pose proof (CardAx0 B) as H2. symmetry in H2.
    destruct H1 as [f [Hif [Hdf Hrf]]].
    destruct H2 as [g [Hig [Hdg Hrg]]].
    exists (g ∘ f). split; [|split].
    + apply compo_injective...
    + destruct Hif as [Hff _].
      destruct Hig as [Hfg _]. rewrite compo_dom...
      apply ExtAx. split; intros Hx.
      * apply SepE in Hx as []...
      * apply SepI... rewrite Hdg. apply Hsub.
        eapply ap_ran... split... split...
    + destruct Hif as [Hff _]. rewrite compo_ran...
      intros x Hx. apply SepE in Hx as []...
  - intros [f Hf]. split; [|split]...
    pose proof (CardAx0 A) as Hg.
    symmetry in Hg. destruct Hg as [g Hg].
    pose proof (CardAx0 B) as [h Hh].
    exists (h ∘ f ∘ g). eapply compo_injection.
    apply bijection_is_surjective_injection. apply Hg.
    eapply compo_injection. apply Hf.
    apply bijection_is_surjective_injection. apply Hh.
Qed.

Lemma cardLeq : ∀ 𝜅 𝜆, 𝜅 ≤ 𝜆 → |𝜅| ≤ |𝜆|.
Proof. intros * [_ [_ H]]. apply cardLeq_iff. apply H. Qed.

(* 基数的序关系良定义 *)
Lemma cardLeq_well_defined : ∀ K₁ K₂ L₁ L₂,
  K₁ ≈ K₂ → L₁ ≈ L₂ → K₁ ≼ L₁ ↔ K₂ ≼ L₂.
Proof with eauto.
  cut (∀ K₁ K₂ L₁ L₂, K₁ ≈ K₂ → L₁ ≈ L₂ → K₁ ≼ L₁ → K₂ ≼ L₂). {
    intros Hstar * Hk Hl. split; intros.
    eapply Hstar... eapply Hstar.
    symmetry... symmetry... apply H.
  }
  intros * Hf [g Hg] [h Hh].
  symmetry in Hf. destruct Hf as [f Hf].
  exists (g ∘ h ∘ f). eapply compo_injection.
  apply bijection_is_surjective_injection. apply Hf.
  eapply compo_injection. apply Hh.
  apply bijection_is_surjective_injection. apply Hg.
Qed.

(* 基数的小于关系 *)
Definition CardLt : set → set → Prop := λ 𝜅 𝜆, 𝜅 ≤ 𝜆 ∧ 𝜅 ≠ 𝜆.
Notation "𝜅 <𝐜 𝜆" := (CardLt 𝜅 𝜆) (at level 70) : Card_scope.

(* 两个集合的基数有小于关系当且仅当这两个集合有真支配关系 *)
Lemma cardLt_iff : ∀ A B, |A| <𝐜 |B| ↔ A ≺ B.
Proof with auto.
  intros. split.
  - intros [Hleq Hnq]. apply cardLeq_iff in Hleq.
    split... intros Hqn. apply Hnq. apply CardAx1...
  - intros [Hdm Hnq]. split. apply cardLeq_iff...
    intros Heq. apply Hnq. apply CardAx1...
Qed.

Lemma cardLt : ∀ 𝜅 𝜆, 𝜅 <𝐜 𝜆 → |𝜅| <𝐜 |𝜆|.
Proof with auto.
  intros * [[Hk [Hl H]] Hnq].
  apply cardLt_iff. split... intros Hqn. apply Hnq.
  rewrite card_of_card, (card_of_card 𝜅)... apply CardAx1...
Qed.

Lemma cardLeq_iff_lt_or_eq : ∀ 𝜅 𝜆, 𝜅 ≤ 𝜆 ↔ 𝜅 <𝐜 𝜆 ∨
  (is_card 𝜅 ∧ is_card 𝜆 ∧ 𝜅 = 𝜆).
Proof with auto.
  intros. split.
  - intros. destruct (classic (𝜅 = 𝜆)).
    right. destruct H as [Hk [Hl _]]. split... left. split...
  - intros [[]|[Hk [Hl Heq]]]... split... split... subst...
Qed.

(* 如果两个集合有子集关系，那么这两个集合的基数有序关系 *)
Lemma cardLeq_sub : ∀ A B, A ⊆ B → |A| ≤ |B|.
Proof.
  intros. apply cardLeq_iff. apply dominate_sub. apply H.
Qed.

(* 如果两个基数有序关系，那么存在有子集关系的集合，它们分别与这两个基数等势 *)
Lemma cardLeq_sub_exists : ∀ 𝜅 𝜆, 𝜅 ≤ 𝜆 →
  ∃ K L, K ≈ 𝜅 ∧ L ≈ 𝜆 ∧ K ⊆ L.
Proof with auto.
  intros * [Hk [Hl [f [Hf [Hd Hr]]]]].
  exists (ran f), 𝜆. split; [|split]...
  rewrite <- Hd. symmetry. exists f. split...
Qed.

(* 如果两个基数有序关系，那么存在有子集关系的集合，它们的基数就是这两个基数 *)
Lemma cardLeq_sub_exists_eq : ∀ 𝜅 𝜆, 𝜅 ≤ 𝜆 →
  ∃ K L, |K| = 𝜅 ∧ |L| = 𝜆 ∧ K ⊆ L.
Proof with auto.
  intros * Hleq. assert (H := Hleq). destruct H as [Hk [Hl _]].
  apply cardLeq_sub_exists in Hleq as [K [L [H1 [H2 H]]]].
  exists K, L. repeat split...
  rewrite card_of_card... apply CardAx1...
  rewrite card_of_card... apply CardAx1...
Qed.

(* 任意基数大于等于零 *)
Fact cardLeq_0_k : ∀ 𝜅, is_card 𝜅 → 0 ≤ 𝜅.
Proof with nauto.
  intros 𝜅 Hcd. split; [|split]... apply nat_is_card...
  exists ∅. apply empty_injective.
Qed.

(* 有限基数的序关系与支配关系等价 *)
Lemma fin_cardLeq_iff_dominate : ∀ m n ∈ ω, m ≤ n ↔ m ≼ n.
Proof with auto.
  intros m Hm n Hn. split; intros.
  - apply cardLeq in H. apply cardLeq_iff in H...
  - apply cardLeq_iff in H.
    rewrite <- card_of_nat, <- card_of_nat in H...
Qed.

(* 有限基数的序关系与自然数序关系等价 *)
Lemma fin_cardLeq_iff_leq : ∀ m n ∈ ω, m ≤ n ↔ (m ≤ n)%n.
Proof with auto.
  intros m Hm n Hn. split; intros.
  - apply fin_cardLeq_iff_dominate in H...
    destruct (classic (m = n))... left.
    apply lt_connected in H0 as []... exfalso.
    apply lt_iff_sub in H0 as []... apply dominate_sub in H0.
    apply H1. apply nat_eqnum_eq... apply Schröeder_Bernstein...
  - apply leq_iff_subeq in H... apply dominate_sub in H.
    apply fin_cardLeq_iff_dominate...
Qed.

Lemma fin_cardLt_iff_lt : ∀ m n ∈ ω, m <𝐜 n ↔ m ∈ n.
Proof with eauto.
  intros m Hm n Hn. split; intros.
  - destruct H as [Hleq Hnq]. apply fin_cardLeq_iff_leq in Hleq...
    apply leq_iff_subeq in Hleq... apply lt_iff_sub...
  - split. apply fin_cardLeq_iff_leq...
    intros Heq. subst. eapply lt_not_refl...
Qed.

(* 任意基数都小于自身的幂集的基数 *)
Lemma cardLt_power : ∀ 𝜅, is_card 𝜅 → 𝜅 <𝐜 2 ^ 𝜅.
Proof with auto.
  intros. rewrite (card_of_card 𝜅), <- card_of_power...
  apply cardLt_iff. split; [|apply Cantor's].
  set (Func 𝜅 (𝒫 𝜅) (λ x, ⎨x⎬)) as f.
  exists f. apply meta_injective.
  - intros x Hx. apply PowerAx. intros y Hy.
    apply SingE in Hy. subst...
  - intros x1 Hx1 x2 Hx2 Heq. assert (x1 ∈ ⎨x1⎬) by auto.
    rewrite Heq in H0. apply SingE in H0...
Qed.

(* 基数的序关系是自反的 *)
Lemma cardLeq_refl : ∀ 𝜅, is_card 𝜅 → 𝜅 ≤ 𝜅.
Proof with auto.
  intros. rewrite (card_of_card 𝜅)... apply cardLeq_iff...
Qed.

(* 基数的序关系是传递的 *)
Lemma cardLeq_tran : ∀ 𝜅 𝜆 𝜇, 𝜅 ≤ 𝜆 → 𝜆 ≤ 𝜇 → 𝜅 ≤ 𝜇.
Proof with eauto.
  intros * [Hk [_ H1]] [_ [Hm H2]].
  repeat split... eapply dominate_tran...
Qed.

(* 基数的序关系是反对称的 *)
Lemma cardLeq_asym : ∀ 𝜅 𝜆, 𝜅 ≤ 𝜆 → 𝜆 ≤ 𝜅 → 𝜅 = 𝜆.
Proof with auto.
  intros * [Hk [Hl H1]] [_ [_ H2]].
  rewrite (card_of_card 𝜅), (card_of_card 𝜆)...
  apply CardAx1. apply Schröeder_Bernstein...
Qed.

Corollary cardLeq_lt_tran : ∀ 𝜅 𝜆 𝜇, 𝜅 ≤ 𝜆 → 𝜆 <𝐜 𝜇 → 𝜅 <𝐜 𝜇.
Proof with eauto.
  intros * H1 [H2 Hnq]. split. eapply cardLeq_tran...
  intros Heq. apply Hnq. rewrite Heq in H1. eapply cardLeq_asym...
Qed.

Corollary cardLt_leq_tran : ∀ 𝜅 𝜆 𝜇, 𝜅 <𝐜 𝜆 → 𝜆 ≤ 𝜇 → 𝜅 <𝐜 𝜇.
Proof with eauto.
  intros * [H1 Hnq] H2. split. eapply cardLeq_tran...
  intros Heq. apply Hnq. rewrite <- Heq in H2. eapply cardLeq_asym...
Qed.

(* 基数加法保持等势关系 *)
Lemma cardAdd_preserve_eqnum : ∀ 𝜅 𝜆 𝜇, 𝜅 ≈ 𝜆 → 𝜅 + 𝜇 ≈ 𝜆 + 𝜇.
Proof with auto.
  intros. unfold CardAdd. rewrite <- CardAx0, <- CardAx0.
  apply cardAdd_well_defined.
  apply cardMul_well_defined... apply cardMul_well_defined...
  apply disjoint_cprod_0_1. apply disjoint_cprod_0_1.
Qed.

(* 基数加法保持序关系 *)
Theorem cardAdd_preserve_leq : ∀ 𝜅 𝜆 𝜇, 𝜅 ≤ 𝜆 → 𝜅 + 𝜇 ≤ 𝜆 + 𝜇.
Proof with auto.
  intros * Hleq.
  apply cardLeq_sub_exists in Hleq as [K [L [Hk [Hl H]]]].
  repeat split... eapply cardLeq_well_defined.
  symmetry. apply cardAdd_preserve_eqnum. apply Hk.
  symmetry. apply cardAdd_preserve_eqnum. apply Hl.
  apply cardLeq_sub. apply sub_mono_bunion. apply sub_mono_cprod...
Qed.

(* 基数乘法保持序关系 *)
Theorem cardMul_preserve_leq : ∀ 𝜅 𝜆 𝜇, 𝜅 ≤ 𝜆 → 𝜅 ⋅ 𝜇 ≤ 𝜆 ⋅ 𝜇.
Proof with auto.
  intros * Hleq.
  apply cardLeq_sub_exists in Hleq as [K [L [H1 [H2 H]]]].
  apply cardLeq_iff. eapply cardLeq_well_defined.
  apply cardMul_well_defined. symmetry. apply H1. reflexivity.
  apply cardMul_well_defined. symmetry. apply H2. reflexivity.
  apply dominate_sub. apply sub_mono_cprod...
Qed.

Lemma sub_mono_arrow : ∀ A B C, A ⊆ B → C ⟶ A ⊆ C ⟶ B.
Proof with auto.
  intros * Hsub f Hf.
  apply arrow_iff in Hf as [Hf [Hd Hr]].
  apply arrow_iff. split; [|split]...
  intros x Hx. apply Hsub. apply Hr...
Qed.

(* 基数乘方保持底数的序关系 *)
Theorem cardExp_preserve_base_leq : ∀ 𝜅 𝜆 𝜇, 𝜅 ≤ 𝜆 → 𝜅 ^ 𝜇 ≤ 𝜆 ^ 𝜇.
Proof with auto.
  intros * Hleq.
  apply cardLeq_sub_exists in Hleq as [K [L [H1 [H2 H]]]].
  apply cardLeq_iff. eapply cardLeq_well_defined.
  apply cardExp_well_defined. symmetry. apply H1. reflexivity.
  apply cardExp_well_defined. symmetry. apply H2. reflexivity.
  apply dominate_sub. apply sub_mono_arrow...
Qed.

(* 基数乘方保持指数的序关系 *)
Theorem cardExp_preserve_exponent_leq : ∀ 𝜅 𝜆 𝜇, (𝜅 ≠ ∅ ∨ 𝜇 ≠ ∅) →
  𝜅 ≤ 𝜆 → 𝜇 ^ 𝜅 ≤ 𝜇 ^ 𝜆.
Proof with neauto.
  intros * Hnq Hleq.
  destruct (classic (𝜇 = ∅)) as [|Hi]. destruct Hnq; [|exfalso]... {
    subst. rewrite cardExp_0_l... rewrite card_of_nat...
    apply cardLeq_sub. apply empty_sub_all.
  }
  apply EmptyNE in Hi as [m Hm].
  apply cardLeq_sub_exists in Hleq as [K [L [Hk [Hl Hsub]]]].
  apply cardLeq_iff. eapply cardLeq_well_defined.
  apply cardExp_well_defined. reflexivity. symmetry. apply Hk.
  apply cardExp_well_defined. reflexivity. symmetry. apply Hl.
  set (Func (K ⟶ 𝜇) (L ⟶ 𝜇) (λ f, f ∪ ((L - K) × ⎨m⎬))) as G.
  exists G. apply meta_injective.
  - intros f Hf.
    apply SepE in Hf as [Hf [Hff [Hdf Hrf]]].
    apply SepI. {
      apply PowerAx. intros x Hx. apply BUnionE in Hx as [].
      - apply PowerAx in Hf. apply Hf in H. eapply sub_mono_cprod...
      - apply cprod_iff in H as [a [Ha [b [Hb H]]]]. subst x.
        apply CProdI. apply SepE in Ha as []...
        apply SingE in Hb. subst b...
    }
    split; [|split].
    + apply bunion_func... {
        repeat split.
        - apply cprod_is_rel.
        - apply domE in H...
        - intros y1 y2 Hp1 Hp2.
          apply cprod_iff in Hp1 as [a [Ha [b [Hb H1]]]].
          apply cprod_iff in Hp2 as [c [Hc [d [Hd H2]]]].
          apply op_iff in H1 as []; subst x y1.
          apply op_iff in H2 as []; subst y2.
          apply SingE in Hb. apply SingE in Hd. congruence.
      }
      intros x Hx. exfalso.
      apply BInterE in Hx as [H1 H2].
      apply domE in H2 as [y H2].
      apply cprod_iff in H2 as [a [Ha [b [_ H2]]]].
      apply op_iff in H2 as [H _]; subst x.
      apply SepE in Ha as [_ H]. congruence.
    + apply ExtAx. split; intros Hx. {
        apply domE in Hx as [y Hp]. apply BUnionE in Hp as [].
        - apply Hsub. rewrite <- Hdf. eapply domI...
        - apply cprod_iff in H as [a [Ha [b [_ H]]]].
          apply op_iff in H as [H _]; subst x.
          apply SepE in Ha as []...
      } {
        destruct (classic (x ∈ K)).
        - rewrite <- Hdf in H. apply domE in H as [y Hp].
          eapply domI. apply BUnionI1...
        - eapply domI. apply BUnionI2...
          apply CProdI... apply SepI...
      }
    + intros y Hy. apply ranE in Hy as [x Hp].
      apply BUnionE in Hp as [].
      * apply ranI in H. apply Hrf...
      * apply CProdE1 in H as [_ Hy]. zfcrewrite.
        apply SingE in Hy. subst y...
  - intros f1 Hf1 f2 Hf2 Heq. eapply ex2_20'...
    apply ExtAx. split; intros Hx.
    + apply BInterE in Hx as [H1 H2].
      apply SepE in Hf1 as [Hf1 _]. apply PowerAx in Hf1.
      apply Hf1 in H1. apply cprod_iff in H1 as [a [Ha [b [Hb H1]]]].
      subst x. apply CProdE1 in H2 as [H _]. zfcrewrite.
      apply SepE in H as [_ H]. exfalso...
    + apply BInterE in Hx as [H1 H2].
      apply SepE in Hf2 as [Hf2 _]. apply PowerAx in Hf2.
      apply Hf2 in H1. apply cprod_iff in H1 as [a [Ha [b [Hb H1]]]].
      subst x. apply CProdE1 in H2 as [H _]. zfcrewrite.
      apply SepE in H as [_ H]. exfalso...
Qed.

(** 阿列夫零 **)
Notation "'ℵ₀'" := (|ω|).

Lemma aleph0_is_card : is_card ℵ₀.
Proof. exists ω. reflexivity. Qed.

Fact card_of_power_ω : |𝒫 ω| = 2 ^ ℵ₀.
Proof. apply card_of_power. Qed.

Fact aleph_0_neq_exp : ℵ₀ ≠ 2 ^ ℵ₀.
Proof. apply card_neq_exp. apply aleph0_is_card. Qed.

(* 有限基数不等于阿列夫零 *)
Lemma fin_card_neq_aleph0 : ∀n ∈ ω, |n| ≠ ℵ₀.
Proof with nauto.
  intros n Hn.
  set {n ∊ ω | λ n, |n| ≠ ℵ₀} as N.
  ω_induction N Hn; intros H.
  - apply CardAx1 in H. symmetry in H.
    apply eqnum_empty in H. rewrite H in Hn. exfalso0.
  - assert (Heqw: ω = (ω - ⎨∅⎬) ∪ ⎨∅⎬) by (apply split_one_element; nauto).
    apply CardAx1 in H. rewrite Heqw in H. symmetry in H.
    apply fin_set_remove_one_element in H...
    apply IH. apply CardAx1. rewrite <- H. symmetry.
    exists σ. apply σ_bijective.
Qed.

(* 有限基数小于阿列夫零 *)
Lemma cardLt_nat_aleph0 : ∀n ∈ ω, n <𝐜 ℵ₀.
Proof with eauto.
  intros n Hn. rewrite card_of_nat... apply cardLt_iff.
  split. apply ω_dominate... intros Hqn.
  apply CardAx1 in Hqn. eapply fin_card_neq_aleph0...
Qed.

Fact cardAdd_aleph0_aleph0 : ℵ₀ + ℵ₀ = ℵ₀.
Proof with neauto; try congruence.
  apply CardAx1. eapply eqnum_tran.
  apply cardAdd_well_defined.
  apply cardMul_well_defined. symmetry. apply CardAx0. reflexivity.
  apply cardMul_well_defined. symmetry. apply CardAx0. reflexivity.
  apply disjoint_cprod_0_1. apply disjoint_cprod_0_1.
  set (Func (ω × ⎨0⎬ ∪ ω × ⎨1⎬) ω (λ x,
    match (ixm (π2 x = 0)) with
    | inl _ => (2 ⋅ (π1 x))%n
    | inr _ => (2 ⋅ (π1 x) + 1)%n
  end)) as f.
  exists f. apply meta_bijective.
  - intros x Hx. apply BUnionE in Hx as [].
    + apply cprod_iff in H as [n [Hn [b [Hb H]]]].
      subst x. zfcrewrite. apply SingE in Hb.
      destruct (ixm (b = 0))... apply mul_ran...
    + apply cprod_iff in H as [n [Hn [b [Hb H]]]].
      subst x. zfcrewrite. apply SingE in Hb.
      destruct (ixm (b = 0)).
      * subst b. exfalso. eapply suc_neq_0...
      * apply add_ran... apply mul_ran...
  - intros x1 H1 x2 H2 Heq.
    assert (H20: Embed 2 ≠ Embed 0). { intros H. eapply suc_neq_0... }
    apply BUnionE in H1 as [H1|H1];
    apply BUnionE in H2 as [H2|H2];
    apply cprod_iff in H1 as [m [Hm [n [Hn H1]]]];
    apply cprod_iff in H2 as [p [Hp [q [Hq H2]]]];
    apply SingE in Hn; apply SingE in Hq;
    subst x1 x2 n q; zfcrewrite; apply op_iff.
    + destruct (ixm (Embed 0 = Embed 0))...
      split... apply mul_cancel' in Heq...
    + destruct (ixm (Embed 0 = Embed 0))...
      destruct (ixm (Embed 1 = Embed 0)).
      split... apply mul_cancel' in Heq...
      assert (H2m: (2 ⋅ m)%n ∈ ω) by (apply mul_ran; nauto).
      pose proof (ex4_14 (2 ⋅ m)%n H2m) as [_ H].
      exfalso. apply H. split. exists m. split...
      rewrite Heq. exists p. split...
    + destruct (ixm (Embed 0 = Embed 0))...
      destruct (ixm (Embed 1 = Embed 0)).
      split... apply mul_cancel' in Heq...
      assert (H2p: (2 ⋅ p)%n ∈ ω) by (apply mul_ran; nauto).
      pose proof (ex4_14 (2 ⋅ p)%n H2p) as [_ H].
      exfalso. apply H. split. exists p. split...
      rewrite <- Heq. exists m. split...
    + destruct (ixm (Embed 1 = Embed 0)).
      * exfalso. eapply suc_neq_0...
      * assert (H2m: (2 ⋅ m)%n ∈ ω) by (apply mul_ran; nauto).
        assert (H2p: (2 ⋅ p)%n ∈ ω) by (apply mul_ran; nauto).
        split... rewrite <- add_suc, <- add_suc in Heq...
        apply suc_injective in Heq... apply mul_cancel' in Heq...
  - intros y Hy. pose proof (ex4_14 y Hy) as [[] _].
    + destruct H as [n [Hn Heqy]].
      exists <n, 0>. split. apply BUnionI1. apply CProdI...
      zfcrewrite. destruct (ixm (Embed 0 = Embed 0))...
    + destruct H as [n [Hn Heqy]].
      exists <n, 1>. split. apply BUnionI2. apply CProdI...
      zfcrewrite. destruct (ixm (Embed 1 = Embed 0))...
      exfalso. eapply suc_neq_0...
Qed.

Fact cardMul_2aleph0_2aleph0 : 2 ^ ℵ₀ ⋅ 2 ^ ℵ₀ = 2 ^ ℵ₀.
Proof.
  rewrite <- cardExp_id_1, cardAdd_aleph0_aleph0. reflexivity.
Qed.

Fact cardMul_aleph0_2aleph0 : ℵ₀ ⋅ 2 ^ ℵ₀ = 2 ^ ℵ₀.
Proof with auto.
  eapply cardLeq_asym.
  - rewrite <- cardMul_2aleph0_2aleph0 at 2.
    apply cardMul_preserve_leq. rewrite <- card_of_power_ω.
    apply cardLeq_sub. apply trans_sub_power. apply ω_trans.
  - rewrite <- (cardMul_ident (2 ^ ℵ₀)) at 1...
    rewrite cardMul_comm. apply cardMul_preserve_leq.
    pose proof (cardLt_nat_aleph0 1) as []; nauto.
Qed.
