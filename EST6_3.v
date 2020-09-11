(** Based on "Elements of Set Theory" Chapter 1 Part 3 **)
(** Coq coding by choukh, Aug 2020 **)

Require Export ZFC.CH6_1.
Require Import ZFC.lib.IndexedFamilyUnion.

(*** EST第六章3：支配关系，施罗德-伯恩斯坦定理，基数的序 ***)

(* 集合的支配关系 *)
Definition dominate : set → set → Prop := λ A B, ∃ f, f: A ⇔ B.
Notation "A ≼ B" := (dominate A B) (at level 70).
Notation "A ≺ B" := (A ≼ B ∧ A ≉ B) (at level 70).

(* 支配关系是自反的 *)
Lemma dominate_refl : ∀ A, A ≼ A.
Proof.
  intros. exists (Ident A).
  apply bijection_is_injection. apply ident_bijective.
Qed.
Hint Immediate dominate_refl : core.

(* 支配关系是传递的 *)
Lemma dominate_tran : ∀ A B C, A ≼ B → B ≼ C → A ≼ C.
Proof.
  intros * [f Hf] [g Hg].
  exists (g ∘ f). eapply compo_injection; eauto.
Qed.

(* 可以证明支配关系也是反对称*)

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
    + apply Hrf. eapply ranI. apply func_correct...
    + rewrite <- Hdg, <- inv_ran. eapply ranI. apply func_correct...
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
    exists (g[y]). split. apply Hrg.
    eapply ranI. apply func_correct...
    destruct (ixm (g[y] ∈ C)) as [Hgy|Hgy];
      [exfalso|rewrite inv_dom_reduction]...
    apply IFUnionE in Hgy as [m Hgy]. destruct m.
    + rewrite HeqC0 in Hgy. apply SepE in Hgy as [_ Hgy].
      apply Hgy. eapply ranI. apply func_correct...
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

(* 自然数被ω支配 *)
Lemma dominate_nat_ω : ∀n ∈ ω, n ≼ ω.
Proof with auto.
  intros n Hn. apply dominate_sub.
  apply trans_sub... apply ω_trans.
Qed.

(* 基数的序关系 *)
Definition CardLeq : set → set → Prop := λ 𝜅 𝜆,
  is_card 𝜅 ∧ is_card 𝜆 ∧ 𝜅 ≼ 𝜆.
Notation "𝜅 ≤ 𝜆" := (CardLeq 𝜅 𝜆) : Card_scope.

(* 两个集合的基数有序关系当且仅当这两个集合有支配关系 *)
Lemma cardLeq_iff : ∀ A B, |A| ≤ |B| ↔ A ≼ B.
Proof with auto; try congruence.
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
        rewrite <- Hrf. eapply ranI. apply func_correct...
    + destruct Hif as [Hff _]. rewrite compo_ran...
      intros x Hx. apply SepE in Hx as []...
  - intros [f Hf]. split; [|split]...
    pose proof (CardAx0 A) as Hg.
    symmetry in Hg. destruct Hg as [g Hg].
    pose proof (CardAx0 B) as [h Hh].
    exists (h ∘ f ∘ g). eapply compo_injection.
    apply bijection_is_injection. apply Hg.
    eapply compo_injection. apply Hf.
    apply bijection_is_injection. apply Hh.
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
  apply bijection_is_injection. apply Hf.
  eapply compo_injection. apply Hh.
  apply bijection_is_injection. apply Hg.
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

(* 如果两个基数有序关系，那么存在有子集关系的集合，它们的基数就是这两个基数 *)
Lemma cardLeq_sub_exists : ∀ 𝜅 𝜆, 𝜅 ≤ 𝜆 →
  ∃ K L, |K| = 𝜅 ∧ |L| = 𝜆 ∧ K ⊆ L.
Proof with auto.
  intros * [Hk [Hl [f [Hf [Hd Hr]]]]].
  exists (ran f), 𝜆. split; [|split].
  - rewrite card_of_card... apply CardAx1. symmetry.
    exists f. split; [|split]...
  - symmetry. apply card_of_card...
  - intros y Hy. apply Hr...
Qed.

(* 任意基数大于等于零 *)
Fact cardLeq_0_k : ∀ 𝜅, is_card 𝜅 → 0 ≤ 𝜅.
Proof with nauto.
  intros 𝜅 Hcd. split; [|split]... apply nat_is_card...
  exists ∅. apply empty_injective.
Qed.

(* 有限基数不等于阿列夫零 *)
Fact fin_card_neq_aleph0 : ∀n ∈ ω, |n| ≠ ℵ₀.
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
Fact cardLt_nat_aleph0 : ∀n ∈ ω, n <𝐜 ℵ₀.
Proof with eauto.
  intros n Hn. rewrite card_of_nat... apply cardLt_iff.
  split. apply dominate_nat_ω... intros Hqn.
  apply CardAx1 in Hqn. eapply fin_card_neq_aleph0...
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

(* 任意基数都小于自身的幂集的基数 *)
Fact cardLt_power : ∀ 𝜅, is_card 𝜅 → 𝜅 <𝐜 2 ^ 𝜅.
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
Lemma cardLeq_tran : ∀ 𝜅 𝜆 𝜇, is_card 𝜅 → is_card 𝜆 → is_card 𝜇 →
  𝜅 ≤ 𝜆 → 𝜆 ≤ 𝜇 → 𝜅 ≤ 𝜇.
Proof with eauto.
  intros * Hk Hl Hm H1 H2.
  rewrite (card_of_card 𝜅) in *...
  rewrite (card_of_card 𝜆) in *...
  rewrite (card_of_card 𝜇) in *...
  apply cardLeq_iff in H1.
  apply cardLeq_iff in H2.
  apply cardLeq_iff. eapply dominate_tran...
Qed.

(* 基数的序关系是反对称的 *)
Lemma cardLeq_asym : ∀ 𝜅 𝜆, is_card 𝜅 → is_card 𝜆 →
  𝜅 ≤ 𝜆 → 𝜆 ≤ 𝜅 → 𝜅 = 𝜆.
Proof with auto.
  intros * Hk Hl H1 H2.
  rewrite (card_of_card 𝜅) in *...
  rewrite (card_of_card 𝜆) in *...
  apply cardLeq_iff in H1.
  apply cardLeq_iff in H2.
  apply CardAx1. apply Schröeder_Bernstein...
Qed.
