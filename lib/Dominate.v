(** Coq coding by choukh, Jan 2021 **)

Require Import ZFC.lib.NatIsomorphism.
Require Import ZFC.lib.algebra.Inj_2n3m.
Require Import ZFC.lib.IndexedFamilyUnion.
Require Export ZFC.EST6_1.

(* 集合的支配关系 *)
Definition Dominate : set → set → Prop := λ A B, ∃ f, f: A ⇔ B.
Notation "A ≼ B" := (Dominate A B) (at level 70).
Notation "A ≺ B" := (A ≼ B ∧ A ≉ B) (at level 70).

(* 空集被任意集合支配 *)
Lemma empty_dominated : ∀ A, ∅ ≼ A.
Proof. intros. exists ∅. apply empty_injection. Qed.

(* 等势的集合相互支配 *)
Lemma eqnum_dominate : ∀ A B, A ≈ B → A ≼ B.
Proof with auto.
  intros * [f Hf]. exists f. apply bijection_is_injection...
Qed.

(* 支配关系是自反的 *)
Lemma dominate_refl : ∀ A, A ≼ A.
Proof.
  intros. exists (Ident A).
  apply bijection_is_injection. apply ident_bijection.
Qed.
Global Hint Immediate dominate_refl : core.

(* 支配关系是传递的 *)
Lemma dominate_tran : ∀ A B C, A ≼ B → B ≼ C → A ≼ C.
Proof.
  intros * [f Hf] [g Hg].
  exists (g ∘ f). eapply compo_injection; eauto.
Qed.

Lemma dominate_rewrite_l : ∀ A B C, B ≈ A → B ≼ C → A ≼ C.
Proof.
  intros * Hqn Hdm. eapply dominate_tran.
  apply eqnum_dominate. symmetry. apply Hqn. apply Hdm.
Qed.

Lemma dominate_rewrite_r : ∀ A B C, C ≈ A → B ≼ C → B ≼ A.
Proof.
  intros * Hqn Hdm. eapply dominate_tran; revgoals.
  apply eqnum_dominate. apply Hqn. apply Hdm.
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
    intros x Hx. eapply nat_IFUnionI. rewrite HeqC0...
  }
  assert (HsubA: C ⊆ A). {
    intros x Hx. apply nat_IFUnionE in Hx as [m Hm].
    destruct m. rewrite HeqC0 in Hm. apply SepE1 in Hm...
    rewrite HeqCn in Hm. apply img_included in Hm. apply Hrg...
  }
  assert (Hxrg:∀x ∈ A, x ∉ C → x ∈ ran g). {
    intros x Hx H. destruct (classic (x ∈ ran g))...
    exfalso. apply H. apply HsubC. apply SepI...
  }
  assert (Hdc: ∀ n, ∀x ∈ ran g, (g⁻¹)[x] ∈ Dᵢ n → x ∈ C). {
    intros n x Hx H. eapply nat_IFUnionI. rewrite HeqCn.
    eapply imgI. apply H. rewrite inv_op. apply func_correct.
    apply inv_func_iff_sr... rewrite inv_dom...
  }
  exists h. apply meta_bijection.
  - intros x Hx. destruct (ixm (x ∈ C)).
    + eapply ap_ran. split... apply Hx.
    + rewrite <- Hdg, <- inv_ran. eapply ap_ran. split...
      apply inv_func_iff_sr... rewrite inv_dom. apply Hxrg...
  - intros x1 Hx1 x2 Hx2 Heq.
    destruct (ixm (x1 ∈ C)) as [H1|H1];
    destruct (ixm (x2 ∈ C)) as [H2|H2].
    + apply (injectiveE f)...
    + apply nat_IFUnionE in H1 as [m Hcm].
      exfalso. apply H2. eapply Hdc. apply Hxrg...
      rewrite <- Heq. eapply imgI. apply Hcm. apply func_correct...
    + apply nat_IFUnionE in H2 as [m Hcm].
      exfalso. apply H1. eapply Hdc. apply Hxrg...
      rewrite Heq. eapply imgI. apply Hcm. apply func_correct...
    + apply (injectiveE g⁻¹)... apply inv_injective...
      rewrite inv_dom. apply Hxrg...
      rewrite inv_dom. apply Hxrg...
  - intros y Hy. destruct (classic (y ∈ D)). {
      apply nat_IFUnionE in H as [m H].
      apply imgE in H as [x [Hx Hpf]].
      apply nat_IFUnionI in Hx. apply func_ap in Hpf...
      exists x. split. apply HsubA...
      destruct (ixm (x ∈ C))... exfalso... 
    }
    exists (g[y]). split. eapply ap_ran... split...
    destruct (ixm (g[y] ∈ C)) as [Hgy|Hgy];
      [exfalso|rewrite inv_dom_reduction]...
    apply nat_IFUnionE in Hgy as [m Hgy]. destruct m.
    + rewrite HeqC0 in Hgy. apply SepE in Hgy as [_ Hgy].
      apply Hgy. eapply ap_ran... split...
    + rewrite HeqCn in Hgy. apply imgE in Hgy as [x [Hx Hp]].
      apply domI in Hp as Hxdg. apply func_ap in Hp...
      apply injectiveE in Hp... subst x. apply H. eapply nat_IFUnionI...
Qed.

(* 子集被支配 *)
Lemma dominate_sub : ∀ A B, A ⊆ B → A ≼ B.
Proof with auto.
  intros. exists (Ident A).
  pose proof (ident_bijection A) as [Hi [Hd Hr]].
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
  apply eqnum_dominate in Hqn as H3. symmetry in Hqn.
  apply eqnum_dominate in Hqn as H4.
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
  - apply (subset_of_finite_is_finite _ B)...
    intros y Hy. rewrite inv_dom in Hy. apply Hr...
Qed.

Fact ω_eqnum_ω_cp_ω : ω ≈ ω × ω.
Proof with nauto.
  apply Schröeder_Bernstein.
  - set (Func ω (ω × ω) (λ n, <n, ∅>)) as f.
    exists f. apply meta_injection.
    + intros n Hn. apply CProdI...
    + intros x1 _ x2 _ Heq. apply op_iff in Heq as []...
  - set (Func (ω × ω) ω (λ p, (2 ^ π1 p ⋅ 3 ^ π2 p)%n)) as f.
    exists f. apply meta_injection.
    + intros p Hp.
      apply CProdE1 in Hp as [n [Hn [m [Hm Hp]]]].
      subst p. zfc_simple. apply mul_ran; apply exp_ran...
    + intros p1 H1 p2 H2 Heq.
      apply CProdE1 in H1 as [n [Hn [m [Hm H1]]]].
      apply CProdE1 in H2 as [p [Hp [q [Hq H2]]]].
      subst p1 p2. zfc_simple.
      do 4 rewrite pow_isomorphic_ω in Heq...
      do 2 rewrite mul_isomorphic_ω in Heq...
      repeat rewrite proj_embed_id in Heq.
      apply embed_injective in Heq.
      apply inj_2n3m in Heq as [H1 H2].
      apply proj_injective in H1...
      apply proj_injective in H2... apply op_iff...
Qed.
