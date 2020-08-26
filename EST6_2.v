(** Based on "Elements of Set Theory" Chapter 1 Part 2 **)
(** Coq coding by choukh, Aug 2020 **)

Require Export ZFC.EST6_1.

(*** EST第六章2：基数算术：加法，乘法，乘方 ***)

(* TODO: We will remove this primitive notion after Chapter 7 *)
Parameter card : set → set.
Notation "| A |" := (card A) (at level 40) : ZFC_scope.
Axiom CardAx0 : ∀ A, |A| ≈ A.
Axiom CardAx1 : ∀ A B, |A| = |B| ↔ A ≈ B.
Axiom CardAx2 : ∀ A, finite A → |A| = fin_card A.

Definition is_card : set → Prop := λ 𝜅, ∃ K, 𝜅 = |K|.

(* 有限基数的基数等于自身 *)
Lemma card_of_fin_card : ∀n ∈ ω, |n| = n.
Proof with auto.
  intros n Hn. rewrite CardAx2.
  apply fin_card_n... apply nat_finite...
Qed.

(* 基数的基数等于自身 *)
Lemma card_of_card : ∀ 𝜅, is_card 𝜅 → |𝜅| = 𝜅.
Proof.
  intros 𝜅 [K H𝜅]. rewrite H𝜅 at 2.
  apply CardAx1. rewrite H𝜅. apply CardAx0.
Qed.

(* 集合的基数为零当且仅当它是空集 *)
Lemma card_empty : ∀ A, |A| = ∅ ↔ A = ∅.
Proof with nauto.
  split; intros.
  - rewrite <- eqnum_empty, <- CardAx1,
      (CardAx2 ∅), (fin_card_n ∅)...
  - subst A. rewrite CardAx2, fin_card_n...
Qed.

(* 集合的基数不为零当且仅当集合非空 *)
Lemma set_nonzero_card_nonzero : ∀ A, ⦿ A ↔ ⦿ |A|.
Proof with nauto.
  split; intros [a Ha].
  - apply EmptyNE. intro.
    rewrite card_empty in H. subst. exfalso0.
  - apply EmptyNE. intro. subst A.
    rewrite CardAx2, fin_card_n in Ha... exfalso0.
Qed.

(* 任意集合都可以在任意非零基数的集合里 *)
Lemma any_set_in_set_with_any_nonzero_card : ∀ a 𝜅,
  is_card 𝜅 → ⦿ 𝜅 → ∃ A, |A| = 𝜅 ∧ a ∈ A.
Proof with auto; try congruence.
  intros * [K H𝜅] Hi. subst 𝜅.
  apply set_nonzero_card_nonzero in Hi as [k Hk].
  destruct (classic (a ∈ K)) as [|Ha]. exists K. split...
  pose proof (bijection_exists_between_set_and_element_replaced
    K k a Hk Ha) as [f Hf].
  exists {ReplaceElement k a | x ∊ K}. split.
  - apply CardAx1. apply eqnum_symm. exists f...
  - apply ReplAx. exists k. split...
    unfold ReplaceElement. destruct (ixm (k = k))...
Qed.

(* 集合与单集的笛卡尔积与原集合等势 *)
Lemma eqnum_cprod_single : ∀ A a, A ≈ A × ⎨a⎬.
Proof with auto.
  intros. set (Func A (A × ⎨ a ⎬) (λ x, <x, a>)) as F.
  exists F. apply meta_bijective.
  - intros x Hx. apply CProdI...
  - intros x1 Hx1 x2 Hx2 Heq.
    apply op_correct in Heq as []...
  - intros y Hy. apply CProd_correct in Hy as [b [Hb [c [Hc Heq]]]].
    apply SingE in Hc. subst. exists b. split...
Qed.

(* 给定任意两个集合，通过笛卡尔积可以构造出分别与原集合等势但不交的两个集合 *)
Lemma cprod_disjoint : ∀ A B, disjoint (A × ⎨0⎬) (B × ⎨1⎬).
Proof.
  intros. apply disjointI.
  intros [x [H1 H2]].
  apply CProd_correct in H1 as [a [Ha [b [Hb H1]]]].
  apply CProd_correct in H2 as [c [Hc [d [Hd H2]]]].
  apply SingE in Hb. apply SingE in Hd. subst.
  apply op_correct in H2 as [_ Contra]. eapply suc_neq_0. eauto.
Qed.

(* 集合1与单集的笛卡尔积 *)
Lemma one_cp_single : ∀ n, 1 × ⎨n⎬ = ⎨<0, n>⎬.
Proof.
  intros. rewrite one. apply ExtAx. split; intros Hx.
  - apply CProd_correct in Hx as [a [Ha [b [Hb H0]]]].
    apply SingE in Ha. apply SingE in Hb. subst. auto.
  - apply SingE in Hx. subst. apply CProdI; apply SingI.
Qed.

Declare Scope Card_scope.
Delimit Scope Card_scope with cd.
Open Scope Card_scope.

(* 基数算术：加法，乘法，乘方 *)
Definition CardAdd : set → set → set := λ 𝜅 𝜆, |𝜅 × ⎨0⎬ ∪ 𝜆 × ⎨1⎬|.
Definition CardMul : set → set → set := λ 𝜅 𝜆, |𝜅 × 𝜆|.
Definition CardExp : set → set → set := λ 𝜅 𝜆, |𝜆 ⟶ 𝜅|.

Notation "𝜅 + 𝜆" := (CardAdd 𝜅 𝜆) : Card_scope.
Notation "𝜅 ⋅ 𝜆" := (CardMul 𝜅 𝜆) : Card_scope.
Notation "𝜅 ^ 𝜆" := (CardExp 𝜅 𝜆) : Card_scope.

Theorem cardAdd_well_defined : ∀ K₁ K₂ L₁ L₂, K₁ ≈ K₂ → L₁ ≈ L₂ →
  disjoint K₁ L₁ → disjoint K₂ L₂ → K₁ ∪ L₁ ≈ K₂ ∪ L₂.
Proof with eauto; try congruence.
  intros * [f [Hif [Hdf Hrf]]] [g [Hig [Hdg Hrg]]] Hdj1 Hdj2.
  assert (Hif' := Hif). destruct Hif' as [Hf Hsf].
  assert (Hig' := Hig). destruct Hig' as [Hg Hsg].
  set (Func (K₁ ∪ L₁) (K₂ ∪ L₂) (λ x,
    match (ixm (x ∈ K₁)) with
    | inl _ => f[x]
    | inr _ => g[x]
    end
  )) as F.
  exists F. apply meta_bijective.
  - intros x Hx. destruct (ixm (x ∈ K₁)).
    + apply BUnionI1. rewrite <- Hrf.
      eapply ranI. apply func_correct...
    + apply BUnionE in Hx as []...
      apply BUnionI2. rewrite <- Hrg.
      eapply ranI. apply func_correct...
  - intros x1 Hx1 x2 Hx2 Heq.
    destruct (ixm (x1 ∈ K₁)) as [H1|H1'];
    destruct (ixm (x2 ∈ K₁)) as [H2|H2'].
    + eapply injectiveE; revgoals...
    + exfalso. apply BUnionE in Hx2 as [|H2]...
      rewrite <- Hdf in H1. rewrite <- Hdg in H2.
      apply func_correct in H1... apply ranI in H1.
      apply func_correct in H2... apply ranI in H2.
      rewrite Hrf in H1. rewrite Hrg in H2.
      eapply disjointE; [apply Hdj2|..]...
    + exfalso. apply BUnionE in Hx1 as [|H1]...
      rewrite <- Hdg in H1. rewrite <- Hdf in H2.
      apply func_correct in H1... apply ranI in H1.
      apply func_correct in H2... apply ranI in H2.
      rewrite Hrg in H1. rewrite Hrf in H2.
      eapply disjointE; [apply Hdj2|..]...
    + apply BUnionE in Hx1 as [|H1]...
      apply BUnionE in Hx2 as [|H2]...
      eapply injectiveE; revgoals...
  - intros y Hy. apply BUnionE in Hy as [Hy|Hy].
    + rewrite <- Hrf in Hy. apply ranE in Hy as [x Hp].
      apply domI in Hp as Hd. apply func_ap in Hp...
      exists x. split. apply BUnionI1...
      destruct (ixm (x ∈ K₁))...
    + rewrite <- Hrg in Hy. apply ranE in Hy as [x Hp].
      apply domI in Hp as Hd. apply func_ap in Hp...
      exists x. split. apply BUnionI2...
      destruct (ixm (x ∈ K₁))...
      exfalso. eapply disjointE; [apply Hdj1|..]...
Qed.

Theorem cardMul_well_defined : ∀ K₁ K₂ L₁ L₂,
  K₁ ≈ K₂ → L₁ ≈ L₂ → K₁ × L₁ ≈ K₂ × L₂.
Proof with eauto; try congruence.
  intros * [f [Hif [Hdf Hrf]]] [g [Hig [Hdg Hrg]]].
  assert (Hif' := Hif). destruct Hif' as [Hf Hsf].
  assert (Hig' := Hig). destruct Hig' as [Hg Hsg].
  set (Func (K₁ × L₁) (K₂ × L₂) (λ x,
    <f[π1 x], g[π2 x]>
  )) as F.
  exists F. apply meta_bijective.
  - intros x Hx.
    apply CProd_correct in Hx as [a [Ha [b [Hb Hx]]]].
    subst x. zfcrewrite. apply CProdI.
    rewrite <- Hrf. eapply ranI. apply func_correct...
    rewrite <- Hrg. eapply ranI. apply func_correct...
  - intros x1 Hx1 x2 Hx2 Heq.
    apply CProd_correct in Hx1 as [a [Ha [b [Hb Hx1]]]].
    apply CProd_correct in Hx2 as [c [Hc [d [Hd Hx2]]]].
    subst. zfcrewrite. apply op_correct in Heq as [].
    apply injectiveE in H... apply injectiveE in H0...
  - intros y Hy.
    apply CProd_correct in Hy as [a [Ha [b [Hb Hy]]]]. subst y.
    rewrite <- Hrf in Ha. apply ranE in Ha as [x1 H1].
    rewrite <- Hrg in Hb. apply ranE in Hb as [x2 H2].
    apply domI in H1 as Hd1. apply ranI in H1 as Hr1.
    apply domI in H2 as Hd2. apply ranI in H2 as Hr2.
    rewrite Hdf in Hd1. apply func_ap in H1...
    rewrite Hdg in Hd2. apply func_ap in H2...
    exists <x1, x2>. split. apply CProdI... zfcrewrite.
Qed.

Theorem cardExp_well_defined : ∀ K₁ K₂ L₁ L₂,
  K₁ ≈ K₂ → L₁ ≈ L₂ → (L₁ ⟶ K₁) ≈ (L₂ ⟶ K₂).
Proof with eauto; try congruence.
  intros * [f [Hif [Hdf Hrf]]] [g [Hig [Hdg Hrg]]].
  assert (Hif' := Hif). destruct Hif' as [Hf Hsf].
  assert (Hig' := Hig). destruct Hig' as [Hg Hsg].
  assert (Hf': is_function f⁻¹) by (apply inv_func_iff_sr; auto).
  assert (Hg': is_function g⁻¹) by (apply inv_func_iff_sr; auto).
  set (Func (L₁ ⟶ K₁) (L₂ ⟶ K₂) (λ x, f ∘ x ∘ g⁻¹ )) as F.
  exists F. apply meta_bijective.
  - intros j Hj. apply Arrow_correct in Hj as [Hfj [Hdj Hrj]].
    assert (Hffj: is_function (f ∘ j)) by (apply compo_func; auto).
    apply Arrow_correct. split; [|split].
    + apply compo_func...
    + apply ExtAx. intros x. split; intros Hx.
      * rewrite compo_dom in Hx... apply SepE in Hx as [Hx _].
        rewrite inv_dom in Hx...
      * rewrite compo_dom... apply SepI. rewrite inv_dom...
        rewrite compo_dom... apply SepI. {
          rewrite Hdj, <- Hdg, <- inv_ran.
          eapply ranI. apply func_correct... rewrite inv_dom...
        } {
          rewrite Hdf. apply Hrj. rewrite <- Hdg, <- inv_ran.
          eapply ranI. apply func_correct... rewrite inv_dom...
        }
    + intros y Hy.
      assert (H1: (g ⁻¹) [y] ∈ L₁). {
        rewrite <- Hdg, <- inv_ran. eapply ranI.
        apply func_correct... rewrite inv_dom, Hrg...
      }
      assert (H2: j [(g ⁻¹) [y]] ∈ dom f). {
        rewrite Hdf. apply Hrj...
      }
      assert (H3: (g ⁻¹) [y] ∈ dom (f ∘ j)). {
        rewrite compo_dom... apply SepI...
      }
      rewrite compo_correct, compo_correct...
      * rewrite <- Hrf. eapply ranI. apply func_correct...
      * rewrite compo_dom... apply SepI... rewrite inv_dom...
  - intros j1 Hj1 j2 Hj2 Heq.
    cut (∀h1 ∈ L₁ ⟶ K₁, ∀h2 ∈ L₁ ⟶ K₁,
      (f ∘ h1) ∘ g ⁻¹ = (f ∘ h2) ∘ g ⁻¹ → h1 ⊆ h2). {
      intros H. apply sub_asym; apply H...
    }
    clear Hj1 Hj2 Heq j1 j2.
    intros j1 Hj1 j2 Hj2 Heq p Hjp.
    apply Arrow_correct in Hj1 as [Hfj1 [Hdj1 Hrj1]].
    apply Arrow_correct in Hj2 as [Hfj2 [Hdj2 Hrj2]].
    assert (H1: is_function (f ∘ j1)) by (apply compo_func; auto).
    assert (H2: is_function (f ∘ j2)) by (apply compo_func; auto).
    apply func_pair in Hjp as Hpeq...
    remember (π1 p) as x. remember (π2 p) as y.
    subst p. clear Heqx Heqy.
    apply domI in Hjp as Hx.
    apply func_ap in Hjp... subst y.
    rewrite Hdj1 in Hx. apply Hrj1 in Hx as Hjx.
    rewrite <- Hdg, <- inv_ran in Hx.
    apply ranE in Hx as [w Hgp]. apply domI in Hgp as Hw.
    apply ranI in Hgp as Hx. rewrite inv_ran in Hx.
    apply func_ap in Hgp... subst x.
    assert (H3: j2 [(g⁻¹)[w]] ∈ dom f). { rewrite Hdf. apply Hrj2... }
    assert (H4: (g⁻¹)[w] ∈ dom (f ∘ j1)). { rewrite compo_dom... apply SepI... }
    assert (H5: (g⁻¹)[w] ∈ dom (f ∘ j2)). { rewrite compo_dom... apply SepI... }
    assert (H6: w ∈ dom ((f ∘ j1) ∘ g⁻¹)). { rewrite compo_dom... apply SepI... }
    assert (H7: w ∈ dom ((f ∘ j2) ∘ g⁻¹)). { rewrite compo_dom... apply SepI... }
    rewrite <- Hdf in Hjx. apply func_correct in Hjx as Hfp...
    apply func_ap in Hfp...
    rewrite <- compo_correct, <- compo_correct in Hfp at 1...
    rewrite Heq, compo_correct, compo_correct in Hfp...
    apply injectiveE in Hfp... rewrite <- Hfp. apply func_correct...
  - intros y Hy.
    apply Arrow_correct in Hy as [Hfy [Hdy Hry]].
    exists ((f⁻¹ ∘ y) ∘ g). split. apply Arrow_correct.
    + assert (Hffy: is_function (f⁻¹ ∘ y)) by (apply compo_func; auto).
      assert (H1: ∀x ∈ L₁, g[x] ∈ dom y). {
        intros x Hx. rewrite Hdy, <- Hrg.
        eapply ranI. apply func_correct...
      }
      assert (H2: ∀x ∈ L₁, y[g[x]] ∈ dom f⁻¹). {
        intros x Hx. rewrite inv_dom, Hrf.
        apply Hry. rewrite <- Hdy. apply H1...
      }
      assert (H3: ∀x ∈ L₁, x ∈ dom ((f⁻¹ ∘ y) ∘ g)). {
        intros x Hx. rewrite compo_dom... apply SepI...
        rewrite compo_dom... apply SepI. apply H1... apply H2...
      }
      assert (H4: ∀x ∈ L₁, g[x] ∈ dom (f⁻¹ ∘ y)). {
        intros x Hx. rewrite compo_dom...
        apply SepI. apply H1... apply H2...
      }
      split; [|split].
      * apply compo_func...
      * apply ExtAx. intros w. split; intros Hw.
        rewrite compo_dom in Hw... apply SepE in Hw as []... apply H3...
      * intros x Hx. rewrite compo_correct, compo_correct...
        rewrite <- Hdf, <- inv_ran. eapply ranI. apply func_correct...
        apply H2... apply H4... apply H3...
    + assert (Hfy' := Hfy). destruct Hfy' as [Hrel _].
      rewrite compo_assoc, compo_assoc, compo_inv_ran_ident...
      rewrite compo_assoc, right_compo_ident.
      rewrite Hrg, <- Hdy, restr_to_dom...
      rewrite <- compo_assoc, compo_inv_ran_ident...
      rewrite left_compo_ident', Hrf...
      rewrite <- (inv_inv y) at 2...
      cut (y ⁻¹ ↾ K₂ = y⁻¹). congruence.
      apply ExtAx. intros x. split; intros Hx.
      * apply restrE1 in Hx as [a [b [Ha []]]]...
      * apply SepI... apply SepE in Hx as [Hcp [Hp _]].
        apply CProdE1 in Hcp as [H _]. apply ranE in H as [w H].
        apply domI in H as Hw. apply func_ap in H...
        split... rewrite <- H. apply Hry...
Qed.

Example cardAdd_1_1_2 : 1 + 1 = 2.
Proof with neauto; try congruence.
  rewrite <- (card_of_fin_card 2)...
  unfold CardAdd. apply CardAx1.
  set (Func (1×⎨0⎬ ∪ 1×⎨1⎬) 2 (λ x,
    match (ixm (x = <0, 0>)) with
    | inl _ => 0
    | inr _ => 1
    end
  )) as F.
  exists F. apply meta_bijective.
  - intros x Hx. destruct (ixm (x = <0, 0>))...
    apply BUnionI1. apply BUnionI2... apply BUnionI2...
  - intros x1 Hx1 x2 Hx2 Heq.
    destruct (ixm (x1 = <0, 0>)) as [H1|H1'];
    destruct (ixm (x2 = <0, 0>)) as [H2|H2']...
    + exfalso. eapply suc_neq_0...
    + exfalso. eapply suc_neq_0...
    + apply BUnionE in Hx1 as []; apply BUnionE in Hx2 as [].
      * rewrite one_cp_single in H. apply SingE in H. exfalso...
      * rewrite one_cp_single in H. apply SingE in H. exfalso...
      * rewrite one_cp_single in H0. apply SingE in H0. exfalso...
      * rewrite one_cp_single in H. apply SingE in H.
        rewrite one_cp_single in H0. apply SingE in H0...
  - intros y Hy. apply BUnionE in Hy as [Hy|Hy].
    + apply BUnionE in Hy as []. exfalso0.
      apply SingE in H. subst y. exists <0, 0>. split.
      apply BUnionI1. rewrite one_cp_single...
      destruct (ixm (<0, 0> = <0, 0>))...
    + apply SingE in Hy. subst y. exists <0, 1>. split.
      apply BUnionI2. rewrite one_cp_single...
      destruct (ixm (<0, 1> = <0, 0>)). {
        apply op_correct in e as [_ Contra].
        exfalso. eapply suc_neq_0...
      } reflexivity.
Qed.



