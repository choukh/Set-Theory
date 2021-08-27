(** Adapted from "Elements of Set Theory" Chapter 6 **)
(** Coq coding by choukh, Aug 2020 **)

Require Export ZFC.Theory.EST6_1.
Require Export ZFC.Theory.EST7_5.

(*** EST第六章2：无限基数，基数算术：加法，乘法，乘方 ***)

Check EST7_5.CardAx0.
(* Theorem CardAx0 : ∀ A, A ≈ |A|. *)
Check EST7_5.CardAx1.
(* Theorem CardAx1 : ∀ A B, |A| = |B| ↔ A ≈ B. *)
Check EST7_5.CardAx2.
(* Theorem CardAx2 : ∀ A, finite A → |A| = FinCard A. *)

Definition is_card := λ 𝜅, ∃ K, 𝜅 = |K|.
Notation 𝐂𝐃 := is_card.

Lemma card_is_card : ∀ A, |A| ⋵ 𝐂𝐃.
Proof. intros. exists A. reflexivity. Qed.
Global Hint Immediate card_is_card : core.

(* 基数的基数等于自身 *)
Lemma card_of_card : ∀𝜅 ⋵ 𝐂𝐃, 𝜅 = |𝜅|.
Proof.
  intros 𝜅 [K H𝜅]. rewrite H𝜅 at 1.
  apply CardAx1. rewrite H𝜅. apply CardAx0.
Qed.

(* 自然数的基数等于自身 *)
Lemma card_of_nat : ∀n ∈ ω, n = |n|.
Proof with auto.
  intros n Hn. rewrite CardAx2.
  rewrite fin_card_n... apply nat_finite...
Qed.

(* 自然数是基数 *)
Lemma nat_is_card : ω ⪽ 𝐂𝐃.
Proof. intros n Hn. exists n. apply (card_of_nat _ Hn). Qed.

Lemma embed_is_card : ∀ n : nat, n ⋵ 𝐂𝐃.
Proof. intros. apply nat_is_card. apply embed_ran. Qed.
Global Hint Immediate embed_is_card : number_hint.

(* 有限基数 *)
Definition fincard := λ n, n ⋵ 𝐂𝐃 ∧ finite n.
Notation 𝐂𝐃ᶠⁱⁿ := fincard.
(* 无限基数 *)
Definition infcard := λ 𝜅, 𝜅 ⋵ 𝐂𝐃 ∧ infinite 𝜅.
Notation 𝐂𝐃ⁱⁿᶠ := infcard.

(* 自然数等价于有限基数 *)
Lemma nat_iff_fincard : ∀ n, n ∈ ω ↔ n ⋵ 𝐂𝐃ᶠⁱⁿ.
Proof with auto; try congruence.
  split.
  - intros Hn. split. apply nat_is_card... apply nat_finite...
  - intros [Hcd Hfin]. apply CardAx2 in Hfin as Heqn.
    rewrite <- card_of_card in Heqn...
    apply fin_card_correct in Hfin as [m [Hm [Heqm _]]]...
Qed.

(* 空集的基数为零 *)
Lemma card_of_empty : |∅| = 0.
Proof. rewrite CardAx2, fin_card_n; nauto. Qed.

(* 集合的基数为零当且仅当它是空集 *)
Lemma card_eq_0 : ∀ A, |A| = 0 ↔ A = ∅.
Proof with nauto.
  split; intros.
  - rewrite <- eqnum_empty, <- CardAx1, (CardAx2 ∅), (fin_card_n ∅)...
  - subst A. apply card_of_empty.
Qed.

(* 集合的基数不为零当且仅当它非空 *)
Lemma card_neq_0 : ∀ A, |A| ≠ 0 ↔ ⦿ A.
Proof with auto.
  split; intros.
  - apply EmptyNE. intros Heq.
    apply H. apply card_eq_0...
  - intros Heq. rewrite card_eq_0 in Heq.
    apply EmptyNI in H...
Qed.

(* 单集的基数为1 *)
Lemma card_of_single : ∀ a, |⎨a⎬| = 1.
Proof with nauto.
  intros. rewrite (card_of_nat 1)...
  apply CardAx1. apply eqnum_single.
Qed.

(* 基数为1的集合是单集 *)
Lemma card_eq_1 : ∀ A, |A| = 1 → ∃ a, A = ⎨a⎬.
Proof with nauto.
  intros A H1. rewrite (card_of_nat 1), one in H1...
  symmetry in H1. apply CardAx1 in H1 as [f [[Hf _] [Hd Hr]]].
  exists (f[0]). ext y Hy.
  - rewrite <- Hr in Hy. apply ranE in Hy as [x Hp].
    apply domI in Hp as Hx. rewrite Hd in Hx.
    apply SingE in Hx. subst x.
    apply func_ap in Hp... subst y...
  - apply SingE in Hy. subst y. rewrite <- Hr. eapply ranI.
    apply func_correct... rewrite Hd. apply SingI.
Qed.

(* 集合有限当且仅当其基数有限 *)
Lemma set_finite_iff_card_finite : ∀ A, finite A ↔ finite (|A|).
Proof.
  now split; intros Hfin; apply set_finite_iff_eqnum_finite_set;
  [exists A|exists (|A|)]; split; auto; rewrite <- CardAx0.
Qed.

(* 集合无限当且仅当其基数无限 *)
Lemma set_infinite_iff_card_infinite : ∀ A, infinite A ↔ infinite (|A|).
Proof.
  split; intros Hinf Hfin; apply Hinf.
  rewrite set_finite_iff_card_finite; auto.
  rewrite <- set_finite_iff_card_finite; auto.
Qed.

(* 集合的基数不为零当且仅当集合非空 *)
Lemma set_nonzero_card_nonzero : ∀ A, ⦿ A ↔ ⦿ |A|.
Proof with nauto.
  split; intros [a Ha].
  - apply EmptyNE. intro.
    rewrite card_eq_0 in H. subst. exfalso0.
  - apply EmptyNE. intro. subst A.
    rewrite CardAx2, fin_card_n in Ha... exfalso0.
Qed.

(* 任意集合都可以在任意非零基数的集合里 *)
Lemma any_set_in_set_with_any_nonzero_card :
  ∀ a, ∀𝜅 ⋵ 𝐂𝐃, ⦿ 𝜅 → ∃ A, |A| = 𝜅 ∧ a ∈ A.
Proof with auto; try congruence.
  intros a 𝜅 [K H𝜅] Hi. subst 𝜅.
  apply set_nonzero_card_nonzero in Hi as [k Hk].
  destruct (classic (a ∈ K)) as [|Ha]. exists K. split...
  pose proof (bijection_exists_between_set_and_element_replaced
    K k a Hk Ha) as [f Hf].
  exists {ReplaceElement k a x | x ∊ K}. split.
  - apply CardAx1. symmetry. exists f...
  - apply ReplAx. exists k. split...
    unfold ReplaceElement. destruct (ixm (k = k))...
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

(* 基数加法的和是基数 *)
Lemma cardAdd_is_card : ∀ 𝜅 𝜆, 𝜅 + 𝜆 ⋵ 𝐂𝐃.
Proof. intros. apply card_is_card. Qed.
Global Hint Immediate cardAdd_is_card : core.

(* 基数乘法的积是基数 *)
Lemma cardMul_is_card : ∀ 𝜅 𝜆, 𝜅 ⋅ 𝜆 ⋵ 𝐂𝐃.
Proof. intros. apply card_is_card. Qed.
Global Hint Immediate cardMul_is_card : core.

(* 基数乘方的幂是基数 *)
Lemma cardExp_is_card : ∀ 𝜅 𝜆, 𝜅 ^ 𝜆 ⋵ 𝐂𝐃.
Proof. intros. apply card_is_card. Qed.
Global Hint Immediate cardExp_is_card : core.

(* 壹与单集的笛卡尔积 *)
Lemma one_cp_single : ∀ n, 1 × ⎨n⎬ = ⎨<0, n>⎬.
Proof.
  intros. rewrite one. ext Hx.
  - apply CPrdE1 in Hx as [a [Ha [b [Hb H0]]]].
    apply SingE in Ha. apply SingE in Hb. subst. auto.
  - apply SingE in Hx. subst. apply CPrdI; apply SingI.
Qed.

(* 基数算术的一加一等于二 *)
Example cardAdd_1_1_2 : 1 + 1 = 2.
Proof with neauto; try congruence.
  rewrite (card_of_nat 2)...
  unfold CardAdd. apply CardAx1.
  set (Func (1×⎨0⎬ ∪ 1×⎨1⎬) 2 (λ x,
    match (ixm (x = <0, 0>)) with
    | inl _ => 0
    | inr _ => 1
    end
  )) as F.
  exists F. apply meta_bijection.
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
        apply op_iff in e as [_ Contra].
        exfalso. eapply suc_neq_0...
      } reflexivity.
Qed.

(* 基数加法良定义 *)
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
  exists F. apply meta_bijection.
  - intros x Hx. destruct (ixm (x ∈ K₁)).
    + apply BUnionI1. eapply ap_ran... split... split...
    + apply BUnionE in Hx as []... apply BUnionI2.
      eapply ap_ran... split... split...
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

(* 基数乘法良定义 *)
Theorem cardMul_well_defined : ∀ K₁ K₂ L₁ L₂,
  K₁ ≈ K₂ → L₁ ≈ L₂ → K₁ × L₁ ≈ K₂ × L₂.
Proof with eauto; try congruence.
  intros * [f [Hif [Hdf Hrf]]] [g [Hig [Hdg Hrg]]].
  assert (Hif' := Hif). destruct Hif' as [Hf Hsf].
  assert (Hig' := Hig). destruct Hig' as [Hg Hsg].
  set (Func (K₁ × L₁) (K₂ × L₂) (λ x,
    <f[π1 x], g[π2 x]>
  )) as F.
  exists F. apply meta_bijection.
  - intros x Hx.
    apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]].
    subst x. zfc_simple. apply CPrdI.
    eapply ap_ran... split... split...
    eapply ap_ran... split... split...
  - intros x1 Hx1 x2 Hx2 Heq.
    apply CPrdE1 in Hx1 as [a [Ha [b [Hb Hx1]]]].
    apply CPrdE1 in Hx2 as [c [Hc [d [Hd Hx2]]]].
    subst. zfc_simple. apply op_iff in Heq as [].
    apply injectiveE in H... apply injectiveE in H0...
  - intros y Hy.
    apply CPrdE1 in Hy as [a [Ha [b [Hb Hy]]]]. subst y.
    rewrite <- Hrf in Ha. apply ranE in Ha as [x1 H1].
    rewrite <- Hrg in Hb. apply ranE in Hb as [x2 H2].
    apply domI in H1 as Hd1. apply ranI in H1 as Hr1.
    apply domI in H2 as Hd2. apply ranI in H2 as Hr2.
    rewrite Hdf in Hd1. apply func_ap in H1...
    rewrite Hdg in Hd2. apply func_ap in H2...
    exists <x1, x2>. split. apply CPrdI... zfc_simple.
Qed.

(* 基数乘方良定义 *)
Theorem cardExp_well_defined : ∀ K₁ K₂ L₁ L₂,
  K₁ ≈ K₂ → L₁ ≈ L₂ → (L₁ ⟶ K₁) ≈ (L₂ ⟶ K₂).
Proof with eauto; try congruence.
  intros * [f [Hif [Hdf Hrf]]] [g [Hig [Hdg Hrg]]].
  assert (Hif' := Hif). destruct Hif' as [Hf Hsf].
  assert (Hig' := Hig). destruct Hig' as [Hg Hsg].
  assert (Hf': is_function f⁻¹) by (apply inv_func_iff_sr; auto).
  assert (Hg': is_function g⁻¹) by (apply inv_func_iff_sr; auto).
  set (Func (L₁ ⟶ K₁) (L₂ ⟶ K₂) (λ x, f ∘ x ∘ g⁻¹ )) as F.
  exists F. apply meta_bijection.
  - intros j Hj. apply arrow_iff in Hj as [Hfj [Hdj Hrj]].
    assert (Hffj: is_function (f ∘ j)) by (apply compo_func; auto).
    apply arrow_iff. split; [|split].
    + apply compo_func...
    + ext Hx.
      * rewrite compo_dom in Hx... apply SepE in Hx as [Hx _].
        rewrite inv_dom in Hx...
      * rewrite compo_dom... apply SepI. rewrite inv_dom...
        rewrite compo_dom... apply SepI. {
          rewrite Hdj, <- Hdg, <- inv_ran.
          eapply ap_ran... split... split... rewrite inv_dom...
        } {
          rewrite Hdf. apply Hrj. rewrite <- Hdg, <- inv_ran.
          eapply ap_ran... split... split... rewrite inv_dom...
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
      * eapply ap_ran... split... split...
      * rewrite compo_dom... apply SepI... rewrite inv_dom...
  - intros j1 Hj1 j2 Hj2 Heq.
    cut (∀h1 ∈ L₁ ⟶ K₁, ∀h2 ∈ L₁ ⟶ K₁,
      (f ∘ h1) ∘ g ⁻¹ = (f ∘ h2) ∘ g ⁻¹ → h1 ⊆ h2). {
      intros H. apply sub_antisym; apply H...
    }
    clear Hj1 Hj2 Heq j1 j2.
    intros j1 Hj1 j2 Hj2 Heq p Hjp.
    apply arrow_iff in Hj1 as [Hfj1 [Hdj1 Hrj1]].
    apply arrow_iff in Hj2 as [Hfj2 [Hdj2 Hrj2]].
    assert (H1: is_function (f ∘ j1)) by (apply compo_func; auto).
    assert (H2: is_function (f ∘ j2)) by (apply compo_func; auto).
    apply func_pair' in Hjp as [x [y [Hjp Heqp]]]... subst p.
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
    apply arrow_iff in Hy as [Hfy [Hdy Hry]].
    exists ((f⁻¹ ∘ y) ∘ g). split. apply arrow_iff.
    + assert (Hffy: is_function (f⁻¹ ∘ y)) by (apply compo_func; auto).
      assert (H1: ∀x ∈ L₁, g[x] ∈ dom y). {
        intros x Hx. rewrite Hdy. eapply ap_ran... split... split...
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
      * ext w Hw.
        rewrite compo_dom in Hw... apply SepE1 in Hw... apply H3...
      * intros x Hx. rewrite compo_correct, compo_correct...
        rewrite <- Hdf, <- inv_ran. eapply ranI. apply func_correct...
    + assert (Hfy' := Hfy). destruct Hfy' as [Hrel _].
      rewrite compo_assoc, compo_assoc, compo_inv_ran_ident...
      rewrite compo_assoc, right_compo_ident.
      rewrite Hrg, <- Hdy, restr_to_dom...
      rewrite <- compo_assoc, compo_inv_ran_ident...
      rewrite left_compo_ident', Hrf...
      rewrite <- (inv_inv y) at 2...
      cut (y ⁻¹ ↾ K₂ = y⁻¹). congruence.
      ext Hx.
      * apply restrE1 in Hx as [a [b [Ha []]]]...
      * apply SepI... apply SepE in Hx as [Hcp [Hp _]].
        apply CPrdE0 in Hcp as [H _]. apply ranE in H as [w H].
        apply domI in H as Hw. apply func_ap in H...
        split... rewrite <- H. apply Hry...
Qed.

(* 不交集的二元并与基数加法的相互转化 *)
Lemma cardAdd_disjoint_iff : ∀ A B C, disjoint A B →
  A ∪ B ≈ C ↔ |A| + |B| = |C|.
Proof with auto.
  intros * Hdj. split; intros H.
  - apply CardAx1.
    eapply Equivalence_Transitive. {
      apply cardAdd_well_defined.
      - apply cardMul_well_defined.
        symmetry. apply CardAx0. reflexivity.
      - apply cardMul_well_defined.
        symmetry. apply CardAx0. reflexivity.
      - apply disjointify_0_1.
      - apply disjointify_0_1.
    }
    eapply Equivalence_Transitive. {
      apply cardAdd_well_defined.
      - symmetry. apply eqnum_cprd_single.
      - symmetry. apply eqnum_cprd_single.
      - apply disjointify_0_1.
      - apply Hdj.
    }
    apply H.
  - eapply Equivalence_Transitive. {
      apply cardAdd_well_defined.
      + apply (eqnum_cprd_single _ 0).
      + apply (eqnum_cprd_single _ 1).
      + apply Hdj.
      + apply disjointify_0_1.
    }
    eapply Equivalence_Transitive. {
      apply cardAdd_well_defined.
      - apply cardMul_well_defined. apply CardAx0. reflexivity.
      - apply cardMul_well_defined. apply CardAx0. reflexivity.
      - apply disjointify_0_1.
      - apply disjointify_0_1.
    }
    apply CardAx1. apply H.
Qed.

(* 二元并与基数加法的相互转化 *)
Lemma cardAdd_iff : ∀ A B C,
  A × ⎨0⎬ ∪ B × ⎨1⎬ ≈ C ↔ |A| + |B| = |C|.
Proof with auto.
  intros. split; intros H.
  - apply CardAx1.
    eapply Equivalence_Transitive. {
      apply cardAdd_well_defined.
      - apply cardMul_well_defined.
        symmetry. apply CardAx0. reflexivity.
      - apply cardMul_well_defined.
        symmetry. apply CardAx0. reflexivity.
      - apply disjointify_0_1.
      - apply disjointify_0_1.
    }
    apply H.
  - eapply Equivalence_Transitive. {
      apply cardAdd_well_defined.
      - apply cardMul_well_defined. apply CardAx0. reflexivity.
      - apply cardMul_well_defined. apply CardAx0. reflexivity.
      - apply disjointify_0_1.
      - apply disjointify_0_1.
    }
    apply CardAx1. apply H.
Qed.

(* 笛卡尔积与基数乘法的相互转化 *)
Lemma cardMul_iff : ∀ A B C, A × B ≈ C ↔ (|A| ⋅ |B|) = |C|.
Proof with auto.
  split; intros.
  - apply CardAx1. eapply Equivalence_Transitive.
    + apply cardMul_well_defined; symmetry; apply CardAx0.
    + apply H.
  - eapply Equivalence_Transitive.
    + apply cardMul_well_defined; apply CardAx0.
    + apply CardAx1. apply H.
Qed.

(* 函数空间与基数乘方的相互转化 *)
Lemma cardExp_iff : ∀ A B C, B ⟶ A ≈ C ↔ (|A| ^ |B|) = |C|.
Proof with auto.
  split; intros.
  - apply CardAx1. eapply Equivalence_Transitive.
    + apply cardExp_well_defined; symmetry; apply CardAx0.
    + apply H.
  - eapply Equivalence_Transitive.
    + apply cardExp_well_defined; apply CardAx0.
    + apply CardAx1. apply H.
Qed.

(* 不交集的基数的和等于它们的二元并的基数 *)
Lemma cardAdd_disjoint : ∀ A B, disjoint A B → |A| + |B| = |A ∪ B|.
Proof. intros. now apply cardAdd_disjoint_iff. Qed.

(* 基数的和等于它们的不交化二元并的基数 *)
Lemma cardAdd : ∀ A B, |A| + |B| = |A × ⎨0⎬ ∪ B × ⎨1⎬|.
Proof. intros. now apply cardAdd_iff. Qed.

(* 集合的基数的积等于它们的笛卡尔积的基数*)
Lemma cardMul : ∀ A B, (|A| ⋅ |B|) = |A × B|.
Proof. intros. now apply cardMul_iff. Qed.

(* 集合的基数的幂等于它们张起的函数空间的基数*)
Lemma cardExp : ∀ A B, (|A| ^ |B|) = |B ⟶ A|.
Proof. intros. now apply cardExp_iff. Qed.

(* 零是基数加法单位元 *)
Lemma cardAdd_0_r : ∀𝜅 ⋵ 𝐂𝐃, 𝜅 + 0 = 𝜅.
Proof with auto.
  intros 𝜅 Hcd. apply card_of_card in Hcd. simpl.
  rewrite Hcd at 2. apply CardAx1.
  rewrite cprd_0_l, bunion_empty. symmetry.
  set (Func 𝜅 (𝜅 × ⎨0⎬) (λ x, <x, 0>)) as F.
  exists F. apply meta_bijection.
  - intros x Hx. apply CPrdI...
  - intros x1 Hx1 x2 Hx2 Heq. apply op_iff in Heq as []...
  - intros y Hy. apply CPrdE1 in Hy as [a [Ha [b [Hb Hy]]]].
    apply SingE in Hb. subst. exists a. split...
Qed.

(* 基数乘于零等于零 *)
Lemma cardMul_0_r_r : ∀ 𝜅, 𝜅 ⋅ 0 = 0.
Proof.
  intros 𝜅. apply card_eq_0. apply EmptyI.
  intros x Hx. apply CPrdE0 in Hx as []. exfalso0.
Qed.

(* 1是基数乘法单位元 *)
Lemma cardMul_1_r : ∀𝜅 ⋵ 𝐂𝐃, 𝜅 ⋅ 1 = 𝜅.
Proof.
  intros 𝜅 Hcd. apply card_of_card in Hcd. simpl.
  rewrite Hcd at 2. apply CardAx1. symmetry.
  rewrite one. apply eqnum_cprd_single.
Qed.

(* 壹到集合A的函数的集合与A等势 *)
Lemma arrow_from_one : ∀ A, 1 ⟶ A ≈ A.
Proof with neauto; try congruence.
  intros. symmetry.
  set (Func A (1 ⟶ A) (λ x, ⎨<0, x>⎬)) as F.
  exists F. apply meta_bijection.
  - intros x Hx.
    destruct (single_pair_bijection 0 x) as [[Hf Hi] [Hd Hr]].
    rewrite one... apply arrow_iff. split; [|split]...
    intros w Hw. apply SingE in Hw. subst.
    eapply single_of_member_is_subset...
    apply (ap_ran ⎨∅⎬)... split... split...
  - intros x1 Hx1 x2 Hx2 Heq.
    assert (<0, x1> ∈ ⎨<0, x1>⎬) by auto.
    rewrite Heq in H. apply SingE in H.
    apply op_iff in H as []...
  - intros f Hf. apply SepE in Hf as [Hsub [Hf [Hd Hr]]].
    assert (H0d: 0 ∈ dom f). { rewrite Hd. apply suc_has_0... }
    apply domE in H0d as [y H]. exists y. split.
    + apply Hr... eapply ranI...
    + ext p Hp.
      * apply SingE in Hp. subst p...
      * apply PowerAx in Hsub. apply Hsub in Hp as Hcp.
        apply CPrdE1 in Hcp as [a [Ha [b [Hb Hp']]]].
        subst p. rewrite one in Ha. apply SingE in Ha. subst a.
        cut (b = y). intros Heq. subst... eapply func_sv...
Qed.

(* 基数的1次幂等于自身 *)
Lemma cardExp_1_r : ∀𝜅 ⋵ 𝐂𝐃, 𝜅 ^ 1 = 𝜅.
Proof.
  intros 𝜅 Hcd. apply card_of_card in Hcd. simpl.
  rewrite Hcd at 2. apply CardAx1. apply arrow_from_one.
Qed.

(* 1的任意基数次幂等于1 *)
Lemma cardExp_1_l : ∀ 𝜅, 1 ^ 𝜅 = 1.
Proof with nauto.
  intros. rewrite (card_of_nat 1) at 2...
  apply CardAx1.
  set (Func (𝜅 ⟶ 1) 1 (λ _, 0)) as F.
  exists F. apply meta_bijection.
  - intros x Hx. apply suc_has_n.
  - intros f1 Hf1 f2 Hf2 Heq.
    cut (∀ g1 g2 𝜆, g1 ∈ 𝜆 ⟶ 1 → g2 ∈ 𝜆 ⟶ 1 → g1 ⊆ g2). {
      intros H. apply sub_antisym; eapply H; eauto.
    }
    clear Heq Hf1 Hf2 f1 f2 𝜅 F.
    intros f1 f2 𝜅 Hf1 Hf2 p Hp.
    apply arrow_iff in Hf1 as [Hf1 [Hd1 Hr1]].
    apply arrow_iff in Hf2 as [Hf2 [Hd2 Hr2]]. subst.
    apply func_pair in Hp as Hpeq...
    rewrite Hpeq. rewrite Hpeq in Hp.
    apply domI in Hp as Hd. apply func_ap in Hp as Hap...
    apply Hr1 in Hd as H1. rewrite one in H1. apply SingE in H1.
    apply Hr2 in Hd as H2. rewrite one in H2. apply SingE in H2.
    rewrite <- Hap, H1, <- H2. apply func_correct... rewrite Hd2...
  - intros y Hy. rewrite one in Hy. apply SingE in Hy. subst.
    set (Func 𝜅 1 (λ _, 0)) as G.
    exists G. split... apply SepI.
    + apply PowerAx. intros p Hp. apply SepE1 in Hp...
    + apply meta_function. intros _ _. apply suc_has_n.
Qed.

(* 空集到任意集合的函数的集合等于壹 *)
Lemma arrow_from_empty : ∀ A, 0 ⟶ A = 1.
Proof with nauto.
  intros. ext p Hp.
  - apply SepE in Hp as [Hp _].
    rewrite PowerAx, cprd_0_l, sub_empty in Hp.
    subst. apply suc_has_0...
  - apply BUnionE in Hp as []. exfalso0.
    apply SingE in H. subst. rewrite <- ident_empty.
    apply arrow_iff. split; [|split].
    + apply ident_is_func.
    + rewrite dom_ident...
    + intros x Hx. exfalso0.
Qed.

(* 任意非空集合到空集的函数的集合等于空集 *)
Lemma arrow_to_empty : ∀ A, ⦿ A → A ⟶ 0 = 0.
Proof with auto.
  intros A [a Ha]. ext p Hp.
  apply arrow_iff in Hp as [_ [_ Hr]].
  apply Hr in Ha. exfalso0. exfalso0.
Qed.

(* 基数的零次幂等于1 *)
Lemma cardExp_0_r : ∀ 𝜅, 𝜅 ^ 0 = 1.
Proof.
  intros. unfold CardExp. rewrite arrow_from_empty.
  symmetry. apply card_of_nat; nauto.
Qed.

(* 零的非零基数次幂等于零 *)
Lemma cardExp_0_l : ∀ 𝜅, 𝜅 ≠ ∅ → 0 ^ 𝜅 = 0.
Proof with auto.
  intros. unfold CardExp. rewrite arrow_to_empty.
  apply card_eq_0... apply EmptyNE. apply H.
Qed.

Fact cardExp_0_0 : 0 ^ 0 = 1.
Proof. apply cardExp_0_r. Qed.

(* 任意集合的幂集的基数等于2的该集合基数次幂 *)
Lemma card_of_power : ∀ A, |𝒫 A| = 2 ^ |A|.
Proof with auto.
  intros. pose proof (power_eqnum_func_to_2 A).
  apply CardAx1 in H. rewrite H. clear H.
  apply CardAx1. apply cardExp_well_defined. easy. apply CardAx0.
Qed.

(* 任意基数不等于2的该基数次幂 *)
Lemma card_neq_exp : ∀𝜅 ⋵ 𝐂𝐃, 𝜅 ≠ 2 ^ 𝜅.
Proof.
  intros 𝜅 Hcd Heq. apply card_of_card in Hcd.
  rewrite Hcd, <- card_of_power in Heq.
  apply CardAx1 in Heq. eapply Cantor's. apply Heq.
Qed.

(* 基数加法交换律 *)
Theorem cardAdd_comm : ∀ 𝜅 𝜆, 𝜅 + 𝜆 = 𝜆 + 𝜅.
Proof.
  intros. apply CardAx1. rewrite bunion_comm.
  apply cardAdd_well_defined.
  - rewrite <- eqnum_cprd_single.
    rewrite <- eqnum_cprd_single. reflexivity.
  - rewrite <- eqnum_cprd_single.
    rewrite <- eqnum_cprd_single. reflexivity.
  - unfold disjoint. rewrite binter_comm. apply disjointify_0_1.
  - apply disjointify_0_1.
Qed.

(* 基数乘法交换律 *)
Theorem cardMul_comm : ∀ 𝜅 𝜆, 𝜅 ⋅ 𝜆 = 𝜆 ⋅ 𝜅.
Proof with auto.
  intros. apply CardAx1.
  set (Func (𝜅 × 𝜆) (𝜆 × 𝜅) (λ x, <π2 x, π1 x>)) as F.
  exists F. apply meta_bijection.
  - intros x Hx. apply CPrdE0 in Hx as []. apply CPrdI...
  - intros x1 Hx1 x2 Hx2 Heq.
    apply cprd_is_pairs in Hx1 as [a [b Hx1]].
    apply cprd_is_pairs in Hx2 as [c [d Hx2]].
    apply op_iff in Heq as []. subst. zfc_simple.
  - intros y Hy.
    apply CPrdE1 in Hy as [a [Ha [b [Hb Hy]]]]. subst.
    exists <b, a>. split. apply CPrdI... zfc_simple.
Qed.

Fact cardAdd_k_k : ∀ 𝜅, 𝜅 + 𝜅 = 2 ⋅ 𝜅.
Proof with auto.
  intros. rewrite cardMul_comm. apply CardAx1.
  cut (𝜅 × ⎨0⎬ ∪ 𝜅 × ⎨1⎬ = 𝜅 × 2). { intros H. now rewrite H. }
  assert (H1_2: 1 ∈ 2). apply suc_has_n.
  assert (H0_2: 0 ∈ 2) by (apply suc_has_0; apply ω_inductive; nauto).
  ext Hx.
  - apply BUnionE in Hx as [].
    + apply CPrdE1 in H as [a [Ha [b [Hb H]]]].
      apply SingE in Hb. subst. apply CPrdI...
    + apply CPrdE1 in H as [a [Ha [b [Hb H]]]].
      apply SingE in Hb. subst. apply CPrdI...
  - apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]].
    subst. apply BUnionE in Hb as [].
    + apply BUnionE in H as []. exfalso0.
      apply BUnionI1. apply CPrdI...
    + apply SingE in H. subst b.
      apply BUnionI2. apply CPrdI...
Qed.

(* 基数加法结合律 *)
Theorem cardAdd_assoc : ∀ 𝜅 𝜆 𝜇, (𝜅 + 𝜆) + 𝜇 = 𝜅 + (𝜆 + 𝜇).
Proof with neauto; try congruence; try easy.
  intros. apply CardAx1.
  assert (Hnq: Embed 1 = Embed 2 → False). {
    intros. apply (nat_irrefl 2)...
    rewrite <- H at 1. apply suc_has_n.
  }
  eapply Equivalence_Transitive. {
    apply cardAdd_well_defined.
    - unfold CardAdd. rewrite <- eqnum_cprd_single, <- CardAx0...
    - rewrite <- eqnum_cprd_single, (eqnum_cprd_single _ 2)...
    - apply disjointify_0_1.
    - unfold disjoint. rewrite binter_comm, binter_bunion_distr.
      apply EmptyI. intros x Hx.
      apply BUnionE in Hx as []; apply BInterE in H as [].
      + eapply disjointE. apply (cprd_disjointify 𝜇 𝜅 2 0).
        apply suc_neq_0. apply H. apply H0.
      + eapply disjointE. apply (cprd_disjointify 𝜇 𝜆 2 1).
        intro. apply Hnq... apply H. apply H0.
  }
  symmetry. eapply Equivalence_Transitive. {
    apply cardAdd_well_defined.
    - reflexivity.
    - unfold CardAdd. rewrite <- eqnum_cprd_single, <- CardAx0.
      apply cardAdd_well_defined.
      + rewrite <- eqnum_cprd_single, (eqnum_cprd_single _ 1)...
      + rewrite <- eqnum_cprd_single, (eqnum_cprd_single _ 2)...
      + apply disjointify_0_1.
      + apply cprd_disjointify. intro. apply Hnq...
    - apply disjointify_0_1.
    - unfold disjoint. rewrite binter_bunion_distr.
      apply EmptyI. intros x Hx. apply BUnionE in Hx as [].
      + pose proof (disjointify_0_1 𝜅 𝜆).
        rewrite H0 in H. exfalso0.
      + apply BInterE in H as [].
        eapply disjointE. apply (cprd_disjointify 𝜅 𝜇 0 2).
        intro. eapply suc_neq_0... apply H. apply H0.
  }
  rewrite bunion_assoc...
Qed.

(* 基数乘法结合律 *)
Theorem cardMul_assoc : ∀ 𝜅 𝜆 𝜇, (𝜅 ⋅ 𝜆) ⋅ 𝜇 = 𝜅 ⋅ (𝜆 ⋅ 𝜇).
Proof.
  intros. apply CardAx1. eapply Equivalence_Transitive.
  - apply cardMul_well_defined.
    symmetry. apply CardAx0. reflexivity.
  - rewrite eqnum_cprd_assoc.
    apply cardMul_well_defined. easy. apply CardAx0.
Qed.

(* 基数乘法分配律 *)
Theorem cardMul_distr : ∀ 𝜅 𝜆 𝜇, 𝜅 ⋅ (𝜆 + 𝜇) = 𝜅 ⋅ 𝜆 + 𝜅 ⋅ 𝜇.
Proof with auto.
  intros. apply CardAx1.
  eapply Equivalence_Transitive. {
    apply cardMul_well_defined.
    reflexivity. symmetry. apply CardAx0...
  }
  rewrite ex3_2_a. apply cardAdd_well_defined.
  - rewrite <- eqnum_cprd_assoc.
    apply cardMul_well_defined... apply CardAx0.
  - rewrite <- eqnum_cprd_assoc.
    apply cardMul_well_defined... apply CardAx0.
  - apply disjointI. intros [x [H1 H2]].
    apply CPrdE0 in H1 as [_ H1].
    apply CPrdE0 in H2 as [_ H2].
    eapply disjointE; revgoals.
    apply H2. apply H1. apply disjointify_0_1.
  - apply disjointify_0_1.
Qed.

Corollary cardMul_distr' : ∀ 𝜅 𝜆 𝜇, (𝜆 + 𝜇) ⋅ 𝜅 = 𝜆 ⋅ 𝜅 + 𝜇 ⋅ 𝜅.
Proof.
  intros. rewrite cardMul_comm, cardMul_distr.
  rewrite cardMul_comm, (cardMul_comm 𝜅). reflexivity.
Qed.

Theorem cardExp_add : ∀ 𝜅 𝜆 𝜇, 𝜅 ^ (𝜆 + 𝜇) = 𝜅 ^ 𝜆 ⋅ 𝜅 ^ 𝜇.
Proof with eauto; try congruence.
  intros. apply CardAx1.
  eapply Equivalence_Transitive. {
    apply cardExp_well_defined.
    reflexivity. symmetry. apply CardAx0.
  }
  symmetry. eapply Equivalence_Transitive. {
    unfold CardExp. apply cardMul_well_defined.
    - rewrite <- CardAx0. apply cardExp_well_defined.
      reflexivity. apply (eqnum_cprd_single _ 0).
    - rewrite <- CardAx0. apply cardExp_well_defined.
      reflexivity. apply (eqnum_cprd_single _ 1).
  }
  remember (𝜆 × ⎨0⎬) as s. remember (𝜇 × ⎨1⎬) as t.
  assert (Hdj: disjoint s t). { subst. apply disjointify_0_1. }
  clear Heqs Heqt. symmetry.
  set (Func (s ∪ t ⟶ 𝜅) ((s ⟶ 𝜅) × (t ⟶ 𝜅)) (λ f,
    <Func s 𝜅 (λ x, f[x]), Func t 𝜅 (λ x, f[x])>
  )) as F.
  exists F. apply meta_bijection.
  - intros f Hf. apply arrow_iff in Hf as [Hf [Hd Hr]].
    apply CPrdI; apply SepI.
    + apply PowerAx. intros p Hp. apply SepE1 in Hp...
    + apply meta_function.
      intros x Hx. apply Hr. apply BUnionI1...
    + apply PowerAx. intros p Hp. apply SepE1 in Hp...
    + apply meta_function.
      intros x Hx. apply Hr. apply BUnionI2...
  - intros f1 Hf1 f2 Hf2 Heq.
    apply op_iff in Heq as [H1 H2].
    apply arrow_iff in Hf1 as [Hf1 [Hd1 Hr1]].
    apply arrow_iff in Hf2 as [Hf2 [Hd2 Hr2]].
    apply func_ext_intro... intros x Hx. rewrite Hd1 in Hx.
    apply BUnionE in Hx as [Hx|Hx].
    + assert (HF: <x, f1[x]> ∈ Func s 𝜅 (λ x, f1[x])). {
        apply SepI. apply CPrdI... apply Hr1.
        apply BUnionI1... zfc_simple.
      }
      rewrite H1 in HF. apply SepE in HF as [_ HF]. zfc_simple.
    + assert (HF: <x, f1[x]> ∈ Func t 𝜅 (λ x, f1[x])). {
        apply SepI. apply CPrdI... apply Hr1.
        apply BUnionI2... zfc_simple.
      }
      rewrite H2 in HF. apply SepE in HF as [_ HF]. zfc_simple.
  - intros y Hy. apply CPrdE1 in Hy as [g [Hg [h [Hh Heq]]]].
    apply arrow_iff in Hg as [Hgf [Hgd Hgr]].
    apply arrow_iff in Hh as [Hhf [Hhd Hhr]].
    set (Func (s ∪ t) 𝜅 (λ x, match (ixm (x ∈ s)) with
      | inl _ => g[x] | inr _ => h[x]
    end )) as f.
    assert (Hf: f: s ∪ t ⇒ 𝜅). {
      apply meta_function. intros x Hx.
      apply BUnionE in Hx as []; destruct (ixm (x ∈ s))...
    }
    exists f. split. apply SepI... apply PowerAx.
    intros p Hp. apply SepE1 in Hp...
    destruct Hf as [Hff [Hfd Hfr]].
    subst y. apply op_iff. split. {
      ext p Hp.
      - apply SepE in Hp as [H1 H2].
        apply CPrdE1 in H1 as [x [Hx [y [_ Hp]]]].
        subst p. zfc_simple. subst y.
        assert (x ∈ dom f). { rewrite Hfd. apply BUnionI1... }
        apply func_correct in H... apply SepE in H as [_ H2].
        zfc_simple. destruct (ixm (x ∈ s))...
        rewrite H2. apply func_correct...
      - apply func_pair' in Hp as [x [y [Hp Heqp]]]...
        subst p. apply domI in Hp as Hx. apply func_ap in Hp...
        subst y. apply SepI.
        + apply CPrdI... apply Hgr...
        + zfc_simple. rewrite Hgd in Hx.
          assert (x ∈ dom f). { rewrite Hfd. apply BUnionI1... }
          apply func_correct in H... apply SepE in H as [_ H].
          zfc_simple. destruct (ixm (x ∈ s))...
    } {
      ext p Hp.
      - apply SepE in Hp as [H1 H2].
        apply CPrdE1 in H1 as [x [Hx [y [_ Hp]]]].
        subst p. zfc_simple. subst y.
        assert (x ∈ dom f). { rewrite Hfd. apply BUnionI2... }
        apply func_correct in H... apply SepE in H as [_ H2].
        zfc_simple. destruct (ixm (x ∈ s))...
        + exfalso. eapply disjointE...
        + rewrite H2. apply func_correct...
      - apply func_pair' in Hp as [x [y [Hp Heqp]]]...
        subst p. apply domI in Hp as Hx. apply func_ap in Hp...
        subst y. apply SepI.
        + apply CPrdI... apply Hhr...
        + zfc_simple. rewrite Hhd in Hx.
          assert (x ∈ dom f). { rewrite Hfd. apply BUnionI2... }
          apply func_correct in H... apply SepE in H as [_ H].
          zfc_simple. destruct (ixm (x ∈ s))...
          exfalso. eapply disjointE...
    }
Qed.

Theorem cardExp_mul : ∀ 𝜅 𝜆 𝜇, (𝜅 ⋅ 𝜆) ^ 𝜇 = 𝜅 ^ 𝜇 ⋅ 𝜆 ^ 𝜇.
Proof with eauto; try congruence.
  intros. apply CardAx1.
  eapply Equivalence_Transitive. {
    apply cardExp_well_defined.
    symmetry. apply CardAx0. reflexivity.
  }
  symmetry. eapply Equivalence_Transitive. {
    unfold CardExp. apply cardMul_well_defined.
    - symmetry. apply CardAx0.
    - symmetry. apply CardAx0.
  }
  set (Func ((𝜇 ⟶ 𝜅) × (𝜇 ⟶ 𝜆)) (𝜇 ⟶ 𝜅 × 𝜆) (λ p,
    Func 𝜇 (𝜅 × 𝜆) (λ x, <(π1 p)[x], (π2 p)[x]>)
  )) as F.
  exists F. apply meta_bijection.
  - intros p Hp. apply CPrdE1 in Hp as [g [Hg [h [Hh Hp]]]].
    apply arrow_iff in Hg as [Hgf [Hgd Hgr]].
    apply arrow_iff in Hh as [Hhf [Hhd Hhr]].
    subst p. zfc_simple. apply SepI.
    + apply PowerAx. intros p Hp. apply SepE1 in Hp...
    + apply meta_function. intros x Hx. apply CPrdI.
      apply Hgr... apply Hhr...
  - intros p1 Hp1 p2 Hp2 Heq.
    apply CPrdE1 in Hp1 as [g1 [Hg1 [h1 [Hh1 H1]]]].
    apply CPrdE1 in Hp2 as [g2 [Hg2 [h2 [Hh2 H2]]]].
    subst p1 p2. zfc_simple. apply op_iff.
    cut (∀x ∈ 𝜇, <g1[x], h1[x]> = <g2[x], h2[x]>). {
      apply arrow_iff in Hg1 as [Hg1 [Hdg1 _]].
      apply arrow_iff in Hh1 as [Hh1 [Hdh1 _]].
      apply arrow_iff in Hg2 as [Hg2 [Hdg2 _]].
      apply arrow_iff in Hh2 as [Hh2 [Hdh2 _]].
      intros H; split; eapply func_ext_intro...
      - intros x Hx. rewrite Hdg1 in Hx.
        apply H in Hx. apply op_iff in Hx as []...
      - intros x Hx. rewrite Hdh1 in Hx.
        apply H in Hx. apply op_iff in Hx as []...
    }
    intros x Hx.
    cut (∀ g h, g ∈ 𝜇 ⟶ 𝜅 → h ∈ 𝜇 ⟶ 𝜆 →
      <x, <g[x], h[x]>> ∈ Func 𝜇 (𝜅 × 𝜆) (λ x, <g[x], h[x]>)). {
      intros H. pose proof (H _ _ Hg1 Hh1).
      rewrite Heq in H0. apply SepE in H0 as [_ H0]. zfc_simple.
    }
    intros g h Hg Hh.
    apply arrow_iff in Hg as [Hg [Hdg Hrg]].
    apply arrow_iff in Hh as [Hh [Hdh Hrh]].
    apply SepI; zfc_simple. apply CPrdI... apply CPrdI.
    apply Hrg... apply Hrh...
  - intros f Hf. apply SepE in Hf as [_ Hf].
    assert (Hf' := Hf). destruct Hf' as [Hff [Hdf Hrf]].
    set (Func 𝜇 𝜅 (λ x, π1 f[x])) as g.
    set (Func 𝜇 𝜆 (λ x, π2 f[x])) as h.
    assert (Hg: g: 𝜇 ⇒ 𝜅). {
      apply meta_function. intros x Hx. rewrite <- Hdf in Hx.
      apply func_correct in Hx... apply ranI in Hx.
      apply Hrf in Hx. apply CPrdE0 in Hx as []...
    }
    assert (Hh: h: 𝜇 ⇒ 𝜆). {
      apply meta_function. intros x Hx. rewrite <- Hdf in Hx.
      apply func_correct in Hx... apply ranI in Hx.
      apply Hrf in Hx. apply CPrdE0 in Hx as []...
    }
    exists <g, h>. split. {
      apply CPrdI; apply SepI...
      - apply PowerAx. intros p Hp. apply SepE1 in Hp...
      - apply PowerAx. intros p Hp. apply SepE1 in Hp...
    }
    destruct Hg as [Hgf [Hgd _]].
    destruct Hh as [Hhf [Hhd _]].
    assert (Hfx: ∀x ∈ 𝜇, f[x] = <g[x], h[x]>). {
      intros x Hx. rewrite <- Hdf in Hx.
      apply func_correct in Hx as Hfx...
      apply ranI in Hfx. apply Hrf in Hfx. 
      apply CPrdE1 in Hfx as [a [Ha [b [Hb Hfx]]]].
      rewrite Hfx. apply op_iff.
      split; symmetry; apply func_ap; auto; (apply SepI;
      [apply CPrdI; congruence|zfc_simple; rewrite Hfx; zfc_simple]).
    }
    ext p Hp.
    + apply SepE in Hp as [Hp Heq].
      apply CPrdE1 in Hp as [x [Hx [y [_ Hp]]]].
      subst p. zfc_simple. subst y. apply Hfx in Hx as Hap.
      rewrite <- Hap. apply func_correct...
    + apply func_pair' in Hp as [x [y [Hp Heqp]]]...
      subst p. apply domI in Hp as Hx. apply ranI in Hp as Hy.
      apply Hrf in Hy. apply SepI; zfc_simple. apply CPrdI...
      rewrite Hdf in Hx. apply Hfx in Hx as Hap.
      rewrite <- Hap. symmetry. apply func_ap...
Qed.

Theorem cardExp_exp : ∀ 𝜅 𝜆 𝜇, (𝜅 ^ 𝜆) ^ 𝜇 = 𝜅 ^ (𝜆 ⋅ 𝜇).
Proof with eauto; try congruence.
  intros. apply CardAx1.
  eapply Equivalence_Transitive. {
    apply cardExp_well_defined.
    symmetry. apply CardAx0. reflexivity.
  }
  symmetry. eapply Equivalence_Transitive. {
    apply cardExp_well_defined.
    reflexivity. symmetry. apply CardAx0.
  }
  set (Func (𝜆 × 𝜇 ⟶ 𝜅) (𝜇 ⟶ (𝜆 ⟶ 𝜅)) (λ f,
    Func 𝜇 (𝜆 ⟶ 𝜅) (λ y,
      Func 𝜆 𝜅 (λ x, f[<x, y>])
  ))) as F.
  exists F. apply meta_bijection.
  - intros f Hf. apply SepI. {
      apply PowerAx. intros p Hp. apply SepE1 in Hp...
    }
    apply meta_function. intros y Hy. apply SepI. {
      apply PowerAx. intros p Hp. apply SepE1 in Hp...
    }
    apply meta_function. intros x Hx.
    apply SepE in Hf as [_ Hf].
    eapply ap_ran... apply CPrdI...
  - intros f1 Hf1 f2 Hf2 Heq.
    apply arrow_iff in Hf1 as [Hf1 [Hdf1 Hrf1]].
    apply arrow_iff in Hf2 as [Hf2 [Hdf2 _]].
    apply func_ext_intro... intros x Hx. rewrite Hdf1 in Hx.
    apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]]. subst x.
    remember (Func 𝜇 (𝜆 ⟶ 𝜅) (λ y, Func 𝜆 𝜅 (λ x, f1[<x, y>]))) as F1.
    cut (<b, Func 𝜆 𝜅 (λ x, f1[<x, b>])> ∈ F1). {
      intros H1. rewrite Heq in H1.
      apply SepE in H1 as [_ H1]. zfc_simple.
      cut (<a, f1[<a, b>]> ∈ Func 𝜆 𝜅 (λ x, f1[<x, b>])). {
        intros H2. rewrite H1 in H2.
        apply SepE in H2 as [_ H2]. zfc_simple.
      }
      apply SepI; zfc_simple.
      apply CPrdI... apply Hrf1. apply CPrdI...
    }
    subst F1. apply SepI; zfc_simple.
    apply CPrdI... apply SepI. {
      apply PowerAx. intros p Hp. apply SepE1 in Hp...
    }
    apply meta_function. intros x Hx.
    apply Hrf1. apply CPrdI...
  - intros f Hf. apply SepE in Hf as [_ [Hff [Hdf Hrf]]].
    set (Func (𝜆 × 𝜇) 𝜅 (λ p, f[π2 p][π1 p])) as g.
    assert (H1: ∀x ∈ dom f, f[x] = Func 𝜆 𝜅 (λ y, g[<y, x>])). {
      intros x Hx. apply func_correct in Hx as Hfx...
      apply ranI in Hfx. apply Hrf in Hfx.
      apply arrow_iff in Hfx as [Hhf [Hhd Hhr]].
      apply func_ext_intro... apply func_is_func.
      - ext y Hy.
        + eapply domI. apply SepI.
          * apply CPrdI... apply Hhr. rewrite <- Hhd. apply Hy.
          * zfc_simple. symmetry.
            apply func_ap. apply func_is_func.
            apply SepI; zfc_simple. apply CPrdI.
            apply CPrdI... apply Hhr...
        + apply domE in Hy as [z Hp]. apply SepE in Hp as [Hy _].
          apply CPrdE2 in Hy as [Hy _]...
      - intros y Hy. symmetry. apply func_ap.
        apply func_is_func. apply SepI; zfc_simple.
        + apply CPrdI... apply Hhr...
        + symmetry. apply func_ap. apply func_is_func.
          apply SepI; zfc_simple. apply CPrdI.
          apply CPrdI... apply Hhr...
    }
    assert (H2: ∀x ∈ dom f, <x, f[x]> ∈ (Func 𝜇 (𝜆 ⟶ 𝜅) (λ b, Func 𝜆 𝜅 (λ a, g[<a, b>])))). {
      intros x Hx. apply SepI; zfc_simple.
      - apply CPrdI. rewrite <- Hdf... apply Hrf.
        eapply ap_ran... split...
      - apply H1...
    }
    assert (H3: dom (Func 𝜇 (𝜆 ⟶ 𝜅) (λ y, Func 𝜆 𝜅 (λ x, g[<x, y>]))) = dom f). {
      ext Hx.
      - apply domE in Hx as [y Hp]. apply SepE in Hp as [Hx _].
        apply CPrdE2 in Hx as [Hx _]...
      - eapply domI. apply H2...
    }
    exists g. split.
    + apply SepI. {
        apply PowerAx. intros p Hp. apply SepE1 in Hp...
      }
      apply meta_function. intros p Hp.
      apply CPrdE1 in Hp as [a [Ha [b [Hb Hp]]]].
      subst p. zfc_simple. rewrite <- Hdf in Hb.
      apply func_correct in Hb... apply ranI in Hb. apply Hrf in Hb.
      apply arrow_iff in Hb as [_ [_ Hr]]. apply Hr...
    + apply func_ext_intro... apply func_is_func.
      intros x Hx. rewrite H3 in Hx.
      apply func_ap. apply func_is_func. apply H2...
Qed.

Lemma cardAdd_suc : ∀ 𝜅 𝜆, 𝜅 + (𝜆 + 1) = (𝜅 + 𝜆) + 1.
Proof. intros. rewrite cardAdd_assoc. auto. Qed.

Lemma cardMul_suc : ∀𝜅 ⋵ 𝐂𝐃, ∀ 𝜆, 𝜅 ⋅ (𝜆 + 1) = 𝜅 ⋅ 𝜆 + 𝜅.
Proof. intros 𝜅 H 𝜆. rewrite cardMul_distr, cardMul_1_r; auto. Qed.

Lemma cardExp_suc : ∀𝜅 ⋵ 𝐂𝐃, ∀ 𝜆, 𝜅 ^ (𝜆 + 1) = 𝜅 ^ 𝜆 ⋅ 𝜅.
Proof. intros 𝜅 H 𝜆. rewrite cardExp_add, cardExp_1_r; auto. Qed.

Lemma card_suc : ∀n ∈ ω, n + 1 = n⁺.
Proof with auto; try easy.
  intros n Hn.
  rewrite (card_of_nat n⁺); [|apply ω_inductive]...
  apply CardAx1. apply cardAdd_well_defined.
  - rewrite <- eqnum_cprd_single...
  - rewrite <- eqnum_cprd_single, eqnum_single...
  - apply disjointify_0_1.
  - apply nat_disjoint...
Qed.

(* 有限基数加法等效于自然数加法 *)
Theorem fin_cardAdd_eq_add : ∀ m n ∈ ω, m + n = (m + n)%ω.
Proof with auto.
  intros m Hm n Hn. generalize dependent m.
  ω_induction n; intros k Hk.
  - rewrite cardAdd_0_r, add_0_r... apply nat_is_card...
  - rewrite <- card_suc at 1...
    rewrite <- cardAdd_assoc, IH, card_suc, add_suc...
    apply add_ran...
Qed.

(* 有限基数乘法等效于自然数乘法 *)
Theorem fin_cardMul_eq_mul : ∀ m n ∈ ω, m ⋅ n = (m ⋅ n)%ω.
Proof with auto.
  intros m Hm n Hn. generalize dependent m.
  ω_induction n; intros k Hk.
  - rewrite cardMul_0_r_r, mul_0_r...
  - rewrite <- card_suc at 1...
    rewrite cardMul_suc, IH, fin_cardAdd_eq_add, mul_suc, add_comm...
    apply mul_ran... apply mul_ran... apply nat_is_card...
Qed.

(* 有限基数乘方等效于自然数乘方 *)
Theorem fin_cardExp_eq_exp : ∀ m n ∈ ω, m ^ n = (m ^ n)%ω.
Proof with auto.
  intros m Hm n Hn. generalize dependent m.
  ω_induction n; intros k Hk.
  - rewrite cardExp_0_r, exp_0_r...
  - rewrite <- card_suc at 1...
    assert ((k ^ m)%ω ∈ ω) by (apply exp_ran; auto).
    rewrite cardExp_suc, IH, fin_cardMul_eq_mul, exp_suc, mul_comm...
    apply nat_is_card...
Qed.

(* 有限基数的和是自然数 *)
Corollary fin_cardAdd_ran : ∀ m n ∈ ω, m + n ∈ ω.
Proof with auto.
  intros m Hm n Hn. rewrite fin_cardAdd_eq_add... apply add_ran...
Qed.

(* 有限基数的积是自然数 *)
Corollary fin_cardMul_ran : ∀ m n ∈ ω, m ⋅ n ∈ ω.
Proof with auto.
  intros m Hm n Hn. rewrite fin_cardMul_eq_mul... apply mul_ran...
Qed.

(* 有限基数的幂是自然数 *)
Corollary fin_cardExp_ran : ∀ m n ∈ ω, m ^ n ∈ ω.
Proof with auto.
  intros m Hm n Hn. rewrite fin_cardExp_eq_exp... apply exp_ran...
Qed.

(* 有限集的二元并仍是有限集 *)
Corollary bunion_finite :
  ∀ A B, finite A → finite B → finite (A ∪ B).
Proof with auto.
  intros * Hfa Hfb. rewrite <- ex2_11_2.
  assert (Hfb': finite (B - A)). {
    apply (subset_of_finite_is_finite _ B)...
  }
  destruct Hfa as [m [Hm Ha]]. destruct Hfb' as [n [Hn Hb]].
  exists (m + n). split. apply fin_cardAdd_ran...
  unfold CardAdd. rewrite <- CardAx0.
  apply cardAdd_well_defined.
  - rewrite Ha. apply eqnum_cprd_single.
  - rewrite Hb. apply eqnum_cprd_single.
  - apply binter_comp_empty.
  - apply disjointify_0_1.
Qed.

(* 有限集的笛卡尔积仍是有限集 *)
Corollary cprd_finite :
  ∀ A B, finite A → finite B → finite (A × B).
Proof with auto.
  intros * [m [Hm Ha]] [n [Hn Hb]].
  exists (m ⋅ n). split. apply fin_cardMul_ran...
  unfold CardMul. rewrite <- CardAx0.
  apply cardMul_well_defined...
Qed.

(* 有限集张起的函数空间是有限集 *)
Corollary arrow_finite :
  ∀ A B, finite A → finite B → finite (B ⟶ A).
Proof with auto.
  intros * [m [Hm Ha]] [n [Hn Hb]].
  exists (m ^ n). split. apply fin_cardExp_ran...
  unfold CardExp. rewrite <- CardAx0.
  apply cardExp_well_defined...
Qed.

(* 与后继数等势的集合非空 *)
Lemma set_eqnum_suc_nonempty : ∀ A, ∀n ∈ ω, A ≈ n⁺ → ⦿ A.
Proof with eauto.
  intros A n Hn HA. apply EmptyNE.
  contra. apply NNPP in H. subst A.
  symmetry in HA. apply eqnum_empty in HA. eapply suc_neq_0...
Qed.

(* 有限集里的补集是有限集 *)
Lemma comp_finite : ∀ A B, finite A → finite (A - B).
Proof with auto.
  intros * [n [Hn Hqn]]. generalize dependent A.
  ω_induction n; intros A Hqn.
  - apply eqnum_empty in Hqn. subst A.
    rewrite empty_comp. apply empty_finite.
  - apply set_eqnum_suc_nonempty in Hqn as Hne...
    destruct Hne as [a Ha].
    apply split_one_element in Ha. rewrite Ha in *.
    apply finite_set_remove_one_element in Hqn... rewrite bunion_comp.
    apply bunion_finite. apply IH...
    destruct (classic (a ∈ B)).
    + replace (⎨a⎬ - B) with ∅. apply empty_finite.
      ext Hx. exfalso0. exfalso.
      apply SepE in Hx as [Hx Hx']. apply SingE in Hx; subst...
    + replace (⎨a⎬ - B) with (⎨a⎬)...
      ext Hx.
      * apply SingE in Hx; subst. apply SepI...
      * apply SepE1 in Hx...
Qed.

(* 有限集加上一个元素仍是有限集 *)
Lemma add_one_still_finite_1 :
  ∀ a A, finite (A - ⎨a⎬) → finite A.
Proof with auto.
  intros * Hfin.
  destruct (classic (a ∈ A)).
  - rewrite <- (remove_one_member_then_return A a)...
    apply bunion_finite...
  - rewrite remove_no_member in Hfin...
Qed.

(* 有限集加上一个元素仍是有限集 *)
Lemma add_one_still_finite_2 : ∀ A a,
  finite A → finite (A ∪ ⎨a⎬).
Proof with auto.
  intros * Hfa.
  destruct (classic (disjoint A ⎨a⎬)).
  - destruct Hfa as [m [Hm HA]].
    exists m⁺. split. apply ω_inductive...
    apply cardAdd_well_defined... apply nat_disjoint...
  - apply EmptyNE in H as [a' Ha].
    apply BInterE in Ha as [Ha Heq].
    apply SingE in Heq. subst a'.
    replace (A ∪ ⎨ a ⎬) with A...
    ext Hx.
    + apply BUnionI1...
    + apply BUnionE in Hx as []... apply SingE in H. subst x...
Qed.

(* 无限集除去一个元素仍是无限集 *)
Lemma remove_one_member_from_infinite :
  ∀ a A, infinite A → infinite (A - ⎨a⎬).
Proof.
  intros * Hinf Hfin. apply Hinf.
  eapply add_one_still_finite_1; eauto.
Qed.

(* 二元并的替代等于替代的二元并 *)
Lemma bunion_of_repl_eq_repl_of_bunion : ∀ F A B,
  {F x | x ∊ A ∪ B} = {F x | x ∊ A} ∪ {F x | x ∊ B}.
Proof with auto.
  intros; apply ExtAx; intros y; split; intros Hy.
  - apply ReplAx in Hy as [x [Hx Heq]];
    apply BUnionE in Hx as [];
    [apply BUnionI1|apply BUnionI2];
    apply ReplAx; exists x; split...
  - apply BUnionE in Hy as [];
    apply ReplAx in H as [x [Hx Heq]];
    apply ReplAx; exists x; split; auto;
    [apply BUnionI1|apply BUnionI2]...
Qed.

(* 任意集合与其一对一的替代等势 *)
Lemma eqnum_repl : ∀ F A, (∀ x1 x2 ∈ A, F x1 = F x2 → x1 = x2) →
  A ≈ {F x | x ∊ A}.
Proof with auto.
  intros. set (Func A {F x | x ∊ A} (λ x, F x)) as f.
  exists f. apply meta_bijection.
  - intros x Hx. apply ReplAx. exists x. split...
  - intros x1 H1 x2 H2 Heq. apply H...
  - intros y Hy. apply ReplAx in Hy...
Qed.

(* 任意单集与其任意替代等势 *)
Lemma eqnum_repl_single : ∀ F a, ⎨a⎬ ≈ {F x | x ∊ ⎨a⎬}.
Proof with auto.
  intros. set (Func ⎨a⎬ {F x | x ∊ ⎨a⎬} (λ x, F x)) as f.
  exists f. apply meta_bijection.
  - intros x Hx. apply ReplAx. exists x. split...
  - intros x1 H1 x2 H2 _.
    apply SingE in H1. apply SingE in H2. congruence.
  - intros y Hy. apply ReplAx in Hy...
Qed.

(* 任意单集的任意替代是有限集 *)
Lemma repl_single_finite : ∀ F a, finite {F x | x ∊ ⎨a⎬}.
Proof with auto.
  intros. exists 1. split. nauto.
  rewrite <- eqnum_repl_single. apply eqnum_single.
Qed.

(* 有限集的替代仍是有限集 *)
Lemma repl_finite : ∀ F A, finite A → finite {F x | x ∊ A}.
Proof with auto.
  intros * [n [Hn Hqn]].
  generalize dependent A.
  ω_induction n; intros A Hqn.
  - apply eqnum_empty in Hqn. subst A.
    rewrite repl_empty. apply empty_finite.
  - apply set_eqnum_suc_nonempty in Hqn as Hne...
    destruct Hne as [a Ha].
    apply split_one_element in Ha. rewrite Ha in *.
    apply finite_set_remove_one_element in Hqn...
    rewrite bunion_of_repl_eq_repl_of_bunion.
    apply bunion_finite. apply IH... apply repl_single_finite.
Qed.

(* 有限集与任意集合的交是有限集 *)
Lemma binter_finite_r : ∀ A B, finite B → finite (A ∩ B).
Proof with auto.
  intros * [n [Hn Hqn]].
  generalize dependent B.
  ω_induction n; intros B Hqn.
  - apply eqnum_empty in Hqn. subst B.
    rewrite binter_empty. apply empty_finite.
  - apply set_eqnum_suc_nonempty in Hqn as Hne...
    destruct Hne as [a Ha].
    apply split_one_element in Ha. rewrite Ha in *.
    apply finite_set_remove_one_element in Hqn...
    rewrite binter_bunion_distr.
    apply bunion_finite. apply IH...
    destruct (classic (a ∈ A)).
    + replace (A ∩ ⎨a⎬) with ⎨a⎬. apply single_finite.
      ext Hx.
      * apply SingE in Hx; subst. apply BInterI...
      * apply BInterE in Hx as []...
    + replace (A ∩ ⎨a⎬) with ∅. apply empty_finite.
      ext Hx. exfalso0. exfalso.
      apply BInterE in Hx as []. apply SingE in H1; subst...
Qed.

Corollary binter_finite_l : ∀ A B, finite A → finite (A ∩ B).
Proof.
  intros. rewrite binter_comm. apply binter_finite_r. apply H.
Qed.
