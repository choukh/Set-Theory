(** Solutions to "Elements of Set Theory" Chapter 6 Part 1 **)
(** Coq coding by choukh, Sep 2020 **)

Require Export ZFC.EST6_2.

(* ex6_3 f(x) = 1/x *)
(* ex6_4 0 ↦ 1/2 ↦ 1/4 ... *)
(* ex6_5 see EST6_1 eqnum_refl symm tran *)

(* 同一基数的所有集合不能构成一个集合 *)
Example ex6_6 : ∀ 𝜅, is_card 𝜅 → ⦿ 𝜅 → ¬∃ A, ∀ x, |x| = 𝜅 → x ∈ A.
Proof with auto.
  intros 𝜅 H𝜅 Hi [A Hcd].
  apply no_set_of_all_set. exists (⋃A).
  intros a. apply UnionAx.
  pose proof (any_set_in_set_with_any_nonzero_card a 𝜅 H𝜅 Hi)
    as [K [Heq Ha]]. exists K. split...
Qed.

(* ==可以不用选择公理== *)
(* 有限集到自身的映射是单射当且仅当该映射是满射 *)
Example ex6_7 : ∀ A f, finite A → f: A ⇒ A →
  injective f ↔ ran f = A.
Proof with auto.
  intros A f [n [Hn [g Hg]]] Hf.
  destruct Hf as [Hff [Hdf Hrf]]. assert (Hg' := Hg).
  destruct Hg' as [Hig [Hdg Hrg]]. assert (Hig' := Hig).
  destruct Hig' as [Hfg Hsg].
  assert (Hig': injective g⁻¹) by (apply inv_injective; auto).
  split; intros H.
  - assert (Higf: injective (g ∘ f)) by (apply ex3_17_b; auto).
    assert (Hfc: is_function (g ∘ f)) by (apply compo_func; auto).
    assert (Hfg': is_function g⁻¹) by (apply inv_func_iff_sr; auto).
    assert (Hf': f: A ⇔ A) by (split; auto).
    pose proof (injection_transform f g A n Hf' Hg) as Hh.
    apply injection_between_same_nat_surjective in Hh as Hreq...
    apply sub_asym... intros y Hy. rewrite <- Hdg in Hy.
    apply domE in Hy as [x Hp]. apply ranI in Hp as Hx.
    rewrite Hrg, <- Hreq, compo_ran in Hx...
    apply SepE in Hx as [Hx _]. rewrite compo_ran in Hx...
    apply SepE in Hx as [_ Hx]. apply inv_op in Hp as Hp'.
    apply func_ap in Hp'... subst y...
  - assert (Hrel: is_relation f) by (destruct Hff; auto).
    assert (Hrel': is_relation f⁻¹) by (apply inv_rel; auto).
    assert (Hf': f: A ⟹ A) by (split; auto).
    pose proof (surjection_transform f g A n Hf' Hg) as Hh.
    apply surjection_between_same_nat_injective in Hh as Hreq...
    replace f with (g⁻¹ ∘ ((g ∘ f) ∘ g⁻¹) ∘ g).
    apply compo_injective... apply compo_injective...
    rewrite compo_assoc, compo_assoc, compo_inv_dom_ident,
      compo_assoc, Hdg, <- Hdf, right_compo_ident, restr_to_dom,
      <- compo_assoc, compo_inv_dom_ident, left_compo_ident',
      Hdg, <- H, <- inv_dom, restr_to_dom, inv_inv...
Qed.

(* 有限集添加一个元素仍是有限集 *)
Lemma finite_set_adding_one_still_finite : ∀ A a,
  finite A → finite (A ∪ ⎨a⎬).
Proof with auto.
  intros * Hfa.
  destruct (classic (disjoint A ⎨a⎬)).
  - destruct Hfa as [m [Hm HA]].
    exists m⁺. split. apply ω_inductive...
    apply cardAdd_well_defined... apply disjoint_nat_single...
  - apply EmptyNE in H as [a' Ha].
    apply BInterE in Ha as [Ha Heq].
    apply SingE in Heq. subst a'.
    replace (A ∪ ⎨ a ⎬) with A...
    apply ExtAx. split; intros Hx.
    + apply BUnionI1...
    + apply BUnionE in Hx as []... apply SingE in H. subst x...
Qed.

(* 等势的集合分别除去一个元素仍然等势 *)
Lemma eqnum_sets_removing_one_element_still_eqnum :
  ∀ A B a b, A ∪ ⎨a⎬ ≈ B ∪ ⎨b⎬ →
  disjoint A ⎨a⎬ → disjoint B ⎨b⎬ → A ≈ B.
Proof with eauto; try congruence.
  intros * [f Hf] Hdja Hdjb. assert (Hf' := Hf).
  destruct Hf' as [Hi [Hd Hr]].
  set (FuncSwapValue f a f⁻¹[b]) as g.
  assert (Ha: a ∈ A ∪ ⎨a⎬) by (apply BUnionI2; auto).
  assert (Hbr: b ∈ ran f). { rewrite Hr. apply BUnionI2... }
  assert (Hb: f⁻¹[b] ∈ A ∪ ⎨a⎬). {
    destruct Hi as [Hff Hs].
    rewrite <- Hd, <- inv_ran. eapply ap_ran. split...
    apply inv_func_iff_sr... rewrite inv_dom...
  }
  apply (bijection_swap_value _ _ _ _ Ha _ Hb) in Hf as Hg.
  assert (Hga: g[a] = b). {
    apply func_ap... destruct Hg as [[Hg _] _]...
    apply SepI. apply CProdI... zfcrewrite.
    destruct (ixm (a = a))... rewrite inv_ran_reduction... 
  }
  clear Hf Hi Hd Hr Ha Hbr Hb.
  destruct Hg as [Hi [Hd Hr]]. assert (Hi' := Hi).
  destruct Hi as [Hg Hs].
  exists (g ↾ A). split; [|split].
  - apply restr_injective...
  - apply restr_dom... intros x Hx. subst g.
    rewrite Hd. apply BUnionI1...
  - apply ExtAx. intros y. split; intros Hy.
    + apply ranE in Hy as [x Hp].
      apply restrE2 in Hp as [Hp Hx].
      apply ranI in Hp as Hy. subst g. rewrite Hr in Hy.
      apply BUnionE in Hy as []...
      apply SingE in H. subst y. apply func_ap in Hp...
      rewrite <- Hp in Hga. cut (a = x).
      * intros H. subst x. exfalso. eapply disjointE.
        apply Hdja. apply Hx. apply SingI.
      * eapply injectiveE...
        rewrite Hd. apply BUnionI2...
        rewrite Hd. apply BUnionI1...
    + assert (y ∈ ran g). { subst g. rewrite Hr. apply BUnionI1... }
      apply ranE in H as [x Hp]. apply domI in Hp as Hx.
      subst g. rewrite Hd in Hx. apply BUnionE in Hx as [].
      * eapply ranI. apply restrI...
      * apply SingE in H. subst x. apply func_ap in Hp...
        rewrite <- Hp, Hga in Hy. exfalso. eapply disjointE.
        apply Hdjb. apply Hy. apply SingI.
Qed.

(* 与后继数等势的集合非空 *)
Lemma set_eqnum_suc_inhabited : ∀ A, ∀n ∈ ω, A ≈ n⁺ → ⦿ A.
Proof with eauto.
  intros A n Hn HA. apply EmptyNE.
  destruct (classic (A = ∅))... exfalso. subst A.
  symmetry in HA. apply eqnum_empty in HA. eapply suc_neq_0...
Qed.

(* 从集合中取出一个元素组成单集，它与取完元素后的集合的并等于原集合 *)
Lemma split_one_element : ∀ A a, a ∈ A → A = (A - ⎨a⎬) ∪ ⎨a⎬.
Proof with auto.
  intros. apply ExtAx. split; intros Hx.
  - destruct (classic (x = a)).
    + subst x. apply BUnionI2...
    + apply BUnionI1. apply SepI...
      intros contra. apply SingE in contra...
  - apply BUnionE in Hx as [].
    + apply SepE in H0 as []...
    + apply SingE in H0. subst x...
Qed.

(* 从有限集中取出一个元素则基数减1 *)
Lemma fin_set_remove_one_element : ∀ A a, ∀n ∈ ω,
  (A - ⎨a⎬) ∪ ⎨a⎬ ≈ n⁺ → A - ⎨a⎬ ≈ n.
Proof with eauto.
  intros * n Hn Hqn.
  eapply eqnum_sets_removing_one_element_still_eqnum...
  apply disjointI. intros [x [H1 H2]]. apply SepE in H1 as []...
  apply disjoint_nat_single...
Qed.

(* 有限集的并仍是有限集（非算术证明） *)
Example ex6_8 : ∀ A B, finite A → finite B → finite (A ∪ B).
Proof with eauto.
  intros * Hfa Hfb. rewrite <- ex2_11_2.
  assert (Hfc: finite (B - A)). {
    apply (sub_of_finite_is_finite _ B)...
  }
  assert (Hdj: disjoint A (B - A)) by apply binter_comp_empty.
  remember (B - A) as C. clear HeqC Hfb B.
  destruct Hfc as [n [Hn Hc]].
  generalize dependent C. generalize dependent A.
  set {n ∊ ω | λ n, ∀ A, finite A →
    ∀ C, C ≈ n → disjoint A C → finite (A ∪ C)} as N.
  ω_induction N Hn; intros A Hfa C HC Hdj.
  - apply eqnum_empty in HC. subst C. rewrite bunion_empty...
  - apply set_eqnum_suc_inhabited in HC as Hi...
    destruct Hi as [c Hc].
    apply split_one_element in Hc.
    rewrite Hc in HC. rewrite bunion_comm in Hc.
    rewrite Hc, bunion_assoc. apply IH.
    + apply finite_set_adding_one_still_finite...
    + apply fin_set_remove_one_element...
    + apply disjointI. intros [x [H1 H2]].
      apply SepE in H2 as [H2 H3].
      apply BUnionE in H1 as []... eapply disjointE...
Qed.

(* 有限集的笛卡尔积仍是有限集（非算术证明） *)
Example ex6_9 : ∀ A B, finite A → finite B → finite (A × B).
Proof with eauto.
  intros * Hfa [n [Hn HB]].
  generalize dependent B. generalize dependent A.
  set {n ∊ ω | λ n, ∀ A, finite A →
    ∀ B, B ≈ n → finite (A × B)} as N.
  ω_induction N Hn; intros A Hfa B HB.
  - apply eqnum_empty in HB. subst B. rewrite cprod_x_0...
  - apply set_eqnum_suc_inhabited in HB as Hi...
    destruct Hi as [b Hb].
    apply split_one_element in Hb.
    rewrite Hb in HB. rewrite bunion_comm in Hb.
    rewrite Hb, ex3_54_b. apply ex6_8.
    + destruct Hfa as [k [Hk HA]].
      exists k. split... rewrite <- eqnum_cprod_single...
    + apply IH... apply fin_set_remove_one_element...
Qed.

(* ex6_10 ex6_11 see EST6_2.v *)

Example ex6_12_a : ∀ K L, K ∪ L = L ∪ K.
Proof. exact bunion_comm. Qed.

Example ex6_12_b : ∀ K L M, K ∪ (L ∪ M) = (K ∪ L) ∪ M.
Proof. exact bunion_assoc. Qed.

Example ex6_12_c : ∀ K L M, K × (L ∪ M) = (K × L) ∪ (K × M).
Proof. exact ex3_2_a. Qed.

(* 有限个有限集的并集仍是有限集 *)
Example ex6_13 : ∀ A, finite A → (∀a ∈ A, finite a) → finite ⋃A.
Proof with eauto.
  intros A [n [Hn HA]].
  generalize dependent A.
  set {n ∊ ω | λ n, ∀ A, A ≈ n →
    (∀a ∈ A, finite a) → finite ⋃ A} as N.
  ω_induction N Hn; intros A HA Hfa.
  - apply eqnum_empty in HA. subst A. rewrite union_empty...
  - apply set_eqnum_suc_inhabited in HA as Hi...
    destruct Hi as [a Ha].
    apply split_one_element in Ha as HeqA.
    rewrite HeqA in HA. rewrite bunion_comm in HeqA.
    rewrite HeqA, ex2_21. apply ex6_8.
    + rewrite union_sing_x_x. apply Hfa...
    + apply IH. apply fin_set_remove_one_element...
      intros b Hb. apply Hfa. apply SepE in Hb as []...
Qed.

(* ex6_14 *)
(* 全排列 *)
Definition Permutation : set → set := λ A,
  {f ∊ A ⟶ A | λ f, f: A ⟺ A}.
(* 基数阶乘 *)
Definition CardFactorial : set → set := λ 𝜅,
  |Permutation 𝜅|.
Notation "𝜅 !" := (CardFactorial 𝜅) (at level 60) : Card_scope.

(* 基数阶乘良定义 *)
Theorem cardFactorial_well_defined : ∀ A B, A ≈ B → A! = B!.
Proof with eauto; try congruence.
  intros * [g Hg]. apply CardAx1.
  set (λ f, g ∘ f ∘ g⁻¹) as ℱ.
  set (Func (Permutation A) (Permutation B) (λ f, ℱ f )) as F.
  exists F. apply meta_bijective.
  - intros f Hf. assert (Hh: ℱ f: B ⟺ B). {
      apply SepE in Hf as [_ Hf]. eapply bijection_transform...
    }
    apply SepI... destruct Hh as [[Hfh _] [Hdh Hrh]].
    apply arrow_iff. split; [|split]...
    intros x Hx. eapply ap_ran... split... split...
  - intros f1 Hf1 f2 Hf2 Heq. destruct Hg as [Hig [Hdg _]].
    apply SepE in Hf1 as [_ [[[Hrel1 _] _] [Hdf1 Hrf1]]].
    apply SepE in Hf2 as [_ [[[Hrel2 _] _] [Hdf2 Hrf2]]].
    assert (H1: (ℱ f1) ∘ g  = (ℱ f2) ∘ g) by congruence.
    unfold ℱ in H1. rewrite
      compo_assoc, compo_inv_dom_ident, Hdg, <- Hdf1,
      compo_assoc, right_compo_ident, restr_to_dom,
      compo_assoc, compo_inv_dom_ident, Hdg, <- Hdf2,
      compo_assoc, right_compo_ident, restr_to_dom in H1...
    assert (H2: g⁻¹ ∘ (g ∘ f1) = g⁻¹ ∘ (g ∘ f2)) by congruence.
    rewrite
      <- compo_assoc, compo_inv_dom_ident, Hdg, <- Hdf1,
      left_compo_ident', Hdf1, <- Hrf1,
      <- inv_dom, restr_to_dom, inv_inv,
      <- compo_assoc, compo_inv_dom_ident, Hdg, <- Hdf2,
      left_compo_ident', Hdf2, <- Hrf2,
      <- inv_dom, restr_to_dom, inv_inv in H2...
  - intros h Hh. apply SepE in Hh as [_ Hh].
    set (g⁻¹ ∘ h ∘ g) as f.
    assert (Hf: f: A ⟺ A). {
      unfold f. rewrite <- (inv_inv g) at 2.
      eapply bijection_transform... apply inv_bijection...
      destruct Hg as [[[]]]...
    }
    assert (Hfp: f ∈ Permutation A). {
      apply SepI... destruct Hf as [[Hff _] [Hdf Hrf]].
      apply arrow_iff. split; [|split]...
      intros x Hx. eapply ap_ran... split... split...
    }
    exists f. split...
    destruct Hg as [[Hfg _] [_ Hrg]].
    destruct Hh as [[[Hrelh _] _] [Hdh Hrh]].
    unfold ℱ, f. rewrite
      compo_assoc, compo_assoc, compo_inv_ran_ident,
      compo_assoc, <- compo_assoc, compo_inv_ran_ident,
      right_compo_ident, Hrg, <- Hdh, restr_to_dom,
      left_compo_ident', Hdh, <- Hrh, <- inv_dom,
      restr_to_dom, inv_inv...
Qed.
