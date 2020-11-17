(** Solutions to "Elements of Set Theory" Chapter 6 Part 1 **)
(** Coq coding by choukh, Sep 2020 **)

Require Export ZFC.EST6_2.
Require Export ZFC.lib.FiniteFacts.

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

(* 有限集的并仍是有限集（非算术证明） *)
Example ex6_8 : ∀ A B, finite A → finite B → finite (A ∪ B).
Proof with eauto.
  intros * Hfa Hfb. rewrite <- ex2_11_2.
  assert (Hfc: finite (B - A)). {
    apply (subset_of_finite_is_finite _ B)...
  }
  assert (Hdj: disjoint A (B - A)) by apply binter_comp_empty.
  remember (B - A) as C. clear HeqC Hfb B.
  destruct Hfc as [n [Hn Hc]].
  generalize dependent C. generalize dependent A.
  set {n ∊ ω | λ n, ∀ A, finite A →
    ∀ C, C ≈ n → disjoint A C → finite (A ∪ C)} as N.
  ω_induction N Hn; intros A Hfa C HC Hdj.
  - apply eqnum_empty in HC. subst C. rewrite bunion_empty...
  - apply set_eqnum_suc_nonempty in HC as Hi...
    destruct Hi as [c Hc].
    apply split_one_element in Hc.
    rewrite Hc in HC. rewrite bunion_comm in Hc.
    rewrite Hc, bunion_assoc. apply IH.
    + apply finite_set_adding_one_still_finite...
    + apply finite_set_remove_one_element...
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
  - apply set_eqnum_suc_nonempty in HB as Hi...
    destruct Hi as [b Hb].
    apply split_one_element in Hb.
    rewrite Hb in HB. rewrite bunion_comm in Hb.
    rewrite Hb, ex3_54_b. apply ex6_8.
    + destruct Hfa as [k [Hk HA]].
      exists k. split... rewrite <- eqnum_cprod_single...
    + apply IH... apply finite_set_remove_one_element...
Qed.

(* ex6_10 ex6_11 see EST6_2.v *)

Example ex6_12_a : ∀ K L, K ∪ L = L ∪ K.
Proof. exact bunion_comm. Qed.

Example ex6_12_b : ∀ K L M, K ∪ (L ∪ M) = (K ∪ L) ∪ M.
Proof. exact bunion_assoc. Qed.

Example ex6_12_c : ∀ K L M, K × (L ∪ M) = (K × L) ∪ (K × M).
Proof. exact ex3_2_a. Qed.

(* ex6_13 *)
(* 有限个有限集的并集仍是有限集 *)
Lemma union_finite : ∀ A, finite A → (∀a ∈ A, finite a) → finite ⋃A.
Proof with eauto.
  intros A [n [Hn HA]].
  generalize dependent A.
  set {n ∊ ω | λ n, ∀ A, A ≈ n → (∀a ∈ A, finite a) → finite ⋃ A} as N.
  ω_induction N Hn; intros A HA Hfa.
  - apply eqnum_empty in HA. subst A. rewrite union_empty...
  - apply set_eqnum_suc_nonempty in HA as Hi...
    destruct Hi as [a Ha].
    apply split_one_element in Ha as HeqA.
    rewrite HeqA in HA. rewrite bunion_comm in HeqA.
    rewrite HeqA, ex2_21. apply ex6_8.
    + rewrite union_single. apply Hfa...
    + apply IH. apply finite_set_remove_one_element...
      intros b Hb. apply Hfa. apply SepE in Hb as []...
Qed.

(** ex6_14 **)

(* 全排列 *)
Definition Permutation : set → set := λ A,
  {f ∊ A ⟶ A | λ f, f: A ⟺ A}.
(* 基数阶乘 *)
Definition CardFactorial : set → set := λ 𝜅,
  |Permutation 𝜅|.
Notation "𝜅 !" := (CardFactorial 𝜅) (at level 60) : Card_scope.

Lemma permutation_iff : ∀ f A, f: A ⟺ A ↔ f ∈ Permutation A.
Proof with auto.
  split; intros H.
  - apply SepI... apply ArrowI. apply bijection_is_func...
  - apply SepE in H as []...
Qed.

(* ex6_14: 基数阶乘良定义 *)
Theorem cardFactorial_well_defined : ∀ A B, |A| = |B| → A! = B!.
Proof with eauto; try congruence.
  intros. apply CardAx1.
  apply CardAx1 in H as [g Hg].
  set (λ f, g ∘ f ∘ g⁻¹) as ℱ.
  set (Func (Permutation A) (Permutation B) ℱ) as F.
  exists F. apply meta_bijective.
  - intros f Hf.
    apply permutation_iff.
    apply permutation_iff in Hf.
    eapply bijection_transform...
  - intros f1 Hf1 f2 Hf2 Heq. destruct Hg as [Hig [Hdg _]].
    apply permutation_iff in Hf1 as [[[Hrel1 _] _] [Hdf1 Hrf1]].
    apply permutation_iff in Hf2 as [[[Hrel2 _] _] [Hdf2 Hrf2]].
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
    exists f. split. apply permutation_iff...
    destruct Hg as [[Hfg _] [_ Hrg]].
    destruct Hh as [[[Hrelh _] _] [Hdh Hrh]].
    unfold ℱ, f. rewrite
      compo_assoc, compo_assoc, compo_inv_ran_ident,
      compo_assoc, <- compo_assoc, compo_inv_ran_ident,
      right_compo_ident, Hrg, <- Hdh, restr_to_dom,
      left_compo_ident', Hdh, <- Hrh, <- inv_dom,
      restr_to_dom, inv_inv...
Qed.
