(** Solutions to "Elements of Set Theory" Chapter 6 **)
(** Coq coding by choukh, June 2020 **)

Require Export ZFC.EST6_2.

(* ch6_3 f(x) = 1/x *)
(* ch6_4 0 ↦ 1/2 ↦ 1/4 ... *)
(* ch6_5 see EST6_1 eqnum_refl symm tran *)

(* 同一基数的所有集合不能构成一个集合 *)
Example ch6_6 : ∀ 𝜅, is_card 𝜅 → ⦿ 𝜅 → ¬∃ A, ∀ x, |x| = 𝜅 → x ∈ A.
Proof with auto.
  intros 𝜅 H𝜅 Hi [A Hcd].
  apply no_set_of_all_set. exists (⋃A).
  intros a. apply UnionAx.
  pose proof (any_set_in_set_with_any_nonzero_card a 𝜅 H𝜅 Hi)
    as [K [Heq Ha]]. exists K. split...
Qed.

(* 有限集到自身的映射是单射当且仅当该映射是满射 *)
Example ch6_7 : ∀ A f, finite A → f: A ⇒ A →
  injective f ↔ ran f = A.
Proof with auto.
  intros A f [n [Hn [g Hg]]] Hf.
  destruct Hf as [Hff [Hdf Hrf]]. assert (Hg' := Hg).
  destruct Hg' as [Hig [Hdg Hrg]]. assert (Hig' := Hig).
  destruct Hig' as [Hfg Hsg].
  assert (Hig': injective g⁻¹) by (apply inv_injective; auto).
  split; intros H.
  - assert (Higf: injective (g ∘ f)) by (apply ch3_17_b; auto).
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
    apply compo_inj... apply compo_inj...
    rewrite compo_assoc, compo_assoc, compo_inv_dom_ident,
      compo_assoc, Hdg, <- Hdf, right_compo_ident, restr_to_dom,
      <- compo_assoc, compo_inv_dom_ident, left_compo_ident',
      Hdg, <- H, <- inv_dom, restr_to_dom, inv_inv...
Qed.

(* 有限集的并仍是有限集（非算术证明） *)
(* Example ch6_8 : ∀ A B, finite A → finite B → finite (A ∪ B).
Proof with auto.
  intros A B Hfa Hfb.
  destruct (classic (finite (A ∪ B)))... exfalso. *)

