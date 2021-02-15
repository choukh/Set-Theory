(** Coq coding by choukh, Feb 2021 **)

Require Export ZFC.lib.Cardinal.

(* 序数上的超限递归模式 *)
Module RecursionSchemaOnOrdinals.
Import TransfiniteRecursion.

Definition F := λ γ δ, constr δ (MemberRel δ) γ.

Local Lemma F_spec : ∀ γ δ,
  (∀ f, ∃! y, γ f y) → is_ord δ →
  is_function (F γ δ) ∧ dom (F γ δ) = δ ∧
  ∀α ∈ δ, γ (F γ δ ↾ α) (F γ δ)[α].
Proof with auto.
  intros γ δ Hoδ Hγ.
  pose proof (spec_intro δ (MemberRel δ) γ) as [HfF [HdF HrF]]... {
    apply ord_woset...
  }
  fold (F γ δ) in HfF, HdF, HrF.
  split... split... intros α Hα.
  apply HrF in Hα as H. rewrite seg_of_ord in H...
Qed.

Local Lemma F_agree_on_smaller_partial : ∀ γ δ ε,
  (∀ f, ∃! y, γ f y) →
  δ ∈ ε → is_ord δ → is_ord ε →
  ∀α ∈ δ ∩ ε, (F γ δ)[α] = (F γ ε)[α].
Proof with eauto; try congruence.
  intros γ δ ε Hγ Hlt Hoδ Hoε α Hα.
  assert (Hsm: δ ∩ ε = δ). {
    apply ExtAx. split; intros Hx.
    - apply BInterE in Hx as []...
    - apply BInterI... eapply ord_trans...
  }
  rewrite Hsm in Hα.
  set {α ∊ δ | λ α, (F γ δ)[α] = (F γ ε)[α]} as δ'.
  replace δ with δ' in Hα. apply SepE2 in Hα... clear Hα α.
  eapply transfinite_induction. apply ord_woset...
  split. intros α Hα. apply SepE1 in Hα...
  intros α Hαδ Hseg. apply SepI...
  rewrite seg_of_ord in Hseg...
  pose proof (F_spec γ δ Hγ Hoδ) as [Hfδ [Hdδ Hγδ]].
  pose proof (F_spec γ ε Hγ Hoε) as [Hfε [Hdε Hγε]].
  assert (Hαε: α ∈ ε). eapply ord_trans...
  assert (Heqf: F γ δ ↾ α = F γ ε ↾ α). {
    apply ExtAx. intros p. split; intros Hp.
    - apply restrE1 in Hp as [a [b [Ha [Hp H1]]]]. subst p.
      apply Hseg in Ha as H. apply SepE2 in H.
      apply restrI... apply func_ap in Hp...
      apply func_point... eapply ord_trans...
    - apply restrE1 in Hp as [a [b [Ha [Hp H1]]]]. subst p.
      apply Hseg in Ha as H. apply SepE2 in H.
      apply restrI... apply func_ap in Hp...
      apply func_point... eapply ord_trans...
  }
  apply Hγδ in Hαδ.
  apply Hγε in Hαε. eapply Hγ...
Qed.

Local Lemma F_agree_on_smaller : ∀ γ δ ε,
  (∀ f, ∃! y, γ f y) →
  is_ord δ → is_ord ε →
  ∀α ∈ δ ∩ ε, (F γ δ)[α] = (F γ ε)[α].
Proof with auto; try congruence.
  intros γ δ ε Hγ Hoδ Hoε α Hα.
  destruct (classic (δ = ε)) as [|Hnq]...
  apply ord_connected in Hnq as []...
  apply (F_agree_on_smaller_partial γ δ ε)... symmetry.
  apply (F_agree_on_smaller_partial γ ε δ)... rewrite binter_comm...
Qed.

Definition Recursion := λ γ α, (F γ α⁺)[α].

Theorem recursion_spec : ∀ γ α, (∀ f, ∃! y, γ f y) →
  is_ord α → γ {λ β, <β, Recursion γ β> | β ∊ α} (Recursion γ α).
Proof with eauto.
  intros γ α Hγ Hoα. unfold Recursion.
  pose proof (F_spec γ α⁺) as [Hf [Hd Hr]]...
  assert (Hα: α ∈ α⁺). apply suc_has_n.
  apply Hr in Hα.
  replace (F γ α⁺ ↾ α) with {λ β, <β, Recursion γ β> | β ∊ α} in Hα...
  apply ExtAx. split; intros Hx.
  - apply ReplAx in Hx as [β [Hβ Hx]]. subst x.
    assert (β ∈ α⁺). apply BUnionI1...
    apply restrI... eapply func_point... rewrite Hd...
    apply F_agree_on_smaller... apply ord_suc_is_ord.
    eapply ord_is_ords... apply BInterI...
  - apply restrE1 in Hx as [a [b [Ha [Hp Heq]]]]. subst x.
    assert (a ∈ α⁺). apply BUnionI1...
    apply ReplAx. exists a. split... apply op_iff. split...
    apply func_ap in Hp... subst b. apply F_agree_on_smaller...
    apply ord_suc_is_ord. eapply ord_is_ords... apply BInterI...
Qed.

Lemma ran_of_op_repl :
  ∀ A G, ran {λ x, <x, G x> | x ∊ A} = {G | x ∊ A}.
Proof with auto.
  intros. apply ExtAx. intros y. split; intros Hy.
  - apply ranE in Hy as [x Hp].
    apply ReplAx in Hp as [α [Hα Hp]].
    apply op_iff in Hp as []; subst. apply ReplI...
  - apply ReplAx in Hy as [x [Hx Hy]]. eapply ranI.
    apply ReplAx. exists x. split... apply op_iff...
Qed.

End RecursionSchemaOnOrdinals.

Module RecursionOnOrdinals.
Import RecursionSchemaOnOrdinals.

Definition Recursion := λ F, Recursion (λ f y, y = F (ran f)).

Theorem recursion_spec : ∀ F α, is_ord α → 
  Recursion F α = F {Recursion F | β ∊ α}.
Proof with auto; try congruence.
  intros F α Hoα. unfold Recursion.
  set (λ f y, y = F (ran f)) as γ.
  assert (Hγ: ∀ f, ∃! y, γ f y). {
    intros f. split... exists (F (ran f))...
  }
  rewrite (recursion_spec γ α Hγ Hoα). f_equal.
  apply ran_of_op_repl.
Qed.

End RecursionOnOrdinals.
