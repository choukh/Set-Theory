(** Coq coding by choukh, Feb 2021 **)

Require Export ZFC.lib.Cardinal.

Lemma dom_of_op_repl :
  ∀ A G, dom {<x, G x> | x ∊ A} = A.
Proof with auto.
  intros. apply ExtAx. split; intros Hx.
  - apply domE in Hx as [y Hp].
    apply ReplAx in Hp as [α [Hα Hp]].
    apply op_iff in Hp as []; subst...
  - eapply domI. apply ReplAx. exists x. split...
Qed.

Lemma ran_of_op_repl :
  ∀ A G, ran {<x, G x> | x ∊ A} = {G x | x ∊ A}.
Proof with auto.
  intros. apply ExtAx. intros y. split; intros Hy.
  - apply ranE in Hy as [x Hp].
    apply ReplAx in Hp as [α [Hα Hp]].
    apply op_iff in Hp as []; subst. apply ReplI...
  - apply ReplAx in Hy as [x [Hx Hy]]. eapply ranI.
    apply ReplAx. exists x. split... apply op_iff...
Qed.

Lemma op_repl_is_func :
  ∀ A G, is_function {<x, G x> | x ∊ A}.
Proof with auto.
  intros. repeat split.
  - intros p Hp. apply ReplAx in Hp as [x [_ H]]; subst...
  - intros x H. rewrite <- unique_existence.
    split. rewrite dom_of_op_repl in H.
    exists (G x). apply ReplAx. exists x. split...
    intros y1 y2 H1 H2.
    apply ReplAx in H1 as [x1 [Hx1 H1]].
    apply ReplAx in H2 as [x2 [Hx2 H2]].
    apply op_iff in H1 as []; apply op_iff in H2 as []; subst...
Qed.

Lemma ap_of_op_repl :
  ∀ A G, ∀ x ∈ A, {<x, G x> | x ∊ A}[x] = G x.
Proof with auto.
  intros A G x Hx. apply func_ap. apply op_repl_is_func.
  apply ReplAx. exists x. split...
Qed.

(* 序数上的超限递归模式 *)
Module RecursionSchemaOnOrdinals.
Import TransfiniteRecursion.

Definition F := λ γ δ, Recursion δ (MemberRel δ) γ.

Local Lemma F_spec : ∀ γ, (∀ f, ∃! y, γ f y) →
  ∀δ ⋵ 𝐎𝐍, is_function (F γ δ) ∧ dom (F γ δ) = δ ∧
  ∀α ∈ δ, γ (F γ δ ↾ α) (F γ δ)[α].
Proof with auto.
  intros γ Hγ δ Hoδ.
  pose proof (recursion_spec_intro δ (MemberRel δ) γ) as [HfF [HdF HrF]]... {
    apply ord_woset...
  }
  fold (F γ δ) in HfF, HdF, HrF.
  split... split... intros α Hα.
  apply HrF in Hα as H. rewrite seg_of_ord in H...
Qed.

Local Lemma F_agree_on_smaller_partial : ∀ γ, (∀ f, ∃! y, γ f y) →
  ∀δ ⋵ 𝐎𝐍, ∀ε ⋵ 𝐎𝐍, δ ∈ ε →
  ∀α ∈ δ ∩ ε, (F γ δ)[α] = (F γ ε)[α].
Proof with eauto; try congruence.
  intros γ Hγ δ Hoδ ε Hoε Hlt α Hα.
  assert (Hsm: δ ∩ ε = δ). {
    apply ExtAx. split; intros Hx.
    - apply BInterE in Hx as []...
    - apply BInterI... eapply ord_trans...
  }
  rewrite Hsm in Hα.
  set {α ∊ δ | (F γ δ)[α] = (F γ ε)[α]} as δ'.
  replace δ with δ' in Hα. apply SepE2 in Hα... clear Hα α.
  eapply transfinite_induction. apply ord_woset...
  split. intros α Hα. apply SepE1 in Hα...
  intros α Hαδ Hseg. apply SepI...
  rewrite seg_of_ord in Hseg...
  pose proof (F_spec γ Hγ δ Hoδ) as [Hfδ [Hdδ Hγδ]].
  pose proof (F_spec γ Hγ ε Hoε) as [Hfε [Hdε Hγε]].
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
  apply Hγδ in Hαδ. apply Hγε in Hαε.
  eapply unique_existence...
Qed.

Local Lemma F_agree_on_smaller : ∀ γ, (∀ f, ∃! y, γ f y) →
  ∀δ ⋵ 𝐎𝐍, ∀ε ⋵ 𝐎𝐍, 
  ∀α ∈ δ ∩ ε, (F γ δ)[α] = (F γ ε)[α].
Proof with auto; try congruence.
  intros γ Hγ δ Hoδ ε Hoε α Hα.
  destruct (classic (δ = ε)) as [|Hnq]...
  apply ord_connected in Hnq as []...
  apply F_agree_on_smaller_partial... symmetry.
  apply F_agree_on_smaller_partial... rewrite binter_comm...
Qed.

Definition Recursion := λ γ α, (F γ α⁺)[α].

Theorem recursion_spec : ∀ γ α, (∀ f, ∃! y, γ f y) →
  α ⋵ 𝐎𝐍 → γ {<β, Recursion γ β> | β ∊ α} (Recursion γ α).
Proof with eauto.
  intros γ α Hγ Hoα. unfold Recursion.
  pose proof (F_spec γ Hγ α⁺) as [Hf [Hd Hr]]...
  assert (Hα: α ∈ α⁺). apply suc_has_n.
  apply Hr in Hα.
  replace (F γ α⁺ ↾ α) with {<β, Recursion γ β> | β ∊ α} in Hα...
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

End RecursionSchemaOnOrdinals.

Module RecursionOnOrdinals.
Import RecursionSchemaOnOrdinals.

Definition Recursion := λ F, Recursion (λ f y, y = F (ran f)).

Theorem recursion_spec : ∀ F, ∀α ⋵ 𝐎𝐍,
  Recursion F α = F {Recursion F β | β ∊ α}.
Proof with auto; try congruence.
  intros F α Hoα. unfold Recursion.
  set (λ f y, y = F (ran f)) as γ.
  assert (Hγ: ∀ f, ∃! y, γ f y). {
    intros f. rewrite <- unique_existence.
    split... exists (F (ran f))...
  }
  rewrite (recursion_spec γ α Hγ Hoα). f_equal.
  apply ran_of_op_repl.
Qed.

End RecursionOnOrdinals.

Lemma count_by_ord :
  ∀ A, countable A → ∃α ⋵ 𝐎𝐍, α ⋸ ω ∧ ∃ f, f: α ⟺ A.
Proof with auto.
  intros A Hcnt.
  apply countable_iff in Hcnt as [[n [Hn Hqn]]|Hqn];
  symmetry in Hqn; destruct Hqn as [f Hf].
  - exists n. repeat split... apply ω_is_ords... exists f...
  - exists ω. repeat split... exists f...
Qed.
