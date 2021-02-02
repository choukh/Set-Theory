(** Solutions to "Elements of Set Theory" Chapter 7 Part 1 **)
(** Coq coding by choukh, Dec 2020 **)

Require Import PropExtensionality.
Require Import ZFC.EST7_4.
Require Import ZFC.lib.FuncFacts.
Import WOStruct.

Declare Scope Ord_scope.
Delimit Scope Ord_scope with ord.
Open Scope Ord_scope.

Record Ord : Type := constr {
  s : set;
  cond : is_ord s;
}.
Hint Immediate cond : core.

Lemma eq_intro : ∀ α β, s α = s β → α = β.
Proof.
  intros α β Heq. destruct α. destruct β.
  simpl in Heq. subst. f_equal. apply proof_irrelevance.
Qed.

Definition Seg := λ t α (H: t ∈ s α),
  constr t (ord_is_ords (s α) (cond α) t H).

Definition Suc := λ α, constr (s α)⁺ (ord_suc_is_ord _ (cond _)).
Notation "α ⁺" := (Suc α) : Ord_scope.

Notation "α <ₒ β" := (s α ∈ s β) (at level 70) : Ord_scope.
Notation "α ≤ β" := (s α ⋸ s β) (at level 70) : Ord_scope.

Definition OrdStruct := λ α,
  WOStruct.constr (s α) (MemberRel (s α)) (ord_woset _ (cond _)).

Definition Recursion := λ α γ,
  (Recursion (OrdStruct α) γ).

Definition recrusion_spec := λ α γ F,
  is_function F ∧ dom F = s α ∧
  ∀t ∈ s α, γ (F ↾ seg t (MemberRel (s α))) F[t].

Lemma recursion_spec_intro : ∀ α γ, (∀ x, ∃! y, γ x y) →
  recrusion_spec α γ (Recursion α γ).
Proof. intros. apply recrusion_spec_intro; auto. Qed.

Module OrdRecursion.

Definition γ := λ F f y, y = F[ran f].
Definition E := λ F α, (Recursion α (γ F)).
Definition OrdRecursion := λ F α, (E F α⁺)[s α].

Lemma e_spec : ∀ F α, is_function F →
  recrusion_spec α (γ F) (E F α).
Proof.
  intros. apply recrusion_spec_intro.
  intros f. unfold γ. split. exists (F[ran f]). auto. congruence.
Qed.

Lemma e_empty : ∀ F α, is_function F → s α = ∅ → E F α = ∅.
Proof.
  intros. destruct (e_spec F α) as [Hf [Hd _]]; auto.
  apply empty_dom; congruence.
Qed.

Lemma e_ap : ∀ F α, is_function F → 
  ∀t ∈ s α, (E F α)[t] = F[(E F α)⟦t⟧].
Proof with auto.
  intros F α HfF t Ht. destruct (e_spec F α) as [_ [_ Hr]]...
  apply Hr in Ht as Heq. rewrite Heq. rewrite seg_of_ord...
Qed.

Lemma image_eq : ∀ F α, is_function F → 
  ∀t ∈ s α, (E F α)⟦t⟧ = {ap (E F α) | x ∊ t}.
Proof with eauto.
  intros F α HfF t Ht.
  destruct (e_spec F α) as [Hf [Hd _]]...
  apply ExtAx. intros y. split; intros Hy.
  - apply ranE in Hy as [x Hp]. apply restrE2 in Hp as [Hp Hx].
    apply ReplAx. exists x. split... apply func_ap in Hp...
  - apply ReplAx in Hy as [x [Hx Hap]].
    apply (ranI _ x). apply restrI... apply func_point...
    rewrite Hd. eapply ord_trans...
Qed.

End OrdRecursion.
