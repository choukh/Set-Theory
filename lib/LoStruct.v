(** Coq coding by choukh, Mar 2021 **)

Require Import Relation_Definitions.
Require Import RelationClasses.
Require Import PropExtensionality.
Require Export ZFC.EST7_3.

Declare Scope LoStruct_scope.
Delimit Scope LoStruct_scope with lo.
Open Scope LoStruct_scope.

Record LoStruct : Type := constr {
  A : set;
  R : set;
  lo : loset A R;
}.
Global Hint Immediate lo : core.

Lemma empty_loset : loset ∅ ∅.
Proof with auto.
  repeat split.
  - intros x H. exfalso0.
  - intros x y z H. exfalso0.
  - intros x H. exfalso0.
Qed.

Notation ø := (constr ∅ ∅ empty_loset).
Notation 𝛚 := (constr ω Lt (proj1 Lt_wellOrder)).

Lemma eq_intro : ∀ S T, A S = A T → R S = R T → S = T.
Proof.
  intros S T HA HR. destruct S. destruct T.
  simpl in *. subst. f_equal. apply proof_irrelevance.
Qed.

(* 序嵌入双射 *)
Definition order_embedding_bijection := λ f S T, f: A S ⟺ A T ∧
  ∀ x y ∈ A S, (x <ᵣ y) (R S) ↔ (f[x] <ᵣ f[y]) (R T).
Notation "f :ₒₑ S ⟺ T" := (order_embedding_bijection f S T)
  (at level 70) : LoStruct_scope.

Definition isomorphic : relation LoStruct :=
  λ S T, ∃ f, f :ₒₑ S ⟺ T.

Notation "S ≅ T" := ( isomorphic S T) (at level 60) : LoStruct_scope.
Notation "S ≇ T" := (¬isomorphic S T) (at level 60) : LoStruct_scope.

Definition SubStruct := λ S T, A S ⊆ A T ∧ R S = R T ⥏ A S.
Notation "S ⊑ T" := (SubStruct S T) (at level 70) : LoStruct_scope.

Local Lemma loset_is_binRel : ∀ A R, loset A R → is_binRel R A.
Proof. intros. apply H. Qed.

Local Definition br := λ S, loset_is_binRel (A S) (R S) (lo S).
Definition parent := λ S, OrderedStruct.constr (A S) (R S) (br S).

Lemma parent_iso : ∀ S T,
  S ≅ T ↔ OrderedStruct.isomorphic (parent S) (parent T).
Proof.
  split; intros [f [Hf Hoe]]; exists f; split; auto.
Qed.

Lemma parent_lo : ∀ S, OrderedStruct.lo (parent S).
Proof. intros. apply lo. Qed.

Theorem iso_refl : Reflexive isomorphic.
Proof.
  intros S. apply parent_iso. apply OrderedStruct.iso_refl.
Qed.

Theorem iso_symm : Symmetric isomorphic.
Proof.
  intros S T H. rewrite parent_iso in H. apply parent_iso.
  apply OrderedStruct.iso_symm; auto.
Qed.

Theorem iso_tran : Transitive isomorphic.
Proof.
  intros S T U H1 H2. rewrite parent_iso in H1, H2.
  apply parent_iso. eapply OrderedStruct.iso_tran; eauto.
Qed.

Theorem iso_equiv : Equivalence isomorphic.
Proof.
  split. apply iso_refl. apply iso_symm. apply iso_tran.
Qed.
Existing Instance iso_equiv.
