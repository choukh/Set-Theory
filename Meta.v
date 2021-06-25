(*** Formal Construction of a Set Theory in Coq ***)
(** based on the thesis by Jonas Kaiser, November 23, 2012 **)
(** Coq coding by choukh, June 2021 **)

Require Export Coq.Unicode.Utf8_core.
Require Export Coq.Logic.Classical.

Declare Scope set_scope.
Delimit Scope set_scope with set.
Open Scope set_scope.

Parameter set : Type.

(** In是集合的成员关系。
    我们用 x ∈ y 表示 "x是y的成员"，用 x ∉ y 表示 "x不是y的成员"。 *)
Parameter In : set → set → Prop.
Notation "x ∈ y" := ( In x y) (at level 70) : set_scope.
Notation "x ∉ y" := (¬In x y) (at level 70) : set_scope.

(* 集合论中配合量词的惯例写法 *)

Notation all_in A P := (∀ x, x ∈ A → P x).
Notation "∀ x .. y ∈ A , P" :=
  (all_in A (λ x, .. (all_in A (λ y, P)) ..))
  (at level 200, x binder, right associativity) : set_scope.

Notation ex_in A P := (λ x, x ∈ A ∧ P x).
Notation "∃ x .. y ∈ A , P" :=
  (ex (ex_in A (λ x, .. (ex (ex_in A (λ y, P))) ..)))
  (at level 200, x binder, right associativity) : set_scope.

(* 关于集合的经典逻辑引理 *)

Lemma set_not_all_not_ex : ∀ A (P : set → Prop),
  ¬(∀x ∈ A, ¬P x) ↔ (∃x ∈ A, P x).
Proof.
  split; intros.
  - destruct (classic (∃x ∈ A, P x)); firstorder.
  - firstorder.
Qed.

Lemma set_not_all_ex_not : ∀ A (P : set → Prop),
  ¬(∀x ∈ A, P x) ↔ (∃x ∈ A, ¬P x).
Proof.
  intros. pose proof (set_not_all_not_ex A (λ x, ¬P x)).
  simpl in H. rewrite <- H. clear H.
  split; intros.
  - intros H1. apply H. intros x Hx. apply H1 in Hx.
    apply NNPP in Hx. apply Hx.
  - firstorder.
Qed.

Notation "'∃' ! x .. y , P" :=
  (ex (unique (λ x, .. (ex (unique (λ y, P))) ..)))
  (at level 200, x binder, right associativity,
   format "'[' '∃' ! '/ ' x .. y , '/ ' P ']'") : type_scope.

(* 经典明确描述 *)
Axiom classical_definite_description : ∀ (A : Type) (P : A → Prop),
  inhabited A → { x | (∃! x, P x) → P x }.

Definition iota := λ {A} i P, proj1_sig (classical_definite_description A P i).
Definition iota_spec := λ {A} i P, proj2_sig (classical_definite_description A P i).

(** 排中律是信息丰富的 **)
Theorem informative_excluded_middle : ∀ P : Prop, P + ¬P.
Proof.
  intros P.
  assert (i: inhabited (P + ¬P)). {
    destruct (classic P).
    - apply inhabits. now apply inl.
    - apply inhabits. now apply inr.
  }
  apply (iota i (λ _, True)).
Qed.
Notation ixm := informative_excluded_middle.

(** 类型的居留性是可判定的 **)
Theorem decidable_inhabitance_of_type : ∀ T : Type, T + (T → False).
Proof.
  intros T.
  destruct (ixm (inhabited T)) as [i|i].
  - left. apply (iota i (λ _, True)).
  - right. intros t. now apply i.
Qed.
Notation dit := decidable_inhabitance_of_type.
