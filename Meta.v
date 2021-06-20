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

Definition all_in := λ A (P : set → Prop) x, x ∈ A → P x.
Notation "∀ x .. y ∈ A , P" :=
  (all (all_in A (λ x, .. (all (all_in A (λ y, P))) ..)))
  (at level 200, x binder, right associativity) : set_scope.

Definition ex_in := λ A (P : set → Prop) x, x ∈ A ∧ P x.
Notation "∃ x .. y ∈ A , P" :=
  (ex (ex_in A (λ x, .. (ex (ex_in A (λ y, P))) ..)))
  (at level 200, x binder, right associativity) : set_scope.

(* 关于集合的经典逻辑引理 *)

Lemma set_not_all_not_ex : ∀ A P, ¬(∀x ∈ A, ¬P x) ↔ (∃x ∈ A, P x).
Proof.
  split; intros.
  - destruct (classic (∃x ∈ A, P x)); firstorder.
  - firstorder.
Qed.

Lemma set_not_all_ex_not : ∀ A P, ¬(∀x ∈ A, P x) ↔ (∃x ∈ A, ¬P x).
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
Definition informative_excluded_middle :=
  ∀ P : Prop, P + ¬P.

Theorem ixm : informative_excluded_middle.
Proof.
  intros P.
  assert (H := classic P).
  assert (I: inhabited (P + ¬P)). {
    destruct H.
    - apply inhabits. apply inl. apply H.
    - apply inhabits. apply inr. apply H.
  }
  apply (iota I (λ _, True)).
Qed.

(** 类型的居留性是可判定的 **)
Definition decidable_inhabitance_of_type :=
  ∀ T : Type, T + (T → False).

Theorem dit : decidable_inhabitance_of_type.
Proof.
  intros T.
  destruct (ixm (inhabited T)) as [I|I].
  - left. apply (iota I (λ _, True)).
  - right. intros t. apply I. apply inhabits. apply t.
Qed.
