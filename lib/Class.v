(** Coq coding by choukh, Feb 2021 **)

Require Export ZFC.ZFC0.

Declare Scope Class_scope.
Open Scope Class_scope.

(* 类 *)
Notation Class := (set → Prop).

(* 类成员 *)
Definition InClass := λ x (C : Class), C x.
Notation "x ⋵ C" := (InClass x C) (at level 70) : Class_scope.
Global Hint Unfold InClass : core.

Definition all_in_class `(A : Class, P : set → Prop) : set → Prop :=
  λ x, x ⋵ A → P x.

Notation "∀ x .. y ⋵ A , P" :=
  ( all ( all_in_class A ( λ x, .. ( all ( all_in_class A ( λ y, P ))) .. )))
  (at level 200, x binder, y binder, right associativity) : Class_scope.

Definition ex_in_class `(A : Class, P : set → Prop) : set → Prop :=
  λ x, x ⋵ A ∧ P x.

Notation "∃ x .. y ⋵ A , P" :=
  ( ex ( ex_in_class A ( λ x, .. ( ex ( ex_in_class A ( λ y, P ))) .. )))
  (at level 200, x binder, y binder, right associativity) : Class_scope.

(* 能成为集合的类 *)
Definition is_set := λ C, ∃ A, ∀ x, x ∈ A ↔ x ⋵ C.

(* 子类 *)
Definition Subclass := λ C D : Class, ∀ x, C x → D x.
Notation "C ⫃ D" := (Subclass C D) (at level 70) : Class_scope.
Global Hint Unfold Subclass : core.

(* 类函数 *)
Definition class_func := λ F D R, ∀x ⋵ D, F x ⋵ R.
Notation "F :ᶜ D ⇒ R" := (class_func F D R) (at level 60) : Class_scope.

(* 类单射 *)
Definition class_injective := λ (F : set → set) D,
  ∀ x y ⋵ D, F x = F y → x = y.
Definition class_injection := λ F D R,
  F :ᶜ D ⇒ R ∧ class_injective F D.
Notation "F :ᶜ D ⇔ R" := (class_injection F D R) (at level 60) : Class_scope.

(* 类满射 *)
Definition class_surjective := λ F D R,
  ∀y ⋵ R, ∃x ⋵ D, F x = y.
Definition class_surjection := λ F D R,
  F :ᶜ D ⇒ R ∧ class_surjective F D R.
Notation "F :ᶜ D ⟹ R" := (class_surjection F D R) (at level 60) : Class_scope.

(* 类双射 *)
Definition class_bijective := λ F D R,
  class_injective F D ∧ class_surjective F D R.
Definition class_bijection := λ F D R,
  F :ᶜ D ⇒ R ∧ class_bijective F D R.
Notation "F :ᶜ D ⟺ R" := (class_bijection F D R) (at level 60) : Class_scope.
