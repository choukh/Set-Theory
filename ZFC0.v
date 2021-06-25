(*** Formal Construction of a Set Theory in Coq ***)
(** based on the thesis by Jonas Kaiser, November 23, 2012 **)
(** Coq coding by choukh, April 2020 **)

Require Export ZFC.Meta.

(**=== 公理1: 外延公理 ===**)
(* 两个集合相等当且仅当它们包含相同的成员 *)
Axiom ExtAx : ∀ A B, (∀ x, x ∈ A ↔ x ∈ B) → A = B.

Lemma ExtNI : ∀ A B, (∃x ∈ B, x ∉ A) → A ≠ B.
Proof.
  intros A B [x [Hx Hx']] Hext. apply Hx'. congruence.
Qed.

(** Sub是集合的子集关系。
    我们用 A ⊆ B 表示 "A是B的子集"，用 A ⊈ B 表示 "A不是B的子集"。 *)
Definition Sub := λ A B, ∀x ∈ A, x ∈ B.
Notation "A ⊆ B" := ( Sub A B) (at level 70) : set_scope.
Notation "A ⊈ B" := (¬Sub A B) (at level 70) : set_scope.

(* 子集关系是自反的 *)
Lemma sub_refl : ∀ A, A ⊆ A.
Proof. easy. Qed.
Global Hint Immediate sub_refl : core.

(* 子集关系是传递的 *)
Lemma sub_tran : ∀ A B C, A ⊆ B → B ⊆ C → A ⊆ C.
Proof. firstorder. Qed.

(* 子集关系是反对称的 *)
Lemma sub_antisym: ∀ A B, A ⊆ B → B ⊆ A → A = B.
Proof.
  intros A B H1 H2. apply ExtAx.
  split. apply H1. apply H2.
Qed.

(* 链：子集关系下的全序集 *)
Definition is_chain := λ 𝒜, ∀ A B ∈ 𝒜, A ⊆ B ∨ B ⊆ A.

(**=== 公理2: 空集公理 ===**)
(* 空集公理保证了集合类型是居留的，即存在最底层的集合，
  任何其他集合都不是它的成员，这样的集合就是空集。 *)
Parameter Empty : set.
Notation "∅" := Empty : set_scope.
Axiom EmptyAx : ∀ x, x ∉ ∅.

Ltac exfalso0 := exfalso; eapply EmptyAx; eassumption.

(* 集合的非空性 (类似于类型的居留性) *)
Definition nonempty := λ A, ∃ x, x ∈ A.
Notation "⦿ x" := (nonempty x) (at level 45) : set_scope.

(* 空集非居留 *)
Fact empty_is_not_inhabited : ¬ ⦿ ∅.
Proof.
  unfold nonempty, not. intros.
  destruct H as [x H].
  eapply EmptyAx. apply H.
Qed.

(* Introduction rule of empty set (空集的介入) *)
Lemma EmptyI : ∀ A, (∀ x, x ∉ A) → A = ∅.
Proof.
  intros A E. apply ExtAx.
  split; intros H.
  - exfalso. eapply E. apply H.
  - exfalso0.
Qed.

(* Elimination rule of empty set (空集的除去) *)
Lemma EmptyE : ∀ A, A = ∅ → (∀ x, x ∉ A).
Proof. intros. subst A. apply EmptyAx. Qed.

(* 居留集不等于空集 *)
Lemma EmptyNI : ∀ A, ⦿ A → A ≠ ∅.
Proof.
  intros A Hi H0.
  destruct Hi as [x Hx].
  eapply EmptyAx. rewrite H0 in Hx. apply Hx.
Qed.

(* 不等于空集的集合是居留的 *)
Lemma EmptyNE : ∀ A, A ≠ ∅ → ⦿ A.
Proof.
  intros. pose proof (classic (⦿ A)).
  destruct H0.
  - apply H0.
  - unfold not in H0.
    assert (∀ x, x ∉ A).
    + intros x H1. apply H0.
      exists x. apply H1.
    + apply EmptyI in H1.
      rewrite H1 in H. exfalso. apply H. reflexivity.
Qed.

(* 空集唯一 *)
Fact emtpy_is_unique : ∀ A Y, (∀ x, x ∉ A) → (∀ y, y ∉ Y) → A = Y.
Proof.
  intros.
  apply EmptyI in H.
  apply EmptyI in H0.
  subst. reflexivity.
Qed.

(* 空集是任意集合的子集 *)
Lemma empty_sub_all : ∀ A, ∅ ⊆ A.
Proof. intros A x Hx. exfalso0. Qed.

(* 集合是空集的子集当且仅当该集合是空集 *)
Lemma sub_empty : ∀ A, A ⊆ ∅ ↔ A = ∅.
Proof.
  split; intros.
  - apply EmptyI. intros x Hx. apply H in Hx. exfalso0.
  - subst. apply empty_sub_all.
Qed.

(* 任意集合要么是空集要么是居留的 *)
Lemma empty_or_not : ∀ A, A = ∅ ∨ ⦿A.
Proof.
  intros. destruct (classic (A = ∅)).
  - left. apply H.
  - right. apply EmptyNE. apply H.  
Qed.

(* 集合明确描述 *)
Theorem set_definite_description : ∀ P : set → Prop,
  { x | (∃! x, P x) → P x }.
Proof.
  intros. exact (classical_definite_description set P (inhabits ∅)).
Qed.
Definition describe := λ P, proj1_sig (set_definite_description P).
Definition desc_spec := λ P, proj2_sig (set_definite_description P).

(**=== 公理3: 并集公理 ===**)
(* 给定集合X，存在X的并集⋃X，它的成员都是X的某个成员的成员 *)
Parameter Union : set → set.
Notation "⋃ A" := (Union A) (at level 9, right associativity) : set_scope.
Axiom UnionAx : ∀ a A, a ∈ ⋃ A ↔ ∃x ∈ A, a ∈ x.

Lemma UnionI : ∀ A, ∀x ∈ A, ∀a ∈ x, a ∈ ⋃ A.
Proof.
  intros A x Hx a Ha. apply UnionAx.
  exists x. split; assumption.
Qed.

(* 空集的并集是空集 *)
Fact union_empty : ⋃∅ = ∅.
Proof.
  apply ExtAx. split.
  - intros. apply UnionAx in H as [a [H _]]. exfalso0.
  - intros. exfalso0.
Qed.

(**=== 公理4: 幂集公理 ===**)
(* 存在幂集，它是给定集合的所有子集组成的集合 *)
Parameter Power : set → set.
Notation "'𝒫' A" := (Power A) (at level 9, right associativity) : set_scope.
Axiom PowerAx : ∀ A Y, Y ∈ 𝒫 A ↔ Y ⊆ A.

(* 空集是任意集合的幂集的成员 *)
Lemma empty_in_all_power: ∀ A, ∅ ∈ 𝒫 A.
Proof. intros. apply PowerAx. apply empty_sub_all. Qed.

(* 任意集合都是自身的幂集的成员 *)
Lemma all_in_its_power: ∀ A, A ∈ 𝒫 A.
Proof. intros. apply PowerAx. apply sub_refl. Qed.

(* 若集合是空集的幂集的成员，那么这个集合是空集 *)
Example only_empty_in_power_empty: ∀ x, x ∈ 𝒫 ∅ → x = ∅.
Proof.
  intros.
  apply PowerAx in H.
  unfold Sub in H.
  apply ExtAx. split; intros.
  - apply H. apply H0.
  - exfalso0.
Qed.

(**=== 公理5: 替代公理（模式） ===**)
(* 给定二元谓词P，如果对任意集合x有唯一集合y使得P x y成立，
  那么给定集合X，存在集合Y，对于Y的任意成员y都存在X中元素x使得P x y成立 *)
Parameter ϕ_Repl : (set → set → Prop) → set → set.
Axiom ϕ_ReplAx : ∀ (P : set → set → Prop) A,
  (∀ x ∈ A, ∃! y, P x y) →
  ∀ y, y ∈ ϕ_Repl P A ↔ ∃x ∈ A, P x y.

Definition Repl : (set → set) → set → set := λ F A,
  ϕ_Repl (λ x y, F x = y) A.
Notation "{ F | x ∊ A }" := (Repl (λ x, F x) A) : set_scope.

Theorem ReplAx : ∀ y F A, y ∈ {F | x ∊ A} ↔ ∃x ∈ A, F x = y.
Proof with auto.
  intros. split.
  - intros Hy. apply ϕ_ReplAx in Hy...
    intros x Hx. exists (F x). split...
  - intros [x [Hx Heq]]. apply ϕ_ReplAx.
    + intros a Ha. exists (F a). split...
    + exists x. split...
Qed.

Lemma ReplI : ∀ A F, ∀x ∈ A, F x ∈ {F | x ∊ A}.
Proof.
  intros A F x Hx. apply ReplAx.
  exists x. split. apply Hx. reflexivity.
Qed.

Lemma repl_ext : ∀ G F A, (∀a ∈ A, F a = G a) →
  {F | a ∊ A} = {G | a ∊ A}.
Proof with auto.
  intros. apply ExtAx. split; intros Hx.
  - apply ReplAx in Hx as [y [Hy Hx]].
    apply ReplAx. exists y. split... rewrite <- H...
  - apply ReplAx in Hx as [y [Hy Hx]].
    apply ReplAx. exists y. split... rewrite H...
Qed.

(* 空集的替代是空集 *)
Fact repl_empty : ∀ F, {F | x ∊ ∅} = ∅.
Proof.
  intros. apply EmptyI. intros x H.
  apply ReplAx in H as [y [H _]]. exfalso0.
Qed.

(* 若某集合的替代是空集，那么该集合是空集 *)
Fact repl_eq_empty : ∀ F A, {F | x ∊ A} = ∅ → A = ∅.
Proof.
  intros. apply sub_empty. intros x Hx.
  eapply ReplI in Hx. rewrite H in Hx. exfalso0.
Qed.
