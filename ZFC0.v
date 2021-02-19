(*** Formal Construction of a Set Theory in Coq ***)
(** based on the thesis by Jonas Kaiser, November 23, 2012 **)
(** Coq coding by choukh, April 2020 **)

Require Export Coq.Unicode.Utf8_core.
Require Export Coq.Logic.Classical.
Require Export Coq.Logic.Epsilon.

Set Implicit Arguments.

Notation "⊤" := True.
Notation "⊥" := False.

(*** 元理论 ***)

(** 排中律 **)
Print classic.
(* Axiom classic : ∀ P : Prop, P ∨ ¬ P *)

(** 和类型 **)
(* 类似于逻辑或[or]，和类型封装了类型A或B *)
Print sum.
(* Inductive sum (A B : Type) : Type :=
    | inl : A → A + B
    | inr : B → A + B *)

(** 存在量化类型 **)
(* 类似于存在量化命题[ex]，Σ类型封装了"存在x使P成立"的证据。 *)
Print sig.
(* Inductive sig (A : Type) (P : A → Prop) : Type :=
    exist : ∀ x : A, P x → {x : A | P x} *)

(** 类型居留谓词 **)
(* 对于任意类型A，如果存在具体的A，则称类型A被居留。 *)
Print inhabited.
(* Inductive inhabited (A : Type) : Prop :=
    inhabits : A → inhabited A *)

(** 希尔伯特ε算子 **)
(* 可以导出ZFC选择公理(见ZFC3) *)

(* 存在ε算子，对于任意类型A和该类型上的任意谓词P，只要A是被居留的，
  用ε算子就可以得到A上的某个x，它使命题P成立，只要存在A上的某个y使P成立。 *)
Print epsilon_statement.
(* Axiom epsilon_statement : ∀ (A : Type) (P : A → Prop),
    inhabited A → {x : A | (∃ y, P y) → P x}. *)

(* 用ε算子可以得到εAP，它是在A上任意选择的一个使P成立的a。
  若这样的a不存在，则εAP为任意A上的a *)
Print epsilon.
(* Definition epsilon (A : Type) (i : inhabited A) (P : A → Prop) : A :=
  proj1_sig (epsilon_statement P i). *)

(* 用ε_spec可以得到εAP满足P的证据，只要存在一个A上的a使P成立。
  若这样的a不存在，则可以证明P(εAP)不成立 *)
Print epsilon_spec.
(* Definition epsilon_spec (A : Type) (i : inhabited A) (P : A → Prop) :
  (∃ x, P x) → P (epsilon i P) :=
  proj2_sig (epsilon_statement P i). *)

(** 排中律是信息丰富的 **)
Definition informative_excluded_middle : Type :=
  ∀ P : Prop, P + ¬P.

Theorem ixm : informative_excluded_middle.
Proof.
  unfold informative_excluded_middle. intros P.
  assert (H := classic P).
  assert (I: inhabited (P + ¬P)). {
    destruct H.
    - apply inhabits. apply inl. apply H.
    - apply inhabits. apply inr. apply H.
  }
  apply (epsilon I (λ _, ⊤)).
Qed.

(** 类型的居留性是可判定的 **)
Definition decidable_inhabitance_of_type : Type :=
  ∀ T : Type, T + (T → ⊥).

Theorem dit : decidable_inhabitance_of_type.
Proof.
  unfold decidable_inhabitance_of_type. intros T.
  destruct (ixm (inhabited T)) as [I|I].
  - left. apply (epsilon I (λ _, ⊤)).
  - right. intros t. apply I. apply inhabits. apply t.
Qed.

(*** Zermelo–Fraenkel集合论公理 ***)

Parameter set : Type.

(** In是集合的成员关系。
    我们用 x ∈ y 表示 "x是y的成员"，用 x ∉ y 表示 "x不是y的成员"。 *)
Parameter In : set → set → Prop.

Notation "x ∈ y" := ( In x y) (at level 70).
Notation "x ∉ y" := (¬In x y) (at level 70).

(* 集合论中配合量词的惯例写法 *)

Definition all_in `(A : set, P : set → Prop) : set → Prop :=
  λ x, x ∈ A → P x.

Notation "∀ x .. y ∈ A , P" :=
  ( all ( all_in A ( λ x, .. ( all ( all_in A ( λ y, P ))) .. )))
  (at level 200, x binder, y binder, right associativity).

Definition ex_in `(A : set, P : set → Prop) : set → Prop :=
  λ x, x ∈ A ∧ P x.

Notation "∃ x .. y ∈ A , P" :=
  ( ex ( ex_in A ( λ x, .. ( ex ( ex_in A ( λ y, P ))) .. )))
  (at level 200, x binder, y binder, right associativity).

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

(** Sub是集合的子集关系。
    我们用 A ⊆ B 表示 "A是B的子集"，用 A ⊈ B 表示 "A不是B的子集"。 *)
Definition Sub : set → set → Prop :=
  λ A B, ∀x ∈ A, x ∈ B.
  
Notation "A ⊆ B" := ( Sub A B) (at level 70).
Notation "A ⊈ B" := (¬Sub A B) (at level 70).

(* 子集关系是自反的 *)
Lemma sub_refl : ∀ A, A ⊆ A.
Proof. unfold Sub. intros A x H. apply H. Qed.
Hint Immediate sub_refl : core.

(* 子集关系是传递的 *)
Lemma sub_tran : ∀ A B C, A ⊆ B → B ⊆ C → A ⊆ C.
Proof.
  unfold Sub. intros * H1 H2 x H.
  apply H2. apply H1. apply H.
Qed.

(**=== 公理1: 外延公理 ===**)
(* 两个集合相等当且仅当它们包含相同的成员 *)
Axiom ExtAx : ∀ A B, A = B ↔ (∀ x, x ∈ A ↔ x ∈ B).

Lemma ExtNI : ∀ A B, (∃x ∈ B, x ∉ A) → A ≠ B.
Proof.
  intros A B [x [Hx Hx']] Hext.
  rewrite ExtAx in Hext. apply Hext in Hx.
  apply Hx'. apply Hx.
Qed.

(* 子集关系是反对称的。至此，子集关系构成了集合上的偏序。 *)
Lemma sub_antisym: ∀ A B, A ⊆ B → B ⊆ A → A = B.
Proof.
  unfold Sub. intros A B H1 H2.
  apply ExtAx.
  split. apply H1. apply H2.
Qed.

(**=== 公理2: 空集公理 ===**)
(* 空集公理保证了集合类型是居留的，即存在最底层的集合，
  任何其他集合都不是它的成员，这样的集合就是空集。 *)
Parameter Empty : set.
Notation "∅" := Empty.
Axiom EmptyAx : ∀ x, x ∉ ∅.

Ltac exfalso0 := exfalso; eapply EmptyAx; eassumption.

(* 集合的非空性 (类似于类型的居留性) *)
Definition nonempty : set → Prop := λ A, ∃ x, x ∈ A.
Notation "⦿ x" := (nonempty x) (at level 45).

(* 空集非居留 *)
Fact empty_is_not_inhabited : ¬ ⦿ ∅.
Proof.
  unfold nonempty, not. intros.
  destruct H as [x H].
  eapply EmptyAx. apply H.
Qed.

(* Introduction rule of empty set (空集的导入) *)
Lemma EmptyI : ∀ A, (∀ x, x ∉ A) → A = ∅.
Proof.
  intros A E. apply ExtAx.
  split; intros H.
  - exfalso. eapply E. apply H.
  - exfalso0.
Qed.

(* Elimination rule of empty set (空集的导出) *)
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
  - apply EmptyI. unfold not. intros.
    apply H in H0. eapply EmptyAx. apply H0.
  - subst. intros x H. apply H.
Qed.

(* 任意集合要么是空集要么是居留的 *)
Lemma empty_or_inh : ∀ A, A = ∅ ∨ ⦿A.
Proof.
  intros. destruct (classic (A = ∅)).
  - left. apply H.
  - right. apply EmptyNE. apply H.  
Qed.

(**=== 公理3: 并集公理 ===**)
(* 给定集合X，存在X的并集⋃X，它的成员都是X的某个成员的成员 *)
Parameter Union : set → set.
Notation "⋃ A" := (Union A) (at level 9, right associativity).
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
Notation "'𝒫' A" := (Power A) (at level 9, right associativity).
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

(* 存在唯一 *)
Definition exu: (set → Prop) → Prop :=
  λ P, (∃ x, P x) ∧ (∀ x y, P x → P y → x = y).
Notation "∃! x , p" := (exu (λ x, p)) (at level 200, x ident).
Notation "∄! x , p" := (¬ exu (λ x, p)) (at level 200, x ident).

(**=== 公理5: 替代公理（模式） ===**)
(* 给定二元谓词P，如果对任意集合x有唯一集合y使得P x y成立，
  那么给定集合X，存在集合Y，对于Y的任意成员y都存在X中元素x使得P x y成立 *)
Parameter ϕ_Repl : (set → set → Prop) → set → set.
Axiom ϕ_ReplAx : ∀ (P : set → set → Prop) A,
  (∀ x ∈ A, ∃! y, P x y) →
  ∀ y, y ∈ ϕ_Repl P A ↔ ∃x ∈ A, P x y.

Definition Repl : (set → set) → set → set := λ F A,
  ϕ_Repl (λ x y, F x = y) A.
Notation "{ F | x ∊ A }" := (Repl (λ x, F x) A).

Theorem ReplAx : ∀ y F A, y ∈ {F | x ∊ A} ↔ ∃x ∈ A, F x = y.
Proof with auto.
  intros. split.
  - intros Hy. apply ϕ_ReplAx in Hy...
    intros x Hx. split. exists (F x)...
    intros y1 y2 H1 H2. congruence.
  - intros [x [Hx Heq]]. apply ϕ_ReplAx.
    + intros a Ha. split. exists (F a)...
      intros y1 y2 H1 H2. congruence.
    + exists x. split...
Qed.

Lemma ReplI : ∀ A F, ∀x ∈ A, F x ∈ {F | x ∊ A}.
Proof.
  intros A F x Hx. apply ReplAx.
  exists x. split. apply Hx. reflexivity.
Qed.

Lemma repl_rewrite : ∀ G F A, (∀a ∈ A, F a = G a) →
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
