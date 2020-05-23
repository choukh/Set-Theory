(*** Formal Construction of a Set Theory in Coq ***)
(** based on the thesis by Jonas Kaiser, November 23, 2012 **)
(** Coq coding by choukh, April 2020 **)

Require Export Coq.Unicode.Utf8_core.
(* 导入以下两个库就不需要元定律里添加的公理 *)
(* Require Export Coq.Logic.Classical_Prop. *)
(* Require Export Coq.Logic.Epsilon. *)

(*** 元定律 ***)

(* 基于归纳构造演算CiC *)

Notation "⊤" := (True).
Notation "⊥" := (False).

(**=== 排中律 ===**)
Axiom classic : ∀ P : Prop, P ∨ ¬P.

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

Set Implicit Arguments.
(**=== 希尔伯特ε算子 ===**) 
(* (在经典逻辑下，结合替代公理和空集公理可以导出Zermelo分类公理(见EX2)，
  可以单独导出ZFC选择公理(见EX3)) *)
(* 存在ε算子，对于任意类型A和该类型上的任意谓词P，只要A是被居留的，
  用ε算子就可以得到A上的某个x，它使命题P成立，只要存在A上的某个y使P成立。 *)
Axiom ε_statement : ∀ (A : Type) (P : A → Prop),
  inhabited A → {x : A | (∃ y, P y) → P x}.

(* 用ε算子可以得到εAP，它是在A上任意选择的一个使P成立的a。
  若这样的a不存在，则εAP为任意A上的a *)
Definition ε (A : Type) (i : inhabited A) (P : A → Prop) : A :=
  proj1_sig (ε_statement P i).

(* 用ε_spec可以得到εAP满足P的证据，只要存在一个A上的a使P成立。
  若这样的a不存在，则可以证明P(εAP)不成立 *)
Definition ε_spec (A : Type) (i : inhabited A) (P : A → Prop) :
  (∃ x, P x) → P (ε i P) :=
  proj2_sig (ε_statement P i).

(* 在经典逻辑下，由ε算子可以得到以下结论 *)

(** Informative Excluded Middle (排中律是信息丰富的) **)
Definition IXM : Type := ∀ P : Prop, P + ¬P.

Theorem ixm : IXM.
Proof.
  unfold IXM. intros P.
  assert (H := classic P).
  assert (I: inhabited (P + ¬P)). {
    destruct H.
    - apply inhabits. apply inl. apply H.
    - apply inhabits. apply inr. apply H.
  }
  apply (ε I (λ _, ⊤)).
Qed.

(** Decidability of the Inhabitance of Types (类型的居留性是可判定的) **)
Definition DIT : Type := ∀ T : Type, T + (T → ⊥).

Theorem dit : DIT.
Proof.
  unfold DIT. intros T.
  destruct (ixm (inhabited T)) as [I|I].
  - left. apply (ε I (λ _, ⊤)).
  - right. intros t. apply I.
    apply inhabits. apply t.
Qed.

(*** Tarski-Grothendieck集合论公理 ***)

Parameter set : Type.

(** In是集合的成员关系。
    我们用 x ∈ y 表示 "x是y的成员"，用 x ∉ y 表示 "x不是y的成员"。 *)
Parameter In : set → set → Prop.

Notation "x ∈ y" := ( In x y) (at level 70).
Notation "x ∉ y" := (¬In x y) (at level 70).

(* 集合论中配合量词的惯例写法 *)

Definition all_in `(X : set, P : set → Prop) : set → Prop :=
  λ x, x ∈ X → P x.

Notation "∀ x .. y ∈ X , P" :=
  ( all ( all_in X ( λ x, .. ( all ( all_in X ( λ y, P ))) .. )))
  (at level 200, x binder, y binder, right associativity).

Definition ex_in `(X : set, P : set → Prop) : set → Prop :=
  λ x, x ∈ X ∧ P x.

Notation "∃ x .. y ∈ X , P" :=
  ( ex ( ex_in X ( λ x, .. ( ex ( ex_in X ( λ y, P ))) .. )))
  (at level 200, x binder, y binder, right associativity).

Ltac unfoldq := unfold all, all_in, ex_in in *.
Ltac introq := unfoldq; intros.

(** Sub是集合的子集关系。
    我们用 X ⊆ Y 表示 "X是Y的子集"，用 X ⊈ Y 表示 "X表示Y的子集"。 *)
Definition Sub : set → set → Prop :=
  λ X Y, ∀x ∈ X, x ∈ Y.
  
Notation "X ⊆ Y" := ( Sub X Y) (at level 70).
Notation "X ⊈ Y" := (¬Sub X Y) (at level 70).

(* 子集关系是自反的 *)
Lemma sub_refl : ∀ A, A ⊆ A.
Proof. unfold Sub. intros A x H. apply H. Qed.

(* 子集关系是传递的 *)
Lemma sub_tran : ∀ A B C, A ⊆ B → B ⊆ C → A ⊆ C.
Proof.
  unfold Sub. intros * H1 H2 x H.
  apply H2. apply H1. apply H.
Qed.

(**=== 公理1: 外延公理 ===**)
(* 两个集合相等当且仅当它们包含相同的成员 *)
Axiom ExtAx : ∀ A B, A = B ↔ (∀ x, x ∈ A ↔ x ∈ B).

(* 子集关系是反对称的。至此，子集关系构成了集合上的偏序。 *)
Lemma sub_asym: ∀ A B, A ⊆ B → B ⊆ A → A = B.
Proof.
  unfold Sub. intros A B H1 H2.
  apply ExtAx.
  split. apply H1. apply H2.
Qed.

(**=== 公理2: ∈归纳原理 (在经典逻辑下可以导出ZFC正则公理(见EX3)) ===**)
(* 对于集合的任意性质P，如果可以通过证明"集合A的所有成员都具有性质P"来证明A具有性质P，
  那么所有集合都具有性质P。 *)
Axiom ε_ind : ∀ P : set → Prop,
  (∀ A, (∀a ∈ A, P a) → P A) → ∀ A, P A.

(**=== 公理3: 空集公理 ===**)
(* 空集公理保证了集合类型是居留的，即存在最底层的集合，
  任何其他集合都不是它的成员，这样的集合就是空集。 *)
Parameter Empty : set.
Notation "∅" := Empty.
Axiom EmptyAx : ∀ x, x ∉ ∅.

Ltac exfalso0 := exfalso; eapply EmptyAx; eassumption.

(* 集合的非空性 (类似于类型的居留性) *)
Definition inhset : set → Prop := λ A, ∃ x, x ∈ A.
Notation "⦿ x" := (inhset x) (at level 45).

Example empty_is_not_inhabited : ¬ ⦿ ∅.
Proof.
  unfold inhset, not. intros.
  destruct H as [x H].
  eapply EmptyAx. apply H.
Qed.

Lemma EmptyI : ∀ X, (∀ x, x ∉ X) → X = ∅.
Proof.
  intros X E. apply ExtAx.
  split; intros H.
  - exfalso. eapply E. apply H.
  - exfalso0.
Qed.

Lemma EmptyE : ∀ X, X = ∅ → (∀ x, x ∉ X).
Proof. intros. subst X. apply EmptyAx. Qed.

Lemma EmptyNI : ∀ X, ⦿ X -> X ≠ ∅.
Proof.
  unfold not. introq.
  destruct H as [x H].
  eapply EmptyAx. rewrite H0 in H. apply H.
Qed.

Lemma EmptyNE : ∀ X, X ≠ ∅ → ⦿ X.
Proof.
  intros. pose proof (classic (⦿ X)).
  destruct H0.
  - apply H0.
  - unfold not in H0.
    assert (∀ x, x ∉ X).
    + intros x H1. apply H0.
      exists x. apply H1.
    + apply EmptyI in H1.
      rewrite H1 in H. exfalso. apply H. reflexivity.
Qed.

Example emtpy_is_unique : ∀ X Y, (∀ x, x ∉ X) → (∀ y, y ∉ Y) → X = Y.
Proof.
  intros.
  apply EmptyI in H.
  apply EmptyI in H0.
  subst. reflexivity.
Qed.

Lemma empty_sub_all : ∀ X, ∅ ⊆ X.
Proof. unfold Sub. introq. exfalso0. Qed.

(**=== 公理4: 配对公理 ===**)
(* 任意两个集合可以组成一个新的集合，新集合的成员就是原来的两个集合 *)
Parameter Pair : set → set → set.
Notation "{ x , y }" := (Pair x y).
Axiom PairAx : ∀ w x y, w ∈ {x, y} ↔ w = x ∨ w = y.

(* Introduction rule of pairing (配对的导入规则) *)
Lemma PairI1 : ∀ x y, x ∈ {x, y}.
Proof. intros. apply PairAx. left. reflexivity. Qed.

Lemma PairI2 : ∀ x y, y ∈ {x, y}.
Proof. intros. apply PairAx. right. reflexivity. Qed.

(* Elimination rule of pairing (配对的导出规则) *)
Lemma PairE : ∀ x y, ∀w ∈ {x, y}, w = x ∨ w = y.
Proof. introq. apply PairAx. apply H. Qed.

(* 配对是顺序无关的 *)
Theorem pair_ordering_agnostic : ∀ a b, {a, b} = {b, a}.
Proof.
  intros. apply ExtAx.
  split; intros.
  - apply PairE in H.
    destruct H as [H1|H2].
    + subst x. apply PairI2.
    + subst x. apply PairI1.
  - apply PairE in H.
    destruct H as [H1|H2].
    + subst x. apply PairI2.
    + subst x. apply PairI1.
Qed.

(**=== 公理5: 并集公理 ===**)
(* 给定集合X，存在X的并集⋃X，它的成员都是X的某个成员的成员 *)
Parameter Union : set → set.
Notation "⋃ X" := (Union X) (at level 9, right associativity).
Axiom UnionAx : ∀ a X, a ∈ ⋃X ↔ ∃x ∈ X, a ∈ x.

Lemma UnionI : ∀ X, ∀x ∈ X, ∀a ∈ x, a ∈ ⋃X.
Proof.
  introq. apply UnionAx.
  exists x. split; assumption.
Qed.

Lemma UnionE1 : ∀ a X, a ∈ ⋃X → ∃ x, x ∈ X.
Proof.
  intros. apply UnionAx in H.
  destruct H as [x [H _]].
  exists x. apply H.
Qed.

Lemma UnionE2 : ∀ a X, a ∈ ⋃X → ∃ x, a ∈ x.
Proof.
  intros. apply UnionAx in H.
  destruct H as [x [_ H]].
  exists x. apply H.
Qed.

(**=== 公理6: 幂集公理 ===**)
(* 存在幂集，它是给定集合的所有子集组成的集合 *)
Parameter Power : set → set.
Notation "'𝒫' X" := (Power X) (at level 9, right associativity).
Axiom PowerAx : ∀ X Y, Y ∈ 𝒫(X) ↔ Y ⊆ X.

Lemma empty_in_all_power: ∀ X, ∅ ∈ 𝒫(X).
Proof. intros. apply PowerAx. apply empty_sub_all. Qed.

Lemma all_in_its_power: ∀ X, X ∈ 𝒫(X).
Proof. intros. apply PowerAx. apply sub_refl. Qed.

Example only_empty_in_power_empty: ∀ x, x ∈ 𝒫(∅) → x = ∅.
Proof.
  intros.
  apply PowerAx in H.
  unfold Sub in H.
  apply ExtAx. split; intros.
  - apply H. apply H0.
  - exfalso0.
Qed.

(**=== 公理7: 替代公理（模式） ===**)
(* 给定任意集合X，和集合间的任意函数F，存在一个集合，它的成员都是对A的成员应用F得到的 *)
Parameter Repl : (set → set) → set → set.
Notation "{ F | x ∊ X }" := (Repl (λ x, F x) X).
Axiom ReplAx : ∀ y F X, y ∈ {F | x ∊ X} ↔ ∃x ∈ X, F x = y.

Lemma ReplI : ∀ X F, ∀x ∈ X, F x ∈ {F | x ∊ X}.
Proof.
  introq. apply ReplAx.
  exists x. split. apply H. reflexivity.
Qed.

Lemma ReplE : ∀ X F, ∀y ∈ {F | x ∊ X}, ∃x ∈ X, F x = y.
Proof. introq. apply ReplAx. apply H. Qed.

(** 集合的传递性 **)
Definition trans : set → Prop :=
  λ X, ∀ a A, a ∈ A → A ∈ X → a ∈ X.

(* 传递集的成员都是该传递集的子集 *)
Example trans_ex_1 : ∀ x X, trans X → x ∈ X → x ⊆ X.
Proof.
  unfold trans, Sub. introq.
  eapply H. apply H1. apply H0.
Qed.

(* 传递集的并集也是该传递集的成员 *)
Example trans_ex_2 : ∀ X, trans X → ⋃X ⊆ X.
Proof.
  unfold trans, Sub. introq.
  apply UnionAx in H0.
  destruct H0 as [A [H1 H2]].
  eapply H. apply H2. apply H1.
Qed.

(**=== 公理8: 格罗滕迪克宇宙公理 ===**)
Parameter GU : set → set.
Notation "'𝒰' N" := (GU N) (at level 9).
Axiom GUIn : ∀ N, N ∈ 𝒰(N).

(* 传递性 *)
Axiom GUTrans : ∀ N, trans 𝒰(N).

(* 封闭性 *)
Axiom GUPair : ∀ N X Y, X ∈ 𝒰(N) → Y ∈ 𝒰(N) → {X, Y} ∈ 𝒰(N).
Axiom GUPower : ∀ N X, X ∈ 𝒰(N) → 𝒫(X) ∈ 𝒰(N).
Axiom GUUnion : ∀ N X, X ∈ 𝒰(N) → ⋃X ∈ 𝒰(N).
Axiom GURepl : ∀ N X F, X ∈ 𝒰(N) →
  (∀x ∈ X, F x ∈ 𝒰(N)) → {F | x ∊ X} ∈ 𝒰(N).

(* 最小性 *)
Axiom GUMin : ∀ N U, N ∈ U
  → (∀ X Y, X ∈ U → Y ∈ X → Y ∈ U)
  → (∀ X Y, X ∈ U → Y ∈ U → {X, Y} ∈ U)
  → (∀X ∈ U, 𝒫(X) ∈ U)
  → (∀X ∈ U, ⋃X ∈ U)
  → (∀ X F, X ∈ U → (∀x ∈ X, F x ∈ U) → {F | x ∊ X} ∈ U)
  → 𝒰(N) ⊆ U.

Module gu_infinite.

(* 集合对函数封闭 *)
Definition close : (set → set) → set → Prop := λ F X,
  ∀x ∈ X, F x ∈ X. 

(* 单射 *)
Definition injective : (set → set) → set → Prop := λ F X,
  ∀ a b ∈ X, F a = F b → a = b.

(* 满射 *)
Definition surjective : (set → set) → set → set → Prop := λ F X Y,
  ∀y ∈ Y, ∃x ∈ X, F x = y.

(** 集合的无穷性 **)
Definition infinite : set → Prop := λ X,
  ∃ F, close F X ∧ injective F X ∧ ¬ surjective F X X.

(* 推论: 𝒰(∅)是无穷集 *)
Theorem gu_infinite : infinite 𝒰(∅).
Proof with unfoldq.
  unfold infinite. exists Power. repeat split.
  - unfold close... intros. apply GUPower. apply H.
  - unfold injective... intros a _ b _ Heq.
    apply sub_asym.
    + pose proof (all_in_its_power a) as Hin.
      rewrite Heq in Hin.
      apply PowerAx. apply Hin.
    + pose proof (all_in_its_power b) as Hin.
      rewrite <- Heq in Hin.
      apply PowerAx. apply Hin.
  - unfold surjective, not... intros.
    pose proof (H ∅ (GUIn ∅)).
    destruct H0 as [x [H1 H2]].
    assert (∀A ∈ 𝒰(∅), 𝒫(A) ≠ ∅)... {
      introq. apply EmptyNI.
      exists ∅. apply empty_in_all_power.
    }
    specialize H0 with x.
    apply H0 in H1. auto.
Qed.

End gu_infinite.
