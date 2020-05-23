(** Based on "Elements of Set Theory" Chapter 4 Part 1 **)
(** Coq coding by choukh, May 2020 **)

Require Export ZFC.CH3_2.

(*** EST第四章1：自然数，归纳集，传递集，皮亚诺结构 ***)

(* 后续运算 *)
Definition S : set → set := λ a, a ∪ ⎨a⎬.
Notation "a ⁺" := (S a) (at level 8).

Lemma S_neq_0 : ∀ x, x⁺ ≠ ∅.
Proof.
  intros x H. eapply EmptyE in H. apply H.
  apply BUnionI2. apply SingI.
Qed.

(** 归纳集 **)
Definition inductive : set → Prop := λ A,
  ∅ ∈ A ∧ ∀a ∈ A, a⁺ ∈ A.

Lemma GU0_inductive : inductive 𝒰(∅).
Proof with auto.
  split. apply GUIn. intros a Ha.
  apply GUBUnion... apply GUSing...
Qed.

(* 由宇宙公理导出原ZFC无穷公理，即归纳集的存在性 *)
Theorem Infinity : ∃ A, inductive A.
Proof. exists (𝒰(∅)). apply GU0_inductive. Qed.

Definition is_nat : set → Prop := λ n, ∀ A, inductive A → n ∈ A.

Theorem ω_exists : ∃ ω, ∀ n, n ∈ ω ↔ is_nat n.
Proof with auto.
  destruct Infinity as [A HA].
  set {x ∊ A | λ x, ∀ B, inductive B → x ∈ B} as ω.
  exists ω. split.
  - intros Hn B HB. apply SepE in Hn as [_ H]. apply H in HB...
  - intros Hn. apply SepI. apply Hn in HA...
    intros B HB. apply Hn in HB...
Qed.

Definition ω : set := {n ∊ 𝒰(∅) | λ n, ∀ A, inductive A → n ∈ A}.

Lemma ω_has_0 : ∅ ∈ ω.
Proof. apply SepI. apply GU0_inductive. intros A [H _]. auto. Qed.

(* ω是归纳集 *)
Theorem ω_inductive : inductive ω.
Proof with auto.
  split.
  - apply SepI. apply GUIn. intros A [H _]...
  - intros a Ha. apply SepE in Ha as [_ H]. apply SepI.
    + apply GUBUnion. apply H. apply GU0_inductive.
      apply GUSing. apply H. apply GU0_inductive.
    + intros A HA. apply H in HA as Ha.
      destruct HA as [_ H1]. apply H1 in Ha...
Qed. 

Theorem ω_sub_inductive : ∀ A, inductive A → ω ⊆ A.
Proof. intros A Hi x Hx. apply SepE in Hx as [_ H]. auto. Qed.

(* ω归纳原理 *)
Theorem ω_ind : ∀ x, x ⊆ ω → inductive x → x = ω.
Proof with auto.
  intros * Hs Hi. apply ExtAx. intros n. split; intros Hn.
  - apply Hs...
  - apply SepE in Hn as [_ Hn]. apply Hn in Hi...
Qed.

Ltac ind T H := cut (T = ω); [
  intros HTeq; rewrite <- HTeq in H;
  apply SepE in H as []; auto |
  apply ω_ind; [
    intros x Hx; apply SepE in Hx as []; auto |
    split; [apply SepI; [apply ω_has_0 |]|]
  ]; [|
    intros a Ha; apply SepE in Ha as [Ha IH];
    apply SepI; [apply ω_inductive; auto |]
  ]
].

(* 自然数是传递集 *)
Theorem nat_trans : ∀n ∈ ω, trans n.
Proof with eauto.
  intros n Hn.
  set {n ∊ ω | λ n, trans n} as T.
  ind T Hn.
  - intros a A Ha HA. exfalso0.
  - intros b B Hb HB. apply BUnionE in HB as [].
    + apply BUnionI1. eapply IH...
    + apply SingE in H. subst. apply BUnionI1...
Qed.

Theorem all_suc : ∀n ∈ ω, n ≠ ∅ → ∃n' ∈ ω, n'⁺ = n.
Proof with auto.
  intros n Hn.
  set {n ∊ ω | λ n, n ≠ ∅ → ∃n' ∈ ω, n'⁺ = n} as T.
  ind T Hn.
  - intros. exfalso. apply H...
  - intros _. exists a. split...
Qed.

(** 传递集 **)
Print trans.
(* trans = λ X : set, ∀ a A : set, a ∈ A → A ∈ X → a ∈ X
   : set → Prop *)

Lemma trans_union_sub : ∀ A, trans A ↔ ⋃A ⊆ A.
Proof with eauto.
  split.
  - intros * Ht x Hx.
    apply UnionAx in Hx as [y [Hy Hx]]. eapply Ht...
  - intros Hs x n Hx Hn. apply Hs. eapply UnionI... 
Qed.

Lemma trans_sub : ∀ A, trans A ↔ ∀a ∈ A, a ⊆ A.
Proof with eauto.
  split.
  - intros * Ht a Ha x Hx. eapply Ht...
  - intros H x n Hx Hn. apply H in Hn. apply Hn...
Qed.

Lemma trans_sub_power : ∀ A, trans A ↔ A ⊆ 𝒫 A.
Proof with eauto.
  split.
  - intros * Ht a Ha. apply PowerAx.
    intros x Hx. eapply Ht...
  - intros H x n Hx Hn. apply H in Hn.
    rewrite PowerAx in Hn. apply Hn...
Qed.

Theorem trans_union_suc : ∀ a, trans a → ⋃a⁺ = a.
Proof with auto.
  intros. unfold S. rewrite ch2_21, union_sing_x_x.
  apply ExtAx. split; intros Hx.
  - apply BUnionE in Hx as []...
    assert (⋃a ⊆ a) by (apply trans_union_sub; auto). apply H1...
  - apply BUnionI2...
Qed.

(* 自然数是传递集 *)
Theorem nat_trans : ∀n ∈ ω, trans n.
Proof with eauto.
  intros n Hn.
  set {n ∊ ω | λ n, trans n} as T.
  ind T Hn.
  - intros a A Ha HA. exfalso0.
  - intros b B Hb HB. apply BUnionE in HB as [].
    + apply BUnionI1. eapply IH...
    + apply SingE in H. subst. apply BUnionI1...
Qed.

(* 集合对函数封闭 *)
Definition close : set → set → Prop := λ S A, ∀x ∈ A, S[x] ∈ A.

(** 皮亚诺结构 **)
Definition is_Peano : set → set → set → Prop := λ N S e,
  S: N ⇒ N → e ∈ N →
  e ∉ ran S ∧
  injective S ∧
  ∀ A, A ⊆ N → e ∈ A → close S A → A = N.

(* <ω, σ, ∅>是一个皮亚诺结构 *)
Theorem ω_Peano : let σ := {λ n, <n, n⁺> | n ∊ ω} in
  is_Peano ω σ ∅.
Proof with eauto.
  intros * [Hf [Hd Hr]] He. split; [|split].
  - intros H. apply ranE in H as [x Hp].
    apply ReplE in Hp as [n [Hn H]].
    apply op_correct in H as [_ H]. eapply S_neq_0...
  - split... intros y Hy. split. apply ranE in Hy...
    intros x1 x2 H1 H2.
    apply ReplE in H1 as [n [Hx1 Hn]].
    apply ReplE in H2 as [m [Hx2 Hm]].
    apply op_correct in Hn as [Hn1 Hn2].
    apply op_correct in Hm as [Hm1 Hm2]. subst.
    assert (⋃x2⁺ = ⋃x1⁺) by congruence.
    apply nat_trans in Hx1. apply nat_trans in Hx2.
    do 2 rewrite trans_union_suc in H...
  - intros A HA H0 Hc. apply ω_ind... split...
    intros a Ha. apply Hc in Ha as Hsa.
    apply HA in Ha. rewrite <- Hd in Ha.
    apply domE in Ha as [a1 Hp]. apply apI in Hp as Hap...
    apply ReplE in Hp as [n [_ Heq]].
    apply op_correct in Heq as []; subst. congruence.
Qed.

(* ω是传递集 *)
Theorem ω_trans : trans ω.
Proof with eauto.
  rewrite trans_sub. intros n Hn.
  set {n ∊ ω | λ n, n ⊆ ω} as T.
  ind T Hn.
  - intros x Hx. exfalso0.
  - intros x Hx. apply BUnionE in Hx as [].
    apply IH... apply SingE in H. subst...
Qed.








