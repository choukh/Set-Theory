(** Based on "Elements of Set Theory" Chapter 2 **)
(** Coq coding by choukh, May 2020 **)

Require Export ZFC.lib.Essential.

(*** EST第二章：补集，真子集，集合代数定律 ***)

(** 补集 **)
Definition Complement : set → set → set := λ A B, {x ∊ A | λ x, x ∉ B}.
Notation "A - B" := (Complement A B) : ZFC_scope.

Lemma CompI : ∀ A B, ∀x ∈ A, x ∉ B → x ∈ A - B.
Proof. intros A B x Hx H. apply SepI. apply Hx. apply H. Qed.

Lemma CompE : ∀ A B, ∀x ∈ A - B, x ∈ A ∧ x ∉ B.
Proof. intros A B x Hx. apply SepE in Hx. apply Hx. Qed.

Lemma CompNE : ∀ A B x, x ∉ A - B → x ∉ A ∨ x ∈ B.
Proof.
  intros. destruct (classic (x ∈ B)).
  - right. apply H0.
  - left. intros H1. apply H. apply CompI; assumption.
Qed.

Lemma union_comp : ∀ A B C, (A ∪ B) - C = (A - C) ∪ (B - C).
Proof.
  intros. apply ExtAx. split; intros.
  - apply CompE in H. destruct H as [H HC].
    apply BUnionE in H. destruct H.
    + apply BUnionI1. apply CompI. apply H. apply HC.
    + apply BUnionI2. apply CompI. apply H. apply HC.
  - apply BUnionE in H. destruct H.
    + apply CompE in H as [HA HC].
      apply CompI. apply BUnionI1. apply HA. apply HC.
    + apply CompE in H as [HB HC].
      apply CompI. apply BUnionI2. apply HB. apply HC.
Qed.

Lemma sub_iff_no_comp : ∀ A B, A ⊆ B ↔ A - B = ∅.
Proof.
  split; intros.
  - apply EmptyI. intros x Hx. apply CompE in Hx as [H1 H2].
    apply H2. apply H. apply H1.
  - intros x Hx. apply EmptyE with (A - B) x in H.
    destruct (classic (x ∈ B)). apply H0.
    exfalso. apply H. apply CompI; assumption.
Qed.

Lemma comp_sub : ∀ A B, A - B ⊆ A.
Proof.
  intros A B x Hx. apply CompE in Hx as []; auto.
Qed.
Global Hint Immediate comp_sub : core.

(* 空集的补集是原集合 *)
Lemma comp_empty : ∀ A, A - ∅ = A.
Proof with auto.
  intros. apply ExtAx. split; intros Hx.
  - apply SepE1 in Hx...
  - apply SepI... intros H. exfalso0.
Qed.

(* 空集里的补集是空集 *)
Lemma empty_comp : ∀ A, ∅ - A = ∅.
Proof with auto.
  intros. apply ExtAx. split; intros Hx.
  - apply SepE in Hx as []. exfalso0.
  - exfalso0.
Qed.

(* 集合除去非自身的元素，集合不变 *)
Lemma remove_no_member : ∀ a A, a ∉ A → A - ⎨a⎬ = A.
Proof with auto.
  intros * Ha. apply ExtAx. split; intros Hx.
  - apply SepE1 in Hx...
  - apply SepI... apply SingNI. intros Heq.
    apply Ha. subst...
Qed.

(* 集合除去自身的一个元素再放回去，集合不变 *)
Lemma remove_one_member_then_return : ∀ A a, a ∈ A → A - ⎨a⎬ ∪ ⎨a⎬ = A.
Proof with auto.
  intros. apply ExtAx. split; intros Hx.
  - apply BUnionE in Hx as [].
    + apply SepE1 in H0...
    + apply SingE in H0. subst...
  - destruct (classic (x = a)).
    + subst. apply BUnionI2...
    + apply BUnionI1. apply SepI... apply SingNI...
Qed.

(* 集合加入一个不是自身的元素再去掉，集合不变 *)
Lemma add_one_member_then_remove : ∀ A a, a ∉ A → A ∪ ⎨a⎬ - ⎨a⎬ = A.
Proof with auto.
  intros. apply ExtAx. split; intros Hx.
  - apply SepE in Hx as [].
    apply BUnionE in H0 as []... exfalso...
  - apply SepI. apply BUnionI1...
    apply SingNI. intros Heq. congruence.
Qed.

(* 从集合中取出一个元素组成单集，它与取完元素后的集合的并等于原集合 *)
Lemma split_one_element : ∀ A a, a ∈ A → A = (A - ⎨a⎬) ∪ ⎨a⎬.
Proof with auto.
  intros. apply ExtAx. split; intros Hx.
  - destruct (classic (x = a)).
    + subst x. apply BUnionI2...
    + apply BUnionI1. apply SepI...
      intros contra. apply SingE in contra...
  - apply BUnionE in Hx as [].
    + apply SepE1 in H0...
    + apply SingE in H0. subst x...
Qed.

(** 真子集 **)
Notation "A ⊂ B" := (A ⊆ B ∧ A ≠ B) (at level 70) : ZFC_scope.

Lemma properSub_intro : ∀ A B, B ⊆ A → (∃ a, a ∈ A ∧ a ∉ B) → B ⊂ A.
Proof with auto.
  intros A B Hsub [a [Ha Ha']]. split... intros Heq.
  rewrite ExtAx in Heq. apply Heq in Ha...
Qed.

Lemma comp_nonempty : ∀ B A, B ⊂ A → ⦿ (A - B).
Proof.
  intros * [Hsub Hnq]. apply EmptyNE.
  intros H0. apply sub_iff_no_comp in H0.
  apply Hnq. apply sub_antisym. apply Hsub. apply H0.
Qed.

(* 并，交，补运算与子集关系构成集合代数，
  类似与自然数的加，乘，减运算与小于等于关系 *)

(** 集合代数定律 **)

(* 二元并交换律 *)
Lemma bunion_comm : ∀ A B, A ∪ B = B ∪ A.
Proof.
  intros. apply ExtAx. split; intros.
  - apply BUnionE in H. destruct H.
    + apply BUnionI2. apply H.
    + apply BUnionI1. apply H.
  - apply BUnionE in H. destruct H.
    + apply BUnionI2. apply H.
    + apply BUnionI1. apply H.
Qed.

(* 二元交交换律 *)
Lemma binter_comm : ∀ A B, A ∩ B = B ∩ A.
Proof.
  intros. apply ExtAx. split; intros.
  - apply BInterE in H as [H1 H2].
    apply BInterI. apply H2. apply H1.
  - apply BInterE in H as [H1 H2].
    apply BInterI. apply H2. apply H1.
Qed.

(* 二元并结合律 *)
Lemma bunion_assoc : ∀ A B C, A ∪ (B ∪ C) = (A ∪ B) ∪ C.
Proof.
  intros. apply ExtAx. split; intros.
  - apply BUnionE in H. destruct H.
    + apply BUnionI1. apply BUnionI1. apply H.
    + apply BUnionE in H. destruct H.
      * apply BUnionI1. apply BUnionI2. apply H.
      * apply BUnionI2. apply H.
  - apply BUnionE in H. destruct H.
    + apply BUnionE in H. destruct H.
      * apply BUnionI1. apply H.
      * apply BUnionI2. apply BUnionI1. apply H.
    + apply BUnionI2. apply BUnionI2. apply H.
Qed.

(* 二元交结合律 *)
Lemma binter_assoc : ∀ A B C, A ∩ (B ∩ C) = (A ∩ B) ∩ C.
Proof.
  intros. apply ExtAx. split; intros.
  - apply BInterE in H as [H1 H2].
    apply BInterE in H2 as [H2 H3].
    repeat apply BInterI; auto.
  - apply BInterE in H as [H1 H2].
    apply BInterE in H1 as [H0 H1].
    repeat apply BInterI; auto.
Qed.

(* 交并分配律 *)
Lemma binter_bunion_distr : ∀ A B C,
  A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C).
Proof.
  intros. apply ExtAx. split; intros.
  - apply BInterE in H as [H1 H2].
    apply BUnionE in H2. destruct H2.
    + apply BUnionI1. apply BInterI; auto.
    + apply BUnionI2. apply BInterI; auto.
  - apply BUnionE in H. destruct H.
    + apply BInterE in H as [H1 H2].
      apply BInterI. apply H1. apply BUnionI1. apply H2.
    + apply BInterE in H as [H1 H2].
      apply BInterI. apply H1. apply BUnionI2. apply H2.
Qed.

(* 并交分配律 *)
Lemma bunion_binter_distr : ∀ A B C,
  A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C).
Proof.
  intros. apply ExtAx. split; intros.
  - apply BUnionE in H. destruct H.
    + apply BInterI; apply BUnionI1; apply H.
    + apply BInterE in H as [H1 H2].
      apply BInterI; apply BUnionI2; auto.
  - apply BInterE in H as [H1 H2].
    apply BUnionE in H1. apply BUnionE in H2.
    destruct H1; destruct H2.
    + apply BUnionI1. apply H.
    + apply BUnionI1. apply H.
    + apply BUnionI1. apply H0.
    + apply BUnionI2. apply BInterI; auto.
Qed.

(* 交补分配律 *)
Lemma binter_comp_distr : ∀ A B C, A ∩ (B - C) = (A ∩ B) - (A ∩ C).
Proof.
  intros. apply ExtAx. split; intros.
  - apply BInterE in H as [H1 H2].
    apply CompE in H2 as [H2 H3].
    apply CompI. apply BInterI; assumption.
    intros H4. apply BInterE in H4 as [_ H4]. auto.
  - apply CompE in H as [H1 H2].
    apply BInterE in H1 as [H0 H1].
    apply BInterI. apply H0. apply CompI. apply H1.
    intros H3. apply H2. apply BInterI; assumption.
Qed.

(* 二元并德摩根定律 *)
Lemma bunion_demorgen : ∀ A B x, x ∉ A ∪ B ↔ x ∉ A ∧ x ∉ B.
Proof.
  intros. split; intros.
  - split; intros.
    + intros HA. apply H. apply BUnionI1. apply HA.
    + intros HB. apply H. apply BUnionI2. apply HB.
  - destruct H as [H1 H2]. intros H.
    apply BUnionE in H. destruct H; auto.
Qed.

(* 二元并补德摩根定律 *)
Lemma comp_bunion_demorgen : ∀ A B C, C - (A ∪ B) = (C - A) ∩ (C - B).
Proof.
  intros. apply ExtAx. split; intros.
  - apply CompE in H as [H1 H2].
    apply bunion_demorgen in H2. destruct H2 as [H2 H3].
    apply BInterI; apply CompI; auto.
  - apply BInterE in H as [H1 H2].
    apply CompE in H1 as [HC HA].
    apply CompE in H2 as [_ HB].
    apply CompI. apply HC. apply bunion_demorgen. auto.
Qed.

(* 二元交德摩根定律 *)
Lemma binter_demorgen : ∀ A B x, x ∉ A ∩ B ↔ x ∉ A ∨ x ∉ B.
Proof.
  intros. split; intros.
  - destruct (classic (x ∈ A)).
    + right. intros HB. apply H.
      apply BInterI; auto.
    + left. apply H0.
  - intros H0. destruct H.
    + apply H. apply BInterE in H0 as [H0 _]. apply H0.
    + apply H. apply BInterE in H0 as [_ H0]. apply H0.
Qed.

(* 二元交补德摩根定律 *)
Lemma comp_binter_demorgen : ∀ A B C, C - (A ∩ B) = (C - A) ∪ (C - B).
Proof.
  intros. apply ExtAx. split; intros.
  - apply CompE in H as [HC H].
    apply binter_demorgen in H. destruct H.
    + apply BUnionI1. apply CompI. apply HC. apply H.
    + apply BUnionI2. apply CompI. apply HC. apply H.
  - apply BUnionE in H. destruct H.
    + apply CompE in H as [HC HA].
      apply CompI. apply HC. apply binter_demorgen. left. apply HA.
    + apply CompE in H as [HC HB].
      apply CompI. apply HC. apply binter_demorgen. right. apply HB.
Qed.

(* 涉及空集的同一性 *)

Lemma bunion_empty : ∀ A, A ∪ ∅ = A.
Proof.
  intros. apply ExtAx. split; intros.
  - apply BUnionE in H. destruct H. apply H. exfalso0.
  - apply BUnionI1. apply H.
Qed.
  
Lemma binter_empty : ∀ A, A ∩ ∅ = ∅.
Proof.
  intros. apply EmptyI. intros x H.
  apply BInterE in H as [_ H]. exfalso0.
Qed.

Lemma binter_comp_empty : ∀ A C, A ∩ (C - A) = ∅.
Proof.
  intros. apply EmptyI. intros x H.
  apply BInterE in H as [H1 H2].
  apply CompE in H2. destruct H2 as [_ H2]. auto.
Qed.

(* 涉及全集的同一性 *)

Lemma bunion_parent : ∀ A S, A ⊆ S → A ∪ S = S.
Proof.
  intros. apply ExtAx. split; intros.
  - apply BUnionE in H0. destruct H0.
    + apply H in H0. apply H0. 
    + apply H0.
  - apply BUnionI2. apply H0.
Qed.

Lemma binter_parent : ∀ A S, A ⊆ S → A ∩ S = A.
Proof.
  intros. apply ExtAx. split; intros.
  - apply BInterE in H0 as [H0 _]. apply H0.
  - apply BInterI. apply H0. apply H in H0. apply H0.
Qed.

Lemma bunion_comp_parent : ∀ A S, A ⊆ S → A ∪ (S - A) = S.
Proof.
  intros. apply ExtAx. split; intros.
  - apply BUnionE in H0. destruct H0.
    + apply H in H0. apply H0.
    + apply CompE in H0 as [H0 _]. apply H0.
  - destruct (classic (x ∈ A)).
    + apply BUnionI1. apply H1.
    + apply BUnionI2. apply CompI. apply H0. apply H1.
Qed.

Lemma binter_comp_parent : ∀ A S, A ⊆ S → A ∩ (S - A) = ∅.
Proof.
  intros. apply EmptyI. intros x Hx.
  apply BInterE in Hx as [H1 H2].
  apply CompE in H2 as [_ H2]. auto.
Qed.

(* 子集关系的单调性 *)

Lemma sub_mono_bunion : ∀ A B C, A ⊆ B → A ∪ C ⊆ B ∪ C.
Proof.
  intros. intros x Hx. apply BUnionE in Hx. destruct Hx.
  - apply H in H0. apply BUnionI1. apply H0.
  - apply BUnionI2. apply H0.
Qed.

Lemma sub_mono_binter : ∀ A B C, A ⊆ B → A ∩ C ⊆ B ∩ C.
Proof.
  intros. intros x Hx. apply BInterE in Hx as [H1 H2].
  apply H in H1. apply BInterI. apply H1. apply H2.
Qed.

Lemma sub_mono_union : ∀ A B, A ⊆ B → ⋃A ⊆ ⋃B.
Proof.
  intros. intros x Hx. apply UnionAx in Hx as [y [H1 H2]].
  eapply UnionI. apply H in H1. apply H1. apply H2.
Qed.

Lemma sub_mono_cprod : ∀ A B C, A ⊆ B → A × C ⊆ B × C.
Proof with auto.
  intros * H x Hx.
  apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]].
  subst x. apply CProdI... apply H...
Qed.

(* 子集关系的反单调性 *)

Lemma sub_amono_comp : ∀ A B C, A ⊆ B → C - B ⊆ C - A.
Proof.
  intros. intros x Hx. apply CompE in Hx as [HC HB].
  apply CompI. apply HC. intros HA.
  apply HB. apply H. apply HA.
Qed.

Lemma sub_amono_inter : ∀ A B, ⦿ A → A ⊆ B → ⋂B ⊆ ⋃A.
Proof.
  intros. intros x Hx. apply InterE in Hx as [_ Hy].
  destruct H as [a Ha]. eapply UnionI. apply Ha.
  apply H0 in Ha. apply Hy in Ha. apply Ha.
Qed.

(* 二元并任意交分配律 *)
Lemma bunion_inter_distr : ∀ A ℬ,
  ⦿ ℬ → A ∪ ⋂ℬ = ⋂{λ X, A ∪ X | X ∊ ℬ}.
Proof.
  intros * Hi. apply ExtAx. split; intros.
  - apply InterI...
    + destruct Hi as [b Hb]. exists (A ∪ b).
      apply ReplAx... exists b. split; auto.
    + intros y Hy. apply ReplAx in Hy as [z [Hz Hu]]. subst y. 
      apply BUnionE in H as [].
      * apply BUnionI1. apply H.
      * apply BUnionI2. apply InterE in H as [_ H].
        apply H. apply Hz.
  - destruct (classic (x ∈ A)) as [HA|HA].
    + apply BUnionI1. apply HA.
    + apply BUnionI2. apply InterI... apply Hi. intros b Hb.
      assert (Hu: A ∪ b ∈ {BUnion A | X ∊ ℬ}). {
        apply ReplI. apply Hb.
      }
      apply InterE in H as [_ H]...
      apply H in Hu. apply BUnionE in Hu as [].
      * exfalso. apply HA. apply H0.
      * apply H0.
Qed.

(* 二元交任意并的分配律 *)
Lemma binter_union_distr : ∀ A ℬ,
  A ∩ ⋃ℬ = ⋃{λ X, A ∩ X | X ∊ ℬ}.
Proof.
  intros. apply ExtAx. split; intros.
  - apply BInterE in H as [HA Hu].
    apply UnionAx in Hu as [b [Hb1 Hb2]].
    eapply FUnionI.
    + apply Hb1.
    + apply BInterI; assumption.
  - apply FUnionE in H as [y [H1 H2]].
    apply BInterE in H2 as [H2 H3].
    apply BInterI. apply H2.
    eapply UnionI. apply H1. apply H3.
Qed.

(* 补并德摩根定律 *)
Lemma comp_union_demorgen : ∀ 𝒜 C,
  ⦿ 𝒜 → C - ⋃𝒜 = ⋂{λ X, C - X | X ∊ 𝒜}.
Proof.
  intros * [a Ha]. apply ExtAx. split; intros.
  - apply CompE in H as [HC HU]. apply InterI.
    + exists (C - a). apply ReplI. apply Ha.
    + intros y Hy. apply ReplAx in Hy as [b [Hb Hc]].
      rewrite <- Hc. apply CompI. apply HC. intros H.
      apply HU. eapply UnionI. apply Hb. apply H.
  - apply InterE in H as [_ H]. apply CompI.
    + assert (C - a ∈ {Complement C | X ∊ 𝒜}). {
        apply ReplI. apply Ha.
      }
      apply H in H0. apply CompE in H0 as [HC _]. apply HC.
    + intros HU. apply UnionAx in HU as [b [Hb1 Hb2]].
      assert (C - b ∈ {Complement C | X ∊ 𝒜}). {
        apply ReplI. apply Hb1.
      }
      apply H in H0. apply CompE in H0 as [_ Hb3]. auto.
Qed.

(* 经典引理：并非所有都否定，则存在肯定 *)
Lemma quantified_imply_to_and : ∀ (A : Type) (P Q : A → Prop),
  ¬ (∀ a, P a → Q a) → ∃ a, P a ∧ ¬ Q a.
Proof.
  intros.
  apply not_all_ex_not in H as [a H].
  apply imply_to_and in H. 
  exists a. apply H.
Qed.

(* x不在𝒜的交集里，则存在𝒜的成员A，x不是A的成员 *)
Lemma not_in_inter_intro : ∀ 𝒜 x, ⦿ 𝒜 → x ∉ ⋂ 𝒜 → ∃A ∈ 𝒜, x ∉ A.
Proof.
  intros * Hi Hx. apply quantified_imply_to_and.
  intros H. apply Hx. apply InterI.
  apply Hi. intros y Hy. apply H. apply Hy.
Qed.

(* 补交德摩根定律 *)
Lemma comp_inter_demorgen : ∀ 𝒜 C,
  ⦿ 𝒜 → C - ⋂𝒜 = ⋃{λ X, C - X | X ∊ 𝒜}.
Proof.
  intros * Hi. apply ExtAx. split; intros.
  - apply CompE in H as [HC HU].
    apply (not_in_inter_intro _ _ Hi) in HU as [a [Ha1 Ha2]].
    eapply FUnionI. apply Ha1.
    apply CompI. apply HC. apply Ha2.
  - apply FUnionE in H as [y [Hy1 Hy2]].
    apply CompE in Hy2 as [HC Hy2].
    apply CompI. apply HC. intros HU.
    apply InterE in HU as [_ H].
    apply Hy2. apply H. apply Hy1.
Qed.
