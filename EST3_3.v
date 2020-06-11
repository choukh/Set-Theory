(** Based on "Elements of Set Theory" Chapter 3 Part 3 **)
(** Coq coding by choukh, May 2020 **)

Require Export ZFC.EST3_2.

(*** EST第三章3：等价关系，等价类，商集，三分律，全序 ***)

(* 在A上的二元关系R *)
Definition rel : set → set → Prop := λ R A, R ⊆ A × A.

Lemma relI : ∀ R A, rel R A → is_relation R.
Proof.
  intros * H p Hp. apply H in Hp. apply CProdE2 in Hp. apply Hp.
Qed.

Lemma rel_dom : ∀ R A, rel R A → dom R ⊆ A.
Proof.
  intros * Hr x Hx. apply domE in Hx as [y Hp].
  apply Hr in Hp. apply CProdE1 in Hp as [Hx _].
  rewrite π1_correct in Hx. apply Hx.
Qed.

Lemma rel_ran : ∀ R A, rel R A → ran R ⊆ A.
Proof.
  intros * Hr x Hx. apply ranE in Hx as [y Hp].
  apply Hr in Hp. apply CProdE1 in Hp as [_ Hx].
  rewrite π2_correct in Hx. apply Hx.
Qed.

(* 自反性 *)
Definition refl : set → set → Prop := λ R A,
  ∀x ∈ A, <x, x> ∈ R.

(* 对称性 *)
Definition symm : set → Prop := λ R,
  ∀ x y, <x, y> ∈ R → <y, x> ∈ R.

(* 传递性 *)
Definition tranr : set → Prop := λ R,
  ∀ x y z, <x, y> ∈ R → <y, z> ∈ R → <x, z> ∈ R.

(** 等价关系 **)
Definition equiv : set → set → Prop := λ R A,
  rel R A ∧ refl R A ∧ symm R ∧ tranr R.

Theorem equiv_fld : ∀ R, is_relation R →
  symm R → tranr R → equiv R (fld R).
Proof with eauto.
  intros R Hr Hs Ht. repeat split...
  - intros x Hx. apply rel_pair in Hx as Hxp... rewrite Hxp in *.
    apply CProdI. apply BUnionI1. eapply domI...
    apply BUnionI2. eapply ranI...
  - intros x Hx. apply BUnionE in Hx as [].
    + apply domE in H as [y Hp]. apply Hs in Hp as Hp'. eapply Ht...
    + apply ranE in H as [y Hp]. apply Hs in Hp as Hp'. eapply Ht...
Qed.

(* 等价类 *)
Definition EquivClass : set → set → set := λ x R,
  {t ∊ ran R | λ t, <x, t> ∈ R}.
Notation "[ x ] R" := (EquivClass x R) (at level 60).

Lemma eqvcI : ∀ R x y, <x, y> ∈ R → y ∈ [x]R.
Proof with eauto. intros. apply SepI... eapply ranI... Qed.

Lemma eqvcE : ∀ R x y, y ∈ [x]R → <x, y> ∈ R.
Proof. intros. apply SepE in H as []; auto. Qed.

Lemma eqvc_refl: ∀ R A, refl R A → ∀x ∈ A, x ∈ [x]R.
Proof. intros R A Hrf x Hx. apply eqvcI. apply Hrf; auto. Qed.

Lemma eqvc_ident : ∀ R A, ∀ x y ∈ A, equiv R A →
  [x]R = [y]R ↔ <x, y> ∈ R.
Proof with eauto.
  intros R A x Hx y Hy [_ [Hrf [Hsy Htr]]]. split.
  - intros Heq.
    assert (y ∈ [y]R) by (eapply eqvc_refl; eauto).
    rewrite <- Heq in H. apply eqvcE in H...
  - intros Hp. apply ExtAx. intros w. split; intros Hw.
    + apply eqvcE in Hw. apply eqvcI...
    + apply eqvcE in Hw. apply eqvcI...
Qed.

Definition disjoint : set → set → Prop := λ X Y,
  X ≠ Y ∧ X ∩ Y = ∅.

Lemma disjointE: ∀ A B x, disjoint A B → x ∈ A → x ∈ B → ⊥.
Proof with eauto.
  intros * [_ H] Ha Hb.
  eapply EmptyE in H. apply H. apply BInterI...
Qed.

(* 划分 *)
Definition partition : set → set → Prop := λ Π A,
  (* 子集 *) (∀B ∈ Π, ⦿ B ∧ B ⊆ A) ∧ 
  (* 不交 *) (∀ X Y ∈ Π, X ≠ Y → disjoint X Y) ∧
  (* 穷尽 *) ∀x ∈ A, ∃X ∈ Π, x ∈ X.

(* 商集：等价类的集合 *)
Definition Quotient : set → set → set := λ R A,
  {λ x, [x]R | x ∊ A}.
Notation "A / R" := (Quotient R A).

Lemma quotI : ∀ R A, ∀a ∈ A, [a]R ∈ A / R.
Proof. intros * a Ha. apply ReplAx. exists a. split; auto. Qed.

Lemma quotE : ∀ R A, ∀x ∈ A / R, ∃a ∈ A, [a]R = x.
Proof.
  intros * x Hx. apply ReplE in Hx as [a [Ha Heq]].
  exists a. split; auto.
Qed.

Theorem quotient_is_partition : ∀ R A,
  equiv R A → partition (A/R) A.
Proof with eauto.
  intros R A [Hr [Hrf [Hsy Htr]]]. split; [|split].
  - intros B HB. split.
    + apply quotE in HB as [a [Ha Heq]]. subst B.
      exists a. apply eqvcI. apply Hrf...
    + intros x Hx. apply quotE in HB as [a [Ha Heq]].
      subst B. apply eqvcE in Hx. apply Hr in Hx.
      apply CProdE1 in Hx as [_ Hx]. rewrite π2_correct in Hx... 
  - intros X HX Y HY Hnq. split... apply EmptyI.
    intros t Ht. apply Hnq. apply BInterE in Ht as [H1 H2].
    apply ReplE in HX as [x [Hx Hxeq]].
    apply ReplE in HY as [y [Hy Hyeq]]. subst X Y.
    apply eqvcE in H1. apply eqvcE in H2.
    eapply eqvc_ident... repeat split...
  - intros x Hx. exists ([x]R). split.
    apply ReplAx. exists x. split... eapply eqvc_refl...
Qed.

(* 函数与关系的相容性 *)
Definition compatible : set → set → set → Prop := λ R A F,
  ∀ x y ∈ A, <x, y> ∈ R → <F[x], F[y]> ∈ R.

Lemma compatibleE0 : ∀ R A F, equiv R A → F: A ⇒ A →
  compatible R A F → ∃F', F': A/R ⇒ A/R ∧ ∀x ∈ A, F'[[x]R] = [F[x]]R.
Proof with eauto.
  intros * Hqv [Hf [Hdf Hrf]] Hc.
  set ({λ x, <[x]R, [F[x]]R> | x ∊ A}) as F'.
  assert (Hf': is_function F'). {
    repeat split.
    (* is_relation *)
    - intros p Hp. apply ReplE in Hp as [x []]. subst p. eexists...
    - apply domE in H...
    (* single value *)
    - intros y1 y2 Hy1 Hy2. apply domE in H as [y0 Hy0].
      apply ReplE in Hy0 as [a0 [_ Heq0]].
      apply ReplE in Hy1 as [a1 [Ha1 Heq1]].
      apply ReplE in Hy2 as [a2 [Ha2 Heq2]].
      apply op_correct in Heq0 as [Heq0 _].
      apply op_correct in Heq1 as [Heq1 Hy1].
      apply op_correct in Heq2 as [Heq2 Hy2].
      subst x y1 y2. rewrite <- Heq2 in Heq1. clear Heq2.
      eapply eqvc_ident in Heq1... apply Hc in Heq1...
      subst A. apply func_correct in Ha1... apply func_correct in Ha2...
      eapply eqvc_ident; eauto + apply Hrf; eapply ranI...
  }
  assert (Hdf': dom F' = A/R). {
    apply ExtAx. split; intros Hx.
    - apply domE in Hx as [y Hp]. apply ReplE in Hp as [a [Hp Heq]].
      apply op_correct in Heq as [Heq _]. subst x. apply quotI...
    - apply quotE in Hx as [a [Ha Heq]]. eapply domI.
      apply ReplAx. exists a. split... apply op_correct...
  }
  assert (Hrf': ran F' ⊆ A/R). {
    intros y Hy. apply ranE in Hy as [].
    apply ReplE in H as [a [Ha Heq]].
    apply op_correct in Heq as [_ Hy]. subst A y.
    apply func_correct in Ha as Hp... apply ranI in Hp as Hr.
    apply Hrf in Hr. apply quotI...
  }
  exists F'. split. split... intros a Ha.
  (* F'[[x]R] = [F[x]]R *)
  assert (Hd: [a]R ∈ A/R) by (apply quotI; auto).
  rewrite <- Hdf' in Hd. apply func_correct in Hd...
  apply ReplE in Hd as [b [Hb Heq]].
  apply op_correct in Heq as [H1 H2].
  eapply eqvc_ident in H1... apply Hc in H1... subst A.
  apply func_correct in Ha as Har... apply ranI in Har.
  apply func_correct in Hb as Hbr... apply ranI in Hbr.
  apply Hrf in Har. apply Hrf in Hbr.
  apply (eqvc_ident R (dom F)) in H1... congruence.
Qed.

Theorem compatibleE : ∀ R A F, equiv R A → F: A ⇒ A →
  compatible R A F → ∃!F', F': A/R ⇒ A/R ∧ ∀x ∈ A, F'[[x]R] = [F[x]]R.
Proof with eauto.
  intros * Hqv Hf Hc. split. apply compatibleE0...
  intros F1 F2 [[HF1 [Hd1 Hr1]] H1] [[HF2 [Hd2 Hr2]] H2].
  apply func_ext... rewrite Hd1, Hd2...
  intros x Hx. rewrite Hd1 in Hx. apply quotE in Hx as [a [Ha Heq]].
  apply H1 in Ha as Heq1. apply H2 in Ha as Heq2. congruence.
Qed.

Theorem compatibleI : ∀ R A F, equiv R A → F: A ⇒ A →
  (∃F', F': A/R ⇒ A/R ∧ ∀x ∈ A, F'[[x]R] = [F[x]]R) →
  compatible R A F.
Proof with eauto.
  intros * Hqv [HF [Hd Hr]] [F' [[HF' [Hd' Hr']] H]].
  intros a Ha b Hb Hp. subst A.
  apply func_correct in Ha as Hp1... apply ranI in Hp1.
  apply func_correct in Hb as Hp2... apply ranI in Hp2.
  apply Hr in Hp1. apply Hr in Hp2.
  apply (eqvc_ident R (dom F)) in Hp...
  assert (Ha': [a]R ∈ dom F') by (rewrite Hd'; apply quotI; auto).
  apply func_correct in Ha'... assert (Hb' := Ha').
  rewrite Hp in Hb' at 2.
  assert (F'[[a]R] = F'[[b]R]) by (eapply func_sv; eauto).
  apply H in Ha. apply H in Hb.
  eapply eqvc_ident... congruence.
Qed.

(** 序关系 **)

(* 三分律 *)
Definition trich : set → set → Prop := λ R A, ∀ x y ∈ A,
  <x, y> ∈ R ∧ x ≠ y ∧ <y, x> ∉ R ∨
  <x, y> ∉ R ∧ x = y ∧ <y, x> ∉ R ∨
  <x, y> ∉ R ∧ x ≠ y ∧ <y, x> ∈ R.

(* 全序 *)
Definition totalOrd : set → set → Prop := λ R A,
  rel R A ∧ tranr R ∧ trich R A.

Definition irreflexive : set → set → Prop := λ R A,
  ¬ ∃ x ∈ A, <x, x> ∈ R.

Definition connected : set → set → Prop := λ R A,
  ∀ x y ∈ A, x ≠ y → <x, y> ∈ R ∨ <y, x> ∈ R.

Theorem totalOrd_irreflexive : ∀ R A,
  totalOrd R A → irreflexive R A.
Proof. intros * [_ [_ Htri]] [x [Hx Hp]]. firstorder. Qed.

Theorem totalOrd_connected : ∀ R A,
  totalOrd R A → connected R A.
Proof. intros * [_ [_ Htri]] x Hx y Hy Hnq. firstorder. Qed.

Theorem trich_iff : ∀ R A, rel R A → tranr R →
  trich R A ↔ irreflexive R A ∧ connected R A.
Proof with eauto; try congruence.
  intros * Hrl Htr. split; intros.
  - firstorder.
  - intros x Hx y Hy. destruct H as [Hir Hco].
    destruct (classic (x = y)).
    + right. left. repeat split...
      * intros Hp. apply Hir. exists x. split...
      * intros Hp. apply Hir. exists x. split...
    + destruct (Hco x Hx y Hy H).
      * left. repeat split...
        intros Hp. apply Hir. exists x. split...
      * right. right. repeat split...
        intros Hp. apply Hir. exists x. split...
Qed.
