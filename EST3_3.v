(** Based on "Elements of Set Theory" Chapter 3 Part 3 **)
(** Coq coding by choukh, May 2020 **)

Require Export ZFC.EST3_2.

(*** EST第三章3：等价关系，等价类，商集，三歧性，线序 ***)

(* 在A上的二元关系R *)
Definition is_binRel : set → set → Prop := λ R A, R ⊆ A × A.

Definition BinRel : set → (set → set → Prop) → set :=
  λ A P, Rel A A P.

Lemma binRelI : ∀ A (P : set → set → Prop), ∀ a b ∈ A,
  P a b → <a, b> ∈ BinRel A P.
Proof.
  intros * a Ha b Hb H. apply SepI.
  apply CProdI; auto. zfc_simple.
Qed.

Lemma binRelE1 : ∀ A P p,
  p ∈ BinRel A P → ∃a ∈ A, ∃b ∈ A, p = <a, b> ∧ P a b.
Proof with auto.
  intros. apply SepE in H as [Hp H].
  apply CProdE1 in Hp as [a [Ha [b [Hb Hp]]]]. subst p.
  zfc_simple. exists a. split... exists b. split...
Qed.

Lemma binRelE2 : ∀ A P a b,
  <a, b> ∈ BinRel A P → a ∈ A ∧ b ∈ A ∧ P a b.
Proof.
  intros. apply SepE in H as [Hp H].
  apply CProdE2 in Hp as [Ha Hb]. zfc_simple. split; auto.
Qed.

Lemma binRelE3 : ∀ A P a b,
  <a, b> ∈ BinRel A P → P a b.
Proof.
  intros. apply binRelE2 in H as [_ [_ H]]. apply H.
Qed.

Lemma binRel_is_binRel : ∀ A P, is_binRel (BinRel A P) A.
Proof.
  intros * p Hp.
  apply binRelE1 in Hp as [a [Ha [b [Hb [Hp _]]]]].
  subst p. apply CProdI; auto.
Qed.

Lemma binRel_is_rel : ∀ R A, is_binRel R A → is_rel R.
Proof.
  intros * H p Hp. apply H in Hp. apply cprod_is_pairs in Hp. apply Hp.
Qed.

Lemma dom_binRel : ∀ R A, is_binRel R A → dom R ⊆ A.
Proof.
  intros * Hr x Hx. apply domE in Hx as [y Hp].
  apply Hr in Hp. apply CProdE2 in Hp as [Hx _]. apply Hx.
Qed.

Lemma ran_binRel : ∀ R A, is_binRel R A → ran R ⊆ A.
Proof.
  intros * Hr x Hx. apply ranE in Hx as [y Hp].
  apply Hr in Hp. apply CProdE2 in Hp as [_ Hx]. apply Hx.
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
  is_binRel R A ∧ refl R A ∧ symm R ∧ tranr R.

Theorem equiv_fld : ∀ R, is_rel R →
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
Notation "[ x ] R" := (EquivClass x R) (at level 35, format "[ x ] R") : ZFC_scope.

Lemma eqvcI : ∀ R x y, <x, y> ∈ R → y ∈ [x]R.
Proof with eauto. intros. apply SepI... eapply ranI... Qed.

Lemma eqvcE : ∀ R x y, y ∈ [x]R → <x, y> ∈ R.
Proof. intros. apply SepE2 in H. apply H. Qed.

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

(* 划分 *)
Definition partition : set → set → Prop := λ Π A,
  (* 子集 *) (∀B ∈ Π, ⦿ B ∧ B ⊆ A) ∧ 
  (* 不交 *) (∀ X Y ∈ Π, X ≠ Y → disjoint X Y) ∧
  (* 穷尽 *) ∀x ∈ A, ∃X ∈ Π, x ∈ X.

(* 商集：等价类的集合 *)
Definition Quotient : set → set → set := λ R A,
  {λ x, [x]R | x ∊ A}.
Notation "A / R" := (Quotient R A) : ZFC_scope.

Lemma quotI : ∀ R A, ∀a ∈ A, [a]R ∈ A / R.
Proof. intros * a Ha. apply ReplAx. exists a. split; auto. Qed.

Lemma quotE : ∀ R A, ∀x ∈ A / R, ∃a ∈ A, [a]R = x.
Proof.
  intros * x Hx. apply ReplAx in Hx as [a [Ha Heq]].
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
      apply CProdE2 in Hx as [_ Hx]...
  - intros X HX Y HY Hnq. apply EmptyI.
    intros t Ht. apply Hnq. apply BInterE in Ht as [H1 H2].
    apply ReplAx in HX as [x [Hx Hxeq]].
    apply ReplAx in HY as [y [Hy Hyeq]]. subst X Y.
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
    (* is_rel *)
    - intros p Hp. apply ReplAx in Hp as [x []]. subst p. eexists...
    - apply domE in H...
    (* single value *)
    - intros y1 y2 Hy1 Hy2. apply domE in H as [y0 Hy0].
      apply ReplAx in Hy0 as [a0 [_ Heq0]].
      apply ReplAx in Hy1 as [a1 [Ha1 Heq1]].
      apply ReplAx in Hy2 as [a2 [Ha2 Heq2]].
      apply op_iff in Heq0 as [Heq0 _].
      apply op_iff in Heq1 as [Heq1 Hy1].
      apply op_iff in Heq2 as [Heq2 Hy2].
      subst x y1 y2. rewrite <- Heq2 in Heq1. clear Heq2.
      eapply eqvc_ident in Heq1... apply Hc in Heq1...
      subst A. apply func_correct in Ha1... apply func_correct in Ha2...
      eapply eqvc_ident; eauto + apply Hrf; eapply ranI...
  }
  assert (Hdf': dom F' = A/R). {
    apply ExtAx. split; intros Hx.
    - apply domE in Hx as [y Hp]. apply ReplAx in Hp as [a [Hp Heq]].
      apply op_iff in Heq as [Heq _]. subst x. apply quotI...
    - apply quotE in Hx as [a [Ha Heq]]. eapply domI.
      apply ReplAx. exists a. split... apply op_iff...
  }
  assert (Hrf': ran F' ⊆ A/R). {
    intros y Hy. apply ranE in Hy as [].
    apply ReplAx in H as [a [Ha Heq]].
    apply op_iff in Heq as [_ Hy]. subst A y.
    apply func_correct in Ha as Hp... apply ranI in Hp as Hr.
    apply Hrf in Hr. apply quotI...
  }
  exists F'. split. split... intros a Ha.
  (* F'[[x]R] = [F[x]]R *)
  assert (Hd: [a]R ∈ A/R) by (apply quotI; auto).
  rewrite <- Hdf' in Hd. apply func_correct in Hd...
  apply ReplAx in Hd as [b [Hb Heq]].
  apply op_iff in Heq as [H1 H2].
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
  apply func_ext_intro... rewrite Hd1, Hd2...
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

(* 三歧性 *)
Definition trich : set → set → Prop := λ R A, ∀ x y ∈ A,
  <x, y> ∈ R ∧ x ≠ y ∧ <y, x> ∉ R ∨
  <x, y> ∉ R ∧ x = y ∧ <y, x> ∉ R ∨
  <x, y> ∉ R ∧ x ≠ y ∧ <y, x> ∈ R.

(* 严格全序，线序 *)
Definition linearOrder : set → set → Prop := λ R A,
  is_binRel R A ∧ tranr R ∧ trich R A.

(* 反自反性 *)
Definition irrefl : set → Prop := λ R,
  ∀ x, <x, x> ∉ R.

(* 连通性 *)
Definition connected : set → set → Prop := λ R A,
  ∀ x y ∈ A, x ≠ y → <x, y> ∈ R ∨ <y, x> ∈ R.

Theorem lo_irrefl : ∀ R A,
  linearOrder R A → irrefl R.
Proof.
  intros * [Hrl [_ Htri]] x Hp. apply Hrl in Hp as Hx.
  apply CProdE2 in Hx as [Hx _]. firstorder.
Qed.

Theorem lo_connected : ∀ R A,
  linearOrder R A → connected R A.
Proof. intros * [_ [_ Htri]] x Hx y Hy Hnq. firstorder. Qed.

Theorem trich_iff : ∀ R A, is_binRel R A → tranr R →
  trich R A ↔ irrefl R ∧ connected R A.
Proof with eauto; try congruence.
  intros * Hrl Htr. split; intros.
  - split. eapply lo_irrefl. split...
    apply lo_connected. split...
  - intros x Hx y Hy. destruct H as [Hir Hco].
    destruct (classic (x = y)).
    + right. left. subst. repeat split...
    + destruct (Hco x Hx y Hy H).
      * left. repeat split...
        intros Hp. eapply Hir...
      * right. right. repeat split...
        intros Hp. eapply Hir...
Qed.
