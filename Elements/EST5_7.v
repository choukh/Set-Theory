(** Adapted from "Elements of Set Theory" Chapter 5 **)
(** Coq coding by choukh, July 2020 **)

Require Export ZFC.Elements.EST5_6.
Require Import ZFC.Lib.FuncFacts.

(*** EST第五章7：实数乘法，乘法逆元，有理数嵌入，实数的稠密性 ***)

(** 实数乘法 **)
Definition RealMul : set → set → set := λ x y,
  match (ixm (realNeg x)) with
  | inl _ =>
    match (ixm (realNeg y)) with
    | inl _ => |x| ⋅₊ |y|
    | inr _ => -(|x| ⋅₊ |y|)
    end
  | inr _ =>
    match (ixm (realNeg y)) with
    | inl _ => -(|x| ⋅₊ |y|)
    | inr _ => x ⋅₊ y
    end
  end.
Notation "x ⋅ y" := (RealMul x y) : Real_scope.

Local Ltac destruct_realMul x y :=
  unfold RealMul;
  destruct (ixm (realNeg x)) as [?Hnx|?Hnnx];
  destruct (ixm (realNeg y)) as [?Hny|?Hnny];
  assert_succeeds (exfalso; auto).

Local Ltac abs := auto;
  try (apply realAbs_ran; auto);
  try (apply realAbs_nonNeg; auto).
Local Ltac mr := apply realNonNegMul_ran; auto.
Local Ltac nn := auto; apply realNonNeg_not_neg; auto.

Theorem realMul_ran : ∀ x y ∈ ℝ, x ⋅ y ∈ ℝ.
Proof with auto.
  intros x Hx y Hy.
  destruct_realMul x y.
  - mr;abs.
  - apply realAddInv_ran. mr;abs.
  - apply realAddInv_ran. mr;abs.
  - apply realNonNegMul_ran; nn.
Qed.

Theorem realMul_comm : ∀ x y ∈ ℝ, x ⋅ y = y ⋅ x.
Proof with auto.
  intros x Hx y Hy. unfold RealMul.
  destruct_realMul x y.
  - apply realNonNegMul_comm; abs.
  - cut (|x| ⋅₊ |y| = |y| ⋅₊ |x|). congruence.
    apply realNonNegMul_comm; abs.
  - cut (|x| ⋅₊ |y| = |y| ⋅₊ |x|). congruence.
    apply realNonNegMul_comm; abs.
  - apply realNonNegMul_comm; nn.
Qed.

Lemma realNeg_neq_0 : ∀x ∈ ℝ, realNeg x → x ≠ Real 0.
Proof.
  intros x Hx Hnx.
  pose proof (realLt_trich _ Hx _ (real_n 0)) as []; tauto.
Qed.

Lemma realAbs_pos : ∀x ∈ ℝ, x ≠ Real 0 → realPos (|x|).
Proof with nauto.
  intros x Hx Hx0.
  assert (Ha: |x| ∈ ℝ) by abs.
  assert (Hnna: realNonNeg (|x|)) by (apply realAbs_nonNeg; auto).
  destruct Hnna.
  pose proof (realLt_trich _ Ha _ (real_n 0)) as []; tauto.
  exfalso. apply Hx0. apply realAbs_eq_0...
Qed.

Lemma realAbs_prd_nn : ∀ x y ∈ ℝ, ¬realNeg (|x| ⋅₊ |y|).
Proof.
  intros x Hx y Hy. apply realNonNeg_not_neg. mr;abs.
  apply realNonNegMul_nonNeg_prd; abs.
Qed.

Lemma realAbs_prd_id : ∀ x y ∈ ℝ, | |x| ⋅₊ |y| | = |x| ⋅₊ |y|.
Proof.
  intros x Hx y Hy. apply realAbs_nonNeg_id.
  apply realNonNegMul_nonNeg_prd; abs.
Qed.

Theorem realMul_assoc : ∀ x y z ∈ ℝ,
  (x ⋅ y) ⋅ z = x ⋅ (y ⋅ z).
Proof with auto.
  intros x Hx y Hy z Hz.
  unfold RealMul;
    destruct (ixm (realNeg x)) as [Hnx|Hnnx];
    destruct (ixm (realNeg y)) as [Hny|Hnny];
    destruct (ixm (realNeg z)) as [Hnz|Hnnz].
  - destruct_realMul (|x| ⋅₊ |y|) (|y| ⋅₊ |z|);
      [exfalso; eapply realAbs_prd_nn; revgoals; eauto..|].
    repeat rewrite realAbs_prd_id...
    cut ((|x| ⋅₊ |y|) ⋅₊ |z| = |x| ⋅₊ (|y| ⋅₊ |z|)). congruence.
    rewrite realNonNegMul_assoc; abs.
  - destruct_realMul (|x| ⋅₊ |y|) (-(|y| ⋅₊ |z|));
      [exfalso; eapply realAbs_prd_nn; revgoals; eauto..| |].
    + apply realNonNeg_not_neg in Hnnz...
      rewrite realAbs_unsigned; [|mr;abs].
      rewrite realAbs_prd_id, (realAbs_nonNeg_id _ Hnnz)...
      rewrite realNonNegMul_assoc; abs.
    + destruct (classic (z = Real 0)).
      * subst. rewrite (realAbs_nonNeg_id (Real 0)); [|right]...
        rewrite realNonNegMul_0_r_r, realNonNegMul_0_r_r, realAddInv_0; [|abs|mr;abs].
        rewrite (realAbs_nonNeg_id (Real 0)); [|right]...
        rewrite realNonNegMul_0_r_r, realAddInv_0; auto; abs.
      * exfalso. apply Hnny. apply realPos_neg.
        apply realNonNegMul_pos_prd; abs; apply realAbs_pos...
        apply realNeg_neq_0...
  - destruct_realMul (-(|x| ⋅₊ |y|)) (-(|y| ⋅₊ |z|)).
    + repeat rewrite realAbs_unsigned; [|mr;abs..].
      repeat rewrite realAbs_prd_id... rewrite realNonNegMul_assoc; abs.
    + destruct (classic (y = Real 0)); [|destruct (classic (z = Real 0))].
      * subst. rewrite (realAbs_nonNeg_id (Real 0)); [|right]...
        rewrite realNonNegMul_0_r_r, realNonNegMul_0_l, realAddInv_0; abs.
        rewrite (realAbs_nonNeg_id (Real 0)); [|right]...
        rewrite realNonNegMul_0_l, realNonNegMul_0_r_r, realAddInv_0; abs.
      * subst. rewrite (realAbs_nonNeg_id (Real 0)); [|right]...
        rewrite realNonNegMul_0_r_r, realNonNegMul_0_r_r, realAddInv_0;
          [|abs|abs; apply realAddInv_ran; mr;abs].
        rewrite (realAbs_nonNeg_id (Real 0)); [|right]...
        rewrite realNonNegMul_0_r_r, realAddInv_0; auto; abs.
      * exfalso. apply Hnny0. apply realPos_neg.
        apply realNonNegMul_pos_prd; abs; apply realAbs_pos...
    + destruct (classic (y = Real 0)).
      * subst. rewrite (realAbs_nonNeg_id (Real 0)); [|right]...
        rewrite realNonNegMul_0_r_r, realNonNegMul_0_l, realAddInv_0; abs.
        rewrite (realAbs_nonNeg_id (Real 0)); [|right]...
        rewrite realNonNegMul_0_l, realNonNegMul_0_r_r, realAddInv_0; abs.
      * exfalso. apply Hnnx. apply realPos_neg.
        apply realNonNegMul_pos_prd; abs; apply realAbs_pos...
        apply realNeg_neq_0...
    + destruct (classic (y = Real 0)).
      * subst. rewrite (realAbs_nonNeg_id (Real 0)); [|right]...
        rewrite realNonNegMul_0_r_r, realNonNegMul_0_l, realAddInv_0; abs.
        rewrite (realAbs_nonNeg_id (Real 0)); [|right]...
        rewrite realNonNegMul_0_l, realNonNegMul_0_r_r, realAddInv_0; abs.
      * exfalso. apply Hnnx. apply realPos_neg.
        apply realNonNegMul_pos_prd; abs; apply realAbs_pos...
        apply realNeg_neq_0...
  - apply realNonNeg_not_neg in Hnny...
    apply realNonNeg_not_neg in Hnnz...
    destruct_realMul (-(|x| ⋅₊ |y|)) (y ⋅₊ z).
    + exfalso. apply realNeg_not_nonNeg in Hny; [|mr].
      apply Hny. apply realNonNegMul_nonNeg_prd...
    + rewrite realAbs_unsigned; [|mr;abs].
      rewrite <- (realAbs_nonNeg_id _ Hnny) at 2.
      rewrite <- (realAbs_nonNeg_id _ Hnnz) at 2.
      repeat rewrite realAbs_prd_id... rewrite realNonNegMul_assoc; abs.
    + destruct (classic (y = Real 0)).
      * subst. rewrite (realAbs_nonNeg_id (Real 0)); [|right]...
        rewrite realNonNegMul_0_r_r, realNonNegMul_0_l, realAddInv_0; abs.
        rewrite (realAbs_nonNeg_id (Real 0)); [|right]...
        rewrite realNonNegMul_0_l, realNonNegMul_0_r_r; abs.
      * exfalso. apply Hnnx. apply realPos_neg.
        apply realNonNegMul_pos_prd; abs; apply realAbs_pos...
        apply realNeg_neq_0...
    + destruct (classic (y = Real 0)).
      * subst. rewrite (realAbs_nonNeg_id (Real 0)); [|right]...
        rewrite realNonNegMul_0_r_r, realNonNegMul_0_l, realAddInv_0; abs.
        rewrite (realAbs_nonNeg_id (Real 0)); [|right]...
        rewrite realNonNegMul_0_l, realNonNegMul_0_r_r, realAddInv_0; abs.
      * exfalso. apply Hnnx. apply realPos_neg.
        apply realNonNegMul_pos_prd; abs; apply realAbs_pos...
        apply realNeg_neq_0...
  - apply realNonNeg_not_neg in Hnnx...
    destruct_realMul (-(|x| ⋅₊ |y|)) (|y| ⋅₊ |z|);
      [exfalso; eapply realAbs_prd_nn; revgoals; eauto| |
       exfalso; eapply realAbs_prd_nn; revgoals; eauto|].
    + rewrite realAbs_unsigned; [|mr;abs].
      rewrite <- (realAbs_nonNeg_id _ Hnnx) at 2.
      repeat rewrite realAbs_prd_id... rewrite realNonNegMul_assoc; abs.
    + destruct (classic (x = Real 0)).
      * subst. rewrite (realAbs_nonNeg_id (Real 0)); [|right]...
        rewrite realNonNegMul_0_l, realNonNegMul_0_l, realAddInv_0; [|mr;abs|abs].
        rewrite (realAbs_nonNeg_id (Real 0)); [|right]...
        rewrite realNonNegMul_0_l, realAddInv_0; abs.
      * exfalso. apply Hnnx0. apply realPos_neg.
        apply realNonNegMul_pos_prd; abs; apply realAbs_pos...
        apply realNeg_neq_0...
  - apply realNonNeg_not_neg in Hnnx...
    apply realNonNeg_not_neg in Hnnz...
    destruct_realMul (-(|x| ⋅₊ |y|)) (-(|y| ⋅₊ |z|)).
    + repeat rewrite realAbs_unsigned; [|mr;abs..].
      repeat rewrite realAbs_prd_id... rewrite realNonNegMul_assoc; abs.
    + destruct (classic (z = Real 0)).
      * subst. rewrite (realAbs_nonNeg_id (Real 0)); [|right]...
        rewrite realNonNegMul_0_r_r, realNonNegMul_0_r_r,
          realAddInv_0, realNonNegMul_0_r_r; abs.
        apply realAddInv_ran. mr; abs.
      * exfalso. apply Hnny. apply realPos_neg.
        apply realNonNegMul_pos_prd; abs; apply realAbs_pos...
        apply realNeg_neq_0...
    + destruct (classic (x = Real 0)).
      * subst. rewrite (realAbs_nonNeg_id (Real 0)); [|right]...
        rewrite realNonNegMul_0_l, realNonNegMul_0_l,
          realAddInv_0, realNonNegMul_0_l; abs.
        apply realAddInv_ran. mr; abs.
      * exfalso. apply Hnnx0. apply realPos_neg.
        apply realNonNegMul_pos_prd; abs; apply realAbs_pos...
        apply realNeg_neq_0...
    + destruct (classic (x = Real 0)).
      * subst. rewrite (realAbs_nonNeg_id (Real 0)); [|right]...
        rewrite realNonNegMul_0_l, realNonNegMul_0_l,
          realAddInv_0, realNonNegMul_0_l; abs.
        apply realAddInv_ran. mr; abs.
      * exfalso. apply Hnnx0. apply realPos_neg.
        apply realNonNegMul_pos_prd; abs; apply realAbs_pos...
        apply realNeg_neq_0...
  - apply realNonNeg_not_neg in Hnnx...
    apply realNonNeg_not_neg in Hnny...
    destruct_realMul (x ⋅₊ y) (-(|y| ⋅₊ |z|)).
    + exfalso. apply realNeg_not_nonNeg in Hnx; [|mr].
      apply Hnx. apply realNonNegMul_nonNeg_prd...
    + exfalso. apply realNeg_not_nonNeg in Hnx; [|mr].
      apply Hnx. apply realNonNegMul_nonNeg_prd...
    + rewrite realAbs_unsigned; [|mr;abs..].
      rewrite <- (realAbs_nonNeg_id _ Hnnx) at 1.
      rewrite <- (realAbs_nonNeg_id _ Hnny) at 1.
      rewrite realAbs_prd_id, realAbs_prd_id, realNonNegMul_assoc; abs.
    + destruct (classic (y = Real 0)).
      * subst. rewrite (realAbs_nonNeg_id (Real 0)); [|right]...
        rewrite realNonNegMul_0_r_r, realNonNegMul_0_l, realAddInv_0; abs.
        rewrite (realAbs_nonNeg_id (Real 0)); [|right]...
        rewrite realNonNegMul_0_l, realNonNegMul_0_r_r, realAddInv_0; abs.
      * exfalso. apply Hnny0. apply realPos_neg.
        apply realNonNegMul_pos_prd; abs; apply realAbs_pos...
        apply realNeg_neq_0...
  - apply realNonNeg_not_neg in Hnnx...
    apply realNonNeg_not_neg in Hnny...
    apply realNonNeg_not_neg in Hnnz...
    destruct_realMul (x ⋅₊ y) (y ⋅₊ z).
    + exfalso. apply realNeg_not_nonNeg in Hnx; [|mr].
      apply Hnx. apply realNonNegMul_nonNeg_prd...
    + exfalso. apply realNeg_not_nonNeg in Hnx; [|mr].
      apply Hnx. apply realNonNegMul_nonNeg_prd...
    + exfalso. apply realNeg_not_nonNeg in Hny; [|mr].
      apply Hny. apply realNonNegMul_nonNeg_prd...
    + rewrite realNonNegMul_assoc; abs.
Qed.

Lemma realAbs_sum_id : ∀ x y ∈ ℝ, | |x| + |y| | = |x| + |y|.
Proof.
  intros x Hx y Hy. apply realAbs_nonNeg_id.
  apply realAdd_nonNeg_sum; abs.
Qed.

Lemma realAbs_sum : ∀ x y ∈ ℝ,
  realNeg x → realNeg y → |x + y| = |x| + |y|.
Proof with auto.
  intros x Hx y Hy Hnx Hny.
  apply realNeg_nonPos in Hnx...
  apply realNeg_nonPos in Hny...
  rewrite <- (realAddInv_double x) at 1...
  rewrite <- (realAddInv_double y) at 1...
  rewrite <- (realAbs_nonPos_flip _ Hnx).
  rewrite <- (realAbs_nonPos_flip _ Hny).
  rewrite <- realAddInv_sum, realAbs_unsigned, realAbs_sum_id; abs.
  apply realAdd_ran; abs.
Qed.

Lemma realAbs_diff : ∀ x y ∈ ℝ,
  realNonPos x → realNonNeg y → x + y = |y| - |x|.
Proof with auto.
  intros x Hx y Hy Hnpx Hnny.
  rewrite (realAbs_nonPos_flip _ Hnpx), realAddInv_double,
    (realAbs_nonNeg_id _ Hnny), realAdd_comm...
Qed.

Theorem realMul_distr : ∀ x y z ∈ ℝ,
  x ⋅ (y + z) = x ⋅ y + x ⋅ z.
Proof with auto.
  intros x Hx y Hy z Hz.
  assert (Hr1: |x| ⋅₊ |y| ∈ ℝ) by (mr;abs).
  assert (Hr2: |x| ⋅₊ |z| ∈ ℝ) by (mr;abs).
  assert (Hr3: -(|x| ⋅₊ |y|) ∈ ℝ) by (apply realAddInv_ran; auto).
  assert (Hr4: y + z ∈ ℝ) by (apply realAdd_ran; auto).
  assert (H1: ∀ u v w ∈ ℝ, realNeg v → ¬realNeg w → realNeg (v + w) →
    |u| ⋅₊ |v + w| = |u| ⋅₊ |v| - |u| ⋅₊ |w|). {
    intros u Hu v Hv w Hw Hnv Hnnw H.
    apply realNeg_nonPos in Hnv...
    apply realNonNeg_not_neg in Hnnw...
    apply realNeg_nonPos in H; [|apply realAdd_ran]...
    rewrite realAbs_diff... rewrite realAbs_diff in H...
    rewrite (realAbs_nonPos_flip _ H).
    apply realNonPos_nonNeg in H;
      [|apply realAdd_ran; abs; apply realAddInv_ran; abs].
    rewrite realAddInv_diff in *; abs.
    rewrite realNonNegMul_distr'; abs.
  }
  assert (H2: ∀ u v w ∈ ℝ, realNeg v → ¬realNeg w → ¬realNeg (v + w) →
    -(|u| ⋅₊ |v + w|) = |u| ⋅₊ |v| - |u| ⋅₊ |w|). {
    intros u Hu v Hv w Hw Hnv Hnnw H.
    apply realNeg_nonPos in Hnv...
    apply realNonNeg_not_neg in Hnnw...
    apply realNonNeg_not_neg in H; [|apply realAdd_ran]...
    rewrite realAbs_diff... rewrite realAbs_diff in H...
    rewrite (realAbs_nonNeg_id _ H), realNonNegMul_distr',
      realAddInv_diff; abs; mr; abs.
  }
  unfold RealMul;
    destruct (ixm (realNeg x)) as [Hnx|Hnnx];
    destruct (ixm (realNeg y)) as [Hny|Hnny];
    destruct (ixm (realNeg z)) as [Hnz|Hnnz];
    destruct (ixm (realNeg (y + z))) as [H|H].
  - rewrite realAbs_sum, realNonNegMul_distr; abs.
  - exfalso. apply H. apply realAdd_neg_sum...
  - apply H1... - apply H2...
  - rewrite (realAdd_comm y) in *...
    rewrite (realAdd_comm (-(|x| ⋅₊ |y|)))...
  - rewrite (realAdd_comm y) in *...
    rewrite (realAdd_comm (-(|x| ⋅₊ |y|)))...
  - exfalso. apply realNeg_not_nonNeg in H... apply H.
    apply realNonNeg_not_neg in Hnny...
    apply realNonNeg_not_neg in Hnnz... apply realAdd_nonNeg_sum...
  - apply realNonNeg_not_neg in Hnny...
    apply realNonNeg_not_neg in Hnnz...
    rewrite <- (realAbs_nonNeg_id _ Hnny) at 1.
    rewrite <- (realAbs_nonNeg_id _ Hnnz) at 1.
    rewrite realAbs_sum_id, realNonNegMul_distr, realAddInv_sum; abs.
  - rewrite realAbs_sum, realNonNegMul_distr, realAddInv_sum; abs.
  - exfalso. apply H. apply realAdd_neg_sum...
  - rewrite (H1 _ Hx _ Hy _ Hz Hny Hnnz H).
    apply realNonNeg_not_neg in Hnnx...
    apply realNonNeg_not_neg in Hnnz...
    rewrite <- (realAbs_nonNeg_id _ Hnnx) at 4.
    rewrite <- (realAbs_nonNeg_id _ Hnnz) at 2.
    rewrite realAddInv_diff, realAdd_comm...
  - apply realNonNeg_not_neg in Hnnx as Hnnx'...
    apply realNonNeg_not_neg in Hnnz as Hnnz'...
    apply realNonNeg_not_neg in H as H'...
    rewrite <- (realAbs_nonNeg_id _ Hnnx') at 1 3.
    rewrite <- (realAbs_nonNeg_id _ H')...
    rewrite <- (realAbs_nonNeg_id _ Hnnz') at 2.
    rewrite (realAdd_comm (-(|x| ⋅₊ |y|))), <- realAddInv_diff...
    rewrite <- (H2 _ Hx _ Hy _ Hz Hny Hnnz H).
    rewrite realAddInv_double; [|mr;abs]...
  - rewrite (realAdd_comm y) in *...
    rewrite (H1 _ Hx _ Hz _ Hy Hnz Hnny H), realAddInv_diff...
    apply realNonNeg_not_neg in Hnnx...
    apply realNonNeg_not_neg in Hnny...
    rewrite (realAbs_nonNeg_id _ Hnnx), (realAbs_nonNeg_id _ Hnny)...
  - apply realNonNeg_not_neg in Hnnx as Hnnx'...
    apply realNonNeg_not_neg in Hnny as Hnny'...
    apply realNonNeg_not_neg in H as H'...
    rewrite <- (realAbs_nonNeg_id _ Hnnx') at 1 2.
    rewrite <- (realAbs_nonNeg_id _ H')...
    rewrite <- (realAbs_nonNeg_id _ Hnny') at 2.
    rewrite (realAdd_comm y) in *...
    rewrite <- realAddInv_diff, <- (H2 _ Hx _ Hz _ Hy Hnz Hnny H),
      realAddInv_double; auto; mr; abs.
  - apply realNonNeg_not_neg in Hnny...
    apply realNonNeg_not_neg in Hnnz...
    apply realNeg_not_nonNeg in H... exfalso. apply H.
    apply realAdd_nonNeg_sum...
  - rewrite realNonNegMul_distr; abs; apply realNonNeg_not_neg...
Qed.

Corollary realMul_distr' : ∀ x y z ∈ ℝ,
  (y + z) ⋅ x = y ⋅ x + z ⋅ x.
Proof with auto.
  intros x Hx y Hy z Hz.
  rewrite realMul_comm, (realMul_comm y), (realMul_comm z)...
  apply realMul_distr... apply realAdd_ran...
Qed.

Theorem realMul_0_r_r : ∀x ∈ ℝ, x ⋅ Real 0 = Real 0.
Proof with neauto.
  intros x Hx. unfold RealMul.
  destruct_realMul x (Real 0).
  - exfalso. eapply realLt_irrefl...
  - apply realNonNeg_not_neg in Hnny...
    rewrite (realAbs_nonNeg_id _ Hnny),
      realNonNegMul_0_r_r, realAddInv_0; abs.
  - exfalso. eapply realLt_irrefl...
  - rewrite realNonNegMul_0_r_r...
Qed.

Corollary realMul_0_l : ∀x ∈ ℝ, Real 0 ⋅ x = Real 0.
Proof with nauto.
  intros x Hx. rewrite realMul_comm, realMul_0_r_r...
Qed.

Theorem realMul_1_r : ∀x ∈ ℝ, x ⋅ Real 1 = x.
Proof with neauto.
  intros x Hx. unfold RealMul.
  destruct_realMul x (Real 1).
  - exfalso. apply realNeg_not_nonNeg in Hny...
    apply Hny. apply realPos_nonNeg...
  - apply realNeg_nonPos in Hnx...
    apply realNonNeg_not_neg in Hnny...
    rewrite (realAbs_nonNeg_id _ Hnny), realNonNegMul_1_r; abs.
    rewrite (realAbs_nonPos_flip _ Hnx), realAddInv_double...
  - exfalso. apply realNeg_not_nonNeg in Hny...
    apply Hny. apply realPos_nonNeg...
  - rewrite realNonNegMul_1_r... apply realNonNeg_not_neg...
Qed.

Corollary realMul_1_l : ∀x ∈ ℝ, Real 1 ⋅ x = x.
Proof with nauto.
  intros x Hx. rewrite realMul_comm, realMul_1_r...
Qed.

(* 非零实数 *)
Definition ℝ' := (ℝ - {Real 0,})%set.

Lemma nzRealI0 : ∀x ∈ ℝ, x ≠ Real 0 → x ∈ ℝ'.
Proof with auto.
  intros x Hx H0. apply CompI... apply SingNI...
Qed.

Lemma nzRealI1 : ∀ n : nat, Real (S n) ∈ ℝ'.
Proof with neauto.
  intros. apply CompI... apply SingNI...
Qed.
Global Hint Immediate nzRealI1 : number_hint.

Lemma nzRealE : ∀x ∈ ℝ', x ∈ ℝ ∧ x ≠ Real 0.
Proof with auto.
  intros x Hx. apply CompE in Hx as [Hx H0].
  split... apply SingNE in H0...
Qed.

Lemma real_sn : ∀ n, Real (S n) ∈ ℝ'.
Proof.
  intros. apply CompI; nauto.
  apply SingNI. apply real_suc_neq_0.
Qed.
Global Hint Immediate real_sn : number_hint.

Lemma realPosMulInv_ran' : ∀x ∈ ℝ, realPos x → (x⁻¹⁺)%r ∈ ℝ'.
Proof with nauto.
  intros x Hx Hpx.
  assert (Hrx: (x ⁻¹⁺)%r ∈ ℝ) by (apply realPosMulInv_ran; auto).
  apply nzRealI0... intros Heq.
  assert (Rat 0 ∉ (x ⁻¹⁺)%r) by (apply realLt_realn'; auto).
  pose proof (realE1 _ Hx) as [r [Hrq Hleft]].
  apply H. apply SepI... exists r. repeat split...
  rewrite ratMul_0_l... apply ratPos_sn...
Qed.

(** 实数乘法逆元 **)
Definition RealMulInv : set → set := λ x,
  match (ixm (x = Real 0)) with
  | inl _ => ∅
  | inr _ =>
    match (ixm (realPos x)) with
    | inl _ => x⁻¹⁺
    | inr _ => -|x|⁻¹⁺
    end
  end.
Notation "x ⁻¹" := (RealMulInv x) : Real_scope.
Notation "x / y" := (x ⋅ y⁻¹) : Real_scope.

Lemma realMulInv_sub_rat : ∀x ∈ ℝ', x⁻¹ ∈ 𝒫 ℚ.
Proof with auto.
  intros x Hx. apply PowerAx. intros p Hp.
  apply nzRealE in Hx as [_ H]. unfold RealMulInv in Hp.
  destruct (ixm (x = Real 0)). exfalso...
  destruct (ixm (realPos x)); apply SepE1 in Hp...
Qed.

Lemma realMulInv_ran : ∀x ∈ ℝ', x⁻¹ ∈ ℝ.
Proof with neauto.
  intros x Hx'. unfold RealMulInv.
  apply nzRealE in Hx' as [Hx Hnq0].
  destruct (ixm (x = Real 0)). exfalso...
  destruct (ixm (realPos x)) as [Hpx|Hnx]. apply realPosMulInv_ran...
  apply realAddInv_ran... apply realNonPos_not_pos in Hnx...
  rewrite (realAbs_nonPos_flip _ Hnx).
  apply realPosMulInv_ran... apply realAddInv_ran...
  destruct Hnx; [|exfalso]... apply realNeg_pos...
Qed.

Lemma realMulInv_ran' : ∀x ∈ ℝ', x⁻¹ ∈ ℝ'.
Proof with auto.
  intros x Hx'. unfold RealMulInv.
  apply nzRealE in Hx' as [Hx Hnq0].
  destruct (ixm (x = Real 0)). exfalso...
  destruct (ixm (realPos x)) as [Hpx|Hnx].
  - apply realPosMulInv_ran'...
  - assert (Hrx: |x|⁻¹⁺ ∈ ℝ'). {
      apply realPosMulInv_ran'; abs. apply realAbs_pos...
    }
    apply nzRealE in Hrx as [Hrx Hnq].
    apply nzRealI0. apply realAddInv_ran...
    intros Heq. apply Hnq. apply realAddInv_eq_0...
Qed.

Lemma realAbs_mulInv : ∀x ∈ ℝ', |x⁻¹| = |x|⁻¹.
Proof with auto.
  intros x Hx'. unfold RealMulInv.
  apply nzRealE in Hx' as [Hx Hnq0].
  destruct (ixm (x = Real 0)). exfalso...
  destruct (ixm (realPos x)) as [Hpx|Hnx]; (
    destruct (ixm (|x| = Real 0)) as [H0|H0]; [
      apply realAbs_eq_0 in H0; auto; exfalso; auto|
      destruct (ixm (realPos (|x|))) as [Hpax|Hnax]
  ]).
  - assert (Hnnx: realNonNeg x) by (left; auto).
    assert (Hnnrx: realNonNeg x⁻¹⁺) by (left; apply realPos_posMulInv; auto).
    rewrite (realAbs_nonNeg_id _ Hnnrx), (realAbs_nonNeg_id _ Hnnx)...
  - exfalso. apply Hnax. destruct (realAbs_nonNeg _ Hx)... exfalso...
  - assert (Hnnx: realNonNeg (|x|)) by (left; auto).
    assert (Hnnrx: realNonNeg (|x|⁻¹⁺)) by (left; apply realPos_posMulInv; abs).
    rewrite realAbs_unsigned, (realAbs_nonNeg_id _ Hnnrx)...
    apply realPosMulInv_ran; abs.
  - exfalso. apply Hnax. destruct (realAbs_nonNeg _ Hx)... exfalso...
Qed.

Lemma realPos_mulInv : ∀x ∈ ℝ', realPos x → realPos (x⁻¹).
Proof with auto.
  intros x Hx' Hpx. unfold RealMulInv.
  apply nzRealE in Hx' as [Hx Hnq0].
  destruct (ixm (x = Real 0)). exfalso...
  destruct (ixm (realPos x)) as [_|Hnx]; [|exfalso]...
  apply realPos_posMulInv...
Qed.

Lemma realNeg_mulInv : ∀x ∈ ℝ', realNeg x → realNeg (x⁻¹).
Proof with auto.
  intros x Hx' Hnx. unfold RealMulInv.
  apply nzRealE in Hx' as [Hx Hnq0].
  destruct (ixm (x = Real 0)). exfalso...
  destruct (ixm (realPos x)) as [Hpx|Hnpx].
  - exfalso. apply realPos_nonNeg in Hpx...
    apply realNonNeg_not_neg in Hpx...
  - apply realPos_neg. apply realPos_posMulInv; abs.
    apply realAbs_pos...
Qed.

Theorem realMulInv_annih : ∀x ∈ ℝ', x ⋅ x⁻¹ = Real 1.
Proof with nauto.
  intros x Hx'. pose proof (nzRealE _ Hx') as [Hx Hnq0].
  destruct_realMul x (x⁻¹).
  - rewrite realAbs_mulInv... unfold RealMulInv.
    destruct (ixm (|x| = Real 0)) as [H0|H0]; [
      apply realAbs_eq_0 in H0; auto; exfalso; auto|
      destruct (ixm (realPos (|x|))) as [Hpax|Hnax]
    ].
    + apply realPosMulInv_annih; abs.
    + exfalso. apply Hnax. destruct (realAbs_nonNeg _ Hx)... exfalso...
  - exfalso. apply Hnny. apply realNeg_mulInv...
  - assert (Hrx: x⁻¹ ∈ ℝ) by (apply realMulInv_ran; auto).
    exfalso. apply realNonNeg_not_neg in Hnnx...
    destruct Hnnx... apply realPos_mulInv in H...
    apply realNeg_nonPos in Hny... apply realNonPos_not_pos in Hny...
  - unfold RealMulInv.
    destruct (ixm (x = Real 0)). exfalso...
    destruct (ixm (realPos x)) as [Hpx|Hnpx].
    + apply realPosMulInv_annih...
    + exfalso. apply realLt_connected in Hnq0 as []...
Qed.

Corollary realMulInv_double : ∀x ∈ ℝ', x⁻¹⁻¹ = x.
Proof with auto.
  intros x Hx'. pose proof (nzRealE _ Hx') as [Hx Hnq0].
  assert (Hr: x⁻¹ ∈ ℝ) by (apply realMulInv_ran; auto).
  assert (Hr': x⁻¹ ∈ ℝ') by (apply realMulInv_ran'; auto).
  assert (Hrr: x⁻¹⁻¹ ∈ ℝ) by (apply realMulInv_ran; auto).
  rewrite <- (realMul_1_r (x⁻¹⁻¹)), <- (realMulInv_annih x),
    realMul_comm, realMul_assoc, realMulInv_annih, realMul_1_r...
  apply realMul_ran...
Qed.

Corollary realMul_cancel : ∀ x y ∈ ℝ, ∀ z ∈ ℝ', x ⋅ z = y ⋅ z → x = y.
Proof with auto.
  intros x Hx y Hy z Hz' Heq.
  assert (x ⋅ z / z = y ⋅ z / z) by congruence.
  assert (Hz: z ∈ ℝ) by (apply nzRealE; auto).
  assert (Hrz: z⁻¹ ∈ ℝ) by (apply realMulInv_ran; auto).
  rewrite realMul_assoc, (realMul_assoc y) in H...
  rewrite realMulInv_annih, realMul_1_r, realMul_1_r in H...
Qed.

Corollary realMul_cancel' : ∀ x y ∈ ℝ, ∀ z ∈ ℝ', z ⋅ x = z ⋅ y → x = y.
Proof with eauto.
  intros x Hx y Hy z Hz Heq.
  eapply realMul_cancel...
  rewrite realMul_comm, (realMul_comm y); auto; apply nzRealE...
Qed.

Corollary realMulInv_1 : (Real 1)⁻¹ = Real 1.
Proof with nauto.
  eapply realMul_cancel. apply realMulInv_ran... nauto.
  apply nzRealI0. apply (real_n 1). apply real_suc_neq_0.
  rewrite realMul_comm, realMulInv_annih, realMul_1_r...
  apply realMulInv_ran...
Qed.

Corollary realMulInv_eq_1 : ∀x ∈ ℝ', x⁻¹ = Real 1 → x = Real 1.
Proof.
  intros. now rewrite <- (realMulInv_double x), H0, realMulInv_1.
Qed.

Lemma nzRealMul_ran : ∀ x y ∈ ℝ', x ⋅ y ∈ ℝ'.
Proof with nauto.
  intros x Hx' y Hy'.
  pose proof (nzRealE _ Hx') as [Hx Hx0].
  pose proof (nzRealE _ Hy') as [Hy Hy0].
  assert (Hrx: x⁻¹ ∈ ℝ) by (apply realMulInv_ran; auto).
  assert (Hry: y⁻¹ ∈ ℝ) by (apply realMulInv_ran; auto).
  apply nzRealI0. apply realMul_ran...
  assert ((x ⋅ x⁻¹) ⋅ (y ⋅ y⁻¹) = Real 1). {
    rewrite realMulInv_annih, realMulInv_annih, realMul_1_r...
  }
  rewrite realMul_assoc, (realMul_comm x⁻¹),
  (realMul_assoc y), <- realMul_assoc in H;
    try timeout 1 auto; [|apply realMul_ran; auto..].
  destruct (classic (x ⋅ y = Real 0)); [|auto].
  rewrite H0 in H. rewrite realMul_0_l in H; [|apply realMul_ran; auto].
  exfalso. eapply real_suc_neq_0. symmetry. apply H.
Qed.

Theorem real_no_0_div : ∀ x y ∈ ℝ,
  x ⋅ y = Real 0 → x = Real 0 ∨ y = Real 0.
Proof with auto.
  intros x Hx y Hy H0.
  destruct (classic (x = Real 0)) as [|Hx'];
  destruct (classic (y = Real 0)) as [|Hy']... exfalso.
  apply nzRealI0 in Hx'... apply nzRealI0 in Hy'...
  pose proof (nzRealMul_ran _ Hx' _ Hy').
  apply nzRealE in H as [_ H]...
Qed.

Corollary realMulInv_prd : ∀ x y ∈ ℝ', (x ⋅ y)⁻¹ = x⁻¹ ⋅ y⁻¹.
Proof with nauto.
  intros x Hx' y Hy'.
  pose proof (nzRealE _ Hx') as [Hx Hx0].
  pose proof (nzRealE _ Hy') as [Hy Hy0].
  assert (Hprd: x ⋅ y ∈ ℝ') by (apply nzRealMul_ran; auto).
  assert (Hrx: x⁻¹ ∈ ℝ) by (apply realMulInv_ran; auto).
  assert (Hry: y⁻¹ ∈ ℝ) by (apply realMulInv_ran; auto).
  assert (Real 1 = Real 1) by auto.
  rewrite <- realMul_1_r in H at 2...
  rewrite <- (realMulInv_annih (x ⋅ y)) in H at 1...
  rewrite <- (realMulInv_annih x) in H at 1...
  rewrite <- (realMulInv_annih y) in H...
  rewrite <- (realMul_assoc (x / x)), (realMul_assoc x Hx (x⁻¹)),
    (realMul_comm (x⁻¹)), <- realMul_assoc, (realMul_assoc (x ⋅ y))
    in H; auto; [|apply realMul_ran..]...
  apply realMul_cancel' in H...
  apply realMulInv_ran... apply realMul_ran...
Qed.

Corollary realMulInv_quot : ∀ x y ∈ ℝ', (x / y)⁻¹ = y / x.
Proof with auto.
  intros x Hx y Hy.
  rewrite realMulInv_prd, realMulInv_double, realMul_comm...
  apply realMulInv_ran... apply nzRealE in Hy as []...
  apply realMulInv_ran'...
Qed.

Lemma realMul_addInv_l : ∀ x y ∈ ℝ, -x ⋅ y = -(x ⋅ y).
Proof with eauto.
  intros x Hx y Hy.
  assert (Hnx: -x ∈ ℝ) by (apply realAddInv_ran; auto).
  assert (Hxy: x ⋅ y ∈ ℝ) by (apply realMul_ran; auto).
  eapply realAdd_cancel...
  apply realMul_ran... apply realAddInv_ran...
  rewrite <- realMul_distr', (realAdd_comm (-x)), realAddInv_annih,
    realMul_0_l, realAdd_comm, realAddInv_annih...
  apply realAddInv_ran...
Qed.

Lemma realMul_addInv_r : ∀ x y ∈ ℝ, x ⋅ -y = -(x ⋅ y).
Proof with auto.
  intros x Hx y Hy.
  rewrite realMul_comm, (realMul_comm x), realMul_addInv_l...
  apply realAddInv_ran...
Qed.

Lemma realMul_addInv_lr : ∀ x y ∈ ℝ, x ⋅ -y = -x ⋅ y.
Proof with auto.
  intros x Hx y Hy.
  rewrite realMul_addInv_l, realMul_addInv_r...
Qed.

Corollary realMul_addInv : ∀x ∈ ℝ, -Real 1 ⋅ x = -x.
Proof with nauto.
  intros x Hx.
  rewrite <- (realMul_1_l x) at 2...
  rewrite realMul_addInv_l...
Qed.

Lemma realMul_pos_prd : ∀ x y ∈ ℝ,
  realPos x → realPos y → realPos (x ⋅ y).
Proof with auto.
  intros x Hx y Hy Hpx Hpy.
  destruct_realMul x y.
  - exfalso. apply realNeg_nonPos in Hnx...
    apply realNonPos_not_pos in Hnx...
  - exfalso. apply realNeg_nonPos in Hnx...
    apply realNonPos_not_pos in Hnx...
  - exfalso. apply realNeg_nonPos in Hny...
    apply realNonPos_not_pos in Hny...
  - apply realNonNegMul_pos_prd...
Qed.

Theorem realMul_preserve_lt : ∀ x y z ∈ ℝ,
  realPos z → x <𝐫 y → x ⋅ z <𝐫 y ⋅ z.
Proof with nauto.
  intros x Hx y Hy z Hz Hpz Hle.
  assert (Hnx: -x ∈ ℝ) by (apply realAddInv_ran; auto).
  assert (Hny: -y ∈ ℝ) by (apply realAddInv_ran; auto).
  assert (Hxy: x - y ∈ ℝ) by (apply realAdd_ran; auto).
  assert (Hprd: (x - y) ⋅ z ∈ ℝ) by (apply realMul_ran; auto).
  rewrite <- (realAdd_0_r x), <- (realAddInv_annih y),
    (realAdd_comm y), <- realAdd_assoc, realMul_distr'...
  rewrite <- (realAdd_0_l (y ⋅ z)) at 2; [|apply realMul_ran]...
  apply realAdd_preserve_lt... apply realMul_ran...
  apply realLt_addInv'... rewrite realAddInv_0, <- realMul_addInv_l...
  rewrite realAddInv_diff... apply realMul_pos_prd...
  apply realAdd_ran... unfold realPos.
  rewrite <- (realAddInv_annih x)... apply realAdd_preserve_lt...
Qed.

Corollary realLt_mulInv : ∀ x y ∈ ℝ, realPos x → x <𝐫 y → y⁻¹ <𝐫 x⁻¹.
Proof with auto.
  intros x Hx y Hy Hpx Hlt.
  assert (Hx': x ∈ ℝ') by (apply nzRealI0; auto; apply real_neq_0; auto).
  assert (Hpy: realPos y) by (eapply realLt_trans; eauto).
  assert (Hy': y ∈ ℝ') by (apply nzRealI0; auto; apply real_neq_0; auto).
  assert (Hrx: x⁻¹ ∈ ℝ) by (apply realMulInv_ran; auto).
  assert (Hry: y⁻¹ ∈ ℝ) by (apply realMulInv_ran; auto).
  rewrite <- (realMul_1_l (y⁻¹)), <- (realMul_1_l (x⁻¹))...
  rewrite <- (realMulInv_annih x) at 1...
  rewrite <- (realMulInv_annih y)...
  rewrite realMul_assoc, realMul_assoc, (realMul_comm (x⁻¹))...
  apply realMul_preserve_lt... apply realMul_ran...
  apply realMul_pos_prd; auto; apply realPos_mulInv...
Qed.

(** 有理数嵌入 **)
Definition RatEmbed := Func ℚ ℝ (λ q, Realq q).

Theorem ratEmbed_function : RatEmbed: ℚ ⇒ ℝ.
Proof.
  apply meta_function.
  intros x Hx. apply real_q; nauto.
Qed.

Corollary ratEmbed_ran : ∀q ∈ ℚ, RatEmbed[q] ∈ ℝ.
Proof with auto.
  pose proof ratEmbed_function as [Hf [Hd Hr]].
  intros q Hq. apply Hr. eapply ranI.
  apply func_correct... rewrite Hd...
Qed.

Lemma ratEmbed_q : ∀q ∈ ℚ, RatEmbed[q] = Realq q.
Proof with nauto.
  intros q Hq. unfold RatEmbed. rewrite meta_func_ap...
  apply ratEmbed_function.
Qed.

Theorem ratEmbed : ∀ n : nat, RatEmbed[Rat n] = Real n.
Proof. intros. rewrite ratEmbed_q; nauto. Qed.

Lemma realq_lt : ∀ r s ∈ ℚ, Realq r <𝐫 Realq s ↔ r <𝐪 s.
Proof with neauto.
  intros r Hr s Hs. split; intros Hlt.
  - assert (Hsr: Realq s ∈ ℝ) by (apply real_q; auto).
    apply binRelE2 in Hlt as [H0 [_ [Hsub Hnq]]].
    destruct (classic (r = s)). exfalso. subst...
    apply ratLt_connected in H as []... exfalso.
    apply Hnq. ext q Hq.
    + apply Hsub in Hq as Hqs. apply SepE in Hq as [Hq _].
      apply realE3 in Hqs as [t [Ht [Hts Hqt]]]...
      eapply realE2; revgoals...
    + apply SepE in Hq as [Hq Hqs].
      apply SepI... eapply ratLt_trans...
  - apply binRelI; [apply real_q..|]... split.
    intros q Hq. apply SepE in Hq as [Hq Hqr].
    apply SepI... eapply ratLt_trans...
    intros Heq. assert (r ∈ Realq s) by (apply SepI; auto).
    rewrite <- Heq in H. apply SepE in H as [_ H].
    eapply ratLt_irrefl...
Qed.

Corollary realq_injective : ∀ r s ∈ ℚ, Realq r = Realq s → r = s.
Proof with eauto.
  intros r Hr s Hs Heq.
  destruct (classic (r = s))...
  exfalso... apply ratLt_connected in H as []...
  - apply realq_lt in H... rewrite Heq in H.
    eapply realLt_irrefl...
  - apply realq_lt in H... rewrite Heq in H.
    eapply realLt_irrefl...
Qed.

Corollary realq_le : ∀ r s ∈ ℚ, Realq r ≤ Realq s ↔ (r ≤ s)%q.
Proof with auto.
  intros r Hr s Hs. split; intros.
  - destruct H. left. apply realq_lt in H...
    right. apply realq_injective in H...
  - destruct H. left. apply realq_lt... right. subst...
Qed.

Theorem ratEmbed_lt : ∀ r s ∈ ℚ,
  r <𝐪 s ↔ RatEmbed[r] <𝐫 RatEmbed[s].
Proof with eauto.
  intros r Hr s Hs.
  repeat rewrite ratEmbed_q...
  rewrite (realq_lt _ Hr _ Hs). reflexivity.
Qed.

Theorem ratEmbed_injective : injective RatEmbed.
Proof with auto.
  apply meta_injection. intros x Hx. apply real_q...
  intros x1 Hx1 x2 Hx2 Heq. apply realq_injective in Heq...
Qed.

Close Scope Real_scope.
Open Scope Rat_scope.

Lemma realq_add : ∀ r s ∈ ℚ, Realq (r + s) = (Realq r + Realq s)%r.
Proof with nauto.
  intros r Hr s Hs.
  ext t Ht.
  - apply SepE in Ht as [Ht Hlt].
    set ((r + s - t) / Rat 2) as ε.
    assert (Hrsq: r + s ∈ ℚ) by (apply ratAdd_ran; auto).
    assert (Hnrsp: - (r + s) ∈ ℚ) by (apply ratAddInv_ran; auto).
    assert (Hntq: -t ∈ ℚ) by (apply ratAddInv_ran; auto).
    assert (Hsumq: r + s - t ∈ ℚ) by (apply ratAdd_ran; auto).
    assert (Hεq: ε ∈ ℚ) by (apply ratMul_ran; nauto).
    assert (Hnεq: -ε ∈ ℚ) by (apply ratAddInv_ran; auto).
    assert (Hsεq: s - ε ∈ ℚ) by (apply ratAdd_ran; auto).
    assert (Hpε: ratPos ε). {
      apply ratMul_pos_prd... unfold ratPos.
      rewrite <- (ratAddInv_annih t)... apply ratAdd_preserve_lt...
    }
    replace t with ((r - ε) + (s - ε)).
    apply realAddI2. apply real_q... apply real_q...
    + apply SepI. apply ratAdd_ran...
      rewrite <- (ratAdd_0_r r) at 2; [|auto].
      apply ratAdd_preserve_lt'... apply ratPos_neg...
    + apply SepI... rewrite <- (ratAdd_0_r s) at 2; [|auto].
      apply ratAdd_preserve_lt'... apply ratPos_neg...
    + rewrite ratAdd_assoc, (ratAdd_comm (-ε)), ratAdd_assoc,
        <- ratAdd_assoc, <- ratAddInv_sum; swap 2 6;
        [|apply ratAdd_ran|..]; [|assumption..]. unfold ε.
      assert ((Rat 2)⁻¹ ∈ ℚ) by nauto.
      rewrite <- (ratMul_distr (r+s-t) Hsumq (Rat 2)⁻¹ H (Rat 2)⁻¹ H),
        ratAdd_r2_r2_1, (ratMul_1_r (r + s - t)), ratAddInv_diff,
        (ratAdd_comm t), <- ratAdd_assoc, ratAddInv_annih, ratAdd_0_l...
  - apply realAddE in Ht as [p [Hpq [q [Hqq [[Hp Hq] Ht]]]]];
      [|apply real_q..]...
    apply SepE in Hp as [_ Hp]. apply SepE in Hq as [_ Hq].
    subst. apply SepI. apply ratAdd_ran...
    apply ratAdd_preserve_lt_trans...
Qed.

Corollary realq_addInv : ∀q ∈ ℚ, Realq (-q) = (-Realq q)%r.
Proof with auto.
  intros q Hq.
  assert (Hqr: Realq q ∈ ℝ) by (apply real_q; auto).
  assert (Hnq: -q ∈ ℚ) by (apply ratAddInv_ran; auto).
  eapply realAdd_cancel'; swap 1 3. apply Hqr.
  apply realAddInv_ran... apply real_q...
  rewrite <- realq_add, ratAddInv_annih, realAddInv_annih...
Qed.

Lemma realq_nonNegMul : ∀ r s ∈ ℚ, ratNonNeg r → ratNonNeg s →
  Realq (r ⋅ s) = (Realq r ⋅₊ Realq s)%r.
Proof with neauto.
  intros r Hr s Hs Hnnr Hnns.
  assert (Hrr: Realq r ∈ ℝ) by (apply real_q; auto).
  assert (Hsr: Realq s ∈ ℝ) by (apply real_q; auto).
  ext t Ht.
  - apply SepE in Ht as [Ht Hlt].
    destruct Hnnr as [Hpr|]; destruct Hnns as [Hps|]; revgoals; subst.
    rewrite ratMul_0_l in Hlt... apply realNonNegMulI0...
    rewrite ratMul_0_l in Hlt... apply realNonNegMulI0...
    rewrite ratMul_0_r_r in Hlt... apply realNonNegMulI0...
    destruct (classic (t = Rat 0)). {
      subst. rewrite <- (ratMul_0_l (Rat 0))...
      apply realNonNegMulI1; auto; [| |right..]...
      apply realLt_realq... apply realq_lt...
      apply realLt_realq... apply realq_lt...
    }
    apply ratLt_connected in H as [Hnt|Hpt]... {
      apply realNonNegMulI0...
    }
    assert (Hs': s ∈ ℚ'). { apply nzRatI0... apply rat_neq_0... }
    assert (Hrs: s⁻¹ ∈ ℚ). { apply nzRatE1. apply ratMulInv_ran... }
    assert (Hts: t/s ∈ ℚ) by (apply ratMul_ran; auto).
    assert (Hpts: ratPos (t/s)). {
      apply ratMul_pos_prd... apply ratPos_mulInv...
    }
    assert (H1: t/s <𝐪 r). {
      rewrite <- (ratMul_1_r r), <- (ratMulInv_annih s),
        <- ratMul_assoc... apply ratMul_preserve_lt...
      apply ratMul_ran... apply ratPos_mulInv...
    }
    apply rat_dense in H1 as [p [Hp [Hp1 Hp2]]]...
    assert (Hpp: ratPos p) by (eapply ratLt_trans; eauto).
    assert (Hp': p ∈ ℚ'). { apply nzRatI0... apply rat_neq_0... }
    assert (Hrp: p⁻¹ ∈ ℚ). { apply nzRatE1. apply ratMulInv_ran... }
    assert (Hprp: ratPos (p⁻¹)) by (apply ratPos_mulInv; auto).
    assert (Htp: (t/p) ∈ ℚ) by (apply ratMul_ran; auto).
    rewrite <- (ratMul_1_r t), <- (ratMulInv_annih p),
      (ratMul_comm p), <- ratMul_assoc, (ratMul_comm (t/p)); [|auto..].
    apply realNonNegMulI1; auto; swap 2 3.
    + apply SepI... + left...
    + apply SepI. apply Htp. rewrite <- (ratMul_1_r s),
        <- (ratMulInv_annih p), <- ratMul_assoc; [|auto..].
      apply ratMul_preserve_lt... apply ratMul_ran...
      rewrite <- (ratMul_1_r p), <- (ratMulInv_annih s),
        <- ratMul_assoc, (ratMul_comm p) in Hp1...
      apply ratMul_preserve_lt in Hp1...
      apply ratMul_ran... apply ratPos_mulInv...
    + left. apply ratMul_pos_prd...
  - apply realNonNegMulE in Ht as []; abs.
    + apply SepE in H as [Ht Hlt]. apply SepI...
      assert (Hnn: ratNonNeg (r ⋅ s)) by (apply ratMul_nonNeg_prd; auto).
      destruct Hnn. eapply ratLt_trans... rewrite <- H...
    + destruct H as [p [Hpq [q [Hqq [[Hp Hq] [[Hnnp Hnnq] Ht]]]]]].
      subst. apply SepI. apply ratMul_ran...
      apply SepE in Hp as [_ Hp]. apply SepE in Hq as [_ Hq].
      destruct Hnnp as [Hposp|Hp0]; destruct Hnnq as [Hposq|Hq0].
      * apply ratMul_preserve_lt_trans...
        eapply ratLt_trans; revgoals...
      * subst. rewrite ratMul_0_r_r... apply ratMul_pos_prd...
        eapply ratLt_trans; revgoals...
      * subst. rewrite ratMul_0_l... apply ratMul_pos_prd...
        eapply ratLt_trans; revgoals...
      * subst. rewrite ratMul_0_l... apply ratMul_pos_prd...
Qed.

Lemma realq_mul : ∀ r s ∈ ℚ, Realq (r ⋅ s) = (Realq r ⋅ Realq s)%r.
Proof with nauto.
  intros r Hr s Hs.
  assert (Hrr: Realq r ∈ ℝ) by (apply real_q; auto).
  assert (Hsr: Realq s ∈ ℝ) by (apply real_q; auto).
  assert (Hnr: -r ∈ ℚ) by (apply ratAddInv_ran; auto).
  assert (Hns: -s ∈ ℚ) by (apply ratAddInv_ran; auto).
  destruct_realMul (Realq r) (Realq s).
  - apply realq_lt in Hnx as Hngr... apply realNeg_nonPos in Hnx...
    apply realq_lt in Hny as Hngs... apply realNeg_nonPos in Hny...
    rewrite (realAbs_nonPos_flip _ Hnx), <- realq_addInv...
    rewrite (realAbs_nonPos_flip _ Hny), <- realq_addInv...
    replace (r ⋅ s) with (-r ⋅ -s).
    + apply realq_nonNegMul; auto; left.
      apply ratNeg_pos in Hngr... apply ratNeg_pos in Hngs...
    + rewrite ratMul_addInv_l, ratMul_addInv_r, ratAddInv_double...
      apply ratMul_ran...
  - apply realq_lt in Hnx as Hngr... apply realNeg_nonPos in Hnx...
    apply realNonNeg_not_neg in Hnny...
    rewrite (realAbs_nonPos_flip _ Hnx), <- realq_addInv...
    rewrite (realAbs_nonNeg_id _ Hnny)...
    rewrite <- (ratAddInv_double r) at 1...
    rewrite ratMul_addInv_l, realq_addInv; auto; [|apply ratMul_ran]...
    cut (Realq (-r ⋅ s)%q = (Realq (-r)%q ⋅₊ Realq s)%r). congruence.
    apply realq_nonNegMul...
    left. apply ratNeg_pos in Hngr... apply realq_le...
  - apply realNonNeg_not_neg in Hnnx...
    apply realq_lt in Hny as Hngs... apply realNeg_nonPos in Hny...
    rewrite (realAbs_nonNeg_id _ Hnnx)...
    rewrite (realAbs_nonPos_flip _ Hny), <- realq_addInv...
    rewrite <- (ratAddInv_double s) at 1...
    rewrite ratMul_addInv_r, realq_addInv; auto; [|apply ratMul_ran]...
    cut (Realq (r ⋅ -s)%q = (Realq r ⋅₊ Realq (-s)%q)%r). congruence.
    apply realq_nonNegMul... apply realq_le...
    left. apply ratNeg_pos in Hngs...
  - apply realq_nonNegMul...
    + apply realNonNeg_not_neg in Hnnx as []; auto; apply realq_le...
    + apply realNonNeg_not_neg in Hnny as []; auto; apply realq_le...
Qed.

Corollary realq_mulInv : ∀q ∈ ℚ', Realq (q⁻¹) = ((Realq q)⁻¹)%r.
Proof with nauto.
  intros q Hq'.
  apply nzRatE0 in Hq' as Hq0.
  apply nzRatE1 in Hq' as Hq.
  assert (Hrq0: Realq q ≠ Real 0). {
    intros H. apply realq_injective in H...
  }
  assert (Hqr: Realq q ∈ ℝ) by (apply real_q; auto).
  assert (Hqr': Realq q ∈ ℝ') by (apply nzRealI0; auto).
  assert (Hnq: q⁻¹ ∈ ℚ) by (apply nzRatE1; apply ratMulInv_ran; auto).
  eapply realMul_cancel'; swap 1 3. apply Hqr'.
  apply realMulInv_ran... apply real_q...
  rewrite <- realq_mul, ratMulInv_annih, realMulInv_annih...
Qed.

Corollary realq_div : ∀r ∈ ℚ, ∀s ∈ ℚ',
  Realq (r / s) = (Realq r / Realq s)%r.
Proof with nauto.
  intros r Hr s Hs'.
  rewrite realq_mul, realq_mulInv...
  apply nzRatE1. apply ratMulInv_ran...
Qed.

Close Scope Rat_scope.
Open Scope Real_scope.

Theorem ratEmbed_add : ∀ r s ∈ ℚ,
  RatEmbed[(r + s)%q] = RatEmbed[r] + RatEmbed[s].
Proof with nauto.
  intros r Hr s Hs.
  repeat rewrite ratEmbed_q; auto; [|apply ratAdd_ran]...
  apply realq_add...
Qed.

Corollary ratEmbed_addInv : ∀q ∈ ℚ, RatEmbed[(-q)%q] = -Realq q.
Proof with auto.
  intros q Hq.
  rewrite ratEmbed_q; [|apply ratAddInv_ran]...
  apply realq_addInv...
Qed.

Theorem ratEmbed_mul : ∀ r s ∈ ℚ,
  RatEmbed[(r ⋅ s)%q] = RatEmbed[r] ⋅ RatEmbed[s].
Proof with nauto.
  intros r Hr s Hs.
  repeat rewrite ratEmbed_q; auto; [|apply ratMul_ran]...
  apply realq_mul...
Qed.

Corollary ratEmbed_mulInv : ∀q ∈ ℚ', RatEmbed[(q⁻¹)%q] = (Realq q)⁻¹.
Proof with auto.
  intros q Hq.
  rewrite ratEmbed_q; [|apply nzRatE1; apply ratMulInv_ran]...
  apply realq_mulInv...
Qed.

Corollary ratEmbed_div : ∀r ∈ ℚ, ∀s ∈ ℚ', 
  RatEmbed[(r / s)%q] = RatEmbed[r] / RatEmbed[s].
Proof with nauto.
  intros r Hr s Hs'. apply nzRatE1 in Hs' as Hs.
  repeat rewrite ratEmbed_q; auto; [|apply ratMul_ran]...
  apply realq_div... apply nzRatE1. apply ratMulInv_ran...
Qed.

(** 实数的稠密性 **)

Notation "ℤ⁺" := {a ∊ ℤ | intPos a} : set_scope.
Definition EE : set → set := λ a, RatEmbed[IntEmbed[a]].

Lemma ee_ran : ∀a ∈ ℤ, EE a ∈ ℝ.
Proof with auto.
  intros a Ha. apply ratEmbed_ran... apply intEmbed_ran...
Qed.

Lemma realLt_supremum : ∀ A, ∀ x z ∈ ℝ, A ⊆ ℝ →
  x <𝐫 z → supremum z A ℝ RealLt → ∃y ∈ A, x <𝐫 y.
Proof with eauto.
  intros A x Hx z Hz Hsub Hxz [Hub Hsup].
  destruct (classic (∃y ∈ A, x <𝐫 y))...
  assert (Hupx: ∀y ∈ A, y ≤ x). {
    intros y Hy. destruct (classic (y = x))...
    apply realLt_connected in H0 as []...
    exfalso. apply H. exists y. split...
  }
  destruct (Hsup x) as []. { split... }
  - pose proof (realLt_trich _ Hx _ Hz) as []; tauto.
  - subst. exfalso. eapply realLt_irrefl...
Qed.

Lemma real_archimedean : ∀ x y ∈ ℝ, realPos x →
  ∃a ∈ ℤ⁺, y <𝐫 x ⋅ EE a.
Proof with neauto.
  intros x Hx y Hy Hpx.
  assert (Hpdr: ∀w ∈ ℝ, ∀a ∈ ℤ⁺, w ⋅ EE a ∈ ℝ). {
    intros w Hw a Ha. apply realMul_ran... apply ee_ran...
    apply SepE1 in Ha...
  }
  destruct (classic (∃a ∈ ℤ⁺, y <𝐫 x ⋅ EE a))...
  assert (Hle: ∀a ∈ ℤ⁺, x ⋅ EE a ≤ y). {
    intros a Ha. remember (x ⋅ EE a) as x'.
    cut (¬(y <𝐫 x')). intros Hnn.
    - destruct (classic (x' = y))...
      apply realLt_connected in H0 as []...
      exfalso... subst x'. apply Hpdr...
    - intros Hnn. apply H. exists a. split... subst...
  }
  set {x ⋅ EE a | a ∊ ℤ⁺} as A.
  assert (Hsub: A ⊆ ℝ). {
    intros w Hw. apply ReplAx in Hw as [a [Ha Heq]].
    subst w. apply Hpdr...
  }
  pose proof (reals_boundedAbove_has_supremum A) as [s [Hub Hsup]]... {
    apply EmptyNI. exists (x ⋅ EE (Int 1)).
    apply ReplAx. exists (Int 1). split... apply SepI...
  } {
    exists y. split; [|repeat split]...
    intros w Hw. apply ReplAx in Hw as [a [Ha Heq]].
    apply Hle in Ha. unfold relLe. congruence.
  }
  assert (Hub' := Hub). destruct Hub' as [Hs Hle'].
  exfalso. clear H Hle.
  assert (Hnx: -x ∈ ℝ) by (apply realAddInv_ran; auto).
  assert (Hlt: s - x <𝐫 s). {
    rewrite realAdd_comm... rewrite <- (realAdd_0_l s) at 2...
    apply realAdd_preserve_lt... apply realPos_neg...
  }
  assert (Hsx: s - x ∈ ℝ) by (apply realAdd_ran; auto).
  pose proof (realLt_supremum A (s - x) Hsx s Hs) as [z [Hz H]]... split...
  apply ReplAx in Hz as [a [Ha Heq]]. subst z.
  remember (x ⋅ EE a) as x'.
  assert (Hx': x' ∈ ℝ) by (subst; apply Hpdr; auto).
  rewrite <- (realAdd_0_r x'), <- (realAddInv_annih x), <- realAdd_assoc in H...
  apply realSubtr_preserve_lt in H; auto; [|apply realAdd_ran]...
  rewrite <- (realMul_1_r x), <- ratEmbed, <- intEmbed in H...
  subst x'. clear Hx'. apply SepE in Ha as [Ha Hpa]. unfold EE in H.
  rewrite <- realMul_distr in H; auto; [|apply ee_ran..]...
  rewrite <- ratEmbed_add in H; [|apply intEmbed_ran..]...
  rewrite <- intEmbed_add in H...
  remember (x ⋅ RatEmbed[IntEmbed[(a + Int 1)%z]]) as x'.
  assert (Ha': (a + Int 1)%z ∈ ℤ⁺). {
    apply SepI... apply intAdd_ran...
    eapply intLt_trans. apply (intPos_sn 0).
    rewrite <- (intAdd_0_l (Int 1)) at 1...
    apply intAdd_preserve_lt...
  }
  assert (Hx': x' ∈ ℝ) by (subst; apply Hpdr; auto).
  cut (x' ≤ s). pose proof (realLt_trich _ Hx' _ Hs) as []; tauto.
  apply Hle'. apply ReplAx. exists (a + Int 1)%z. split...
Qed.

Theorem real_dense : ∀ x y ∈ ℝ, x <𝐫 y →
  ∃r ∈ ℚ, x <𝐫 RatEmbed[r] ∧ RatEmbed[r] <𝐫 y.
Proof with neauto.
  intros x Hx y Hy Hxy.
  (* a *)
  assert (Hnx: -x ∈ ℝ) by (apply realAddInv_ran; auto).
  assert (Hyx: y - x ∈ ℝ) by (apply realAdd_ran; auto).
  assert (Hpyx: realPos (y - x)). {
    unfold realPos. rewrite <- (realAddInv_annih x)...
    apply realAdd_preserve_lt...
  }
  pose proof (real_archimedean _ Hyx _ (real_n 1) Hpyx) as [a [Ha H1]].
  apply SepE in Ha as [Ha Hpa].
  assert (Heea: EE a ∈ ℝ) by (apply ee_ran; auto).
  assert (Hxa: x ⋅ EE a ∈ ℝ) by (apply realMul_ran; auto).
  assert (Hnxa: -(x ⋅ EE a) ∈ ℝ) by (apply realAddInv_ran; auto).
  rewrite realMul_distr', realMul_addInv_l,
    <- (realAdd_0_r (Real 1)), <- (realAddInv_annih (x ⋅ EE a)),
    <- realAdd_assoc, (realAdd_comm (Real 1)) in H1...
  apply realSubtr_preserve_lt in H1; auto;
    [|apply realAdd_ran|apply realMul_ran]...
  clear Hxy Hnx Hyx Hpyx Hnxa.
  (* b c *)
  pose proof (real_archimedean _ (real_n 1) _ Hxa (realPos_sn 0)) as [b [Hb H2]].
  apply SepE in Hb as [Hb Hpb].
  assert (Heeb: EE b ∈ ℝ) by (apply ee_ran; auto).
  rewrite realMul_1_l in H2...
  assert (Hneea: -EE a ∈ ℝ) by (apply realAddInv_ran; auto).
  assert (Hxna: x ⋅ -EE a ∈ ℝ) by (apply realMul_ran; auto).
  pose proof (real_archimedean _ (real_n 1) _ Hxna (realPos_sn 0)) as [c [Hc H3]].
  apply SepE in Hc as [Hc Hpc].
  assert (Heec: EE c ∈ ℝ) by (apply ee_ran; auto).
  rewrite realMul_1_l, realMul_addInv_r in H3...
  apply realLt_addInv in H3; auto; [|apply realAddInv_ran]...
  rewrite realAddInv_double in H3...
  set {d ∊ ℤ | x ⋅ EE a <𝐫 EE d} as A.
  pose proof (ints_boundedBelow_has_min' A) as [d [Hd Hd']]. {
    apply EmptyNI. exists b. apply SepI...
  } {
    intros d Hd. apply SepE1 in Hd...
  } {
    assert (Hnc: (-c)%z ∈ ℤ) by (apply intAddInv_ran; auto).
    exists (-c)%z. split...
    intros d Hd. apply SepE in Hd as [Hd Hlt].
    left. apply intEmbed_lt... apply ratEmbed_lt.
    apply intEmbed_ran... apply intEmbed_ran...
    rewrite intEmbed_addInv, <- intEmbed_a, ratEmbed_addInv,
      <- ratEmbed_q; auto; [|apply intEmbed_ran..]...
    eapply realLt_trans...
  }
  clear Hneea Hxna Hb Hpb H2 Heeb b Hc Hpc H3 Heec c.
  (* d *)
  apply SepE in Hd as [Hd Hlt1].
  assert (Hdm: (d - Int 1)%z ∈ ℤ) by (apply intAdd_ran; nauto).
  assert (Heedm: EE (d - Int 1)%z ∈ ℝ) by (apply ee_ran; auto).
  assert (H2: EE (d - Int 1)%z ≤ x ⋅ EE a). {
    destruct (classic (EE (d - Int 1)%z ≤ x ⋅ EE a))...
    exfalso. apply Hd'. apply SepI...
    pose proof (realLt_trich _ Heedm _ Hxa) as []; tauto.
  }
  assert (Hee1: EE (Int 1) ∈ ℝ) by (apply ee_ran; nauto).
  assert (Hnee1: -EE (Int 1) ∈ ℝ) by (apply realAddInv_ran; auto).
  unfold EE in H2. rewrite intEmbed_add, ratEmbed_add,
    intEmbed_addInv, <- intEmbed_a, ratEmbed_addInv, <- ratEmbed_q,
    <- (realAdd_0_r (x ⋅ RatEmbed[IntEmbed[a]])),
    <- (realAddInv_annih (EE (Int 1))),
    <- realAdd_assoc in H2; nauto; [|apply intEmbed_ran..]...
  apply realSubtr_preserve_le in H2; auto;
    [|apply ee_ran|apply realAdd_ran]...
  unfold EE in H2. rewrite intEmbed, ratEmbed in H2.
  assert (Hlt2: EE d <𝐫 y ⋅ EE a). {
    destruct H2. eapply realLt_trans...
    unfold EE in H1. rewrite <- H in H1...
  }
  clear A Hd' Hdm Heedm Hee1 Hnee1 H1 H2.
  (* mulInv *)
  assert (Hpea: ratPos (IntEmbed [a])). {
    unfold ratPos. rewrite <- intEmbed. apply intEmbed_lt...
  }
  assert (Hpeea: realPos (EE a)). {
    unfold realPos. rewrite <- ratEmbed.
    apply ratEmbed_lt... apply intEmbed_ran...
  }
  assert (Heea': EE a ∈ ℝ'). { apply nzRealI0... apply real_neq_0... }
  assert (Hra: (EE a)⁻¹ ∈ ℝ). { apply nzRealE. apply realMulInv_ran'... }
  assert (Hpra: realPos (EE a)⁻¹) by (apply realPos_mulInv; auto).
  assert (Heed: EE d ∈ ℝ) by (apply ee_ran; auto).
  assert (Hya: y ⋅ EE a ∈ ℝ) by (apply realMul_ran; auto).
  assert (Ha': a ∈ ℤ'). { apply nzIntI0... apply int_neq_0... }
  assert (Hed: IntEmbed [d] ∈ ℚ) by (apply intEmbed_ran; auto).
  assert (Hea: IntEmbed [a] ∈ ℚ) by (apply intEmbed_ran; auto).
  assert (Hea': IntEmbed [a] ∈ ℚ'). { apply nzRatI0... apply rat_neq_0... }
  eapply realMul_preserve_lt in Hlt1; revgoals; [apply Hpra|..]...
  eapply realMul_preserve_lt in Hlt2; revgoals; [apply Hpra|..]...
  rewrite realMul_assoc, realMulInv_annih, realMul_1_r in Hlt1, Hlt2...
  unfold EE in Hlt1, Hlt2.
  rewrite <- ratEmbed_div, <- intEmbed_div in Hlt1, Hlt2...
  exists ([<d, a>]~). split. apply pQuotI... split...
Qed.
