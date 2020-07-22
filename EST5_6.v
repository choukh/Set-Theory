(** Based on "Elements of Set Theory" Chapter 5 Part 6 **)
(** Coq coding by choukh, July 2020 **)

Require Export ZFC.EST5_5.

(*** EST第五章6：实数绝对值，实数乘法，有理数嵌入 ***)

Lemma realLt_addInv : ∀ x y ∈ ℝ, x <𝐫 y → -y <𝐫 -x.
Proof with auto.
  intros x Hx y Hy Hlt.
  apply realLtE in Hlt as [_ [_ [Hsub Hnq]]]. apply realLt...
  apply realAddInv_real... apply realAddInv_real... split.
  - intros q Hq. apply SepE in Hq as [Hq [s [Hs [Hlt Hout]]]].
    apply SepI... exists s. repeat split...
    intros Hin. apply Hout. apply Hsub...
  - intros Heq. apply Hnq. assert (--y = --x) by congruence.
    rewrite realAddInv_double, realAddInv_double in H...
Qed.

Lemma realLt_addInv' : ∀ x y ∈ ℝ, -y <𝐫 -x → x <𝐫 y.
Proof with eauto.
  intros x Hx y Hy Hlt. destruct (classic (x = y)).
  - exfalso. subst.
    eapply realLt_not_refl; revgoals... apply realAddInv_real...
  - apply realLt_connected in H as []...
    exfalso. apply realLt_addInv in H...
    eapply realLt_not_refl; revgoals.
    eapply realLt_tranr; revgoals... apply realAddInv_real...
Qed.

Lemma realLeq_addInv : ∀ x y ∈ ℝ, x ≤ y → -y ≤ -x.
Proof with auto.
  intros x Hx y Hy [Hlt|Heq].
  - left. apply realLt_addInv...
  - right. congruence.
Qed.

Lemma realLeq_addInv' : ∀ x y ∈ ℝ, -y ≤ -x → x ≤ y.
Proof with eauto.
  intros x Hx y Hy [Hlt|Heq].
  - left. apply realLt_addInv'...
  - right. assert (--y = --x) by congruence.
    rewrite realAddInv_double, realAddInv_double in H...
Qed.

Lemma realAddInv_0 : -Real 0 = Real 0.
Proof with neauto.
  apply ExtAx. intros q. split; intros Hq.
  - apply SepE in Hq as [Hq [s [Hs [Hlt Hout]]]].
    apply SepI... destruct (classic (q = Rat 0)).
    + exfalso. subst. apply Hout. apply SepI.
      apply ratAddInv_rat... apply rat_pos_neg...
    + apply ratLt_connected in H as []...
      exfalso. apply Hout. apply SepI.
      apply ratAddInv_rat... apply rat_pos_neg. eapply ratLt_tranr...
  - apply SepE in Hq as [Hq Hlt]. apply SepI...
    exists (Rat 0). repeat split... intros Hin.
    apply SepE in Hin as [_ H]. rewrite ratAddInv_0 in H.
    eapply ratLt_not_refl; revgoals...
Qed.

Definition realPos : set → Prop := λ x, Real 0 <𝐫 x.
Definition realNeg : set → Prop := λ x, x <𝐫 Real 0.

Lemma realPosI : ∀x ∈ ℝ, Rat 0 ∈ x → realPos x.
Proof with neauto.
  intros x Hx H. apply realLtI... split.
  - intros p Hp. apply SepE in Hp as [Hpq Hlt].
    eapply realE2; revgoals...
  - intros H0. subst. apply SepE in H as [_ H].
    eapply ratLt_not_refl; revgoals...
Qed.

Lemma realPosE : ∀ x, realPos x → Rat 0 ∈ x.
Proof with neauto.
  intros. apply realLtE in H as [H0 [Hx [Hsub Hnq]]].
  destruct (classic (Rat 0 ∈ x))... exfalso.
  apply Hnq. apply ExtAx. intros p. split; intros Hp.
  - apply Hsub in Hp as Hpx. apply SepE in Hp as [Hpq _].
    apply realE3 in Hpx as [q [Hq Hlt]]...
    eapply realE2; revgoals... apply (real_sub_rat x Hx)...
  - assert (Hpq: p ∈ ℚ) by (apply (real_sub_rat x Hx); auto).
    apply SepI... eapply realE2_1...
Qed.

Lemma real_pos_neg : ∀ x, realPos x → realNeg (-x).
Proof with neauto.
  intros. apply realLt_addInv in H... rewrite realAddInv_0 in H...
  apply realLtE in H as [_ [Hx _]]...
Qed.

Lemma real_neg_pos : ∀ x, realNeg x → realPos (-x).
Proof with nauto.
  intros. apply realLt_addInv in H... rewrite realAddInv_0 in H...
  apply realLtE in H as [Hx _]...
Qed.

(** 实数绝对值 **)
Definition RealAbs : set → set := λ x, x ∪ -x.
Notation "| r |" := (RealAbs r) (at level 60) : Real_scope.
Notation " x ≥ y " := (y ≤ x) (at level 70): Real_scope.

Lemma realAbs_id : ∀ x, x ≥ Real 0 → |x| = x.
Proof with neauto.
  intros x [Hpos|H0].
  - apply realPosE in Hpos as H0.
    assert (H := Hpos). apply realLtE in H as [_ [Hx _]]...
    apply ExtAx. intros q. split; intros Hq; revgoals.
    apply BUnionI1... apply BUnionE in Hq as []...
    apply SepE in H as [Hq [s [Hs [Hlt H]]]].
    eapply realE2_1 in H; revgoals... apply ratAddInv_rat...
    apply rat_pos_neg in H. rewrite ratAddInv_double in H...
    assert (Hnq: ratNeg q) by (eapply ratLt_tranr; eauto).
    eapply realE2; revgoals...
  - subst. apply ExtAx. intros q. split; intros Hq.
    + apply BUnionE in Hq as []... rewrite realAddInv_0 in H...
    + apply BUnionI1...
Qed.

Lemma realAbs_id' : ∀x ∈ ℝ, |x| = x → x ≥ Real 0.
Proof with neauto.
  intros x Hx Heq. apply realLeq... intros q Hq.
  apply SepE in Hq as [Hq Hlt]. rewrite <- Heq.
  destruct (classic (Rat 0 ∈ x)).
  - apply BUnionI1. eapply realE2; revgoals...
  - apply BUnionI2. apply SepI... exists (Rat 0).
    split... split... rewrite ratAddInv_0...
Qed.

Lemma realAbs_flip : ∀ x, x ≤ Real 0 → |x| = -x.
Proof with neauto.
  intros x [Hneg|Heq].
  - apply real_neg_pos in Hneg as Hpos.
    apply realPosE in Hpos as H0.
    assert (H := Hneg). apply realLtE in H as [Hx _]...
    apply ExtAx. intros q. split; intros Hq; revgoals.
    apply BUnionI2... apply BUnionE in Hq as [Hqx|]...
    assert (Hq: q ∈ ℚ) by (apply (real_sub_rat x Hx); auto).
    apply SepI... apply SepE in H0 as [_ [s [Hs [Hlt Hout]]]].
    exists s. split... split... eapply ratLt_tranr...
    eapply realE2_1... intros H. apply realPosI in H...
    eapply realLt_not_refl; revgoals.
    eapply realLt_tranr... apply real_n.
  - subst. apply ExtAx. intros q. split; intros Hq.
    + apply BUnionE in Hq as []... rewrite realAddInv_0...
    + apply BUnionI2...
Qed.

Lemma realAbs_flip' : ∀x ∈ ℝ, |x| = -x → x ≤ Real 0.
Proof with neauto.
  intros x Hx Heq. apply realLeq_addInv'...
  rewrite realAddInv_0. apply realLeq... apply realAddInv_real...
  intros q Hq. apply SepE in Hq as [Hq Hlt]. rewrite <- Heq.
  destruct (classic (Rat 0 ∈ x)).
  - apply BUnionI1. eapply realE2; revgoals...
  - apply BUnionI2. apply SepI... exists (Rat 0).
    split... split... rewrite ratAddInv_0...
Qed.

Lemma realAbs_geq_0 : ∀x ∈ ℝ, |x| ≥ Real 0.
Proof with neauto.
  intros x Hx. destruct (classic (x ≥ Real 0)).
  - rewrite (realAbs_id _ H)...
  - assert (x ≠ Real 0) by auto. assert (¬ Real 0 <𝐫 x) by auto.
    apply realLt_connected in H0 as []; revgoals... exfalso...
    assert (x ≤ Real 0) by auto. rewrite (realAbs_flip _ H2).
    apply realLeq_addInv in H2... rewrite realAddInv_0 in H2...
Qed.





